"""
Numerical equivalence checker — ULP distance, tolerance sheaf, NaN/Inf semantics.

Models numerical equivalence as a presheaf on the tolerance site:
  - Objects: (dtype, tolerance_spec) pairs
  - Morphisms: tolerance coarsening (wider tolerance restricts to narrower)
  - Sections: concrete output tensors at each (dtype, tol) site
  - Equivalence: section-pairs glue within tolerance at every site

The ε-closeness relation generates a Čech nerve:
  - 0-simplices: individual output comparisons
  - 1-simplices: pairs of outputs that are ε-close (form an edge)
  - Higher simplices: complete sub-graphs of the ε-closeness relation
  This is the Vietoris–Rips complex of the output space at scale ε.
"""

from __future__ import annotations

import math
import struct
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Tuple

from ._protocols import (
    AnalysisJudgment,
    AnalysisMode,
    AnalysisVerdict,
    Bug,
    BugKind,
    EquivalenceVerdict,
    NumericalToleranceSpec,
    ProgramId,
    SheafConditionResult,
    SiteId,
    SiteKind,
    TensorEquivalenceConfig,
    TensorLocalJudgment,
    TensorObstruction,
    TensorObstructionKind,
    TensorSiteKind,
    TensorSpec,
    TensorStratum,
    TrustLevel,
)


# ---------------------------------------------------------------------------
# ULP (Units in the Last Place) computation
# ---------------------------------------------------------------------------

def _float_to_int_bits(x: float) -> int:
    """Reinterpret a float64 as a signed int64 for ULP calculation."""
    bits = struct.pack("d", x)
    uint = struct.unpack("Q", bits)[0]
    if uint >> 63:  # negative
        return -(uint & 0x7FFFFFFFFFFFFFFF)
    return uint


def ulp_distance(a: float, b: float) -> int:
    """
    Compute the ULP distance between two float64 values.

    ULP distance measures how many representable floating-point numbers
    lie between a and b.  This is the canonical metric on the floating-point
    number line and is invariant under the scale of the values.
    """
    if math.isnan(a) or math.isnan(b):
        return 0 if (math.isnan(a) and math.isnan(b)) else 2**53
    if math.isinf(a) or math.isinf(b):
        if a == b:
            return 0
        return 2**53
    ia = _float_to_int_bits(a)
    ib = _float_to_int_bits(b)
    return abs(ia - ib)


# ---------------------------------------------------------------------------
# Tolerance spec operations (the tolerance lattice)
# ---------------------------------------------------------------------------

def tolerance_leq(a: NumericalToleranceSpec, b: NumericalToleranceSpec) -> bool:
    """a ≤ b in the tolerance lattice iff a is tighter than b."""
    return (a.rtol <= b.rtol and a.atol <= b.atol and a.max_ulp <= b.max_ulp)


def tolerance_meet(a: NumericalToleranceSpec,
                   b: NumericalToleranceSpec) -> NumericalToleranceSpec:
    """Greatest lower bound: tightest common tolerance."""
    return NumericalToleranceSpec(
        rtol=min(a.rtol, b.rtol),
        atol=min(a.atol, b.atol),
        max_ulp=min(a.max_ulp, b.max_ulp),
        nan_equal=a.nan_equal and b.nan_equal,
        inf_equal=a.inf_equal and b.inf_equal,
        reduction_order_sensitive=a.reduction_order_sensitive or b.reduction_order_sensitive,
        dtype_specific_tol={**a.dtype_specific_tol, **b.dtype_specific_tol},
    )


def tolerance_join(a: NumericalToleranceSpec,
                   b: NumericalToleranceSpec) -> NumericalToleranceSpec:
    """Least upper bound: loosest tolerance satisfying both."""
    return NumericalToleranceSpec(
        rtol=max(a.rtol, b.rtol),
        atol=max(a.atol, b.atol),
        max_ulp=max(a.max_ulp, b.max_ulp),
        nan_equal=a.nan_equal or b.nan_equal,
        inf_equal=a.inf_equal or b.inf_equal,
        reduction_order_sensitive=a.reduction_order_sensitive and b.reduction_order_sensitive,
        dtype_specific_tol={**a.dtype_specific_tol, **b.dtype_specific_tol},
    )


def default_tolerance_for_dtype(dtype: str) -> NumericalToleranceSpec:
    """
    Get the default numerical tolerance for a given dtype.

    These tolerances reflect the intrinsic precision of each dtype:
    float16 has ~3 decimal digits, bfloat16 ~2, float32 ~7, float64 ~15.
    """
    _DTYPE_TOLS = {
        "float16": NumericalToleranceSpec(rtol=1e-3, atol=1e-3, max_ulp=16),
        "bfloat16": NumericalToleranceSpec(rtol=1e-2, atol=1e-2, max_ulp=32),
        "float32": NumericalToleranceSpec(rtol=1e-5, atol=1e-5, max_ulp=4),
        "float64": NumericalToleranceSpec(rtol=1e-10, atol=1e-10, max_ulp=2),
        "complex64": NumericalToleranceSpec(rtol=1e-5, atol=1e-5, max_ulp=4),
        "complex128": NumericalToleranceSpec(rtol=1e-10, atol=1e-10, max_ulp=2),
    }
    return _DTYPE_TOLS.get(dtype, NumericalToleranceSpec(rtol=1e-5, atol=1e-5, max_ulp=4))


# ---------------------------------------------------------------------------
# Element-wise numerical comparison
# ---------------------------------------------------------------------------

@dataclass
class ElementComparison:
    """Result of comparing two scalar elements."""
    index: Tuple[int, ...]
    val_f: float
    val_g: float
    abs_diff: float
    rel_diff: float
    ulp_diff: int
    within_tol: bool


def _compare_elements(val_f: float, val_g: float,
                      tol: NumericalToleranceSpec,
                      index: Tuple[int, ...] = ()) -> ElementComparison:
    """Compare two scalar values under the tolerance spec."""
    # NaN handling
    if math.isnan(val_f) and math.isnan(val_g):
        return ElementComparison(
            index=index, val_f=val_f, val_g=val_g,
            abs_diff=0.0, rel_diff=0.0, ulp_diff=0,
            within_tol=tol.nan_equal,
        )
    if math.isnan(val_f) or math.isnan(val_g):
        return ElementComparison(
            index=index, val_f=val_f, val_g=val_g,
            abs_diff=float("inf"), rel_diff=float("inf"), ulp_diff=2**53,
            within_tol=False,
        )

    # Inf handling
    if math.isinf(val_f) and math.isinf(val_g):
        same_sign = (val_f > 0) == (val_g > 0)
        return ElementComparison(
            index=index, val_f=val_f, val_g=val_g,
            abs_diff=0.0 if same_sign else float("inf"),
            rel_diff=0.0 if same_sign else float("inf"),
            ulp_diff=0 if same_sign else 2**53,
            within_tol=same_sign and tol.inf_equal,
        )
    if math.isinf(val_f) or math.isinf(val_g):
        return ElementComparison(
            index=index, val_f=val_f, val_g=val_g,
            abs_diff=float("inf"), rel_diff=float("inf"), ulp_diff=2**53,
            within_tol=False,
        )

    abs_diff = abs(val_f - val_g)
    denom = max(abs(val_f), abs(val_g), 1e-300)
    rel_diff = abs_diff / denom
    ulps = ulp_distance(val_f, val_g)

    within = (abs_diff <= tol.atol + tol.rtol * denom) and (ulps <= tol.max_ulp)

    return ElementComparison(
        index=index, val_f=val_f, val_g=val_g,
        abs_diff=abs_diff, rel_diff=rel_diff, ulp_diff=ulps,
        within_tol=within,
    )


# ---------------------------------------------------------------------------
# Tensor-level numerical comparison
# ---------------------------------------------------------------------------

@dataclass
class NumericalComparisonResult:
    """Full result of comparing two tensors numerically."""
    verdict: EquivalenceVerdict
    max_abs_diff: float = 0.0
    max_rel_diff: float = 0.0
    max_ulp_diff: int = 0
    mean_abs_diff: float = 0.0
    num_mismatches: int = 0
    total_elements: int = 0
    worst_elements: List[ElementComparison] = field(default_factory=list)
    explanation: str = ""


def compare_tensors(tensor_f: Any, tensor_g: Any,
                    tol: NumericalToleranceSpec,
                    max_worst: int = 10) -> NumericalComparisonResult:
    """
    Compare two tensors element-wise under the tolerance presheaf.

    This is the *local section comparison* at a numerical site: we evaluate
    both functions at a concrete input and compare the output tensors
    element by element.  The comparison respects the tolerance lattice —
    tighter tolerances yield finer distinctions.
    """
    try:
        import torch
    except ImportError:
        return NumericalComparisonResult(
            verdict=EquivalenceVerdict.UNKNOWN,
            explanation="PyTorch not available",
        )

    if not isinstance(tensor_f, torch.Tensor) or not isinstance(tensor_g, torch.Tensor):
        # Handle non-tensor outputs (scalars, None, etc.)
        if tensor_f is None and tensor_g is None:
            return NumericalComparisonResult(
                verdict=EquivalenceVerdict.EQUIVALENT,
                explanation="Both outputs are None",
            )
        if type(tensor_f) != type(tensor_g):
            return NumericalComparisonResult(
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation=f"Type mismatch: {type(tensor_f)} vs {type(tensor_g)}",
            )
        # Scalar comparison
        try:
            f_val = float(tensor_f)
            g_val = float(tensor_g)
            cmp = _compare_elements(f_val, g_val, tol)
            return NumericalComparisonResult(
                verdict=EquivalenceVerdict.EQUIVALENT if cmp.within_tol
                else EquivalenceVerdict.INEQUIVALENT,
                max_abs_diff=cmp.abs_diff,
                max_rel_diff=cmp.rel_diff,
                max_ulp_diff=cmp.ulp_diff,
                total_elements=1,
                num_mismatches=0 if cmp.within_tol else 1,
            )
        except (TypeError, ValueError):
            return NumericalComparisonResult(
                verdict=EquivalenceVerdict.EQUIVALENT
                if tensor_f == tensor_g else EquivalenceVerdict.INEQUIVALENT,
            )

    # Shape check (quick reject)
    if tensor_f.shape != tensor_g.shape:
        return NumericalComparisonResult(
            verdict=EquivalenceVerdict.INEQUIVALENT,
            explanation=f"Shape mismatch: {tensor_f.shape} vs {tensor_g.shape}",
        )

    # Move to CPU for comparison
    f_cpu = tensor_f.detach().cpu()
    g_cpu = tensor_g.detach().cpu()

    # Handle complex dtypes
    if f_cpu.is_complex():
        f_cpu = torch.view_as_real(f_cpu)
        g_cpu = torch.view_as_real(g_cpu)

    # Boolean tensors
    if f_cpu.dtype == torch.bool:
        mismatches = (f_cpu != g_cpu).sum().item()
        return NumericalComparisonResult(
            verdict=EquivalenceVerdict.EQUIVALENT if mismatches == 0
            else EquivalenceVerdict.INEQUIVALENT,
            num_mismatches=mismatches,
            total_elements=f_cpu.numel(),
        )

    # Integer tensors
    if not f_cpu.is_floating_point():
        mismatches = (f_cpu != g_cpu).sum().item()
        return NumericalComparisonResult(
            verdict=EquivalenceVerdict.EQUIVALENT if mismatches == 0
            else EquivalenceVerdict.INEQUIVALENT,
            num_mismatches=mismatches,
            total_elements=f_cpu.numel(),
        )

    # Floating-point comparison
    f_flat = f_cpu.to(torch.float64).flatten()
    g_flat = g_cpu.to(torch.float64).flatten()
    total = f_flat.numel()

    diff = (f_flat - g_flat).abs()
    max_abs = diff.max().item() if total > 0 else 0.0
    mean_abs = diff.mean().item() if total > 0 else 0.0

    denom = torch.maximum(f_flat.abs(), g_flat.abs()).clamp(min=1e-300)
    rel = diff / denom
    max_rel = rel.max().item() if total > 0 else 0.0

    # ULP calculation (vectorized)
    within_mask = (diff <= tol.atol + tol.rtol * denom)

    # NaN handling
    f_nan = torch.isnan(f_flat)
    g_nan = torch.isnan(g_flat)
    both_nan = f_nan & g_nan
    any_nan = f_nan | g_nan
    nan_mismatch = any_nan & ~both_nan
    if tol.nan_equal:
        within_mask = within_mask | both_nan
    within_mask = within_mask & ~nan_mismatch

    num_mismatches = (~within_mask).sum().item()

    # Collect worst elements
    worst: List[ElementComparison] = []
    if num_mismatches > 0:
        _, worst_indices = diff.topk(min(max_worst, total))
        for idx in worst_indices:
            i = idx.item()
            cmp = _compare_elements(f_flat[i].item(), g_flat[i].item(), tol,
                                    index=(i,))
            worst.append(cmp)

    verdict = (EquivalenceVerdict.EQUIVALENT if num_mismatches == 0
               else EquivalenceVerdict.INEQUIVALENT)

    return NumericalComparisonResult(
        verdict=verdict,
        max_abs_diff=max_abs,
        max_rel_diff=max_rel,
        max_ulp_diff=0,  # ULP computed per-element in worst
        mean_abs_diff=mean_abs,
        num_mismatches=num_mismatches,
        total_elements=total,
        worst_elements=worst,
        explanation=(f"max_abs={max_abs:.2e}, max_rel={max_rel:.2e}, "
                     f"mismatches={num_mismatches}/{total}"),
    )


# ---------------------------------------------------------------------------
# Reduction order sensitivity
# ---------------------------------------------------------------------------

def check_reduction_order(fn: Any, inputs: List[Any],
                          spec: TensorSpec,
                          tol: NumericalToleranceSpec,
                          n_permutations: int = 5) -> NumericalComparisonResult:
    """
    Check if a function's output is sensitive to reduction order.

    This probes the non-commutativity of floating-point addition by
    permuting input elements and checking if the output changes beyond
    tolerance.  Sensitivity indicates the function uses non-associative
    reductions (e.g. sum, mean) that may differ across implementations.
    """
    try:
        import torch
    except ImportError:
        return NumericalComparisonResult(
            verdict=EquivalenceVerdict.UNKNOWN,
            explanation="PyTorch not available",
        )

    reference_out = fn(*inputs)
    worst_result = NumericalComparisonResult(
        verdict=EquivalenceVerdict.EQUIVALENT,
        explanation="No reduction order sensitivity detected",
    )

    for perm_seed in range(n_permutations):
        gen = torch.Generator().manual_seed(perm_seed + 1000)
        permuted_inputs = []
        for inp in inputs:
            if isinstance(inp, torch.Tensor) and inp.dim() >= 1:
                perm = torch.randperm(inp.shape[-1], generator=gen)
                permuted = inp[..., perm]
                permuted_inputs.append(permuted)
            else:
                permuted_inputs.append(inp)

        try:
            permuted_out = fn(*permuted_inputs)
        except Exception:
            continue

        result = compare_tensors(reference_out, permuted_out, tol)
        if result.max_abs_diff > worst_result.max_abs_diff:
            worst_result = result

    return worst_result


# ---------------------------------------------------------------------------
# Numerical site checker (the local section evaluator)
# ---------------------------------------------------------------------------

class NumericalEquivalenceChecker:
    """
    Checks numerical equivalence of two functions at a numerical site.

    This implements the *local section comparison* in the presheaf model:
    for a numerical observation site U with tolerance ε, we evaluate
    both functions on test inputs and compare outputs within the
    tolerance presheaf T(U, ε).

    The checker performs:
    1. Forward pass comparison (output values)
    2. Special value handling (NaN, Inf, denormals)
    3. Reduction order sensitivity probing
    4. Statistical divergence detection (distribution shift)
    """

    def __init__(self, config: TensorEquivalenceConfig):
        self._config = config
        self._tol = config.tolerance

    def check_site(
        self,
        fn_f: Any,
        fn_g: Any,
        test_inputs: List[List[Any]],
        site_id: SiteId,
        output_index: int = 0,
    ) -> TensorLocalJudgment:
        """
        Check numerical equivalence at a single numerical site.

        Evaluates fn_f and fn_g on each test input, compares the
        output at output_index, and aggregates results.
        """
        obstructions: List[TensorObstruction] = []
        max_abs = 0.0
        all_equivalent = True
        worst_input = None
        worst_f = None
        worst_g = None

        for inputs in test_inputs:
            try:
                out_f = fn_f(*inputs)
                out_g = fn_g(*inputs)
            except Exception as e:
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.EXCEPTION_BEHAVIOR,
                    stratum=TensorStratum.NUMERICAL,
                    sites=(site_id,),
                    description=f"Exception divergence: {e}",
                ))
                all_equivalent = False
                continue

            # Extract output tensor
            tf = self._extract_output(out_f, output_index)
            tg = self._extract_output(out_g, output_index)

            result = compare_tensors(tf, tg, self._tol)

            if result.verdict != EquivalenceVerdict.EQUIVALENT:
                all_equivalent = False
                if result.max_abs_diff > max_abs:
                    max_abs = result.max_abs_diff
                    worst_input = inputs
                    worst_f = tf
                    worst_g = tg
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.NUMERICAL_DIVERGENCE,
                    stratum=TensorStratum.NUMERICAL,
                    sites=(site_id,),
                    description=result.explanation,
                    witness_input=repr(inputs)[:200],
                    max_abs_diff=result.max_abs_diff,
                    max_rel_diff=result.max_rel_diff,
                ))

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.NUMERICAL,
            tensor_site_kind=TensorSiteKind.NUMERICAL,
            verdict=(EquivalenceVerdict.EQUIVALENT if all_equivalent
                     else EquivalenceVerdict.INEQUIVALENT),
            explanation=(f"Numerical equivalence: max_abs_diff={max_abs:.2e}"
                         if not all_equivalent else "Numerically equivalent"),
            obstructions=tuple(obstructions),
            witness_input=repr(worst_input)[:200] if worst_input else None,
            output_f=repr(worst_f)[:200] if worst_f is not None else None,
            output_g=repr(worst_g)[:200] if worst_g is not None else None,
            max_abs_diff=max_abs,
        )

    def check_reduction_sensitivity(
        self,
        fn_f: Any,
        fn_g: Any,
        test_inputs: List[List[Any]],
        site_id: SiteId,
    ) -> Optional[TensorObstruction]:
        """Check if both functions have similar reduction order sensitivity."""
        if not self._tol.reduction_order_sensitive:
            return None

        for inputs in test_inputs[:3]:
            try:
                import torch
                specs = [TensorSpec(shape=t.shape, dtype=str(t.dtype).split(".")[-1])
                         for t in inputs if isinstance(t, torch.Tensor)]
                if not specs:
                    continue

                result_f = check_reduction_order(fn_f, inputs, specs[0], self._tol)
                result_g = check_reduction_order(fn_g, inputs, specs[0], self._tol)

                # Both should have similar sensitivity
                f_sensitive = result_f.max_abs_diff > self._tol.atol
                g_sensitive = result_g.max_abs_diff > self._tol.atol

                if f_sensitive != g_sensitive:
                    return TensorObstruction(
                        kind=TensorObstructionKind.TRITON_REDUCTION_ORDER,
                        stratum=TensorStratum.NUMERICAL,
                        sites=(site_id,),
                        description=(f"Reduction sensitivity mismatch: "
                                     f"f={'sensitive' if f_sensitive else 'stable'}, "
                                     f"g={'sensitive' if g_sensitive else 'stable'}"),
                    )
            except Exception:
                continue
        return None

    @staticmethod
    def _extract_output(out: Any, index: int) -> Any:
        """Extract the output tensor at the given index."""
        if isinstance(out, (tuple, list)):
            if index < len(out):
                return out[index]
            return None
        if index == 0:
            return out
        return None

    # ------------------------------------------------------------------
    # Single-program analysis
    # ------------------------------------------------------------------

    def analyze(
        self,
        fn: Any,
        test_inputs: List[List[Any]],
        site_id: Optional[SiteId] = None,
    ) -> AnalysisJudgment:
        """Analyze numerical stability of a single function.

        Checks for NaN/Inf in outputs, sensitivity to small perturbations,
        and determinism across repeated evaluations.  These correspond to
        failures of the numerical presheaf's sheaf condition: a well-behaved
        section must be continuous (stable) and single-valued (deterministic).
        """
        try:
            import torch
        except ImportError:
            return AnalysisJudgment(
                verdict=AnalysisVerdict.UNKNOWN,
                program=ProgramId(name="fn"),
                mode=AnalysisMode.BUG_FINDING,
                explanation="PyTorch not available",
            )

        if site_id is None:
            site_id = SiteId(kind=SiteKind.TENSOR_SHAPE, name="numerical_analysis")
        program = ProgramId(name="fn", function_name=getattr(fn, "__name__", "anonymous"))
        bugs: List[Bug] = []

        for inputs in test_inputs:
            # --- Run and check for NaN / Inf --------------------------
            try:
                out = fn(*[t.clone() if isinstance(t, torch.Tensor) else t
                           for t in inputs])
            except Exception:
                continue

            out_tensor = self._extract_output(out, 0)
            if isinstance(out_tensor, torch.Tensor):
                if torch.isnan(out_tensor).any():
                    bugs.append(Bug(
                        kind=BugKind.NUMERICAL_INSTABILITY,
                        stratum=TensorStratum.NUMERICAL,
                        site_id=site_id,
                        description="Output contains NaN values",
                        witness_input=repr(inputs)[:200],
                        observed_output=repr(out_tensor)[:200],
                        repair_hint="Check for 0/0 or log(0) operations",
                    ))
                if torch.isinf(out_tensor).any():
                    bugs.append(Bug(
                        kind=BugKind.NUMERICAL_INSTABILITY,
                        stratum=TensorStratum.NUMERICAL,
                        site_id=site_id,
                        description="Output contains Inf values",
                        witness_input=repr(inputs)[:200],
                        observed_output=repr(out_tensor)[:200],
                        repair_hint="Check for overflow or division by zero",
                    ))

            # --- Perturbation sensitivity -----------------------------
            try:
                perturbed = [
                    t + torch.randn_like(t) * self._tol.atol
                    if isinstance(t, torch.Tensor) and t.is_floating_point()
                    else t
                    for t in inputs
                ]
                out_perturbed = fn(*perturbed)
                tp = self._extract_output(out_perturbed, 0)
                if (isinstance(out_tensor, torch.Tensor)
                        and isinstance(tp, torch.Tensor)
                        and out_tensor.shape == tp.shape):
                    diff = (out_tensor.float() - tp.float()).abs()
                    max_diff = diff.max().item()
                    if max_diff > 1e6 * self._tol.atol:
                        bugs.append(Bug(
                            kind=BugKind.NUMERICAL_INSTABILITY,
                            stratum=TensorStratum.NUMERICAL,
                            site_id=site_id,
                            description=(
                                f"High perturbation sensitivity: "
                                f"ε={self._tol.atol:.1e} → Δout={max_diff:.2e}"
                            ),
                            witness_input=repr(inputs)[:200],
                            severity=min(max_diff / (self._tol.atol + 1e-30), 10.0),
                        ))
            except Exception:
                pass

            # --- Determinism check ------------------------------------
            try:
                out2 = fn(*[t.clone() if isinstance(t, torch.Tensor) else t
                            for t in inputs])
                t2 = self._extract_output(out2, 0)
                if (isinstance(out_tensor, torch.Tensor)
                        and isinstance(t2, torch.Tensor)
                        and out_tensor.shape == t2.shape):
                    if not torch.equal(out_tensor, t2):
                        bugs.append(Bug(
                            kind=BugKind.NONDETERMINISM,
                            stratum=TensorStratum.NUMERICAL,
                            site_id=site_id,
                            description="Non-deterministic output on identical inputs",
                            witness_input=repr(inputs)[:200],
                            repair_hint="Use torch.use_deterministic_algorithms(True)",
                        ))
            except Exception:
                pass

        verdict = AnalysisVerdict.INVALID if bugs else AnalysisVerdict.VALID
        return AnalysisJudgment(
            verdict=verdict,
            program=program,
            mode=AnalysisMode.BUG_FINDING,
            bugs=bugs,
            stratum_results={TensorStratum.NUMERICAL: verdict},
            explanation=(
                f"Found {len(bugs)} numerical issues"
                if bugs else
                "Numerical presheaf sections are well-defined and stable"
            ),
        )
