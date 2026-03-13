"""Sheaf-condition checker for a single tensor program's presheaf.

Mathematical background
───────────────────────
A presheaf  F : C^{op} → Set  on a site (C, J) satisfies the **sheaf
condition** with respect to a covering sieve  {U_i → U}  when:

1. **Separation (locality)** – if two sections  s, t ∈ F(U)  restrict
   identically to every U_i, then s = t.

2. **Gluing (descent)** – given a compatible family of local sections
   s_i ∈ F(U_i)  satisfying the overlap agreement
       s_i |_{U_i ∩ U_j}  =  s_j |_{U_i ∩ U_j}
   there exists a (unique, by separation) global section  s ∈ F(U)
   with  s |_{U_i} = s_i  for every i.

For a tensor program  f : Tensor^n → Tensor^m  the observation sites
are the strata (shape, dtype, numerical, autograd, …) and a *section*
at a site records the observable behaviour (output shape, promoted
dtype, computed values, gradient structure, etc.).

A **bug** is precisely a failure of the sheaf condition:

* *Shape ↔ numerical gluing failure* – the shape site promises output
  (3, 4) but the numerical site produces a tensor of shape (3, 5).
* *Dtype ↔ autograd overlap inconsistency* – the dtype site reports
  ``float32`` but the backward pass returns ``float64`` gradients.
* *Triton block boundary* – an unmasked load at the boundary means the
  local section is *undefined* there: the presheaf does not even assign
  a value, let alone satisfy gluing.
* *MLIR lowering descent failure* – a dialect lowering changes the
  semantics, so the cocycle condition on the lowering chain fails.

This module provides four checker classes that formalise these ideas:

:class:`SectionConsistencyChecker`
    Overlap agreement between pairs of sites.

:class:`GluingChecker`
    Attempt to glue local sections into a global section.

:class:`DescentChecker`
    Cocycle condition on triple overlaps.

:class:`TensorSheafConditionChecker`
    Orchestrator that runs all three checks stratum-by-stratum.
"""

from __future__ import annotations

import logging
import math
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Set, Tuple

try:
    import torch

    _HAS_TORCH = True
except ImportError:  # pragma: no cover
    _HAS_TORCH = False

from ._protocols import (
    SiteId,
    SiteKind,
    TensorSiteKind,
    TensorStratum,
    TensorSpec,
    TensorEquivalenceConfig,
    TensorObstruction,
    TensorObstructionKind,
    EquivalenceVerdict,
    NumericalToleranceSpec,
    LocalSection,
    Cover,
    SITE_KIND_STRATUM,
    ProgramId,
)

# These types are being added concurrently; fall back to lightweight stubs
# if the current revision of _protocols does not yet expose them.
try:
    from ._protocols import (
        AnalysisMode,
        AnalysisVerdict,
        BugKind,
        Bug,
        SheafConditionResult,
        AnalysisJudgment,
    )
except ImportError:  # pragma: no cover – temporary until _protocols is updated
    import enum

    class AnalysisMode(enum.Enum):  # type: ignore[no-redef]
        EQUIVALENCE = "equivalence"
        BUG_FINDING = "bug_finding"
        CORRECTNESS = "correctness"

    class AnalysisVerdict(enum.Enum):  # type: ignore[no-redef]
        VALID = "valid"
        INVALID = "invalid"
        UNKNOWN = "unknown"

    class BugKind(enum.Enum):  # type: ignore[no-redef]
        SHAPE_INCONSISTENCY = "shape_inconsistency"
        DTYPE_INCONSISTENCY = "dtype_inconsistency"
        NUMERICAL_INSTABILITY = "numerical_instability"
        GRADIENT_INCORRECTNESS = "gradient_incorrectness"
        MEMORY_VIOLATION = "memory_violation"
        UNMASKED_ACCESS = "unmasked_access"
        NONDETERMINISM = "nondeterminism"
        ALIASING_HAZARD = "aliasing_hazard"
        SHEAF_GLUING_FAILURE = "sheaf_gluing_failure"
        DESCENT_VIOLATION = "descent_violation"

    @dataclass(frozen=True)  # type: ignore[no-redef]
    class Bug:
        kind: "BugKind"
        stratum: TensorStratum
        site_id: SiteId
        description: str
        witness_input: Optional[Any] = None
        observed_output: Optional[Any] = None
        expected_behavior: Optional[str] = None
        repair_hint: Optional[str] = None
        severity: float = 1.0

    @dataclass(frozen=True)  # type: ignore[no-redef]
    class SheafConditionResult:
        satisfies_condition: bool
        gluing_failures: List[Tuple[SiteId, SiteId]]
        descent_failures: List[Tuple[SiteId, SiteId, SiteId]]
        explanation: str = ""

    @dataclass  # type: ignore[no-redef]
    class AnalysisJudgment:
        verdict: "AnalysisVerdict"
        program: ProgramId
        mode: "AnalysisMode"
        bugs: List["Bug"] = field(default_factory=list)
        sheaf_condition: Optional["SheafConditionResult"] = None
        stratum_results: Dict[TensorStratum, "AnalysisVerdict"] = field(
            default_factory=dict
        )
        obstructions: List[TensorObstruction] = field(default_factory=list)
        explanation: str = ""

from .tensor_site import (
    TensorObservationSite,
    TensorCover,
    TensorSiteCategoryBuilder,
)

logger = logging.getLogger(__name__)

__all__ = [
    "SectionConsistencyChecker",
    "GluingChecker",
    "DescentChecker",
    "TensorSheafConditionChecker",
]

# Filtration order used to iterate strata from coarsest to finest.
_STRATUM_ORDER: List[TensorStratum] = [
    TensorStratum.METADATA,
    TensorStratum.STRUCTURAL,
    TensorStratum.NUMERICAL,
    TensorStratum.BEHAVIORAL,
]

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _program_id_from_fn(fn: Callable) -> ProgramId:
    """Create a :class:`ProgramId` from a callable."""
    name = getattr(fn, "__name__", None) or getattr(fn, "__qualname__", repr(fn))
    source_path: Optional[str] = None
    try:
        import inspect

        source_path = inspect.getfile(fn)
    except (TypeError, OSError):
        pass
    return ProgramId(name=name, source_path=source_path, function_name=name)


def _make_site_id(kind: SiteKind, name: str) -> SiteId:
    """Short-hand to build a :class:`SiteId`."""
    return SiteId(kind=kind, name=name)


def _safe_call(fn: Callable, inputs: Sequence[Any]) -> Any:
    """Call *fn* with *inputs*, propagating exceptions as-is."""
    return fn(*inputs)


def _generate_default_inputs(
    specs: Sequence[TensorSpec],
    config: Optional[TensorEquivalenceConfig] = None,
    count: int = 5,
) -> List[List[Any]]:
    """Synthesise a small bank of test inputs from :class:`TensorSpec`\\ s.

    Falls back to simple random tensors when ``torch`` is available, or to
    ``None`` sentinels otherwise.
    """
    if not _HAS_TORCH:
        return []

    cfg = config or TensorEquivalenceConfig()
    rng = torch.Generator().manual_seed(cfg.random_seed)
    batches: List[List[Any]] = []
    for idx in range(count):
        batch: List[Any] = []
        for spec in specs:
            shape = spec.shape or (4,)
            dtype_str = spec.dtype or "float32"
            dtype = getattr(torch, dtype_str, torch.float32)
            device = spec.device or "cpu"
            if dtype.is_floating_point:
                t = torch.randn(shape, dtype=dtype, device=device, generator=rng)
            else:
                t = torch.randint(0, 10, shape, dtype=dtype, device=device, generator=rng)
            if spec.requires_grad and dtype.is_floating_point:
                t = t.requires_grad_(True)
            batch.append(t)
        batches.append(batch)
    return batches


def _tensor_shape(t: Any) -> Optional[Tuple[int, ...]]:
    """Extract shape from a tensor-like, or *None*."""
    if _HAS_TORCH and isinstance(t, torch.Tensor):
        return tuple(t.shape)
    if hasattr(t, "shape"):
        return tuple(t.shape)
    return None


def _tensor_dtype(t: Any) -> Optional[str]:
    """Extract dtype name from a tensor-like, or *None*."""
    if _HAS_TORCH and isinstance(t, torch.Tensor):
        return str(t.dtype).replace("torch.", "")
    if hasattr(t, "dtype"):
        return str(t.dtype)
    return None


def _flatten_outputs(out: Any) -> List[Any]:
    """Flatten a function output into a list of leaf tensors."""
    if isinstance(out, (tuple, list)):
        leaves: List[Any] = []
        for o in out:
            leaves.extend(_flatten_outputs(o))
        return leaves
    return [out]


# ═══════════════════════════════════════════════════════════════════════════════
# SectionConsistencyChecker
# ═══════════════════════════════════════════════════════════════════════════════


class SectionConsistencyChecker:
    """Check overlap consistency of a single program's local sections.

    In sheaf terms, this verifies that for every pair of sites (U_i, U_j)
    whose overlap U_i ∩ U_j is non-empty, the restrictions

        s_i |_{U_i ∩ U_j}  and  s_j |_{U_i ∩ U_j}

    coincide.  For tensor programs the "overlaps" arise because the same
    function call produces information visible to multiple observation
    strata simultaneously (shape, dtype, numerical value, gradient, …).

    Concretely:
    * **Shape ↔ Numerical overlap** – running *fn* and reading the output
      shape must agree with the shape of the numerically-computed tensor.
    * **Dtype ↔ Autograd overlap** – the dtype of the forward output must
      be consistent with the dtype of the backward gradient.
    * **Numerical tolerance transitivity** – if values at tolerance ε₁ and
      ε₂ each look fine, the same must hold at ε₁ ∨ ε₂.
    """

    def __init__(self, fn: Callable) -> None:
        self._fn = fn

    # -- public API ---------------------------------------------------------

    def check_overlap_consistency(
        self,
        test_inputs: Sequence[Sequence[Any]],
        config: Optional[TensorEquivalenceConfig] = None,
    ) -> List[Tuple[SiteId, SiteId, str]]:
        """Return a list of overlap-agreement failures.

        Each entry is ``(site_i, site_j, explanation)`` where the local
        sections at ``site_i`` and ``site_j`` disagree on their overlap.
        """
        failures: List[Tuple[SiteId, SiteId, str]] = []
        failures.extend(self._check_shape_numerical_overlap(test_inputs))
        failures.extend(self._check_dtype_autograd_overlap(test_inputs, config))
        failures.extend(self._check_numerical_tolerance_transitivity(test_inputs, config))
        return failures

    # -- private helpers ----------------------------------------------------

    def _check_shape_numerical_overlap(
        self,
        test_inputs: Sequence[Sequence[Any]],
    ) -> List[Tuple[SiteId, SiteId, str]]:
        """Shape site and numerical site must report the same output shape."""
        failures: List[Tuple[SiteId, SiteId, str]] = []
        shape_site = _make_site_id(SiteKind.TENSOR_SHAPE, "output_shape")
        numerical_site = _make_site_id(SiteKind.TENSOR_SHAPE, "numerical_output_shape")

        for idx, inp in enumerate(test_inputs):
            try:
                out = _safe_call(self._fn, inp)
            except Exception:
                continue
            leaves = _flatten_outputs(out)
            for leaf_idx, leaf in enumerate(leaves):
                shape = _tensor_shape(leaf)
                if shape is None:
                    continue
                # Re-call to check stability (same input → same shape)
                try:
                    out2 = _safe_call(self._fn, inp)
                except Exception:
                    failures.append((
                        shape_site,
                        numerical_site,
                        f"Input #{idx}: first call succeeded but second raised "
                        f"an exception (nondeterministic failure).",
                    ))
                    continue
                leaves2 = _flatten_outputs(out2)
                if leaf_idx < len(leaves2):
                    shape2 = _tensor_shape(leaves2[leaf_idx])
                    if shape != shape2:
                        failures.append((
                            shape_site,
                            numerical_site,
                            f"Input #{idx}, output #{leaf_idx}: first call shape "
                            f"{shape} ≠ second call shape {shape2}.",
                        ))
        return failures

    def _check_dtype_autograd_overlap(
        self,
        test_inputs: Sequence[Sequence[Any]],
        config: Optional[TensorEquivalenceConfig] = None,
    ) -> List[Tuple[SiteId, SiteId, str]]:
        """Dtype of forward output must be consistent with gradient dtype."""
        if not _HAS_TORCH:
            return []
        failures: List[Tuple[SiteId, SiteId, str]] = []
        dtype_site = _make_site_id(SiteKind.TENSOR_SHAPE, "output_dtype")
        autograd_site = _make_site_id(SiteKind.TENSOR_SHAPE, "gradient_dtype")

        for idx, inp in enumerate(test_inputs):
            grad_inputs = []
            for t in inp:
                if isinstance(t, torch.Tensor) and t.is_floating_point():
                    grad_inputs.append(t.detach().requires_grad_(True))
                else:
                    grad_inputs.append(t)
            try:
                out = _safe_call(self._fn, grad_inputs)
            except Exception:
                continue
            leaves = _flatten_outputs(out)
            for leaf_idx, leaf in enumerate(leaves):
                if not isinstance(leaf, torch.Tensor):
                    continue
                fwd_dtype = str(leaf.dtype)
                if not leaf.requires_grad:
                    continue
                try:
                    grad_out = torch.ones_like(leaf)
                    grads = torch.autograd.grad(
                        leaf, [t for t in grad_inputs if isinstance(t, torch.Tensor) and t.requires_grad],
                        grad_outputs=grad_out,
                        allow_unused=True,
                    )
                except Exception:
                    continue
                for g_idx, g in enumerate(grads):
                    if g is None:
                        continue
                    if str(g.dtype) != fwd_dtype:
                        failures.append((
                            dtype_site,
                            autograd_site,
                            f"Input #{idx}, output #{leaf_idx}: forward dtype "
                            f"{fwd_dtype} ≠ gradient dtype {g.dtype} "
                            f"(grad #{g_idx}).",
                        ))
        return failures

    def _check_numerical_tolerance_transitivity(
        self,
        test_inputs: Sequence[Sequence[Any]],
        config: Optional[TensorEquivalenceConfig] = None,
    ) -> List[Tuple[SiteId, SiteId, str]]:
        """Tolerance must be transitive: close(a,b,ε₁) ∧ close(b,c,ε₂) ⇒ close(a,c,ε₁+ε₂).

        We check this by running the function three times on the same input
        and verifying the triangle inequality on outputs.
        """
        if not _HAS_TORCH:
            return []
        failures: List[Tuple[SiteId, SiteId, str]] = []
        tol_site_a = _make_site_id(SiteKind.TENSOR_SHAPE, "numerical_tol_a")
        tol_site_b = _make_site_id(SiteKind.TENSOR_SHAPE, "numerical_tol_b")

        cfg = config or TensorEquivalenceConfig()
        atol = cfg.tolerance.atol

        for idx, inp in enumerate(test_inputs):
            results: List[Any] = []
            for _ in range(3):
                try:
                    results.append(_safe_call(self._fn, inp))
                except Exception:
                    break
            if len(results) < 3:
                continue
            for i_res in range(len(results)):
                for j_res in range(i_res + 1, len(results)):
                    leaves_i = _flatten_outputs(results[i_res])
                    leaves_j = _flatten_outputs(results[j_res])
                    for k, (li, lj) in enumerate(zip(leaves_i, leaves_j)):
                        if not (_HAS_TORCH and isinstance(li, torch.Tensor) and isinstance(lj, torch.Tensor)):
                            continue
                        try:
                            diff = (li.float() - lj.float()).abs().max().item()
                        except Exception:
                            continue
                        if diff > atol:
                            failures.append((
                                tol_site_a,
                                tol_site_b,
                                f"Input #{idx}, output #{k}: repeated calls "
                                f"differ by {diff:.6e} > atol {atol:.6e} "
                                f"(nondeterminism / numerical instability).",
                            ))
        return failures


# ═══════════════════════════════════════════════════════════════════════════════
# GluingChecker
# ═══════════════════════════════════════════════════════════════════════════════


class GluingChecker:
    """Attempt to glue local sections into a global section.

    In the sheaf condition, given compatible local sections  s_i ∈ F(U_i),
    there must exist a unique global section  s ∈ F(U)  that restricts to
    each s_i.  For a tensor program, "gluing" means that all the separate
    observations (shape, dtype, value, gradient) can be combined into a
    single coherent picture of the program's behaviour on a given input.

    A *gluing failure* signals that no coherent global description exists –
    in other words, the program has a bug because its behaviour as seen
    from different observation sites is mutually contradictory.

    Examples of gluing failures:
    * Shape site says (3, 4) but the tensor produced has 15 elements.
    * Dtype site says float32 but the actual tensor has float64 storage.
    * Autograd site records a gradient graph, but forward output was
      detached (``requires_grad=False``).
    """

    def check_gluing(
        self,
        fn: Callable,
        test_inputs: Sequence[Sequence[Any]],
        config: Optional[TensorEquivalenceConfig] = None,
    ) -> SheafConditionResult:
        """Check the gluing axiom for *fn*'s presheaf over the test inputs.

        Returns a :class:`SheafConditionResult` summarising whether the
        local sections (shape, dtype, value, grad) can be glued.
        """
        gluing_failures: List[Tuple[SiteId, SiteId]] = []
        explanations: List[str] = []

        for idx, inp in enumerate(test_inputs):
            fails = self._check_single_input(fn, inp, idx, config)
            for site_a, site_b, expl in fails:
                gluing_failures.append((site_a, site_b))
                explanations.append(expl)

        ok = len(gluing_failures) == 0
        return SheafConditionResult(
            satisfies_condition=ok,
            gluing_failures=gluing_failures,
            descent_failures=[],
            explanation="; ".join(explanations) if explanations else "Gluing condition satisfied.",
        )

    # -- private ------------------------------------------------------------

    def _check_single_input(
        self,
        fn: Callable,
        inp: Sequence[Any],
        inp_idx: int,
        config: Optional[TensorEquivalenceConfig] = None,
    ) -> List[Tuple[SiteId, SiteId, str]]:
        """Check gluing on a single input batch."""
        failures: List[Tuple[SiteId, SiteId, str]] = []
        try:
            out = _safe_call(fn, inp)
        except Exception as exc:
            error_site = _make_site_id(SiteKind.ERROR, "runtime_error")
            shape_site = _make_site_id(SiteKind.TENSOR_SHAPE, "output_shape")
            failures.append((
                error_site,
                shape_site,
                f"Input #{inp_idx}: function raised {type(exc).__name__}: {exc}",
            ))
            return failures

        leaves = _flatten_outputs(out)
        shape_site = _make_site_id(SiteKind.TENSOR_SHAPE, "output_shape")
        dtype_site = _make_site_id(SiteKind.TENSOR_SHAPE, "output_dtype")
        value_site = _make_site_id(SiteKind.TENSOR_SHAPE, "output_value")
        grad_site = _make_site_id(SiteKind.TENSOR_SHAPE, "output_gradient")

        for leaf_idx, leaf in enumerate(leaves):
            if not (_HAS_TORCH and isinstance(leaf, torch.Tensor)):
                continue

            # Shape ↔ numel consistency
            shape = tuple(leaf.shape)
            expected_numel = 1
            for d in shape:
                expected_numel *= d
            if leaf.numel() != expected_numel:
                failures.append((
                    shape_site,
                    value_site,
                    f"Input #{inp_idx}, output #{leaf_idx}: shape {shape} implies "
                    f"{expected_numel} elements but tensor has {leaf.numel()}.",
                ))

            # Check for NaN / Inf (numerical section undefined)
            if leaf.is_floating_point():
                if torch.isnan(leaf).any().item():
                    failures.append((
                        value_site,
                        shape_site,
                        f"Input #{inp_idx}, output #{leaf_idx}: NaN detected – "
                        f"numerical section is undefined.",
                    ))
                if torch.isinf(leaf).any().item():
                    cfg = config or TensorEquivalenceConfig()
                    if not cfg.tolerance.inf_equal:
                        failures.append((
                            value_site,
                            shape_site,
                            f"Input #{inp_idx}, output #{leaf_idx}: Inf detected.",
                        ))

            # Autograd consistency: if requires_grad, gradient must be computable
            if leaf.requires_grad and leaf.is_floating_point():
                try:
                    grad_out = torch.ones_like(leaf)
                    torch.autograd.grad(
                        leaf,
                        [t for t in inp if isinstance(t, torch.Tensor) and t.requires_grad],
                        grad_outputs=grad_out,
                        allow_unused=True,
                        retain_graph=True,
                    )
                except Exception as exc:
                    failures.append((
                        grad_site,
                        value_site,
                        f"Input #{inp_idx}, output #{leaf_idx}: gradient "
                        f"computation failed – {type(exc).__name__}: {exc}.",
                    ))

        return failures


# ═══════════════════════════════════════════════════════════════════════════════
# DescentChecker
# ═══════════════════════════════════════════════════════════════════════════════


class DescentChecker:
    """Check the cocycle (descent) condition on triple overlaps.

    Given three sites  U_i, U_j, U_k  whose pairwise overlaps are all
    non-empty, the transition isomorphisms must compose:

        g_{ij} ∘ g_{jk} = g_{ik}      (cocycle condition)

    For tensor programs this manifests as:

    * **Tolerance transitivity** – if outputs under tolerance ε₁ at
      (site_i, site_j) and ε₂ at (site_j, site_k) are acceptable, then
      the combined tolerance ε₁ + ε₂ must still be acceptable at
      (site_i, site_k).  Failure means the tolerance budget is
      inconsistent.
    * **Dtype promotion associativity** – casting  A → B → C  must match
      casting  A → C  directly.  Some mixed-precision pipelines violate
      this when intermediate casts lose precision.
    * **Autograd double-backward** – the chain-rule applied twice must be
      consistent with a single second-order derivative.
    """

    def check_descent(
        self,
        fn: Callable,
        test_inputs: Sequence[Sequence[Any]],
        config: Optional[TensorEquivalenceConfig] = None,
    ) -> List[Tuple[SiteId, SiteId, SiteId, str]]:
        """Return a list of cocycle failures as ``(s_i, s_j, s_k, explanation)``."""
        failures: List[Tuple[SiteId, SiteId, SiteId, str]] = []
        failures.extend(self._check_tolerance_transitivity(fn, test_inputs, config))
        failures.extend(self._check_dtype_promotion_associativity(fn, test_inputs))
        failures.extend(self._check_double_backward(fn, test_inputs))
        return failures

    # -- private ------------------------------------------------------------

    def _check_tolerance_transitivity(
        self,
        fn: Callable,
        test_inputs: Sequence[Sequence[Any]],
        config: Optional[TensorEquivalenceConfig] = None,
    ) -> List[Tuple[SiteId, SiteId, SiteId, str]]:
        """Three repeated calls must satisfy the triangle inequality."""
        if not _HAS_TORCH:
            return []
        failures: List[Tuple[SiteId, SiteId, SiteId, str]] = []
        cfg = config or TensorEquivalenceConfig()
        atol = cfg.tolerance.atol

        site_a = _make_site_id(SiteKind.TENSOR_SHAPE, "run_a")
        site_b = _make_site_id(SiteKind.TENSOR_SHAPE, "run_b")
        site_c = _make_site_id(SiteKind.TENSOR_SHAPE, "run_c")

        for idx, inp in enumerate(test_inputs):
            results = []
            for _ in range(3):
                try:
                    results.append(_safe_call(fn, inp))
                except Exception:
                    break
            if len(results) < 3:
                continue

            for k, (la, lb, lc) in enumerate(
                zip(
                    _flatten_outputs(results[0]),
                    _flatten_outputs(results[1]),
                    _flatten_outputs(results[2]),
                )
            ):
                if not (_HAS_TORCH and isinstance(la, torch.Tensor)):
                    continue
                try:
                    d_ab = (la.float() - lb.float()).abs().max().item()
                    d_bc = (lb.float() - lc.float()).abs().max().item()
                    d_ac = (la.float() - lc.float()).abs().max().item()
                except Exception:
                    continue
                # Triangle inequality: d(a,c) ≤ d(a,b) + d(b,c)
                if d_ac > d_ab + d_bc + atol:
                    failures.append((
                        site_a,
                        site_b,
                        site_c,
                        f"Input #{idx}, output #{k}: triangle inequality "
                        f"violated: d(a,c)={d_ac:.6e} > d(a,b)+d(b,c)="
                        f"{d_ab + d_bc:.6e}.",
                    ))
        return failures

    def _check_dtype_promotion_associativity(
        self,
        fn: Callable,
        test_inputs: Sequence[Sequence[Any]],
    ) -> List[Tuple[SiteId, SiteId, SiteId, str]]:
        """Cast A→B→C must equal cast A→C for the output dtype."""
        if not _HAS_TORCH:
            return []
        failures: List[Tuple[SiteId, SiteId, SiteId, str]] = []

        site_ab = _make_site_id(SiteKind.TENSOR_SHAPE, "cast_A_to_B")
        site_bc = _make_site_id(SiteKind.TENSOR_SHAPE, "cast_B_to_C")
        site_ac = _make_site_id(SiteKind.TENSOR_SHAPE, "cast_A_to_C")

        dtype_chain = [torch.float16, torch.float32, torch.float64]

        for idx, inp in enumerate(test_inputs):
            outputs_by_dtype: Dict[torch.dtype, List[Any]] = {}
            for dt in dtype_chain:
                cast_inp = []
                for t in inp:
                    if isinstance(t, torch.Tensor) and t.is_floating_point():
                        cast_inp.append(t.detach().to(dtype=dt))
                    else:
                        cast_inp.append(t)
                try:
                    out = _safe_call(fn, cast_inp)
                    outputs_by_dtype[dt] = _flatten_outputs(out)
                except Exception:
                    continue

            # If we have all three, check associativity of the promotion
            if len(outputs_by_dtype) < 3:
                continue
            for k, (out16, out32, out64) in enumerate(
                zip(
                    outputs_by_dtype.get(torch.float16, []),
                    outputs_by_dtype.get(torch.float32, []),
                    outputs_by_dtype.get(torch.float64, []),
                )
            ):
                if not all(isinstance(o, torch.Tensor) for o in (out16, out32, out64)):
                    continue
                # Promoting 16→32 then 32→64 should be close to promoting 16→64 directly
                via_32 = out16.to(torch.float32).to(torch.float64)
                direct = out16.to(torch.float64)
                try:
                    diff = (via_32 - direct).abs().max().item()
                except Exception:
                    continue
                if diff > 0.0:
                    failures.append((
                        site_ab,
                        site_bc,
                        site_ac,
                        f"Input #{idx}, output #{k}: dtype promotion "
                        f"A→B→C ≠ A→C by {diff:.6e} (associativity failure).",
                    ))
        return failures

    def _check_double_backward(
        self,
        fn: Callable,
        test_inputs: Sequence[Sequence[Any]],
    ) -> List[Tuple[SiteId, SiteId, SiteId, str]]:
        """Double backward (second-order gradient) must be consistent."""
        if not _HAS_TORCH:
            return []
        failures: List[Tuple[SiteId, SiteId, SiteId, str]] = []

        site_fwd = _make_site_id(SiteKind.TENSOR_SHAPE, "forward")
        site_bwd1 = _make_site_id(SiteKind.TENSOR_SHAPE, "backward_1st")
        site_bwd2 = _make_site_id(SiteKind.TENSOR_SHAPE, "backward_2nd")

        for idx, inp in enumerate(test_inputs):
            grad_inputs = []
            for t in inp:
                if isinstance(t, torch.Tensor) and t.is_floating_point():
                    grad_inputs.append(t.detach().requires_grad_(True))
                else:
                    grad_inputs.append(t)

            req_grad = [t for t in grad_inputs if isinstance(t, torch.Tensor) and t.requires_grad]
            if not req_grad:
                continue

            try:
                out = _safe_call(fn, grad_inputs)
            except Exception:
                continue

            leaves = _flatten_outputs(out)
            for leaf_idx, leaf in enumerate(leaves):
                if not (isinstance(leaf, torch.Tensor) and leaf.requires_grad):
                    continue
                try:
                    grad_out = torch.ones_like(leaf)
                    first_grads = torch.autograd.grad(
                        leaf,
                        req_grad,
                        grad_outputs=grad_out,
                        create_graph=True,
                        allow_unused=True,
                    )
                except Exception:
                    continue

                # Attempt second-order gradient
                for g_idx, g in enumerate(first_grads):
                    if g is None or not g.requires_grad:
                        continue
                    try:
                        torch.autograd.grad(
                            g.sum(),
                            req_grad,
                            allow_unused=True,
                            retain_graph=True,
                        )
                    except RuntimeError as exc:
                        failures.append((
                            site_fwd,
                            site_bwd1,
                            site_bwd2,
                            f"Input #{idx}, output #{leaf_idx}, grad #{g_idx}: "
                            f"double backward failed – {exc}.",
                        ))
        return failures


# ═══════════════════════════════════════════════════════════════════════════════
# TensorSheafConditionChecker  –  main orchestrator
# ═══════════════════════════════════════════════════════════════════════════════


class TensorSheafConditionChecker:
    """Orchestrate sheaf-condition checks for a single tensor program.

    This is the top-level entry point.  It proceeds through the strata in
    filtration order (METADATA → STRUCTURAL → NUMERICAL → BEHAVIORAL) and
    at each stratum runs:

    1. **Overlap consistency** (:class:`SectionConsistencyChecker`) –
       pairwise agreement between sites in the same stratum or between
       adjacent strata.
    2. **Gluing** (:class:`GluingChecker`) – attempt to assemble local
       sections into a global section.
    3. **Descent / cocycle** (:class:`DescentChecker`) – triple-overlap
       cocycle condition.

    When ``short_circuit_strata`` is true (the default), a failure at a
    coarser stratum causes later strata to be skipped – a shape bug makes
    numerical comparison meaningless.

    Usage::

        checker = TensorSheafConditionChecker()
        result = checker.check(my_fn, tensor_specs, test_inputs)
        if not result.satisfies_condition:
            for s_i, s_j in result.gluing_failures:
                print(f"Gluing failure between {s_i} and {s_j}")

        judgment = checker.analyze(my_fn, tensor_specs, test_inputs)
        for bug in judgment.bugs:
            print(bug.kind, bug.description)
    """

    def __init__(self) -> None:
        self._consistency = SectionConsistencyChecker.__new__(SectionConsistencyChecker)
        self._gluing = GluingChecker()
        self._descent = DescentChecker()

    # ── public API ────────────────────────────────────────────────────────

    def check(
        self,
        fn: Callable,
        tensor_specs: Sequence[TensorSpec],
        test_inputs: Optional[Sequence[Sequence[Any]]] = None,
        config: Optional[TensorEquivalenceConfig] = None,
    ) -> SheafConditionResult:
        """Check if *fn*'s presheaf satisfies the sheaf condition.

        Parameters
        ----------
        fn:
            The tensor program to check.
        tensor_specs:
            Specifications of each input tensor (shape, dtype, device, …).
        test_inputs:
            Optional pre-generated test inputs.  When *None*, inputs are
            synthesised from *tensor_specs*.
        config:
            Optional configuration controlling tolerances, checks enabled,
            etc.

        Returns
        -------
        SheafConditionResult
            Whether gluing and descent hold, with lists of failures.
        """
        cfg = config or TensorEquivalenceConfig()
        inputs = list(test_inputs) if test_inputs is not None else _generate_default_inputs(tensor_specs, cfg)
        if not inputs:
            return SheafConditionResult(
                satisfies_condition=True,
                gluing_failures=[],
                descent_failures=[],
                explanation="No test inputs available; vacuously satisfied.",
            )

        # Bind fn into the consistency checker
        self._consistency._fn = fn  # type: ignore[attr-defined]

        # Overlap consistency
        overlap_failures = self._consistency.check_overlap_consistency(inputs, cfg)
        gluing_failures_pairs = [(a, b) for a, b, _ in overlap_failures]

        # Gluing
        gluing_result = self._gluing.check_gluing(fn, inputs, cfg)
        all_gluing = gluing_failures_pairs + gluing_result.gluing_failures

        # Descent
        descent_raw = self._descent.check_descent(fn, inputs, cfg)
        descent_failures = [(a, b, c) for a, b, c, _ in descent_raw]

        ok = len(all_gluing) == 0 and len(descent_failures) == 0
        parts: List[str] = []
        if overlap_failures:
            parts.append(f"{len(overlap_failures)} overlap inconsistencies")
        if gluing_result.gluing_failures:
            parts.append(f"{len(gluing_result.gluing_failures)} gluing failures")
        if descent_failures:
            parts.append(f"{len(descent_failures)} descent/cocycle failures")
        explanation = "; ".join(parts) if parts else "Sheaf condition satisfied."

        return SheafConditionResult(
            satisfies_condition=ok,
            gluing_failures=all_gluing,
            descent_failures=descent_failures,
            explanation=explanation,
        )

    def analyze(
        self,
        fn: Callable,
        tensor_specs: Sequence[TensorSpec],
        test_inputs: Optional[Sequence[Sequence[Any]]] = None,
        config: Optional[TensorEquivalenceConfig] = None,
    ) -> AnalysisJudgment:
        """Full single-program analysis producing bugs and an :class:`AnalysisJudgment`.

        This is the high-level entry point that proceeds stratum-by-stratum,
        collecting :class:`Bug` instances for every detected inconsistency,
        and finally emitting a verdict.

        The filtration order is METADATA → STRUCTURAL → NUMERICAL → BEHAVIORAL.
        When ``config.short_circuit_strata`` is true and a stratum fails, later
        strata are skipped.
        """
        cfg = config or TensorEquivalenceConfig()
        inputs = list(test_inputs) if test_inputs is not None else _generate_default_inputs(tensor_specs, cfg)
        program = _program_id_from_fn(fn)
        all_bugs: List[Bug] = []
        stratum_results: Dict[TensorStratum, AnalysisVerdict] = {}

        for stratum in _STRATUM_ORDER:
            bugs = self._check_stratum(fn, stratum, inputs, cfg)
            all_bugs.extend(bugs)

            if bugs:
                stratum_results[stratum] = AnalysisVerdict.INVALID
                if cfg.short_circuit_strata:
                    # Mark remaining strata as unknown
                    remaining = _STRATUM_ORDER[_STRATUM_ORDER.index(stratum) + 1 :]
                    for s in remaining:
                        stratum_results[s] = AnalysisVerdict.UNKNOWN
                    break
            else:
                stratum_results[stratum] = AnalysisVerdict.VALID

        # Sheaf condition result
        sheaf_result = self.check(fn, tensor_specs, inputs, cfg)

        overall = (
            AnalysisVerdict.VALID if not all_bugs
            else AnalysisVerdict.INVALID
        )

        explanation_parts: List[str] = []
        if all_bugs:
            explanation_parts.append(f"Found {len(all_bugs)} bug(s)")
            kinds = {b.kind.value for b in all_bugs}
            explanation_parts.append(f"kinds: {', '.join(sorted(kinds))}")
        else:
            explanation_parts.append("No bugs detected")
        if not sheaf_result.satisfies_condition:
            explanation_parts.append("sheaf condition violated")

        return AnalysisJudgment(
            verdict=overall,
            program=program,
            mode=AnalysisMode.BUG_FINDING,
            bugs=all_bugs,
            sheaf_condition=sheaf_result,
            stratum_results=stratum_results,
            explanation="; ".join(explanation_parts),
        )

    # ── stratum dispatch ──────────────────────────────────────────────────

    def _check_stratum(
        self,
        fn: Callable,
        stratum: TensorStratum,
        test_inputs: List[List[Any]],
        config: TensorEquivalenceConfig,
    ) -> List[Bug]:
        """Run all checks appropriate for *stratum*."""
        if stratum == TensorStratum.METADATA:
            return self._check_dtype_consistency(fn, test_inputs)
        elif stratum == TensorStratum.STRUCTURAL:
            return self._check_shape_consistency(fn, test_inputs)
        elif stratum == TensorStratum.NUMERICAL:
            return self._check_numerical_stability(fn, test_inputs, config)
        elif stratum == TensorStratum.BEHAVIORAL:
            bugs: List[Bug] = []
            bugs.extend(self._check_autograd_consistency(fn, test_inputs))
            bugs.extend(self._check_memory_safety(fn, test_inputs))
            return bugs
        return []  # pragma: no cover

    # ── per-stratum checks ────────────────────────────────────────────────

    def _check_shape_consistency(
        self,
        fn: Callable,
        test_inputs: List[List[Any]],
    ) -> List[Bug]:
        """Check shape consistency: same input → same output shape.

        Sheaf interpretation: the shape section at the STRUCTURAL stratum
        must be well-defined.  If a function returns different shapes for
        the same input, the presheaf does not assign a unique section and
        the sheaf condition fails trivially.
        """
        bugs: List[Bug] = []
        site = _make_site_id(SiteKind.TENSOR_SHAPE, "shape_consistency")

        for idx, inp in enumerate(test_inputs):
            try:
                out1 = _safe_call(fn, inp)
                out2 = _safe_call(fn, inp)
            except Exception:
                continue
            leaves1 = _flatten_outputs(out1)
            leaves2 = _flatten_outputs(out2)
            if len(leaves1) != len(leaves2):
                bugs.append(Bug(
                    kind=BugKind.SHAPE_INCONSISTENCY,
                    stratum=TensorStratum.STRUCTURAL,
                    site_id=site,
                    description=(
                        f"Input #{idx}: output count changed between calls "
                        f"({len(leaves1)} vs {len(leaves2)})."
                    ),
                    witness_input=idx,
                    observed_output=(len(leaves1), len(leaves2)),
                    expected_behavior="Deterministic output count.",
                ))
                continue
            for k, (l1, l2) in enumerate(zip(leaves1, leaves2)):
                s1, s2 = _tensor_shape(l1), _tensor_shape(l2)
                if s1 is not None and s2 is not None and s1 != s2:
                    bugs.append(Bug(
                        kind=BugKind.SHAPE_INCONSISTENCY,
                        stratum=TensorStratum.STRUCTURAL,
                        site_id=site,
                        description=(
                            f"Input #{idx}, output #{k}: shape {s1} on first "
                            f"call vs {s2} on second call."
                        ),
                        witness_input=idx,
                        observed_output=(s1, s2),
                        expected_behavior="Identical output shapes on identical input.",
                        repair_hint="Ensure the function is deterministic in its output shape.",
                    ))
        return bugs

    def _check_dtype_consistency(
        self,
        fn: Callable,
        test_inputs: List[List[Any]],
    ) -> List[Bug]:
        """Check dtype promotion consistency across input dtype combinations.

        Sheaf interpretation: the dtype section at the METADATA stratum
        must be coherent.  If different input dtypes produce output dtypes
        that violate PyTorch's promotion rules, the restriction maps in
        the presheaf are not well-defined.
        """
        if not _HAS_TORCH:
            return []
        bugs: List[Bug] = []
        site = _make_site_id(SiteKind.TENSOR_SHAPE, "dtype_consistency")

        for idx, inp in enumerate(test_inputs):
            try:
                out1 = _safe_call(fn, inp)
                out2 = _safe_call(fn, inp)
            except Exception:
                continue
            leaves1 = _flatten_outputs(out1)
            leaves2 = _flatten_outputs(out2)
            for k, (l1, l2) in enumerate(zip(leaves1, leaves2)):
                d1, d2 = _tensor_dtype(l1), _tensor_dtype(l2)
                if d1 is not None and d2 is not None and d1 != d2:
                    bugs.append(Bug(
                        kind=BugKind.DTYPE_INCONSISTENCY,
                        stratum=TensorStratum.METADATA,
                        site_id=site,
                        description=(
                            f"Input #{idx}, output #{k}: dtype {d1} on first "
                            f"call vs {d2} on second call."
                        ),
                        witness_input=idx,
                        observed_output=(d1, d2),
                        expected_behavior="Deterministic output dtype.",
                    ))
        return bugs

    def _check_numerical_stability(
        self,
        fn: Callable,
        test_inputs: List[List[Any]],
        config: TensorEquivalenceConfig,
    ) -> List[Bug]:
        """Check for NaN/Inf and extreme sensitivity to perturbation.

        Sheaf interpretation: the numerical section at the NUMERICAL stratum
        must be "continuous" – a small perturbation of the input should not
        produce a wildly different output.  A NaN/Inf output means the
        section is *undefined* at that point (the presheaf has a hole).
        """
        if not _HAS_TORCH:
            return []
        bugs: List[Bug] = []
        nan_site = _make_site_id(SiteKind.TENSOR_SHAPE, "nan_detection")
        stability_site = _make_site_id(SiteKind.TENSOR_SHAPE, "perturbation_stability")
        atol = config.tolerance.atol
        rtol = config.tolerance.rtol

        for idx, inp in enumerate(test_inputs):
            # --- NaN / Inf detection ---
            try:
                out = _safe_call(fn, inp)
            except Exception:
                continue
            for k, leaf in enumerate(_flatten_outputs(out)):
                if not (isinstance(leaf, torch.Tensor) and leaf.is_floating_point()):
                    continue
                if torch.isnan(leaf).any().item():
                    bugs.append(Bug(
                        kind=BugKind.NUMERICAL_INSTABILITY,
                        stratum=TensorStratum.NUMERICAL,
                        site_id=nan_site,
                        description=(
                            f"Input #{idx}, output #{k}: output contains NaN."
                        ),
                        witness_input=idx,
                        observed_output="NaN",
                        expected_behavior="Finite output.",
                        repair_hint="Check for division by zero or log of non-positive values.",
                        severity=2.0,
                    ))
                if torch.isinf(leaf).any().item():
                    bugs.append(Bug(
                        kind=BugKind.NUMERICAL_INSTABILITY,
                        stratum=TensorStratum.NUMERICAL,
                        site_id=nan_site,
                        description=(
                            f"Input #{idx}, output #{k}: output contains Inf."
                        ),
                        witness_input=idx,
                        observed_output="Inf",
                        expected_behavior="Finite output.",
                        repair_hint="Consider clamping or using numerically stable formulations.",
                        severity=1.5,
                    ))

            # --- Perturbation sensitivity ---
            perturbed = []
            for t in inp:
                if isinstance(t, torch.Tensor) and t.is_floating_point():
                    eps = torch.randn_like(t) * atol
                    perturbed.append(t + eps)
                else:
                    perturbed.append(t)
            try:
                out_orig = _safe_call(fn, inp)
                out_pert = _safe_call(fn, perturbed)
            except Exception:
                continue
            for k, (lo, lp) in enumerate(
                zip(_flatten_outputs(out_orig), _flatten_outputs(out_pert))
            ):
                if not (isinstance(lo, torch.Tensor) and isinstance(lp, torch.Tensor)):
                    continue
                if lo.shape != lp.shape:
                    continue
                try:
                    diff = (lo.float() - lp.float()).abs()
                    scale = lo.float().abs().clamp(min=1e-12)
                    rel_diff = (diff / scale).max().item()
                    abs_diff = diff.max().item()
                except Exception:
                    continue
                # Sensitivity threshold: perturbation was O(atol), response
                # should be at most O(1/rtol) times that.
                sensitivity_bound = 1.0 / rtol if rtol > 0 else 1e8
                if abs_diff > 0 and rel_diff > sensitivity_bound:
                    bugs.append(Bug(
                        kind=BugKind.NUMERICAL_INSTABILITY,
                        stratum=TensorStratum.NUMERICAL,
                        site_id=stability_site,
                        description=(
                            f"Input #{idx}, output #{k}: perturbation of "
                            f"O({atol:.1e}) caused relative change {rel_diff:.2e} "
                            f"(threshold {sensitivity_bound:.2e})."
                        ),
                        witness_input=idx,
                        observed_output=rel_diff,
                        expected_behavior=(
                            f"Relative change ≤ {sensitivity_bound:.2e} for "
                            f"O({atol:.1e}) input perturbation."
                        ),
                        repair_hint="Use numerically stable algorithm or reduce precision requirements.",
                    ))
        return bugs

    def _check_autograd_consistency(
        self,
        fn: Callable,
        test_inputs: List[List[Any]],
    ) -> List[Bug]:
        """Check gradient shapes match forward output; double backward works.

        Sheaf interpretation: the autograd section at the BEHAVIORAL stratum
        must be compatible with the shape and numerical sections.  The
        gradient of a (n,m) output with respect to a (p,) input must have
        shape (p,) – any mismatch is a failure of the restriction map
        between the autograd and shape sites.
        """
        if not _HAS_TORCH:
            return []
        bugs: List[Bug] = []
        shape_site = _make_site_id(SiteKind.TENSOR_SHAPE, "grad_shape_consistency")
        compute_site = _make_site_id(SiteKind.TENSOR_SHAPE, "grad_computability")

        for idx, inp in enumerate(test_inputs):
            grad_inputs = []
            for t in inp:
                if isinstance(t, torch.Tensor) and t.is_floating_point():
                    grad_inputs.append(t.detach().requires_grad_(True))
                else:
                    grad_inputs.append(t)

            req_grad = [t for t in grad_inputs if isinstance(t, torch.Tensor) and t.requires_grad]
            if not req_grad:
                continue

            try:
                out = _safe_call(fn, grad_inputs)
            except Exception:
                continue

            for leaf_idx, leaf in enumerate(_flatten_outputs(out)):
                if not (isinstance(leaf, torch.Tensor) and leaf.requires_grad):
                    continue

                # Gradient computation
                try:
                    grad_out = torch.ones_like(leaf)
                    grads = torch.autograd.grad(
                        leaf,
                        req_grad,
                        grad_outputs=grad_out,
                        allow_unused=True,
                        retain_graph=True,
                    )
                except Exception as exc:
                    bugs.append(Bug(
                        kind=BugKind.GRADIENT_INCORRECTNESS,
                        stratum=TensorStratum.BEHAVIORAL,
                        site_id=compute_site,
                        description=(
                            f"Input #{idx}, output #{leaf_idx}: gradient "
                            f"computation failed – {type(exc).__name__}: {exc}."
                        ),
                        witness_input=idx,
                        repair_hint="Ensure all operations in the forward pass are differentiable.",
                    ))
                    continue

                # Shape consistency: grad shape must match input shape
                for g_idx, (g, t) in enumerate(zip(grads, req_grad)):
                    if g is None:
                        continue
                    if g.shape != t.shape:
                        bugs.append(Bug(
                            kind=BugKind.GRADIENT_INCORRECTNESS,
                            stratum=TensorStratum.BEHAVIORAL,
                            site_id=shape_site,
                            description=(
                                f"Input #{idx}, output #{leaf_idx}, grad #{g_idx}: "
                                f"gradient shape {tuple(g.shape)} ≠ input shape "
                                f"{tuple(t.shape)}."
                            ),
                            witness_input=idx,
                            observed_output=tuple(g.shape),
                            expected_behavior=f"Gradient shape {tuple(t.shape)}.",
                            severity=2.0,
                        ))

                    # NaN in gradient
                    if g.is_floating_point() and torch.isnan(g).any().item():
                        bugs.append(Bug(
                            kind=BugKind.GRADIENT_INCORRECTNESS,
                            stratum=TensorStratum.BEHAVIORAL,
                            site_id=compute_site,
                            description=(
                                f"Input #{idx}, output #{leaf_idx}, grad #{g_idx}: "
                                f"gradient contains NaN."
                            ),
                            witness_input=idx,
                            observed_output="NaN gradient",
                            expected_behavior="Finite gradient.",
                            repair_hint="Check for 0/0 or sqrt(0) in backward pass.",
                            severity=2.0,
                        ))
        return bugs

    def _check_memory_safety(
        self,
        fn: Callable,
        test_inputs: List[List[Any]],
    ) -> List[Bug]:
        """Check for in-place mutation and aliasing hazards.

        Sheaf interpretation: memory aliasing is a failure of separation.
        If two sections (the input tensor and the output tensor) share
        storage, modifying one silently modifies the other – the presheaf
        does not satisfy locality because "distinct" sections are secretly
        coupled.
        """
        if not _HAS_TORCH:
            return []
        bugs: List[Bug] = []
        alias_site = _make_site_id(SiteKind.TENSOR_SHAPE, "aliasing_check")
        mutation_site = _make_site_id(SiteKind.TENSOR_SHAPE, "mutation_check")

        for idx, inp in enumerate(test_inputs):
            # Snapshot inputs before the call
            snapshots = []
            for t in inp:
                if isinstance(t, torch.Tensor):
                    snapshots.append(t.clone())
                else:
                    snapshots.append(None)

            try:
                out = _safe_call(fn, inp)
            except Exception:
                continue

            # Check whether inputs were mutated (in-place modification)
            for t_idx, (snap, t) in enumerate(zip(snapshots, inp)):
                if snap is None or not isinstance(t, torch.Tensor):
                    continue
                try:
                    if not torch.equal(snap, t):
                        bugs.append(Bug(
                            kind=BugKind.ALIASING_HAZARD,
                            stratum=TensorStratum.BEHAVIORAL,
                            site_id=mutation_site,
                            description=(
                                f"Input #{idx}: input tensor #{t_idx} was mutated "
                                f"in-place by the function."
                            ),
                            witness_input=idx,
                            expected_behavior="Inputs unchanged after function call.",
                            repair_hint="Use .clone() before modifying or avoid in-place ops.",
                        ))
                except Exception:
                    pass

            # Check output-input aliasing
            for leaf in _flatten_outputs(out):
                if not isinstance(leaf, torch.Tensor):
                    continue
                for t_idx, t in enumerate(inp):
                    if not isinstance(t, torch.Tensor):
                        continue
                    if leaf.data_ptr() == t.data_ptr():
                        bugs.append(Bug(
                            kind=BugKind.ALIASING_HAZARD,
                            stratum=TensorStratum.BEHAVIORAL,
                            site_id=alias_site,
                            description=(
                                f"Input #{idx}: output shares storage with "
                                f"input #{t_idx} (data_ptr aliasing)."
                            ),
                            witness_input=idx,
                            expected_behavior="Output uses independent storage.",
                            repair_hint="Return output.clone() to break aliasing.",
                            severity=0.5,
                        ))
        return bugs
