"""
Dtype equivalence checker — promotion lattice, casting presheaf.

Models dtype equivalence as a presheaf on the dtype promotion lattice:
  - Objects: PyTorch scalar types (float16, float32, float64, int32, ...)
  - Morphisms: promotion maps (the lattice order)
  - Sections: dtype propagation functions δ_f, δ_g: input_dtypes → output_dtypes
  - Equivalence: ∀ input dtypes d, δ_f(d) = δ_g(d) under promotion

The dtype promotion lattice is the standard PyTorch type hierarchy:
  bool < uint8 < int8 < int16 < int32 < int64 < float16 < bfloat16 < float32 < float64
  (with complex branches: complex64 < complex128)

Restriction along promotion morphisms models how a function's dtype
behavior at a coarser type restricts to its behavior at a finer type.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

from ._protocols import (
    AnalysisJudgment,
    AnalysisMode,
    AnalysisVerdict,
    Bug,
    BugKind,
    EquivalenceVerdict,
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
)


# ---------------------------------------------------------------------------
# Dtype lattice (the partial order on PyTorch scalar types)
# ---------------------------------------------------------------------------

# Canonical ordering index (lower = coarser)
_DTYPE_ORDER: Dict[str, int] = {
    "bool": 0,
    "uint8": 1,
    "int8": 2,
    "int16": 3,
    "int32": 4,
    "int64": 5,
    "float16": 6,
    "bfloat16": 7,
    "float32": 8,
    "float64": 9,
    "complex64": 10,
    "complex128": 11,
}

# Dtype categories for promotion rules
_DTYPE_CATEGORY: Dict[str, str] = {
    "bool": "boolean",
    "uint8": "integer",
    "int8": "integer",
    "int16": "integer",
    "int32": "integer",
    "int64": "integer",
    "float16": "floating",
    "bfloat16": "floating",
    "float32": "floating",
    "float64": "floating",
    "complex64": "complex",
    "complex128": "complex",
}

# Category promotion order
_CATEGORY_ORDER = {"boolean": 0, "integer": 1, "floating": 2, "complex": 3}


def dtype_leq(a: str, b: str) -> bool:
    """a ≤ b in the dtype promotion lattice."""
    return _DTYPE_ORDER.get(a, -1) <= _DTYPE_ORDER.get(b, -1)


def dtype_join(a: str, b: str) -> str:
    """Least upper bound in the dtype promotion lattice (result_type)."""
    try:
        import torch
        ta = getattr(torch, a, None)
        tb = getattr(torch, b, None)
        if ta is not None and tb is not None:
            result = torch.result_type(torch.zeros(1, dtype=ta),
                                       torch.zeros(1, dtype=tb))
            return str(result).split(".")[-1]
    except Exception:
        pass
    # Fallback
    oa = _DTYPE_ORDER.get(a, -1)
    ob = _DTYPE_ORDER.get(b, -1)
    if oa >= ob:
        return a
    return b


def dtype_meet(a: str, b: str) -> str:
    """Greatest lower bound in the dtype promotion lattice."""
    oa = _DTYPE_ORDER.get(a, -1)
    ob = _DTYPE_ORDER.get(b, -1)
    if oa <= ob:
        return a
    return b


def dtypes_compatible(a: str, b: str) -> bool:
    """Check if two dtypes can be promoted to a common type."""
    return dtype_join(a, b) is not None


def dtype_category(dtype: str) -> str:
    """Get the category of a dtype (boolean, integer, floating, complex)."""
    return _DTYPE_CATEGORY.get(dtype, "unknown")


def is_widening_cast(source: str, target: str) -> bool:
    """Check if source → target is a widening (lossless) cast."""
    return dtype_leq(source, target)


def is_narrowing_cast(source: str, target: str) -> bool:
    """Check if source → target is a narrowing (potentially lossy) cast."""
    return dtype_leq(target, source) and source != target


# ---------------------------------------------------------------------------
# Dtype promotion oracle
# ---------------------------------------------------------------------------

class DtypePromotionOracle:
    """
    Oracle for dtype promotion rules.

    This implements the *section* of the dtype presheaf: given input dtypes,
    the oracle produces the output dtype by running promotion inference.
    """

    @staticmethod
    def infer_output_dtype(fn: Any,
                           input_specs: Sequence[TensorSpec]) -> Optional[List[str]]:
        """Infer output dtypes by running fn on small tensors."""
        try:
            import torch
        except ImportError:
            return None

        test_inputs = []
        for spec in input_specs:
            dtype = getattr(torch, spec.dtype, torch.float32)
            if dtype.is_floating_point:
                t = torch.randn(spec.shape, dtype=dtype)
            elif dtype == torch.bool:
                t = torch.randint(0, 2, spec.shape).bool()
            elif dtype.is_complex:
                real = torch.randn(spec.shape)
                imag = torch.randn(spec.shape)
                t = torch.complex(real, imag).to(dtype)
            else:
                t = torch.randint(-10, 10, spec.shape, dtype=dtype)
            test_inputs.append(t)

        try:
            out = fn(*test_inputs)
        except Exception:
            return None

        if isinstance(out, (tuple, list)):
            return [str(o.dtype).split(".")[-1] for o in out
                    if hasattr(o, "dtype")]
        elif hasattr(out, "dtype"):
            return [str(out.dtype).split(".")[-1]]
        return None


# ---------------------------------------------------------------------------
# Dtype equivalence checker
# ---------------------------------------------------------------------------

class DtypeEquivalenceChecker:
    """
    Checks dtype equivalence of two tensor functions.

    This implements the local section comparison at dtype sites:
    for each combination of input dtypes, compare the output dtypes
    of fn_f and fn_g.  Dtype equivalence means both functions respect
    the same promotion rules.

    Sheaf-theoretically, this is checking that the restriction maps
    along promotion morphisms commute: if we promote an input dtype,
    both functions promote the output dtype in the same way.
    """

    def __init__(self, config: TensorEquivalenceConfig):
        self._config = config
        self._oracle = DtypePromotionOracle()

    # Standard dtype test matrix
    _FLOAT_DTYPES = ["float16", "bfloat16", "float32", "float64"]
    _INT_DTYPES = ["int8", "int16", "int32", "int64"]
    _ALL_DTYPES = ["bool", "uint8"] + _INT_DTYPES + _FLOAT_DTYPES + ["complex64", "complex128"]

    def check_site(
        self,
        fn_f: Any,
        fn_g: Any,
        base_specs: Sequence[TensorSpec],
        site_id: SiteId,
        dtype_matrix: Optional[Sequence[str]] = None,
    ) -> TensorLocalJudgment:
        """
        Check dtype equivalence at a single dtype site.

        Tests fn_f and fn_g across a matrix of input dtypes, checking
        that output dtypes agree for each input combination.
        """
        test_dtypes = list(dtype_matrix) if dtype_matrix else self._FLOAT_DTYPES

        obstructions: List[TensorObstruction] = []
        tested = 0

        for test_dtype in test_dtypes:
            # Create specs with the test dtype
            modified_specs = [
                TensorSpec(
                    shape=spec.shape,
                    dtype=test_dtype,
                    device=spec.device,
                    requires_grad=spec.requires_grad and test_dtype in self._FLOAT_DTYPES,
                )
                for spec in base_specs
            ]

            dtypes_f = self._oracle.infer_output_dtype(fn_f, modified_specs)
            dtypes_g = self._oracle.infer_output_dtype(fn_g, modified_specs)

            if dtypes_f is None and dtypes_g is None:
                continue  # Both fail — not an obstruction
            tested += 1

            if dtypes_f is None or dtypes_g is None:
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.DTYPE_MISMATCH,
                    stratum=TensorStratum.METADATA,
                    sites=(site_id,),
                    description=(f"dtype={test_dtype}: one function fails "
                                 f"(f={'ok' if dtypes_f else 'fail'}, "
                                 f"g={'ok' if dtypes_g else 'fail'})"),
                ))
                continue

            if dtypes_f != dtypes_g:
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.DTYPE_MISMATCH,
                    stratum=TensorStratum.METADATA,
                    sites=(site_id,),
                    description=(f"dtype={test_dtype}: output dtypes differ: "
                                 f"f→{dtypes_f}, g→{dtypes_g}"),
                ))

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.METADATA,
                tensor_site_kind=TensorSiteKind.DTYPE,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation=f"Dtype mismatch in {len(obstructions)}/{tested} tests",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.METADATA,
            tensor_site_kind=TensorSiteKind.DTYPE,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation=f"Dtype behavior matches across {tested} dtype variants",
        )

    def check_promotion_coherence(
        self,
        fn_f: Any,
        fn_g: Any,
        base_specs: Sequence[TensorSpec],
        site_id: SiteId,
    ) -> TensorLocalJudgment:
        """
        Check that dtype promotion morphisms commute.

        For each pair of dtypes (d₁, d₂) where d₁ ≤ d₂, verify that:
          promote(output_dtype(f, d₁)) = output_dtype(f, d₂)
        and similarly for g.  This is the *restriction coherence* condition
        for the dtype presheaf.
        """
        obstructions: List[TensorObstruction] = []

        for i, d1 in enumerate(self._FLOAT_DTYPES):
            for d2 in self._FLOAT_DTYPES[i + 1:]:
                if not dtype_leq(d1, d2):
                    continue

                specs_d1 = [TensorSpec(shape=s.shape, dtype=d1) for s in base_specs]
                specs_d2 = [TensorSpec(shape=s.shape, dtype=d2) for s in base_specs]

                out_f_d1 = self._oracle.infer_output_dtype(fn_f, specs_d1)
                out_f_d2 = self._oracle.infer_output_dtype(fn_f, specs_d2)
                out_g_d1 = self._oracle.infer_output_dtype(fn_g, specs_d1)
                out_g_d2 = self._oracle.infer_output_dtype(fn_g, specs_d2)

                # Check that promotion morphism commutes for f
                if out_f_d1 and out_f_d2:
                    promoted = [dtype_join(d, d2) for d in out_f_d1]
                    if promoted != out_f_d2:
                        obstructions.append(TensorObstruction(
                            kind=TensorObstructionKind.DTYPE_MISMATCH,
                            stratum=TensorStratum.METADATA,
                            sites=(site_id,),
                            description=(f"Promotion incoherence (f): "
                                         f"{d1}→{d2}: promote({out_f_d1})="
                                         f"{promoted} ≠ {out_f_d2}"),
                        ))

                # Check same for g
                if out_g_d1 and out_g_d2:
                    promoted = [dtype_join(d, d2) for d in out_g_d1]
                    if promoted != out_g_d2:
                        obstructions.append(TensorObstruction(
                            kind=TensorObstructionKind.DTYPE_MISMATCH,
                            stratum=TensorStratum.METADATA,
                            sites=(site_id,),
                            description=(f"Promotion incoherence (g): "
                                         f"{d1}→{d2}: promote({out_g_d1})="
                                         f"{promoted} ≠ {out_g_d2}"),
                        ))

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.METADATA,
                tensor_site_kind=TensorSiteKind.DTYPE,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation="Promotion coherence violated",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.METADATA,
            tensor_site_kind=TensorSiteKind.DTYPE,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation="Promotion coherence satisfied",
        )

    # ------------------------------------------------------------------
    # Single-program analysis
    # ------------------------------------------------------------------

    def analyze(
        self,
        fn: Any,
        base_specs: Sequence[TensorSpec],
        site_id: Optional[SiteId] = None,
    ) -> AnalysisJudgment:
        """Analyze dtype promotion consistency of a single function.

        Checks that the function's output dtype follows standard promotion
        rules when input dtypes are widened along the promotion lattice.
        A bug means the dtype presheaf's restriction maps are incoherent —
        widening an input dtype doesn't widen the output dtype monotonically.
        """
        if site_id is None:
            site_id = SiteId(kind=SiteKind.TENSOR_SHAPE, name="dtype_analysis")
        program = ProgramId(name="fn", function_name=getattr(fn, "__name__", "anonymous"))
        bugs: List[Bug] = []

        # Collect output dtypes for each test dtype in the promotion chain
        results: Dict[str, Optional[List[str]]] = {}
        for test_dtype in self._FLOAT_DTYPES:
            modified = [
                TensorSpec(
                    shape=s.shape,
                    dtype=test_dtype,
                    device=s.device,
                    requires_grad=s.requires_grad and test_dtype in self._FLOAT_DTYPES,
                )
                for s in base_specs
            ]
            results[test_dtype] = self._oracle.infer_output_dtype(fn, modified)

        # Check promotion monotonicity: d1 ≤ d2 implies out(d1) ≤ out(d2)
        for i, d1 in enumerate(self._FLOAT_DTYPES):
            for d2 in self._FLOAT_DTYPES[i + 1:]:
                if not dtype_leq(d1, d2):
                    continue
                out_d1 = results.get(d1)
                out_d2 = results.get(d2)
                if out_d1 is None or out_d2 is None:
                    continue
                if len(out_d1) != len(out_d2):
                    bugs.append(Bug(
                        kind=BugKind.DTYPE_INCONSISTENCY,
                        stratum=TensorStratum.METADATA,
                        site_id=site_id,
                        description=(
                            f"Output count changes: {len(out_d1)} outputs at {d1} "
                            f"vs {len(out_d2)} at {d2}"
                        ),
                        expected_behavior="Output count should be dtype-independent",
                    ))
                    continue
                for idx, (o1, o2) in enumerate(zip(out_d1, out_d2)):
                    if not dtype_leq(o1, o2):
                        bugs.append(Bug(
                            kind=BugKind.DTYPE_INCONSISTENCY,
                            stratum=TensorStratum.METADATA,
                            site_id=site_id,
                            description=(
                                f"Promotion incoherence: input {d1}→{d2} but "
                                f"output[{idx}] {o1}→{o2} violates lattice order"
                            ),
                            expected_behavior=(
                                f"Output dtype should be monotone: "
                                f"{o1} ≤ {o2} expected"
                            ),
                        ))

        # Check that promoted output equals direct output at the join
        for i, d1 in enumerate(self._FLOAT_DTYPES):
            for d2 in self._FLOAT_DTYPES[i + 1:]:
                if not dtype_leq(d1, d2):
                    continue
                out_d1 = results.get(d1)
                out_d2 = results.get(d2)
                if out_d1 is None or out_d2 is None:
                    continue
                if len(out_d1) != len(out_d2):
                    continue
                for idx, (o1, o2) in enumerate(zip(out_d1, out_d2)):
                    promoted = dtype_join(o1, d2)
                    if promoted != o2:
                        bugs.append(Bug(
                            kind=BugKind.DTYPE_INCONSISTENCY,
                            stratum=TensorStratum.METADATA,
                            site_id=site_id,
                            description=(
                                f"Promotion diagram non-commutative: "
                                f"promote(out({d1}), {d2})={promoted} ≠ out({d2})={o2}"
                            ),
                            repair_hint="Check for explicit dtype casts that bypass promotion",
                        ))

        verdict = AnalysisVerdict.INVALID if bugs else AnalysisVerdict.VALID
        return AnalysisJudgment(
            verdict=verdict,
            program=program,
            mode=AnalysisMode.BUG_FINDING,
            bugs=bugs,
            stratum_results={TensorStratum.METADATA: verdict},
            explanation=(
                f"Found {len(bugs)} dtype promotion inconsistencies"
                if bugs else
                "Dtype presheaf restriction maps are coherent"
            ),
        )
