"""
PyTorch global equivalence checker — tensor descent and gluing.

Assembles local judgments from the local checker into a global
equivalence verdict via tensor descent.

The gluing procedure mirrors classical sheaf descent:
  1. Local judgments at each site kind are the *sections*
  2. On overlaps (sites related by restriction morphisms), sections
     must agree (cocycle condition)
  3. The descent datum is the compatible family of local judgments
  4. If descent succeeds, the global section (overall verdict) is unique

The canonical filtration provides a spectral sequence structure:
  E₁^{p,q} = H^q(stratum_p cover, local judgments)
converging to the global H⁰ (= glued verdict).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Sequence, Tuple

from ._protocols import (
    EquivalenceStrength,
    EquivalenceVerdict,
    ProgramId,
    SiteId,
    TensorCohomologyClass,
    TensorDescentDatum,
    TensorEquivalenceConfig,
    TensorGlobalJudgment,
    TensorLocalJudgment,
    TensorObstruction,
    TensorObstructionKind,
    TensorSiteKind,
    TensorSpec,
    TensorStratum,
    TritonKernelSpec,
    MLIRModuleSpec,
    SITE_KIND_STRATUM,
)

from .torch_local_checker import TorchLocalChecker, LocalCheckResult
from .base_bridge import (
    compute_cohomology_via_base,
    verify_descent_via_base,
    FullDescentResult,
)


# ---------------------------------------------------------------------------
# Descent verification
# ---------------------------------------------------------------------------

@dataclass
class DescentResult:
    """Result of verifying the tensor descent condition."""
    is_effective: bool = False
    cocycle_violations: List[str] = field(default_factory=list)
    glued_verdict: EquivalenceVerdict = EquivalenceVerdict.UNKNOWN


def verify_tensor_descent(
    local_result: LocalCheckResult,
    config: TensorEquivalenceConfig,
) -> DescentResult:
    """
    Verify the tensor descent condition.

    Two-phase verification:
    1. **Base framework**: Delegates to ``EquivalenceDescentChecker`` from
       ``deppy.equivalence.descent`` for formal Čech-cohomological H¹ check.
    2. **Tensor-specific**: Checks domain-specific cross-stratum coherence
       (shape↔stride, dtype↔numerical, autograd↔numerical).

    The combined result is effective iff both phases pass.
    """
    violations: List[str] = []
    judgments_by_kind: Dict[TensorSiteKind, TensorLocalJudgment] = {}

    for j in local_result.judgments:
        judgments_by_kind[j.tensor_site_kind] = j

    # ── Phase 1: Base framework descent (Čech cohomology H¹ check) ──────
    base_descent: Optional[FullDescentResult] = None
    try:
        base_descent = verify_descent_via_base(local_result.judgments)
        if not base_descent.is_effective:
            violations.extend(base_descent.cocycle_violations)
    except Exception:
        pass  # Fall through to tensor-specific checks

    # ── Phase 2: Tensor-specific cross-stratum coherence ────────────────

    # 1. Shape ↔ Stride coherence
    shape_j = judgments_by_kind.get(TensorSiteKind.SHAPE)
    stride_j = judgments_by_kind.get(TensorSiteKind.STRIDE)
    if (shape_j and stride_j and
            shape_j.verdict == EquivalenceVerdict.EQUIVALENT and
            stride_j.verdict == EquivalenceVerdict.INEQUIVALENT):
        pass  # Different memory layouts OK

    # 2. Dtype ↔ Numerical coherence
    dtype_j = judgments_by_kind.get(TensorSiteKind.DTYPE)
    numerical_j = judgments_by_kind.get(TensorSiteKind.NUMERICAL)
    if (dtype_j and numerical_j and
            dtype_j.verdict == EquivalenceVerdict.INEQUIVALENT and
            numerical_j.verdict == EquivalenceVerdict.EQUIVALENT):
        violations.append(
            "Descent violation: dtype differs but numerical values match — "
            "possible coincidental agreement"
        )

    # 3. Shape ↔ Numerical coherence
    if (shape_j and numerical_j and
            shape_j.verdict == EquivalenceVerdict.INEQUIVALENT and
            numerical_j.verdict == EquivalenceVerdict.EQUIVALENT):
        violations.append(
            "Descent violation: shapes differ but numerical values match — "
            "impossible for correctly shaped outputs"
        )

    # 4. Autograd ↔ Numerical coherence
    autograd_j = judgments_by_kind.get(TensorSiteKind.AUTOGRAD)
    if (autograd_j and numerical_j and
            autograd_j.verdict == EquivalenceVerdict.INEQUIVALENT and
            numerical_j.verdict == EquivalenceVerdict.EQUIVALENT):
        pass  # Numerical equivalent but autograd different: possible

    is_effective = len(violations) == 0

    # Determine glued verdict
    if local_result.all_equivalent:
        glued = EquivalenceVerdict.EQUIVALENT
    elif any(j.verdict == EquivalenceVerdict.INEQUIVALENT
             for j in local_result.judgments):
        glued = EquivalenceVerdict.INEQUIVALENT
    elif any(j.verdict == EquivalenceVerdict.REFINED
             for j in local_result.judgments):
        glued = EquivalenceVerdict.REFINED
    else:
        glued = EquivalenceVerdict.UNKNOWN

    return DescentResult(
        is_effective=is_effective,
        cocycle_violations=violations,
        glued_verdict=glued,
    )


# ---------------------------------------------------------------------------
# Cohomology computation
# ---------------------------------------------------------------------------

def compute_tensor_cohomology(
    local_result: LocalCheckResult,
    descent: DescentResult,
) -> List[TensorCohomologyClass]:
    """
    Compute obstruction cohomology classes via the base Čech framework.

    Delegates to ``CechCohomologyComputer`` from ``deppy.equivalence.cohomology``
    for the full C⁰ → C¹ → C² → H⁰, H¹ computation.  Falls back to the
    direct extraction when base framework types are unavailable.

    Each obstruction (failed site) contributes to H¹ of the tensor
    site cover.  The cohomology classes classify the *types* of
    inequivalence:
    - H¹ with shape coefficients: shape-level obstruction
    - H¹ with numerical coefficients: numerical divergence
    - H¹ with behavioral coefficients: autograd/dispatch mismatch
    """
    # Try base framework cohomology first
    try:
        _result, tensor_classes = compute_cohomology_via_base(local_result.judgments)
        if tensor_classes:
            if (
                any(j.verdict == EquivalenceVerdict.INEQUIVALENT for j in local_result.judgments)
                and not any(not c.is_trivial for c in tensor_classes)
            ):
                for j in local_result.judgments:
                    if j.verdict == EquivalenceVerdict.INEQUIVALENT:
                        tensor_classes.append(TensorCohomologyClass(
                            degree=1,
                            representative_sites=[j.site_id],
                            is_trivial=False,
                            obstruction_description=(
                                f"{j.tensor_site_kind.name}: {j.explanation}"
                            ),
                            numerical_obstruction=j.max_abs_diff,
                        ))
            # Augment with descent violations as H² classes
            for v in descent.cocycle_violations:
                tensor_classes.append(TensorCohomologyClass(
                    degree=2,
                    representative_sites=[],
                    is_trivial=False,
                    obstruction_description=v,
                ))
            return tensor_classes
    except Exception:
        pass  # Fall through to direct extraction

    # Direct extraction fallback
    classes: List[TensorCohomologyClass] = []

    for j in local_result.judgments:
        if j.verdict == EquivalenceVerdict.INEQUIVALENT:
            classes.append(TensorCohomologyClass(
                degree=1,
                representative_sites=[j.site_id],
                is_trivial=False,
                obstruction_description=(
                    f"{j.tensor_site_kind.name}: {j.explanation}"
                ),
                numerical_obstruction=j.max_abs_diff,
            ))

    for v in descent.cocycle_violations:
        classes.append(TensorCohomologyClass(
            degree=2,
            representative_sites=[],
            is_trivial=False,
            obstruction_description=v,
        ))

    return classes


# ---------------------------------------------------------------------------
# Natural transformation witness
# ---------------------------------------------------------------------------

@dataclass
class TensorNaturalTransformation:
    """
    Witness of a natural transformation between tensor presheaves.

    Components η_k: Sem_f(k) → Sem_g(k) at each site kind k,
    together with a proof that the naturality squares commute.
    """
    components: Dict[TensorSiteKind, EquivalenceVerdict]
    is_natural: bool = False
    is_isomorphism: bool = False
    naturality_failures: List[str] = field(default_factory=list)


def build_natural_transformation(
    local_result: LocalCheckResult,
    descent: DescentResult,
) -> TensorNaturalTransformation:
    """
    Build a natural transformation from local judgments.

    Each local judgment provides a component.  Naturality is verified
    by the descent condition.
    """
    components: Dict[TensorSiteKind, EquivalenceVerdict] = {}

    for j in local_result.judgments:
        components[j.tensor_site_kind] = j.verdict

    is_iso = all(v == EquivalenceVerdict.EQUIVALENT for v in components.values())
    is_natural = descent.is_effective

    return TensorNaturalTransformation(
        components=components,
        is_natural=is_natural,
        is_isomorphism=is_iso and is_natural,
        naturality_failures=descent.cocycle_violations,
    )


# ---------------------------------------------------------------------------
# Global checker
# ---------------------------------------------------------------------------

class TorchGlobalChecker:
    """
    Global equivalence checker for PyTorch functions.

    Orchestrates the full sheaf-theoretic checking pipeline:
    1. Local checking at each tensor site (via TorchLocalChecker)
    2. Descent verification (cocycle condition)
    3. Cohomology computation (obstruction classification)
    4. Natural transformation construction (isomorphism witness)
    5. Global verdict assembly

    The global checker implements the *global sections functor*
    Γ: Sh(TensorSite) → Set, which takes a sheaf and returns
    its global sections.  Equivalence = Γ(Eq) is non-empty.
    """

    def __init__(self, config: TensorEquivalenceConfig):
        self._config = config
        self._local_checker = TorchLocalChecker(config)

    def check(
        self,
        fn_f: Callable,
        fn_g: Callable,
        tensor_specs: Sequence[TensorSpec],
        test_inputs: Optional[Sequence[Sequence[Any]]] = None,
        triton_spec_f: Optional[TritonKernelSpec] = None,
        triton_spec_g: Optional[TritonKernelSpec] = None,
        mlir_spec_f: Optional[MLIRModuleSpec] = None,
        mlir_spec_g: Optional[MLIRModuleSpec] = None,
    ) -> TensorGlobalJudgment:
        """
        Check global equivalence of two PyTorch functions.

        Returns a TensorGlobalJudgment with the full sheaf-theoretic
        analysis: local judgments, descent data, cohomology, natural
        transformation, and the global verdict.
        """
        fn_f_name = getattr(fn_f, "__name__", "f")
        fn_g_name = getattr(fn_g, "__name__", "g")
        prog_f = ProgramId(name=fn_f_name)
        prog_g = ProgramId(name=fn_g_name)

        # Phase 1: Local checking
        local_result = self._local_checker.check_all_sites(
            fn_f, fn_g, tensor_specs, test_inputs,
            triton_spec_f, triton_spec_g,
            mlir_spec_f, mlir_spec_g,
        )

        # Phase 2: Descent verification
        descent = verify_tensor_descent(local_result, self._config)

        # Phase 3: Cohomology
        cohomology = compute_tensor_cohomology(local_result, descent)

        # Phase 4: Natural transformation
        nat_trans = build_natural_transformation(local_result, descent)

        # Phase 5: Assemble stratum results
        stratum_results: Dict[TensorStratum, EquivalenceVerdict] = {}
        for j in local_result.judgments:
            stratum = SITE_KIND_STRATUM.get(j.tensor_site_kind, TensorStratum.METADATA)
            current = stratum_results.get(stratum)
            if current is None:
                stratum_results[stratum] = j.verdict
            elif j.verdict == EquivalenceVerdict.INEQUIVALENT:
                stratum_results[stratum] = EquivalenceVerdict.INEQUIVALENT
            elif (j.verdict == EquivalenceVerdict.UNKNOWN and
                  current != EquivalenceVerdict.INEQUIVALENT):
                stratum_results[stratum] = EquivalenceVerdict.UNKNOWN

        # Phase 6: Global verdict
        verdict = self._compute_global_verdict(
            descent.glued_verdict, nat_trans, cohomology
        )

        # Determine strength
        strength = self._determine_strength(local_result, nat_trans)

        # Collect all obstructions
        all_obstructions: List[TensorObstruction] = []
        for j in local_result.judgments:
            all_obstructions.extend(j.obstructions)

        # Build local judgments dict for TensorGlobalJudgment
        local_judgments_dict: Dict[SiteId, TensorLocalJudgment] = {
            j.site_id: j for j in local_result.judgments
        }

        # Build descent data (using actual TensorDescentDatum fields)
        descent_data = TensorDescentDatum(
            local_judgments=local_judgments_dict,
            cocycle_checks={},  # TODO: triple-overlap checking
            tolerance_budget=self._config.tolerance.rtol if self._config.tolerance else None,
        )

        # Explanation
        explanation = self._build_explanation(
            verdict, local_result, descent, cohomology
        )

        # Pick first cohomology class if any
        cohomology_class = cohomology[0] if cohomology else None

        return TensorGlobalJudgment(
            verdict=verdict,
            program_f=prog_f,
            program_g=prog_g,
            strength=strength,
            stratum_results=stratum_results,
            local_judgments=local_judgments_dict,
            descent=descent_data,
            cohomology=cohomology_class,
            obstructions=all_obstructions,
            test_inputs_used=len(test_inputs) if test_inputs else 0,
            explanation=explanation,
        )

    def _compute_global_verdict(
        self,
        descent_verdict: EquivalenceVerdict,
        nat_trans: TensorNaturalTransformation,
        cohomology: List[TensorCohomologyClass],
    ) -> EquivalenceVerdict:
        """Compute the global verdict from components."""
        # Natural isomorphism → equivalent
        if nat_trans.is_isomorphism:
            return EquivalenceVerdict.EQUIVALENT

        # Descent says inequivalent → inequivalent
        if descent_verdict == EquivalenceVerdict.INEQUIVALENT:
            return EquivalenceVerdict.INEQUIVALENT

        # Non-trivial cohomology → inequivalent
        if any(not c.is_trivial for c in cohomology):
            return EquivalenceVerdict.INEQUIVALENT

        # All components equivalent but not natural → refined
        if (all(v == EquivalenceVerdict.EQUIVALENT
                for v in nat_trans.components.values()) and
                not nat_trans.is_natural):
            return EquivalenceVerdict.REFINED

        return descent_verdict

    def _determine_strength(
        self,
        local_result: LocalCheckResult,
        nat_trans: TensorNaturalTransformation,
    ) -> EquivalenceStrength:
        """Determine the strength of the equivalence."""
        if nat_trans.is_isomorphism:
            return EquivalenceStrength.DENOTATIONAL
        if nat_trans.is_natural:
            return EquivalenceStrength.OBSERVATIONAL
        return EquivalenceStrength.OBSERVATIONAL

    def _build_explanation(
        self,
        verdict: EquivalenceVerdict,
        local_result: LocalCheckResult,
        descent: DescentResult,
        cohomology: List[TensorCohomologyClass],
    ) -> str:
        """Build a human-readable explanation."""
        parts = []

        if verdict == EquivalenceVerdict.EQUIVALENT:
            parts.append("Functions are equivalent across all tensor sites")
        elif verdict == EquivalenceVerdict.INEQUIVALENT:
            failed = [j for j in local_result.judgments
                      if j.verdict == EquivalenceVerdict.INEQUIVALENT]
            kinds = [j.tensor_site_kind.name for j in failed]
            parts.append(f"Inequivalent at: {', '.join(kinds)}")

        if local_result.short_circuited_at:
            parts.append(f"Short-circuited at {local_result.short_circuited_at.name}")

        if descent.cocycle_violations:
            parts.append(f"{len(descent.cocycle_violations)} descent violations")

        if cohomology:
            non_trivial = [c for c in cohomology if not c.is_trivial]
            if non_trivial:
                parts.append(f"H¹ obstructions: {len(non_trivial)}")

        return "; ".join(parts) if parts else "Analysis complete"

    # -------------------------------------------------------------------
    # Single-program analysis (general, not equivalence-specific)
    # -------------------------------------------------------------------

    def analyze(
        self,
        fn: Callable,
        tensor_specs: Sequence[TensorSpec],
        test_inputs: Optional[Sequence[Sequence[Any]]] = None,
        triton_spec: Optional[TritonKernelSpec] = None,
        mlir_spec: Optional[MLIRModuleSpec] = None,
    ) -> "AnalysisJudgment":
        """
        Analyze a single PyTorch function for bugs.

        This is the global-level single-program analysis.  It:
        1. Runs local analysis at each tensor site
        2. Checks sheaf condition (section consistency)
        3. Collects bugs and produces an AnalysisJudgment

        Sheaf-theoretic interpretation: check if Γ(F_fn) is well-defined,
        i.e., the global sections functor produces a consistent result
        when applied to the single program's presheaf.
        """
        from ._protocols import (
            AnalysisMode, AnalysisVerdict, AnalysisJudgment as AJ,
            ProgramId, SheafConditionResult,
        )

        fn_name = getattr(fn, "__name__", "fn")
        program = ProgramId(name=fn_name)

        # Phase 1: Local single-program analysis
        local_result = self._local_checker.analyze_single(
            fn, tensor_specs, test_inputs, triton_spec, mlir_spec,
        )

        # Phase 2: Sheaf condition check
        sheaf_result = None
        try:
            from .sheaf_condition import TensorSheafConditionChecker
            sheaf_checker = TensorSheafConditionChecker(self._config)
            sheaf_result = sheaf_checker.check(fn, tensor_specs, test_inputs)
        except ImportError:
            pass
        except Exception:
            pass

        # Merge bugs
        all_bugs = list(local_result.bugs)
        if sheaf_result and hasattr(sheaf_result, 'gluing_failures'):
            from ._protocols import BugKind, Bug, SiteKind
            for sf, st in getattr(sheaf_result, 'gluing_failures', []):
                all_bugs.append(Bug(
                    kind=BugKind.SHEAF_GLUING_FAILURE,
                    stratum=TensorStratum.NUMERICAL,
                    site_id=sf if isinstance(sf, SiteId) else SiteId(
                        kind=SiteKind.TENSOR_SHAPE, name=str(sf)),
                    description=f"Gluing failure between {sf} and {st}",
                ))

        verdict = (AnalysisVerdict.INVALID if all_bugs
                   else AnalysisVerdict.VALID)

        return AJ(
            verdict=verdict,
            program=program,
            mode=AnalysisMode.BUG_FINDING,
            bugs=all_bugs,
            sheaf_condition=sheaf_result,
            stratum_results=local_result.stratum_results,
            explanation=(
                f"Found {len(all_bugs)} bug(s) in {fn_name}"
                if all_bugs else f"No bugs found in {fn_name}"
            ),
        )
