"""
Bridge between the torch equivalence layer and the base deppy framework.

This module enables the torch layer to *use* the categorical machinery
already implemented in the base deppy equivalence package:

  1. **Bug detection bridge** — Runs ``deppy.render.bug_detect.detect_bugs``
     on torch function source code, converting ``GluingObstruction``s into
     the unified ``Bug`` type.  This catches Python-level bugs (div-zero,
     null-ptr, key-error, data-race, taint, ...) *alongside* tensor-level
     bugs (shape mismatch, numerical instability, unmasked access, ...).

  2. **Judgment bridge** — Converts ``TensorLocalJudgment`` to the base
     ``LocalEquivalenceJudgment`` so that the base Čech cohomology and
     descent checkers can consume torch results directly.

  3. **Cohomology bridge** — Delegates to the base ``CechCohomologyComputer``
     for full H⁰/H¹ computation rather than the hand-rolled extraction.

  4. **Descent bridge** — Delegates to the base ``EquivalenceDescentChecker``
     for formal cocycle verification.

Sheaf-theoretically, this module is a **functor** from the tensor site
category to the base deppy site category, preserving the obstruction
algebra structure.
"""

from __future__ import annotations

import inspect
import textwrap
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Sequence, Tuple

from deppy.core._protocols import SiteId, SiteKind
from deppy.core.site import SiteCategory, Site

from deppy.equivalence._protocols import (
    EquivalenceObligation,
    EquivalenceObstruction,
    EquivalenceStrength,
    EquivalenceVerdict as BaseVerdict,
    LocalEquivalenceJudgment,
)
from deppy.equivalence.cohomology import (
    CechCohomologyComputer,
    CechCohomologyResult,
    extract_obstructions_from_h1,
)
from deppy.equivalence.descent import (
    DescentDatumBuilder,
    EquivalenceDescentChecker,
    DescentResult as BaseDescentResult,
)

from ._protocols import (
    AnalysisVerdict,
    Bug,
    BugKind,
    EquivalenceVerdict,
    SiteId as TorchSiteId,
    TensorCohomologyClass,
    TensorLocalJudgment,
    TensorObstruction,
    TensorStratum,
    SITE_KIND_STRATUM,
)


# ═══════════════════════════════════════════════════════════════════════════════
# 1. Bug-detect bridge — Python-level bug detection on torch functions
# ═══════════════════════════════════════════════════════════════════════════════

# Mapping from bug_detect bug_type strings → BugKind enum values.
_BUGDETECT_TO_BUGKIND: Dict[str, BugKind] = {
    "division_by_zero": BugKind.DIV_ZERO,
    "null_dereference": BugKind.NULL_DEREF,
    "null_ptr": BugKind.NULL_DEREF,
    "index_out_of_bounds": BugKind.INDEX_OUT_OF_BOUNDS,
    "key_error": BugKind.KEY_MISSING,
    "type_error": BugKind.TYPE_ERROR,
    "type_confusion": BugKind.TYPE_ERROR,
    "unbound_variable": BugKind.UNBOUND_VARIABLE,
    "unbound_var": BugKind.UNBOUND_VARIABLE,
    "integer_overflow": BugKind.INTEGER_OVERFLOW,
    "fp_domain": BugKind.FP_DOMAIN_ERROR,
    "memory_leak": BugKind.RESOURCE_LEAK,
    "use_after_close": BugKind.USE_AFTER_CLOSE,
    "use_after_free": BugKind.USE_AFTER_CLOSE,
    "double_free": BugKind.USE_AFTER_CLOSE,
    "double_close": BugKind.USE_AFTER_CLOSE,
    "data_race": BugKind.DATA_RACE,
    "concurrent_modification": BugKind.DATA_RACE,
    "non_termination": BugKind.NON_TERMINATION,
    "stack_overflow": BugKind.STACK_OVERFLOW,
    "assert_failure": BugKind.ASSERT_FAILURE,
    "bounds": BugKind.INDEX_OUT_OF_BOUNDS,
    "sql_injection": BugKind.TAINT_FLOW,
    "command_injection": BugKind.TAINT_FLOW,
    "code_injection": BugKind.TAINT_FLOW,
    "xss": BugKind.TAINT_FLOW,
    "ssrf": BugKind.TAINT_FLOW,
    "path_traversal": BugKind.TAINT_FLOW,
    "iterator_protocol": BugKind.PROTOCOL_VIOLATION,
    "context_manager_protocol": BugKind.PROTOCOL_VIOLATION,
    "value_error": BugKind.EXCEPTION_DIVERGENCE,
    "runtime_error": BugKind.EXCEPTION_DIVERGENCE,
}


def detect_python_bugs(fn: Callable) -> List[Bug]:
    """Run the base sheaf-theoretic bug detector on a torch function.

    Uses ``inspect.getsource`` to extract source, then delegates to
    ``deppy.render.bug_detect.detect_bugs`` for the full 6-phase pipeline:
    presheaf construction → requirement extraction → section assignment →
    guard recognition → obstruction resolution → Z3 discharge.

    Returns Bug instances compatible with the torch analysis pipeline.
    """
    try:
        from deppy.render.bug_detect import detect_bugs
    except ImportError:
        return []

    # Extract source code
    try:
        source = inspect.getsource(fn)
        source = textwrap.dedent(source)
    except (OSError, TypeError):
        return []

    fn_name = getattr(fn, "__name__", "") or getattr(fn, "__qualname__", "")

    # Run the base sheaf-theoretic bug detector
    try:
        report = detect_bugs(source, function_name=fn_name)
    except Exception:
        return []

    # Convert GluingObstructions → Bug instances
    bugs: List[Bug] = []
    for obs in report.obstructions:
        if obs.resolved_by_guard:
            continue  # Guard resolved — not a genuine bug
        if obs.z3_status == "unsat":
            continue  # Z3 proved unreachable

        bug_kind = _BUGDETECT_TO_BUGKIND.get(
            obs.bug_type, BugKind.SHEAF_GLUING_FAILURE
        )

        bugs.append(Bug(
            kind=bug_kind,
            stratum=TensorStratum.BEHAVIORAL,
            site_id=SiteId(
                kind=SiteKind.TENSOR_SHAPE,
                name=f"python_{obs.bug_type}_L{obs.line}",
            ),
            description=(
                f"[Python] {obs.description}"
                if obs.description
                else f"[Python] {obs.bug_type} at line {obs.line}"
            ),
            repair_hint=(
                str(obs.repair_guard)
                if obs.repair_guard is not None
                else None
            ),
            severity=obs.confidence,
        ))

    return bugs


# ═══════════════════════════════════════════════════════════════════════════════
# 2. Judgment bridge — TensorLocalJudgment → base LocalEquivalenceJudgment
# ═══════════════════════════════════════════════════════════════════════════════

def _verdict_to_base(v: EquivalenceVerdict) -> BaseVerdict:
    """Convert torch EquivalenceVerdict to base EquivalenceVerdict."""
    return BaseVerdict[v.name]


def tensor_judgment_to_base(
    tj: TensorLocalJudgment,
) -> LocalEquivalenceJudgment:
    """Convert a TensorLocalJudgment to a base LocalEquivalenceJudgment.

    This is the image of the tensor judgment under the forgetful functor
    from the tensor site category to the base site category.
    """
    return LocalEquivalenceJudgment(
        site_id=tj.site_id,
        verdict=_verdict_to_base(tj.verdict),
        obligation=EquivalenceObligation(
            site_id=tj.site_id,
            description=tj.explanation or f"{tj.tensor_site_kind.name} check",
        ),
        explanation=tj.explanation or "",
    )


def build_base_site_category(
    judgments: Sequence[TensorLocalJudgment],
) -> SiteCategory:
    """Build a base SiteCategory from tensor local judgments.

    Creates sites for each judgment and morphisms connecting
    sites within the same stratum (since they share restrictions).
    """
    from deppy.core.site import ConcreteMorphism

    cat = SiteCategory()

    # Add a site for each judgment
    for j in judgments:
        site = Site(site_id=j.site_id)
        cat.add_site(site)

    # Add morphisms between sites that share a stratum.
    # Within a stratum, sections should restrict consistently → overlap.
    sites_by_stratum: Dict[TensorStratum, List[SiteId]] = {}
    for j in judgments:
        stratum = SITE_KIND_STRATUM.get(j.tensor_site_kind, TensorStratum.METADATA)
        sites_by_stratum.setdefault(stratum, []).append(j.site_id)

    # Cross-stratum morphisms follow the filtration order:
    # METADATA → STRUCTURAL → NUMERICAL → BEHAVIORAL
    # Lower strata restrict to higher strata.
    sorted_strata = sorted(sites_by_stratum.keys(), key=lambda s: s.value)
    for i, src_stratum in enumerate(sorted_strata):
        for tgt_stratum in sorted_strata[i + 1:]:
            for src_sid in sites_by_stratum[src_stratum]:
                for tgt_sid in sites_by_stratum[tgt_stratum]:
                    # Create a morphism from the base site to the extension site.
                    # This records that lower-stratum info restricts to higher strata.
                    common_target = SiteId(
                        kind=SiteKind.TENSOR_SHAPE,
                        name=f"overlap_{src_sid.name}_{tgt_sid.name}",
                    )
                    overlap_site = Site(site_id=common_target)
                    cat.add_site(overlap_site)
                    cat.add_morphism(ConcreteMorphism(
                        source=src_sid, target=common_target,
                    ))
                    cat.add_morphism(ConcreteMorphism(
                        source=tgt_sid, target=common_target,
                    ))

    # Within each stratum, create pairwise overlaps
    for stratum, sids in sites_by_stratum.items():
        if len(sids) < 2:
            continue
        for i, s1 in enumerate(sids):
            for s2 in sids[i + 1:]:
                common_target = SiteId(
                    kind=SiteKind.TENSOR_SHAPE,
                    name=f"intra_{s1.name}_{s2.name}",
                )
                overlap_site = Site(site_id=common_target)
                cat.add_site(overlap_site)
                cat.add_morphism(ConcreteMorphism(
                    source=s1, target=common_target,
                ))
                cat.add_morphism(ConcreteMorphism(
                    source=s2, target=common_target,
                ))

    return cat


# ═══════════════════════════════════════════════════════════════════════════════
# 3. Cohomology bridge — delegate to base CechCohomologyComputer
# ═══════════════════════════════════════════════════════════════════════════════

def compute_cohomology_via_base(
    judgments: Sequence[TensorLocalJudgment],
) -> Tuple[CechCohomologyResult, List[TensorCohomologyClass]]:
    """Compute Čech cohomology through the base framework.

    Converts tensor judgments → base judgments, builds a site category,
    then delegates to ``CechCohomologyComputer`` for the full
    C⁰ → C¹ → C² → H⁰, H¹ computation.

    Returns both the raw ``CechCohomologyResult`` and a list of
    ``TensorCohomologyClass`` instances for the torch layer.
    """
    # Convert to base types
    base_judgments = {
        tj.site_id: tensor_judgment_to_base(tj)
        for tj in judgments
    }

    # Build site category and find overlaps
    cat = build_base_site_category(judgments)
    site_ids = frozenset(tj.site_id for tj in judgments)
    overlaps = cat.find_overlaps(site_ids)

    # Delegate to base cohomology computer
    computer = CechCohomologyComputer(
        judgments=base_judgments,
        overlaps=overlaps,
    )
    result = computer.compute()

    # Convert H¹ obstructions back to tensor cohomology classes
    tensor_classes: List[TensorCohomologyClass] = []

    if result.h1_trivial:
        # No obstructions — all cohomology trivial
        tensor_classes.append(TensorCohomologyClass(
            degree=0,
            representative_sites=list(site_ids),
            is_trivial=True,
            obstruction_description="",
        ))
    else:
        # Extract obstructions from H¹
        base_obstructions = extract_obstructions_from_h1(result)
        for obs in base_obstructions:
            tensor_classes.append(TensorCohomologyClass(
                degree=1,
                representative_sites=[obs.site_id] if hasattr(obs, 'site_id') else [],
                is_trivial=False,
                obstruction_description=str(obs),
            ))

    return result, tensor_classes


# ═══════════════════════════════════════════════════════════════════════════════
# 4. Descent bridge — delegate to base EquivalenceDescentChecker
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class FullDescentResult:
    """Extended descent result combining base + tensor-specific checks."""
    is_effective: bool = False
    cocycle_violations: List[str] = field(default_factory=list)
    glued_verdict: EquivalenceVerdict = EquivalenceVerdict.UNKNOWN
    base_result: Optional[BaseDescentResult] = None
    cohomology_result: Optional[CechCohomologyResult] = None


def verify_descent_via_base(
    judgments: Sequence[TensorLocalJudgment],
) -> FullDescentResult:
    """Verify the descent condition through the base framework.

    Delegates to ``EquivalenceDescentChecker`` which internally:
    1. Builds the Čech complex from local judgments
    2. Computes H⁰ (global sections) and H¹ (obstructions)
    3. Checks if H¹ = 0 (descent holds)
    4. Extracts and classifies obstructions if H¹ ≠ 0
    """
    base_judgments_list = [tensor_judgment_to_base(tj) for tj in judgments]
    cat = build_base_site_category(judgments)

    checker = EquivalenceDescentChecker(site_category=cat)
    base_result = checker.check(base_judgments_list)

    # Convert back to torch descent result
    violations = [str(obs) for obs in base_result.obstructions]

    # Determine glued verdict from judgment majority
    equiv_count = sum(1 for j in judgments if j.verdict == EquivalenceVerdict.EQUIVALENT)
    inequiv_count = sum(1 for j in judgments if j.verdict == EquivalenceVerdict.INEQUIVALENT)

    if base_result.descent_holds and inequiv_count == 0:
        glued = EquivalenceVerdict.EQUIVALENT
    elif inequiv_count > 0:
        glued = EquivalenceVerdict.INEQUIVALENT
    else:
        glued = EquivalenceVerdict.UNKNOWN

    return FullDescentResult(
        is_effective=base_result.descent_holds,
        cocycle_violations=violations,
        glued_verdict=glued,
        base_result=base_result,
        cohomology_result=base_result.cohomology_result,
    )
