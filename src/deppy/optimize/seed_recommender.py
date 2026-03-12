"""Recommend seeds, proofs, and theory activations for residual obstructions.

Given the residual obstructions that remain after the frontier search,
SeedRecommender determines which annotations, proofs, or library theory
activations would resolve them.  Each recommendation carries a rationale,
expected benefit, and the specific sites it targets.
"""

from __future__ import annotations

import math
from collections import defaultdict
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    Cover,
    LocalSection,
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)


# ---------------------------------------------------------------------------
# Recommendation kinds
# ---------------------------------------------------------------------------

class RecommendationKind:
    """Classification of recommendation types."""

    ANNOTATION = "annotation"
    PROOF = "proof"
    THEORY_ACTIVATION = "theory_activation"
    INVARIANT_SEED = "invariant_seed"
    TRUST_UPGRADE = "trust_upgrade"
    GUARD_SEED = "guard_seed"


# ---------------------------------------------------------------------------
# Recommendation data class
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Recommendation:
    """A recommended action to resolve one or more residual obstructions.

    Attributes:
        kind: The type of recommendation (annotation, proof, etc.).
        description: Human-readable explanation of what to do.
        target_sites: The sites this recommendation applies to.
        expected_benefit: Estimated fraction of obstructions resolved.
        rationale: Why this recommendation was generated.
        code_hint: Optional code fragment illustrating the recommendation.
        obstructions_addressed: Indices into the residual list.
        priority: Ordering priority (lower = more urgent).
    """

    _kind: str
    _description: str
    _target_sites: FrozenSet[SiteId]
    _expected_benefit: float
    _rationale: str
    _code_hint: str = ""
    _obstructions_addressed: Tuple[int, ...] = ()
    _priority: int = 5

    @property
    def kind(self) -> str:
        return self._kind

    @property
    def description(self) -> str:
        return self._description

    @property
    def target_sites(self) -> FrozenSet[SiteId]:
        return self._target_sites

    @property
    def expected_benefit(self) -> float:
        return self._expected_benefit

    @property
    def rationale(self) -> str:
        return self._rationale

    @property
    def code_hint(self) -> str:
        return self._code_hint

    @property
    def obstructions_addressed(self) -> Tuple[int, ...]:
        return self._obstructions_addressed

    @property
    def priority(self) -> int:
        return self._priority


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

def _sites_from_obs(obs: ObstructionData) -> Set[SiteId]:
    """Collect all sites referenced in an obstruction."""
    sites: Set[SiteId] = set()
    for a_id, b_id in obs.conflicting_overlaps:
        sites.add(a_id)
        sites.add(b_id)
    return sites


def _site_kind_distribution(sites: Set[SiteId]) -> Dict[SiteKind, int]:
    """Count site kinds in a set of sites."""
    dist: Dict[SiteKind, int] = defaultdict(int)
    for sid in sites:
        dist[sid.kind] += 1
    return dict(dist)


def _has_loop_sites(sites: Set[SiteId]) -> bool:
    """Check if any site is a loop header invariant."""
    return any(s.kind == SiteKind.LOOP_HEADER_INVARIANT for s in sites)


def _has_boundary_sites(sites: Set[SiteId]) -> bool:
    """Check if any site is an argument or return boundary."""
    return any(
        s.kind in (SiteKind.ARGUMENT_BOUNDARY, SiteKind.RETURN_OUTPUT_BOUNDARY)
        for s in sites
    )


def _has_proof_sites(sites: Set[SiteId]) -> bool:
    """Check if any site is a proof site."""
    return any(s.kind == SiteKind.PROOF for s in sites)


def _has_tensor_sites(sites: Set[SiteId]) -> bool:
    """Check if any site involves tensors."""
    return any(
        s.kind in (SiteKind.TENSOR_SHAPE, SiteKind.TENSOR_ORDER, SiteKind.TENSOR_INDEXING)
        for s in sites
    )


def _extract_variable(site_id: SiteId) -> str:
    """Extract a variable name from a site ID."""
    parts = site_id.name.rsplit(".", 1)
    return parts[-1] if parts else site_id.name


# ---------------------------------------------------------------------------
# Recommendation generators
# ---------------------------------------------------------------------------

def _recommend_annotation(
    obs: ObstructionData,
    obs_idx: int,
    sites: Set[SiteId],
) -> Optional[Recommendation]:
    """Recommend adding a type annotation at boundary sites."""
    boundary_sites = {
        s for s in sites
        if s.kind in (SiteKind.ARGUMENT_BOUNDARY, SiteKind.RETURN_OUTPUT_BOUNDARY)
    }
    if not boundary_sites:
        all_sites = sites
    else:
        all_sites = boundary_sites

    var_names = [_extract_variable(s) for s in all_sites]
    vars_str = ", ".join(sorted(set(var_names))[:3])

    return Recommendation(
        _kind=RecommendationKind.ANNOTATION,
        _description=(
            f"Add type annotations for {vars_str} to resolve "
            f"the type ambiguity at this site."
        ),
        _target_sites=frozenset(all_sites),
        _expected_benefit=0.7,
        _rationale=(
            f"The obstruction arises because types cannot be inferred "
            f"at {len(all_sites)} site(s). Explicit annotations would "
            f"provide the missing type information."
        ),
        _code_hint=(
            f"# Add type annotations:\n"
            f"def func({vars_str}: ExpectedType) -> ReturnType:\n"
            f"    ..."
        ),
        _obstructions_addressed=(obs_idx,),
        _priority=3,
    )


def _recommend_proof(
    obs: ObstructionData,
    obs_idx: int,
    sites: Set[SiteId],
) -> Optional[Recommendation]:
    """Recommend providing a proof obligation."""
    explanation = obs.explanation.lower()

    if "bound" in explanation or "range" in explanation:
        proof_kind = "bounds proof"
        code_hint = (
            "# Provide a bounds proof:\n"
            "@deppy.proof\n"
            "def bounds_proof(x: int) -> deppy.Proof[x >= 0]:\n"
            "    return deppy.by_construction(x)"
        )
    elif "invariant" in explanation:
        proof_kind = "loop invariant proof"
        code_hint = (
            "# Provide a loop invariant:\n"
            "@deppy.invariant\n"
            "def loop_inv(i: int, acc: int) -> deppy.Proof[acc >= 0]:\n"
            "    return deppy.by_induction(base=0, step=lambda: acc + i)"
        )
    elif "none" in explanation or "optional" in explanation:
        proof_kind = "non-nullity proof"
        code_hint = (
            "# Provide a non-None proof:\n"
            "@deppy.proof\n"
            "def not_none_proof(x: T) -> deppy.Proof[x is not None]:\n"
            "    assert x is not None\n"
            "    return deppy.by_assertion()"
        )
    else:
        proof_kind = "type proof"
        code_hint = (
            "# Provide a type proof:\n"
            "@deppy.proof\n"
            "def type_proof(x: T) -> deppy.Proof[isinstance(x, Expected)]:\n"
            "    return deppy.by_isinstance_check(x, Expected)"
        )

    return Recommendation(
        _kind=RecommendationKind.PROOF,
        _description=(
            f"Provide a {proof_kind} to discharge the verification "
            f"condition at this site."
        ),
        _target_sites=frozenset(sites),
        _expected_benefit=0.85,
        _rationale=(
            f"The obstruction involves a property that cannot be "
            f"automatically verified. A user-supplied proof would "
            f"establish the required invariant."
        ),
        _code_hint=code_hint,
        _obstructions_addressed=(obs_idx,),
        _priority=4,
    )


def _recommend_theory_activation(
    obs: ObstructionData,
    obs_idx: int,
    sites: Set[SiteId],
) -> Optional[Recommendation]:
    """Recommend activating a library theory."""
    explanation = obs.explanation.lower()
    theories: List[Tuple[str, str]] = []

    if _has_tensor_sites(sites) or "tensor" in explanation or "shape" in explanation:
        theories.append((
            "tensor_algebra",
            "Activate tensor algebra theory for shape reasoning",
        ))

    if "sort" in explanation or "order" in explanation:
        theories.append((
            "total_order",
            "Activate total order theory for comparison reasoning",
        ))

    if "collection" in explanation or "list" in explanation or "set" in explanation:
        theories.append((
            "collection_theory",
            "Activate collection theory for membership/length reasoning",
        ))

    if "arith" in explanation or "numeric" in explanation or "overflow" in explanation:
        theories.append((
            "linear_arithmetic",
            "Activate linear arithmetic theory for numeric reasoning",
        ))

    if not theories:
        theories.append((
            "default_theory",
            "Activate default background theory",
        ))

    theory_name, theory_desc = theories[0]
    code_hint = (
        f"# Activate the {theory_name} theory:\n"
        f"import deppy.library_theories.{theory_name} as theory\n"
        f"deppy.activate_theory(theory)"
    )

    return Recommendation(
        _kind=RecommendationKind.THEORY_ACTIVATION,
        _description=theory_desc,
        _target_sites=frozenset(sites),
        _expected_benefit=0.60,
        _rationale=(
            f"The obstruction involves properties that the "
            f"'{theory_name}' theory can discharge automatically."
        ),
        _code_hint=code_hint,
        _obstructions_addressed=(obs_idx,),
        _priority=2,
    )


def _recommend_invariant_seed(
    obs: ObstructionData,
    obs_idx: int,
    sites: Set[SiteId],
) -> Optional[Recommendation]:
    """Recommend providing a loop invariant seed."""
    loop_sites = {s for s in sites if s.kind == SiteKind.LOOP_HEADER_INVARIANT}
    if not loop_sites:
        return None

    var_names = [_extract_variable(s) for s in loop_sites]
    vars_str = ", ".join(sorted(set(var_names))[:3])

    return Recommendation(
        _kind=RecommendationKind.INVARIANT_SEED,
        _description=(
            f"Provide a loop invariant for {vars_str} to enable "
            f"verification of the loop body."
        ),
        _target_sites=frozenset(loop_sites),
        _expected_benefit=0.80,
        _rationale=(
            f"The loop at this site requires an invariant to verify "
            f"that the type refinements are maintained across iterations."
        ),
        _code_hint=(
            f"# Loop invariant annotation:\n"
            f"@deppy.loop_invariant\n"
            f"def invariant({vars_str}):\n"
            f"    return {vars_str} >= 0  # adjust predicate"
        ),
        _obstructions_addressed=(obs_idx,),
        _priority=3,
    )


def _recommend_trust_upgrade(
    obs: ObstructionData,
    obs_idx: int,
    sites: Set[SiteId],
) -> Optional[Recommendation]:
    """Recommend upgrading trust level via runtime validation."""
    return Recommendation(
        _kind=RecommendationKind.TRUST_UPGRADE,
        _description=(
            "Add runtime validation to upgrade the trust level "
            "of the section at this site from RESIDUAL to TRACE_BACKED."
        ),
        _target_sites=frozenset(sites),
        _expected_benefit=0.50,
        _rationale=(
            "The current trust level is too low for the refinement "
            "to be considered valid. Runtime checks would establish "
            "trace-backed trust."
        ),
        _code_hint=(
            "# Add runtime validation:\n"
            "assert isinstance(value, expected_type), \\\n"
            '    f"Expected {expected_type}, got {type(value)}"\n'
            "# This establishes TRACE_BACKED trust"
        ),
        _obstructions_addressed=(obs_idx,),
        _priority=6,
    )


def _recommend_guard_seed(
    obs: ObstructionData,
    obs_idx: int,
    sites: Set[SiteId],
) -> Optional[Recommendation]:
    """Recommend a guard seed for branch narrowing."""
    guard_sites = {s for s in sites if s.kind == SiteKind.BRANCH_GUARD}
    target = guard_sites if guard_sites else sites

    var_names = [_extract_variable(s) for s in target]
    primary = var_names[0] if var_names else "x"

    return Recommendation(
        _kind=RecommendationKind.GUARD_SEED,
        _description=(
            f"Add a branch guard for '{primary}' to enable type narrowing."
        ),
        _target_sites=frozenset(target),
        _expected_benefit=0.75,
        _rationale=(
            "A guard condition would allow the type checker to narrow "
            "the type on the true branch, resolving the conflict."
        ),
        _code_hint=(
            f"if isinstance({primary}, ExpectedType):\n"
            f"    # narrowed: {primary} is ExpectedType\n"
            f"    ...\n"
            f"else:\n"
            f"    raise TypeError(f\"Unexpected type: {{type({primary})}}\")"
        ),
        _obstructions_addressed=(obs_idx,),
        _priority=2,
    )


# ---------------------------------------------------------------------------
# SeedRecommender
# ---------------------------------------------------------------------------

class SeedRecommender:
    """Recommend seeds/proofs/theory activations for residual obstructions.

    Given the list of unresolved obstructions and the cover topology,
    SeedRecommender generates a prioritized list of recommendations.
    """

    def __init__(
        self,
        *,
        max_recommendations_per_obs: int = 3,
        min_expected_benefit: float = 0.0,
    ) -> None:
        self._max_per_obs = max_recommendations_per_obs
        self._min_benefit = min_expected_benefit

    def recommend(
        self,
        residuals: List[ObstructionData],
        cover: Optional[Cover] = None,
    ) -> List[Recommendation]:
        """Generate recommendations for all residual obstructions.

        Returns a list sorted by priority then expected benefit.
        """
        if cover is None:
            cover = Cover()

        all_recs: List[Recommendation] = []

        for idx, obs in enumerate(residuals):
            if obs.is_trivial:
                continue

            sites = _sites_from_obs(obs)
            obs_recs = self._generate_for_obstruction(obs, idx, sites, cover)

            filtered = [
                r for r in obs_recs if r.expected_benefit >= self._min_benefit
            ]
            filtered.sort(key=lambda r: (r.priority, -r.expected_benefit))
            all_recs.extend(filtered[: self._max_per_obs])

        all_recs.sort(key=lambda r: (r.priority, -r.expected_benefit))
        return _deduplicate_recommendations(all_recs)

    def _generate_for_obstruction(
        self,
        obs: ObstructionData,
        idx: int,
        sites: Set[SiteId],
        cover: Cover,
    ) -> List[Recommendation]:
        """Generate all applicable recommendations for one obstruction."""
        recs: List[Recommendation] = []
        explanation = obs.explanation.lower()

        if _has_loop_sites(sites):
            inv_rec = _recommend_invariant_seed(obs, idx, sites)
            if inv_rec is not None:
                recs.append(inv_rec)

        if _has_boundary_sites(sites):
            ann_rec = _recommend_annotation(obs, idx, sites)
            if ann_rec is not None:
                recs.append(ann_rec)

        if (
            "bound" in explanation
            or "invariant" in explanation
            or "none" in explanation
            or _has_proof_sites(sites)
        ):
            proof_rec = _recommend_proof(obs, idx, sites)
            if proof_rec is not None:
                recs.append(proof_rec)

        if _has_tensor_sites(sites) or any(
            kw in explanation for kw in ("tensor", "shape", "sort", "arith")
        ):
            theory_rec = _recommend_theory_activation(obs, idx, sites)
            if theory_rec is not None:
                recs.append(theory_rec)

        if "guard" in explanation or "branch" in explanation or "narrowing" in explanation:
            guard_rec = _recommend_guard_seed(obs, idx, sites)
            if guard_rec is not None:
                recs.append(guard_rec)

        if not recs:
            ann_rec = _recommend_annotation(obs, idx, sites)
            if ann_rec is not None:
                recs.append(ann_rec)
            trust_rec = _recommend_trust_upgrade(obs, idx, sites)
            if trust_rec is not None:
                recs.append(trust_rec)

        return recs

    def summarize(
        self,
        recommendations: List[Recommendation],
    ) -> str:
        """Produce a human-readable summary of recommendations."""
        if not recommendations:
            return "No recommendations generated."

        lines: List[str] = []
        lines.append(f"Seed Recommendations ({len(recommendations)} total):")
        lines.append("=" * 60)

        by_kind: Dict[str, List[Recommendation]] = {}
        for r in recommendations:
            by_kind.setdefault(r.kind, []).append(r)

        for kind, kind_recs in sorted(by_kind.items()):
            lines.append(f"\n  [{kind}] ({len(kind_recs)} recommendations)")
            for i, r in enumerate(kind_recs, 1):
                sites_str = ", ".join(
                    str(s) for s in sorted(r.target_sites, key=str)
                )[:60]
                lines.append(
                    f"    {i}. [benefit={r.expected_benefit:.0%}] "
                    f"{r.description}"
                )
                lines.append(f"       Sites: {sites_str}")
                if r.code_hint:
                    first_line = r.code_hint.split("\n")[0]
                    lines.append(f"       Hint: {first_line}")

        return "\n".join(lines)


def _deduplicate_recommendations(
    recs: List[Recommendation],
) -> List[Recommendation]:
    """Remove duplicate recommendations targeting the same sites with the same kind."""
    seen: Set[Tuple[str, FrozenSet[SiteId]]] = set()
    deduped: List[Recommendation] = []
    for r in recs:
        key = (r.kind, r.target_sites)
        if key not in seen:
            seen.add(key)
            deduped.append(r)
    return deduped
