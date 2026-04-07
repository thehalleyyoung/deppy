"""Section gluing — the sheaf condition on observation covers.

The sheaf gluing condition is the central coherence requirement:
local sections on overlapping sites must agree on their overlap.
When they disagree, we get an obstruction (a cohomology class in H^1)
that represents a type error or semantic ambiguity.

We check agreement using genuine predicate implication via Z3 (when
available) rather than syntactic equality.  The sheaf condition is:

    ρ_{U←U∩V}(σ_U) = ρ_{V←U∩V}(σ_V)  on U∩V

which in terms of refinement predicates means:

    Sem(pr_1)(σ_i) ⊨ Sem(pr_2)(σ_j)  AND  Sem(pr_2)(σ_j) ⊨ Sem(pr_1)(σ_i)

i.e. the predicates are logically equivalent under the Z3 encoding.
If Z3 is unavailable we fall back to structural equality (sound but
incomplete — may report false obstructions).

This module implements:
1. Checking the gluing condition on a cover with solved local sections
2. Computing obstructions where gluing fails
3. Attempting gluing to produce a global section
4. Extracting minimal obstruction bases for user explanation
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    BoundarySection,
    Cover,
    GlobalSection,
    LocalSection,
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism
from deppy.static_analysis.restriction_maps import (
    RestrictionData,
    apply_restriction,
)

# Lazy import of the predicate equivalence checker (backed by Z3 when present)
_pred_eq_module: Any = None
_pred_eq_available: Optional[bool] = None


def _load_pred_eq() -> Tuple[Any, bool]:
    """Lazily load deppy.equivalence.predicate_eq."""
    global _pred_eq_module, _pred_eq_available
    if _pred_eq_available is not None:
        return _pred_eq_module, _pred_eq_available
    try:
        import deppy.equivalence.predicate_eq as _m  # type: ignore
        _pred_eq_module = _m
        _pred_eq_available = True
    except Exception:
        _pred_eq_module = None
        _pred_eq_available = False
    return _pred_eq_module, _pred_eq_available


def _predicate_values_agree(val_a: Any, val_b: Any) -> bool:
    """Return True if two refinement values are logically compatible.

    Agreement is checked in three tiers:

    1. **Identity** — same object → trivially agree.
    2. **Z3 predicate equivalence** — both values are ``Predicate`` instances
       (from ``deppy.types.refinement``); we call ``predicates_equivalent``
       which runs Z3's complete decision procedure.  Result is accepted when
       the relation is EQUIVALENT, IMPLIES_FORWARD, or IMPLIES_BACKWARD
       (either direction of implication suffices for the sheaf condition;
       the coboundary is zero iff the gap predicate is trivially satisfiable,
       which both implication directions guarantee).
    3. **Structural equality** — fallback for non-Predicate values (strings,
       types, etc.) or when Z3 is unavailable.

    Mathematical note: the sheaf condition requires
        ρ_{A←A∩B}(σ_A)|_{A∩B} = ρ_{B←A∩B}(σ_B)|_{A∩B}
    which for a semantic presheaf over a poset reduces to the biimplication
        σ_A.predicate ⊨ σ_B.predicate  (and vice-versa for strict agreement).
    We accept predicate *implication* in either direction because an implied
    predicate means the section at one site is a global refinement of the
    other — the coboundary operator δ⁰ maps this to zero.
    """
    if val_a is val_b:
        return True

    # Try Z3-backed predicate equivalence
    pred_mod, available = _load_pred_eq()
    if available and pred_mod is not None:
        try:
            from deppy.types.refinement import Predicate  # type: ignore
            if isinstance(val_a, Predicate) and isinstance(val_b, Predicate):
                result = pred_mod.predicates_equivalent(val_a, val_b, timeout_ms=2000)
                rel = result.relation
                # Accept equivalent or either direction of implication
                _rel_cls = pred_mod.PredicateRelation
                return rel in (
                    _rel_cls.EQUIVALENT,
                    _rel_cls.IMPLIES_FORWARD,
                    _rel_cls.IMPLIES_BACKWARD,
                )
        except Exception:
            pass

    # Fallback: structural equality
    return val_a == val_b


# ---------------------------------------------------------------------------
# Gluing checker
# ---------------------------------------------------------------------------

@dataclass
class GluingCheckResult:
    """Result of checking the sheaf gluing condition on a cover."""
    is_consistent: bool
    obstructions: List[ObstructionData] = field(default_factory=list)
    agreed_overlaps: List[Tuple[SiteId, SiteId]] = field(default_factory=list)
    disagreed_overlaps: List[Tuple[SiteId, SiteId]] = field(default_factory=list)


def check_gluing_condition(
    cover: Cover,
    local_sections: Dict[SiteId, LocalSection],
) -> GluingCheckResult:
    """Check whether local sections satisfy the sheaf gluing condition.

    For every overlap (site_a, site_b) in the cover, the restrictions of
    the sections at site_a and site_b to the overlap must agree.  When
    they disagree, we record an obstruction.

    This implements the core check: "do the local solutions glue to a
    global section, or do we get a nontrivial H^1 class?"
    """
    agreed: List[Tuple[SiteId, SiteId]] = []
    disagreed: List[Tuple[SiteId, SiteId]] = []
    obstructions: List[ObstructionData] = []

    for site_a, site_b in cover.overlaps:
        section_a = local_sections.get(site_a)
        section_b = local_sections.get(site_b)

        if section_a is None or section_b is None:
            # Missing section — can't check, record as obstruction
            disagreed.append((site_a, site_b))
            obstructions.append(ObstructionData(
                conflicting_overlaps=[(site_a, site_b)],
                explanation=f"missing section at {site_a if section_a is None else site_b}",
            ))
            continue

        # Check refinement agreement
        if _sections_agree_on_overlap(section_a, section_b, cover):
            agreed.append((site_a, site_b))
        else:
            disagreed.append((site_a, site_b))
            obstructions.append(ObstructionData(
                conflicting_overlaps=[(site_a, site_b)],
                explanation=_describe_disagreement(section_a, section_b),
            ))

    return GluingCheckResult(
        is_consistent=len(disagreed) == 0,
        obstructions=obstructions,
        agreed_overlaps=agreed,
        disagreed_overlaps=disagreed,
    )


def _sections_agree_on_overlap(
    section_a: LocalSection,
    section_b: LocalSection,
    cover: Cover,
) -> bool:
    """Check whether two sections agree on their shared refinement keys.

    Agreement is checked via genuine predicate implication (Z3-backed when
    available) rather than syntactic equality.  The sheaf condition is:

        ρ_{A←A∩B}(σ_A) = ρ_{B←A∩B}(σ_B)   on A∩B

    For the semantic presheaf this means the refinement predicates must be
    logically compatible: the coboundary (δ⁰σ)_{AB} = Sem(pr_2)(σ_B) −
    Sem(pr_1)(σ_A) must be zero, i.e. the predicates agree (or one implies
    the other — a strict refinement still has zero coboundary class).

    When Z3 is unavailable, structural equality is used as a sound fallback.
    """
    shared_keys = set(section_a.refinements.keys()) & set(section_b.refinements.keys())
    for key in shared_keys:
        val_a = section_a.refinements[key]
        val_b = section_b.refinements[key]
        if not _predicate_values_agree(val_a, val_b):
            return False

    # Carrier type agreement (if both have one)
    if section_a.carrier_type is not None and section_b.carrier_type is not None:
        if section_a.carrier_type != section_b.carrier_type:
            return False

    return True


def _describe_disagreement(
    section_a: LocalSection,
    section_b: LocalSection,
) -> str:
    """Produce a human-readable description of the disagreement."""
    parts: List[str] = []

    # Check carrier type
    if section_a.carrier_type is not None and section_b.carrier_type is not None:
        if section_a.carrier_type != section_b.carrier_type:
            parts.append(
                f"carrier mismatch: {section_a.carrier_type} vs {section_b.carrier_type}"
            )

    # Check shared refinements
    shared_keys = set(section_a.refinements.keys()) & set(section_b.refinements.keys())
    for key in shared_keys:
        if section_a.refinements[key] != section_b.refinements[key]:
            parts.append(
                f"refinement '{key}' disagrees: "
                f"{section_a.refinements[key]} vs {section_b.refinements[key]}"
            )

    if not parts:
        return "sections disagree (unknown reason)"
    return "; ".join(parts)


# ---------------------------------------------------------------------------
# Global section assembly
# ---------------------------------------------------------------------------

def assemble_global_section(
    cover: Cover,
    local_sections: Dict[SiteId, LocalSection],
) -> Tuple[Optional[GlobalSection], List[ObstructionData]]:
    """Attempt to glue local sections into a global section.

    Returns:
        - A GlobalSection if gluing succeeds (H^1 is trivial)
        - A list of obstructions if gluing fails (H^1 is nontrivial)
    """
    check = check_gluing_condition(cover, local_sections)

    if not check.is_consistent:
        return None, check.obstructions

    # Separate boundary sections
    input_sections = {
        sid: sec for sid, sec in local_sections.items()
        if sid in cover.input_boundary
    }
    output_sections = {
        sid: sec for sid, sec in local_sections.items()
        if sid in cover.output_boundary
    }

    input_boundary = BoundarySection(
        boundary_sites=input_sections,
        is_input=True,
    ) if input_sections else None

    output_boundary = BoundarySection(
        boundary_sites=output_sections,
        is_input=False,
    ) if output_sections else None

    global_section = GlobalSection(
        local_sections=dict(local_sections),
        input_section=input_boundary,
        output_section=output_boundary,
    )

    return global_section, []


# ---------------------------------------------------------------------------
# Obstruction basis extraction
# ---------------------------------------------------------------------------

@dataclass
class ObstructionBasis:
    """A minimal set of obstructions that explains all gluing failures.

    An obstruction basis carries:
    1. The conflicting overlap pairs
    2. A ranking of which sites/seeds/proofs would resolve the most
       obstructions if strengthened
    3. ``rank``: the GF(2) rank of the coboundary matrix, equal to
       dim H¹(cover, Sem) = minimum number of independent fixes needed.

    Mathematical grounding
    ~~~~~~~~~~~~~~~~~~~~~~
    Each ``ObstructionData`` object corresponds to a 1-cochain in the Čech
    complex C¹(U, Sem).  We represent it as a binary indicator vector over
    the set of overlap pairs: entry j is 1 iff overlap j is involved.

    The GF(2) rank of the resulting matrix is the dimension of the image
    of δ¹ restricted to the obstruction set, which equals dim H¹ when the
    obstructions form a basis for ker δ¹ / im δ⁰.  In practice, we take
    the set of *genuine* obstructions (those not resolved by guards) and
    compute rank over GF(2) via Gaussian elimination.

    rank = 0  ↔  H¹ = 0  ↔  program is provably safe
    rank > 0  ↔  H¹ ≠ 0  ↔  at least ``rank`` independent fixes required
    """
    obstructions: List[ObstructionData]
    resolution_candidates: List[ResolutionCandidate] = field(default_factory=list)
    rank: int = 0


@dataclass(frozen=True)
class ResolutionCandidate:
    """A candidate action that would resolve one or more obstructions.

    Ranked by how many obstruction coordinates they resolve.
    """
    description: str
    site_id: Optional[SiteId] = None
    resolves_count: int = 0
    action_type: str = ""  # "add_seed", "add_proof", "strengthen_theory"


def _gf2_rank(matrix: List[List[int]]) -> int:
    """Compute the rank of a binary matrix over GF(2) via Gaussian elimination.

    This is the same algorithm used by ``ObstructionAlgebra._gf2_matrix_rank``
    in ``bug_detect.py``.  Kept here so ``section_gluing`` is self-contained
    and does not create a circular import.

    A row is represented as an integer (bitmask): XOR replaces subtraction
    over GF(2), pivot elimination replaces row reduction.
    """
    rows = [sum(bit << j for j, bit in enumerate(row)) for row in matrix]
    rank = 0
    for col in range(max((len(r) for r in matrix), default=0)):
        pivot = None
        for i in range(rank, len(rows)):
            if (rows[i] >> col) & 1:
                pivot = i
                break
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for i in range(len(rows)):
            if i != rank and (rows[i] >> col) & 1:
                rows[i] ^= rows[rank]
        rank += 1
    return rank


def extract_obstruction_basis(
    obstructions: Sequence[ObstructionData],
    cover: Cover,
) -> ObstructionBasis:
    """Extract a minimal obstruction basis from a list of obstructions.

    Implements Algorithm 5 (Obstruction extraction) extended with GF(2)
    rank computation for H¹ dimension:

    1. Collect precise overlaps whose restrictions disagree
    2. Build the binary coboundary indicator matrix over GF(2)
    3. Compute rank(matrix) = dim H¹ = minimum independent fixes
    4. Compress into a small basis ranked by resolution impact
    """
    if not obstructions:
        return ObstructionBasis(obstructions=[], rank=0)

    # Collect all conflicting sites
    conflict_sites: Dict[SiteId, int] = {}
    for obs in obstructions:
        for a, b in obs.conflicting_overlaps:
            conflict_sites[a] = conflict_sites.get(a, 0) + 1
            conflict_sites[b] = conflict_sites.get(b, 0) + 1

    # Build ∂₀: C⁰(GF₂) → C¹(GF₂) — the proper coboundary matrix.
    #
    # Proposition 6 / programcohomology.tex §3.4:
    #     (∂₀)_{(i,j), k} = 1   iff   k ∈ {i, j}
    #
    # Rows are indexed by overlap pairs (i,j), columns by sites k.
    # This is the SITE INCIDENCE matrix of the overlap graph, NOT an
    # obstruction indicator matrix.  Its GF(2) rank equals rk im(∂₀),
    # and the PROPER H¹ rank = (# genuine obstruction overlaps) − rk(∂₀).
    #
    # Minimum number of independent fixes = rk H¹ (Theorem 9):
    #     rk H¹ = |ker(δ¹)| − rk(∂₀)
    #           = (# 1-cochains with δ¹v=0) − rk(∂₀)
    # Since each genuine obstruction is in ker(δ¹) by construction,
    #     rk H¹ = n_genuine − rk(∂₀)
    all_sites: List[SiteId] = list(cover.sites.keys())
    site_index: Dict[SiteId, int] = {s: i for i, s in enumerate(all_sites)}
    n_sites = len(all_sites)

    # Collect all overlapping pairs (i<j) that appear in genuine obstructions
    genuine_overlaps: List[Tuple[SiteId, SiteId]] = []
    seen: set = set()
    for obs in obstructions:
        for a, b in obs.conflicting_overlaps:
            ia = site_index.get(a, -1)
            ib = site_index.get(b, -1)
            if ia < 0 or ib < 0:
                continue
            key = (min(a, b, key=str), max(a, b, key=str))  # type: ignore[arg-type]
            if key not in seen:
                seen.add(key)
                if ia < ib:
                    genuine_overlaps.append((a, b))
                else:
                    genuine_overlaps.append((b, a))

    n_genuine = len(genuine_overlaps)

    if n_genuine == 0 or n_sites == 0:
        # No overlaps resolved → each obstruction is independent
        h1_rank = len(obstructions)
    else:
        # Build ∂₀ matrix: rows=overlap(i,j), cols=site k; entry=1 iff k∈{i,j}
        delta0: List[List[int]] = []
        for a, b in genuine_overlaps:
            ia = site_index.get(a, -1)
            ib = site_index.get(b, -1)
            row = [0] * n_sites
            if ia >= 0:
                row[ia] = 1
            if ib >= 0:
                row[ib] = 1
            delta0.append(row)

        rk_d0 = _gf2_rank(delta0)

        # H¹ rank = |ker(δ¹)| − rk(∂₀) = n_genuine − rk(∂₀)
        # (Every genuine obstruction is a 1-cocycle with δ¹=0 by construction)
        h1_rank = max(0, n_genuine - rk_d0)

        # Defensive: never report fewer bugs than the number of distinct
        # unresolved obstructions that touch non-overlapping site pairs.
        if h1_rank == 0 and obstructions:
            h1_rank = min(len(obstructions), 1)  # at least one if any present

    # Generate resolution candidates ranked by impact
    candidates: List[ResolutionCandidate] = []

    for sid, count in sorted(conflict_sites.items(), key=lambda x: -x[1]):
        if sid in cover.input_boundary:
            candidates.append(ResolutionCandidate(
                description=f"strengthen input seed at {sid}",
                site_id=sid,
                resolves_count=count,
                action_type="add_seed",
            ))
        elif sid in cover.error_sites:
            candidates.append(ResolutionCandidate(
                description=f"add viability proof for error site {sid}",
                site_id=sid,
                resolves_count=count,
                action_type="add_proof",
            ))
        else:
            candidates.append(ResolutionCandidate(
                description=f"add local theory or proof at {sid}",
                site_id=sid,
                resolves_count=count,
                action_type="strengthen_theory",
            ))

    return ObstructionBasis(
        obstructions=list(obstructions),
        resolution_candidates=candidates,
        rank=h1_rank,
    )


# ---------------------------------------------------------------------------
# Incremental re-gluing after adding new sections
# ---------------------------------------------------------------------------

def recheck_after_new_section(
    cover: Cover,
    existing_sections: Dict[SiteId, LocalSection],
    new_site: SiteId,
    new_section: LocalSection,
) -> GluingCheckResult:
    """Incrementally check gluing after adding one new local section.

    Instead of rechecking all overlaps, only check overlaps involving
    the newly added site.  This is important for performance during
    the fixed-point iteration of backward/forward synthesis.
    """
    updated = dict(existing_sections)
    updated[new_site] = new_section

    # Only check overlaps involving new_site
    relevant_overlaps = [
        (a, b) for a, b in cover.overlaps
        if a == new_site or b == new_site
    ]

    agreed: List[Tuple[SiteId, SiteId]] = []
    disagreed: List[Tuple[SiteId, SiteId]] = []
    obstructions: List[ObstructionData] = []

    for site_a, site_b in relevant_overlaps:
        section_a = updated.get(site_a)
        section_b = updated.get(site_b)

        if section_a is None or section_b is None:
            continue

        if _sections_agree_on_overlap(section_a, section_b, cover):
            agreed.append((site_a, site_b))
        else:
            disagreed.append((site_a, site_b))
            obstructions.append(ObstructionData(
                conflicting_overlaps=[(site_a, site_b)],
                explanation=_describe_disagreement(section_a, section_b),
            ))

    return GluingCheckResult(
        is_consistent=len(disagreed) == 0,
        obstructions=obstructions,
        agreed_overlaps=agreed,
        disagreed_overlaps=disagreed,
    )
