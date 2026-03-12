"""Search for optimal input/output refinement frontiers.

Implements the Pareto-optimal frontier search from Part V of the DepPy
monograph.  Given a cover and a family of local sections, FrontierSearch
finds:

- **Input frontier**: the least-restrictive input refinements that prevent
  all obstructions (type errors).
- **Output frontier**: the most-informative output refinements that can be
  soundly derived from the solved global section.

The search operates over the information lattice defined on local sections,
using a worklist algorithm that iteratively relaxes input constraints while
tightening output constraints until a Pareto-stable fixpoint is reached.
"""

from __future__ import annotations

import itertools
import math
from collections import defaultdict, deque
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterable,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    BoundarySection,
    Cover,
    FrontierPoint,
    FrontierSummary,
    GlobalSection,
    LocalSection,
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.types.base import (
    ANY_TYPE,
    NEVER_TYPE,
    AnyType,
    NeverType,
    TypeBase,
    type_join,
    type_meet,
)


# ---------------------------------------------------------------------------
# Data structures for frontier search
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class _FrontierCandidate:
    """An individual candidate on a Pareto frontier.

    Each candidate associates a set of input-site sections with a set of
    output-site sections plus a score vector used for dominance testing.
    """

    _input_sections: Dict[SiteId, LocalSection]
    _output_sections: Dict[SiteId, LocalSection]
    _residual_errors: FrozenSet[SiteId]
    _input_cost: float
    _output_info: float
    _proof_debt: int

    @property
    def input_sections(self) -> Dict[SiteId, LocalSection]:
        return dict(self._input_sections)

    @property
    def output_sections(self) -> Dict[SiteId, LocalSection]:
        return dict(self._output_sections)

    @property
    def residual_errors(self) -> FrozenSet[SiteId]:
        return self._residual_errors

    @property
    def input_cost(self) -> float:
        return self._input_cost

    @property
    def output_info(self) -> float:
        return self._output_info

    @property
    def proof_debt(self) -> int:
        return self._proof_debt


@dataclass(frozen=True)
class _DominanceVector:
    """Six-component objective vector for lexicographic dominance."""

    _residual_count: int
    _input_cost: float
    _output_info: float
    _local_coverage: float
    _proof_debt: int
    _explanation_complexity: float

    def dominates(self, other: _DominanceVector) -> bool:
        """Return True if self Pareto-dominates other (all <= and at least one <)."""
        s = (
            self._residual_count,
            self._input_cost,
            -self._output_info,
            -self._local_coverage,
            self._proof_debt,
            self._explanation_complexity,
        )
        o = (
            other._residual_count,
            other._input_cost,
            -other._output_info,
            -other._local_coverage,
            other._proof_debt,
            other._explanation_complexity,
        )
        all_leq = all(a <= b for a, b in zip(s, o))
        some_lt = any(a < b for a, b in zip(s, o))
        return all_leq and some_lt

    def to_tuple(self) -> Tuple[int, float, float, float, int, float]:
        return (
            self._residual_count,
            self._input_cost,
            self._output_info,
            self._local_coverage,
            self._proof_debt,
            self._explanation_complexity,
        )


@dataclass
class _SectionLattice:
    """Operations on the information lattice of local sections at a site.

    The lattice order is: bottom <= sigma <= top, where bottom = Any (no
    information) and top = Never (maximum information / contradiction).
    """

    _site_id: SiteId

    def bottom(self) -> LocalSection:
        """Return the bottom section (Any, no refinements)."""
        return LocalSection(
            site_id=self._site_id,
            carrier_type=ANY_TYPE,
            refinements={},
            trust=TrustLevel.ASSUMED,
            provenance="lattice_bottom",
        )

    def top(self) -> LocalSection:
        """Return the top section (Never, maximal refinements)."""
        return LocalSection(
            site_id=self._site_id,
            carrier_type=NEVER_TYPE,
            refinements={"_top": True},
            trust=TrustLevel.TRUSTED_AUTO,
            provenance="lattice_top",
        )

    def join(self, a: LocalSection, b: LocalSection) -> LocalSection:
        """Least upper bound: weaken to the join of carrier types, intersect
        refinements (keep only those present in both)."""
        joined_type = type_join(
            a.carrier_type if a.carrier_type is not None else ANY_TYPE,
            b.carrier_type if b.carrier_type is not None else ANY_TYPE,
        )
        common_keys = set(a.refinements.keys()) & set(b.refinements.keys())
        joined_refs: Dict[str, Any] = {}
        for k in common_keys:
            if a.refinements[k] == b.refinements[k]:
                joined_refs[k] = a.refinements[k]
        weaker_trust = _weaker_trust(a.trust, b.trust)
        return LocalSection(
            site_id=self._site_id,
            carrier_type=joined_type,
            refinements=joined_refs,
            trust=weaker_trust,
            provenance="join",
        )

    def meet(self, a: LocalSection, b: LocalSection) -> LocalSection:
        """Greatest lower bound: strengthen to the meet of carrier types,
        union refinements."""
        met_type = type_meet(
            a.carrier_type if a.carrier_type is not None else ANY_TYPE,
            b.carrier_type if b.carrier_type is not None else ANY_TYPE,
        )
        merged_refs: Dict[str, Any] = {}
        merged_refs.update(a.refinements)
        merged_refs.update(b.refinements)
        stronger_trust = _stronger_trust(a.trust, b.trust)
        return LocalSection(
            site_id=self._site_id,
            carrier_type=met_type,
            refinements=merged_refs,
            trust=stronger_trust,
            provenance="meet",
        )

    def leq(self, a: LocalSection, b: LocalSection) -> bool:
        """Return True if a carries at most the information of b."""
        if isinstance(a.carrier_type, AnyType):
            return True
        if isinstance(b.carrier_type, NeverType):
            return True
        a_keys = set(a.refinements.keys())
        b_keys = set(b.refinements.keys())
        if not a_keys <= b_keys:
            return False
        for k in a_keys:
            if a.refinements[k] != b.refinements.get(k):
                return False
        return True

    def information_content(self, section: LocalSection) -> float:
        """Compute an information score for a section.

        Higher means more refined/informative.  The score is the number of
        refinement keys plus a bonus for non-Any carrier types.
        """
        score = float(len(section.refinements))
        if section.carrier_type is not None and not isinstance(
            section.carrier_type, AnyType
        ):
            score += 1.0
        if isinstance(section.carrier_type, NeverType):
            score += 100.0
        return score

    def cost(self, section: LocalSection) -> float:
        """Compute the *cost* of requiring a section as input.

        More refinements = higher cost = more restrictive precondition.
        """
        return float(len(section.refinements)) + (
            0.0 if isinstance(section.carrier_type, AnyType) else 0.5
        )


def _weaker_trust(a: TrustLevel, b: TrustLevel) -> TrustLevel:
    """Return the weaker (less trusted) of two trust levels."""
    order = {
        TrustLevel.PROOF_BACKED: 5,
        TrustLevel.TRUSTED_AUTO: 4,
        TrustLevel.TRACE_BACKED: 3,
        TrustLevel.BOUNDED_AUTO: 2,
        TrustLevel.ASSUMED: 1,
        TrustLevel.RESIDUAL: 0,
    }
    if order.get(a, 0) <= order.get(b, 0):
        return a
    return b


def _stronger_trust(a: TrustLevel, b: TrustLevel) -> TrustLevel:
    """Return the stronger (more trusted) of two trust levels."""
    order = {
        TrustLevel.PROOF_BACKED: 5,
        TrustLevel.TRUSTED_AUTO: 4,
        TrustLevel.TRACE_BACKED: 3,
        TrustLevel.BOUNDED_AUTO: 2,
        TrustLevel.ASSUMED: 1,
        TrustLevel.RESIDUAL: 0,
    }
    if order.get(a, 0) >= order.get(b, 0):
        return a
    return b


# ---------------------------------------------------------------------------
# Adjacency and reachability helpers
# ---------------------------------------------------------------------------

def _build_adjacency(cover: Cover) -> Dict[SiteId, Set[SiteId]]:
    """Build a directed adjacency map from morphisms."""
    adj: Dict[SiteId, Set[SiteId]] = defaultdict(set)
    for m in cover.morphisms:
        adj[m.source].add(m.target)
    return adj


def _reachable_from(
    start: SiteId, adj: Dict[SiteId, Set[SiteId]]
) -> Set[SiteId]:
    """BFS reachability from start."""
    visited: Set[SiteId] = set()
    queue: deque[SiteId] = deque([start])
    while queue:
        current = queue.popleft()
        if current in visited:
            continue
        visited.add(current)
        for nb in adj.get(current, set()):
            if nb not in visited:
                queue.append(nb)
    return visited


def _reverse_adjacency(adj: Dict[SiteId, Set[SiteId]]) -> Dict[SiteId, Set[SiteId]]:
    """Reverse the adjacency map."""
    rev: Dict[SiteId, Set[SiteId]] = defaultdict(set)
    for src, targets in adj.items():
        for tgt in targets:
            rev[tgt].add(src)
    return rev


# ---------------------------------------------------------------------------
# Overlap compatibility checker
# ---------------------------------------------------------------------------

def _check_overlap_compatible(
    sections: Dict[SiteId, LocalSection],
    overlaps: List[Tuple[SiteId, SiteId]],
) -> List[Tuple[SiteId, SiteId]]:
    """Return overlapping pairs where sections are incompatible."""
    conflicts: List[Tuple[SiteId, SiteId]] = []
    for a_id, b_id in overlaps:
        sec_a = sections.get(a_id)
        sec_b = sections.get(b_id)
        if sec_a is None or sec_b is None:
            continue
        if not _sections_compatible(sec_a, sec_b):
            conflicts.append((a_id, b_id))
    return conflicts


def _sections_compatible(a: LocalSection, b: LocalSection) -> bool:
    """Check whether two sections are compatible on their common refinements."""
    common_keys = set(a.refinements.keys()) & set(b.refinements.keys())
    for k in common_keys:
        if a.refinements[k] != b.refinements[k]:
            return False
    if a.carrier_type is not None and b.carrier_type is not None:
        if isinstance(a.carrier_type, NeverType) or isinstance(b.carrier_type, NeverType):
            return False
    return True


# ---------------------------------------------------------------------------
# Refinement relaxation strategies
# ---------------------------------------------------------------------------

def _relax_section(section: LocalSection, amount: float = 0.5) -> LocalSection:
    """Produce a relaxed version of a section by dropping some refinements.

    The *amount* parameter (0..1) controls how aggressively to relax.
    At amount=0 we keep everything; at amount=1 we drop everything.
    """
    refs = dict(section.refinements)
    n_drop = max(0, int(len(refs) * amount))
    keys = sorted(refs.keys())
    for k in keys[:n_drop]:
        del refs[k]
    return LocalSection(
        site_id=section.site_id,
        carrier_type=section.carrier_type,
        refinements=refs,
        trust=section.trust,
        provenance=f"relaxed({section.provenance})",
    )


def _strengthen_section(
    section: LocalSection, source: LocalSection
) -> LocalSection:
    """Strengthen a section with refinements from *source*."""
    merged = dict(section.refinements)
    merged.update(source.refinements)
    carrier = section.carrier_type
    if carrier is None or isinstance(carrier, AnyType):
        carrier = source.carrier_type
    elif source.carrier_type is not None and not isinstance(
        source.carrier_type, AnyType
    ):
        carrier = type_meet(carrier, source.carrier_type)
    return LocalSection(
        site_id=section.site_id,
        carrier_type=carrier,
        refinements=merged,
        trust=_stronger_trust(section.trust, source.trust),
        provenance=f"strengthened({section.provenance})",
    )


# ---------------------------------------------------------------------------
# Input frontier search
# ---------------------------------------------------------------------------

def _compute_input_cost(
    input_sections: Dict[SiteId, LocalSection],
) -> float:
    """Sum the cost of all input-boundary sections."""
    total = 0.0
    for sid, sec in input_sections.items():
        total += float(len(sec.refinements)) * 1.0
        if sec.carrier_type is not None and not isinstance(
            sec.carrier_type, AnyType
        ):
            total += 0.5
    return total


def _compute_output_info(
    output_sections: Dict[SiteId, LocalSection],
) -> float:
    """Sum the information content of all output-boundary sections."""
    total = 0.0
    for sid, sec in output_sections.items():
        total += float(len(sec.refinements))
        if sec.carrier_type is not None and not isinstance(
            sec.carrier_type, AnyType
        ):
            total += 1.0
    return total


def _compute_proof_debt(
    sections: Dict[SiteId, LocalSection],
) -> int:
    """Count sections with residual or assumed trust."""
    debt = 0
    for sec in sections.values():
        if sec.trust in (TrustLevel.RESIDUAL, TrustLevel.ASSUMED):
            debt += 1
    return debt


def _propagate_forward(
    cover: Cover,
    sections: Dict[SiteId, LocalSection],
) -> Dict[SiteId, LocalSection]:
    """Propagate sections forward along morphisms.

    For each morphism src->tgt, if src has a section but tgt does not,
    restrict the src section to produce a tgt section.
    """
    result = dict(sections)
    changed = True
    iterations = 0
    max_iterations = len(cover.sites) * 2 + 10
    while changed and iterations < max_iterations:
        changed = False
        iterations += 1
        for m in cover.morphisms:
            if m.source in result and m.target not in result:
                try:
                    restricted = m.restrict(result[m.source])
                    result[m.target] = restricted
                    changed = True
                except (ValueError, KeyError):
                    pass
    return result


def _propagate_backward(
    cover: Cover,
    sections: Dict[SiteId, LocalSection],
) -> Dict[SiteId, LocalSection]:
    """Backward propagation: from output boundary toward input boundary.

    For each morphism src->tgt where tgt has a section but src does not,
    we create a lifted section at src with the same refinements.
    """
    result = dict(sections)
    rev_adj = _reverse_adjacency(_build_adjacency(cover))
    changed = True
    iterations = 0
    max_iterations = len(cover.sites) * 2 + 10
    while changed and iterations < max_iterations:
        changed = False
        iterations += 1
        for tgt_id, src_ids in rev_adj.items():
            if tgt_id not in result:
                continue
            tgt_sec = result[tgt_id]
            for src_id in src_ids:
                if src_id not in result:
                    lifted = LocalSection(
                        site_id=src_id,
                        carrier_type=tgt_sec.carrier_type,
                        refinements=dict(tgt_sec.refinements),
                        trust=TrustLevel.BOUNDED_AUTO,
                        provenance=f"lifted_from({tgt_id})",
                    )
                    result[src_id] = lifted
                    changed = True
    return result


# ---------------------------------------------------------------------------
# FrontierSearch
# ---------------------------------------------------------------------------

class FrontierSearch:
    """Search for Pareto-optimal input/output refinement frontiers.

    The frontier search implements the bidirectional refinement problem from
    Part V: given a cover C and sections {sigma_i}, find the Pareto front
    of (input cost, output information, residual errors, proof debt).

    The algorithm operates in three phases:
    1. Forward propagation from input boundary through interior sites.
    2. Backward propagation from output boundary to find required inputs.
    3. Pareto filtering to identify the non-dominated frontier points.
    """

    def __init__(
        self,
        *,
        max_iterations: int = 100,
        relaxation_steps: int = 5,
        convergence_threshold: float = 1e-6,
    ) -> None:
        self._max_iterations = max_iterations
        self._relaxation_steps = relaxation_steps
        self._convergence_threshold = convergence_threshold
        self._lattices: Dict[SiteId, _SectionLattice] = {}

    def _get_lattice(self, site_id: SiteId) -> _SectionLattice:
        """Get or create the section lattice for a site."""
        if site_id not in self._lattices:
            self._lattices[site_id] = _SectionLattice(_site_id=site_id)
        return self._lattices[site_id]

    # -- Main search entry points ------------------------------------------

    def search_input_frontier(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Dict[SiteId, LocalSection]:
        """Find the least-restrictive input sections that prevent all errors.

        Starting from the given sections, iteratively relax input-boundary
        sections while checking that no new overlaps become conflicting.
        Returns the relaxed input sections.
        """
        if not cover.input_boundary:
            return {}

        input_secs: Dict[SiteId, LocalSection] = {}
        for sid in cover.input_boundary:
            if sid in sections:
                input_secs[sid] = sections[sid]
            else:
                input_secs[sid] = self._get_lattice(sid).bottom()

        best_input = dict(input_secs)
        best_cost = _compute_input_cost(best_input)

        for step in range(self._relaxation_steps):
            relaxation_amount = (step + 1) / (self._relaxation_steps + 1)
            candidate_input: Dict[SiteId, LocalSection] = {}
            for sid, sec in best_input.items():
                candidate_input[sid] = _relax_section(sec, relaxation_amount)

            all_sections = dict(sections)
            all_sections.update(candidate_input)
            propagated = _propagate_forward(cover, all_sections)

            conflicts = _check_overlap_compatible(
                propagated, cover.overlaps
            )

            if not conflicts:
                candidate_cost = _compute_input_cost(candidate_input)
                if candidate_cost < best_cost:
                    best_input = candidate_input
                    best_cost = candidate_cost

        return best_input

    def search_output_frontier(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Dict[SiteId, LocalSection]:
        """Find the most-informative output sections.

        Starting from the given sections, strengthen output-boundary sections
        by propagating interior section information forward.
        Returns the strengthened output sections.
        """
        if not cover.output_boundary:
            return {}

        all_propagated = _propagate_forward(cover, sections)

        output_secs: Dict[SiteId, LocalSection] = {}
        for sid in cover.output_boundary:
            if sid in all_propagated:
                output_secs[sid] = all_propagated[sid]
            elif sid in sections:
                output_secs[sid] = sections[sid]
            else:
                output_secs[sid] = self._get_lattice(sid).bottom()

        adj = _build_adjacency(cover)
        rev = _reverse_adjacency(adj)

        for sid in cover.output_boundary:
            predecessors = rev.get(sid, set())
            for pred_id in predecessors:
                if pred_id in all_propagated and sid in output_secs:
                    pred_sec = all_propagated[pred_id]
                    output_secs[sid] = _strengthen_section(
                        output_secs[sid], pred_sec
                    )

        return output_secs

    def search_full_frontier(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
        obstructions: Optional[List[ObstructionData]] = None,
    ) -> FrontierSummary:
        """Compute the full Pareto frontier.

        Combines input frontier search, output frontier search, and
        obstruction analysis into a FrontierSummary.
        """
        if obstructions is None:
            obstructions = []

        candidates: List[_FrontierCandidate] = []

        for step in range(self._relaxation_steps + 1):
            relaxation = step / max(self._relaxation_steps, 1)

            input_secs: Dict[SiteId, LocalSection] = {}
            for sid in cover.input_boundary:
                if sid in sections:
                    input_secs[sid] = _relax_section(
                        sections[sid], relaxation
                    )
                else:
                    input_secs[sid] = self._get_lattice(sid).bottom()

            all_secs = dict(sections)
            all_secs.update(input_secs)
            propagated = _propagate_forward(cover, all_secs)

            conflicts = _check_overlap_compatible(
                propagated, cover.overlaps
            )
            error_sites = frozenset(
                s for pair in conflicts for s in pair
            ) | frozenset(cover.error_sites)

            output_secs = self.search_output_frontier(cover, propagated)

            candidate = _FrontierCandidate(
                _input_sections=input_secs,
                _output_sections=output_secs,
                _residual_errors=error_sites,
                _input_cost=_compute_input_cost(input_secs),
                _output_info=_compute_output_info(output_secs),
                _proof_debt=_compute_proof_debt(propagated),
            )
            candidates.append(candidate)

        pareto = self._pareto_optimal(candidates)

        frontier_points: List[FrontierPoint] = []
        for c in pareto:
            input_boundary = BoundarySection(
                boundary_sites=c.input_sections, is_input=True
            )
            output_boundary = BoundarySection(
                boundary_sites=c.output_sections, is_input=False
            )
            global_sec = GlobalSection(
                local_sections={**c.input_sections, **c.output_sections},
                input_section=input_boundary,
                output_section=output_boundary,
            )
            fp = FrontierPoint(
                input_section=input_boundary,
                output_section=output_boundary,
                global_section=global_sec,
                residual_errors=set(c.residual_errors),
                proof_debt=c.proof_debt,
                information_score=c.output_info,
            )
            frontier_points.append(fp)

        return FrontierSummary(
            points=frontier_points,
            obstructions=list(obstructions),
            repairs=[],
        )

    def _pareto_optimal(
        self,
        candidates: List[_FrontierCandidate],
    ) -> List[_FrontierCandidate]:
        """Filter candidates to the Pareto-optimal subset.

        A candidate is Pareto-optimal if no other candidate dominates it
        on all six objectives simultaneously.
        """
        if not candidates:
            return []

        vectors: List[Tuple[_DominanceVector, _FrontierCandidate]] = []
        for c in candidates:
            all_secs = {**c.input_sections, **c.output_sections}
            total_sites = max(len(all_secs), 1)
            covered = sum(
                1 for s in all_secs.values()
                if len(s.refinements) > 0
            )
            local_coverage = covered / total_sites

            explanation_complexity = 0.0
            for s in all_secs.values():
                explanation_complexity += len(s.refinements) * 0.1
                if s.provenance:
                    explanation_complexity += len(s.provenance) * 0.01

            vec = _DominanceVector(
                _residual_count=len(c.residual_errors),
                _input_cost=c.input_cost,
                _output_info=c.output_info,
                _local_coverage=local_coverage,
                _proof_debt=c.proof_debt,
                _explanation_complexity=explanation_complexity,
            )
            vectors.append((vec, c))

        pareto: List[_FrontierCandidate] = []
        for i, (vi, ci) in enumerate(vectors):
            dominated = False
            for j, (vj, cj) in enumerate(vectors):
                if i != j and vj.dominates(vi):
                    dominated = True
                    break
            if not dominated:
                pareto.append(ci)

        return pareto if pareto else [candidates[0]]

    # -- Utility methods ---------------------------------------------------

    def compute_dominance_vector(
        self,
        input_sections: Dict[SiteId, LocalSection],
        output_sections: Dict[SiteId, LocalSection],
        residual_errors: Set[SiteId],
        proof_debt: int,
    ) -> Tuple[int, float, float, float, int, float]:
        """Compute the six-component objective vector for a given assignment."""
        all_secs = {**input_sections, **output_sections}
        total = max(len(all_secs), 1)
        covered = sum(
            1 for s in all_secs.values() if len(s.refinements) > 0
        )
        local_cov = covered / total

        expl = sum(
            len(s.refinements) * 0.1 + len(s.provenance or "") * 0.01
            for s in all_secs.values()
        )

        return (
            len(residual_errors),
            _compute_input_cost(input_sections),
            _compute_output_info(output_sections),
            local_cov,
            proof_debt,
            expl,
        )

    def monotone_propagate(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
        direction: str = "forward",
    ) -> Dict[SiteId, LocalSection]:
        """Monotone propagation in the specified direction.

        'forward' propagates from input to output boundary.
        'backward' propagates from output to input boundary.
        'both' performs forward then backward.
        """
        if direction == "forward":
            return _propagate_forward(cover, sections)
        elif direction == "backward":
            return _propagate_backward(cover, sections)
        elif direction == "both":
            fwd = _propagate_forward(cover, sections)
            return _propagate_backward(cover, fwd)
        else:
            raise ValueError(f"Unknown direction: {direction!r}")

    def fixpoint_iterate(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Dict[SiteId, LocalSection]:
        """Iterate forward/backward propagation to a fixpoint.

        Returns the sections once no further changes occur or the maximum
        iteration count is reached.
        """
        current = dict(sections)
        for iteration in range(self._max_iterations):
            fwd = _propagate_forward(cover, current)
            bwd = _propagate_backward(cover, fwd)

            changed = False
            for sid in bwd:
                if sid not in current:
                    changed = True
                    break
                old = current[sid]
                new = bwd[sid]
                if (
                    old.carrier_type != new.carrier_type
                    or old.refinements != new.refinements
                ):
                    changed = True
                    break

            current = bwd
            if not changed:
                break

        return current

    def information_gain(
        self,
        old_sections: Dict[SiteId, LocalSection],
        new_sections: Dict[SiteId, LocalSection],
    ) -> float:
        """Compute the total information gain from old to new sections."""
        gain = 0.0
        all_sites = set(old_sections.keys()) | set(new_sections.keys())
        for sid in all_sites:
            old_sec = old_sections.get(sid)
            new_sec = new_sections.get(sid)
            if new_sec is not None and old_sec is None:
                lattice = self._get_lattice(sid)
                gain += lattice.information_content(new_sec)
            elif new_sec is not None and old_sec is not None:
                lattice = self._get_lattice(sid)
                old_info = lattice.information_content(old_sec)
                new_info = lattice.information_content(new_sec)
                gain += max(0.0, new_info - old_info)
        return gain
