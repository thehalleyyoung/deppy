"""Algorithm 4 -- Forward output synthesis.

Starting from input boundary seeds, propagate sections forward along
restriction maps to the output boundary.  This completes the bidirectional
refinement problem: backward synthesis determines *what* the inputs need
to be, and forward synthesis determines *what* the outputs will be.

The forward synthesizer performs:

1. **Seed initialization**: Start with sections at input boundary sites.
   These may come from user annotations, backward synthesis, or the
   local solver.

2. **Forward propagation**: For each input boundary site, follow morphisms
   in the forward direction (push-forward), applying restriction maps to
   transport section data downstream.

3. **Phi-merge handling**: When forward propagation reaches a join site,
   sections from different branches are merged using the phi-merger
   (join in the information lattice).

4. **Output boundary collection**: When propagation reaches output boundary
   sites, the accumulated sections become the synthesized output type.

5. **Convergence**: Forward synthesis terminates when all reachable output
   boundary sites have sections, or when propagation reaches a fixed point.
"""

from __future__ import annotations

import enum
from collections import deque
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
    BoundarySection,
    Cover,
    LocalSection,
    Morphism,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism
from deppy.static_analysis.restriction_maps import (
    RestrictionData,
    RestrictionKind,
    apply_restriction,
)
from deppy.kernel.trust_classifier import (
    TrustClassifier,
    trust_meet,
    trust_rank,
    _extract_restriction_data,
)
from deppy.kernel.section_propagator import SectionPropagator
from deppy.kernel.phi_merge import PhiMerger


# ---------------------------------------------------------------------------
# Forward synthesis status
# ---------------------------------------------------------------------------

class ForwardStatus(enum.Enum):
    """Status of a forward synthesis run."""
    CONVERGED = "converged"
    MAX_ITERATIONS = "max_iterations"
    NO_INPUT_SEEDS = "no_input_seeds"
    NO_OUTPUT_BOUNDARY = "no_output_boundary"
    PARTIAL = "partial"


# ---------------------------------------------------------------------------
# Forward synthesis result
# ---------------------------------------------------------------------------

@dataclass
class ForwardSynthesisResult:
    """Result of forward output synthesis."""
    output_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    boundary_section: Optional[BoundarySection] = None
    intermediate_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    status: ForwardStatus = ForwardStatus.CONVERGED
    iterations: int = 0
    sites_reached: Set[SiteId] = field(default_factory=set)
    unreachable_outputs: Set[SiteId] = field(default_factory=set)

    @property
    def num_output_sections(self) -> int:
        return len(self.output_sections)

    def all_sections(self) -> Dict[SiteId, LocalSection]:
        """Return all computed sections (output + intermediate)."""
        result = dict(self.intermediate_sections)
        result.update(self.output_sections)
        return result

    def __repr__(self) -> str:
        return (
            f"ForwardSynthesisResult(status={self.status.value}, "
            f"outputs={self.num_output_sections}, "
            f"iterations={self.iterations}, "
            f"reached={len(self.sites_reached)})"
        )


# ---------------------------------------------------------------------------
# Forward synthesizer
# ---------------------------------------------------------------------------

class ForwardSynthesizer:
    """Algorithm 4: Forward output synthesis.

    Start from input boundary seeds, propagate forward along restriction
    maps to the output boundary.  The synthesized boundary section
    encodes the output type guarantees.
    """

    def __init__(
        self,
        *,
        max_iterations: int = 100,
        propagator: Optional[SectionPropagator] = None,
        phi_merger: Optional[PhiMerger] = None,
        trust_classifier: Optional[TrustClassifier] = None,
    ) -> None:
        self._max_iterations = max_iterations
        self._propagator = propagator or SectionPropagator()
        self._phi_merger = phi_merger or PhiMerger()
        self._trust_classifier = trust_classifier or TrustClassifier()

    # -- Main entry point --------------------------------------------------

    def synthesize(
        self,
        cover: Cover,
        input_sections: Dict[SiteId, LocalSection],
    ) -> ForwardSynthesisResult:
        """Run forward synthesis from input boundary to output boundary.

        Args:
            cover: The observation cover.
            input_sections: Sections at input boundary sites (seeds).

        Returns:
            ForwardSynthesisResult with synthesized output boundary sections.
        """
        result = ForwardSynthesisResult()

        # Validate inputs
        if not input_sections:
            result.status = ForwardStatus.NO_INPUT_SEEDS
            return result

        if not cover.output_boundary:
            result.status = ForwardStatus.NO_OUTPUT_BOUNDARY
            return result

        # Build forward adjacency: source -> [(target, morphism)]
        forward_adj = self._build_forward_adjacency(cover)

        # Build phi-site detection: sites with multiple incoming morphisms
        incoming_count = self._compute_incoming_counts(cover)

        # Initialize worklist with input boundary seeds
        worklist: deque[Tuple[SiteId, LocalSection]] = deque()
        forward_sections: Dict[SiteId, LocalSection] = dict(input_sections)

        for site_id, section in input_sections.items():
            worklist.append((site_id, section))
            result.sites_reached.add(site_id)

        # Pending merge tracker: for phi sites, accumulate incoming sections
        # before merging and propagating further
        pending_merge: Dict[SiteId, List[LocalSection]] = {}

        # Iterative forward propagation
        iteration = 0

        while worklist and iteration < self._max_iterations:
            iteration += 1
            current_site, current_section = worklist.popleft()

            # Check if we've reached the output boundary
            if current_site in cover.output_boundary:
                result.output_sections[current_site] = current_section
                # Don't stop: the section might also propagate further

            # Propagate forward along all outgoing morphisms
            outgoing = forward_adj.get(current_site, [])

            for target_site, morphism in outgoing:
                # Push the section forward
                pushed = self._push_forward(current_section, morphism)

                # Check if the target is a phi/join site
                in_count = incoming_count.get(target_site, 0)
                if in_count > 1:
                    # Phi site: accumulate sections before merging
                    pending_merge.setdefault(target_site, []).append(pushed)

                    if len(pending_merge[target_site]) >= in_count:
                        # All predecessors arrived: merge and propagate
                        merged = self._join_at_merge(
                            pending_merge[target_site], target_site
                        )
                        forward_sections[target_site] = merged
                        result.sites_reached.add(target_site)
                        worklist.append((target_site, merged))
                        del pending_merge[target_site]
                    elif target_site not in forward_sections:
                        # Not all predecessors yet; store partial
                        forward_sections[target_site] = pushed
                else:
                    # Single incoming: propagate immediately
                    existing = forward_sections.get(target_site)
                    if existing is not None:
                        # Merge with existing (e.g., from a different worklist entry)
                        merged = self._join_at_merge(
                            [existing, pushed], target_site
                        )
                        if merged.refinements != existing.refinements:
                            forward_sections[target_site] = merged
                            result.sites_reached.add(target_site)
                            worklist.append((target_site, merged))
                    else:
                        forward_sections[target_site] = pushed
                        result.sites_reached.add(target_site)
                        worklist.append((target_site, pushed))

        # Handle pending merges that never got all predecessors
        for site_id, pending_secs in pending_merge.items():
            if pending_secs:
                merged = self._join_at_merge(pending_secs, site_id)
                forward_sections[site_id] = merged
                result.sites_reached.add(site_id)
                if site_id in cover.output_boundary:
                    result.output_sections[site_id] = merged

        # Determine convergence status
        if iteration >= self._max_iterations:
            result.status = ForwardStatus.MAX_ITERATIONS
        else:
            result.status = ForwardStatus.CONVERGED

        # Check for unreachable output sites
        for out_site in cover.output_boundary:
            if out_site not in result.output_sections:
                result.unreachable_outputs.add(out_site)

        if result.unreachable_outputs and result.output_sections:
            result.status = ForwardStatus.PARTIAL

        result.iterations = iteration
        result.intermediate_sections = {
            sid: sec for sid, sec in forward_sections.items()
            if sid not in cover.output_boundary and sid not in input_sections
        }

        # Build boundary section
        if result.output_sections:
            result.boundary_section = BoundarySection(
                boundary_sites=dict(result.output_sections),
                is_input=False,
            )

        return result

    # -- Push-forward along morphism ---------------------------------------

    def _push_forward(
        self,
        section: LocalSection,
        morphism: ConcreteMorphism,
    ) -> LocalSection:
        """Push a section forward along a morphism.

        This is the standard presheaf restriction: apply the morphism's
        restriction map to transport section data from source to target.
        """
        return self._propagator.propagate_forward(section, morphism)

    # -- Join at merge point -----------------------------------------------

    def _join_at_merge(
        self,
        sections: Sequence[LocalSection],
        merge_site: SiteId,
    ) -> LocalSection:
        """Merge sections at a join point during forward propagation.

        In forward synthesis, merging at a phi-node uses the information
        lattice join: the result carries only the information that is
        *common* to all predecessors.
        """
        return self._phi_merger.merge(sections, merge_site)

    # -- Output boundary reaching ------------------------------------------

    def _reach_output_boundary(
        self,
        cover: Cover,
        forward_sections: Dict[SiteId, LocalSection],
    ) -> Dict[SiteId, LocalSection]:
        """Extract the sections at output boundary sites."""
        output_sections: Dict[SiteId, LocalSection] = {}
        for site_id in cover.output_boundary:
            sec = forward_sections.get(site_id)
            if sec is not None:
                output_sections[site_id] = sec
        return output_sections

    # -- Adjacency builder -------------------------------------------------

    def _build_forward_adjacency(
        self,
        cover: Cover,
    ) -> Dict[SiteId, List[Tuple[SiteId, ConcreteMorphism]]]:
        """Build forward adjacency: source -> [(target, morphism)]."""
        forward: Dict[SiteId, List[Tuple[SiteId, ConcreteMorphism]]] = {}
        for morphism in cover.morphisms:
            forward.setdefault(morphism.source, []).append(
                (morphism.target, morphism)
            )
        return forward

    def _compute_incoming_counts(
        self,
        cover: Cover,
    ) -> Dict[SiteId, int]:
        """Compute the number of incoming morphisms for each site."""
        counts: Dict[SiteId, int] = {}
        for morphism in cover.morphisms:
            counts[morphism.target] = counts.get(morphism.target, 0) + 1
        return counts

    # -- Incremental forward synthesis -------------------------------------

    def synthesize_incremental(
        self,
        cover: Cover,
        input_sections: Dict[SiteId, LocalSection],
        previous_result: ForwardSynthesisResult,
        changed_inputs: Set[SiteId],
    ) -> ForwardSynthesisResult:
        """Incrementally update forward synthesis after input changes.

        Only re-propagates from input sites that have changed, reusing
        previously computed intermediate sections for unchanged paths.
        """
        # Merge previous intermediate sections with changed inputs
        combined = dict(input_sections)
        for sid, sec in previous_result.intermediate_sections.items():
            if sid not in combined:
                # Check if this site is downstream of a changed input
                if not self._is_downstream_of(sid, changed_inputs, cover):
                    combined[sid] = sec

        return self.synthesize(cover, combined)

    def _is_downstream_of(
        self,
        site_id: SiteId,
        sources: Set[SiteId],
        cover: Cover,
    ) -> bool:
        """Check if a site is reachable from any of the given sources."""
        visited: Set[SiteId] = set()
        queue: deque[SiteId] = deque(sources)

        while queue:
            current = queue.popleft()
            if current == site_id:
                return True
            if current in visited:
                continue
            visited.add(current)
            for m in cover.morphisms:
                if m.source == current:
                    queue.append(m.target)

        return False

    # -- Batch forward from specific input sites ---------------------------

    def synthesize_from_inputs(
        self,
        cover: Cover,
        input_sections: Dict[SiteId, LocalSection],
        input_subset: Optional[Set[SiteId]] = None,
    ) -> ForwardSynthesisResult:
        """Run forward synthesis from a specific subset of input sites.

        Useful for incremental analysis when only certain inputs have changed.
        """
        if input_subset is not None:
            filtered = {
                sid: sec for sid, sec in input_sections.items()
                if sid in input_subset
            }
            return self.synthesize(cover, filtered)
        return self.synthesize(cover, input_sections)
