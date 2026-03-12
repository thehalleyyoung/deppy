"""Algorithm 3 -- Backward safe-input synthesis.

Starting from error sites, propagate safe-input requirements backward
along restriction maps to the input boundary.  This is the core of the
sheaf-descent type-error anticipation engine: runtime errors become
preconditions on function inputs.

The backward synthesizer performs the following steps:

1. **Error collection**: Identify all error sites and their viability
   predicates from the cover.

2. **Backward propagation**: For each error site, traverse morphisms
   in reverse (pullback direction) to propagate viability requirements
   upstream.  At each step, the viability predicate is pulled back
   through the restriction map.

3. **Phi-merge handling**: When backward propagation reaches a phi/join
   site, the viability requirements from different paths are conjoined
   (because the input must be safe on *all* paths leading to the error).

4. **Input boundary projection**: When propagation reaches the input
   boundary, the accumulated viability predicates become the synthesized
   safe-input requirements (BoundarySection).

5. **Convergence**: The backward pass terminates when all reachable input
   boundary sites have been assigned sections, or when propagation
   reaches a fixed point.
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
# Backward synthesis status
# ---------------------------------------------------------------------------

class BackwardStatus(enum.Enum):
    """Status of a backward synthesis run."""
    CONVERGED = "converged"
    MAX_ITERATIONS = "max_iterations"
    NO_ERROR_SITES = "no_error_sites"
    NO_INPUT_BOUNDARY = "no_input_boundary"


# ---------------------------------------------------------------------------
# Backward synthesis result
# ---------------------------------------------------------------------------

@dataclass
class BackwardSynthesisResult:
    """Result of backward safe-input synthesis."""
    input_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    boundary_section: Optional[BoundarySection] = None
    intermediate_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    status: BackwardStatus = BackwardStatus.CONVERGED
    iterations: int = 0
    error_sites_processed: Set[SiteId] = field(default_factory=set)
    viability_map: Dict[SiteId, Any] = field(default_factory=dict)

    @property
    def num_input_sections(self) -> int:
        return len(self.input_sections)

    def all_sections(self) -> Dict[SiteId, LocalSection]:
        """Return all computed sections (input + intermediate)."""
        result = dict(self.intermediate_sections)
        result.update(self.input_sections)
        return result

    def __repr__(self) -> str:
        return (
            f"BackwardSynthesisResult(status={self.status.value}, "
            f"inputs={self.num_input_sections}, "
            f"iterations={self.iterations}, "
            f"errors_processed={len(self.error_sites_processed)})"
        )


# ---------------------------------------------------------------------------
# Viability precondition
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ViabilityPrecondition:
    """A precondition derived from backward propagation of an error site."""
    _error_site: SiteId
    _predicate: Any
    _path: Tuple[SiteId, ...]
    _trust: TrustLevel = TrustLevel.BOUNDED_AUTO

    @property
    def error_site(self) -> SiteId:
        return self._error_site

    @property
    def predicate(self) -> Any:
        return self._predicate

    @property
    def path(self) -> Tuple[SiteId, ...]:
        return self._path

    @property
    def trust(self) -> TrustLevel:
        return self._trust

    def __repr__(self) -> str:
        return (
            f"ViabilityPrecondition(error={self._error_site}, "
            f"path_len={len(self._path)})"
        )


# ---------------------------------------------------------------------------
# Backward synthesizer
# ---------------------------------------------------------------------------

class BackwardSynthesizer:
    """Algorithm 3: Backward safe-input synthesis.

    Start from error sites, propagate safe-input requirements backward
    along restriction maps to the input boundary.  The synthesized
    boundary section encodes the preconditions that prevent runtime errors.
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
        solved_sections: Dict[SiteId, LocalSection],
    ) -> BackwardSynthesisResult:
        """Run backward synthesis from error sites to input boundary.

        Args:
            cover: The observation cover.
            solved_sections: Sections from the local solver dispatch.

        Returns:
            BackwardSynthesisResult with synthesized input boundary sections.
        """
        result = BackwardSynthesisResult()

        if not cover.error_sites:
            result.status = BackwardStatus.NO_ERROR_SITES
            return result

        if not cover.input_boundary:
            result.status = BackwardStatus.NO_INPUT_BOUNDARY
            return result

        # Build reverse adjacency: target -> list of (source, morphism) pairs
        reverse_adj = self._build_reverse_adjacency(cover)

        # Build forward adjacency for path finding
        forward_adj = self._build_forward_adjacency(cover)

        # Initialize backward propagation from error sites
        worklist: deque[Tuple[SiteId, LocalSection, Tuple[SiteId, ...]]] = deque()
        backward_sections: Dict[SiteId, LocalSection] = dict(solved_sections)

        for error_site in cover.error_sites:
            result.error_sites_processed.add(error_site)

            # Get or create the error site's section
            error_section = solved_sections.get(error_site)
            if error_section is None:
                error_section = LocalSection(
                    site_id=error_site,
                    trust=TrustLevel.RESIDUAL,
                    provenance="backward_synth: error site seed",
                )

            # Generate viability preconditions
            viability = self._propagate_viability(
                error_site, error_section, cover
            )
            result.viability_map[error_site] = viability

            # Add to backward section map and worklist
            backward_sections[error_site] = error_section
            worklist.append((error_site, error_section, (error_site,)))

        # Iterative backward propagation
        iteration = 0
        visited: Set[SiteId] = set(cover.error_sites)

        while worklist and iteration < self._max_iterations:
            iteration += 1
            current_site, current_section, path = worklist.popleft()

            # Check if we've reached the input boundary
            if current_site in cover.input_boundary:
                result.input_sections[current_site] = current_section
                continue

            # Propagate backward along all incoming morphisms
            incoming = reverse_adj.get(current_site, [])

            for source_site, morphism in incoming:
                if source_site in visited and source_site not in cover.input_boundary:
                    # Already processed (avoid cycles), but allow revisiting
                    # input boundary sites to accumulate requirements
                    existing = backward_sections.get(source_site)
                    if existing is not None:
                        # Merge the new pullback with the existing section
                        pulled = self._pullback_along_morphism(
                            current_section, morphism
                        )
                        merged = self._merge_at_phi(
                            [existing, pulled], source_site
                        )
                        if merged.refinements != existing.refinements:
                            backward_sections[source_site] = merged
                            worklist.append(
                                (source_site, merged, path + (source_site,))
                            )
                    continue

                visited.add(source_site)

                # Pull back the current section along the morphism
                pulled = self._pullback_along_morphism(
                    current_section, morphism
                )
                backward_sections[source_site] = pulled
                result.intermediate_sections[source_site] = pulled

                new_path = path + (source_site,)
                worklist.append((source_site, pulled, new_path))

        # Determine convergence status
        if iteration >= self._max_iterations:
            result.status = BackwardStatus.MAX_ITERATIONS
        else:
            result.status = BackwardStatus.CONVERGED

        result.iterations = iteration
        result.intermediate_sections = {
            sid: sec for sid, sec in backward_sections.items()
            if sid not in cover.input_boundary and sid not in cover.error_sites
        }

        # Build boundary section
        if result.input_sections:
            result.boundary_section = BoundarySection(
                boundary_sites=dict(result.input_sections),
                is_input=True,
            )

        return result

    # -- Viability propagation ---------------------------------------------

    def _propagate_viability(
        self,
        error_site: SiteId,
        error_section: LocalSection,
        cover: Cover,
    ) -> List[ViabilityPrecondition]:
        """Extract viability preconditions from an error site.

        The viability predicate expresses: "if these conditions hold at the
        input, this error site will not be reached / will not fault."
        """
        preconditions: List[ViabilityPrecondition] = []

        # Extract viability predicates from refinements
        for key, value in error_section.refinements.items():
            if "viability" in key or "error" in key or "guard" in key:
                preconditions.append(ViabilityPrecondition(
                    _error_site=error_site,
                    _predicate=value,
                    _path=(error_site,),
                    _trust=error_section.trust,
                ))

        # If no explicit viability, generate a generic one from the error site
        if not preconditions:
            preconditions.append(ViabilityPrecondition(
                _error_site=error_site,
                _predicate=("error_unreachable", error_site),
                _path=(error_site,),
                _trust=TrustLevel.RESIDUAL,
            ))

        return preconditions

    # -- Pullback along morphism -------------------------------------------

    def _pullback_along_morphism(
        self,
        section: LocalSection,
        morphism: ConcreteMorphism,
    ) -> LocalSection:
        """Pull a section backward along a morphism.

        This is the adjoint of restriction: given a section at the
        morphism's target, produce a section at the source that is
        consistent with the target section.
        """
        return self._propagator.propagate_backward(section, morphism)

    # -- Phi-merge at join points ------------------------------------------

    def _merge_at_phi(
        self,
        sections: Sequence[LocalSection],
        phi_site: SiteId,
    ) -> LocalSection:
        """Merge sections at a phi/join point during backward propagation.

        In backward synthesis, merging at a phi-node means *conjoining*
        the viability requirements from different paths (because all paths
        must be safe).
        """
        if not sections:
            return LocalSection(
                site_id=phi_site,
                trust=TrustLevel.ASSUMED,
                provenance="backward_merge: no predecessors",
            )

        if len(sections) == 1:
            sec = sections[0]
            return LocalSection(
                site_id=phi_site,
                carrier_type=sec.carrier_type,
                refinements=dict(sec.refinements),
                trust=sec.trust,
                provenance=f"backward_merge: single path from {sec.site_id}",
                witnesses=dict(sec.witnesses),
            )

        # For backward synthesis, we conjoin refinements (must satisfy all)
        merged_refinements: Dict[str, Any] = {}
        for sec in sections:
            for key, value in sec.refinements.items():
                if key in merged_refinements:
                    existing = merged_refinements[key]
                    if existing != value:
                        # Conjoin: both must hold for safety
                        merged_refinements[key] = ("conjunction", existing, value)
                else:
                    merged_refinements[key] = value

        # Trust is the meet of all incoming trusts
        merged_trust = sections[0].trust
        for sec in sections[1:]:
            merged_trust = trust_meet(merged_trust, sec.trust)

        # Carrier type: use the first non-None carrier
        carrier = None
        for sec in sections:
            if sec.carrier_type is not None:
                carrier = sec.carrier_type
                break

        pred_names = ", ".join(str(s.site_id) for s in sections)
        return LocalSection(
            site_id=phi_site,
            carrier_type=carrier,
            refinements=merged_refinements,
            trust=merged_trust,
            provenance=f"backward_merge: [{pred_names}]",
        )

    # -- Input boundary reaching -------------------------------------------

    def _reach_input_boundary(
        self,
        cover: Cover,
        backward_sections: Dict[SiteId, LocalSection],
    ) -> Dict[SiteId, LocalSection]:
        """Extract the sections at input boundary sites.

        These are the synthesized safe-input requirements.
        """
        input_sections: Dict[SiteId, LocalSection] = {}
        for site_id in cover.input_boundary:
            sec = backward_sections.get(site_id)
            if sec is not None:
                input_sections[site_id] = sec
        return input_sections

    # -- Adjacency builders ------------------------------------------------

    def _build_reverse_adjacency(
        self,
        cover: Cover,
    ) -> Dict[SiteId, List[Tuple[SiteId, ConcreteMorphism]]]:
        """Build reverse adjacency: target -> [(source, morphism)]."""
        reverse: Dict[SiteId, List[Tuple[SiteId, ConcreteMorphism]]] = {}
        for morphism in cover.morphisms:
            reverse.setdefault(morphism.target, []).append(
                (morphism.source, morphism)
            )
        return reverse

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

    # -- Batch backward from multiple error sites --------------------------

    def synthesize_from_errors(
        self,
        cover: Cover,
        solved_sections: Dict[SiteId, LocalSection],
        error_subset: Optional[Set[SiteId]] = None,
    ) -> BackwardSynthesisResult:
        """Run backward synthesis from a specific subset of error sites.

        This is useful when only certain error sites need attention (e.g.,
        after incremental changes).
        """
        if error_subset is not None:
            # Create a modified cover with only the specified error sites
            modified_cover = Cover(
                sites=cover.sites,
                morphisms=cover.morphisms,
                overlaps=cover.overlaps,
                error_sites=error_subset & cover.error_sites,
                input_boundary=cover.input_boundary,
                output_boundary=cover.output_boundary,
            )
            return self.synthesize(modified_cover, solved_sections)
        return self.synthesize(cover, solved_sections)

    # -- Incremental backward synthesis ------------------------------------

    def synthesize_incremental(
        self,
        cover: Cover,
        solved_sections: Dict[SiteId, LocalSection],
        previous_result: BackwardSynthesisResult,
        changed_error_sites: Set[SiteId],
    ) -> BackwardSynthesisResult:
        """Incrementally update backward synthesis after changes.

        Only re-propagates from error sites that have changed, reusing
        previously computed intermediate sections where possible.
        """
        # Merge previous intermediate sections with current solved sections
        combined = dict(solved_sections)
        for sid, sec in previous_result.intermediate_sections.items():
            if sid not in combined and sid not in changed_error_sites:
                combined[sid] = sec

        return self.synthesize_from_errors(
            cover, combined, changed_error_sites
        )
