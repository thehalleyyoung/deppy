"""Fixed-point engine -- iterate backward+forward synthesis until stable.

The fixed-point engine orchestrates the complete kernel pipeline:

1. **Local solve** (Algorithm 2): Dispatch theory packs to each site.
2. **Backward synthesis** (Algorithm 3): Propagate error requirements
   to the input boundary.
3. **Forward synthesis** (Algorithm 4): Propagate input seeds to the
   output boundary.
4. **Obstruction extraction** (Algorithm 5): Check gluing conditions
   and extract obstruction basis.
5. **Viability checking**: Verify error-site viability.
6. **Convergence check**: If new sections were produced or existing
   sections refined, repeat from step 1.  Otherwise, return.

The iteration terminates when:
- No new sections are produced in a round.
- No existing sections are refined (refinements stabilize).
- Maximum iteration count is reached.
- All obstructions are resolved (H^1 becomes trivial).
"""

from __future__ import annotations

import enum
import time
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
    BidirectionalResult,
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
from deppy.static_analysis.section_gluing import (
    assemble_global_section,
    GluingCheckResult,
)
from deppy.kernel.local_solver_dispatch import (
    LocalSolverDispatch,
    SolverResult,
)
from deppy.kernel.backward_synthesis import (
    BackwardSynthesizer,
    BackwardSynthesisResult,
)
from deppy.kernel.forward_synthesis import (
    ForwardSynthesizer,
    ForwardSynthesisResult,
)
from deppy.kernel.obstruction_extractor import (
    ObstructionExtractor,
    ExtractionResult,
)
from deppy.kernel.viability_checker import (
    ViabilityChecker,
    ViabilitySummary,
)
from deppy.kernel.trust_classifier import TrustClassifier


# ---------------------------------------------------------------------------
# Fixed-point convergence status
# ---------------------------------------------------------------------------

class ConvergenceStatus(enum.Enum):
    """Status of the fixed-point iteration."""
    CONVERGED = "converged"
    MAX_ITERATIONS = "max_iterations"
    GLOBAL_SECTION_FOUND = "global_section_found"
    OBSTRUCTIONS_REMAIN = "obstructions_remain"
    NO_PROGRESS = "no_progress"
    ERROR = "error"


# ---------------------------------------------------------------------------
# Iteration snapshot
# ---------------------------------------------------------------------------

@dataclass
class IterationSnapshot:
    """Snapshot of state at a single fixed-point iteration."""
    iteration: int = 0
    num_sections: int = 0
    num_new_sections: int = 0
    num_refined_sections: int = 0
    num_obstructions: int = 0
    num_viable_errors: int = 0
    num_total_errors: int = 0
    elapsed_ms: float = 0.0
    phase_timings: Dict[str, float] = field(default_factory=dict)

    @property
    def made_progress(self) -> bool:
        return self.num_new_sections > 0 or self.num_refined_sections > 0

    def __repr__(self) -> str:
        return (
            f"Iteration({self.iteration}: "
            f"sections={self.num_sections}, "
            f"new={self.num_new_sections}, "
            f"refined={self.num_refined_sections}, "
            f"obstructions={self.num_obstructions}, "
            f"elapsed={self.elapsed_ms:.1f}ms)"
        )


# ---------------------------------------------------------------------------
# Fixed-point result
# ---------------------------------------------------------------------------

@dataclass
class FixedPointResult:
    """Result of the fixed-point engine."""
    # Core outputs
    global_section: Optional[GlobalSection] = None
    input_section: Optional[BoundarySection] = None
    output_section: Optional[BoundarySection] = None
    all_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)

    # Obstructions
    obstructions: List[ObstructionData] = field(default_factory=list)
    extraction_result: Optional[ExtractionResult] = None

    # Viability
    viability_summary: Optional[ViabilitySummary] = None
    error_viability: Dict[SiteId, bool] = field(default_factory=dict)

    # Convergence info
    status: ConvergenceStatus = ConvergenceStatus.CONVERGED
    iterations: int = 0
    snapshots: List[IterationSnapshot] = field(default_factory=list)
    total_elapsed_ms: float = 0.0

    # Sub-results
    solver_result: Optional[SolverResult] = None
    backward_result: Optional[BackwardSynthesisResult] = None
    forward_result: Optional[ForwardSynthesisResult] = None

    @property
    def converged(self) -> bool:
        return self.status in (
            ConvergenceStatus.CONVERGED,
            ConvergenceStatus.GLOBAL_SECTION_FOUND,
        )

    @property
    def has_global_section(self) -> bool:
        return self.global_section is not None

    @property
    def num_obstructions(self) -> int:
        return len(self.obstructions)

    def to_bidirectional_result(self) -> BidirectionalResult:
        """Convert to the protocol's BidirectionalResult."""
        return BidirectionalResult(
            input_section=self.input_section or BoundarySection(is_input=True),
            output_section=self.output_section or BoundarySection(is_input=False),
            global_section=self.global_section or GlobalSection(),
            obstructions=list(self.obstructions),
            error_viability=dict(self.error_viability),
            converged=self.converged,
        )

    def __repr__(self) -> str:
        return (
            f"FixedPointResult(status={self.status.value}, "
            f"iterations={self.iterations}, "
            f"sections={len(self.all_sections)}, "
            f"obstructions={self.num_obstructions}, "
            f"elapsed={self.total_elapsed_ms:.1f}ms)"
        )


# ---------------------------------------------------------------------------
# Fixed-point engine
# ---------------------------------------------------------------------------

class FixedPointEngine:
    """Fixed-point engine iterating backward+forward until stable.

    Orchestrates the complete kernel pipeline:
    local_solve -> backward_synth -> forward_synth -> check_obstructions
    -> repeat until convergence.
    """

    def __init__(
        self,
        *,
        max_iterations: int = 20,
        solver: Optional[LocalSolverDispatch] = None,
        backward: Optional[BackwardSynthesizer] = None,
        forward: Optional[ForwardSynthesizer] = None,
        extractor: Optional[ObstructionExtractor] = None,
        viability: Optional[ViabilityChecker] = None,
        trust_classifier: Optional[TrustClassifier] = None,
        convergence_threshold: float = 0.0,
        early_stop_on_global_section: bool = True,
    ) -> None:
        self._max_iterations = max_iterations
        self._trust = trust_classifier or TrustClassifier()
        self._solver = solver or LocalSolverDispatch(trust_classifier=self._trust)
        self._backward = backward or BackwardSynthesizer(trust_classifier=self._trust)
        self._forward = forward or ForwardSynthesizer(trust_classifier=self._trust)
        self._extractor = extractor or ObstructionExtractor()
        self._viability = viability or ViabilityChecker(trust_classifier=self._trust)
        self._convergence_threshold = convergence_threshold
        self._early_stop = early_stop_on_global_section

    # -- Main entry point --------------------------------------------------

    def run(
        self,
        cover: Cover,
        theory_packs: Optional[Sequence[Any]] = None,
        callee_summaries: Optional[Dict[str, "FixedPointResult"]] = None,
    ) -> FixedPointResult:
        """Run the fixed-point engine on a cover.

        Args:
            cover: The observation cover to analyze.
            theory_packs: Optional additional theory packs for the solver.
            callee_summaries: Optional map {callee_name → FixedPointResult}
                for interprocedural section transport (§4.4 of the paper).
                When provided, output sections from each callee are transported
                via actual→formal and return→caller morphisms to the caller's
                CALL_RESULT sites after each forward synthesis phase.

        Returns:
            FixedPointResult with the final state of the analysis.
        """
        result = FixedPointResult()
        overall_start = time.monotonic()

        # Phase 1: Local solve
        t0 = time.monotonic()
        solver_result = self._solver.dispatch(cover, theory_packs)
        result.solver_result = solver_result
        local_solve_ms = (time.monotonic() - t0) * 1000.0

        # Merge solved sections into the working set
        current_sections = dict(solver_result.solved_sections)

        # Main fixed-point loop
        for iteration in range(self._max_iterations):
            iter_start = time.monotonic()
            snapshot = IterationSnapshot(iteration=iteration)

            # Phase 2: Backward synthesis
            t0 = time.monotonic()
            backward_result = self._backward.synthesize(
                cover, current_sections
            )
            result.backward_result = backward_result
            backward_ms = (time.monotonic() - t0) * 1000.0
            snapshot.phase_timings["backward"] = backward_ms

            # Merge backward sections
            new_sections, refined_sections = self._merge_sections(
                current_sections, backward_result.all_sections()
            )
            snapshot.num_new_sections += new_sections
            snapshot.num_refined_sections += refined_sections

            # Phase 3: Forward synthesis
            t0 = time.monotonic()
            # Collect input sections for forward synthesis
            input_seeds = {
                sid: sec for sid, sec in current_sections.items()
                if sid in cover.input_boundary
            }
            forward_result = self._forward.synthesize(cover, input_seeds)
            result.forward_result = forward_result
            forward_ms = (time.monotonic() - t0) * 1000.0
            snapshot.phase_timings["forward"] = forward_ms

            # Merge forward sections
            new_fwd, refined_fwd = self._merge_sections(
                current_sections, forward_result.all_sections()
            )
            snapshot.num_new_sections += new_fwd
            snapshot.num_refined_sections += refined_fwd

            # Phase 3.5: Interprocedural section transport (§4.4)
            # For each CALL_RESULT site in the cover, if we have a callee
            # summary, transport the callee's output sections back to the
            # caller's call-result site via return→caller morphisms.
            #
            # This implements Grothendieck transitivity: the global section
            # assignment must be compatible across function call boundaries.
            if callee_summaries:
                transport_secs = self._run_interprocedural_transport(
                    cover, current_sections, callee_summaries
                )
                if transport_secs:
                    new_t, refined_t = self._merge_sections(
                        current_sections, transport_secs
                    )
                    snapshot.num_new_sections += new_t
                    snapshot.num_refined_sections += refined_t

            # Phase 4: Obstruction extraction
            t0 = time.monotonic()
            extraction = self._extractor.extract(cover, current_sections)
            result.extraction_result = extraction
            result.obstructions = [
                ro.obstruction for ro in extraction.obstructions
            ]
            obstruction_ms = (time.monotonic() - t0) * 1000.0
            snapshot.phase_timings["obstruction"] = obstruction_ms
            snapshot.num_obstructions = len(extraction.obstructions)

            # Phase 5: Viability checking
            t0 = time.monotonic()
            viability_summary = self._viability.check_all(
                cover, current_sections
            )
            result.viability_summary = viability_summary
            viability_ms = (time.monotonic() - t0) * 1000.0
            snapshot.phase_timings["viability"] = viability_ms
            snapshot.num_viable_errors = sum(
                1 for r in viability_summary.results.values() if r.is_viable
            )
            snapshot.num_total_errors = len(cover.error_sites)

            # Update error viability map
            for sid, vr in viability_summary.results.items():
                result.error_viability[sid] = vr.is_viable

            # Record snapshot
            snapshot.num_sections = len(current_sections)
            snapshot.elapsed_ms = (time.monotonic() - iter_start) * 1000.0
            result.snapshots.append(snapshot)

            # Early stop: global section found
            if extraction.is_consistent and self._early_stop:
                global_sec, _ = assemble_global_section(
                    cover, current_sections
                )
                if global_sec is not None:
                    result.global_section = global_sec
                    result.status = ConvergenceStatus.GLOBAL_SECTION_FOUND
                    break

            # Convergence check: no progress
            if not snapshot.made_progress:
                if extraction.is_consistent:
                    result.status = ConvergenceStatus.CONVERGED
                else:
                    result.status = ConvergenceStatus.OBSTRUCTIONS_REMAIN
                break

        else:
            # Max iterations reached
            result.status = ConvergenceStatus.MAX_ITERATIONS

        # Finalize result
        result.all_sections = dict(current_sections)
        result.iterations = len(result.snapshots)
        result.total_elapsed_ms = (time.monotonic() - overall_start) * 1000.0

        # Build boundary sections
        input_secs = {
            sid: sec for sid, sec in current_sections.items()
            if sid in cover.input_boundary
        }
        output_secs = {
            sid: sec for sid, sec in current_sections.items()
            if sid in cover.output_boundary
        }
        if input_secs:
            result.input_section = BoundarySection(
                boundary_sites=input_secs, is_input=True
            )
        if output_secs:
            result.output_section = BoundarySection(
                boundary_sites=output_secs, is_input=False
            )

        # Attempt global section assembly if not yet done
        if result.global_section is None and result.extraction_result is not None:
            if result.extraction_result.is_consistent:
                global_sec, _ = assemble_global_section(
                    cover, current_sections
                )
                result.global_section = global_sec

        return result

    # -- Incremental run ---------------------------------------------------

    def run_incremental(
        self,
        cover: Cover,
        previous_result: FixedPointResult,
        changed_sites: Set[SiteId],
        theory_packs: Optional[Sequence[Any]] = None,
    ) -> FixedPointResult:
        """Re-run the fixed-point engine incrementally.

        Only re-solves changed sites and their downstream dependencies.
        """
        result = FixedPointResult()
        overall_start = time.monotonic()

        # Phase 1: Incremental local solve
        solver_result = self._solver.dispatch_incremental(
            cover,
            previous_result.all_sections,
            changed_sites,
            theory_packs,
        )
        result.solver_result = solver_result

        # Start from previous sections + updated solver results
        current_sections = dict(previous_result.all_sections)
        current_sections.update(solver_result.solved_sections)

        # Run the standard fixed-point loop on the updated sections
        for iteration in range(self._max_iterations):
            iter_start = time.monotonic()
            snapshot = IterationSnapshot(iteration=iteration)

            # Backward synthesis
            backward_result = self._backward.synthesize(cover, current_sections)
            result.backward_result = backward_result
            new_bwd, refined_bwd = self._merge_sections(
                current_sections, backward_result.all_sections()
            )
            snapshot.num_new_sections += new_bwd
            snapshot.num_refined_sections += refined_bwd

            # Forward synthesis
            input_seeds = {
                sid: sec for sid, sec in current_sections.items()
                if sid in cover.input_boundary
            }
            forward_result = self._forward.synthesize(cover, input_seeds)
            result.forward_result = forward_result
            new_fwd, refined_fwd = self._merge_sections(
                current_sections, forward_result.all_sections()
            )
            snapshot.num_new_sections += new_fwd
            snapshot.num_refined_sections += refined_fwd

            # Obstruction extraction
            extraction = self._extractor.extract(cover, current_sections)
            result.extraction_result = extraction
            result.obstructions = [
                ro.obstruction for ro in extraction.obstructions
            ]
            snapshot.num_obstructions = len(extraction.obstructions)

            # Viability checking
            viability_summary = self._viability.check_all(cover, current_sections)
            result.viability_summary = viability_summary
            for sid, vr in viability_summary.results.items():
                result.error_viability[sid] = vr.is_viable

            snapshot.num_sections = len(current_sections)
            snapshot.elapsed_ms = (time.monotonic() - iter_start) * 1000.0
            result.snapshots.append(snapshot)

            # Early stop
            if extraction.is_consistent and self._early_stop:
                global_sec, _ = assemble_global_section(cover, current_sections)
                if global_sec is not None:
                    result.global_section = global_sec
                    result.status = ConvergenceStatus.GLOBAL_SECTION_FOUND
                    break

            if not snapshot.made_progress:
                if extraction.is_consistent:
                    result.status = ConvergenceStatus.CONVERGED
                else:
                    result.status = ConvergenceStatus.OBSTRUCTIONS_REMAIN
                break
        else:
            result.status = ConvergenceStatus.MAX_ITERATIONS

        result.all_sections = dict(current_sections)
        result.iterations = len(result.snapshots)
        result.total_elapsed_ms = (time.monotonic() - overall_start) * 1000.0

        return result

    # -- Interprocedural section transport (§4.4) --------------------------

    def _run_interprocedural_transport(
        self,
        cover: Cover,
        current_sections: Dict[SiteId, LocalSection],
        callee_summaries: Dict[str, "FixedPointResult"],
    ) -> Dict[SiteId, LocalSection]:
        """Transport callee output sections onto caller CALL_RESULT sites.

        Implements §4.4 of programcohomology.tex:
        For each call site in the cover, the callee's output boundary
        sections are transported to the caller via return→caller morphisms.

        The Grothendieck transitivity axiom requires that the composition
        of restriction maps across call boundaries must commute.  Any
        disagreement becomes an H¹ obstruction at the CALL_RESULT site.

        Parameters
        ----------
        cover : Cover
            The caller's cover; CALL_RESULT sites are endpoints.
        current_sections : dict
            Current caller sections; input-boundary sections are actuals.
        callee_summaries : dict
            {callee_name: FixedPointResult} — pre-computed callee analyses.

        Returns
        -------
        dict
            Transported sections to be merged into current_sections.
        """
        try:
            from deppy.interprocedural.section_transport import SectionTransporter
            from deppy.interprocedural.call_graph import CallEdge
        except ImportError:
            return {}

        transported: Dict[SiteId, LocalSection] = {}
        transporter = SectionTransporter(trust_policy="downgrade")

        # Identify CALL_RESULT sites in this cover
        call_result_sites = {
            sid: site
            for sid, site in cover.sites.items()
            if sid.kind == SiteKind.CALL_RESULT
        }

        for call_site_id, _call_site in call_result_sites.items():
            # Determine which callee this call-result belongs to.
            # Convention: CALL_RESULT site name is "<caller>.call_<callee>"
            # or just "<callee>" if unqualified.
            name = call_site_id.name
            callee_name: Optional[str] = None
            if ".call_" in name:
                callee_name = name.split(".call_", 1)[1]
            elif "." in name:
                callee_name = name.rsplit(".", 1)[1]
            else:
                callee_name = name

            summary = callee_summaries.get(callee_name)
            if summary is None:
                # Try prefix matching (handles qualified names)
                for k, v in callee_summaries.items():
                    if k.endswith(callee_name) or callee_name.endswith(k):
                        summary = v
                        callee_name = k
                        break

            if summary is None or summary.output_section is None:
                continue

            # Build a minimal CallEdge for the transport morphisms
            edge = CallEdge(
                caller=cover.function_name if hasattr(cover, "function_name") else "caller",
                callee=callee_name,
                call_site_id=call_site_id,
            )

            # Transport return→caller
            try:
                tr = transporter.transport_return_to_caller(
                    return_sections=dict(summary.output_section.boundary_sites),
                    call_edge=edge,
                )
                transported.update(tr.sections)
            except Exception:
                # Transport failed (missing morphism data) — skip gracefully
                pass

        return transported

    # -- Section merging utility -------------------------------------------

    def _merge_sections(
        self,
        current: Dict[SiteId, LocalSection],
        new_sections: Dict[SiteId, LocalSection],
    ) -> Tuple[int, int]:
        """Merge new sections into the current set.

        Returns (num_new, num_refined):
        - num_new: sections at sites not previously in current
        - num_refined: sections that have more refinements than before
        """
        num_new = 0
        num_refined = 0

        for sid, new_sec in new_sections.items():
            existing = current.get(sid)
            if existing is None:
                current[sid] = new_sec
                num_new += 1
            else:
                # Check if the new section has more information
                merged = self._merge_single(existing, new_sec)
                if merged is not None:
                    current[sid] = merged
                    num_refined += 1

        return num_new, num_refined

    def _merge_single(
        self,
        existing: LocalSection,
        new_section: LocalSection,
    ) -> Optional[LocalSection]:
        """Merge two sections at the same site.

        Returns the merged section if it differs from existing, None otherwise.
        """
        # Collect all refinements
        merged_refinements = dict(existing.refinements)
        changed = False

        for key, value in new_section.refinements.items():
            if key not in merged_refinements:
                merged_refinements[key] = value
                changed = True
            elif merged_refinements[key] != value:
                # Prefer the value with higher trust provenance
                from deppy.kernel.trust_classifier import trust_rank as trank
                if trank(new_section.trust) > trank(existing.trust):
                    merged_refinements[key] = value
                    changed = True

        # Use the higher trust level
        from deppy.kernel.trust_classifier import trust_join
        merged_trust = trust_join(existing.trust, new_section.trust)
        if merged_trust != existing.trust:
            changed = True

        # Use the more specific carrier type
        carrier = existing.carrier_type
        if carrier is None and new_section.carrier_type is not None:
            carrier = new_section.carrier_type
            changed = True

        # Merge witnesses
        merged_witnesses = dict(existing.witnesses)
        for key, value in new_section.witnesses.items():
            if key not in merged_witnesses:
                merged_witnesses[key] = value
                changed = True

        if not changed:
            return None

        return LocalSection(
            site_id=existing.site_id,
            carrier_type=carrier,
            refinements=merged_refinements,
            trust=merged_trust,
            provenance=f"merged: {existing.provenance} + {new_section.provenance}",
            witnesses=merged_witnesses,
        )
