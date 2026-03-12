"""Backward + forward synthesis stage for the sheaf-descent analysis pipeline.

Stage 4: Run Algorithms 3 (backward synthesis) and 4 (forward synthesis)
to propagate type information across the site cover.  Backward synthesis
pulls output constraints back to inputs; forward synthesis pushes input
types forward to compute output types.  Iterates until convergence or
max iterations.
"""

from __future__ import annotations

import time
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
    CechCochainData,
    CohomologyClass,
)
from deppy.core.site import ConcreteMorphism, SiteCategory
from deppy.pipeline.pipeline_config import PipelineConfig
from deppy.pipeline.stage_registry import Stage, StageMetadata
from deppy.pipeline.stages.cover_stage import CoverResult
from deppy.pipeline.stages.solve_stage import SolveResult


# ===================================================================
#  Synthesis data structures
# ===================================================================


@dataclass(frozen=True)
class PropagationRecord:
    """Record of a single propagation step."""

    _from_site: SiteId
    _to_site: SiteId
    _direction: str  # "backward" or "forward"
    _refinements_added: int
    _iteration: int

    @property
    def from_site(self) -> SiteId:
        return self._from_site

    @property
    def to_site(self) -> SiteId:
        return self._to_site

    @property
    def direction(self) -> str:
        return self._direction

    @property
    def refinements_added(self) -> int:
        return self._refinements_added

    @property
    def iteration(self) -> int:
        return self._iteration


@dataclass(frozen=True)
class ConvergenceInfo:
    """Information about convergence of the synthesis loop."""

    _converged: bool
    _iterations_used: int
    _max_iterations: int
    _final_delta: float
    _history: Tuple[float, ...]  # delta per iteration

    @property
    def converged(self) -> bool:
        return self._converged

    @property
    def iterations_used(self) -> int:
        return self._iterations_used

    @property
    def max_iterations(self) -> int:
        return self._max_iterations

    @property
    def final_delta(self) -> float:
        return self._final_delta

    @property
    def history(self) -> Tuple[float, ...]:
        return self._history


@dataclass(frozen=True)
class SynthesisResult:
    """Result of the backward + forward synthesis stage."""

    _sections: Dict[SiteId, LocalSection]
    _obstructions: Tuple[ObstructionData, ...]
    _convergence: ConvergenceInfo
    _propagation_log: Tuple[PropagationRecord, ...]
    _total_elapsed: float = 0.0
    _warnings: Tuple[str, ...] = ()

    @property
    def sections(self) -> Dict[SiteId, LocalSection]:
        return dict(self._sections)

    @property
    def obstructions(self) -> Tuple[ObstructionData, ...]:
        return self._obstructions

    @property
    def convergence(self) -> ConvergenceInfo:
        return self._convergence

    @property
    def propagation_log(self) -> Tuple[PropagationRecord, ...]:
        return self._propagation_log

    @property
    def total_elapsed(self) -> float:
        return self._total_elapsed

    @property
    def warnings(self) -> Tuple[str, ...]:
        return self._warnings

    @property
    def has_obstructions(self) -> bool:
        return len(self._obstructions) > 0

    @property
    def obstruction_count(self) -> int:
        return len(self._obstructions)

    def section_at(self, site_id: SiteId) -> Optional[LocalSection]:
        return self._sections.get(site_id)


# ===================================================================
#  Synthesis engine
# ===================================================================


class _SynthesisEngine:
    """Implements bidirectional refinement propagation.

    Algorithm 3 (backward synthesis):
      For each output boundary site, trace morphisms backward to
      propagate output constraints to intermediate and input sites.

    Algorithm 4 (forward synthesis):
      For each input boundary site, trace morphisms forward to
      propagate input types through intermediate sites to outputs.

    The gluing check detects obstructions where sections on overlapping
    sites are incompatible.
    """

    def __init__(self, config: PipelineConfig) -> None:
        self._config = config
        self._propagation_log: List[PropagationRecord] = []
        self._warnings: List[str] = []

    def synthesize(
        self,
        cover: Cover,
        category: SiteCategory,
        initial_sections: Dict[SiteId, LocalSection],
    ) -> SynthesisResult:
        """Run the full bidirectional synthesis loop."""
        start_time = time.monotonic()
        sections = dict(initial_sections)
        max_iter = self._config.max_iterations
        delta_history: List[float] = []

        # Build adjacency for backward/forward traversal
        forward_adj = self._build_forward_adjacency(cover)
        backward_adj = self._build_backward_adjacency(cover)
        morphism_map = self._build_morphism_map(cover)

        converged = False
        iteration = 0

        for iteration in range(1, max_iter + 1):
            prev_refinement_count = self._count_refinements(sections)

            # Backward synthesis: propagate from outputs to inputs
            self._backward_pass(
                cover, backward_adj, morphism_map, sections, iteration
            )

            # Forward synthesis: propagate from inputs to outputs
            self._forward_pass(
                cover, forward_adj, morphism_map, sections, iteration
            )

            curr_refinement_count = self._count_refinements(sections)
            delta = abs(curr_refinement_count - prev_refinement_count)
            delta_history.append(float(delta))

            if delta == 0:
                converged = True
                break

        # Obstruction extraction: check gluing condition on overlaps
        obstructions = self._extract_obstructions(cover, sections)

        elapsed = time.monotonic() - start_time

        convergence = ConvergenceInfo(
            _converged=converged,
            _iterations_used=iteration,
            _max_iterations=max_iter,
            _final_delta=delta_history[-1] if delta_history else 0.0,
            _history=tuple(delta_history),
        )

        return SynthesisResult(
            _sections=sections,
            _obstructions=tuple(obstructions),
            _convergence=convergence,
            _propagation_log=tuple(self._propagation_log),
            _total_elapsed=elapsed,
            _warnings=tuple(self._warnings),
        )

    # -- Adjacency building -----------------------------------------------

    @staticmethod
    def _build_forward_adjacency(cover: Cover) -> Dict[SiteId, List[SiteId]]:
        """Build source -> [targets] adjacency from morphisms."""
        adj: Dict[SiteId, List[SiteId]] = defaultdict(list)
        for morphism in cover.morphisms:
            adj[morphism.source].append(morphism.target)
        return dict(adj)

    @staticmethod
    def _build_backward_adjacency(cover: Cover) -> Dict[SiteId, List[SiteId]]:
        """Build target -> [sources] adjacency from morphisms."""
        adj: Dict[SiteId, List[SiteId]] = defaultdict(list)
        for morphism in cover.morphisms:
            adj[morphism.target].append(morphism.source)
        return dict(adj)

    @staticmethod
    def _build_morphism_map(
        cover: Cover,
    ) -> Dict[Tuple[SiteId, SiteId], Any]:
        """Build (source, target) -> morphism map."""
        result: Dict[Tuple[SiteId, SiteId], Any] = {}
        for morphism in cover.morphisms:
            result[(morphism.source, morphism.target)] = morphism
        return result

    # -- Backward synthesis (Algorithm 3) ---------------------------------

    def _backward_pass(
        self,
        cover: Cover,
        backward_adj: Dict[SiteId, List[SiteId]],
        morphism_map: Dict[Tuple[SiteId, SiteId], Any],
        sections: Dict[SiteId, LocalSection],
        iteration: int,
    ) -> None:
        """Propagate constraints backward from output boundary."""
        worklist: List[SiteId] = list(cover.output_boundary)
        visited: Set[SiteId] = set()

        while worklist:
            current = worklist.pop(0)
            if current in visited:
                continue
            visited.add(current)

            current_section = sections.get(current)
            if current_section is None:
                continue

            # Propagate to predecessors
            predecessors = backward_adj.get(current, [])
            for pred_id in predecessors:
                morphism = morphism_map.get((pred_id, current))
                if morphism is None:
                    continue

                pred_section = sections.get(pred_id)
                if pred_section is None:
                    continue

                # Pull back refinements along the morphism
                new_refinements = self._pullback_refinements(
                    current_section, pred_section, morphism
                )

                if new_refinements:
                    merged = dict(pred_section.refinements)
                    for k, v in new_refinements.items():
                        if k not in merged:
                            merged[k] = v

                    if len(merged) > len(pred_section.refinements):
                        sections[pred_id] = LocalSection(
                            site_id=pred_id,
                            carrier_type=pred_section.carrier_type,
                            refinements=merged,
                            trust=self._min_trust(
                                pred_section.trust, current_section.trust
                            ),
                            provenance=f"backward_synth:iter{iteration}",
                        )
                        self._propagation_log.append(PropagationRecord(
                            _from_site=current,
                            _to_site=pred_id,
                            _direction="backward",
                            _refinements_added=len(merged) - len(pred_section.refinements),
                            _iteration=iteration,
                        ))

                    worklist.append(pred_id)

    # -- Forward synthesis (Algorithm 4) ----------------------------------

    def _forward_pass(
        self,
        cover: Cover,
        forward_adj: Dict[SiteId, List[SiteId]],
        morphism_map: Dict[Tuple[SiteId, SiteId], Any],
        sections: Dict[SiteId, LocalSection],
        iteration: int,
    ) -> None:
        """Propagate types forward from input boundary."""
        worklist: List[SiteId] = list(cover.input_boundary)
        visited: Set[SiteId] = set()

        while worklist:
            current = worklist.pop(0)
            if current in visited:
                continue
            visited.add(current)

            current_section = sections.get(current)
            if current_section is None:
                continue

            # Propagate to successors
            successors = forward_adj.get(current, [])
            for succ_id in successors:
                morphism = morphism_map.get((current, succ_id))
                if morphism is None:
                    continue

                succ_section = sections.get(succ_id)
                if succ_section is None:
                    continue

                # Push forward refinements along the morphism
                new_refinements = self._pushforward_refinements(
                    current_section, succ_section, morphism
                )

                if new_refinements:
                    merged = dict(succ_section.refinements)
                    for k, v in new_refinements.items():
                        if k not in merged:
                            merged[k] = v

                    if len(merged) > len(succ_section.refinements):
                        # Promote carrier type if successor has none
                        carrier = succ_section.carrier_type
                        if carrier is None and current_section.carrier_type is not None:
                            carrier = current_section.carrier_type

                        sections[succ_id] = LocalSection(
                            site_id=succ_id,
                            carrier_type=carrier,
                            refinements=merged,
                            trust=self._min_trust(
                                succ_section.trust, current_section.trust
                            ),
                            provenance=f"forward_synth:iter{iteration}",
                        )
                        self._propagation_log.append(PropagationRecord(
                            _from_site=current,
                            _to_site=succ_id,
                            _direction="forward",
                            _refinements_added=len(merged) - len(succ_section.refinements),
                            _iteration=iteration,
                        ))

                    worklist.append(succ_id)

    # -- Obstruction extraction -------------------------------------------

    def _extract_obstructions(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[ObstructionData]:
        """Check the gluing condition on overlaps.

        Two sections on overlapping sites must agree on their shared
        refinements.  A disagreement is an obstruction in H^1.
        """
        obstructions: List[ObstructionData] = []

        for site_a, site_b in cover.overlaps:
            section_a = sections.get(site_a)
            section_b = sections.get(site_b)
            if section_a is None or section_b is None:
                continue

            conflicts = self._check_overlap_compatibility(
                section_a, section_b
            )
            if conflicts:
                cochain = CechCochainData(
                    degree=1,
                    values={(site_a, site_b): conflicts},
                )
                cohomology = CohomologyClass(
                    degree=1,
                    representative=cochain,
                    is_trivial=False,
                )
                obstruction = ObstructionData(
                    cohomology_class=cohomology,
                    conflicting_overlaps=[(site_a, site_b)],
                    explanation=self._format_conflict(
                        site_a, site_b, conflicts
                    ),
                )
                obstructions.append(obstruction)

        return obstructions

    # -- Refinement propagation helpers -----------------------------------

    @staticmethod
    def _pullback_refinements(
        target_section: LocalSection,
        source_section: LocalSection,
        morphism: Any,
    ) -> Dict[str, Any]:
        """Pull refinements back from target to source along morphism."""
        new_refs: Dict[str, Any] = {}
        projection = getattr(morphism, "projection", None)

        if projection:
            # Use the projection to map target keys back to source keys
            inverse_proj = {v: k for k, v in projection.items()}
            for tgt_key, value in target_section.refinements.items():
                src_key = inverse_proj.get(tgt_key, tgt_key)
                if src_key not in source_section.refinements:
                    new_refs[src_key] = value
        else:
            # Identity projection: all target refinements apply to source
            for key, value in target_section.refinements.items():
                if key not in source_section.refinements:
                    new_refs[key] = value

        return new_refs

    @staticmethod
    def _pushforward_refinements(
        source_section: LocalSection,
        target_section: LocalSection,
        morphism: Any,
    ) -> Dict[str, Any]:
        """Push refinements forward from source to target along morphism."""
        new_refs: Dict[str, Any] = {}
        projection = getattr(morphism, "projection", None)

        if projection:
            for tgt_key, src_key in projection.items():
                if src_key in source_section.refinements:
                    if tgt_key not in target_section.refinements:
                        new_refs[tgt_key] = source_section.refinements[src_key]
        else:
            for key, value in source_section.refinements.items():
                if key not in target_section.refinements:
                    new_refs[key] = value

        return new_refs

    @staticmethod
    def _check_overlap_compatibility(
        section_a: LocalSection,
        section_b: LocalSection,
    ) -> Dict[str, Tuple[Any, Any]]:
        """Check if two sections agree on shared refinement keys."""
        conflicts: Dict[str, Tuple[Any, Any]] = {}
        shared_keys = set(section_a.refinements.keys()) & set(section_b.refinements.keys())

        for key in shared_keys:
            val_a = section_a.refinements[key]
            val_b = section_b.refinements[key]
            if val_a != val_b:
                # Check for semantic compatibility, not just syntactic equality
                if not _semantically_compatible(val_a, val_b):
                    conflicts[key] = (val_a, val_b)

        return conflicts

    @staticmethod
    def _format_conflict(
        site_a: SiteId,
        site_b: SiteId,
        conflicts: Dict[str, Tuple[Any, Any]],
    ) -> str:
        """Format a conflict description for diagnostics."""
        parts: List[str] = [
            f"Gluing obstruction between {site_a} and {site_b}:"
        ]
        for key, (val_a, val_b) in conflicts.items():
            parts.append(f"  Key '{key}': {val_a!r} vs {val_b!r}")
        return "\n".join(parts)

    @staticmethod
    def _count_refinements(sections: Dict[SiteId, LocalSection]) -> int:
        """Count total refinements across all sections."""
        return sum(len(s.refinements) for s in sections.values())

    @staticmethod
    def _min_trust(a: TrustLevel, b: TrustLevel) -> TrustLevel:
        """Return the lower of two trust levels."""
        order = {
            TrustLevel.PROOF_BACKED: 5,
            TrustLevel.TRUSTED_AUTO: 4,
            TrustLevel.BOUNDED_AUTO: 3,
            TrustLevel.TRACE_BACKED: 2,
            TrustLevel.ASSUMED: 1,
            TrustLevel.RESIDUAL: 0,
        }
        if order.get(a, 0) <= order.get(b, 0):
            return a
        return b


def _semantically_compatible(a: Any, b: Any) -> bool:
    """Check if two refinement values are semantically compatible.

    Conservative check -- only returns True when compatibility is clear.
    """
    if a == b:
        return True
    # Numeric bounds compatibility
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        return False  # different numbers are different constraints
    # String subsumption
    if isinstance(a, str) and isinstance(b, str):
        return a in b or b in a
    return False


# ===================================================================
#  SynthesisStage
# ===================================================================


class SynthesisStage(Stage):
    """Stage 4: Backward + forward synthesis.

    Runs Algorithms 3 and 4 to propagate type information
    bidirectionally across the site cover until convergence.
    Extracts obstructions from incompatible sections on overlaps.
    """

    def metadata(self) -> StageMetadata:
        return StageMetadata(
            _name="synthesis",
            _description="Bidirectional refinement synthesis (Algorithms 3+4)",
            _dependencies=frozenset({"cover", "solve"}),
            _order_hint=40,
        )

    def run(self, context: Dict[str, Any], config: PipelineConfig) -> SynthesisResult:
        """Execute bidirectional synthesis.

        Expects context to contain:
        - ``cover``: CoverResult
        - ``solve``: SolveResult
        """
        cover_result: CoverResult = context.get("cover")  # type: ignore[assignment]
        solve_result: SolveResult = context.get("solve")  # type: ignore[assignment]

        if cover_result is None or solve_result is None:
            return SynthesisResult(
                _sections={},
                _obstructions=(),
                _convergence=ConvergenceInfo(
                    _converged=True,
                    _iterations_used=0,
                    _max_iterations=config.max_iterations,
                    _final_delta=0.0,
                    _history=(),
                ),
                _propagation_log=(),
                _warnings=("Required stages did not produce results",),
            )

        engine = _SynthesisEngine(config)
        return engine.synthesize(
            cover_result.cover,
            cover_result.site_category,
            solve_result.sections,
        )
