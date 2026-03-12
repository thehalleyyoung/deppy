"""Local solving stage for the sheaf-descent analysis pipeline.

Stage 3: Dispatch each site to the appropriate theory pack and produce
local sections.  The solver fills in carrier types and refinement
predicates at each site, constrained by the guards harvested in Stage 1.
"""

from __future__ import annotations

import time
from collections import defaultdict
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Protocol,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteSite, SiteCategory
from deppy.pipeline.pipeline_config import PipelineConfig, TheoryPack
from deppy.pipeline.stage_registry import Stage, StageMetadata
from deppy.pipeline.stages.cover_stage import CoverResult


# ===================================================================
#  Theory solver protocol
# ===================================================================


class TheorySolver(Protocol):
    """Protocol for theory-specific local solvers."""

    def can_handle(self, site_kind: SiteKind) -> bool:
        """Return True if this solver handles the given site kind."""
        ...

    def solve_site(
        self,
        site_id: SiteId,
        site: Any,
        context: Dict[str, Any],
        config: PipelineConfig,
    ) -> Optional[LocalSection]:
        """Produce a local section for the given site.

        Returns None if the site cannot be solved by this theory.
        """
        ...


# ===================================================================
#  Built-in theory solvers
# ===================================================================


class ArithmeticSolver:
    """Theory solver for arithmetic and numeric refinements.

    Handles sites involving integer arithmetic, comparisons, and
    numeric bounds.  Produces refinements like ``v > 0``, ``v >= 0``,
    bounded ranges, etc.
    """

    def can_handle(self, site_kind: SiteKind) -> bool:
        return site_kind in (
            SiteKind.ARGUMENT_BOUNDARY,
            SiteKind.RETURN_OUTPUT_BOUNDARY,
            SiteKind.BRANCH_GUARD,
            SiteKind.SSA_VALUE,
            SiteKind.LOOP_HEADER_INVARIANT,
        )

    def solve_site(
        self,
        site_id: SiteId,
        site: Any,
        context: Dict[str, Any],
        config: PipelineConfig,
    ) -> Optional[LocalSection]:
        metadata = getattr(site, "metadata", None) or {}
        carrier_schema = getattr(site, "carrier_schema", None) or {}

        refinements: Dict[str, Any] = {}
        carrier_type: Any = None

        # Extract type from annotation if available
        if isinstance(carrier_schema, dict):
            if "guard_kind" in carrier_schema:
                source = carrier_schema.get("source", "")
                refinements["guard_source"] = source
                refinements["guard_kind"] = carrier_schema["guard_kind"]

        # Build numeric refinements from guard context
        guard_info = context.get("guard_info", {}).get(str(site_id), {})
        if guard_info:
            if "lower_bound" in guard_info:
                refinements["lower_bound"] = guard_info["lower_bound"]
            if "upper_bound" in guard_info:
                refinements["upper_bound"] = guard_info["upper_bound"]

        trust = TrustLevel.TRUSTED_AUTO
        if site_id.kind == SiteKind.LOOP_HEADER_INVARIANT:
            trust = TrustLevel.BOUNDED_AUTO

        return LocalSection(
            site_id=site_id,
            carrier_type=carrier_type,
            refinements=refinements,
            trust=trust,
            provenance=f"arithmetic_solver:{site_id.kind.value}",
        )


class StringSolver:
    """Theory solver for string refinements.

    Handles sites involving string operations: length constraints,
    pattern matching, encoding properties.
    """

    def can_handle(self, site_kind: SiteKind) -> bool:
        return site_kind in (
            SiteKind.ARGUMENT_BOUNDARY,
            SiteKind.RETURN_OUTPUT_BOUNDARY,
            SiteKind.BRANCH_GUARD,
        )

    def solve_site(
        self,
        site_id: SiteId,
        site: Any,
        context: Dict[str, Any],
        config: PipelineConfig,
    ) -> Optional[LocalSection]:
        carrier_schema = getattr(site, "carrier_schema", None) or {}

        # Only handle string-related sites
        if isinstance(carrier_schema, dict):
            source = carrier_schema.get("source", "")
            if not any(kw in source for kw in ("str", "len(", ".startswith", ".endswith", "encode")):
                return None

        refinements: Dict[str, Any] = {}
        if isinstance(carrier_schema, dict) and "source" in carrier_schema:
            refinements["string_constraint"] = carrier_schema["source"]

        return LocalSection(
            site_id=site_id,
            carrier_type=None,
            refinements=refinements,
            trust=TrustLevel.TRUSTED_AUTO,
            provenance="string_solver",
        )


class CollectionSolver:
    """Theory solver for collection (list, dict, set) refinements.

    Handles sites involving collection operations: length bounds,
    membership, emptiness, containment.
    """

    def can_handle(self, site_kind: SiteKind) -> bool:
        return site_kind in (
            SiteKind.ARGUMENT_BOUNDARY,
            SiteKind.RETURN_OUTPUT_BOUNDARY,
            SiteKind.BRANCH_GUARD,
        )

    def solve_site(
        self,
        site_id: SiteId,
        site: Any,
        context: Dict[str, Any],
        config: PipelineConfig,
    ) -> Optional[LocalSection]:
        carrier_schema = getattr(site, "carrier_schema", None) or {}

        if isinstance(carrier_schema, dict):
            source = carrier_schema.get("source", "")
            if not any(kw in source for kw in ("list", "dict", "set", "len(", "append", "in ")):
                return None

        refinements: Dict[str, Any] = {}
        if isinstance(carrier_schema, dict) and "source" in carrier_schema:
            refinements["collection_constraint"] = carrier_schema["source"]

        return LocalSection(
            site_id=site_id,
            carrier_type=None,
            refinements=refinements,
            trust=TrustLevel.TRUSTED_AUTO,
            provenance="collection_solver",
        )


class NoneSolver:
    """Theory solver for None/Optional refinements.

    Handles isinstance checks, ``is None``/``is not None`` guards,
    and Optional type annotations.
    """

    def can_handle(self, site_kind: SiteKind) -> bool:
        return site_kind in (
            SiteKind.ARGUMENT_BOUNDARY,
            SiteKind.RETURN_OUTPUT_BOUNDARY,
            SiteKind.BRANCH_GUARD,
        )

    def solve_site(
        self,
        site_id: SiteId,
        site: Any,
        context: Dict[str, Any],
        config: PipelineConfig,
    ) -> Optional[LocalSection]:
        carrier_schema = getattr(site, "carrier_schema", None) or {}

        if isinstance(carrier_schema, dict):
            source = carrier_schema.get("source", "")
            guard_kind = carrier_schema.get("guard_kind", "")
            if "none_check" not in guard_kind and "None" not in source and "Optional" not in source:
                return None

        metadata = getattr(site, "metadata", None) or {}
        refinements: Dict[str, Any] = {}
        negated = metadata.get("negated", False)

        if negated:
            refinements["nullability"] = "non_null"
        else:
            refinements["nullability"] = "nullable"

        return LocalSection(
            site_id=site_id,
            carrier_type=None,
            refinements=refinements,
            trust=TrustLevel.TRUSTED_AUTO,
            provenance="none_solver",
        )


class TensorSolver:
    """Theory solver for tensor shape refinements."""

    def can_handle(self, site_kind: SiteKind) -> bool:
        return site_kind in (
            SiteKind.TENSOR_SHAPE,
            SiteKind.TENSOR_ORDER,
            SiteKind.TENSOR_INDEXING,
        )

    def solve_site(
        self,
        site_id: SiteId,
        site: Any,
        context: Dict[str, Any],
        config: PipelineConfig,
    ) -> Optional[LocalSection]:
        return LocalSection(
            site_id=site_id,
            carrier_type=None,
            refinements={"tensor": True},
            trust=TrustLevel.BOUNDED_AUTO,
            provenance="tensor_solver",
        )


class HeapSolver:
    """Theory solver for heap protocol refinements."""

    def can_handle(self, site_kind: SiteKind) -> bool:
        return site_kind == SiteKind.HEAP_PROTOCOL

    def solve_site(
        self,
        site_id: SiteId,
        site: Any,
        context: Dict[str, Any],
        config: PipelineConfig,
    ) -> Optional[LocalSection]:
        return LocalSection(
            site_id=site_id,
            carrier_type=None,
            refinements={"heap": True},
            trust=TrustLevel.BOUNDED_AUTO,
            provenance="heap_solver",
        )


# ===================================================================
#  Solver dispatch
# ===================================================================


_THEORY_SOLVERS: Dict[TheoryPack, Callable[[], Any]] = {
    TheoryPack.BUILTIN_ARITHMETIC: ArithmeticSolver,
    TheoryPack.BUILTIN_STRING: StringSolver,
    TheoryPack.BUILTIN_COLLECTION: CollectionSolver,
    TheoryPack.BUILTIN_NONE: NoneSolver,
    TheoryPack.TENSOR_SHAPE: TensorSolver,
    TheoryPack.HEAP_PROTOCOL: HeapSolver,
}


def _build_solvers(packs: Sequence[TheoryPack]) -> List[Any]:
    """Instantiate solvers for the requested theory packs."""
    solvers: List[Any] = []
    for pack in packs:
        factory = _THEORY_SOLVERS.get(pack)
        if factory is not None:
            solvers.append(factory())
    return solvers


# ===================================================================
#  Solve result
# ===================================================================


@dataclass(frozen=True)
class SiteSolveRecord:
    """Record of solving a single site."""

    _site_id: SiteId
    _section: Optional[LocalSection]
    _solver_name: str
    _elapsed_seconds: float
    _success: bool

    @property
    def site_id(self) -> SiteId:
        return self._site_id

    @property
    def section(self) -> Optional[LocalSection]:
        return self._section

    @property
    def solver_name(self) -> str:
        return self._solver_name

    @property
    def elapsed_seconds(self) -> float:
        return self._elapsed_seconds

    @property
    def success(self) -> bool:
        return self._success


@dataclass(frozen=True)
class SolveResult:
    """Result of the local solving stage."""

    _sections: Dict[SiteId, LocalSection]
    _records: Tuple[SiteSolveRecord, ...]
    _unsolved_sites: FrozenSet[SiteId]
    _total_elapsed: float = 0.0
    _warnings: Tuple[str, ...] = ()

    @property
    def sections(self) -> Dict[SiteId, LocalSection]:
        return dict(self._sections)

    @property
    def records(self) -> Tuple[SiteSolveRecord, ...]:
        return self._records

    @property
    def unsolved_sites(self) -> FrozenSet[SiteId]:
        return self._unsolved_sites

    @property
    def total_elapsed(self) -> float:
        return self._total_elapsed

    @property
    def warnings(self) -> Tuple[str, ...]:
        return self._warnings

    @property
    def solved_count(self) -> int:
        return len(self._sections)

    @property
    def unsolved_count(self) -> int:
        return len(self._unsolved_sites)

    def section_at(self, site_id: SiteId) -> Optional[LocalSection]:
        return self._sections.get(site_id)


# ===================================================================
#  SolveStage
# ===================================================================


class SolveStage(Stage):
    """Stage 3: Dispatch sites to theory solvers and produce local sections.

    Iterates over all sites in the cover, finds the appropriate theory
    solver for each, and produces a local section.  Sites that no solver
    can handle are recorded as unsolved.
    """

    def metadata(self) -> StageMetadata:
        return StageMetadata(
            _name="solve",
            _description="Dispatch sites to theory solvers for local solving",
            _dependencies=frozenset({"cover"}),
            _order_hint=30,
        )

    def run(self, context: Dict[str, Any], config: PipelineConfig) -> SolveResult:
        """Execute local solving.

        Expects context to contain ``cover`` key with a CoverResult.
        """
        cover_result: CoverResult = context.get("cover")  # type: ignore[assignment]
        if cover_result is None:
            return SolveResult(
                _sections={},
                _records=(),
                _unsolved_sites=frozenset(),
                _warnings=("Cover stage did not produce results",),
            )

        cover = cover_result.cover
        solvers = _build_solvers(config.theory_packs)

        sections: Dict[SiteId, LocalSection] = {}
        records: List[SiteSolveRecord] = []
        unsolved: Set[SiteId] = set()
        warnings: List[str] = []

        overall_start = time.monotonic()

        for site_id, site in cover.sites.items():
            site_start = time.monotonic()
            solved = False
            solver_name = ""

            for solver in solvers:
                if solver.can_handle(site_id.kind):
                    try:
                        section = solver.solve_site(
                            site_id, site, context, config
                        )
                        if section is not None:
                            sections[site_id] = section
                            solver_name = type(solver).__name__
                            solved = True
                            break
                    except Exception as exc:
                        warnings.append(
                            f"Solver {type(solver).__name__} failed on "
                            f"{site_id}: {exc}"
                        )

            if not solved:
                # Create a residual section for unsolved sites
                fallback = LocalSection(
                    site_id=site_id,
                    carrier_type=None,
                    refinements={},
                    trust=TrustLevel.RESIDUAL,
                    provenance="unsolved",
                )
                sections[site_id] = fallback
                unsolved.add(site_id)
                solver_name = "fallback"

            site_elapsed = time.monotonic() - site_start
            records.append(SiteSolveRecord(
                _site_id=site_id,
                _section=sections.get(site_id),
                _solver_name=solver_name,
                _elapsed_seconds=site_elapsed,
                _success=solved,
            ))

        overall_elapsed = time.monotonic() - overall_start

        return SolveResult(
            _sections=sections,
            _records=tuple(records),
            _unsolved_sites=frozenset(unsolved),
            _total_elapsed=overall_elapsed,
            _warnings=tuple(warnings),
        )
