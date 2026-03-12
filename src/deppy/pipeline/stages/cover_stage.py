"""Cover synthesis stage for the sheaf-descent analysis pipeline.

Stage 2: Build the site cover {U_i -> S} using Algorithm 1 from the
sheaf-descent framework.  Maps harvested guards and annotations to
observation sites, constructs morphisms between sites, and identifies
overlaps.
"""

from __future__ import annotations

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
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite, CoverBuilder, SiteCategory
from deppy.pipeline.pipeline_config import PipelineConfig
from deppy.pipeline.stage_registry import Stage, StageMetadata
from deppy.pipeline.stages.parse_stage import IRModule, ScopeInfo, ParseResult
from deppy.pipeline.stages.harvest_stage import (
    GuardKind,
    HarvestedGuard,
    HarvestResult,
)


# ===================================================================
#  Cover result
# ===================================================================


@dataclass(frozen=True)
class CoverResult:
    """Result of the cover synthesis stage."""

    _cover: Cover
    _site_category: SiteCategory
    _site_scope_map: Dict[SiteId, str]
    _scope_sites: Dict[str, Tuple[SiteId, ...]]
    _warnings: Tuple[str, ...] = ()

    @property
    def cover(self) -> Cover:
        return self._cover

    @property
    def site_category(self) -> SiteCategory:
        return self._site_category

    @property
    def site_scope_map(self) -> Dict[SiteId, str]:
        return self._site_scope_map

    @property
    def scope_sites(self) -> Dict[str, Tuple[SiteId, ...]]:
        return self._scope_sites

    @property
    def warnings(self) -> Tuple[str, ...]:
        return self._warnings

    @property
    def site_count(self) -> int:
        return len(self._cover.sites)

    @property
    def morphism_count(self) -> int:
        return len(self._cover.morphisms)

    @property
    def overlap_count(self) -> int:
        return len(self._cover.overlaps)


# ===================================================================
#  Site name generation
# ===================================================================


class _SiteNamer:
    """Generates unique, deterministic site names."""

    def __init__(self) -> None:
        self._counters: Dict[str, int] = defaultdict(int)

    def name_for(self, kind: SiteKind, scope: str, suffix: str = "") -> str:
        """Generate a unique site name."""
        base = f"{scope}:{kind.value}"
        if suffix:
            base = f"{base}:{suffix}"
        self._counters[base] += 1
        count = self._counters[base]
        if count > 1:
            return f"{base}#{count}"
        return base


# ===================================================================
#  Cover synthesis algorithm
# ===================================================================


class _CoverSynthesizer:
    """Algorithm 1: Build site cover from harvested guards.

    For each function scope:
    1. Create argument-boundary sites for each parameter.
    2. Create return-boundary sites.
    3. Create branch-guard sites from harvested guards.
    4. Create loop-invariant sites from while-conditions.
    5. Create error sites from try/except handlers.
    6. Build morphisms connecting sites.
    7. Detect overlaps between sites sharing variables.
    """

    def __init__(self, config: PipelineConfig) -> None:
        self._config = config
        self._namer = _SiteNamer()
        self._category = SiteCategory()
        self._builder = CoverBuilder()
        self._site_scope_map: Dict[SiteId, str] = {}
        self._scope_sites: Dict[str, List[SiteId]] = defaultdict(list)
        self._variable_sites: Dict[str, List[SiteId]] = defaultdict(list)
        self._warnings: List[str] = []

    def synthesize(
        self,
        ir: IRModule,
        harvest: HarvestResult,
    ) -> CoverResult:
        """Run the full cover synthesis algorithm."""
        for scope in ir.scopes:
            if scope.kind in ("function", "method", "async_function"):
                self._synthesize_function_cover(scope, harvest)
            elif scope.kind == "class":
                self._synthesize_class_cover(scope, harvest)

        # Build overlaps from shared variables
        self._build_variable_overlaps()

        # Build the cover
        cover = self._builder.build()

        frozen_scope_sites = {
            k: tuple(v) for k, v in self._scope_sites.items()
        }

        return CoverResult(
            _cover=cover,
            _site_category=self._category,
            _site_scope_map=dict(self._site_scope_map),
            _scope_sites=frozen_scope_sites,
            _warnings=tuple(self._warnings),
        )

    def _synthesize_function_cover(
        self,
        scope: ScopeInfo,
        harvest: HarvestResult,
    ) -> None:
        """Synthesize cover for a function scope."""
        scope_name = scope.qualified_name
        guards = harvest.guards_for_scope(scope_name)

        # Step 1: Argument-boundary sites
        arg_sites: List[SiteId] = []
        for param in scope.parameters:
            if param.is_self or param.is_cls:
                continue
            site_id = SiteId(
                kind=SiteKind.ARGUMENT_BOUNDARY,
                name=self._namer.name_for(
                    SiteKind.ARGUMENT_BOUNDARY, scope_name, param.name
                ),
                source_location=(
                    scope.qualified_name,
                    scope.line_start,
                    scope.line_end,
                ),
            )
            site = ConcreteSite(
                _site_id=site_id,
                _carrier_schema={"param": param.name},
                _metadata={
                    "scope": scope_name,
                    "param": param.name,
                    "has_annotation": param.has_annotation,
                },
            )
            self._register_site(site, scope_name)
            self._builder.mark_input(site_id)
            arg_sites.append(site_id)
            if param.name:
                self._variable_sites[f"{scope_name}:{param.name}"].append(site_id)

        # Step 2: Return-boundary site
        ret_site_id = SiteId(
            kind=SiteKind.RETURN_OUTPUT_BOUNDARY,
            name=self._namer.name_for(
                SiteKind.RETURN_OUTPUT_BOUNDARY, scope_name, "return"
            ),
            source_location=(scope_name, scope.line_start, scope.line_end),
        )
        ret_site = ConcreteSite(
            _site_id=ret_site_id,
            _carrier_schema={"return": True},
            _metadata={"scope": scope_name},
        )
        self._register_site(ret_site, scope_name)
        self._builder.mark_output(ret_site_id)

        # Step 3: Guard sites
        for guard in guards:
            if guard.kind in (GuardKind.TYPE_ANNOTATION,
                              GuardKind.CONTRACT_REQUIRES,
                              GuardKind.CONTRACT_ENSURES):
                continue  # Already handled as boundary sites

            guard_site_kind = guard.site_kind()
            site_name = self._namer.name_for(
                guard_site_kind, scope_name,
                f"L{guard.line}"
            )
            guard_site_id = SiteId(
                kind=guard_site_kind,
                name=site_name,
                source_location=(scope_name, guard.line, guard.col),
            )
            guard_site = ConcreteSite(
                _site_id=guard_site_id,
                _carrier_schema={
                    "guard_kind": guard.kind.value,
                    "source": guard.source_text,
                },
                _metadata={
                    "scope": scope_name,
                    "line": guard.line,
                    "negated": guard.negated,
                    "branch": guard.branch,
                },
            )
            self._register_site(guard_site, scope_name)

            if guard.kind == GuardKind.TRY_EXCEPT:
                self._builder.mark_error(guard_site_id)

            # Track variable-site associations
            if guard.variable_name:
                var_key = f"{scope_name}:{guard.variable_name}"
                self._variable_sites[var_key].append(guard_site_id)

        # Step 4: Build morphisms from arguments to guard sites
        self._build_scope_morphisms(scope_name, arg_sites, ret_site_id)

    def _synthesize_class_cover(
        self,
        scope: ScopeInfo,
        harvest: HarvestResult,
    ) -> None:
        """Synthesize cover for a class scope (module-summary site)."""
        site_id = SiteId(
            kind=SiteKind.MODULE_SUMMARY,
            name=self._namer.name_for(SiteKind.MODULE_SUMMARY, scope.qualified_name),
            source_location=(scope.qualified_name, scope.line_start, scope.line_end),
        )
        site = ConcreteSite(
            _site_id=site_id,
            _carrier_schema={"class": scope.name},
            _metadata={"scope": scope.qualified_name, "kind": "class"},
        )
        self._register_site(site, scope.qualified_name)

    def _register_site(self, site: ConcreteSite, scope_name: str) -> None:
        """Register a site with the category and builder."""
        self._category.add_site(site)
        self._builder.add_site(site)
        self._site_scope_map[site.site_id] = scope_name
        self._scope_sites[scope_name].append(site.site_id)

    def _build_scope_morphisms(
        self,
        scope_name: str,
        arg_sites: List[SiteId],
        ret_site_id: SiteId,
    ) -> None:
        """Build morphisms within a function scope.

        Creates restriction morphisms from argument sites to guard sites
        that reference those arguments, and from guard sites to the
        return site.
        """
        scope_site_ids = self._scope_sites.get(scope_name, [])
        guard_sites = [
            sid for sid in scope_site_ids
            if sid.kind not in (SiteKind.ARGUMENT_BOUNDARY,
                                SiteKind.RETURN_OUTPUT_BOUNDARY,
                                SiteKind.MODULE_SUMMARY)
        ]

        # Argument -> guard morphisms
        for arg_site in arg_sites:
            for guard_site in guard_sites:
                # Check if the guard references this argument's variable
                arg_var = self._get_site_variable(arg_site)
                guard_var = self._get_site_variable(guard_site)
                if arg_var and guard_var and arg_var == guard_var:
                    morphism = ConcreteMorphism(
                        _source=arg_site,
                        _target=guard_site,
                        _metadata={"kind": "arg_to_guard"},
                    )
                    self._category.add_morphism(morphism)
                    self._builder.add_morphism(morphism)

        # Guard -> return morphisms (for guards that constrain return type)
        for guard_site in guard_sites:
            if guard_site.kind != SiteKind.ERROR:
                morphism = ConcreteMorphism(
                    _source=guard_site,
                    _target=ret_site_id,
                    projection=None,
                    _metadata={"kind": "guard_to_return"},
                )
                self._category.add_morphism(morphism)
                self._builder.add_morphism(morphism)

        # Argument -> return morphisms (direct data flow)
        for arg_site in arg_sites:
            morphism = ConcreteMorphism(
                _source=arg_site,
                _target=ret_site_id,
                _metadata={"kind": "arg_to_return"},
            )
            self._category.add_morphism(morphism)
            self._builder.add_morphism(morphism)

    def _get_site_variable(self, site_id: SiteId) -> Optional[str]:
        """Get the primary variable associated with a site."""
        site = self._category.get_site(site_id)
        if site is None:
            return None
        metadata = getattr(site, "metadata", None)
        if metadata and isinstance(metadata, dict):
            return metadata.get("param") or metadata.get("variable")
        return None

    def _build_variable_overlaps(self) -> None:
        """Build overlaps between sites that share variables."""
        for var_key, site_ids in self._variable_sites.items():
            for i in range(len(site_ids)):
                for j in range(i + 1, len(site_ids)):
                    self._builder.add_overlap(site_ids[i], site_ids[j])


# ===================================================================
#  CoverStage
# ===================================================================


class CoverStage(Stage):
    """Stage 2: Synthesize the site cover.

    Builds the cover {U_i -> S} in the Grothendieck topology from
    harvested guards and parsed scope information.
    """

    def metadata(self) -> StageMetadata:
        return StageMetadata(
            _name="cover",
            _description="Synthesize site cover from harvested guards",
            _dependencies=frozenset({"parse", "harvest"}),
            _order_hint=20,
        )

    def run(self, context: Dict[str, Any], config: PipelineConfig) -> CoverResult:
        """Execute cover synthesis.

        Expects context to contain:
        - ``parse``: ParseResult
        - ``harvest``: HarvestResult
        """
        parse_result: ParseResult = context.get("parse")  # type: ignore[assignment]
        harvest_result: HarvestResult = context.get("harvest")  # type: ignore[assignment]

        if parse_result is None or not parse_result.success:
            empty_cover = Cover()
            return CoverResult(
                _cover=empty_cover,
                _site_category=SiteCategory(),
                _site_scope_map={},
                _scope_sites={},
                _warnings=("Parse stage did not succeed",),
            )

        if harvest_result is None:
            return CoverResult(
                _cover=Cover(),
                _site_category=SiteCategory(),
                _site_scope_map={},
                _scope_sites={},
                _warnings=("Harvest stage did not produce results",),
            )

        synthesizer = _CoverSynthesizer(config)
        return synthesizer.synthesize(parse_result.ir_module, harvest_result)
