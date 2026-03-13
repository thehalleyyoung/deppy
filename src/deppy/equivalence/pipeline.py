"""Equivalence checking pipeline.

Orchestrates the full equivalence analysis from source files to verdict:

    parse_both -> harvest_both -> align_covers -> local_check -> glue -> report

This follows the same staged architecture as the main deppy pipeline
(pipeline/pipeline.py) but adds paired analysis and fiber-product
construction.

The pipeline can be used programmatically or via the CLI.
"""

from __future__ import annotations

import time
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Tuple,
)

from deppy.core._protocols import (
    Cover,
    GlobalSection,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.presheaf import ConcretePresheaf, ConcretePresheafBuilder
from deppy.core.site import CoverBuilder, SiteCategory

from deppy.equivalence._protocols import (
    EquivalenceJudgment,
    EquivalenceObstruction,
    EquivalenceStrength,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
    ProgramId,
    SiteCorrespondence,
)
from deppy.equivalence.global_checker import (
    GlobalEquivalenceChecker,
    GlobalEquivalenceResult,
)
from deppy.equivalence.site_alignment import (
    CommonRefinementBuilder,
    CommonRefinement,
    SiteMatcher,
)
from deppy.equivalence.obstruction import (
    ObstructionClassifier,
    RepairSuggester,
)


# ===========================================================================
# Pipeline configuration
# ===========================================================================


@dataclass
class EquivalencePipelineConfig:
    """Configuration for the equivalence pipeline."""
    strength: EquivalenceStrength = EquivalenceStrength.DENOTATIONAL
    function_name: Optional[str] = None
    check_gluing: bool = True
    compute_cohomology: bool = True
    use_solver: bool = True
    solver_timeout_ms: int = 10000
    max_sites: int = 500
    use_stalk_check: bool = False
    verbose: bool = False
    sarif_output: Optional[str] = None


# ===========================================================================
# Pipeline result
# ===========================================================================


@dataclass
class EquivalencePipelineResult:
    """Result of the equivalence pipeline."""
    verdict: EquivalenceVerdict = EquivalenceVerdict.UNKNOWN
    global_result: Optional[GlobalEquivalenceResult] = None
    common_refinement: Optional[CommonRefinement] = None
    stages: Dict[str, float] = field(default_factory=dict)
    total_elapsed: float = 0.0
    sarif_path: Optional[str] = None

    @property
    def is_equivalent(self) -> bool:
        return self.verdict == EquivalenceVerdict.EQUIVALENT


# ===========================================================================
# Pipeline hooks (callbacks for observability)
# ===========================================================================


@dataclass
class EquivalencePipelineHooks:
    """Callbacks for pipeline stage events."""
    on_stage_start: Optional[Callable[[str], None]] = None
    on_stage_end: Optional[Callable[[str, float], None]] = None
    on_local_judgment: Optional[Callable[[LocalEquivalenceJudgment], None]] = None
    on_obstruction: Optional[Callable[[EquivalenceObstruction], None]] = None
    on_verdict: Optional[Callable[[EquivalenceVerdict], None]] = None


# ===========================================================================
# Equivalence pipeline
# ===========================================================================


class EquivalencePipeline:
    """Full equivalence checking pipeline.

    Stages:
    1. **parse_both**: Parse both source files into ASTs
    2. **harvest_both**: Extract semantic presheaves from both programs
    3. **align_covers**: Build common refinement cover
    4. **local_check + naturality + descent + gluing**: via GlobalEquivalenceChecker
    5. **report**: Generate verdict, obstructions, repair suggestions
    """

    def __init__(
        self,
        config: Optional[EquivalencePipelineConfig] = None,
        hooks: Optional[EquivalencePipelineHooks] = None,
    ) -> None:
        self._config = config or EquivalencePipelineConfig()
        self._hooks = hooks or EquivalencePipelineHooks()
        self._stages: Dict[str, float] = {}

    def run(
        self,
        source_f: str,
        source_g: str,
        program_f: Optional[ProgramId] = None,
        program_g: Optional[ProgramId] = None,
    ) -> EquivalencePipelineResult:
        """Run the full equivalence pipeline on two source files."""
        start = time.monotonic()

        prog_f = program_f or ProgramId(name="program_f", source_file=source_f)
        prog_g = program_g or ProgramId(name="program_g", source_file=source_g)

        # Stage 1: Parse and harvest
        self._stage_start("parse")
        sections_f, cover_f = self._parse_and_harvest(source_f, prog_f)
        sections_g, cover_g = self._parse_and_harvest(source_g, prog_g)
        self._stage_end("parse")

        # Stage 2: Build presheaves
        self._stage_start("build_presheaves")
        presheaf_f = self._build_presheaf(sections_f)
        presheaf_g = self._build_presheaf(sections_g)
        self._stage_end("build_presheaves")

        return self._run_from_presheaves(
            presheaf_f, presheaf_g,
            cover_f, cover_g,
            sections_f, sections_g,
            start,
        )

    def run_from_presheaves(
        self,
        presheaf_f: ConcretePresheaf,
        presheaf_g: ConcretePresheaf,
        cover_f: Cover,
        cover_g: Cover,
        sections_f: Optional[Dict[SiteId, LocalSection]] = None,
        sections_g: Optional[Dict[SiteId, LocalSection]] = None,
    ) -> EquivalencePipelineResult:
        """Run from pre-built presheaves (skip parsing)."""
        start = time.monotonic()
        sf = sections_f or {}
        sg = sections_g or {}
        return self._run_from_presheaves(
            presheaf_f, presheaf_g,
            cover_f, cover_g,
            sf, sg, start,
        )

    def _run_from_presheaves(
        self,
        presheaf_f: ConcretePresheaf,
        presheaf_g: ConcretePresheaf,
        cover_f: Cover,
        cover_g: Cover,
        sections_f: Dict[SiteId, LocalSection],
        sections_g: Dict[SiteId, LocalSection],
        start: float,
    ) -> EquivalencePipelineResult:
        """Core pipeline logic."""
        # Stage 3: Align covers
        self._stage_start("align_covers")
        site_cat = SiteCategory()
        alignment_builder = CommonRefinementBuilder(site_cat)
        refinement = alignment_builder.build(cover_f, cover_g)
        self._stage_end("align_covers")

        # Stage 4: Global equivalence check (local + naturality + descent + gluing)
        self._stage_start("equivalence_check")
        checker = GlobalEquivalenceChecker(
            presheaf_f=presheaf_f,
            presheaf_g=presheaf_g,
            site_category=site_cat,
            correspondences=refinement.correspondences,
            sections_f=sections_f,
            sections_g=sections_g,
            use_stalk_check=self._config.use_stalk_check,
        )
        global_result = checker.check()
        self._stage_end("equivalence_check")

        # Notify
        if self._hooks.on_verdict:
            self._hooks.on_verdict(global_result.verdict)
        for obs in global_result.obstructions:
            if self._hooks.on_obstruction:
                self._hooks.on_obstruction(obs)

        total = time.monotonic() - start

        result = EquivalencePipelineResult(
            verdict=global_result.verdict,
            global_result=global_result,
            common_refinement=refinement,
            stages=dict(self._stages),
            total_elapsed=total,
        )

        # SARIF export
        if self._config.sarif_output:
            result.sarif_path = self._export_sarif(
                global_result, self._config.sarif_output,
            )

        return result

    # -- Internal stages ---------------------------------------------------

    def _parse_and_harvest(
        self,
        source: str,
        program: ProgramId,
    ) -> Tuple[Dict[SiteId, LocalSection], Cover]:
        """Parse a source file and extract sections + cover."""
        sections: Dict[SiteId, LocalSection] = {}
        sites: List[SiteId] = []

        try:
            from deppy.pipeline.pipeline import Pipeline, PipelineConfig
            config = PipelineConfig()
            pipeline = Pipeline(config)
            result = pipeline.run(source)
            if result is not None and hasattr(result, "cover") and result.cover is not None:
                for site_id in result.cover.site_ids():
                    if hasattr(result, "global_section") and result.global_section is not None:
                        local_sec = result.global_section.at(site_id)
                        if local_sec is not None:
                            sections[site_id] = local_sec
                    sites.append(site_id)
        except (ImportError, AttributeError, Exception):
            import ast
            try:
                tree = ast.parse(source)
            except SyntaxError:
                try:
                    with open(source) as f:
                        tree = ast.parse(f.read())
                except (FileNotFoundError, SyntaxError):
                    tree = ast.parse("")

            for node in ast.walk(tree):
                if isinstance(node, ast.FunctionDef):
                    if (self._config.function_name is not None
                            and node.name != self._config.function_name):
                        continue
                    site_id = SiteId(
                        kind=SiteKind.CALL_RESULT,
                        name=node.name,
                        source_location=(program.source_file, node.lineno, node.col_offset),
                    )
                    sites.append(site_id)
                    sections[site_id] = LocalSection(
                        site_id=site_id,
                        carrier_type=None,
                        refinements={},
                        trust=TrustLevel.RESIDUAL,
                        provenance=f"ast_harvest:{program.source_file}",
                    )

        cover_builder = CoverBuilder()
        for site_id in sites:
            cover_builder.add_site(site_id)
        cover = cover_builder.build()
        return sections, cover

    def _build_presheaf(
        self,
        sections: Dict[SiteId, LocalSection],
    ) -> ConcretePresheaf:
        """Build a ConcretePresheaf from harvested sections."""
        builder = ConcretePresheafBuilder()
        for site_id, section in sections.items():
            builder.add_section(section)
        return builder.build()

    def _export_sarif(
        self,
        result: GlobalEquivalenceResult,
        output_path: str,
    ) -> str:
        """Export results as SARIF."""
        try:
            from deppy.equivalence.render import EquivalenceSarifRenderer
            renderer = EquivalenceSarifRenderer()
            return renderer.export(result, output_path)
        except (ImportError, AttributeError):
            return output_path

    # -- Stage timing ------------------------------------------------------

    def _stage_start(self, name: str) -> None:
        self._stages[f"_start_{name}"] = time.monotonic()
        if self._hooks.on_stage_start:
            self._hooks.on_stage_start(name)

    def _stage_end(self, name: str) -> None:
        start_key = f"_start_{name}"
        if start_key in self._stages:
            elapsed = time.monotonic() - self._stages.pop(start_key)
            self._stages[name] = elapsed
            if self._hooks.on_stage_end:
                self._hooks.on_stage_end(name, elapsed)
