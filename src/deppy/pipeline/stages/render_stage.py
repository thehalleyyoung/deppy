"""Rendering stage for the sheaf-descent analysis pipeline.

Stage 5: Generate diagnostics and contracts from the synthesis results.
Produces human-readable diagnostics, machine-readable diagnostics, and
contract annotations.
"""

from __future__ import annotations

import enum
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
from deppy.pipeline.pipeline_config import PipelineConfig
from deppy.pipeline.stage_registry import Stage, StageMetadata
from deppy.pipeline.stages.cover_stage import CoverResult
from deppy.pipeline.stages.synthesis_stage import SynthesisResult


# ===================================================================
#  Diagnostic types
# ===================================================================


class DiagnosticSeverity(enum.Enum):
    """Severity levels for diagnostics."""

    ERROR = "error"
    WARNING = "warning"
    INFO = "info"
    HINT = "hint"


@dataclass(frozen=True)
class DiagnosticLocation:
    """Location of a diagnostic in source code."""

    _file: str
    _line: int
    _col: int
    _end_line: Optional[int] = None
    _end_col: Optional[int] = None

    @property
    def file(self) -> str:
        return self._file

    @property
    def line(self) -> int:
        return self._line

    @property
    def col(self) -> int:
        return self._col

    @property
    def end_line(self) -> Optional[int]:
        return self._end_line

    @property
    def end_col(self) -> Optional[int]:
        return self._end_col

    def pretty(self) -> str:
        loc = f"{self._file}:{self._line}:{self._col}"
        if self._end_line is not None:
            loc += f"-{self._end_line}"
        return loc


@dataclass(frozen=True)
class Diagnostic:
    """A diagnostic message from the analysis."""

    _severity: DiagnosticSeverity
    _message: str
    _location: Optional[DiagnosticLocation] = None
    _code: str = ""
    _site_id: Optional[SiteId] = None
    _suggestion: Optional[str] = None
    _related: Tuple[DiagnosticLocation, ...] = ()

    @property
    def severity(self) -> DiagnosticSeverity:
        return self._severity

    @property
    def message(self) -> str:
        return self._message

    @property
    def location(self) -> Optional[DiagnosticLocation]:
        return self._location

    @property
    def code(self) -> str:
        return self._code

    @property
    def site_id(self) -> Optional[SiteId]:
        return self._site_id

    @property
    def suggestion(self) -> Optional[str]:
        return self._suggestion

    @property
    def related(self) -> Tuple[DiagnosticLocation, ...]:
        return self._related

    def pretty(self) -> str:
        parts: List[str] = []
        if self._location:
            parts.append(self._location.pretty())
        parts.append(f"[{self._severity.value}]")
        if self._code:
            parts.append(f"({self._code})")
        parts.append(self._message)
        result = " ".join(parts)
        if self._suggestion:
            result += f"\n  Suggestion: {self._suggestion}"
        return result


@dataclass(frozen=True)
class ContractAnnotation:
    """A generated contract annotation for a function scope."""

    _scope_name: str
    _kind: str  # "requires", "ensures", "invariant"
    _predicate_text: str
    _variable: Optional[str] = None
    _trust: TrustLevel = TrustLevel.TRUSTED_AUTO
    _source_sites: Tuple[SiteId, ...] = ()

    @property
    def scope_name(self) -> str:
        return self._scope_name

    @property
    def kind(self) -> str:
        return self._kind

    @property
    def predicate_text(self) -> str:
        return self._predicate_text

    @property
    def variable(self) -> Optional[str]:
        return self._variable

    @property
    def trust(self) -> TrustLevel:
        return self._trust

    @property
    def source_sites(self) -> Tuple[SiteId, ...]:
        return self._source_sites

    def to_decorator_string(self) -> str:
        """Render as a Python decorator string."""
        if self._variable:
            return f"@{self._kind}(lambda {self._variable}: {self._predicate_text})"
        return f"@{self._kind}({self._predicate_text!r})"


# ===================================================================
#  Render result
# ===================================================================


@dataclass(frozen=True)
class RenderResult:
    """Result of the rendering stage."""

    _diagnostics: Tuple[Diagnostic, ...]
    _contracts: Tuple[ContractAnnotation, ...]
    _error_count: int = 0
    _warning_count: int = 0
    _info_count: int = 0

    @property
    def diagnostics(self) -> Tuple[Diagnostic, ...]:
        return self._diagnostics

    @property
    def contracts(self) -> Tuple[ContractAnnotation, ...]:
        return self._contracts

    @property
    def error_count(self) -> int:
        return self._error_count

    @property
    def warning_count(self) -> int:
        return self._warning_count

    @property
    def info_count(self) -> int:
        return self._info_count

    @property
    def has_errors(self) -> bool:
        return self._error_count > 0

    def diagnostics_by_severity(
        self, severity: DiagnosticSeverity
    ) -> Tuple[Diagnostic, ...]:
        return tuple(d for d in self._diagnostics if d.severity == severity)

    def diagnostics_for_file(self, file_path: str) -> Tuple[Diagnostic, ...]:
        return tuple(
            d for d in self._diagnostics
            if d.location is not None and d.location.file == file_path
        )


# ===================================================================
#  Rendering engine
# ===================================================================


class _RenderEngine:
    """Generates diagnostics and contracts from synthesis results."""

    def __init__(self, config: PipelineConfig) -> None:
        self._config = config

    def render(
        self,
        cover_result: CoverResult,
        synthesis_result: SynthesisResult,
    ) -> RenderResult:
        """Generate diagnostics and contracts."""
        diagnostics: List[Diagnostic] = []
        contracts: List[ContractAnnotation] = []

        # Generate obstruction diagnostics
        if self._config.emit_diagnostics:
            obstruction_diags = self._render_obstructions(
                synthesis_result.obstructions
            )
            diagnostics.extend(obstruction_diags)

            # Generate convergence diagnostics
            conv_diags = self._render_convergence(synthesis_result.convergence)
            diagnostics.extend(conv_diags)

            # Generate unsolved-site diagnostics
            unsolved_diags = self._render_unsolved_sites(
                synthesis_result.sections, cover_result.cover
            )
            diagnostics.extend(unsolved_diags)

        # Generate contract annotations
        if self._config.emit_contracts:
            generated_contracts = self._generate_contracts(
                synthesis_result.sections, cover_result
            )
            contracts.extend(generated_contracts)

        error_count = sum(
            1 for d in diagnostics if d.severity == DiagnosticSeverity.ERROR
        )
        warning_count = sum(
            1 for d in diagnostics if d.severity == DiagnosticSeverity.WARNING
        )
        info_count = sum(
            1 for d in diagnostics if d.severity == DiagnosticSeverity.INFO
        )

        return RenderResult(
            _diagnostics=tuple(diagnostics),
            _contracts=tuple(contracts),
            _error_count=error_count,
            _warning_count=warning_count,
            _info_count=info_count,
        )

    def _render_obstructions(
        self,
        obstructions: Tuple[ObstructionData, ...],
    ) -> List[Diagnostic]:
        """Render obstructions as error diagnostics."""
        diagnostics: List[Diagnostic] = []

        for obs in obstructions:
            if obs.is_trivial:
                continue

            location = None
            if obs.conflicting_overlaps:
                site_a, site_b = obs.conflicting_overlaps[0]
                if site_a.source_location:
                    file, line, col = site_a.source_location
                    location = DiagnosticLocation(
                        _file=str(file),
                        _line=int(line),
                        _col=int(col),
                    )

            related: List[DiagnosticLocation] = []
            for site_a, site_b in obs.conflicting_overlaps:
                if site_b.source_location:
                    file, line, col = site_b.source_location
                    related.append(DiagnosticLocation(
                        _file=str(file),
                        _line=int(line),
                        _col=int(col),
                    ))

            diagnostics.append(Diagnostic(
                _severity=DiagnosticSeverity.ERROR,
                _message=obs.explanation or "Type incompatibility detected (H^1 obstruction)",
                _location=location,
                _code="SHEAF001",
                _related=tuple(related),
            ))

        return diagnostics

    def _render_convergence(self, convergence: Any) -> List[Diagnostic]:
        """Render convergence warnings."""
        diagnostics: List[Diagnostic] = []

        if not convergence.converged:
            diagnostics.append(Diagnostic(
                _severity=DiagnosticSeverity.WARNING,
                _message=(
                    f"Analysis did not converge after {convergence.iterations_used} "
                    f"iterations (max: {convergence.max_iterations}). "
                    f"Results may be incomplete."
                ),
                _code="SHEAF002",
            ))

        return diagnostics

    def _render_unsolved_sites(
        self,
        sections: Dict[SiteId, LocalSection],
        cover: Cover,
    ) -> List[Diagnostic]:
        """Render diagnostics for sites with residual trust."""
        diagnostics: List[Diagnostic] = []

        for site_id, section in sections.items():
            if section.trust == TrustLevel.RESIDUAL and site_id not in cover.error_sites:
                location = None
                if site_id.source_location:
                    file, line, col = site_id.source_location
                    location = DiagnosticLocation(
                        _file=str(file),
                        _line=int(line),
                        _col=int(col),
                    )
                diagnostics.append(Diagnostic(
                    _severity=DiagnosticSeverity.INFO,
                    _message=f"Site {site_id.name} has residual trust (no solver could handle it)",
                    _location=location,
                    _code="SHEAF003",
                    _site_id=site_id,
                    _suggestion="Add a type annotation or contract to guide the analysis",
                ))

        return diagnostics

    def _generate_contracts(
        self,
        sections: Dict[SiteId, LocalSection],
        cover_result: CoverResult,
    ) -> List[ContractAnnotation]:
        """Generate contract annotations from solved sections."""
        contracts: List[ContractAnnotation] = []
        scope_contracts: Dict[str, List[ContractAnnotation]] = {}

        for site_id, section in sections.items():
            if not section.refinements:
                continue
            if section.trust == TrustLevel.RESIDUAL:
                continue

            scope_name = cover_result.site_scope_map.get(site_id, "")
            if not scope_name:
                continue

            # Generate requires for input boundary sites
            if site_id.kind == SiteKind.ARGUMENT_BOUNDARY:
                for key, value in section.refinements.items():
                    if key.startswith("_") or key in ("guard_source", "guard_kind"):
                        continue
                    contract = ContractAnnotation(
                        _scope_name=scope_name,
                        _kind="requires",
                        _predicate_text=f"{key}: {value!r}",
                        _variable=key if key.isidentifier() else None,
                        _trust=section.trust,
                        _source_sites=(site_id,),
                    )
                    contracts.append(contract)

            # Generate ensures for output boundary sites
            elif site_id.kind == SiteKind.RETURN_OUTPUT_BOUNDARY:
                for key, value in section.refinements.items():
                    if key.startswith("_") or key in ("guard_source", "guard_kind"):
                        continue
                    contract = ContractAnnotation(
                        _scope_name=scope_name,
                        _kind="ensures",
                        _predicate_text=f"{key}: {value!r}",
                        _trust=section.trust,
                        _source_sites=(site_id,),
                    )
                    contracts.append(contract)

            # Generate invariants for loop-header sites
            elif site_id.kind == SiteKind.LOOP_HEADER_INVARIANT:
                for key, value in section.refinements.items():
                    if key.startswith("_") or key in ("guard_source", "guard_kind"):
                        continue
                    contract = ContractAnnotation(
                        _scope_name=scope_name,
                        _kind="invariant",
                        _predicate_text=f"{key}: {value!r}",
                        _trust=section.trust,
                        _source_sites=(site_id,),
                    )
                    contracts.append(contract)

        return contracts


# ===================================================================
#  RenderStage
# ===================================================================


class RenderStage(Stage):
    """Stage 5: Render diagnostics and contracts.

    Produces human-readable diagnostics from obstructions and unsolved
    sites, and generates contract annotations for well-typed scopes.
    """

    def metadata(self) -> StageMetadata:
        return StageMetadata(
            _name="render",
            _description="Generate diagnostics and contract annotations",
            _dependencies=frozenset({"cover", "synthesis"}),
            _order_hint=50,
        )

    def run(self, context: Dict[str, Any], config: PipelineConfig) -> RenderResult:
        """Execute rendering.

        Expects context to contain:
        - ``cover``: CoverResult
        - ``synthesis``: SynthesisResult
        """
        cover_result: CoverResult = context.get("cover")  # type: ignore[assignment]
        synthesis_result: SynthesisResult = context.get("synthesis")  # type: ignore[assignment]

        if cover_result is None or synthesis_result is None:
            return RenderResult(
                _diagnostics=(),
                _contracts=(),
            )

        engine = _RenderEngine(config)
        return engine.render(cover_result, synthesis_result)
