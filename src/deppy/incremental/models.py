"""Immutable models for workspace-level incremental analysis."""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, Mapping, Optional, Tuple

from deppy.pipeline import IncrementalConfig, IncrementalStrategy, PipelineResult
from deppy.pipeline.stages.render_stage import Diagnostic


class WorkspaceConfigurationError(ValueError):
    """Raised for invalid workspace configuration or path usage."""


def _normalize_lines(lines: Iterable[int]) -> Tuple[int, ...]:
    return tuple(sorted({line for line in lines if line > 0}))


def _module_name_from_path(path: Path, root: Path) -> str:
    relative = path.relative_to(root)
    parts = list(relative.parts)
    if parts[-1] == "__init__.py":
        parts = parts[:-1]
    else:
        parts[-1] = Path(parts[-1]).stem
    return ".".join(part for part in parts if part)


def _scope_name(scope: object) -> str:
    qualified_name = getattr(scope, "qualified_name", None)
    if isinstance(qualified_name, str) and qualified_name:
        return qualified_name
    name = getattr(scope, "name", "")
    return name if isinstance(name, str) else ""


@dataclass(frozen=True)
class WorkspaceConfig:
    """Workspace configuration for incremental project analysis."""

    root: str
    incremental: IncrementalConfig = field(
        default_factory=lambda: IncrementalConfig(
            _strategy=IncrementalStrategy.FUNCTION_LEVEL,
        )
    )
    persist_cache: bool = False
    theory_packs: Tuple[str, ...] = ()
    cache_dir: Optional[str] = None

    def __post_init__(self) -> None:
        if not self.root:
            raise WorkspaceConfigurationError("Workspace root must be non-empty.")

    @property
    def root_path(self) -> Path:
        return Path(self.root).expanduser().resolve()

    @property
    def effective_cache_dir(self) -> Path:
        if self.cache_dir:
            return Path(self.cache_dir).expanduser().resolve()
        if self.incremental.cache_dir:
            cache_dir = Path(self.incremental.cache_dir).expanduser()
            if cache_dir.is_absolute():
                return cache_dir.resolve()
            return (self.root_path / cache_dir).resolve()
        return (self.root_path / ".deppy_incremental_cache").resolve()


@dataclass(frozen=True)
class ChangeNotice:
    """A filesystem change observed by the workspace."""

    path: str
    changed_lines: Tuple[int, ...] = ()
    content_hash: Optional[str] = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "changed_lines", _normalize_lines(self.changed_lines))


@dataclass(frozen=True)
class ImpactSet:
    """Computed transitive impact of a batch of changes."""

    changed_files: Tuple[str, ...]
    affected_modules: Tuple[str, ...]
    affected_sites: Tuple[str, ...]
    requires_full_reanalysis: bool
    rationale: Tuple[str, ...] = ()


@dataclass(frozen=True)
class SectionSnapshot:
    """Serializable summary of a module analysis result."""

    module_name: str
    source_path: str
    relative_path: str
    source_hash: str
    imports: Tuple[str, ...]
    exported_functions: Tuple[str, ...]
    exported_classes: Tuple[str, ...]
    section_ids: Tuple[str, ...]
    module_summary_sites: Tuple[str, ...]
    diagnostics: Tuple[str, ...]
    warnings: Tuple[str, ...]
    errors: Tuple[str, ...]
    success: bool

    @classmethod
    def from_result(
        cls,
        *,
        source_path: Path,
        root: Path,
        result: PipelineResult,
    ) -> "SectionSnapshot":
        ir_module = result.ir_module
        imports: Tuple[str, ...] = ()
        exported_functions: Tuple[str, ...] = ()
        exported_classes: Tuple[str, ...] = ()
        source_hash = ""

        if ir_module is not None:
            imports = tuple(ir_module.imports)
            source_hash = ir_module.source_info.source_hash
            scopes = tuple(ir_module.scopes)
            exported_functions = tuple(
                sorted(
                    _scope_name(scope)
                    for scope in scopes
                    if getattr(scope, "kind", "") in {"function", "method", "async_function"}
                    and not _scope_name(scope).split(".")[-1].startswith("_")
                )
            )
            exported_classes = tuple(
                sorted(
                    _scope_name(scope)
                    for scope in scopes
                    if getattr(scope, "kind", "") == "class"
                    and not _scope_name(scope).split(".")[-1].startswith("_")
                )
            )

        site_ids = tuple(sorted(str(site_id) for site_id in result.sections.keys()))
        module_summary_sites = tuple(
            sorted(
                str(site_id)
                for site_id in result.sections.keys()
                if getattr(getattr(site_id, "kind", None), "name", "") == "MODULE_SUMMARY"
            )
        )
        diagnostics = tuple(sorted(diagnostic.pretty() for diagnostic in result.diagnostics))

        return cls(
            module_name=_module_name_from_path(source_path, root),
            source_path=str(source_path),
            relative_path=str(source_path.relative_to(root)),
            source_hash=source_hash,
            imports=tuple(sorted(imports)),
            exported_functions=exported_functions,
            exported_classes=exported_classes,
            section_ids=site_ids,
            module_summary_sites=module_summary_sites,
            diagnostics=diagnostics,
            warnings=tuple(result.warnings),
            errors=tuple(result.errors),
            success=result.success,
        )


@dataclass(frozen=True)
class IncrementalAnalysisReport:
    """Workspace-level result for full or incremental analysis."""

    full_result: Optional[PipelineResult]
    updated_modules: Tuple[str, ...]
    reused_modules: Tuple[str, ...]
    diagnostics: Tuple[Diagnostic, ...]
    warnings: Tuple[str, ...] = ()
    errors: Tuple[str, ...] = ()
    impact_set: Optional[ImpactSet] = None
    _module_snapshots: Tuple[Tuple[str, SectionSnapshot], ...] = ()

    @property
    def module_snapshots(self) -> Dict[str, SectionSnapshot]:
        return dict(self._module_snapshots)

    @classmethod
    def from_snapshots(
        cls,
        *,
        full_result: Optional[PipelineResult],
        updated_modules: Iterable[str],
        reused_modules: Iterable[str],
        diagnostics: Iterable[Diagnostic],
        warnings: Iterable[str],
        errors: Iterable[str],
        impact_set: Optional[ImpactSet],
        module_snapshots: Mapping[str, SectionSnapshot],
    ) -> "IncrementalAnalysisReport":
        return cls(
            full_result=full_result,
            updated_modules=tuple(sorted(updated_modules)),
            reused_modules=tuple(sorted(reused_modules)),
            diagnostics=tuple(diagnostics),
            warnings=tuple(warnings),
            errors=tuple(errors),
            impact_set=impact_set,
            _module_snapshots=tuple(sorted(module_snapshots.items())),
        )
