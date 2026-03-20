"""Workspace orchestration for incremental project analysis."""

from __future__ import annotations

import hashlib
from pathlib import Path
from typing import Dict, Iterable, Optional

from deppy.incremental.differ import WorkspaceDiffer
from deppy.incremental.models import (
    ChangeNotice,
    IncrementalAnalysisReport,
    WorkspaceConfig,
    WorkspaceConfigurationError,
)
from deppy.incremental.propagator import IncrementalPropagator
from deppy.incremental.section_cache import CachedSectionRecord, SectionCache


def _compute_content_hash(path: Path) -> Optional[str]:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()[:16]
    except OSError:
        return None


class Workspace:
    """A project-tree view that supports full and incremental analysis."""

    def __init__(
        self,
        root: str | Path,
        config: Optional[WorkspaceConfig] = None,
        *,
        incremental=None,
        persist_cache: Optional[bool] = None,
        cache_dir: Optional[str] = None,
    ) -> None:
        root_path = Path(root).expanduser().resolve()
        if not root_path.exists() or not root_path.is_dir():
            raise WorkspaceConfigurationError(f"Workspace root does not exist: {root_path}")

        if config is None:
            if incremental is None:
                from deppy.pipeline import IncrementalConfig, IncrementalStrategy

                incremental = IncrementalConfig(
                    _strategy=IncrementalStrategy.FUNCTION_LEVEL,
                    _persist_between_runs=bool(persist_cache),
                    _cache_dir=cache_dir,
                )
            config = WorkspaceConfig(
                root=str(root_path),
                incremental=incremental,
                persist_cache=bool(
                    incremental.persist_between_runs if persist_cache is None else persist_cache
                ),
                cache_dir=cache_dir,
            )

        self._config = config
        self._root = config.root_path
        self._cache = SectionCache(
            config.effective_cache_dir,
            persist=config.persist_cache or config.incremental.persist_between_runs,
            max_entries=config.incremental.max_cache_entries,
        )
        self._differ = WorkspaceDiffer(self._root)
        self._propagator = IncrementalPropagator(config, self._cache)
        self._records: Dict[str, CachedSectionRecord] = {}
        self._pending_changes: Dict[str, ChangeNotice] = {}
        self._last_report: Optional[IncrementalAnalysisReport] = None

    @property
    def config(self) -> WorkspaceConfig:
        return self._config

    def analyze(self) -> IncrementalAnalysisReport:
        """Analyze the full workspace, reusing valid persisted module results."""
        files = self._discover_python_files()
        self._hydrate_records(files)
        dirty_modules = {
            str(path.resolve())
            for path in files
            if str(path.resolve()) not in self._records
        }
        run = self._propagator.run(
            all_files=files,
            dirty_modules=dirty_modules,
            records=self._records,
            changes={},
        )
        report = IncrementalAnalysisReport.from_snapshots(
            full_result=run.full_result,
            updated_modules=run.updated_modules,
            reused_modules=run.reused_modules,
            diagnostics=run.full_result.diagnostics,
            warnings=run.warnings,
            errors=run.errors,
            impact_set=None,
            module_snapshots={path: record.snapshot for path, record in run.records.items()},
        )
        self._last_report = report
        return report

    def notify_change(
        self,
        path: str | Path,
        changed_lines: Optional[Iterable[int]] = None,
    ) -> ChangeNotice:
        """Record a file change to be processed by ``reanalyze``."""
        absolute = self._resolve_workspace_path(path)
        content_hash = _compute_content_hash(Path(absolute))
        notice = ChangeNotice(
            path=absolute,
            changed_lines=tuple(changed_lines or ()),
            content_hash=content_hash,
        )
        self._pending_changes[absolute] = notice
        return notice

    def reanalyze(self) -> IncrementalAnalysisReport:
        """Incrementally reanalyze the workspace after queued changes."""
        if not self._records:
            return self.analyze()

        files = self._discover_python_files()
        self._hydrate_records(files)

        for missing in set(self._records) - {str(path.resolve()) for path in files}:
            self._pending_changes.setdefault(
                missing,
                ChangeNotice(path=missing, changed_lines=(), content_hash=None),
            )

        impact_set = self._differ.compute_impact_set(
            list(self._pending_changes.values()),
            self._records,
        )

        if impact_set.requires_full_reanalysis:
            dirty_modules = {str(path.resolve()) for path in files}
        else:
            dirty_modules = {
                str((self._root / relative).resolve())
                for relative in impact_set.affected_modules
                if (self._root / relative).exists()
            }

        run = self._propagator.run(
            all_files=files,
            dirty_modules=dirty_modules,
            records=self._records,
            changes=self._pending_changes,
        )
        report = IncrementalAnalysisReport.from_snapshots(
            full_result=run.full_result,
            updated_modules=run.updated_modules,
            reused_modules=run.reused_modules,
            diagnostics=run.full_result.diagnostics,
            warnings=tuple(run.warnings) + impact_set.rationale,
            errors=run.errors,
            impact_set=impact_set,
            module_snapshots={path: record.snapshot for path, record in run.records.items()},
        )
        self._pending_changes.clear()
        self._last_report = report
        return report

    def _discover_python_files(self) -> list[Path]:
        files = []
        cache_dir = self._config.effective_cache_dir
        for path in self._root.rglob("*.py"):
            if "__pycache__" in path.parts:
                continue
            if path.is_relative_to(cache_dir):
                continue
            files.append(path.resolve())
        return sorted(files)

    def _hydrate_records(self, files: Iterable[Path]) -> None:
        current_paths = {str(path.resolve()) for path in files}
        for stale_path in set(self._records) - current_paths:
            self._records.pop(stale_path, None)

        for file_path in files:
            absolute = str(file_path.resolve())
            content_hash = _compute_content_hash(file_path)
            if content_hash is None:
                continue
            record = self._cache.get(absolute, content_hash)
            if record is not None:
                self._records[absolute] = record

    def _resolve_workspace_path(self, path: str | Path) -> str:
        candidate = Path(path)
        if not candidate.is_absolute():
            candidate = self._root / candidate
        absolute = candidate.resolve()
        try:
            absolute.relative_to(self._root)
        except ValueError as exc:
            raise WorkspaceConfigurationError(
                f"Path is outside workspace root: {absolute}"
            ) from exc
        return str(absolute)
