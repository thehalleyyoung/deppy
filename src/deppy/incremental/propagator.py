"""Selective re-execution over workspace module caches."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, Mapping, MutableMapping, Optional, Sequence, Set

from deppy.core._protocols import Cover
from deppy.incremental.models import ChangeNotice, SectionSnapshot, WorkspaceConfig
from deppy.incremental.section_cache import CachedSectionRecord, SectionCache
from deppy.pipeline import AnalysisPipeline, PipelineConfig, PipelineResult


def _compute_source_hash(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()[:16]
    except OSError:
        return ""


@dataclass(frozen=True)
class PropagatorRunReport:
    """Detailed result of a propagation pass."""

    full_result: PipelineResult
    updated_modules: tuple[str, ...]
    reused_modules: tuple[str, ...]
    warnings: tuple[str, ...]
    errors: tuple[str, ...]
    records: Dict[str, CachedSectionRecord]


class IncrementalPropagator:
    """Reuses unchanged module results and selectively reruns dirty files."""

    def __init__(self, config: WorkspaceConfig, cache: SectionCache) -> None:
        self._config = config
        self._cache = cache

    def run(
        self,
        *,
        all_files: Sequence[Path],
        dirty_modules: Set[str],
        records: MutableMapping[str, CachedSectionRecord],
        changes: Mapping[str, ChangeNotice],
    ) -> PropagatorRunReport:
        pipeline_config = PipelineConfig(_incremental=self._config.incremental)
        pipeline = AnalysisPipeline(pipeline_config)

        current_paths = {str(path.resolve()) for path in all_files}
        warnings = list(self._cache.drain_warnings())
        errors = []
        updated_modules = set()
        reused_modules = set()

        for cached_path in list(records):
            if cached_path not in current_paths:
                records.pop(cached_path, None)
                self._cache.invalidate(cached_path)

        for file_path in sorted(all_files):
            absolute = str(file_path.resolve())
            if absolute not in dirty_modules and absolute in records:
                reused_modules.add(self._relativeize(file_path))
                continue

            notice = changes.get(absolute)
            result = pipeline.run_incremental(
                absolute,
                changed_lines=set(notice.changed_lines) if notice and notice.changed_lines else None,
            )
            snapshot = SectionSnapshot.from_result(
                source_path=file_path,
                root=self._config.root_path,
                result=result,
            )
            record = self._cache.make_record(
                module_path=absolute,
                source_hash=snapshot.source_hash or _compute_source_hash(file_path),
                snapshot=snapshot,
                result=result,
            )
            records[absolute] = record
            self._cache.put(record)
            warnings.extend(self._cache.drain_warnings())
            updated_modules.add(self._relativeize(file_path))
            if result.errors:
                errors.extend(result.errors)

        full_result = self._aggregate_pipeline_results(records.values())
        return PropagatorRunReport(
            full_result=full_result,
            updated_modules=tuple(sorted(updated_modules)),
            reused_modules=tuple(sorted(reused_modules)),
            warnings=tuple(warnings),
            errors=tuple(errors),
            records=dict(records),
        )

    def _aggregate_pipeline_results(
        self,
        records: Iterable[CachedSectionRecord],
    ) -> PipelineResult:
        merged_cover = Cover()
        sections = {}
        obstructions = []
        diagnostics = []
        contracts = []
        warnings = []
        errors = []
        success = True
        have_cover = False

        for record in records:
            result = record.result
            if result.cover is not None:
                have_cover = True
                merged_cover.sites.update(result.cover.sites)
                merged_cover.morphisms.extend(result.cover.morphisms)
                merged_cover.overlaps.extend(result.cover.overlaps)
                merged_cover.error_sites.update(result.cover.error_sites)
                merged_cover.input_boundary.update(result.cover.input_boundary)
                merged_cover.output_boundary.update(result.cover.output_boundary)
            sections.update(result.sections)
            obstructions.extend(result.obstructions)
            diagnostics.extend(result.diagnostics)
            contracts.extend(result.contracts)
            warnings.extend(result.warnings)
            errors.extend(result.errors)
            success = success and result.success

        return PipelineResult(
            _cover=merged_cover if have_cover else None,
            _sections=sections,
            _obstructions=tuple(obstructions),
            _diagnostics=tuple(diagnostics),
            _contracts=tuple(contracts),
            _timing=None,
            _convergence=None,
            _ir_module=None,
            _success=success and not errors,
            _errors=tuple(errors),
            _warnings=tuple(warnings),
        )

    def _relativeize(self, path: Path) -> str:
        return str(path.resolve().relative_to(self._config.root_path))
