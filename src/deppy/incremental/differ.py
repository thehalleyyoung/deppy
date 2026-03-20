"""Dependency-aware differ for workspace incremental analysis."""

from __future__ import annotations

import importlib
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

from deppy.incremental.models import ChangeNotice, ImpactSet
from deppy.incremental.section_cache import CachedSectionRecord
from deppy.render.incremental_verify import plan_incremental_reverify


@dataclass(frozen=True)
class AffectedStalk:
    """A stalk or site deemed affected by a change."""

    module_path: str
    site_id: str
    rationale: str


class WorkspaceDiffer:
    """Computes transitive impact sets for file changes."""

    def __init__(self, root: Path) -> None:
        self._root = root

    def compute_impact_set(
        self,
        changes: Sequence[ChangeNotice],
        records: Mapping[str, CachedSectionRecord],
    ) -> ImpactSet:
        if not changes:
            return ImpactSet(
                changed_files=(),
                affected_modules=(),
                affected_sites=(),
                requires_full_reanalysis=False,
                rationale=("No pending changes.",),
            )

        module_name_index = {
            record.snapshot.module_name: module_path
            for module_path, record in records.items()
        }
        reverse_graph = self._build_reverse_import_graph(records, module_name_index)
        changed_paths = {self._normalize_path(change.path) for change in changes}
        affected_modules: Set[str] = set()
        affected_sites: Set[str] = set()
        rationale: List[str] = []
        precise_support = self._load_precise_affected_stalks()

        for change in changes:
            module_path = self._normalize_path(change.path)
            affected_modules.add(module_path)
            record = records.get(module_path)
            precise_sites = self._precise_sites_for_change(
                record=record,
                change=change,
                precise_support=precise_support,
            )
            if precise_sites:
                affected_sites.update(site.site_id for site in precise_sites)
                rationale.extend(site.rationale for site in precise_sites)
            elif change.changed_lines:
                rationale.append(
                    f"No precise site mapping for {Path(module_path).name}; using module-level invalidation."
                )

            queue = list(reverse_graph.get(module_path, ()))
            while queue:
                dependent = queue.pop(0)
                if dependent in affected_modules:
                    continue
                affected_modules.add(dependent)
                dependent_record = records.get(dependent)
                if dependent_record is not None:
                    affected_sites.update(dependent_record.snapshot.module_summary_sites)
                queue.extend(reverse_graph.get(dependent, ()))

        if precise_support is None:
            rationale.append(
                "deppy.cover.affected_stalks unavailable; using locality + import-graph propagation."
            )

        return ImpactSet(
            changed_files=tuple(sorted(self._relativeize(path) for path in changed_paths)),
            affected_modules=tuple(sorted(self._relativeize(path) for path in affected_modules)),
            affected_sites=tuple(sorted(affected_sites)),
            requires_full_reanalysis=False,
            rationale=tuple(dict.fromkeys(rationale)),
        )

    def _build_reverse_import_graph(
        self,
        records: Mapping[str, CachedSectionRecord],
        module_name_index: Mapping[str, str],
    ) -> Dict[str, Set[str]]:
        reverse: Dict[str, Set[str]] = {}
        for module_path, record in records.items():
            for imported_name in record.snapshot.imports:
                resolved = self._resolve_local_import(imported_name, module_name_index)
                if resolved is None:
                    continue
                reverse.setdefault(resolved, set()).add(module_path)
        return reverse

    def _resolve_local_import(
        self,
        import_name: str,
        module_name_index: Mapping[str, str],
    ) -> Optional[str]:
        cleaned = import_name.strip(".")
        if not cleaned:
            return None
        candidate = cleaned
        while candidate:
            if candidate in module_name_index:
                return module_name_index[candidate]
            if "." not in candidate:
                break
            candidate = candidate.rsplit(".", 1)[0]
        return None

    def _precise_sites_for_change(
        self,
        *,
        record: Optional[CachedSectionRecord],
        change: ChangeNotice,
        precise_support: Optional[object],
    ) -> Tuple[AffectedStalk, ...]:
        if record is None or not change.changed_lines:
            return ()

        site_ids: Set[str] = set()
        rationales: List[str] = []

        if callable(precise_support):
            try:
                precise_result = precise_support(record.result.cover, changed_lines=set(change.changed_lines))
            except TypeError:
                try:
                    precise_result = precise_support(record.result.cover, set(change.changed_lines))
                except Exception:
                    precise_result = None
            except Exception:
                precise_result = None
            if precise_result:
                precise_items = getattr(precise_result, "stalks", precise_result)
                for stalk in precise_items:
                    site_text = str(getattr(stalk, "site_id", stalk))
                    site_ids.add(site_text)
                if site_ids:
                    rationales.append(
                        f"Precise affected_stalks marked {len(site_ids)} site(s) in {record.snapshot.relative_path}."
                    )

        locality_sites = self._locality_sites(record, change.changed_lines)
        site_ids.update(locality_sites)
        if locality_sites:
            rationales.append(
                f"Locality planner marked {len(locality_sites)} site(s) in {record.snapshot.relative_path}."
            )

        if not site_ids:
            site_ids.update(record.snapshot.module_summary_sites)
            if record.snapshot.module_summary_sites:
                rationales.append(
                    f"Falling back to module-summary invalidation for {record.snapshot.relative_path}."
                )

        return tuple(
            AffectedStalk(
                module_path=record.key.module_path,
                site_id=site_id,
                rationale=rationales[0] if rationales else "Affected by change.",
            )
            for site_id in sorted(site_ids)
        )

    def _locality_sites(
        self,
        record: CachedSectionRecord,
        changed_lines: Sequence[int],
    ) -> Set[str]:
        cover = record.result.cover
        if cover is None or not getattr(cover, "sites", None):
            return set()

        ordered_site_ids = tuple(sorted(cover.sites.keys(), key=str))
        overlaps: Dict[int, Set[int]] = {index: set() for index in range(len(ordered_site_ids))}
        index_for_site = {site_id: index for index, site_id in enumerate(ordered_site_ids)}
        for left, right in getattr(cover, "overlaps", ()):
            if left in index_for_site and right in index_for_site:
                li = index_for_site[left]
                ri = index_for_site[right]
                overlaps.setdefault(li, set()).add(ri)
                overlaps.setdefault(ri, set()).add(li)

        adapter_sites = []
        adapter_paths = []
        for index, site_id in enumerate(ordered_site_ids):
            adapter_sites.append(SimpleNamespace(path_idx=index, conjunct_idx=index))
            source_location = getattr(site_id, "source_location", None)
            if (
                isinstance(source_location, tuple)
                and len(source_location) >= 2
                and isinstance(source_location[1], int)
            ):
                line = source_location[1]
                adapter_paths.append(SimpleNamespace(line_range=(line, line), conditions=()))
            else:
                adapter_paths.append(SimpleNamespace(line_range=(), conditions=()))

        adapter_result = SimpleNamespace(
            cover=SimpleNamespace(sites=adapter_sites, overlap_graph=overlaps),
            vc_results=list(range(len(adapter_sites))),
            spec_decomposition=None,
            impl_analysis=SimpleNamespace(paths=adapter_paths),
        )

        try:
            plan = plan_incremental_reverify(adapter_result, set(changed_lines))
        except Exception:
            return set()
        return {
            str(ordered_site_ids[index])
            for index in plan.recheck_vcs
            if 0 <= index < len(ordered_site_ids)
        }

    @staticmethod
    def _load_precise_affected_stalks() -> Optional[object]:
        try:
            module = importlib.import_module("deppy.cover")
        except Exception:
            return None
        return getattr(module, "affected_stalks", None)

    def _normalize_path(self, path: str) -> str:
        candidate = Path(path)
        if not candidate.is_absolute():
            candidate = self._root / candidate
        return str(candidate.resolve())

    def _relativeize(self, path: str) -> str:
        try:
            return str(Path(path).resolve().relative_to(self._root))
        except ValueError:
            return str(Path(path).resolve())


def compute_impact_set(
    *,
    root: Path,
    changes: Sequence[ChangeNotice],
    records: Mapping[str, CachedSectionRecord],
) -> ImpactSet:
    """Convenience wrapper for computing workspace impact."""
    differ = WorkspaceDiffer(root)
    return differ.compute_impact_set(changes, records)
