"""Persistent section cache for workspace incremental analysis."""

from __future__ import annotations

import hashlib
import pickle
import threading
import time
from collections import OrderedDict
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional

from deppy.incremental.models import SectionSnapshot
from deppy.pipeline import PipelineResult


@dataclass(frozen=True)
class CacheKey:
    """Content-addressed cache key for a module result."""

    module_path: str
    source_hash: str


@dataclass(frozen=True)
class CachedSectionRecord:
    """A persisted module result and its normalized snapshot."""

    key: CacheKey
    snapshot: SectionSnapshot
    result: PipelineResult
    updated_at: float


class SectionCache:
    """Memory + disk cache for per-module pipeline results."""

    def __init__(
        self,
        cache_dir: Path,
        *,
        persist: bool,
        max_entries: int = 5000,
    ) -> None:
        self._cache_dir = cache_dir
        self._persist = persist
        self._max_entries = max_entries
        self._cache: "OrderedDict[str, CachedSectionRecord]" = OrderedDict()
        self._warnings: List[str] = []
        self._lock = threading.RLock()
        if self._persist:
            self._cache_dir.mkdir(parents=True, exist_ok=True)

    def _record_path(self, module_path: str) -> Path:
        digest = hashlib.sha256(module_path.encode("utf-8")).hexdigest()
        return self._cache_dir / f"{digest}.pkl"

    def get(self, module_path: str, source_hash: str) -> Optional[CachedSectionRecord]:
        """Return a cache record when the source hash still matches."""
        with self._lock:
            record = self._cache.get(module_path)
            if record is None and self._persist:
                record = self._load_from_disk(module_path)
            if record is None:
                return None
            if record.key.source_hash != source_hash:
                return None
            self._cache.move_to_end(module_path)
            return record

    def put(self, record: CachedSectionRecord) -> None:
        """Store or update a cache entry."""
        with self._lock:
            self._cache[record.key.module_path] = record
            self._cache.move_to_end(record.key.module_path)
            while len(self._cache) > self._max_entries:
                self._cache.popitem(last=False)
            if self._persist:
                self._write_to_disk(record)

    def invalidate(self, module_path: str) -> None:
        """Remove a cached module entry from memory and disk."""
        with self._lock:
            self._cache.pop(module_path, None)
            if self._persist:
                record_path = self._record_path(module_path)
                try:
                    if record_path.exists():
                        record_path.unlink()
                except OSError as exc:
                    self._warnings.append(
                        f"Could not remove cache entry for {module_path}: {exc}"
                    )

    def clear(self) -> None:
        """Clear the cache."""
        with self._lock:
            self._cache.clear()
            if self._persist and self._cache_dir.exists():
                for path in self._cache_dir.glob("*.pkl"):
                    try:
                        path.unlink()
                    except OSError as exc:
                        self._warnings.append(f"Could not remove cache file {path}: {exc}")

    def make_record(
        self,
        *,
        module_path: str,
        source_hash: str,
        snapshot: SectionSnapshot,
        result: PipelineResult,
    ) -> CachedSectionRecord:
        return CachedSectionRecord(
            key=CacheKey(module_path=module_path, source_hash=source_hash),
            snapshot=snapshot,
            result=result,
            updated_at=time.time(),
        )

    def drain_warnings(self) -> tuple[str, ...]:
        with self._lock:
            warnings = tuple(self._warnings)
            self._warnings.clear()
            return warnings

    def _load_from_disk(self, module_path: str) -> Optional[CachedSectionRecord]:
        record_path = self._record_path(module_path)
        if not record_path.exists():
            return None
        try:
            with record_path.open("rb") as handle:
                loaded = pickle.load(handle)
            if not isinstance(loaded, CachedSectionRecord):
                raise TypeError(f"Unexpected cache payload type: {type(loaded)!r}")
            self._cache[module_path] = loaded
            self._cache.move_to_end(module_path)
            return loaded
        except Exception as exc:
            self._warnings.append(
                f"Ignoring corrupt incremental cache entry for {module_path}: {exc}"
            )
            try:
                record_path.unlink(missing_ok=True)
            except OSError:
                pass
            return None

    def _write_to_disk(self, record: CachedSectionRecord) -> None:
        record_path = self._record_path(record.key.module_path)
        tmp_path = record_path.with_suffix(".tmp")
        try:
            with tmp_path.open("wb") as handle:
                pickle.dump(record, handle, protocol=pickle.HIGHEST_PROTOCOL)
            tmp_path.replace(record_path)
        except Exception as exc:
            self._warnings.append(
                f"Could not persist incremental cache entry for {record.key.module_path}: {exc}"
            )
            try:
                tmp_path.unlink(missing_ok=True)
            except OSError:
                pass
