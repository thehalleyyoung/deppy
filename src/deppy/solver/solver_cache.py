"""Query caching and incremental solving layer.

Provides:

- **SolverCache**: A content-addressed cache that maps (formula_hash, context_hash)
  pairs to ``SolverResult`` values.  Avoids re-solving identical obligations.
- **CachedSolver**: A wrapper around any ``LocalSolverInterface`` that intercepts
  ``check`` calls and serves cached results when available.
- **IncrementalSolver**: Manages push/pop state for incremental solving, tracking
  which assertions have been made at each level.

Cache invalidation is by content hash -- if the formula or context changes,
the cache is bypassed.  The cache has a configurable maximum size and uses
LRU eviction.
"""

from __future__ import annotations

import hashlib
import logging
import threading
import time
from collections import OrderedDict
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.predicates.base import Predicate
from deppy.solver.solver_interface import (
    LocalSolverInterface,
    SolverObligation,
    SolverResult,
    SolverStatistics,
    SolverStatus,
)

logger = logging.getLogger(__name__)


# ═══════════════════════════════════════════════════════════════════════════════
# Cache key computation
# ═══════════════════════════════════════════════════════════════════════════════


def _compute_cache_key(obligation: SolverObligation) -> str:
    """Compute a deterministic cache key for an obligation.

    The key is based on:
    - The formula's string representation.
    - The context predicates' string representations.
    - (NOT the site_id or trust_level, which are metadata.)
    """
    h = hashlib.sha256()
    h.update(repr(obligation.formula).encode("utf-8"))
    for ctx in sorted(repr(c) for c in obligation.context):
        h.update(ctx.encode("utf-8"))
    return h.hexdigest()


def _compute_formula_hash(formula: Predicate) -> str:
    """Compute a hash for a single formula."""
    h = hashlib.sha256()
    h.update(repr(formula).encode("utf-8"))
    return h.hexdigest()


# ═══════════════════════════════════════════════════════════════════════════════
# Cache entry
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class CacheEntry:
    """A single cache entry."""
    key: str
    result: SolverResult
    timestamp: float
    hit_count: int = 0

    def with_hit(self) -> CacheEntry:
        """Return a copy with incremented hit count."""
        return CacheEntry(
            key=self.key,
            result=self.result,
            timestamp=self.timestamp,
            hit_count=self.hit_count + 1,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Solver cache
# ═══════════════════════════════════════════════════════════════════════════════


class SolverCache:
    """Content-addressed cache for solver results.

    Thread-safe via a reentrant lock.

    Attributes:
        max_size: Maximum number of entries before LRU eviction.
    """

    def __init__(self, max_size: int = 10000) -> None:
        self._max_size = max_size
        self._cache: OrderedDict[str, CacheEntry] = OrderedDict()
        self._lock = threading.RLock()
        self._hits = 0
        self._misses = 0

    def get(self, obligation: SolverObligation) -> Optional[SolverResult]:
        """Look up a cached result.

        Returns the cached ``SolverResult`` if found, None otherwise.
        """
        key = _compute_cache_key(obligation)
        with self._lock:
            entry = self._cache.get(key)
            if entry is not None:
                self._hits += 1
                # Move to end (most recently used)
                self._cache.move_to_end(key)
                # Update hit count
                self._cache[key] = entry.with_hit()
                return entry.result
            self._misses += 1
            return None

    def put(
        self,
        obligation: SolverObligation,
        result: SolverResult,
    ) -> None:
        """Store a solver result in the cache.

        Only caches definitive results (SAT or UNSAT), not UNKNOWN/TIMEOUT.
        """
        if result.status not in {SolverStatus.SAT, SolverStatus.UNSAT}:
            return

        key = _compute_cache_key(obligation)
        entry = CacheEntry(
            key=key,
            result=result,
            timestamp=time.time(),
        )
        with self._lock:
            if key in self._cache:
                self._cache.move_to_end(key)
            self._cache[key] = entry
            # Evict if over capacity
            while len(self._cache) > self._max_size:
                self._cache.popitem(last=False)

    def invalidate(self, obligation: SolverObligation) -> bool:
        """Remove a specific obligation from the cache.

        Returns True if an entry was removed.
        """
        key = _compute_cache_key(obligation)
        with self._lock:
            if key in self._cache:
                del self._cache[key]
                return True
            return False

    def invalidate_formula(self, formula: Predicate) -> int:
        """Remove all entries whose formula matches.

        Returns the number of entries removed.
        """
        formula_hash = _compute_formula_hash(formula)
        formula_repr = repr(formula)
        removed = 0
        with self._lock:
            keys_to_remove = [
                key for key, entry in self._cache.items()
                if formula_repr in key or formula_hash in key
            ]
            for key in keys_to_remove:
                del self._cache[key]
                removed += 1
        return removed

    def clear(self) -> None:
        """Clear the entire cache."""
        with self._lock:
            self._cache.clear()
            self._hits = 0
            self._misses = 0

    @property
    def size(self) -> int:
        with self._lock:
            return len(self._cache)

    @property
    def hits(self) -> int:
        return self._hits

    @property
    def misses(self) -> int:
        return self._misses

    @property
    def hit_rate(self) -> float:
        total = self._hits + self._misses
        if total == 0:
            return 0.0
        return self._hits / total

    def statistics(self) -> Dict[str, Any]:
        with self._lock:
            return {
                "size": len(self._cache),
                "max_size": self._max_size,
                "hits": self._hits,
                "misses": self._misses,
                "hit_rate": round(self.hit_rate, 4),
            }


# ═══════════════════════════════════════════════════════════════════════════════
# Cached solver wrapper
# ═══════════════════════════════════════════════════════════════════════════════


class CachedSolver:
    """Wraps any ``LocalSolverInterface`` with result caching.

    On ``check``:
    1. Compute the cache key for the obligation.
    2. If a cached result exists, return it immediately.
    3. Otherwise, delegate to the underlying solver and cache the result.

    All other methods (push, pop, assert_formula, get_model, reset) are
    forwarded to the underlying solver.

    Implements ``LocalSolverInterface``.
    """

    def __init__(
        self,
        solver: LocalSolverInterface,
        cache: Optional[SolverCache] = None,
        stats: Optional[SolverStatistics] = None,
    ) -> None:
        self._solver = solver
        self._cache = cache or SolverCache()
        self._stats = stats or SolverStatistics()

    def check(self, obligation: SolverObligation) -> SolverResult:
        # Try cache first
        cached = self._cache.get(obligation)
        if cached is not None:
            self._stats.cache_hits += 1
            logger.debug("Cache hit for obligation at %s", obligation.site_id)
            return SolverResult(
                status=cached.status,
                model=cached.model,
                proof_certificate=cached.proof_certificate,
                time_ms=0.0,  # Cached results are instant
                unsat_core=cached.unsat_core,
                statistics=cached.statistics,
                explanation=f"[cached] {cached.explanation}",
            )

        # Cache miss: delegate to underlying solver
        self._stats.cache_misses += 1
        result = self._solver.check(obligation)

        # Cache the result (only definitive results)
        self._cache.put(obligation, result)

        self._stats.record(result)
        return result

    def push(self) -> None:
        self._solver.push()

    def pop(self) -> None:
        self._solver.pop()

    def assert_formula(self, formula: Predicate) -> None:
        self._solver.assert_formula(formula)

    def get_model(self) -> Dict[str, Any]:
        return self._solver.get_model()

    def reset(self) -> None:
        self._solver.reset()
        self._cache.clear()

    @property
    def cache(self) -> SolverCache:
        return self._cache

    @property
    def statistics(self) -> SolverStatistics:
        return self._stats

    @property
    def underlying(self) -> LocalSolverInterface:
        return self._solver


# ═══════════════════════════════════════════════════════════════════════════════
# Incremental solver
# ═══════════════════════════════════════════════════════════════════════════════


class IncrementalSolver:
    """Manages incremental solving with push/pop and assertion tracking.

    Wraps a ``LocalSolverInterface`` and tracks which assertions have been
    made at each push level, enabling:

    - Efficient incremental solving (shared context across related obligations).
    - Assertion replay after solver reset.
    - Debugging: list all active assertions at the current level.

    Implements ``LocalSolverInterface``.
    """

    def __init__(self, solver: LocalSolverInterface) -> None:
        self._solver = solver
        self._levels: List[List[Predicate]] = [[]]  # Level 0 = base
        self._total_assertions: int = 0

    def check(self, obligation: SolverObligation) -> SolverResult:
        """Check with incremental context.

        Pushes a new level, asserts the obligation's context and formula,
        checks, then pops.
        """
        self.push()
        try:
            for ctx in obligation.context:
                self.assert_formula(ctx)
            self.assert_formula(obligation.formula)
            # Direct check on the underlying solver (assertions already added)
            from deppy.core._protocols import SiteId, SiteKind
            # Create a minimal obligation (formula already asserted)
            from deppy.predicates.boolean import And
            trivial = SolverObligation(
                site_id=obligation.site_id,
                formula=And([]),  # True -- everything is already asserted
                trust_level=obligation.trust_level,
                timeout_ms=obligation.timeout_ms,
            )
            return self._solver.check(trivial)
        finally:
            self.pop()

    def push(self) -> None:
        """Create a new assertion level."""
        self._solver.push()
        self._levels.append([])

    def pop(self) -> None:
        """Pop the current assertion level."""
        if len(self._levels) > 1:
            popped = self._levels.pop()
            self._total_assertions -= len(popped)
            self._solver.pop()
        else:
            logger.warning("IncrementalSolver.pop() at base level (no-op)")

    def assert_formula(self, formula: Predicate) -> None:
        """Assert a formula at the current level."""
        self._solver.assert_formula(formula)
        self._levels[-1].append(formula)
        self._total_assertions += 1

    def get_model(self) -> Dict[str, Any]:
        return self._solver.get_model()

    def reset(self) -> None:
        """Reset to the base level."""
        self._solver.reset()
        self._levels = [[]]
        self._total_assertions = 0

    @property
    def depth(self) -> int:
        """Current push depth (0 = base level)."""
        return len(self._levels) - 1

    @property
    def total_assertions(self) -> int:
        return self._total_assertions

    def current_level_assertions(self) -> List[Predicate]:
        """Return assertions made at the current level."""
        return list(self._levels[-1])

    def all_assertions(self) -> List[Predicate]:
        """Return all active assertions across all levels."""
        result: List[Predicate] = []
        for level in self._levels:
            result.extend(level)
        return result

    @property
    def underlying(self) -> LocalSolverInterface:
        return self._solver
