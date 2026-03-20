"""Hybrid type checker — the central verification engine for DepPy's hybrid system.

Algebraic-geometric interpretation
──────────────────────────────────
Type checking at a single *site* is verifying that a runtime value is a
**section** of the appropriate presheaf.  Cross-site checking corresponds to
the **gluing condition**: local sections must agree on overlaps.  A failure to
glue is an element of the first Čech cohomology H¹ — an *obstruction*.

Bidirectional dependent type checking
─────────────────────────────────────
We combine **synthesis** (bottom-up: infer a type from a value) with
**checking** (top-down: verify a value against an expected type).  Dependent
types are instantiated lazily when concrete values arrive at runtime.

LLM oracle theory
─────────────────
Semantic predicates that cannot be decided structurally are delegated to an
LLM oracle.  An aggressive **SemanticCheckCache** keyed on
``(predicate_name, content_hash)`` ensures that the same question is never
asked twice for unchanged code, saving tokens proportionally to cache hit rate.
"""

from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.kernel.fixed_point import FixedPointEngine as _CoreFixedPointEngine
    from deppy.kernel.trust_classifier import TrustClassifier as _CoreTrustClassifier
    from deppy.solver import FragmentDispatcher as _CoreDispatcher, SolverObligation, SolverResult
    from deppy.core.presheaf import ConcretePresheaf as _CorePresheaf, SheafConditionChecker
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

import hashlib
import inspect
import json
import logging
import os
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from enum import Enum, auto
from pathlib import Path
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

if TYPE_CHECKING:
    from deppy.hybrid.core.types import (
        HybridDependentType,
        HybridRefinementType,
        HybridSigmaType,
        HybridTrustLevel,
        HybridType,
        IdentityType,
        SemanticPredicate,
        Z3Sort,
        Z3Type,
    )

# ── Optional Z3 ──────────────────────────────────────────────────────────────

try:
    import z3

    _Z3_AVAILABLE = True
except ImportError:

    z3 = None  # type: ignore[assignment]
    _Z3_AVAILABLE = False

logger = logging.getLogger(__name__)

# ═══════════════════════════════════════════════════════════════════════════════
# CheckMode
# ═══════════════════════════════════════════════════════════════════════════════

class CheckMode(Enum):
    """Selects which phases of hybrid checking to run.

    * ``STRUCTURAL_ONLY`` — Z3 / Python structural checking only.
    * ``SEMANTIC_ONLY``  — LLM oracle semantic checking only.
    * ``FULL``           — structural *then* semantic (default).
    * ``LEAN_COMPILE``   — full check *plus* emit a Lean 4 proof obligation.
    """

    STRUCTURAL_ONLY = auto()
    SEMANTIC_ONLY = auto()
    FULL = auto()
    LEAN_COMPILE = auto()

# ═══════════════════════════════════════════════════════════════════════════════
# Content hashing
# ═══════════════════════════════════════════════════════════════════════════════

def _content_hash(value: Any) -> str:
    """Compute a stable SHA-256 hex digest for *value*.

    The hash is computed over a canonical string representation so that
    structurally identical values always produce the same digest regardless of
    object identity.
    """
    try:
        if isinstance(value, (bytes, bytearray)):
            raw = value if isinstance(value, bytes) else bytes(value)
        elif isinstance(value, str):
            raw = value.encode("utf-8")
        elif isinstance(value, (int, float, bool, type(None))):
            raw = repr(value).encode("utf-8")
        elif isinstance(value, (list, tuple)):
            raw = json.dumps(value, sort_keys=True, default=str).encode("utf-8")
        elif isinstance(value, dict):
            raw = json.dumps(value, sort_keys=True, default=str).encode("utf-8")
        elif callable(value):
            source_parts: list[str] = []
            try:
                source_parts.append(inspect.getsource(value))
            except (OSError, TypeError):
                source_parts.append(repr(value))
            if hasattr(value, "__doc__") and value.__doc__:
                source_parts.append(value.__doc__)
            raw = "\n".join(source_parts).encode("utf-8")
        else:
            raw = repr(value).encode("utf-8")
    except Exception:
        raw = repr(value).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()

# ═══════════════════════════════════════════════════════════════════════════════
# CacheEntry / CacheStats
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class CacheEntry:
    """A single cached semantic-check result.

    Attributes:
        result:       Whether the semantic predicate held.
        confidence:   Oracle-reported confidence ∈ [0, 1].
        timestamp:    ISO-8601 time the entry was created.
        oracle_model: Which LLM model produced the judgment.
        reasoning:    Free-text explanation from the oracle.
        access_count: Number of times this entry was read (for LRU eviction).
    """

    result: bool
    confidence: float
    timestamp: str
    oracle_model: str
    reasoning: str
    access_count: int = 0

    # ── Serialisation helpers ──

    def to_dict(self) -> Dict[str, Any]:
        return {
            "result": self.result,
            "confidence": self.confidence,
            "timestamp": self.timestamp,
            "oracle_model": self.oracle_model,
            "reasoning": self.reasoning,
            "access_count": self.access_count,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> CacheEntry:
        return cls(
            result=d["result"],
            confidence=d["confidence"],
            timestamp=d["timestamp"],
            oracle_model=d.get("oracle_model", "unknown"),
            reasoning=d.get("reasoning", ""),
            access_count=d.get("access_count", 0),
        )

    def age_seconds(self) -> float:
        """Seconds elapsed since this entry was created."""
        try:
            created = datetime.fromisoformat(self.timestamp)
            if created.tzinfo is None:
                created = created.replace(tzinfo=timezone.utc)
            now = datetime.now(timezone.utc)
            return (now - created).total_seconds()
        except (ValueError, TypeError):
            return float("inf")

@dataclass
class CacheStats:
    """Aggregate statistics for :class:`SemanticCheckCache`."""

    hits: int
    misses: int
    hit_rate: float
    total_entries: int
    tokens_saved_estimate: int

    def to_dict(self) -> Dict[str, Any]:
        return {
            "hits": self.hits,
            "misses": self.misses,
            "hit_rate": round(self.hit_rate, 4),
            "total_entries": self.total_entries,
            "tokens_saved_estimate": self.tokens_saved_estimate,
        }

    def __repr__(self) -> str:
        return (
            f"CacheStats(hits={self.hits}, misses={self.misses}, "
            f"hit_rate={self.hit_rate:.2%}, entries={self.total_entries}, "
            f"tokens_saved≈{self.tokens_saved_estimate})"
        )

# ═══════════════════════════════════════════════════════════════════════════════
# SemanticCheckCache
# ═══════════════════════════════════════════════════════════════════════════════

# Estimated tokens consumed by a single LLM oracle call (prompt + response).
_TOKENS_PER_ORACLE_CALL = 650

class SemanticCheckCache:
    """Content-addressed cache for LLM semantic type-check results.

    Keys are ``(predicate_name, content_hash)`` pairs.  If the content hash
    has not changed since the last check, the cached result is returned
    *without* invoking the LLM oracle — this is the primary mechanism for
    token savings during iterative development.

    Parameters:
        max_age:        Entries older than this many seconds are considered stale.
        min_confidence: Entries with confidence below this threshold are re-checked.
    """

    def __init__(
        self,
        max_age: float = 3600.0,
        min_confidence: float = 0.7,
    ) -> None:
        self._entries: Dict[Tuple[str, str], CacheEntry] = {}
        self._hits: int = 0
        self._misses: int = 0
        self._max_age = max_age
        self._min_confidence = min_confidence

    # ── Query / mutate ────────────────────────────────────────────────────

    def get(
        self,
        predicate_name: str,
        content_hash: str,
    ) -> Optional[CacheEntry]:
        """Look up a cached entry.

        Returns ``None`` (a miss) if the entry is absent, stale, or below the
        confidence threshold.
        """
        key = (predicate_name, content_hash)
        entry = self._entries.get(key)
        if entry is None:
            self._misses += 1
            return None

        if entry.age_seconds() > self._max_age:
            logger.debug(
                "Cache STALE for (%s, %s…): age %.0fs > max %.0fs",
                predicate_name,
                content_hash[:12],
                entry.age_seconds(),
                self._max_age,
            )
            del self._entries[key]
            self._misses += 1
            return None

        if entry.confidence < self._min_confidence:
            logger.debug(
                "Cache LOW-CONFIDENCE for (%s, %s…): %.2f < %.2f",
                predicate_name,
                content_hash[:12],
                entry.confidence,
                self._min_confidence,
            )
            del self._entries[key]
            self._misses += 1
            return None

        entry.access_count += 1
        self._hits += 1
        logger.debug(
            "Cache HIT for (%s, %s…) → result=%s confidence=%.2f",
            predicate_name,
            content_hash[:12],
            entry.result,
            entry.confidence,
        )
        return entry

    def put(
        self,
        predicate_name: str,
        content_hash: str,
        result: bool,
        confidence: float,
        oracle_model: str,
        reasoning: str,
    ) -> CacheEntry:
        """Insert or update a cache entry after an LLM oracle call."""
        entry = CacheEntry(
            result=result,
            confidence=confidence,
            timestamp=datetime.now(timezone.utc).isoformat(),
            oracle_model=oracle_model,
            reasoning=reasoning,
            access_count=0,
        )
        self._entries[(predicate_name, content_hash)] = entry
        logger.debug(
            "Cache PUT (%s, %s…) → result=%s confidence=%.2f model=%s",
            predicate_name,
            content_hash[:12],
            result,
            confidence,
            oracle_model,
        )
        return entry

    # ── Invalidation ──────────────────────────────────────────────────────

    def invalidate(self, content_hash: str) -> int:
        """Remove *all* entries matching *content_hash* (any predicate).

        Returns the number of entries removed.
        """
        to_remove = [k for k in self._entries if k[1] == content_hash]
        for k in to_remove:
            del self._entries[k]
        if to_remove:
            logger.debug("Cache INVALIDATED %d entries for hash %s…", len(to_remove), content_hash[:12])
        return len(to_remove)

    def invalidate_predicate(self, predicate_name: str) -> int:
        """Remove *all* entries matching *predicate_name* (any content hash).

        Returns the number of entries removed.
        """
        to_remove = [k for k in self._entries if k[0] == predicate_name]
        for k in to_remove:
            del self._entries[k]
        if to_remove:
            logger.debug("Cache INVALIDATED %d entries for predicate %s", len(to_remove), predicate_name)
        return len(to_remove)

    def prune(
        self,
        max_age_seconds: Optional[float] = None,
        min_confidence: Optional[float] = None,
    ) -> int:
        """Remove stale and/or low-confidence entries.

        Parameters default to the cache's own ``max_age`` and
        ``min_confidence`` if not supplied.  Returns the count of pruned
        entries.
        """
        age_limit = max_age_seconds if max_age_seconds is not None else self._max_age
        conf_limit = min_confidence if min_confidence is not None else self._min_confidence

        to_remove: list[Tuple[str, str]] = []
        for key, entry in self._entries.items():
            if entry.age_seconds() > age_limit:
                to_remove.append(key)
            elif entry.confidence < conf_limit:
                to_remove.append(key)

        for k in to_remove:
            del self._entries[k]

        if to_remove:
            logger.debug("Cache PRUNED %d entries (age>%.0fs or conf<%.2f)", len(to_remove), age_limit, conf_limit)
        return len(to_remove)

    # ── Persistence ───────────────────────────────────────────────────────

    def save(self, path: Union[str, Path]) -> None:
        """Serialize the entire cache to *path* as JSON."""
        data = {
            "version": 1,
            "max_age": self._max_age,
            "min_confidence": self._min_confidence,
            "hits": self._hits,
            "misses": self._misses,
            "entries": {
                f"{k[0]}||{k[1]}": v.to_dict()
                for k, v in self._entries.items()
            },
        }
        target = Path(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        with open(target, "w", encoding="utf-8") as fh:
            json.dump(data, fh, indent=2, ensure_ascii=False)
        logger.info("Cache saved to %s (%d entries)", target, len(self._entries))

    @classmethod
    def load(cls, path: Union[str, Path]) -> SemanticCheckCache:
        """Deserialize a cache from *path*."""
        target = Path(path)
        with open(target, encoding="utf-8") as fh:
            data = json.load(fh)

        cache = cls(
            max_age=data.get("max_age", 3600.0),
            min_confidence=data.get("min_confidence", 0.7),
        )
        cache._hits = data.get("hits", 0)
        cache._misses = data.get("misses", 0)

        for composite_key, entry_dict in data.get("entries", {}).items():
            parts = composite_key.split("||", 1)
            if len(parts) != 2:
                logger.warning("Skipping malformed cache key: %s", composite_key)
                continue
            pred_name, chash = parts
            cache._entries[(pred_name, chash)] = CacheEntry.from_dict(entry_dict)

        logger.info("Cache loaded from %s (%d entries)", target, len(cache._entries))
        return cache

    # ── Statistics ─────────────────────────────────────────────────────────

    def stats(self) -> CacheStats:
        total = self._hits + self._misses
        return CacheStats(
            hits=self._hits,
            misses=self._misses,
            hit_rate=self._hits / total if total > 0 else 0.0,
            total_entries=len(self._entries),
            tokens_saved_estimate=self._hits * _TOKENS_PER_ORACLE_CALL,
        )

    def clear(self) -> None:
        """Remove all cached entries and reset counters."""
        self._entries.clear()
        self._hits = 0
        self._misses = 0
        logger.debug("Cache CLEARED")

    # ── Dunder ─────────────────────────────────────────────────────────────

    def __len__(self) -> int:
        return len(self._entries)

    def __contains__(self, key: Tuple[str, str]) -> bool:
        return key in self._entries

    def __repr__(self) -> str:
        s = self.stats()
        return f"SemanticCheckCache(entries={s.total_entries}, hit_rate={s.hit_rate:.2%})"

# ═══════════════════════════════════════════════════════════════════════════════
# OracleConfig
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class OracleConfig:
    """Configuration for the LLM oracle backend.

    Attributes:
        model:              Model identifier (e.g. ``"gpt-4o"``).
        timeout:            Per-call timeout in seconds.
        max_retries:        How many times to retry on transient failures.
        cache_max_age:      Maximum age (seconds) for cache entries.
        cache_min_confidence: Minimum confidence for cache entries.
        temperature:        Sampling temperature for the oracle.
        system_prompt:      Optional system prompt override.
    """

    model: str = "gpt-4o"
    timeout: float = 30.0
    max_retries: int = 3
    cache_max_age: float = 3600.0
    cache_min_confidence: float = 0.7
    temperature: float = 0.0
    system_prompt: Optional[str] = None

# ═══════════════════════════════════════════════════════════════════════════════
# Structural check helpers
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class StructuralCheckResult:
    """Outcome of the Z3/Python structural checking phase."""

    valid: bool
    solver_used: str  # "z3" | "python_fallback" | "skipped"
    elapsed_ms: float = 0.0
    counterexample: Optional[str] = None
    z3_model_str: Optional[str] = None
    violations: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "valid": self.valid,
            "solver_used": self.solver_used,
            "elapsed_ms": round(self.elapsed_ms, 3),
            "counterexample": self.counterexample,
            "z3_model_str": self.z3_model_str,
            "violations": self.violations,
        }

@dataclass
class SemanticCheckResult:
    """Outcome of the LLM oracle semantic checking phase."""

    valid: bool
    confidence: float
    reasoning: str
    oracle_model: str
    cache_hit: bool
    elapsed_ms: float = 0.0
    predicate_name: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "valid": self.valid,
            "confidence": self.confidence,
            "reasoning": self.reasoning,
            "oracle_model": self.oracle_model,
            "cache_hit": self.cache_hit,
            "elapsed_ms": round(self.elapsed_ms, 3),
            "predicate_name": self.predicate_name,
        }

# ═══════════════════════════════════════════════════════════════════════════════
# SubtypeResult / GluingCheckResult
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class SubtypeResult:
    """Result of a subtype check ``A <: B``."""

    is_subtype: bool
    structural_entailment: Optional[bool] = None
    semantic_judgment: Optional[bool] = None
    counterexample: Optional[str] = None
    reasoning: str = ""
    violations: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "is_subtype": self.is_subtype,
            "structural_entailment": self.structural_entailment,
            "semantic_judgment": self.semantic_judgment,
            "counterexample": self.counterexample,
            "reasoning": self.reasoning,
            "violations": self.violations,
        }

@dataclass
class GluingCheckResult:
    """Result of the sheaf gluing condition check.

    In sheaf-theoretic terms, sections defined over an open cover must agree on
    pairwise overlaps.  ``obstructions`` records the disagreements; an empty
    list means the cocycle condition holds and the sections glue.
    """

    compatible: bool
    obstructions: List[Dict[str, Any]] = field(default_factory=list)
    local_agreements: Dict[str, bool] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "compatible": self.compatible,
            "obstructions": self.obstructions,
            "local_agreements": self.local_agreements,
        }

    def __bool__(self) -> bool:
        return self.compatible

# ═══════════════════════════════════════════════════════════════════════════════
# HybridCheckResult
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class HybridCheckResult:
    """Combined result of a hybrid (structural + semantic) type check.

    Attributes:
        valid:              Overall verdict.
        structural_result:  Phase-1 outcome (may be ``None`` in SEMANTIC_ONLY mode).
        semantic_result:    Phase-2 outcome (may be ``None`` in STRUCTURAL_ONLY mode).
        trust_level:        Name of the :class:`HybridTrustLevel` governing this check.
        lean_obligation:    Lean 4 theorem statement (LEAN_COMPILE mode).
        content_hash:       SHA-256 of the checked value (for cache keying).
        cache_hit:          ``True`` when the semantic result was served from cache.
        violations:         Human-readable violation messages.
    """

    valid: bool
    structural_result: Optional[StructuralCheckResult] = None
    semantic_result: Optional[SemanticCheckResult] = None
    trust_level: str = "UNKNOWN"
    lean_obligation: Optional[str] = None
    content_hash: str = ""
    cache_hit: bool = False
    violations: List[str] = field(default_factory=list)

    # ── Dunder helpers ────────────────────────────────────────────────────

    def __bool__(self) -> bool:
        return self.valid

    def __str__(self) -> str:
        status = "✓ VALID" if self.valid else "✗ INVALID"
        parts = [f"HybridCheck {status} (trust={self.trust_level})"]

        if self.structural_result is not None:
            sr = self.structural_result
            parts.append(
                f"  structural: {'✓' if sr.valid else '✗'} "
                f"[{sr.solver_used}, {sr.elapsed_ms:.1f}ms]"
            )

        if self.semantic_result is not None:
            sem = self.semantic_result
            cache_tag = " (cached)" if sem.cache_hit else ""
            parts.append(
                f"  semantic:   {'✓' if sem.valid else '✗'} "
                f"[conf={sem.confidence:.2f}, {sem.oracle_model}{cache_tag}]"
            )

        if self.lean_obligation:
            parts.append(f"  lean: {self.lean_obligation[:80]}…")

        if self.violations:
            parts.append("  violations:")
            for v in self.violations:
                parts.append(f"    - {v}")

        return "\n".join(parts)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "valid": self.valid,
            "structural_result": self.structural_result.to_dict() if self.structural_result else None,
            "semantic_result": self.semantic_result.to_dict() if self.semantic_result else None,
            "trust_level": self.trust_level,
            "lean_obligation": self.lean_obligation,
            "content_hash": self.content_hash,
            "cache_hit": self.cache_hit,
            "violations": self.violations,
        }

# ═══════════════════════════════════════════════════════════════════════════════
# Z3 structural checking helpers (internal)
# ═══════════════════════════════════════════════════════════════════════════════

class _Z3Engine:
    """Thin wrapper around Z3 for structural constraint checking.

    Handles solver creation, timeout, and safe fallback when Z3 is unavailable.
    """

    def __init__(self, timeout_ms: int = 5000) -> None:
        self._timeout_ms = timeout_ms

    @property
    def available(self) -> bool:
        return _Z3_AVAILABLE

    # ── Constraint-based check ────────────────────────────────────────────

    def check_constraints(
        self,
        value: Any,
        constraints_fn: Optional[Callable[..., Any]],
    ) -> StructuralCheckResult:
        """Check *value* against Z3 constraints produced by *constraints_fn*.

        *constraints_fn* receives a Z3 variable and should return a list of Z3
        Bool expressions that must all be satisfiable simultaneously with the
        variable equal to *value*.
        """
        if not _Z3_AVAILABLE or constraints_fn is None:
            return self._python_fallback(value, constraints_fn)

        t0 = time.perf_counter()
        try:
            solver = z3.Solver()
            solver.set("timeout", self._timeout_ms)

            z3_val = self._to_z3_value(value)
            if z3_val is None:
                return self._python_fallback(value, constraints_fn)

            constraints = constraints_fn(z3_val)
            if not isinstance(constraints, (list, tuple)):
                constraints = [constraints]

            for c in constraints:
                solver.add(c)

            result = solver.check()
            elapsed = (time.perf_counter() - t0) * 1000

            if result == z3.sat:
                return StructuralCheckResult(
                    valid=True,
                    solver_used="z3",
                    elapsed_ms=elapsed,
                )
            elif result == z3.unsat:
                return StructuralCheckResult(
                    valid=False,
                    solver_used="z3",
                    elapsed_ms=elapsed,
                    violations=["Z3: constraints unsatisfiable"],
                )
            else:
                return StructuralCheckResult(
                    valid=False,
                    solver_used="z3",
                    elapsed_ms=elapsed,
                    violations=["Z3: solver returned unknown (timeout?)"],
                )
        except Exception as exc:
            elapsed = (time.perf_counter() - t0) * 1000
            logger.warning("Z3 check failed, falling back to Python: %s", exc)
            return self._python_fallback(value, constraints_fn)

    def check_entailment(
        self,
        antecedent_fn: Optional[Callable[..., Any]],
        consequent_fn: Optional[Callable[..., Any]],
    ) -> Tuple[bool, Optional[str]]:
        """Check ``∀x. antecedent(x) ⟹ consequent(x)`` via Z3.

        Returns ``(entails, counterexample_str | None)``.
        """
        if not _Z3_AVAILABLE or antecedent_fn is None or consequent_fn is None:
            return False, "Z3 unavailable or constraints missing"

        try:
            solver = z3.Solver()
            solver.set("timeout", self._timeout_ms)

            x = z3.Int("x")
            ante = antecedent_fn(x)
            cons = consequent_fn(x)
            if not isinstance(ante, (list, tuple)):
                ante = [ante]
            if not isinstance(cons, (list, tuple)):
                cons = [cons]

            for a in ante:
                solver.add(a)
            solver.add(z3.Not(z3.And(*cons)))

            result = solver.check()
            if result == z3.unsat:
                return True, None
            elif result == z3.sat:
                model = solver.model()
                return False, str(model)
            else:
                return False, "Z3: unknown (timeout?)"
        except Exception as exc:
            logger.warning("Z3 entailment check failed: %s", exc)
            return False, f"Z3 error: {exc}"

    def check_equality(self, lhs: Any, rhs: Any) -> Tuple[bool, Optional[str]]:
        """Check structural equality of *lhs* and *rhs* via Z3.

        Falls back to Python ``==`` when Z3 cannot handle the values.
        """
        if not _Z3_AVAILABLE:
            return lhs == rhs, None

        try:
            z3_lhs = self._to_z3_value(lhs)
            z3_rhs = self._to_z3_value(rhs)
            if z3_lhs is None or z3_rhs is None:
                return lhs == rhs, None

            solver = z3.Solver()
            solver.set("timeout", self._timeout_ms)
            solver.add(z3_lhs != z3_rhs)
            result = solver.check()
            if result == z3.unsat:
                return True, None
            elif result == z3.sat:
                return False, str(solver.model())
            else:
                return lhs == rhs, None
        except Exception:
            return lhs == rhs, None

    # ── Python fallback ───────────────────────────────────────────────────

    def _python_fallback(
        self,
        value: Any,
        constraints_fn: Optional[Callable[..., Any]],
    ) -> StructuralCheckResult:
        """Evaluate constraints via Python when Z3 is unavailable."""
        t0 = time.perf_counter()
        if constraints_fn is None:
            return StructuralCheckResult(
                valid=True,
                solver_used="python_fallback",
                elapsed_ms=(time.perf_counter() - t0) * 1000,
            )
        try:
            result = constraints_fn(value)
            if isinstance(result, bool):
                valid = result
            elif isinstance(result, (list, tuple)):
                valid = all(bool(r) for r in result)
            else:
                valid = bool(result)
            elapsed = (time.perf_counter() - t0) * 1000
            return StructuralCheckResult(
                valid=valid,
                solver_used="python_fallback",
                elapsed_ms=elapsed,
                violations=[] if valid else ["Python fallback: constraint failed"],
            )
        except Exception as exc:
            elapsed = (time.perf_counter() - t0) * 1000
            return StructuralCheckResult(
                valid=False,
                solver_used="python_fallback",
                elapsed_ms=elapsed,
                violations=[f"Python fallback error: {exc}"],
            )

    # ── Z3 value conversion ───────────────────────────────────────────────

    @staticmethod
    def _to_z3_value(value: Any) -> Any:
        """Convert a Python value to a Z3 expression, or return ``None``."""
        if not _Z3_AVAILABLE:
            return None
        if isinstance(value, bool):
            return z3.BoolVal(value)
        if isinstance(value, int):
            return z3.IntVal(value)
        if isinstance(value, float):
            return z3.RealVal(value)
        if isinstance(value, str):
            return z3.StringVal(value)
        return None

# ═══════════════════════════════════════════════════════════════════════════════
# Python structural checking (no Z3)
# ═══════════════════════════════════════════════════════════════════════════════

class _PythonStructuralChecker:
    """Pure-Python structural checks for when Z3 is unavailable.

    Performs isinstance checks, bound checks, length checks, etc.
    """

    @staticmethod
    def check_python_type(value: Any, expected_type: type) -> StructuralCheckResult:
        t0 = time.perf_counter()
        valid = isinstance(value, expected_type)
        elapsed = (time.perf_counter() - t0) * 1000
        violations = [] if valid else [f"Expected {expected_type.__name__}, got {type(value).__name__}"]
        return StructuralCheckResult(
            valid=valid,
            solver_used="python_fallback",
            elapsed_ms=elapsed,
            violations=violations,
        )

    @staticmethod
    def check_bounds(
        value: Any,
        lower: Optional[Any] = None,
        upper: Optional[Any] = None,
    ) -> StructuralCheckResult:
        t0 = time.perf_counter()
        violations: List[str] = []
        if lower is not None and value < lower:
            violations.append(f"Value {value} < lower bound {lower}")
        if upper is not None and value > upper:
            violations.append(f"Value {value} > upper bound {upper}")
        elapsed = (time.perf_counter() - t0) * 1000
        return StructuralCheckResult(
            valid=len(violations) == 0,
            solver_used="python_fallback",
            elapsed_ms=elapsed,
            violations=violations,
        )

    @staticmethod
    def check_predicate_python(
        value: Any,
        predicate: Callable[[Any], bool],
        predicate_name: str = "<predicate>",
    ) -> StructuralCheckResult:
        t0 = time.perf_counter()
        try:
            result = predicate(value)
            valid = bool(result)
        except Exception as exc:
            valid = False
            elapsed = (time.perf_counter() - t0) * 1000
            return StructuralCheckResult(
                valid=False,
                solver_used="python_fallback",
                elapsed_ms=elapsed,
                violations=[f"Predicate '{predicate_name}' raised: {exc}"],
            )
        elapsed = (time.perf_counter() - t0) * 1000
        return StructuralCheckResult(
            valid=valid,
            solver_used="python_fallback",
            elapsed_ms=elapsed,
            violations=[] if valid else [f"Predicate '{predicate_name}' failed"],
        )

# ═══════════════════════════════════════════════════════════════════════════════
# Lean obligation emitter (internal)
# ═══════════════════════════════════════════════════════════════════════════════

class _LeanEmitter:
    """Generates Lean 4 proof obligations from hybrid type-check results."""

    @staticmethod
    def emit_membership(
        value_repr: str,
        type_repr: str,
        *,
        structural_ok: bool = True,
        semantic_ok: bool = True,
    ) -> str:
        """Emit a Lean theorem stating *value* is a member of *type*."""
        sanitised_val = _LeanEmitter._sanitise(value_repr)
        sanitised_ty = _LeanEmitter._sanitise(type_repr)
        theorem_name = f"check_{sanitised_val}_mem_{sanitised_ty}"
        if structural_ok and semantic_ok:
            return (
                f"theorem {theorem_name} : "
                f"{sanitised_val} ∈ {sanitised_ty} := by\n"
                f"  -- structural + semantic evidence\n"
                f"  sorry"
            )
        elif structural_ok:
            return (
                f"theorem {theorem_name} : "
                f"{sanitised_val} ∈ {sanitised_ty} := by\n"
                f"  -- structural evidence only; semantic TBD\n"
                f"  sorry"
            )
        else:
            return (
                f"-- FAILED: {sanitised_val} ∉ {sanitised_ty}\n"
                f"-- Structural check failed"
            )

    @staticmethod
    def emit_subtype(a_repr: str, b_repr: str, *, holds: bool) -> str:
        sanitised_a = _LeanEmitter._sanitise(a_repr)
        sanitised_b = _LeanEmitter._sanitise(b_repr)
        if holds:
            return (
                f"theorem subtype_{sanitised_a}_{sanitised_b} : "
                f"∀ x, x ∈ {sanitised_a} → x ∈ {sanitised_b} := by\n"
                f"  sorry"
            )
        return (
            f"-- FAILED: {sanitised_a} is NOT a subtype of {sanitised_b}"
        )

    @staticmethod
    def emit_identity(carrier_repr: str, lhs_repr: str, rhs_repr: str) -> str:
        sanitised_c = _LeanEmitter._sanitise(carrier_repr)
        sanitised_l = _LeanEmitter._sanitise(lhs_repr)
        sanitised_r = _LeanEmitter._sanitise(rhs_repr)
        return (
            f"theorem id_{sanitised_l}_eq_{sanitised_r} : "
            f"@Eq {sanitised_c} {sanitised_l} {sanitised_r} := by\n"
            f"  sorry"
        )

    @staticmethod
    def emit_gluing(cover_repr: str, n_sites: int) -> str:
        return (
            f"-- Gluing obligation over {n_sites} sites\n"
            f"-- Cover: {cover_repr}\n"
            f"theorem gluing_condition : True := by trivial"
        )

    @staticmethod
    def _sanitise(name: str) -> str:
        """Make a Python repr safe for use as a Lean identifier fragment."""
        result: list[str] = []
        for ch in name:
            if ch.isalnum() or ch == "_":
                result.append(ch)
            elif ch in (" ", "-", ".", ":"):
                result.append("_")
        cleaned = "".join(result).strip("_")
        if not cleaned or not cleaned[0].isalpha():
            cleaned = "v_" + cleaned
        return cleaned[:64]

# ═══════════════════════════════════════════════════════════════════════════════
# HybridTypeChecker — the main engine
# ═══════════════════════════════════════════════════════════════════════════════

class HybridTypeChecker:
    """Central verification engine for DepPy's hybrid type system.

    Orchestrates four phases:

    1. **Structural** — discharge decidable constraints via Z3 (or Python
       fallback).
    2. **Semantic** — delegate undecidable / natural-language predicates to an
       LLM oracle, with an aggressive content-hash cache.
    3. **Combine** — merge structural and semantic verdicts under the type's
       trust policy.
    4. **Lean emit** — optionally produce a Lean 4 proof obligation for the
       verified judgment.

    Parameters:
        oracle_fn:     ``(prompt, model, temperature) → dict`` callback that
                       calls the LLM.  May be ``None`` (semantic checks skipped).
        oracle_config: Configuration for the oracle backend.
        cache:         A pre-populated :class:`SemanticCheckCache`.  A fresh
                       one is created if ``None``.
        z3_timeout:    Z3 solver timeout in milliseconds.
    """

    def __init__(
        self,
        oracle_fn: Optional[Callable[..., Dict[str, Any]]] = None,
        oracle_config: Optional[OracleConfig] = None,
        cache: Optional[SemanticCheckCache] = None,
        z3_timeout: int = 5000,
    ) -> None:
        self._oracle_fn = oracle_fn
        self._config = oracle_config or OracleConfig()
        self._cache = cache or SemanticCheckCache(
            max_age=self._config.cache_max_age,
            min_confidence=self._config.cache_min_confidence,
        )
        self._z3 = _Z3Engine(timeout_ms=z3_timeout)
        self._python_checker = _PythonStructuralChecker()
        self._lean = _LeanEmitter()

    # ── Properties ────────────────────────────────────────────────────────

    @property
    def cache(self) -> SemanticCheckCache:
        """The semantic check cache used by this checker."""
        return self._cache

    @property
    def z3_available(self) -> bool:
        return self._z3.available

    # ══════════════════════════════════════════════════════════════════════
    # check — primary entry point
    # ══════════════════════════════════════════════════════════════════════

    def check(
        self,
        value: Any,
        hybrid_type: HybridType,
        mode: CheckMode = CheckMode.FULL,
    ) -> HybridCheckResult:
        """Check *value* against *hybrid_type* under the given *mode*.

        Phase 1 (structural): uses Z3 or Python to verify decidable
        constraints such as type membership, bound checks, and refinement
        predicates that have executable implementations.

        Phase 2 (semantic): consults the :class:`SemanticCheckCache` first; on
        a miss, invokes the LLM oracle and updates the cache.

        Phase 3 (combine): merges structural and semantic verdicts.

        Phase 4 (Lean emit): in ``LEAN_COMPILE`` mode, emits a proof
        obligation.
        """
        chash = _content_hash(value)
        violations: List[str] = []

        # ── Phase 1: structural ───────────────────────────────────────────
        structural_result: Optional[StructuralCheckResult] = None
        if mode in (CheckMode.STRUCTURAL_ONLY, CheckMode.FULL, CheckMode.LEAN_COMPILE):
            structural_result = self._structural_check(value, hybrid_type)
            violations.extend(structural_result.violations)

        # ── Phase 2: semantic ─────────────────────────────────────────────
        semantic_result: Optional[SemanticCheckResult] = None
        if mode in (CheckMode.SEMANTIC_ONLY, CheckMode.FULL, CheckMode.LEAN_COMPILE):
            semantic_result = self._semantic_check(value, hybrid_type, chash)
            if not semantic_result.valid:
                violations.append(
                    f"Semantic predicate failed: {semantic_result.reasoning}"
                )

        # ── Phase 3: combine ──────────────────────────────────────────────
        valid = self._combine_verdicts(structural_result, semantic_result, mode)

        trust_level = self._resolve_trust_level(hybrid_type)

        # ── Phase 4: Lean obligation ──────────────────────────────────────
        lean_obligation: Optional[str] = None
        if mode == CheckMode.LEAN_COMPILE:
            lean_obligation = self._lean.emit_membership(
                repr(value),
                self._type_repr(hybrid_type),
                structural_ok=structural_result.valid if structural_result else True,
                semantic_ok=semantic_result.valid if semantic_result else True,
            )

        cache_hit = semantic_result.cache_hit if semantic_result else False

        return HybridCheckResult(
            valid=valid,
            structural_result=structural_result,
            semantic_result=semantic_result,
            trust_level=trust_level,
            lean_obligation=lean_obligation,
            content_hash=chash,
            cache_hit=cache_hit,
            violations=violations,
        )

    # ══════════════════════════════════════════════════════════════════════
    # check_dependent — Π-type checking
    # ══════════════════════════════════════════════════════════════════════

    def check_dependent(
        self,
        input_value: Any,
        output_value: Any,
        dep_type: HybridDependentType,
        mode: CheckMode = CheckMode.FULL,
    ) -> HybridCheckResult:
        """Check a dependent function application.

        Given ``f : Π(x:A).B(x)``, verifies:
        1. *input_value* ∈ A  (the domain type)
        2. Instantiate ``B(input_value)``
        3. *output_value* ∈ B(input_value)
        """
        # Step 1: check input against domain
        domain_type = self._get_domain_type(dep_type)
        if domain_type is not None:
            domain_result = self.check(input_value, domain_type, mode)
            if not domain_result.valid:
                return HybridCheckResult(
                    valid=False,
                    structural_result=domain_result.structural_result,
                    semantic_result=domain_result.semantic_result,
                    trust_level=self._resolve_trust_level(dep_type),
                    content_hash=_content_hash(input_value),
                    violations=[
                        f"Input value failed domain check: {v}"
                        for v in domain_result.violations
                    ],
                )

        # Step 2: instantiate the codomain type
        codomain_type = self._instantiate_codomain(dep_type, input_value)

        # Step 3: check output against instantiated codomain
        if codomain_type is not None:
            output_result = self.check(output_value, codomain_type, mode)
            return HybridCheckResult(
                valid=output_result.valid,
                structural_result=output_result.structural_result,
                semantic_result=output_result.semantic_result,
                trust_level=self._resolve_trust_level(dep_type),
                lean_obligation=output_result.lean_obligation,
                content_hash=_content_hash(output_value),
                cache_hit=output_result.cache_hit,
                violations=output_result.violations,
            )

        # Fallback: if we cannot instantiate, do a direct structural + semantic check
        return self.check(output_value, dep_type, mode)

    # ══════════════════════════════════════════════════════════════════════
    # check_sigma — Σ-type checking
    # ══════════════════════════════════════════════════════════════════════

    def check_sigma(
        self,
        fst: Any,
        snd: Any,
        sigma_type: HybridSigmaType,
        mode: CheckMode = CheckMode.FULL,
    ) -> HybridCheckResult:
        """Check a dependent pair ``(fst, snd) : Σ(x:A).B(x)``.

        1. Check *fst* ∈ A  (the base type).
        2. Instantiate B(fst).
        3. Check *snd* ∈ B(fst) (the fiber type).
        """
        all_violations: List[str] = []
        combined_structural: Optional[StructuralCheckResult] = None
        combined_semantic: Optional[SemanticCheckResult] = None

        # Step 1: check fst against base type
        base_type = self._get_base_type(sigma_type)
        if base_type is not None:
            fst_result = self.check(fst, base_type, mode)
            combined_structural = fst_result.structural_result
            combined_semantic = fst_result.semantic_result
            if not fst_result.valid:
                all_violations.extend(
                    f"Σ fst: {v}" for v in fst_result.violations
                )
                return HybridCheckResult(
                    valid=False,
                    structural_result=combined_structural,
                    semantic_result=combined_semantic,
                    trust_level=self._resolve_trust_level(sigma_type),
                    content_hash=_content_hash((fst, snd)),
                    violations=all_violations,
                )

        # Step 2 + 3: instantiate fiber and check snd
        fiber_type = self._instantiate_fiber(sigma_type, fst)
        if fiber_type is not None:
            snd_result = self.check(snd, fiber_type, mode)
            if not snd_result.valid:
                all_violations.extend(
                    f"Σ snd: {v}" for v in snd_result.violations
                )
            return HybridCheckResult(
                valid=snd_result.valid and len(all_violations) == 0,
                structural_result=snd_result.structural_result or combined_structural,
                semantic_result=snd_result.semantic_result or combined_semantic,
                trust_level=self._resolve_trust_level(sigma_type),
                content_hash=_content_hash((fst, snd)),
                cache_hit=snd_result.cache_hit,
                violations=all_violations,
            )

        # No fiber type available — check the pair as a whole
        pair_hash = _content_hash((fst, snd))
        return HybridCheckResult(
            valid=len(all_violations) == 0,
            structural_result=combined_structural,
            semantic_result=combined_semantic,
            trust_level=self._resolve_trust_level(sigma_type),
            content_hash=pair_hash,
            violations=all_violations,
        )

    # ══════════════════════════════════════════════════════════════════════
    # check_refinement — {v:τ | φ(v)} checking
    # ══════════════════════════════════════════════════════════════════════

    def check_refinement(
        self,
        value: Any,
        ref_type: HybridRefinementType,
        mode: CheckMode = CheckMode.FULL,
    ) -> HybridCheckResult:
        """Check *value* against a hybrid refinement type ``{v:τ | φ(v)}``.

        1. Check *value* ∈ τ (the base type).
        2. Check φ(value) (the refinement predicate — may be structural,
           semantic, or both).
        """
        violations: List[str] = []

        # Step 1: base type check
        base_type = self._get_base_type(ref_type)
        base_result: Optional[HybridCheckResult] = None
        if base_type is not None:
            base_result = self.check(value, base_type, mode)
            if not base_result.valid:
                violations.extend(f"Refinement base: {v}" for v in base_result.violations)
                return HybridCheckResult(
                    valid=False,
                    structural_result=base_result.structural_result,
                    semantic_result=base_result.semantic_result,
                    trust_level=self._resolve_trust_level(ref_type),
                    content_hash=_content_hash(value),
                    violations=violations,
                )

        # Step 2: refinement predicate check
        chash = _content_hash(value)
        predicate_result = self._check_refinement_predicate(value, ref_type, chash, mode)
        if not predicate_result.valid:
            violations.extend(predicate_result.violations)

        structural = predicate_result.structural_result
        if base_result and base_result.structural_result and structural:
            structural = StructuralCheckResult(
                valid=base_result.structural_result.valid and structural.valid,
                solver_used=structural.solver_used,
                elapsed_ms=base_result.structural_result.elapsed_ms + structural.elapsed_ms,
                violations=base_result.structural_result.violations + structural.violations,
            )
        elif base_result and base_result.structural_result:
            structural = base_result.structural_result

        lean_obligation: Optional[str] = None
        if mode == CheckMode.LEAN_COMPILE:
            lean_obligation = self._lean.emit_membership(
                repr(value),
                self._type_repr(ref_type),
                structural_ok=structural.valid if structural else True,
                semantic_ok=predicate_result.semantic_result.valid if predicate_result.semantic_result else True,
            )

        return HybridCheckResult(
            valid=predicate_result.valid and len(violations) == 0,
            structural_result=structural,
            semantic_result=predicate_result.semantic_result,
            trust_level=self._resolve_trust_level(ref_type),
            lean_obligation=lean_obligation,
            content_hash=chash,
            cache_hit=predicate_result.cache_hit,
            violations=violations,
        )

    # ══════════════════════════════════════════════════════════════════════
    # check_identity — Id_A(a, b)
    # ══════════════════════════════════════════════════════════════════════

    def check_identity(
        self,
        id_type: IdentityType,
        mode: CheckMode = CheckMode.FULL,
    ) -> HybridCheckResult:
        """Check an identity type ``Id_A(lhs, rhs)``.

        Structural phase: Z3 equality check on lhs and rhs.
        Semantic phase: LLM equivalence judgment (useful when lhs/rhs are
        natural-language descriptions or complex objects).
        """
        lhs = self._extract_identity_lhs(id_type)
        rhs = self._extract_identity_rhs(id_type)
        carrier = self._extract_identity_carrier(id_type)

        violations: List[str] = []

        # Structural: Z3 equality
        structural_result: Optional[StructuralCheckResult] = None
        if mode in (CheckMode.STRUCTURAL_ONLY, CheckMode.FULL, CheckMode.LEAN_COMPILE):
            t0 = time.perf_counter()
            eq, counterexample = self._z3.check_equality(lhs, rhs)
            elapsed = (time.perf_counter() - t0) * 1000
            structural_result = StructuralCheckResult(
                valid=eq,
                solver_used="z3" if self._z3.available else "python_fallback",
                elapsed_ms=elapsed,
                counterexample=counterexample,
                violations=[] if eq else [f"Structural inequality: {lhs!r} ≠ {rhs!r}"],
            )
            if not eq:
                violations.append(f"Id check: {lhs!r} ≢ {rhs!r} (structural)")

        # Semantic: LLM equivalence judgment
        semantic_result: Optional[SemanticCheckResult] = None
        if mode in (CheckMode.SEMANTIC_ONLY, CheckMode.FULL, CheckMode.LEAN_COMPILE):
            identity_hash = _content_hash((lhs, rhs, repr(carrier)))
            semantic_result = self._semantic_identity_check(
                lhs, rhs, carrier, identity_hash,
            )
            if not semantic_result.valid:
                violations.append(
                    f"Id check: LLM judges {lhs!r} ≢ {rhs!r} — {semantic_result.reasoning}"
                )

        valid = self._combine_verdicts(structural_result, semantic_result, mode)

        lean_obligation: Optional[str] = None
        if mode == CheckMode.LEAN_COMPILE:
            lean_obligation = self._lean.emit_identity(
                repr(carrier), repr(lhs), repr(rhs),
            )

        return HybridCheckResult(
            valid=valid,
            structural_result=structural_result,
            semantic_result=semantic_result,
            trust_level="VERIFIED" if valid else "REFUTED",
            lean_obligation=lean_obligation,
            content_hash=_content_hash((lhs, rhs)),
            cache_hit=semantic_result.cache_hit if semantic_result else False,
            violations=violations,
        )

    # ══════════════════════════════════════════════════════════════════════
    # synthesize — bottom-up type inference
    # ══════════════════════════════════════════════════════════════════════

    def synthesize(self, value: Any) -> Dict[str, Any]:
        """Infer the most precise *HybridType* descriptor for *value*.

        Returns a dictionary description of the synthesized type that can be
        consumed by the type-construction layer in ``deppy.hybrid.core.types``
        to build a proper ``HybridType`` instance.

        Bottom-up inference rules:

        * ``int`` → Z3Sort.INT with tight bounds ``[value, value]``.
        * ``float`` → Z3Sort.REAL with tight bounds.
        * ``bool`` → Z3Sort.BOOL with exact value.
        * ``str`` → Z3Sort.STRING with length bounds.
        * ``list`` → Z3Sort.ARRAY with element type union and length.
        * ``tuple`` → product of element types.
        * ``dict`` → structural record with per-key types.
        * ``function`` → inferred from signature + docstring.
        * ``None`` → unit type.
        """
        if value is None:
            return {"sort": "UNIT", "value": None}

        if isinstance(value, bool):
            return {
                "sort": "BOOL",
                "exact_value": value,
                "structural_constraints": {"eq": value},
            }

        if isinstance(value, int):
            return {
                "sort": "INT",
                "exact_value": value,
                "structural_constraints": {
                    "lower_bound": value,
                    "upper_bound": value,
                },
            }

        if isinstance(value, float):
            return {
                "sort": "REAL",
                "exact_value": value,
                "structural_constraints": {
                    "lower_bound": value,
                    "upper_bound": value,
                },
            }

        if isinstance(value, str):
            return {
                "sort": "STRING",
                "exact_value": value,
                "structural_constraints": {
                    "min_length": len(value),
                    "max_length": len(value),
                },
            }

        if isinstance(value, (list, tuple)):
            element_types = [self.synthesize(elem) for elem in value]
            sort_name = "ARRAY" if isinstance(value, list) else "PRODUCT"
            unified_sort = self._unify_element_sorts(element_types)
            return {
                "sort": sort_name,
                "element_types": element_types,
                "unified_element_sort": unified_sort,
                "structural_constraints": {
                    "length": len(value),
                    "min_length": len(value),
                    "max_length": len(value),
                },
            }

        if isinstance(value, dict):
            key_types: Dict[str, Any] = {}
            for k, v in value.items():
                key_types[str(k)] = self.synthesize(v)
            return {
                "sort": "RECORD",
                "fields": key_types,
                "structural_constraints": {
                    "num_fields": len(value),
                    "required_keys": list(value.keys()),
                },
            }

        if callable(value):
            return self._synthesize_callable(value)

        # Fallback: opaque type
        return {
            "sort": "OPAQUE",
            "python_type": type(value).__qualname__,
            "content_hash": _content_hash(value),
        }

    def _synthesize_callable(self, fn: Callable[..., Any]) -> Dict[str, Any]:
        """Synthesize a type for a callable."""
        sig_info: Dict[str, Any] = {}
        try:
            sig = inspect.signature(fn)
            params: Dict[str, Any] = {}
            for name, param in sig.parameters.items():
                p_info: Dict[str, Any] = {"name": name, "kind": param.kind.name}
                if param.annotation is not inspect.Parameter.empty:
                    p_info["annotation"] = str(param.annotation)
                if param.default is not inspect.Parameter.empty:
                    p_info["has_default"] = True
                    p_info["default_type"] = type(param.default).__name__
                params[name] = p_info
            sig_info["parameters"] = params
            if sig.return_annotation is not inspect.Signature.empty:
                sig_info["return_annotation"] = str(sig.return_annotation)
        except (ValueError, TypeError):
            pass

        docstring = getattr(fn, "__doc__", None) or ""
        qualname = getattr(fn, "__qualname__", repr(fn))

        return {
            "sort": "FUNCTION",
            "qualname": qualname,
            "signature": sig_info,
            "docstring": docstring[:500] if docstring else "",
            "content_hash": _content_hash(fn),
        }

    @staticmethod
    def _unify_element_sorts(element_types: List[Dict[str, Any]]) -> str:
        """Find the least upper bound of sorts for a homogeneous collection."""
        if not element_types:
            return "BOTTOM"
        sorts = {et.get("sort", "OPAQUE") for et in element_types}
        if len(sorts) == 1:
            return sorts.pop()
        if sorts <= {"INT", "REAL"}:
            return "REAL"
        if sorts <= {"INT", "REAL", "BOOL"}:
            return "REAL"
        return "TOP"

    # ══════════════════════════════════════════════════════════════════════
    # subtype — A <: B
    # ══════════════════════════════════════════════════════════════════════

    def subtype(
        self,
        a: HybridType,
        b: HybridType,
        mode: CheckMode = CheckMode.FULL,
    ) -> SubtypeResult:
        """Check whether *a* is a subtype of *b*.

        Structural phase: if both types expose Z3 constraint generators, check
        ``∀x. a.constraints(x) ⟹ b.constraints(x)`` via Z3 entailment.

        Semantic phase: ask the LLM oracle whether ``a`` implies ``b``.
        """
        violations: List[str] = []

        # ── Structural entailment ─────────────────────────────────────────
        structural_entailment: Optional[bool] = None
        counterexample: Optional[str] = None
        if mode in (CheckMode.STRUCTURAL_ONLY, CheckMode.FULL, CheckMode.LEAN_COMPILE):
            a_constraints = self._get_constraint_fn(a)
            b_constraints = self._get_constraint_fn(b)
            if a_constraints is not None and b_constraints is not None:
                structural_entailment, counterexample = self._z3.check_entailment(
                    a_constraints, b_constraints,
                )
                if not structural_entailment:
                    violations.append(
                        f"Structural: a ⊬ b"
                        + (f" (counterexample: {counterexample})" if counterexample else "")
                    )
            else:
                # Cannot structurally verify — leave as None
                pass

        # ── Semantic judgment ─────────────────────────────────────────────
        semantic_judgment: Optional[bool] = None
        if mode in (CheckMode.SEMANTIC_ONLY, CheckMode.FULL, CheckMode.LEAN_COMPILE):
            a_repr = self._type_repr(a)
            b_repr = self._type_repr(b)
            subtype_hash = _content_hash((a_repr, b_repr))
            cached = self._cache.get("__subtype__", subtype_hash)
            if cached is not None:
                semantic_judgment = cached.result
            elif self._oracle_fn is not None:
                prompt = (
                    f"Is type A a subtype of type B?\n"
                    f"A: {a_repr}\n"
                    f"B: {b_repr}\n"
                    f"Answer with JSON: {{\"is_subtype\": true/false, "
                    f"\"confidence\": 0.0-1.0, \"reasoning\": \"...\"}}"
                )
                oracle_result = self._call_oracle(prompt)
                semantic_judgment = oracle_result.get("is_subtype", False)
                confidence = oracle_result.get("confidence", 0.5)
                reasoning = oracle_result.get("reasoning", "")
                self._cache.put(
                    "__subtype__",
                    subtype_hash,
                    semantic_judgment,
                    confidence,
                    self._config.model,
                    reasoning,
                )
                if not semantic_judgment:
                    violations.append(f"Semantic: LLM judges A ≮: B — {reasoning}")

        # ── Combine ───────────────────────────────────────────────────────
        if structural_entailment is not None and semantic_judgment is not None:
            is_subtype = structural_entailment and semantic_judgment
        elif structural_entailment is not None:
            is_subtype = structural_entailment
        elif semantic_judgment is not None:
            is_subtype = semantic_judgment
        else:
            is_subtype = False
            violations.append("Neither structural nor semantic check was available")

        return SubtypeResult(
            is_subtype=is_subtype,
            structural_entailment=structural_entailment,
            semantic_judgment=semantic_judgment,
            counterexample=counterexample,
            reasoning="; ".join(violations) if violations else "Subtype relation holds",
            violations=violations,
        )

    # ══════════════════════════════════════════════════════════════════════
    # check_gluing — sheaf cocycle condition
    # ══════════════════════════════════════════════════════════════════════

    def check_gluing(
        self,
        local_types: Dict[str, Any],
        cover: List[Tuple[str, str]],
        mode: CheckMode = CheckMode.FULL,
    ) -> GluingCheckResult:
        """Verify the sheaf gluing (cocycle) condition.

        Given local sections ``local_types[i]`` over sites ``i``, and a cover
        specifying overlaps as pairs ``(i, j)``, verify that for each overlap
        the restriction of the section at *i* agrees with the restriction at
        *j*.

        In cohomological terms, disagreements are **obstructions** living in
        H¹(cover, F) where F is the type presheaf.

        Parameters:
            local_types: Mapping from site name to the local type / section
                         (any object — compared via content hash and semantic
                         equivalence).
            cover:       List of overlap pairs ``(site_i, site_j)``.
            mode:        Check mode for individual comparisons.
        """
        obstructions: List[Dict[str, Any]] = []
        local_agreements: Dict[str, bool] = {}

        for site_i, site_j in cover:
            overlap_key = f"{site_i}∩{site_j}"

            section_i = local_types.get(site_i)
            section_j = local_types.get(site_j)

            if section_i is None or section_j is None:
                obstructions.append({
                    "overlap": overlap_key,
                    "reason": f"Missing section: {'site_i=' + site_i if section_i is None else 'site_j=' + site_j}",
                    "type": "missing_section",
                })
                local_agreements[overlap_key] = False
                continue

            # Structural comparison
            hash_i = _content_hash(section_i)
            hash_j = _content_hash(section_j)

            if hash_i == hash_j:
                local_agreements[overlap_key] = True
                continue

            # Hashes differ — try deeper comparison
            structural_eq: Optional[bool] = None
            semantic_eq: Optional[bool] = None

            if mode in (CheckMode.STRUCTURAL_ONLY, CheckMode.FULL, CheckMode.LEAN_COMPILE):
                eq, _ = self._z3.check_equality(section_i, section_j)
                structural_eq = eq

            if mode in (CheckMode.SEMANTIC_ONLY, CheckMode.FULL, CheckMode.LEAN_COMPILE):
                gluing_hash = _content_hash((hash_i, hash_j))
                cached = self._cache.get("__gluing__", gluing_hash)
                if cached is not None:
                    semantic_eq = cached.result
                elif self._oracle_fn is not None:
                    prompt = (
                        f"Do these two type descriptions agree (are they equivalent)?\n"
                        f"Section at site {site_i}: {repr(section_i)[:500]}\n"
                        f"Section at site {site_j}: {repr(section_j)[:500]}\n"
                        f"Answer JSON: {{\"equivalent\": true/false, "
                        f"\"confidence\": 0.0-1.0, \"reasoning\": \"...\"}}"
                    )
                    oracle_result = self._call_oracle(prompt)
                    semantic_eq = oracle_result.get("equivalent", False)
                    confidence = oracle_result.get("confidence", 0.5)
                    reasoning = oracle_result.get("reasoning", "")
                    self._cache.put(
                        "__gluing__",
                        gluing_hash,
                        semantic_eq,
                        confidence,
                        self._config.model,
                        reasoning,
                    )

            # Combine
            if structural_eq is True or semantic_eq is True:
                local_agreements[overlap_key] = True
            else:
                local_agreements[overlap_key] = False
                obstruction_detail: Dict[str, Any] = {
                    "overlap": overlap_key,
                    "site_i": site_i,
                    "site_j": site_j,
                    "hash_i": hash_i[:16],
                    "hash_j": hash_j[:16],
                    "structural_eq": structural_eq,
                    "semantic_eq": semantic_eq,
                    "type": "section_mismatch",
                }
                obstructions.append(obstruction_detail)

        compatible = len(obstructions) == 0

        return GluingCheckResult(
            compatible=compatible,
            obstructions=obstructions,
            local_agreements=local_agreements,
        )

    # ══════════════════════════════════════════════════════════════════════
    # batch_check — amortised checking over many values
    # ══════════════════════════════════════════════════════════════════════

    def batch_check(
        self,
        values_and_types: List[Tuple[Any, Any]],
        mode: CheckMode = CheckMode.FULL,
    ) -> List[HybridCheckResult]:
        """Check multiple ``(value, hybrid_type)`` pairs.

        Maximises cache hits by pre-computing content hashes and grouping
        identical values so the oracle is invoked at most once per unique
        content hash.

        Returns results in the same order as the input list.
        """
        results: List[Optional[HybridCheckResult]] = [None] * len(values_and_types)

        # Pre-compute hashes to identify duplicates
        hash_to_indices: Dict[str, List[int]] = {}
        for idx, (value, _) in enumerate(values_and_types):
            chash = _content_hash(value)
            hash_to_indices.setdefault(chash, []).append(idx)

        # Process each unique (hash, type) pair once
        processed: Dict[Tuple[str, int], HybridCheckResult] = {}

        for idx, (value, hybrid_type) in enumerate(values_and_types):
            chash = _content_hash(value)
            type_id_key = id(hybrid_type)
            cache_key = (chash, type_id_key)

            if cache_key in processed:
                # Re-use a previously computed result for the same value+type
                results[idx] = processed[cache_key]
                continue

            result = self.check(value, hybrid_type, mode)
            processed[cache_key] = result
            results[idx] = result

        # Propagate results for duplicate values with identical types
        for idx in range(len(results)):
            if results[idx] is None:
                value, hybrid_type = values_and_types[idx]
                results[idx] = self.check(value, hybrid_type, mode)

        return results  # type: ignore[return-value]

    # ══════════════════════════════════════════════════════════════════════
    # Private: structural check dispatch
    # ══════════════════════════════════════════════════════════════════════

    def _structural_check(
        self,
        value: Any,
        hybrid_type: Any,
    ) -> StructuralCheckResult:
        """Run the structural (Z3 / Python) check phase.

        Inspects *hybrid_type* for:
        - ``python_type``: an ``isinstance`` check.
        - ``structural_constraints`` or ``z3_constraints_fn``: Z3 constraint check.
        - ``structural_predicate``: a Python callable predicate.

        Falls back to a permissive pass if the type provides no structural
        information.
        """
        t0 = time.perf_counter()
        violations: List[str] = []

        # Check Python type if specified
        py_type = getattr(hybrid_type, "python_type", None)
        if py_type is not None:
            if not isinstance(value, py_type):
                violations.append(
                    f"Expected Python type {py_type.__name__}, "
                    f"got {type(value).__name__}"
                )

        # Z3 constraint function
        z3_fn = getattr(hybrid_type, "z3_constraints_fn", None)
        if z3_fn is not None:
            z3_result = self._z3.check_constraints(value, z3_fn)
            violations.extend(z3_result.violations)
            elapsed = (time.perf_counter() - t0) * 1000
            return StructuralCheckResult(
                valid=len(violations) == 0,
                solver_used=z3_result.solver_used,
                elapsed_ms=elapsed,
                violations=violations,
                z3_model_str=z3_result.z3_model_str,
            )

        # Python structural predicate
        structural_pred = getattr(hybrid_type, "structural_predicate", None)
        if structural_pred is not None and callable(structural_pred):
            try:
                pred_ok = structural_pred(value)
                if not pred_ok:
                    violations.append("Structural predicate failed")
            except Exception as exc:
                violations.append(f"Structural predicate error: {exc}")

        # Structural constraints dict (bounds, etc.)
        constraints_dict = getattr(hybrid_type, "structural_constraints", None)
        if isinstance(constraints_dict, dict):
            violations.extend(self._check_constraints_dict(value, constraints_dict))

        elapsed = (time.perf_counter() - t0) * 1000
        return StructuralCheckResult(
            valid=len(violations) == 0,
            solver_used="python_fallback",
            elapsed_ms=elapsed,
            violations=violations,
        )

    def _check_constraints_dict(
        self,
        value: Any,
        constraints: Dict[str, Any],
    ) -> List[str]:
        """Evaluate a dictionary of named constraints against *value*."""
        violations: List[str] = []

        lower = constraints.get("lower_bound")
        if lower is not None:
            try:
                if value < lower:
                    violations.append(f"Value {value!r} < lower bound {lower}")
            except TypeError:
                pass

        upper = constraints.get("upper_bound")
        if upper is not None:
            try:
                if value > upper:
                    violations.append(f"Value {value!r} > upper bound {upper}")
            except TypeError:
                pass

        min_len = constraints.get("min_length")
        if min_len is not None:
            try:
                if len(value) < min_len:
                    violations.append(f"Length {len(value)} < min_length {min_len}")
            except TypeError:
                pass

        max_len = constraints.get("max_length")
        if max_len is not None:
            try:
                if len(value) > max_len:
                    violations.append(f"Length {len(value)} > max_length {max_len}")
            except TypeError:
                pass

        eq = constraints.get("eq")
        if eq is not None:
            if value != eq:
                violations.append(f"Value {value!r} ≠ expected {eq!r}")

        pattern = constraints.get("pattern")
        if pattern is not None and isinstance(value, str):
            import re

            if not re.search(pattern, value):
                violations.append(f"Value does not match pattern {pattern!r}")

        one_of = constraints.get("one_of")
        if one_of is not None:
            if value not in one_of:
                violations.append(f"Value {value!r} not in {one_of!r}")

        return violations

    # ══════════════════════════════════════════════════════════════════════
    # Private: semantic check dispatch
    # ══════════════════════════════════════════════════════════════════════

    def _semantic_check(
        self,
        value: Any,
        hybrid_type: Any,
        content_hash: str,
    ) -> SemanticCheckResult:
        """Run the semantic (LLM oracle) check phase.

        Consults the :class:`SemanticCheckCache` **first**.  On a miss, calls
        the oracle and updates the cache.  If no oracle is configured, returns
        a vacuously-true result.
        """
        predicates = self._get_semantic_predicates(hybrid_type)

        if not predicates:
            return SemanticCheckResult(
                valid=True,
                confidence=1.0,
                reasoning="No semantic predicates to check",
                oracle_model="none",
                cache_hit=False,
            )

        all_valid = True
        combined_confidence = 1.0
        combined_reasoning: List[str] = []
        any_cache_hit = False
        total_elapsed = 0.0

        for pred_name, pred_desc in predicates:
            # ── Cache lookup ──────────────────────────────────────────────
            cached_entry = self._cache.get(pred_name, content_hash)
            if cached_entry is not None:
                any_cache_hit = True
                if not cached_entry.result:
                    all_valid = False
                combined_confidence = min(combined_confidence, cached_entry.confidence)
                combined_reasoning.append(
                    f"[{pred_name}] (cached) {cached_entry.reasoning}"
                )
                continue

            # ── Oracle call ───────────────────────────────────────────────
            if self._oracle_fn is None:
                combined_reasoning.append(
                    f"[{pred_name}] No oracle available — assumed true"
                )
                continue

            prompt = (
                f"Does the following value satisfy the semantic predicate?\n\n"
                f"Predicate: {pred_name}\n"
                f"Description: {pred_desc}\n"
                f"Value: {repr(value)[:1000]}\n\n"
                f"Answer with JSON: {{"
                f"\"satisfies\": true/false, "
                f"\"confidence\": 0.0-1.0, "
                f"\"reasoning\": \"...\""
                f"}}"
            )

            t0 = time.perf_counter()
            oracle_result = self._call_oracle(prompt)
            elapsed = (time.perf_counter() - t0) * 1000
            total_elapsed += elapsed

            satisfies = oracle_result.get("satisfies", True)
            confidence = oracle_result.get("confidence", 0.5)
            reasoning = oracle_result.get("reasoning", "")

            # ── Cache update ──────────────────────────────────────────────
            self._cache.put(
                pred_name,
                content_hash,
                satisfies,
                confidence,
                self._config.model,
                reasoning,
            )

            if not satisfies:
                all_valid = False
            combined_confidence = min(combined_confidence, confidence)
            combined_reasoning.append(f"[{pred_name}] {reasoning}")

        return SemanticCheckResult(
            valid=all_valid,
            confidence=combined_confidence,
            reasoning="; ".join(combined_reasoning) if combined_reasoning else "All predicates passed",
            oracle_model=self._config.model,
            cache_hit=any_cache_hit and len(predicates) > 0,
            elapsed_ms=total_elapsed,
        )

    def _semantic_identity_check(
        self,
        lhs: Any,
        rhs: Any,
        carrier: Any,
        identity_hash: str,
    ) -> SemanticCheckResult:
        """Semantic equivalence check for identity types."""
        cached_entry = self._cache.get("__identity__", identity_hash)
        if cached_entry is not None:
            return SemanticCheckResult(
                valid=cached_entry.result,
                confidence=cached_entry.confidence,
                reasoning=cached_entry.reasoning,
                oracle_model=cached_entry.oracle_model,
                cache_hit=True,
            )

        if self._oracle_fn is None:
            eq = lhs == rhs
            return SemanticCheckResult(
                valid=eq,
                confidence=1.0 if eq else 0.0,
                reasoning="Python equality (no oracle)" if eq else "Python inequality (no oracle)",
                oracle_model="none",
                cache_hit=False,
            )

        prompt = (
            f"Are these two values equivalent at the given type?\n\n"
            f"Type: {repr(carrier)[:300]}\n"
            f"LHS: {repr(lhs)[:500]}\n"
            f"RHS: {repr(rhs)[:500]}\n\n"
            f"Answer with JSON: {{\"equivalent\": true/false, "
            f"\"confidence\": 0.0-1.0, \"reasoning\": \"...\"}}"
        )

        t0 = time.perf_counter()
        oracle_result = self._call_oracle(prompt)
        elapsed = (time.perf_counter() - t0) * 1000

        equivalent = oracle_result.get("equivalent", False)
        confidence = oracle_result.get("confidence", 0.5)
        reasoning = oracle_result.get("reasoning", "")

        self._cache.put(
            "__identity__",
            identity_hash,
            equivalent,
            confidence,
            self._config.model,
            reasoning,
        )

        return SemanticCheckResult(
            valid=equivalent,
            confidence=confidence,
            reasoning=reasoning,
            oracle_model=self._config.model,
            cache_hit=False,
            elapsed_ms=elapsed,
        )

    # ══════════════════════════════════════════════════════════════════════
    # Private: refinement predicate checking
    # ══════════════════════════════════════════════════════════════════════

    def _check_refinement_predicate(
        self,
        value: Any,
        ref_type: Any,
        content_hash: str,
        mode: CheckMode,
    ) -> HybridCheckResult:
        """Check the refinement predicate for a refinement type.

        Handles both structural predicates (Python callables) and semantic
        predicates (LLM-checked natural language descriptions).
        """
        violations: List[str] = []
        structural_result: Optional[StructuralCheckResult] = None
        semantic_result: Optional[SemanticCheckResult] = None

        # Structural predicate
        structural_pred = getattr(ref_type, "refinement_predicate", None)
        if structural_pred is not None and callable(structural_pred):
            if mode in (CheckMode.STRUCTURAL_ONLY, CheckMode.FULL, CheckMode.LEAN_COMPILE):
                t0 = time.perf_counter()
                try:
                    pred_ok = bool(structural_pred(value))
                except Exception as exc:
                    pred_ok = False
                    violations.append(f"Refinement predicate error: {exc}")
                elapsed = (time.perf_counter() - t0) * 1000
                if not pred_ok:
                    violations.append("Refinement predicate failed")
                structural_result = StructuralCheckResult(
                    valid=pred_ok,
                    solver_used="python_fallback",
                    elapsed_ms=elapsed,
                    violations=violations[:],
                )

        # Semantic predicates
        if mode in (CheckMode.SEMANTIC_ONLY, CheckMode.FULL, CheckMode.LEAN_COMPILE):
            semantic_result = self._semantic_check(value, ref_type, content_hash)
            if not semantic_result.valid:
                violations.append(f"Semantic refinement failed: {semantic_result.reasoning}")

        valid = self._combine_verdicts(structural_result, semantic_result, mode)

        return HybridCheckResult(
            valid=valid,
            structural_result=structural_result,
            semantic_result=semantic_result,
            trust_level=self._resolve_trust_level(ref_type),
            content_hash=content_hash,
            cache_hit=semantic_result.cache_hit if semantic_result else False,
            violations=violations,
        )

    # ══════════════════════════════════════════════════════════════════════
    # Private: oracle invocation
    # ══════════════════════════════════════════════════════════════════════

    def _call_oracle(self, prompt: str) -> Dict[str, Any]:
        """Call the LLM oracle with retries and JSON parsing.

        Returns a parsed dict, or a fallback dict on failure.
        """
        if self._oracle_fn is None:
            return {"error": "no_oracle", "satisfies": True, "confidence": 0.0}

        last_error: Optional[Exception] = None
        for attempt in range(self._config.max_retries):
            try:
                raw = self._oracle_fn(
                    prompt,
                    self._config.model,
                    self._config.temperature,
                )

                if isinstance(raw, dict):
                    return raw

                if isinstance(raw, str):
                    return self._parse_oracle_json(raw)

                return {"raw": raw, "satisfies": True, "confidence": 0.5}

            except Exception as exc:
                last_error = exc
                logger.warning(
                    "Oracle call attempt %d/%d failed: %s",
                    attempt + 1,
                    self._config.max_retries,
                    exc,
                )
                if attempt < self._config.max_retries - 1:
                    time.sleep(min(2 ** attempt, 8))

        logger.error("Oracle exhausted retries: %s", last_error)
        return {
            "error": str(last_error),
            "satisfies": False,
            "confidence": 0.0,
            "reasoning": f"Oracle failed after {self._config.max_retries} retries: {last_error}",
        }

    @staticmethod
    def _parse_oracle_json(raw: str) -> Dict[str, Any]:
        """Extract a JSON object from a possibly noisy LLM response."""
        raw = raw.strip()

        # Try direct parse
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            pass

        # Try to find JSON within markdown code fences
        import re

        fence_match = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", raw, re.DOTALL)
        if fence_match:
            try:
                return json.loads(fence_match.group(1))
            except json.JSONDecodeError:
                pass

        # Try to find any JSON object
        brace_match = re.search(r"\{[^{}]*\}", raw, re.DOTALL)
        if brace_match:
            try:
                return json.loads(brace_match.group(0))
            except json.JSONDecodeError:
                pass

        return {"raw": raw, "satisfies": True, "confidence": 0.3, "reasoning": "Unparseable oracle output"}

    # ══════════════════════════════════════════════════════════════════════
    # Private: verdict combination
    # ══════════════════════════════════════════════════════════════════════

    @staticmethod
    def _combine_verdicts(
        structural: Optional[StructuralCheckResult],
        semantic: Optional[SemanticCheckResult],
        mode: CheckMode,
    ) -> bool:
        """Combine structural and semantic verdicts into a single boolean.

        Policy:
        - STRUCTURAL_ONLY: structural verdict only (True if absent).
        - SEMANTIC_ONLY: semantic verdict only (True if absent).
        - FULL / LEAN_COMPILE: both must pass (conjunction).
        """
        if mode == CheckMode.STRUCTURAL_ONLY:
            return structural.valid if structural is not None else True
        if mode == CheckMode.SEMANTIC_ONLY:
            return semantic.valid if semantic is not None else True

        # FULL or LEAN_COMPILE: conjunction
        s_ok = structural.valid if structural is not None else True
        m_ok = semantic.valid if semantic is not None else True
        return s_ok and m_ok

    # ══════════════════════════════════════════════════════════════════════
    # Private: type introspection helpers
    # ══════════════════════════════════════════════════════════════════════

    @staticmethod
    def _get_semantic_predicates(hybrid_type: Any) -> List[Tuple[str, str]]:
        """Extract ``(name, description)`` semantic predicate pairs from a type.

        Looks for ``semantic_predicates`` attribute (list of predicate objects
        or tuples) on *hybrid_type*.
        """
        raw = getattr(hybrid_type, "semantic_predicates", None)
        if raw is None:
            return []

        result: List[Tuple[str, str]] = []
        if isinstance(raw, (list, tuple)):
            for item in raw:
                if isinstance(item, tuple) and len(item) >= 2:
                    result.append((str(item[0]), str(item[1])))
                elif hasattr(item, "name") and hasattr(item, "description"):
                    result.append((item.name, item.description))
                elif isinstance(item, str):
                    result.append((item, item))
        elif isinstance(raw, dict):
            for name, desc in raw.items():
                result.append((str(name), str(desc)))

        return result

    @staticmethod
    def _get_constraint_fn(hybrid_type: Any) -> Optional[Callable[..., Any]]:
        """Extract a Z3 constraint generator from a type, if present."""
        return getattr(hybrid_type, "z3_constraints_fn", None)

    @staticmethod
    def _get_domain_type(dep_type: Any) -> Optional[Any]:
        """Extract the domain (parameter) type from a dependent type."""
        return getattr(dep_type, "domain_type", None) or getattr(dep_type, "param_type", None)

    @staticmethod
    def _get_base_type(hybrid_type: Any) -> Optional[Any]:
        """Extract the base type from a sigma or refinement type."""
        return (
            getattr(hybrid_type, "base_type", None)
            or getattr(hybrid_type, "fst_type", None)
            or getattr(hybrid_type, "param_type", None)
        )

    @staticmethod
    def _instantiate_codomain(dep_type: Any, input_value: Any) -> Optional[Any]:
        """Instantiate the codomain of a dependent type with a concrete value."""
        instantiate = getattr(dep_type, "instantiate", None)
        if instantiate is not None and callable(instantiate):
            try:
                return instantiate(input_value)
            except Exception as exc:
                logger.warning("Failed to instantiate codomain: %s", exc)
                return None

        codomain_fn = getattr(dep_type, "codomain_fn", None)
        if codomain_fn is not None and callable(codomain_fn):
            try:
                return codomain_fn(input_value)
            except Exception as exc:
                logger.warning("Failed to compute codomain: %s", exc)
                return None

        return getattr(dep_type, "return_type", None)

    @staticmethod
    def _instantiate_fiber(sigma_type: Any, fst_value: Any) -> Optional[Any]:
        """Instantiate the fiber (second component type) of a Σ-type."""
        instantiate = getattr(sigma_type, "instantiate_fiber", None)
        if instantiate is not None and callable(instantiate):
            try:
                return instantiate(fst_value)
            except Exception as exc:
                logger.warning("Failed to instantiate fiber: %s", exc)
                return None

        fiber_fn = getattr(sigma_type, "fiber_fn", None)
        if fiber_fn is not None and callable(fiber_fn):
            try:
                return fiber_fn(fst_value)
            except Exception as exc:
                logger.warning("Failed to compute fiber: %s", exc)
                return None

        return getattr(sigma_type, "snd_type", None)

    @staticmethod
    def _extract_identity_lhs(id_type: Any) -> Any:
        return getattr(id_type, "lhs", None)

    @staticmethod
    def _extract_identity_rhs(id_type: Any) -> Any:
        return getattr(id_type, "rhs", None)

    @staticmethod
    def _extract_identity_carrier(id_type: Any) -> Any:
        return getattr(id_type, "carrier", None)

    @staticmethod
    def _resolve_trust_level(hybrid_type: Any) -> str:
        """Resolve the trust level name from a hybrid type."""
        trust = getattr(hybrid_type, "trust_level", None)
        if trust is not None:
            if isinstance(trust, str):
                return trust
            name = getattr(trust, "name", None)
            if name is not None:
                return str(name)
            return str(trust)
        return "UNKNOWN"

    @staticmethod
    def _type_repr(hybrid_type: Any) -> str:
        """Get a human-readable representation of a type."""
        name = getattr(hybrid_type, "name", None)
        if name:
            return str(name)
        description = getattr(hybrid_type, "description", None)
        if description:
            return str(description)
        try:
            return repr(hybrid_type)
        except Exception:
            return str(type(hybrid_type).__name__)

    # ══════════════════════════════════════════════════════════════════════
    # Dunder / utility
    # ══════════════════════════════════════════════════════════════════════

    def __repr__(self) -> str:
        return (
            f"HybridTypeChecker("
            f"oracle={'configured' if self._oracle_fn else 'none'}, "
            f"z3={'available' if self._z3.available else 'unavailable'}, "
            f"cache={self._cache!r})"
        )
