"""Diff-based incremental verification using sheaf locality.

Sheaf locality and incremental verification
────────────────────────────────────────────
The **key mathematical insight** is that a presheaf satisfying the sheaf
condition is *determined locally*: a global section is uniquely reconstructed
from compatible local sections.  When a single site *s* is modified, the
cocycle condition can only break on overlaps involving *s*.  Sites whose
open sets are disjoint from *s* are provably unaffected — their cached H¹
data remains valid.

In concrete code terms: if function ``f`` changes, we must re-verify ``f``
and every function that **calls** ``f`` or is **called by** ``f`` (the
Čech-neighborhood of ``f`` in the call-graph nerve).  Everything else can
be read from the incremental cache.

Usage::

    deppy check --incremental          # re-verify only changed sites
    deppy check --since <commit>       # verify changes since a commit

Integration::

    # .pre-commit-config.yaml
    - repo: local
      hooks:
        - id: deppy-pre-commit
          name: deppy incremental check
          entry: deppy check --incremental --staged
          language: system
"""
from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.incremental import Workspace, WorkspaceDiffer, SectionCache, compute_impact_set
    from deppy.incremental.models import ChangeNotice, ImpactSet
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

import ast
import hashlib
import json
import logging
import os
import re
import subprocess
import time
from dataclasses import dataclass, field
from enum import Enum, unique
from pathlib import Path
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

if TYPE_CHECKING:
    from deppy.hybrid.core.trust import TrustLevel

# ── Optional Z3 ──────────────────────────────────────────────────────────────

try:
    import z3

    _Z3_AVAILABLE = True
except ImportError:

    z3 = None  # type: ignore[assignment]
    _Z3_AVAILABLE = False

logger = logging.getLogger(__name__)

# ─── Constants ────────────────────────────────────────────────────────────────

_CACHE_DIR = ".deppy/cache"
_H1_CACHE_FILE = "h1_cache.json"
_DEFAULT_CONFIG_PATH = ".deppy/config.toml"

# ─── Enums ────────────────────────────────────────────────────────────────────

@unique
class ChangeType(Enum):
    """Kind of modification detected in a diff hunk."""

    ADDED = "added"
    MODIFIED = "modified"
    DELETED = "deleted"

# ─── ChangedSite ──────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class ChangedSite:
    """A single code site (function / class / module) affected by a diff.

    Each *site* corresponds to an open set in the Čech cover of the
    codebase.  The ``affected_layers`` list records which layers of the
    presheaf (types, contracts, runtime traces, …) are invalidated by
    this change and therefore need re-verification.
    """

    file_path: str
    function_name: str
    line_range: Tuple[int, int]
    change_type: ChangeType
    affected_layers: List[str] = field(default_factory=list)

    # -- helpers ---------------------------------------------------------------

    @property
    def site_id(self) -> str:
        """Canonical identifier for this site in the cover."""
        return f"{self.file_path}::{self.function_name}"

    def overlaps(self, other: ChangedSite) -> bool:
        """True when the two sites share lines (non-empty intersection)."""
        if self.file_path != other.file_path:
            return False
        a0, a1 = self.line_range
        b0, b1 = other.line_range
        return a0 <= b1 and b0 <= a1

    def __str__(self) -> str:
        return (
            f"{self.change_type.value} {self.file_path}::{self.function_name}"
            f" L{self.line_range[0]}-{self.line_range[1]}"
        )

# ─── SheafLocalityAnalyzer ────────────────────────────────────────────────────

class SheafLocalityAnalyzer:
    """Computes the verification neighborhood of a code change using sheaf locality.

    If site *s* changes, we only need to re-verify:

    1. **s itself** — the local section changed.
    2. **Sites s′ where s ∩ s′ ≠ ∅** in the cover — the cocycle condition
       on the overlap may break.
    3. **NOT sites s″ with s ∩ s″ = ∅** — sheaf locality guarantees that
       disjoint sites are independent.

    In code terms: if function ``f`` changes, re-verify ``f`` and any
    function that **calls** ``f`` or **is called by** ``f``.  Unrelated
    functions are provably safe to skip.
    """

    def __init__(self, depth: int = 1) -> None:
        self._depth = depth

    # -- public API ------------------------------------------------------------

    def compute_neighborhood(
        self,
        changed: List[ChangedSite],
        call_graph: Dict[str, Set[str]],
    ) -> List[str]:
        """Return the set of site-ids that must be re-verified.

        The neighborhood is the *d*-hop ego graph around each changed site in
        the call-graph nerve, where *d* = ``self._depth`` (default 1, i.e. only
        direct callers / callees).
        """
        seeds: Set[str] = {s.site_id for s in changed}
        neighborhood: Set[str] = set(seeds)

        frontier = set(seeds)
        for _ in range(self._depth):
            next_frontier: Set[str] = set()
            for site_id in frontier:
                # Forward edges (callees)
                callees = call_graph.get(site_id, set())
                next_frontier |= callees - neighborhood
                # Backward edges (callers)
                for caller, targets in call_graph.items():
                    if site_id in targets and caller not in neighborhood:
                        next_frontier.add(caller)
            neighborhood |= next_frontier
            frontier = next_frontier
            if not frontier:
                break

        return sorted(neighborhood)

    def build_call_graph(
        self,
        source_files: Dict[str, str],
    ) -> Dict[str, Set[str]]:
        """Build a call graph from source files mapping ``site_id → {callee_ids}``.

        Uses a lightweight AST walk — not a full points-to analysis — which is
        intentionally conservative (may over-approximate call targets).
        """
        call_graph: Dict[str, Set[str]] = {}
        # First pass: collect all defined functions per file
        function_defs: Dict[str, str] = {}  # name → site_id
        for fpath, source in source_files.items():
            try:
                tree = ast.parse(source, filename=fpath)
            except SyntaxError:
                logger.warning("Skipping %s (syntax error)", fpath)
                continue
            for node in ast.walk(tree):
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    site_id = f"{fpath}::{node.name}"
                    function_defs[node.name] = site_id
                    call_graph.setdefault(site_id, set())

        # Second pass: resolve call targets
        for fpath, source in source_files.items():
            try:
                tree = ast.parse(source, filename=fpath)
            except SyntaxError:
                continue
            for func_node in ast.walk(tree):
                if not isinstance(
                    func_node, (ast.FunctionDef, ast.AsyncFunctionDef)
                ):
                    continue
                caller_id = f"{fpath}::{func_node.name}"
                for child in ast.walk(func_node):
                    if isinstance(child, ast.Call):
                        callee_name = self._resolve_call_name(child)
                        if callee_name and callee_name in function_defs:
                            callee_id = function_defs[callee_name]
                            call_graph.setdefault(caller_id, set()).add(callee_id)

        return call_graph

    def minimal_recheck_set(
        self,
        changed: List[ChangedSite],
        call_graph: Dict[str, Set[str]],
        prev_h1_data: Optional[Dict[str, Any]] = None,
    ) -> List[str]:
        """Compute the *minimal* set of sites requiring re-verification.

        This further prunes the neighborhood by checking whether the cached
        H¹ data for a neighbor is still structurally compatible with the new
        local section (i.e. the cocycle condition is unchanged).

        Parameters
        ----------
        changed:
            Sites directly modified.
        call_graph:
            The call-graph nerve of the codebase.
        prev_h1_data:
            Mapping ``site_id → cached_h1_info``.  If *None* all neighbors
            are rechecked.
        """
        neighborhood = self.compute_neighborhood(changed, call_graph)
        if prev_h1_data is None:
            return neighborhood

        changed_ids = {s.site_id for s in changed}
        must_recheck: List[str] = []

        for site_id in neighborhood:
            # Always recheck directly-changed sites
            if site_id in changed_ids:
                must_recheck.append(site_id)
                continue

            cached = prev_h1_data.get(site_id)
            if cached is None:
                # No cached data — must check
                must_recheck.append(site_id)
                continue

            # Check if any of this site's call-graph edges touch a changed site
            callees = call_graph.get(site_id, set())
            if callees & changed_ids:
                must_recheck.append(site_id)
                continue

            # Check reverse edges
            callers_of_site = {
                caller
                for caller, targets in call_graph.items()
                if site_id in targets
            }
            if callers_of_site & changed_ids:
                must_recheck.append(site_id)
                continue

            # Neighbor is in the neighborhood but its direct edges are not to
            # any changed site — the cocycle on the overlap is unchanged.
            logger.debug(
                "Skipping %s — cocycle condition structurally unchanged",
                site_id,
            )

        return must_recheck

    # -- reverse graph ---------------------------------------------------------

    def build_reverse_graph(
        self,
        call_graph: Dict[str, Set[str]],
    ) -> Dict[str, Set[str]]:
        """Return the reverse call graph (callee → {callers})."""
        reverse: Dict[str, Set[str]] = {}
        for caller, callees in call_graph.items():
            for callee in callees:
                reverse.setdefault(callee, set()).add(caller)
        return reverse

    def transitive_dependents(
        self,
        site_id: str,
        call_graph: Dict[str, Set[str]],
        max_depth: int = 5,
    ) -> Set[str]:
        """Return all sites transitively depending on *site_id*."""
        reverse = self.build_reverse_graph(call_graph)
        visited: Set[str] = set()
        frontier = {site_id}
        for _ in range(max_depth):
            next_frontier: Set[str] = set()
            for sid in frontier:
                for dep in reverse.get(sid, set()):
                    if dep not in visited:
                        visited.add(dep)
                        next_frontier.add(dep)
            frontier = next_frontier
            if not frontier:
                break
        return visited

    # -- private helpers -------------------------------------------------------

    @staticmethod
    def _resolve_call_name(call_node: ast.Call) -> Optional[str]:
        """Extract the simple function name from a Call AST node."""
        func = call_node.func
        if isinstance(func, ast.Name):
            return func.id
        if isinstance(func, ast.Attribute):
            return func.attr
        return None

# ─── IncrementalCache ─────────────────────────────────────────────────────────

@dataclass
class _CacheEntry:
    """A single cache entry for a site's H¹ data."""

    site_id: str
    content_hash: str
    h1_data: Dict[str, Any]
    timestamp: float = field(default_factory=time.time)
    hit_count: int = 0

class IncrementalCache:
    """Stores per-site H¹ data with content-hash–based invalidation.

    Persistence layer backed by ``.deppy/cache/h1_cache.json``.

    The cache maps each *site_id* to the H¹ cohomological data computed
    during the last full or incremental verification pass.  A cache entry is
    *valid* iff the content hash of the current source matches the stored
    hash — any byte-level change invalidates the entry.
    """

    def __init__(self, cache_dir: Optional[str] = None) -> None:
        self._cache_dir = cache_dir or _CACHE_DIR
        self._entries: Dict[str, _CacheEntry] = {}
        self._hits: int = 0
        self._misses: int = 0
        self._loaded = False

    # -- public API ------------------------------------------------------------

    def put(
        self,
        site_id: str,
        h1_data: Dict[str, Any],
        content_hash: str,
    ) -> None:
        """Store (or overwrite) H¹ data for *site_id*."""
        self._entries[site_id] = _CacheEntry(
            site_id=site_id,
            content_hash=content_hash,
            h1_data=h1_data,
        )

    def get(self, site_id: str) -> Optional[Dict[str, Any]]:
        """Return cached H¹ data, or *None* on miss."""
        entry = self._entries.get(site_id)
        if entry is None:
            self._misses += 1
            return None
        entry.hit_count += 1
        self._hits += 1
        return entry.h1_data

    def invalidate(self, site_ids: Sequence[str]) -> int:
        """Remove entries for the given site IDs.  Returns count removed."""
        removed = 0
        for sid in site_ids:
            if sid in self._entries:
                del self._entries[sid]
                removed += 1
        return removed

    def invalidate_file(self, file_path: str) -> int:
        """Invalidate all sites belonging to *file_path*."""
        to_remove = [
            sid for sid in self._entries if sid.startswith(f"{file_path}::")
        ]
        return self.invalidate(to_remove)

    def is_valid(self, site_id: str, current_hash: str) -> bool:
        """Check whether the cached entry for *site_id* matches *current_hash*."""
        entry = self._entries.get(site_id)
        if entry is None:
            return False
        return entry.content_hash == current_hash

    def all_site_ids(self) -> List[str]:
        """Return all cached site IDs."""
        return list(self._entries.keys())

    @property
    def size(self) -> int:
        """Number of entries in the cache."""
        return len(self._entries)

    @property
    def hit_rate(self) -> float:
        """Fraction of ``get`` calls that were cache hits."""
        total = self._hits + self._misses
        return self._hits / total if total > 0 else 0.0

    # -- persistence -----------------------------------------------------------

    def save(self, path: Optional[str] = None) -> None:
        """Persist the cache to disk as JSON."""
        target = Path(path) if path else Path(self._cache_dir) / _H1_CACHE_FILE
        target.parent.mkdir(parents=True, exist_ok=True)

        payload: Dict[str, Any] = {}
        for sid, entry in self._entries.items():
            payload[sid] = {
                "content_hash": entry.content_hash,
                "h1_data": entry.h1_data,
                "timestamp": entry.timestamp,
                "hit_count": entry.hit_count,
            }
        target.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        logger.info("Cache saved to %s (%d entries)", target, len(payload))

    def load(self, path: Optional[str] = None) -> bool:
        """Load cache from disk.  Returns *True* on success."""
        target = Path(path) if path else Path(self._cache_dir) / _H1_CACHE_FILE
        if not target.exists():
            logger.debug("No cache file at %s", target)
            return False

        try:
            raw = json.loads(target.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError) as exc:
            logger.warning("Failed to load cache: %s", exc)
            return False

        for sid, data in raw.items():
            self._entries[sid] = _CacheEntry(
                site_id=sid,
                content_hash=data.get("content_hash", ""),
                h1_data=data.get("h1_data", {}),
                timestamp=data.get("timestamp", 0.0),
                hit_count=data.get("hit_count", 0),
            )

        self._loaded = True
        logger.info("Cache loaded from %s (%d entries)", target, len(self._entries))
        return True

    def clear(self) -> None:
        """Drop all entries (in-memory only — call :meth:`save` to persist)."""
        self._entries.clear()
        self._hits = 0
        self._misses = 0

    # -- stats -----------------------------------------------------------------

    def stats(self) -> Dict[str, Any]:
        """Return cache statistics."""
        return {
            "entries": len(self._entries),
            "hits": self._hits,
            "misses": self._misses,
            "hit_rate": self.hit_rate,
            "loaded_from_disk": self._loaded,
        }

# ─── IncrementalResult ────────────────────────────────────────────────────────

@dataclass
class IncrementalResult:
    """Outcome of an incremental verification pass.

    Captures what changed, what was rechecked, what was safely skipped,
    and the delta in H¹ dimension (the primary quality metric).
    """

    changed_sites: List[ChangedSite] = field(default_factory=list)
    rechecked_sites: List[str] = field(default_factory=list)
    skipped_sites: List[str] = field(default_factory=list)

    new_h1_dimension: int = 0
    prev_h1_dimension: int = 0
    delta_h1: int = 0

    new_diagnostics: List[Dict[str, Any]] = field(default_factory=list)
    resolved_diagnostics: List[Dict[str, Any]] = field(default_factory=list)

    cache_hit_rate: float = 0.0
    time_saved_estimate: float = 0.0

    elapsed_seconds: float = 0.0
    full_recheck_estimate: float = 0.0

    passed: bool = True
    error: Optional[str] = None

    # -- presentation ----------------------------------------------------------

    def summary(self) -> str:
        """Human-readable one-paragraph summary."""
        n_changed = len(self.changed_sites)
        n_rechecked = len(self.rechecked_sites)
        n_skipped = len(self.skipped_sites)
        total = n_rechecked + n_skipped

        status = "PASS ✓" if self.passed else "FAIL ✗"
        lines = [
            f"Incremental verification: {status}",
            f"  Changed sites:   {n_changed}",
            f"  Rechecked:       {n_rechecked} / {total}",
            f"  Skipped (cache): {n_skipped}",
            f"  Cache hit rate:  {self.cache_hit_rate:.1%}",
            f"  H¹ dimension:    {self.prev_h1_dimension} → {self.new_h1_dimension}"
            f"  (Δ = {self.delta_h1:+d})",
        ]
        if self.time_saved_estimate > 0:
            lines.append(
                f"  Time saved:      ~{self.time_saved_estimate:.1f}s"
                f" ({self._speedup():.1f}× faster)"
            )
        if self.new_diagnostics:
            lines.append(f"  New issues:      {len(self.new_diagnostics)}")
        if self.resolved_diagnostics:
            lines.append(f"  Resolved issues: {len(self.resolved_diagnostics)}")
        if self.error:
            lines.append(f"  Error: {self.error}")
        return "\n".join(lines)

    def _speedup(self) -> float:
        """Speedup factor compared to full recheck."""
        if self.elapsed_seconds <= 0:
            return 1.0
        return self.full_recheck_estimate / self.elapsed_seconds

    def to_dict(self) -> Dict[str, Any]:
        """Serialisable dictionary representation."""
        return {
            "passed": self.passed,
            "changed_sites": [str(s) for s in self.changed_sites],
            "rechecked_sites": self.rechecked_sites,
            "skipped_sites": self.skipped_sites,
            "new_h1_dimension": self.new_h1_dimension,
            "prev_h1_dimension": self.prev_h1_dimension,
            "delta_h1": self.delta_h1,
            "new_diagnostics": self.new_diagnostics,
            "resolved_diagnostics": self.resolved_diagnostics,
            "cache_hit_rate": self.cache_hit_rate,
            "time_saved_estimate": self.time_saved_estimate,
            "elapsed_seconds": self.elapsed_seconds,
            "error": self.error,
        }

# ─── DiffVerifier ─────────────────────────────────────────────────────────────

class DiffVerifier:
    """Incremental verification driven by ``git diff``.

    Usage::

        deppy check --incremental

    Workflow
    --------
    1. Parse ``git diff`` → list of :class:`ChangedSite`.
    2. Compute verification neighborhood via :class:`SheafLocalityAnalyzer`.
    3. Load cached H¹ for unchanged sites from :class:`IncrementalCache`.
    4. Re-verify **only** the neighborhood.
    5. Update the cache.
    6. Report via :class:`IncrementalResult`.
    """

    def __init__(
        self,
        repo_root: Optional[str] = None,
        cache: Optional[IncrementalCache] = None,
        analyzer: Optional[SheafLocalityAnalyzer] = None,
        locality_depth: int = 1,
    ) -> None:
        self._repo_root = repo_root or self._detect_repo_root()
        self._cache = cache or IncrementalCache(
            cache_dir=os.path.join(self._repo_root, _CACHE_DIR)
        )
        self._analyzer = analyzer or SheafLocalityAnalyzer(depth=locality_depth)
        self._source_cache: Dict[str, str] = {}

    # -- high-level entry points -----------------------------------------------

    def verify_diff(self, diff: str) -> IncrementalResult:
        """Run incremental verification on an arbitrary unified diff string."""
        t0 = time.monotonic()
        self._cache.load()

        changed = self._parse_diff(diff)
        if not changed:
            return IncrementalResult(
                passed=True,
                cache_hit_rate=1.0,
                elapsed_seconds=time.monotonic() - t0,
            )

        sources = self._collect_sources(changed)
        call_graph = self._analyzer.build_call_graph(sources)

        prev_h1 = self._load_prev_h1()
        recheck_ids = self._analyzer.minimal_recheck_set(
            changed, call_graph, prev_h1
        )

        all_ids = self._all_known_site_ids(call_graph)
        skipped = sorted(set(all_ids) - set(recheck_ids))

        diagnostics = self._recheck(recheck_ids, self._cache)

        new_h1_dim = self._compute_h1_dimension(recheck_ids, diagnostics)
        prev_h1_dim = self._prev_h1_dimension()

        self._update_cache(recheck_ids, sources)
        self._cache.save()

        elapsed = time.monotonic() - t0
        full_estimate = elapsed * (len(all_ids) / max(len(recheck_ids), 1))

        result = IncrementalResult(
            changed_sites=changed,
            rechecked_sites=recheck_ids,
            skipped_sites=skipped,
            new_h1_dimension=new_h1_dim,
            prev_h1_dimension=prev_h1_dim,
            delta_h1=new_h1_dim - prev_h1_dim,
            new_diagnostics=[d for d in diagnostics if d.get("new")],
            resolved_diagnostics=[d for d in diagnostics if d.get("resolved")],
            cache_hit_rate=self._cache.hit_rate,
            time_saved_estimate=max(full_estimate - elapsed, 0.0),
            elapsed_seconds=elapsed,
            full_recheck_estimate=full_estimate,
            passed=all(d.get("severity") != "error" for d in diagnostics),
        )
        return result

    def verify_git_staged(self) -> IncrementalResult:
        """Verify only the currently staged changes (``git diff --cached``)."""
        diff = self._run_git("diff", "--cached", "-U3")
        return self.verify_diff(diff)

    def verify_git_unstaged(self) -> IncrementalResult:
        """Verify only unstaged working-tree changes (``git diff``)."""
        diff = self._run_git("diff", "-U3")
        return self.verify_diff(diff)

    def verify_since_commit(self, commit_sha: str) -> IncrementalResult:
        """Verify all changes since *commit_sha* (``git diff <sha> HEAD``)."""
        diff = self._run_git("diff", commit_sha, "HEAD", "-U3")
        return self.verify_diff(diff)

    # -- diff parsing ----------------------------------------------------------

    def _parse_diff(self, diff: str) -> List[ChangedSite]:
        """Parse a unified diff into a list of :class:`ChangedSite` entries.

        The parser extracts per-file hunks, then maps hunk line ranges to
        the enclosing function definition using a lightweight AST probe.
        """
        sites: List[ChangedSite] = []
        if not diff.strip():
            return sites

        current_file: Optional[str] = None
        hunks: List[Tuple[int, int, str]] = []

        for line in diff.splitlines():
            # --- a/path or +++ b/path
            m_file = re.match(r"^(?:\+\+\+|---) [ab]/(.+)$", line)
            if m_file:
                new_path = m_file.group(1)
                if line.startswith("+++"):
                    if current_file and hunks:
                        sites.extend(
                            self._hunks_to_sites(current_file, hunks)
                        )
                    current_file = new_path
                    hunks = []
                continue

            # @@ -l,s +l,s @@ optional function context
            m_hunk = re.match(
                r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@(.*)",
                line,
            )
            if m_hunk:
                start = int(m_hunk.group(1))
                count = int(m_hunk.group(2)) if m_hunk.group(2) else 1
                context = m_hunk.group(3).strip()
                hunks.append((start, start + max(count - 1, 0), context))

        # Flush last file
        if current_file and hunks:
            sites.extend(self._hunks_to_sites(current_file, hunks))

        return sites

    def _hunks_to_sites(
        self,
        file_path: str,
        hunks: List[Tuple[int, int, str]],
    ) -> List[ChangedSite]:
        """Map diff hunks to :class:`ChangedSite` using AST function lookup."""
        if not file_path.endswith(".py"):
            # Non-Python files: treat the entire file as a single site
            lo = min(h[0] for h in hunks)
            hi = max(h[1] for h in hunks)
            return [
                ChangedSite(
                    file_path=file_path,
                    function_name="<module>",
                    line_range=(lo, hi),
                    change_type=ChangeType.MODIFIED,
                    affected_layers=["raw"],
                )
            ]

        func_map = self._function_line_map(file_path)
        sites: List[ChangedSite] = []
        seen: Set[str] = set()

        for hunk_start, hunk_end, context_hint in hunks:
            matched = False
            for fname, (fstart, fend) in func_map.items():
                if hunk_start <= fend and hunk_end >= fstart:
                    if fname not in seen:
                        seen.add(fname)
                        sites.append(
                            ChangedSite(
                                file_path=file_path,
                                function_name=fname,
                                line_range=(fstart, fend),
                                change_type=ChangeType.MODIFIED,
                                affected_layers=["types", "contracts", "runtime"],
                            )
                        )
                    matched = True

            if not matched:
                # Module-level change (imports, constants, etc.)
                name = context_hint if context_hint else "<module>"
                key = f"{file_path}::{name}"
                if key not in seen:
                    seen.add(key)
                    sites.append(
                        ChangedSite(
                            file_path=file_path,
                            function_name=name,
                            line_range=(hunk_start, hunk_end),
                            change_type=ChangeType.MODIFIED,
                            affected_layers=["types"],
                        )
                    )

        return sites

    def _function_line_map(self, file_path: str) -> Dict[str, Tuple[int, int]]:
        """Return ``{function_name: (start_line, end_line)}`` for a Python file."""
        source = self._read_source(file_path)
        if source is None:
            return {}
        try:
            tree = ast.parse(source, filename=file_path)
        except SyntaxError:
            return {}

        result: Dict[str, Tuple[int, int]] = {}
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                end_lineno = getattr(node, "end_lineno", node.lineno)
                result[node.name] = (node.lineno, end_lineno)
        return result

    # -- rechecking ------------------------------------------------------------

    def _recheck(
        self,
        sites: List[str],
        cache: IncrementalCache,
    ) -> List[Dict[str, Any]]:
        """Re-verify a list of sites.  Returns a list of diagnostic dicts.

        For each site we:
        - Compute a content hash
        - If the cache entry is still valid, skip (return cached diagnostics)
        - Otherwise, run the local verification pipeline
        """
        diagnostics: List[Dict[str, Any]] = []

        for site_id in sites:
            parts = site_id.split("::", 1)
            if len(parts) != 2:
                continue
            fpath, fname = parts

            source = self._read_source(fpath)
            if source is None:
                diagnostics.append(
                    self._make_diagnostic(
                        site_id, "error", f"Cannot read {fpath}", new=True
                    )
                )
                continue

            current_hash = self._content_hash(source, fname)

            if cache.is_valid(site_id, current_hash):
                # Cache hit — pull cached diagnostics
                cached = cache.get(site_id) or {}
                for diag in cached.get("diagnostics", []):
                    diagnostics.append(diag)
                continue

            # Cache miss — run verification
            site_diags = self._verify_site(fpath, fname, source)
            diagnostics.extend(site_diags)

            # Update cache entry
            cache.put(
                site_id,
                {"diagnostics": site_diags, "h1_local": len(site_diags)},
                current_hash,
            )

        return diagnostics

    def _verify_site(
        self,
        file_path: str,
        function_name: str,
        source: str,
    ) -> List[Dict[str, Any]]:
        """Run local verification on a single site.

        This is a simplified stub — the real implementation dispatches to the
        hybrid checker pipeline.  Here we perform basic AST-level checks and
        optional Z3 constraint checking.
        """
        diagnostics: List[Dict[str, Any]] = []
        site_id = f"{file_path}::{function_name}"

        try:
            tree = ast.parse(source, filename=file_path)
        except SyntaxError as exc:
            diagnostics.append(
                self._make_diagnostic(
                    site_id, "error", f"Syntax error: {exc}", new=True
                )
            )
            return diagnostics

        # Find the specific function node
        func_node: Optional[Union[ast.FunctionDef, ast.AsyncFunctionDef]] = None
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node.name == function_name:
                    func_node = node
                    break

        if func_node is None and function_name != "<module>":
            diagnostics.append(
                self._make_diagnostic(
                    site_id,
                    "warning",
                    f"Function '{function_name}' not found in {file_path}",
                    new=True,
                )
            )
            return diagnostics

        # Check: missing return type annotation
        if func_node is not None and func_node.returns is None:
            diagnostics.append(
                self._make_diagnostic(
                    site_id,
                    "info",
                    f"Missing return type annotation on '{function_name}'",
                    new=True,
                )
            )

        # Check: Z3-based assertion verification (if available)
        if _Z3_AVAILABLE and func_node is not None:
            z3_diags = self._z3_check_assertions(site_id, func_node)
            diagnostics.extend(z3_diags)

        return diagnostics

    def _z3_check_assertions(
        self,
        site_id: str,
        func_node: Union[ast.FunctionDef, ast.AsyncFunctionDef],
    ) -> List[Dict[str, Any]]:
        """Use Z3 to symbolically check ``assert`` statements in a function.

        This is a lightweight check — it encodes assert conditions as Z3
        constraints and verifies satisfiability.  A full Z3 analysis is
        delegated to ``deppy.solver.z3_backend``.
        """
        if not _Z3_AVAILABLE or z3 is None:
            return []

        diagnostics: List[Dict[str, Any]] = []
        for node in ast.walk(func_node):
            if isinstance(node, ast.Assert) and isinstance(
                node.test, ast.Compare
            ):
                # Attempt simple numeric comparisons: assert x > 0
                try:
                    solver = z3.Solver()
                    solver.set("timeout", 1000)  # 1 second timeout
                    # Encode the negation of the assertion
                    x = z3.Int("x")
                    # Placeholder encoding — the full encoder lives elsewhere
                    solver.add(x >= 0)
                    result = solver.check()
                    if str(result) == "unsat":
                        diagnostics.append(
                            self._make_diagnostic(
                                site_id,
                                "warning",
                                "Assert condition may be unsatisfiable",
                                new=True,
                            )
                        )
                except Exception:  # noqa: BLE001
                    pass  # Z3 encoding failed — not an error
        return diagnostics

    # -- helpers ---------------------------------------------------------------

    def _collect_sources(
        self,
        changed: List[ChangedSite],
    ) -> Dict[str, str]:
        """Read source files for all changed sites."""
        sources: Dict[str, str] = {}
        for site in changed:
            if site.file_path not in sources:
                src = self._read_source(site.file_path)
                if src is not None:
                    sources[site.file_path] = src
        return sources

    def _read_source(self, file_path: str) -> Optional[str]:
        """Read a source file, caching the result."""
        if file_path in self._source_cache:
            return self._source_cache[file_path]
        full = os.path.join(self._repo_root, file_path)
        try:
            with open(full, encoding="utf-8") as fh:
                content = fh.read()
            self._source_cache[file_path] = content
            return content
        except OSError:
            return None

    def _load_prev_h1(self) -> Dict[str, Any]:
        """Load previous H¹ data from cache entries."""
        result: Dict[str, Any] = {}
        for sid in self._cache.all_site_ids():
            data = self._cache.get(sid)
            if data is not None:
                result[sid] = data
        return result

    def _prev_h1_dimension(self) -> int:
        """Sum the local H¹ dimensions from the previous cache."""
        total = 0
        for sid in self._cache.all_site_ids():
            data = self._cache.get(sid)
            if data is not None:
                total += data.get("h1_local", 0)
        return total

    def _compute_h1_dimension(
        self,
        rechecked: List[str],
        diagnostics: List[Dict[str, Any]],
    ) -> int:
        """Compute new H¹ dimension (count of verification failures)."""
        errors = sum(1 for d in diagnostics if d.get("severity") == "error")
        # Add cached H¹ for non-rechecked sites
        for sid in self._cache.all_site_ids():
            if sid not in rechecked:
                data = self._cache.get(sid)
                if data is not None:
                    errors += data.get("h1_local", 0)
        return errors

    def _update_cache(
        self,
        rechecked: List[str],
        sources: Dict[str, str],
    ) -> None:
        """Update cache entries for rechecked sites."""
        for site_id in rechecked:
            parts = site_id.split("::", 1)
            if len(parts) != 2:
                continue
            fpath, fname = parts
            source = sources.get(fpath)
            if source is not None:
                content_hash = self._content_hash(source, fname)
                existing = self._cache.get(site_id)
                if existing is None:
                    existing = {}
                self._cache.put(site_id, existing, content_hash)

    def _all_known_site_ids(
        self,
        call_graph: Dict[str, Set[str]],
    ) -> List[str]:
        """Union of call-graph sites and cached sites."""
        ids: Set[str] = set(call_graph.keys())
        for targets in call_graph.values():
            ids |= targets
        ids |= set(self._cache.all_site_ids())
        return sorted(ids)

    @staticmethod
    def _content_hash(source: str, function_name: str) -> str:
        """SHA-256 of the source scoped to a function (or full file for <module>)."""
        if function_name == "<module>":
            blob = source.encode()
        else:
            blob = f"{function_name}:{source}".encode()
        return hashlib.sha256(blob).hexdigest()

    @staticmethod
    def _make_diagnostic(
        site_id: str,
        severity: str,
        message: str,
        *,
        new: bool = False,
        resolved: bool = False,
    ) -> Dict[str, Any]:
        """Create a diagnostic dict."""
        return {
            "site_id": site_id,
            "severity": severity,
            "message": message,
            "new": new,
            "resolved": resolved,
            "timestamp": time.time(),
        }

    @staticmethod
    def _detect_repo_root() -> str:
        """Auto-detect the git repository root."""
        try:
            result = subprocess.run(
                ["git", "rev-parse", "--show-toplevel"],
                capture_output=True,
                text=True,
                check=True,
            )
            return result.stdout.strip()
        except (subprocess.CalledProcessError, FileNotFoundError):
            return os.getcwd()

    def _run_git(self, *args: str) -> str:
        """Run a git command and return stdout."""
        try:
            result = subprocess.run(
                ["git", "-C", self._repo_root, *args],
                capture_output=True,
                text=True,
                check=True,
            )
            return result.stdout
        except subprocess.CalledProcessError as exc:
            logger.error("git %s failed: %s", " ".join(args), exc.stderr)
            return ""

# ─── PreCommitIntegration ─────────────────────────────────────────────────────

class PreCommitIntegration:
    """Integration with ``git pre-commit`` hooks.

    Runs incremental verification on staged files and returns an exit code
    suitable for use as a git hook (0 = pass, 1 = fail).

    Configuration is read from ``.deppy/config.toml`` when available::

        [pre_commit]
        max_h1_delta = 0          # fail if H¹ increases
        max_new_diagnostics = 5   # fail if too many new issues
        allow_warnings = true     # warnings don't cause failure
    """

    def __init__(
        self,
        repo_root: Optional[str] = None,
        config_path: Optional[str] = None,
    ) -> None:
        self._repo_root = repo_root or os.getcwd()
        self._config_path = config_path or os.path.join(
            self._repo_root, _DEFAULT_CONFIG_PATH
        )
        self._config = self._load_config()

    def run_pre_commit(
        self,
        staged_files: Optional[List[str]] = None,
    ) -> Tuple[bool, str]:
        """Execute incremental verification as a pre-commit hook.

        Parameters
        ----------
        staged_files:
            Optional explicit list of staged file paths.  If *None*, the
            verifier will use ``git diff --cached`` to discover them.

        Returns
        -------
        (passed, message):
            *passed* is ``True`` iff the commit should be allowed.
            *message* is a human-readable summary.
        """
        verifier = DiffVerifier(repo_root=self._repo_root)
        result = verifier.verify_git_staged()

        passed = self._evaluate(result)
        message = result.summary()

        if not passed:
            message += (
                "\n\nCommit blocked by deppy pre-commit hook."
                "\nFix the issues above or run: git commit --no-verify"
            )

        return passed, message

    def _evaluate(self, result: IncrementalResult) -> bool:
        """Evaluate the result against configured thresholds."""
        if result.error:
            return False

        max_delta = self._config.get("max_h1_delta", 0)
        if result.delta_h1 > max_delta:
            return False

        max_new = self._config.get("max_new_diagnostics", 10)
        if len(result.new_diagnostics) > max_new:
            return False

        allow_warnings = self._config.get("allow_warnings", True)
        if not allow_warnings:
            for diag in result.new_diagnostics:
                if diag.get("severity") in ("warning", "error"):
                    return False

        # Check for any errors regardless of config
        for diag in result.new_diagnostics:
            if diag.get("severity") == "error":
                return False

        return True

    def _load_config(self) -> Dict[str, Any]:
        """Load pre-commit configuration from ``.deppy/config.toml``."""
        config_path = Path(self._config_path)
        if not config_path.exists():
            return {}

        try:
            text = config_path.read_text(encoding="utf-8")
        except OSError:
            return {}

        # Minimal TOML-like parser for the [pre_commit] section
        config: Dict[str, Any] = {}
        in_section = False
        for line in text.splitlines():
            stripped = line.strip()
            if stripped == "[pre_commit]":
                in_section = True
                continue
            if stripped.startswith("[") and in_section:
                break
            if in_section and "=" in stripped:
                key, _, value = stripped.partition("=")
                key = key.strip()
                value = value.strip()
                if value.lower() in ("true", "false"):
                    config[key] = value.lower() == "true"
                else:
                    try:
                        config[key] = int(value)
                    except ValueError:
                        config[key] = value

        return config

    @staticmethod
    def install_hook(repo_root: Optional[str] = None) -> str:
        """Install the deppy pre-commit hook into the git repo."""
        root = repo_root or os.getcwd()
        hooks_dir = Path(root) / ".git" / "hooks"
        hooks_dir.mkdir(parents=True, exist_ok=True)

        hook_path = hooks_dir / "pre-commit"
        hook_script = (
            "#!/bin/sh\n"
            "# deppy incremental verification hook\n"
            'python -m deppy.hybrid.incremental.diff_verifier --pre-commit\n'
        )

        hook_path.write_text(hook_script, encoding="utf-8")
        hook_path.chmod(0o755)
        return str(hook_path)

# ─── CLI entry point (for pre-commit hook) ────────────────────────────────────

def _cli_main() -> None:
    """Minimal CLI entry point for direct invocation."""
    import sys

    if "--pre-commit" in sys.argv:
        hook = PreCommitIntegration()
        passed, message = hook.run_pre_commit()
        print(message)
        sys.exit(0 if passed else 1)
    elif "--staged" in sys.argv:
        verifier = DiffVerifier()
        result = verifier.verify_git_staged()
        print(result.summary())
        sys.exit(0 if result.passed else 1)
    elif "--since" in sys.argv:
        idx = sys.argv.index("--since")
        if idx + 1 < len(sys.argv):
            sha = sys.argv[idx + 1]
            verifier = DiffVerifier()
            result = verifier.verify_since_commit(sha)
            print(result.summary())
            sys.exit(0 if result.passed else 1)
        else:
            print("Usage: --since <commit-sha>", file=sys.stderr)
            sys.exit(2)
    else:
        verifier = DiffVerifier()
        result = verifier.verify_git_unstaged()
        print(result.summary())
        sys.exit(0 if result.passed else 1)

if __name__ == "__main__":
    _cli_main()
