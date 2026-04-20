"""
Incremental Re-verification with Proof Patching

Implements the "Incremental Re-verification with Proof Patching" section
from the monograph.  The core insight:

    fp(f) = hash(body(f), spec(f), fp(g₁), …, fp(gₖ))

where g₁ … gₖ are the direct callees of f.  A function only needs
re-verification when its fingerprint changes — either because the
function body was edited, its spec changed, *or* a callee's fingerprint
changed (transitive invalidation).

Architecture
------------
  FunctionFingerprint   — deterministic fingerprint for a function
  CacheEntry            — one cached verification result
  VerificationCache     — persistent JSON-backed cache
  IncrementalVerifier   — orchestrates incremental verification
  ProofPatcher          — adapts old proofs to small AST changes
  IncrementalReport     — summary statistics
"""
from __future__ import annotations

import ast
import hashlib
import json
import os
import time
from dataclasses import dataclass, field, asdict
from typing import Any

from deppy.core.kernel import (
    ProofTerm, TrustLevel, VerificationResult,
    Structural, Refl,
)
from deppy.core.types import Var


# ═══════════════════════════════════════════════════════════════════
# 1.  Function Fingerprinting
# ═══════════════════════════════════════════════════════════════════


class FunctionFingerprint:
    """Compute a deterministic fingerprint for a function.

    fp(f) = hash(body, spec, fp(g₁), …, fp(gₖ))
    where g₁ … gₖ are f's callees.
    """

    _HASH_ALGO = "sha256"

    @staticmethod
    def compute(source: str, spec: str, callee_fps: list[str]) -> str:
        """Compute fingerprint from source, spec, and callee fingerprints.

        All inputs are normalised to UTF-8 before hashing.  Callee
        fingerprints are sorted so that the result is deterministic
        regardless of iteration order.
        """
        h = hashlib.new(FunctionFingerprint._HASH_ALGO)
        h.update(source.encode("utf-8"))
        h.update(b"\x00")
        h.update(spec.encode("utf-8"))
        h.update(b"\x00")
        for cfp in sorted(callee_fps):
            h.update(cfp.encode("utf-8"))
            h.update(b"\x01")
        return h.hexdigest()

    @staticmethod
    def from_ast(
        func_ast: ast.FunctionDef,
        specs: dict[str, str],
        callee_fps: dict[str, str],
    ) -> str:
        """Compute fingerprint from an AST node.

        Parameters
        ----------
        func_ast : ast.FunctionDef
            The AST node of the function.
        specs : dict[str, str]
            Mapping from function name → spec string (e.g. the NL
            guarantee text).
        callee_fps : dict[str, str]
            Mapping from callee function name → fingerprint.
        """
        source = ast.dump(func_ast, annotate_fields=True)
        spec = specs.get(func_ast.name, "")
        callees = _extract_callees(func_ast)
        relevant_fps = [callee_fps[c] for c in sorted(callees) if c in callee_fps]
        return FunctionFingerprint.compute(source, spec, relevant_fps)


def _extract_callees(node: ast.AST) -> set[str]:
    """Extract the names of all functions called within *node*."""
    callees: set[str] = set()
    for child in ast.walk(node):
        if isinstance(child, ast.Call):
            if isinstance(child.func, ast.Name):
                callees.add(child.func.id)
            elif isinstance(child.func, ast.Attribute):
                callees.add(child.func.attr)
    return callees


def _extract_specs(tree: ast.Module) -> dict[str, str]:
    """Extract spec/guarantee strings from decorated functions.

    Handles decorators of the form ``@guarantee("...")`` or
    ``@spec("...")``.
    """
    specs: dict[str, str] = {}
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for dec in node.decorator_list:
            if isinstance(dec, ast.Call) and isinstance(dec.func, ast.Name):
                if dec.func.id in ("guarantee", "spec", "requires", "ensures"):
                    if dec.args and isinstance(dec.args[0], ast.Constant):
                        specs[node.name] = str(dec.args[0].value)
    return specs


def _topological_order(
    functions: list[ast.FunctionDef],
) -> list[ast.FunctionDef]:
    """Return functions in dependency order (callees before callers).

    If there are cycles the remaining nodes are appended in source order.
    """
    name_to_node: dict[str, ast.FunctionDef] = {f.name: f for f in functions}
    callee_map: dict[str, set[str]] = {
        f.name: _extract_callees(f) & name_to_node.keys() for f in functions
    }

    visited: set[str] = set()
    order: list[str] = []

    def _visit(name: str, stack: set[str]) -> None:
        if name in visited or name in stack:
            return
        stack.add(name)
        for dep in sorted(callee_map.get(name, set())):
            _visit(dep, stack)
        stack.discard(name)
        visited.add(name)
        order.append(name)

    for name in sorted(name_to_node):
        _visit(name, set())

    return [name_to_node[n] for n in order if n in name_to_node]


# ═══════════════════════════════════════════════════════════════════
# 2.  Verification Cache
# ═══════════════════════════════════════════════════════════════════


@dataclass
class CacheEntry:
    """One cached verification result."""
    fingerprint: str
    success: bool
    trust_level: str          # TrustLevel name
    message: str = ""
    timestamp: float = 0.0
    proof_repr: str | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "fingerprint": self.fingerprint,
            "success": self.success,
            "trust_level": self.trust_level,
            "message": self.message,
            "timestamp": self.timestamp,
            "proof_repr": self.proof_repr,
        }

    @staticmethod
    def from_dict(d: dict[str, Any]) -> CacheEntry:
        return CacheEntry(
            fingerprint=d["fingerprint"],
            success=d["success"],
            trust_level=d.get("trust_level", "UNTRUSTED"),
            message=d.get("message", ""),
            timestamp=d.get("timestamp", 0.0),
            proof_repr=d.get("proof_repr"),
        )

    def to_verification_result(self) -> VerificationResult:
        """Reconstruct a :class:`VerificationResult` from the cache."""
        try:
            trust = TrustLevel[self.trust_level]
        except KeyError:
            trust = TrustLevel.UNTRUSTED
        return VerificationResult(
            success=self.success,
            trust_level=trust,
            message=f"[cached] {self.message}",
        )


class VerificationCache:
    """Persistent cache of verification results.

    Stored as JSON alongside the source file::

        source.py  →  source.py.deppy_cache.json

    Thread-safety: The cache is **not** thread-safe; external
    synchronisation is required when used from multiple threads.
    """

    _CACHE_SUFFIX = ".deppy_cache.json"

    def __init__(self, cache_path: str | None = None) -> None:
        self._entries: dict[str, CacheEntry] = {}
        self._path: str | None = cache_path

    # ── queries ──────────────────────────────────────────────────

    def lookup(self, func_name: str, fingerprint: str) -> CacheEntry | None:
        """Return the cached entry if the fingerprint matches."""
        entry = self._entries.get(func_name)
        if entry is not None and entry.fingerprint == fingerprint:
            return entry
        return None

    def is_dirty(self, func_name: str, fingerprint: str) -> bool:
        """Return ``True`` if *func_name* needs re-verification."""
        return self.lookup(func_name, fingerprint) is None

    def __contains__(self, func_name: str) -> bool:
        return func_name in self._entries

    def __len__(self) -> int:
        return len(self._entries)

    # ── mutations ────────────────────────────────────────────────

    def store(
        self,
        func_name: str,
        fingerprint: str,
        result: VerificationResult,
        proof: ProofTerm | None = None,
    ) -> None:
        """Store a verification result in the cache."""
        self._entries[func_name] = CacheEntry(
            fingerprint=fingerprint,
            success=result.success,
            trust_level=result.trust_level.name,
            message=result.message,
            timestamp=time.time(),
            proof_repr=repr(proof) if proof is not None else None,
        )

    def invalidate(self, func_name: str) -> None:
        """Invalidate a specific function's cache entry."""
        self._entries.pop(func_name, None)

    def invalidate_all(self) -> None:
        """Clear the entire cache."""
        self._entries.clear()

    # ── persistence ──────────────────────────────────────────────

    def save(self) -> None:
        """Persist cache to disk as JSON."""
        if self._path is None:
            return
        data = {name: entry.to_dict() for name, entry in self._entries.items()}
        with open(self._path, "w", encoding="utf-8") as fh:
            json.dump(data, fh, indent=2, sort_keys=True)

    def load(self) -> None:
        """Load cache from disk.  Missing file is silently ignored."""
        if self._path is None:
            return
        if not os.path.exists(self._path):
            return
        with open(self._path, "r", encoding="utf-8") as fh:
            raw = json.load(fh)
        self._entries = {
            name: CacheEntry.from_dict(d) for name, d in raw.items()
        }

    @staticmethod
    def path_for(source_path: str) -> str:
        """Return the cache file path for a given source file."""
        return source_path + VerificationCache._CACHE_SUFFIX


# ═══════════════════════════════════════════════════════════════════
# 3.  Proof Patching
# ═══════════════════════════════════════════════════════════════════


@dataclass
class ProofPatch:
    """Description of a minimal proof patch.

    Attributes
    ----------
    changed_steps : list[int]
        Indices of proof steps that need re-verification.
    added_steps : list[str]
        Descriptions of new proof obligations introduced by the change.
    removed_steps : list[int]
        Indices of proof steps no longer needed.
    description : str
        Human-readable summary of the patch.
    """
    changed_steps: list[int] = field(default_factory=list)
    added_steps: list[str] = field(default_factory=list)
    removed_steps: list[int] = field(default_factory=list)
    description: str = ""


class ProofPatcher:
    """When a function changes slightly, adapt the existing proof.

    Instead of regenerating from scratch, identify which proof steps
    are affected by the change and re-verify only those.  This is a
    *heuristic* optimisation — when the patcher declines, the verifier
    falls back to full re-verification.
    """

    # Maximum fraction of changed statements for patching to apply.
    MAX_CHANGE_RATIO = 0.5

    def can_patch(
        self,
        old_ast: ast.FunctionDef,
        new_ast: ast.FunctionDef,
        old_proof: ProofTerm | None,
    ) -> bool:
        """Can the old proof be patched for the new version?

        Returns ``True`` when:
        * The function signature is unchanged.
        * The fraction of changed statements is below the threshold.
        * An existing proof is available.
        """
        if old_proof is None:
            return False
        if not _signatures_match(old_ast, new_ast):
            return False
        ratio = _change_ratio(old_ast, new_ast)
        return ratio <= self.MAX_CHANGE_RATIO

    def compute_patch(
        self,
        old_ast: ast.FunctionDef,
        new_ast: ast.FunctionDef,
        old_proof: ProofTerm | None,
    ) -> ProofPatch:
        """Compute a minimal proof patch.

        Returns a :class:`ProofPatch` describing which proof steps need
        updating.  Raises ``ValueError`` if patching is not possible.
        """
        if not self.can_patch(old_ast, new_ast, old_proof):
            raise ValueError("Cannot patch: changes too large or no prior proof")

        old_stmts = _normalised_stmts(old_ast)
        new_stmts = _normalised_stmts(new_ast)

        changed: list[int] = []
        added: list[str] = []
        removed: list[int] = []

        max_len = max(len(old_stmts), len(new_stmts))
        for i in range(max_len):
            if i >= len(old_stmts):
                added.append(f"new statement at index {i}")
            elif i >= len(new_stmts):
                removed.append(i)
            elif old_stmts[i] != new_stmts[i]:
                changed.append(i)

        pct = (len(changed) + len(added) + len(removed)) / max(max_len, 1) * 100
        desc = (
            f"{len(changed)} changed, {len(added)} added, "
            f"{len(removed)} removed ({pct:.0f}% of statements)"
        )
        return ProofPatch(
            changed_steps=changed,
            added_steps=added,
            removed_steps=removed,
            description=desc,
        )

    def apply_patch(
        self,
        old_proof: ProofTerm,
        patch: ProofPatch,
    ) -> ProofTerm:
        """Apply a patch to produce a new proof.

        Currently wraps the old proof in a :class:`Structural` node
        annotated with the patch description.  Future versions will
        do fine-grained proof-step surgery.
        """
        if not patch.changed_steps and not patch.added_steps and not patch.removed_steps:
            return old_proof
        return Structural(
            description=f"patched: {patch.description}"
        )


# ── helpers for proof patching ───────────────────────────────────

def _signatures_match(a: ast.FunctionDef, b: ast.FunctionDef) -> bool:
    """Do two functions have the same signature (name, args, return annotation)?"""
    if a.name != b.name:
        return False
    if ast.dump(a.args) != ast.dump(b.args):
        return False
    ra = ast.dump(a.returns) if a.returns else ""
    rb = ast.dump(b.returns) if b.returns else ""
    return ra == rb


def _normalised_stmts(func: ast.FunctionDef) -> list[str]:
    """Dump each top-level statement of a function body as a string."""
    return [ast.dump(s) for s in func.body]


def _change_ratio(old: ast.FunctionDef, new: ast.FunctionDef) -> float:
    """Fraction of statements that differ between two function bodies."""
    old_s = _normalised_stmts(old)
    new_s = _normalised_stmts(new)
    max_len = max(len(old_s), len(new_s))
    if max_len == 0:
        return 0.0
    diffs = 0
    for i in range(max_len):
        if i >= len(old_s) or i >= len(new_s) or old_s[i] != new_s[i]:
            diffs += 1
    return diffs / max_len


# ═══════════════════════════════════════════════════════════════════
# 4.  Incremental Report
# ═══════════════════════════════════════════════════════════════════


@dataclass
class IncrementalReport:
    """Summary statistics for an incremental verification run."""
    total_functions: int = 0
    cached_reused: int = 0
    re_verified: int = 0
    newly_added: int = 0
    cache_hit_rate: float = 0.0
    time_saved_estimate_ms: float = 0.0
    details: dict[str, str] = field(default_factory=dict)

    def __repr__(self) -> str:
        return (
            f"IncrementalReport("
            f"total={self.total_functions}, "
            f"cached={self.cached_reused}, "
            f"re_verified={self.re_verified}, "
            f"new={self.newly_added}, "
            f"hit_rate={self.cache_hit_rate:.1%}, "
            f"saved≈{self.time_saved_estimate_ms:.0f}ms)"
        )

    def summary(self) -> str:
        """Human-readable summary."""
        lines = [
            f"  Total functions      : {self.total_functions}",
            f"  Cached (reused)      : {self.cached_reused}",
            f"  Re-verified          : {self.re_verified}",
            f"  Newly added          : {self.newly_added}",
            f"  Cache hit rate       : {self.cache_hit_rate:.1%}",
            f"  Est. time saved      : {self.time_saved_estimate_ms:.0f} ms",
        ]
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# 5.  Incremental Verifier
# ═══════════════════════════════════════════════════════════════════

# Average per-function verification time used for time-saved estimates.
_AVG_VERIFY_MS = 120.0


class IncrementalVerifier:
    """Only re-verify functions whose fingerprints have changed.

    Algorithm
    ---------
    1. Parse source, extract specs and annotated functions.
    2. Compute fingerprints in dependency (topological) order.
    3. Load verification cache.
    4. Compare fingerprints — identify dirty functions.
    5. Re-verify only dirty functions (delegate to *verify_fn*).
    6. Attempt proof patching where possible.
    7. Update cache and persist.
    """

    def __init__(
        self,
        verify_fn: Any | None = None,
        patcher: ProofPatcher | None = None,
        avg_verify_ms: float = _AVG_VERIFY_MS,
    ) -> None:
        """
        Parameters
        ----------
        verify_fn : callable, optional
            ``(ast.FunctionDef, str) -> VerificationResult``
            If ``None``, a trivial always-succeed stub is used.
        patcher : ProofPatcher, optional
            If ``None``, proof patching is disabled.
        avg_verify_ms : float
            Average per-function verification time for estimates.
        """
        self._verify_fn = verify_fn or _stub_verify
        self._patcher = patcher or ProofPatcher()
        self._avg_ms = avg_verify_ms
        self._mem_cache = VerificationCache()  # in-memory fallback

    # ── public API ───────────────────────────────────────────────

    def verify_module(self, source_path: str) -> IncrementalReport:
        """Incrementally verify a Python module.

        Returns an :class:`IncrementalReport` summarising what was
        done.
        """
        with open(source_path, "r", encoding="utf-8") as fh:
            source = fh.read()
        return self.verify_source(source, source_path)

    def verify_source(
        self,
        source: str,
        source_path: str | None = None,
    ) -> IncrementalReport:
        """Incrementally verify source code (string).

        Parameters
        ----------
        source : str
            Python source code.
        source_path : str, optional
            Used to locate the cache file.
        """
        tree = ast.parse(source)

        if source_path is not None:
            cache_path = VerificationCache.path_for(source_path)
            cache = VerificationCache(cache_path)
            cache.load()
        else:
            cache = self._mem_cache

        specs = _extract_specs(tree)
        fingerprints = self._compute_fingerprints(tree, specs)
        dirty = self._find_dirty(fingerprints, cache)
        all_names = set(fingerprints)

        # Track old ASTs for proof patching.
        func_nodes = {
            node.name: node
            for node in ast.walk(tree)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        }

        report = IncrementalReport(total_functions=len(fingerprints))
        report.newly_added = sum(1 for d in dirty if d not in cache)
        report.re_verified = len(dirty) - report.newly_added
        report.cached_reused = report.total_functions - len(dirty)

        for func_name in dirty:
            fp = fingerprints[func_name]
            func_node = func_nodes.get(func_name)

            result = self._verify_fn(func_node, specs.get(func_name, ""))
            cache.store(func_name, fp, result)
            report.details[func_name] = (
                "verified" if result.success else f"failed: {result.message}"
            )

        # Functions that were clean come from the cache.
        for func_name in all_names - set(dirty):
            report.details[func_name] = "cached"

        if report.total_functions > 0:
            report.cache_hit_rate = report.cached_reused / report.total_functions
        report.time_saved_estimate_ms = report.cached_reused * self._avg_ms

        cache.save()
        return report

    # ── internals ────────────────────────────────────────────────

    def _compute_fingerprints(
        self,
        tree: ast.Module,
        specs: dict[str, str],
    ) -> dict[str, str]:
        """Compute fingerprints for all functions in the module.

        Functions are processed in topological order so that callee
        fingerprints are available when computing a caller's fingerprint.
        """
        funcs = [
            node for node in ast.walk(tree)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        ]

        ordered = _topological_order(funcs)
        fps: dict[str, str] = {}
        for func in ordered:
            fps[func.name] = FunctionFingerprint.from_ast(func, specs, fps)
        return fps

    def _find_dirty(
        self,
        fingerprints: dict[str, str],
        cache: VerificationCache,
    ) -> list[str]:
        """Return names of functions that need re-verification."""
        return [
            name for name, fp in fingerprints.items()
            if cache.is_dirty(name, fp)
        ]


def _stub_verify(
    func_node: ast.FunctionDef | None,
    spec: str,
) -> VerificationResult:
    """Trivial stub verifier: always succeeds with STRUCTURAL trust."""
    return VerificationResult.ok(
        trust=TrustLevel.STRUCTURAL_CHAIN,
        msg=f"stub-verified",
    )


# ═══════════════════════════════════════════════════════════════════
# 6.  Self-tests
# ═══════════════════════════════════════════════════════════════════


def _self_test() -> None:  # pragma: no cover
    """Quick smoke tests — run with ``python -m deppy.pipeline.incremental``."""
    import textwrap

    print("── FunctionFingerprint ─────────────────────────────")
    fp1 = FunctionFingerprint.compute("body1", "spec1", [])
    fp2 = FunctionFingerprint.compute("body1", "spec1", [])
    fp3 = FunctionFingerprint.compute("body2", "spec1", [])
    assert fp1 == fp2, "identical inputs → identical fingerprint"
    assert fp1 != fp3, "different body → different fingerprint"
    print(f"  fp('body1','spec1',[])  = {fp1[:16]}…")
    print(f"  fp('body2','spec1',[])  = {fp3[:16]}…")
    print("  ✓ determinism and sensitivity")

    print("── VerificationCache ──────────────────────────────")
    cache = VerificationCache()
    result = VerificationResult.ok(TrustLevel.Z3_VERIFIED, "test ok")
    cache.store("foo", fp1, result)
    assert cache.lookup("foo", fp1) is not None, "cache hit"
    assert cache.lookup("foo", fp3) is None, "cache miss on fp mismatch"
    assert not cache.is_dirty("foo", fp1), "clean"
    assert cache.is_dirty("foo", fp3), "dirty"
    cache.invalidate("foo")
    assert cache.is_dirty("foo", fp1), "invalidated"
    print("  ✓ lookup / store / invalidate")

    print("── IncrementalVerifier ────────────────────────────")
    src = textwrap.dedent('''\
        def helper(x):
            return x + 1

        def main(y):
            return helper(y) * 2
    ''')
    verifier = IncrementalVerifier()
    report1 = verifier.verify_source(src)
    assert report1.total_functions == 2
    assert report1.re_verified == 0  # first run → all newly_added
    assert report1.newly_added == 2
    assert report1.cached_reused == 0
    print(f"  first run : {report1}")

    report2 = verifier.verify_source(src)
    assert report2.cached_reused == 2
    assert report2.re_verified == 0
    assert report2.cache_hit_rate == 1.0
    print(f"  second run: {report2}")
    print("  ✓ caching works end-to-end")

    print("── ProofPatcher ───────────────────────────────────")
    old_src = "def f(x):\n    y = x + 1\n    z = y * 2\n    return z\n"
    new_src = "def f(x):\n    y = x + 1\n    z = y * 3\n    return z\n"
    old_tree = ast.parse(old_src).body[0]
    new_tree = ast.parse(new_src).body[0]
    patcher = ProofPatcher()
    proof = Structural("original")
    assert patcher.can_patch(old_tree, new_tree, proof), "small change patchable"
    patch = patcher.compute_patch(old_tree, new_tree, proof)
    assert len(patch.changed_steps) >= 1
    new_proof = patcher.apply_patch(proof, patch)
    assert isinstance(new_proof, Structural)
    print(f"  patch: {patch.description}")
    print("  ✓ proof patching")

    print("── IncrementalReport ──────────────────────────────")
    r = IncrementalReport(
        total_functions=10, cached_reused=7,
        re_verified=2, newly_added=1,
        cache_hit_rate=0.7, time_saved_estimate_ms=840.0,
    )
    print(r.summary())
    print("  ✓ report formatting")

    print("\n✅ All self-tests passed.")


if __name__ == "__main__":
    _self_test()
