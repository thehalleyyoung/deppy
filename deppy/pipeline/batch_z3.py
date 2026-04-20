"""
Batch Z3 Verification Engine
=============================

Amortizes axiom context across many proof obligations by reusing Z3
solver instances with hierarchical push/pop scoping.  Implements the
"Batch Z3 with Shared Axiom Context" section from the monograph's
*Scalable Verification* chapter.

Architecture
------------
  Z3BatchContext        — manages a single Z3 solver with layered axiom scoping
  AdaptiveTimeout       — computes per-obligation timeouts from formula complexity
  FallbackChain         — timeout → simplify → split → abstract → unresolvable
  BatchStats            — statistics accumulator
  ModuleBatchVerifier   — orchestrates batch verification of an entire module

Axiom hierarchy (innermost is cheapest to push/pop):

  1. **Global context**   — Python language axioms (len ≥ 0, …)
  2. **Library context**  — imported library axioms (one batch per library)
  3. **Module context**   — module-level definitions and invariants
  4. **Function context** — function pre/postconditions (push/pop per function)

All Z3 imports are guarded so the module degrades gracefully when Z3
is not installed.
"""
from __future__ import annotations

import ast
import hashlib
import math
import re
import textwrap
import time
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    Spec, SpecKind, FunctionSpec,
    Var, Literal, PyObjType, PyIntType, PyFloatType, PyStrType,
    PyBoolType, PyNoneType, PyListType, PyCallableType,
    RefinementType, PiType, arrow,
)
from deppy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Z3Proof, Structural, AxiomInvocation, AxiomEntry,
)

# ── guarded Z3 import ─────────────────────────────────────────────
try:
    import z3
    _HAS_Z3 = True
except ImportError:
    z3 = None  # type: ignore[assignment]
    _HAS_Z3 = False


def _require_z3() -> None:
    """Raise at call-sites that cannot function without Z3."""
    if not _HAS_Z3:
        raise RuntimeError(
            "Z3 is required for batch verification but is not installed. "
            "Install with: pip install z3-solver"
        )


# ═══════════════════════════════════════════════════════════════════
# 1.  Data Structures
# ═══════════════════════════════════════════════════════════════════

class FallbackLevel(Enum):
    """Which fallback stage resolved an obligation."""
    DIRECT = 0         # Z3 proved directly
    SIMPLIFIED = 1     # proved after simplification
    SPLIT = 2          # proved after splitting into sub-obligations
    ABSTRACTED = 3     # proved after abstracting complex sub-terms
    UNRESOLVABLE = 4   # Z3 could not resolve — needs LLM oracle


@dataclass
class BatchItem:
    """A single obligation within a batch.

    Parameters
    ----------
    obligation : str
        SMT-LIB-style formula string (``x > 0 and y > 0 implies x + y > 0``).
    function_name : str
        Name of the function this obligation came from.
    module : str
        Dotted module path, e.g. ``"mypackage.util"``.
    preconditions : list[str]
        Additional assertions scoped to this function.
    description : str
        Human-readable label.
    """
    obligation: str
    function_name: str = ""
    module: str = ""
    preconditions: list[str] = field(default_factory=list)
    description: str = ""


@dataclass
class BatchResult:
    """Result of verifying one ``BatchItem``."""
    item: BatchItem
    proved: bool
    fallback_level: FallbackLevel = FallbackLevel.DIRECT
    z3_time_ms: float = 0.0
    error: str | None = None

    def __repr__(self) -> str:
        status = "✓" if self.proved else "✗"
        desc = self.item.description or self.item.obligation[:40]
        return f"{status} [{self.fallback_level.name}] {desc} ({self.z3_time_ms:.1f}ms)"


@dataclass
class FallbackResult:
    """Internal result from :class:`FallbackChain`."""
    proved: bool
    level: FallbackLevel
    z3_time_ms: float = 0.0
    sub_results: list[bool] = field(default_factory=list)
    error: str | None = None


@dataclass
class BatchStats:
    """Accumulated statistics for a batch verification run."""
    total_obligations: int = 0
    resolved_at_level: dict[int, int] = field(
        default_factory=lambda: {0: 0, 1: 0, 2: 0, 3: 0, 4: 0}
    )
    z3_calls: int = 0
    z3_cache_hits: int = 0
    total_z3_time_ms: float = 0.0
    timeouts: int = 0
    axioms_shared: int = 0

    @property
    def proved_count(self) -> int:
        return sum(v for k, v in self.resolved_at_level.items() if k < 4)

    @property
    def unresolvable_count(self) -> int:
        return self.resolved_at_level.get(4, 0)

    def record(self, result: BatchResult) -> None:
        """Absorb a single result into the running statistics."""
        self.total_obligations += 1
        lvl = result.fallback_level.value
        self.resolved_at_level[lvl] = self.resolved_at_level.get(lvl, 0) + 1
        self.total_z3_time_ms += result.z3_time_ms

    def __repr__(self) -> str:
        return (
            f"BatchStats(total={self.total_obligations}, "
            f"proved={self.proved_count}, "
            f"unresolvable={self.unresolvable_count}, "
            f"z3_calls={self.z3_calls}, "
            f"cache_hits={self.z3_cache_hits}, "
            f"timeouts={self.timeouts}, "
            f"axioms_shared={self.axioms_shared}, "
            f"z3_time={self.total_z3_time_ms:.1f}ms)"
        )


@dataclass
class FunctionResult:
    """Batch-verification result for one function."""
    name: str
    obligations: list[BatchResult]
    trust_level: TrustLevel
    duration_ms: float

    @property
    def verified(self) -> bool:
        return all(r.proved for r in self.obligations)

    @property
    def proved_count(self) -> int:
        return sum(1 for r in self.obligations if r.proved)

    def __repr__(self) -> str:
        status = "✓" if self.verified else "✗"
        total = len(self.obligations)
        return (
            f"{status} {self.name}: {self.proved_count}/{total} "
            f"[{self.trust_level.name}] ({self.duration_ms:.1f}ms)"
        )


@dataclass
class ModuleVerificationReport:
    """Aggregate result for an entire module."""
    module_path: str
    functions: list[FunctionResult]
    stats: BatchStats
    duration_ms: float

    @property
    def verified(self) -> bool:
        return all(f.verified for f in self.functions)

    def summary(self) -> str:
        total_fn = len(self.functions)
        ok_fn = sum(1 for f in self.functions if f.verified)
        return (
            f"Module {self.module_path}: {ok_fn}/{total_fn} functions verified "
            f"({self.stats.proved_count}/{self.stats.total_obligations} obligations) "
            f"in {self.duration_ms:.1f}ms"
        )

    def __repr__(self) -> str:
        return self.summary()


# ═══════════════════════════════════════════════════════════════════
# 2.  Adaptive Timeout
# ═══════════════════════════════════════════════════════════════════

# Patterns used to estimate formula complexity
_QUANTIFIER_RE = re.compile(r'\b(forall|exists|ForAll|Exists)\b')
_FUNC_SYMBOL_RE = re.compile(r'\b[a-zA-Z_]\w*\s*\(')
_LET_RE = re.compile(r'\b(let|Let)\b')
_IMPLIES_RE = re.compile(r'\b(implies|Implies|=>)\b')
_NESTED_PARENS_RE = re.compile(r'\(')


class AdaptiveTimeout:
    """Compute per-obligation timeouts based on formula complexity.

    ``timeout(O) = base * (1 + log₂(complexity(O)))``

    where *complexity* counts quantifiers, function symbols, nested
    ``let``-bindings, and parenthetical depth.
    """

    def __init__(self, base_ms: int = 2000, min_ms: int = 500, max_ms: int = 30000):
        self._base_ms = base_ms
        self._min_ms = min_ms
        self._max_ms = max_ms

    def compute_timeout(self, obligation: str) -> int:
        """Return an adaptive timeout in milliseconds."""
        c = self.complexity(obligation)
        if c <= 0:
            return self._base_ms
        raw = self._base_ms * (1.0 + math.log2(max(c, 1)))
        return int(max(self._min_ms, min(raw, self._max_ms)))

    @staticmethod
    def complexity(formula: str) -> int:
        """Estimate formula complexity.

        Counts quantifiers, function applications, let-bindings,
        implications, and nesting depth.
        """
        score = 0
        score += len(_QUANTIFIER_RE.findall(formula)) * 4
        score += len(_FUNC_SYMBOL_RE.findall(formula))
        score += len(_LET_RE.findall(formula)) * 2
        score += len(_IMPLIES_RE.findall(formula))
        # Nesting depth proxy: max count of unmatched open-parens
        depth = 0
        max_depth = 0
        for ch in formula:
            if ch == '(':
                depth += 1
                max_depth = max(max_depth, depth)
            elif ch == ')':
                depth = max(depth - 1, 0)
        score += max_depth
        return score


# ═══════════════════════════════════════════════════════════════════
# 3.  Formula Helpers  (string ↔ Z3)
# ═══════════════════════════════════════════════════════════════════

_ARITH_OPS = {"+", "-", "*", "/", "//", "%", "**"}
_CMP_OPS = {"==", "!=", "<", ">", "<=", ">="}
_LOGIC_OPS = {"and", "or", "not", "implies", "True", "False"}
_BUILTINS = {"len", "abs", "min", "max", "sum"}
_RESERVED = _ARITH_OPS | _CMP_OPS | _LOGIC_OPS | _BUILTINS | {"(", ")", ","}


def _extract_variables(formula: str) -> set[str]:
    """Return free variable names from a simple formula string."""
    tokens = re.findall(r'[a-zA-Z_]\w*', formula)
    return {t for t in tokens if t not in _LOGIC_OPS and t not in _BUILTINS
            and t not in {"int", "float", "str", "bool", "list", "True", "False", "None"}}


def _parse_formula(formula: str, variables: dict[str, Any] | None = None) -> Any:
    """Best-effort parse of a Python-syntax formula into a Z3 expression.

    Falls back to ``z3.BoolVal(False)`` if parsing fails.
    """
    _require_z3()
    var_names = _extract_variables(formula)
    env: dict[str, Any] = {}

    if variables:
        env.update(variables)
    for v in var_names:
        if v not in env:
            env[v] = z3.Int(v)

    env.update({
        "And": z3.And, "Or": z3.Or, "Not": z3.Not,
        "Implies": z3.Implies, "ForAll": z3.ForAll,
        "Exists": z3.Exists, "If": z3.If,
        "True": z3.BoolVal(True), "False": z3.BoolVal(False),
        "implies": lambda a, b: z3.Implies(a, b),
        "abs": lambda x: z3.If(x >= 0, x, -x),
        "len": lambda x: z3.Int("_len_" + str(x)),
        "min": lambda a, b: z3.If(a <= b, a, b),
        "max": lambda a, b: z3.If(a >= b, a, b),
    })

    normalized = formula
    normalized = re.sub(r'\band\b', ' and ', normalized)
    normalized = re.sub(r'\bor\b', ' or ', normalized)
    normalized = re.sub(r'\bnot\b', ' not ', normalized)

    try:
        result = eval(normalized, {"__builtins__": {}}, env)  # noqa: S307
        if isinstance(result, bool):
            return z3.BoolVal(result)
        return result
    except Exception:
        return z3.BoolVal(False)


def _simplify_formula_str(formula: str) -> str:
    """Attempt to algebraically simplify a formula string via Z3."""
    _require_z3()
    try:
        expr = _parse_formula(formula)
        simplified = z3.simplify(expr)
        return str(simplified)
    except Exception:
        return formula


def _split_conjunction(formula: str) -> list[str]:
    """Split a top-level conjunction into parts.

    ``"a > 0 and b > 0 and c > 0"`` → ``["a > 0", "b > 0", "c > 0"]``
    """
    parts = re.split(r'\band\b', formula)
    return [p.strip() for p in parts if p.strip()]


def _abstract_subterms(formula: str) -> str:
    """Replace nested function calls with fresh uninterpreted constants.

    For example ``f(g(x))`` → ``_abs_0`` where ``_abs_0`` is an opaque
    integer.  The caller re-checks the simplified formula.
    """
    counter = 0
    result = formula

    nested_call = re.compile(r'[a-zA-Z_]\w*\s*\([^()]*\)')
    for _ in range(5):
        m = nested_call.search(result)
        if not m:
            break
        placeholder = f"_abs_{counter}"
        result = result[:m.start()] + placeholder + result[m.end():]
        counter += 1
    return result


# ═══════════════════════════════════════════════════════════════════
# 4.  Fallback Chain
# ═══════════════════════════════════════════════════════════════════

class FallbackChain:
    """When Z3 times out, try progressively:

    1. **Simplify + retry** — algebraically simplify and re-check.
    2. **Split** — break conjunction into independent sub-goals.
    3. **Abstract** — replace complex sub-terms with uninterpreted constants.
    4. **Unresolvable** — report as needing LLM oracle.
    """

    def __init__(self, stats: BatchStats | None = None):
        self._stats = stats or BatchStats()

    def try_with_fallback(
        self,
        solver: Any,
        obligation: str,
        timeout_ms: int,
        preconditions: list[str] | None = None,
    ) -> FallbackResult:
        """Attempt to prove *obligation* with progressive fallbacks."""
        # Level 0: direct
        proved, elapsed = self._check(solver, obligation, timeout_ms, preconditions)
        if proved:
            return FallbackResult(proved=True, level=FallbackLevel.DIRECT,
                                  z3_time_ms=elapsed)

        # Level 1: simplify + retry
        simplified = _simplify_formula_str(obligation)
        if simplified != obligation:
            proved, elapsed2 = self._check(solver, simplified, timeout_ms, preconditions)
            elapsed += elapsed2
            if proved:
                return FallbackResult(proved=True, level=FallbackLevel.SIMPLIFIED,
                                      z3_time_ms=elapsed)

        # Level 2: split conjunction
        parts = _split_conjunction(obligation)
        if len(parts) > 1:
            all_ok = True
            sub_results: list[bool] = []
            for part in parts:
                ok, dt = self._check(solver, part, timeout_ms, preconditions)
                elapsed += dt
                sub_results.append(ok)
                if not ok:
                    all_ok = False
                    break
            if all_ok:
                return FallbackResult(proved=True, level=FallbackLevel.SPLIT,
                                      z3_time_ms=elapsed, sub_results=sub_results)

        # Level 3: abstract
        abstracted = _abstract_subterms(obligation)
        if abstracted != obligation:
            proved, elapsed3 = self._check(solver, abstracted, timeout_ms, preconditions)
            elapsed += elapsed3
            if proved:
                return FallbackResult(proved=True, level=FallbackLevel.ABSTRACTED,
                                      z3_time_ms=elapsed)

        # Level 4: unresolvable
        self._stats.timeouts += 1
        return FallbackResult(proved=False, level=FallbackLevel.UNRESOLVABLE,
                              z3_time_ms=elapsed)

    def _check(
        self,
        solver: Any,
        formula_str: str,
        timeout_ms: int,
        preconditions: list[str] | None = None,
    ) -> tuple[bool, float]:
        """Single Z3 check: assert ¬formula, check unsat → proved.

        Returns ``(proved, elapsed_ms)``.
        """
        _require_z3()
        self._stats.z3_calls += 1

        solver.push()
        try:
            solver.set("timeout", timeout_ms)

            if preconditions:
                for pre in preconditions:
                    try:
                        pre_expr = _parse_formula(pre)
                        solver.add(pre_expr)
                    except Exception:
                        pass

            try:
                goal = _parse_formula(formula_str)
                solver.add(z3.Not(goal))
            except Exception:
                return False, 0.0

            t0 = time.perf_counter_ns()
            result = solver.check()
            elapsed = (time.perf_counter_ns() - t0) / 1e6

            if result == z3.unsat:
                return True, elapsed
            return False, elapsed
        finally:
            solver.pop()


# ═══════════════════════════════════════════════════════════════════
# 5.  Z3 Batch Context
# ═══════════════════════════════════════════════════════════════════

# Global (Python-language) axioms expressed as formula strings.
_GLOBAL_AXIOMS: list[str] = [
    "len_x >= 0",             # len(anything) ≥ 0
    "abs_x >= 0",             # abs(anything) ≥ 0
    "idx >= 0",               # list indices ≥ 0 (general shape)
]

# Variables pre-declared for the global axioms.
_GLOBAL_VARS = {
    "len_x": None,   # filled lazily
    "abs_x": None,
    "idx": None,
}


class Z3BatchContext:
    """Manages a Z3 solver with hierarchical axiom scoping.

    Axiom hierarchy
    ---------------
    1. **Global context** — Python language axioms (asserted once per session).
    2. **Library context** — imported library axioms (asserted once per module).
    3. **Module context** — module-level definitions (asserted once per module).
    4. **Function context** — function pre/postconditions (push/pop per fn).

    The solver is lazily initialised on first use so importing this module
    never triggers Z3 if it is not installed.
    """

    def __init__(self, timeout_ms: int = 5000):
        self._solver: Any | None = None
        self._global_asserted: bool = False
        self._library_axioms: list[str] = []
        self._library_axiom_set: set[str] = set()
        self._module_axioms: list[str] = []
        self._module_axiom_set: set[str] = set()
        self._stats = BatchStats()
        self._timeout_ms = timeout_ms
        self._adaptive = AdaptiveTimeout(base_ms=timeout_ms)
        self._fallback = FallbackChain(stats=self._stats)
        self._cache: dict[str, bool] = {}
        self._scope_depth: int = 0

    # ── property access ───────────────────────────────────────────

    @property
    def stats(self) -> BatchStats:
        return self._stats

    @property
    def solver(self) -> Any:
        self._ensure_solver()
        return self._solver

    # ── lazy init ─────────────────────────────────────────────────

    def _ensure_solver(self) -> None:
        """Lazy-init the Z3 solver."""
        if self._solver is not None:
            return
        _require_z3()
        self._solver = z3.Solver()
        self._solver.set("timeout", self._timeout_ms)

    # ── axiom layers ──────────────────────────────────────────────

    def assert_global_axioms(self) -> None:
        """Assert Python language axioms (len ≥ 0, etc.).

        Idempotent — safe to call multiple times.
        """
        if self._global_asserted:
            return
        self._ensure_solver()

        len_x = z3.Int("len_x")
        abs_x = z3.Int("abs_x")
        idx = z3.Int("idx")

        self._solver.add(len_x >= 0)
        self._solver.add(abs_x >= 0)

        # For any list-like len function, result is non-negative
        _len = z3.Function("_len", z3.IntSort(), z3.IntSort())
        x = z3.Int("x")
        self._solver.add(z3.ForAll([x], _len(x) >= 0))

        self._global_asserted = True
        self._stats.axioms_shared += 3

    def assert_library_axioms(self, module: str, axioms: list[str]) -> None:
        """Assert library axioms for *module*.

        Each axiom string is parsed and added to the solver.  Duplicates
        (by string equality) are silently skipped.
        """
        self._ensure_solver()
        new_count = 0
        for ax in axioms:
            key = f"{module}:{ax}"
            if key in self._library_axiom_set:
                continue
            self._library_axiom_set.add(key)
            self._library_axioms.append(key)
            try:
                expr = _parse_formula(ax)
                self._solver.add(expr)
                new_count += 1
            except Exception:
                pass
        self._stats.axioms_shared += new_count

    def assert_module_axioms(self, axioms: list[str]) -> None:
        """Assert module-level axioms / invariants."""
        self._ensure_solver()
        new_count = 0
        for ax in axioms:
            if ax in self._module_axiom_set:
                continue
            self._module_axiom_set.add(ax)
            self._module_axioms.append(ax)
            try:
                expr = _parse_formula(ax)
                self._solver.add(expr)
                new_count += 1
            except Exception:
                pass
        self._stats.axioms_shared += new_count

    # ── single-function verification ──────────────────────────────

    def verify_function(
        self,
        obligations: list[str],
        preconditions: list[str] | None = None,
    ) -> list[bool]:
        """Verify multiple obligations for one function.

        Uses push/pop to scope function-specific precondition assertions
        so they don't pollute the solver for subsequent functions.

        Returns a list of booleans parallel to *obligations*.
        """
        self._ensure_solver()
        self.assert_global_axioms()

        results: list[bool] = []
        # Push function scope
        self._solver.push()
        self._scope_depth += 1
        try:
            # Assert function-level preconditions
            if preconditions:
                for pre in preconditions:
                    try:
                        expr = _parse_formula(pre)
                        self._solver.add(expr)
                    except Exception:
                        pass

            for obl in obligations:
                cache_key = self._cache_key(obl, preconditions)
                if cache_key in self._cache:
                    results.append(self._cache[cache_key])
                    self._stats.z3_cache_hits += 1
                    continue

                timeout = self._adaptive.compute_timeout(obl)
                fb = self._fallback.try_with_fallback(
                    self._solver, obl, timeout,
                )
                self._stats.total_z3_time_ms += fb.z3_time_ms
                proved = fb.proved
                self._cache[cache_key] = proved
                results.append(proved)
        finally:
            self._solver.pop()
            self._scope_depth -= 1

        return results

    # ── batch verification ────────────────────────────────────────

    def verify_batch(self, batch: list[BatchItem]) -> list[BatchResult]:
        """Verify a batch of obligations across multiple functions.

        Groups items by module for axiom reuse, then by function for
        precondition scoping.
        """
        self._ensure_solver()
        self.assert_global_axioms()

        # Group by module → function
        by_module: dict[str, dict[str, list[BatchItem]]] = {}
        index_map: dict[int, int] = {}  # original index → order seen
        ordered_items: list[tuple[int, BatchItem]] = list(enumerate(batch))

        for idx, item in ordered_items:
            mod = item.module or "__main__"
            fn = item.function_name or "__top__"
            by_module.setdefault(mod, {}).setdefault(fn, []).append(item)

        result_map: dict[int, BatchResult] = {}

        for mod, fn_map in by_module.items():
            for fn, items in fn_map.items():
                preconditions = items[0].preconditions if items else []
                obligs = [it.obligation for it in items]
                bools = self.verify_function(obligs, preconditions)

                for item, proved in zip(items, bools):
                    orig_idx = batch.index(item)
                    br = BatchResult(
                        item=item,
                        proved=proved,
                        fallback_level=(FallbackLevel.DIRECT if proved
                                        else FallbackLevel.UNRESOLVABLE),
                    )
                    self._stats.record(br)
                    result_map[orig_idx] = br

        return [result_map[i] for i in range(len(batch))]

    # ── reset ─────────────────────────────────────────────────────

    def reset(self) -> None:
        """Drop solver state and start fresh (keeps statistics)."""
        self._solver = None
        self._global_asserted = False
        self._library_axioms.clear()
        self._library_axiom_set.clear()
        self._module_axioms.clear()
        self._module_axiom_set.clear()
        self._cache.clear()
        self._scope_depth = 0

    # ── internals ─────────────────────────────────────────────────

    @staticmethod
    def _cache_key(obligation: str, preconditions: list[str] | None) -> str:
        blob = obligation
        if preconditions:
            blob += "||" + "&&".join(sorted(preconditions))
        return hashlib.sha256(blob.encode()).hexdigest()


# ═══════════════════════════════════════════════════════════════════
# 6.  Module-Level Batch Verifier
# ═══════════════════════════════════════════════════════════════════

class ModuleBatchVerifier:
    """Verify an entire Python module's obligations in batch.

    Workflow
    --------
    1. Parse source, extract all annotated functions via :class:`SpecExtractor`.
    2. Compute dependency order (callees first).
    3. Group obligations by shared axiom context.
    4. Verify in batch with a shared Z3 solver.
    """

    def __init__(self, timeout_ms: int = 5000):
        self._ctx = Z3BatchContext(timeout_ms=timeout_ms)
        # Import here to avoid circular import at module level
        from deppy.pipeline.verifier import SpecExtractor, ObligationGenerator
        self._extractor = SpecExtractor()
        self._obligation_gen = ObligationGenerator()

    @property
    def stats(self) -> BatchStats:
        return self._ctx.stats

    # ── public API ────────────────────────────────────────────────

    def verify_module(self, module_path: str) -> ModuleVerificationReport:
        """Verify all annotated functions in a Python source file.

        Parameters
        ----------
        module_path : str
            Path to a ``.py`` file **or** a raw Python source string.
        """
        t0 = time.perf_counter_ns()

        source = self._read_source(module_path)
        specs = self._extractor.extract_from_source(source)

        # Compute dependency order (simple heuristic: alphabetical for now,
        # since true call-graph analysis requires deeper AST work).
        specs = self._dependency_order(specs, source)

        fn_results = self.verify_functions(specs)

        elapsed = (time.perf_counter_ns() - t0) / 1e6
        return ModuleVerificationReport(
            module_path=module_path,
            functions=fn_results,
            stats=self._ctx.stats,
            duration_ms=elapsed,
        )

    def verify_functions(self, functions: list[FunctionSpec]) -> list[FunctionResult]:
        """Verify a list of function specifications in batch."""
        results: list[FunctionResult] = []

        for spec in functions:
            t0 = time.perf_counter_ns()
            obligation_pairs = self._obligation_gen.generate(spec)

            # Convert formal obligations into formula strings
            obligs: list[str] = []
            for desc, judgment in obligation_pairs:
                formula = self._judgment_to_formula(judgment)
                obligs.append(formula)

            preconditions = [a.description for a in spec.assumptions]
            bools = self._ctx.verify_function(obligs, preconditions or None)

            batch_results: list[BatchResult] = []
            for (desc, _), proved in zip(obligation_pairs, bools):
                br = BatchResult(
                    item=BatchItem(
                        obligation=desc,
                        function_name=spec.name,
                        description=desc,
                    ),
                    proved=proved,
                )
                self._ctx.stats.record(br)
                batch_results.append(br)

            elapsed = (time.perf_counter_ns() - t0) / 1e6
            trust = TrustLevel.Z3_VERIFIED if all(bools) else TrustLevel.UNTRUSTED
            results.append(FunctionResult(
                name=spec.name,
                obligations=batch_results,
                trust_level=trust,
                duration_ms=elapsed,
            ))

        return results

    # ── helpers ────────────────────────────────────────────────────

    @staticmethod
    def _read_source(path_or_source: str) -> str:
        """Read source from a file path or return raw source."""
        if "\n" in path_or_source or "def " in path_or_source:
            return path_or_source
        try:
            with open(path_or_source, "r") as fh:
                return fh.read()
        except (OSError, IOError):
            return path_or_source

    @staticmethod
    def _dependency_order(specs: list[FunctionSpec], source: str) -> list[FunctionSpec]:
        """Sort functions so callees come before callers (best-effort).

        Uses a simple heuristic: if function A's source mentions function B's
        name, A depends on B.  Falls back to original order on failure.
        """
        try:
            tree = ast.parse(textwrap.dedent(source))
        except SyntaxError:
            return specs

        name_set = {s.name for s in specs}
        fn_bodies: dict[str, str] = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef) and node.name in name_set:
                fn_bodies[node.name] = ast.dump(node)

        # Build adjacency: fn → set of fns it calls
        deps: dict[str, set[str]] = {s.name: set() for s in specs}
        for fname, body_dump in fn_bodies.items():
            for other in name_set:
                if other != fname and other in body_dump:
                    deps[fname].add(other)

        # Topological sort (Kahn's algorithm)
        in_degree: dict[str, int] = {n: 0 for n in deps}
        for n, callees in deps.items():
            for c in callees:
                if c in in_degree:
                    in_degree[c] = in_degree.get(c, 0)  # callee first → no increment
        # Actually we want callees first, so reverse edges
        reverse_deg: dict[str, int] = {n: 0 for n in deps}
        for n, callees in deps.items():
            reverse_deg[n] += len(callees)

        queue = [n for n, d in reverse_deg.items() if d == 0]
        ordered: list[str] = []
        visited: set[str] = set()
        while queue:
            n = queue.pop(0)
            if n in visited:
                continue
            visited.add(n)
            ordered.append(n)
            for other, callees in deps.items():
                if n in callees and other not in visited:
                    reverse_deg[other] -= 1
                    if reverse_deg[other] <= 0:
                        queue.append(other)

        # Add any remaining
        for s in specs:
            if s.name not in visited:
                ordered.append(s.name)

        name_to_spec = {s.name: s for s in specs}
        return [name_to_spec[n] for n in ordered if n in name_to_spec]

    @staticmethod
    def _judgment_to_formula(judgment: Judgment) -> str:
        """Extract a formula string from a Judgment for Z3 checking."""
        if judgment.kind == JudgmentKind.TYPE_CHECK:
            ty = judgment.type_
            if isinstance(ty, RefinementType):
                return ty.predicate
            return f"True"  # trivial type check
        elif judgment.kind == JudgmentKind.EQUAL:
            left = str(judgment.left) if judgment.left else "?"
            right = str(judgment.right) if judgment.right else "?"
            return f"({left}) == ({right})"
        elif judgment.kind == JudgmentKind.WELL_FORMED:
            ty = judgment.type_
            if isinstance(ty, RefinementType):
                return ty.predicate
            return "True"
        return "True"


# ═══════════════════════════════════════════════════════════════════
# 7.  Self-Tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Lightweight self-tests — run with ``python -m deppy.pipeline.batch_z3``."""
    _require_z3()

    print("=" * 60)
    print("batch_z3 self-tests")
    print("=" * 60)

    # ── AdaptiveTimeout ───────────────────────────────────────────
    at = AdaptiveTimeout(base_ms=1000)
    assert at.complexity("x > 0") >= 0
    assert at.complexity("forall x. x >= 0") > at.complexity("x > 0")
    assert at.complexity("f(g(x)) > 0") > at.complexity("x > 0")
    t1 = at.compute_timeout("x > 0")
    t2 = at.compute_timeout("forall x. f(g(x)) > h(y) and p(q(r(z)))")
    assert t2 >= t1, f"complex formula should have higher timeout: {t2} vs {t1}"
    print(f"  ✓ AdaptiveTimeout: simple={t1}ms, complex={t2}ms")

    # ── BatchStats ────────────────────────────────────────────────
    stats = BatchStats()
    item = BatchItem(obligation="x > 0", function_name="f", description="test")
    br = BatchResult(item=item, proved=True, fallback_level=FallbackLevel.DIRECT)
    stats.record(br)
    assert stats.total_obligations == 1
    assert stats.proved_count == 1
    assert stats.unresolvable_count == 0
    print(f"  ✓ BatchStats: {stats}")

    # ── Z3BatchContext — basic verification ───────────────────────
    ctx = Z3BatchContext(timeout_ms=5000)
    results = ctx.verify_function(["x + 1 > x", "y * 0 == 0"])
    assert results == [True, True], f"expected [True, True], got {results}"
    print(f"  ✓ Z3BatchContext.verify_function: {results}")

    # ── verify_function with preconditions ────────────────────────
    results2 = ctx.verify_function(
        ["x > 5"],
        preconditions=["x > 10"],
    )
    assert results2 == [True], f"expected [True], got {results2}"
    print(f"  ✓ precondition scoping: {results2}")

    # ── verify_function: false obligation ─────────────────────────
    results3 = ctx.verify_function(["x > 0"])
    assert results3 == [False], f"unprovable without preconditions: {results3}"
    print(f"  ✓ unprovable obligation: {results3}")

    # ── cache hits ────────────────────────────────────────────────
    ctx2 = Z3BatchContext(timeout_ms=5000)
    ctx2.verify_function(["x + 1 > x"])
    initial_calls = ctx2.stats.z3_calls
    ctx2.verify_function(["x + 1 > x"])
    assert ctx2.stats.z3_cache_hits >= 1, "cache miss on duplicate"
    print(f"  ✓ cache: {ctx2.stats.z3_cache_hits} hit(s)")

    # ── verify_batch ──────────────────────────────────────────────
    batch = [
        BatchItem(obligation="a + 1 > a", function_name="f1",
                  module="mod", description="f1: a+1>a"),
        BatchItem(obligation="b * 0 == 0", function_name="f2",
                  module="mod", description="f2: b*0==0"),
        BatchItem(obligation="c > 0", function_name="f3",
                  module="mod", description="f3: c>0 (unprovable)"),
    ]
    ctx3 = Z3BatchContext(timeout_ms=5000)
    batch_res = ctx3.verify_batch(batch)
    assert len(batch_res) == 3
    assert batch_res[0].proved is True
    assert batch_res[1].proved is True
    assert batch_res[2].proved is False
    print(f"  ✓ verify_batch: {[r.proved for r in batch_res]}")

    # ── library axioms ────────────────────────────────────────────
    ctx4 = Z3BatchContext(timeout_ms=5000)
    ctx4.assert_library_axioms("mylib", ["p > 100"])
    results4 = ctx4.verify_function(["p > 50"])
    assert results4 == [True], f"library axiom should help: {results4}"
    print(f"  ✓ library axioms: {results4}")

    # ── module axioms ─────────────────────────────────────────────
    ctx5 = Z3BatchContext(timeout_ms=5000)
    ctx5.assert_module_axioms(["q == 42"])
    results5 = ctx5.verify_function(["q > 0"])
    assert results5 == [True], f"module axiom should help: {results5}"
    print(f"  ✓ module axioms: {results5}")

    # ── axiom deduplication ───────────────────────────────────────
    ctx6 = Z3BatchContext(timeout_ms=5000)
    ctx6.assert_library_axioms("lib", ["r > 0", "r > 0", "r > 0"])
    assert len(ctx6._library_axioms) == 1, "axiom dedup failed"
    print(f"  ✓ axiom dedup: {len(ctx6._library_axioms)} unique")

    # ── FallbackChain ─────────────────────────────────────────────
    solver = z3.Solver()
    solver.set("timeout", 5000)
    chain = FallbackChain()

    fb = chain.try_with_fallback(solver, "x + 1 > x", 5000)
    assert fb.proved is True
    assert fb.level == FallbackLevel.DIRECT
    print(f"  ✓ FallbackChain direct: {fb.level.name}")

    # conjunction split
    fb2 = chain.try_with_fallback(solver, "x + 1 > x and y * 0 == 0", 5000)
    assert fb2.proved is True
    print(f"  ✓ FallbackChain (conjunction): level={fb2.level.name}")

    # unresolvable
    fb3 = chain.try_with_fallback(solver, "x > 0", 5000)
    assert fb3.proved is False
    assert fb3.level == FallbackLevel.UNRESOLVABLE
    print(f"  ✓ FallbackChain unresolvable: {fb3.level.name}")

    # ── ModuleBatchVerifier ───────────────────────────────────────
    sample_source = textwrap.dedent("""\
        def add(x: int, y: int) -> int:
            \"\"\"x + y == y + x\"\"\"
            return x + y

        def double(n: int) -> int:
            \"\"\"n * 2 == n + n\"\"\"
            return n * 2
    """)
    mbv = ModuleBatchVerifier(timeout_ms=5000)
    report = mbv.verify_module(sample_source)
    assert len(report.functions) == 2
    print(f"  ✓ ModuleBatchVerifier: {report}")

    # ── reset ─────────────────────────────────────────────────────
    ctx.reset()
    assert ctx._solver is None
    assert ctx._global_asserted is False
    print(f"  ✓ reset")

    # ── formula helpers ───────────────────────────────────────────
    vars_found = _extract_variables("x + y > z")
    assert "x" in vars_found and "y" in vars_found and "z" in vars_found
    print(f"  ✓ _extract_variables: {vars_found}")

    parts = _split_conjunction("a > 0 and b > 0 and c > 0")
    assert len(parts) == 3
    print(f"  ✓ _split_conjunction: {parts}")

    abst = _abstract_subterms("f(g(x)) > 0")
    assert "_abs_" in abst
    print(f"  ✓ _abstract_subterms: {abst}")

    print()
    print("All self-tests passed ✓")
    print("=" * 60)


if __name__ == "__main__":
    _self_test()
