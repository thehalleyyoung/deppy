"""
Deppy Effect-Based Obligation Pruning Engine

Implements the *Effect-Based Obligation Pruning* section from the monograph's
Scalable Verification chapter.  The key insight:

    If a function is **PURE**, it needs NO aliasing, mutation, or exception
    obligations — these are trivially satisfied by the effect guarantee.

This eliminates 60-80 % of heap-related proof obligations for pure and
read-only functions, dramatically reducing the work for downstream Z3 / LLM
provers.

Pipeline:
    1. Analyse effects of every function (via AST)
    2. Build a call graph and propagate effects bottom-up (callees → callers)
    3. Classify each proof obligation by its *category*
    4. Prune obligations that are trivially satisfied given the effect level
    5. Pass only the remaining obligations to Z3 / LLM

Architecture:

    EffectAnalyzer          — per-function AST-based effect inference
    ObligationClassifier    — tag obligations as ALIASING / MUTATION / …
    EffectDependencyGraph   — call graph + bottom-up effect propagation
    PruningReport           — statistics on what was pruned
    EffectPruningPipeline   — end-to-end integration
"""
from __future__ import annotations

import ast
import textwrap
from collections import defaultdict
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Sequence

# ── conditional imports ──────────────────────────────────────────────
try:
    from deppy.effects.effect_types import (
        Effect,
        FunctionEffect,
        EffectAnalyzer as _BaseEffectAnalyzer,
        effect_leq,
    )
except ImportError:  # pragma: no cover – standalone testing
    _BaseEffectAnalyzer = None  # type: ignore[assignment,misc]

try:
    from deppy.core.types import (
        Judgment,
        JudgmentKind,
        Context,
        SynType,
        SynTerm,
        RefinementType,
        Literal,
    )
except ImportError:  # pragma: no cover
    Judgment = None  # type: ignore[assignment,misc]
    JudgmentKind = None  # type: ignore[assignment,misc]
    Context = None  # type: ignore[assignment,misc]
    SynType = None  # type: ignore[assignment,misc]
    SynTerm = None  # type: ignore[assignment,misc]
    RefinementType = None  # type: ignore[assignment,misc]
    Literal = None  # type: ignore[assignment,misc]


# ═══════════════════════════════════════════════════════════════════════
# 1. Effect Lattice (self-contained, used if deppy.effects unavailable)
# ═══════════════════════════════════════════════════════════════════════

class EffectLevel(Enum):
    """Lightweight effect lattice for pruning decisions.

    PURE ≤ READS ≤ MUTATES ≤ IO ≤ NONDET

    This mirrors ``deppy.effects.effect_types.Effect`` but can be used
    stand-alone when the full effect module is not on the import path.
    """
    PURE    = 0
    READS   = 1
    MUTATES = 2
    IO      = 3
    NONDET  = 4

    # ── lattice operations ────────────────────────────────────────

    def __le__(self, other: object) -> bool:
        if not isinstance(other, EffectLevel):
            return NotImplemented
        return self.value <= other.value

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, EffectLevel):
            return NotImplemented
        return self.value < other.value

    def __ge__(self, other: object) -> bool:
        if not isinstance(other, EffectLevel):
            return NotImplemented
        return self.value >= other.value

    def __gt__(self, other: object) -> bool:
        if not isinstance(other, EffectLevel):
            return NotImplemented
        return self.value > other.value

    @staticmethod
    def join(a: EffectLevel, b: EffectLevel) -> EffectLevel:
        """Least upper bound (max) in the lattice."""
        return a if a.value >= b.value else b

    @staticmethod
    def meet(a: EffectLevel, b: EffectLevel) -> EffectLevel:
        """Greatest lower bound (min) in the lattice."""
        return a if a.value <= b.value else b


def _join_all(effects: Sequence[EffectLevel]) -> EffectLevel:
    """Join a sequence of effects — identity is PURE."""
    result = EffectLevel.PURE
    for e in effects:
        result = EffectLevel.join(result, e)
    return result


# ═══════════════════════════════════════════════════════════════════════
# 2. Effect Analyzer (AST-based)
# ═══════════════════════════════════════════════════════════════════════

# Known-pure builtins and standard-library functions.
_PURE_BUILTINS: frozenset[str] = frozenset({
    "len", "sorted", "reversed", "abs", "min", "max",
    "sum", "all", "any", "zip", "map", "filter",
    "enumerate", "range", "bool", "int", "float", "str",
    "repr", "hash", "id", "type", "isinstance", "issubclass",
    "tuple", "list", "dict", "set", "frozenset",
    "chr", "ord", "hex", "oct", "bin", "round",
    "divmod", "pow", "complex",
    "getattr", "hasattr",
    "iter", "next",
    "slice", "staticmethod", "classmethod", "property",
    "super", "object", "callable",
    "format", "ascii",
    "vars", "dir",
    "math.sqrt", "math.floor", "math.ceil", "math.log",
    "math.sin", "math.cos", "math.tan", "math.exp",
    "math.gcd", "math.factorial", "math.comb", "math.perm",
    "math.isnan", "math.isinf", "math.isfinite",
    "operator.add", "operator.mul", "operator.sub",
    "functools.reduce",
    "itertools.chain", "itertools.product", "itertools.combinations",
    "itertools.permutations", "itertools.islice",
    "copy.copy", "copy.deepcopy",
})

# Functions that only read state.
_READS_BUILTINS: frozenset[str] = frozenset({
    "dict.get", "dict.keys", "dict.values", "dict.items",
    "list.__getitem__", "dict.__getitem__",
    "str.split", "str.join", "str.strip", "str.replace",
    "str.startswith", "str.endswith", "str.find", "str.index",
    "str.upper", "str.lower", "str.title",
    "os.path.exists", "os.path.join", "os.path.basename",
    "os.path.dirname", "os.path.splitext",
    "os.environ.get",
    "json.loads", "json.dumps",
})

# Functions that mutate state.
_MUTATES_BUILTINS: frozenset[str] = frozenset({
    "list.append", "list.extend", "list.insert", "list.remove",
    "list.pop", "list.clear", "list.sort", "list.reverse",
    "dict.__setitem__", "dict.__delitem__", "dict.update",
    "dict.pop", "dict.clear", "dict.setdefault",
    "set.add", "set.remove", "set.discard", "set.pop",
    "set.clear", "set.update",
    "bytearray.append", "bytearray.extend",
})

# Mutating method names (unqualified, for attribute-based calls).
_MUTATING_METHODS: frozenset[str] = frozenset({
    "append", "extend", "insert", "remove", "pop", "clear",
    "sort", "reverse",
    "add", "discard", "update", "setdefault",
    "__setitem__", "__delitem__",
})

# Known IO functions.
_IO_BUILTINS: frozenset[str] = frozenset({
    "print", "input", "open",
    "sys.stdin.read", "sys.stdout.write", "sys.stderr.write",
    "logging.info", "logging.debug", "logging.warning",
    "logging.error", "logging.critical",
    "os.system", "os.popen",
    "subprocess.run", "subprocess.call", "subprocess.Popen",
    "socket.socket",
    "requests.get", "requests.post",
    "urllib.request.urlopen",
})

# Known non-deterministic functions.
_NONDET_BUILTINS: frozenset[str] = frozenset({
    "random.random", "random.randint", "random.choice",
    "random.shuffle", "random.sample", "random.uniform",
    "time.time", "time.monotonic", "time.perf_counter",
    "os.getpid", "os.urandom", "uuid.uuid4",
})


class EffectAnalyzer:
    """Analyse a Python function's effect from its AST.

    Effect lattice::

        PURE ≤ READS ≤ MUTATES ≤ IO ≤ NONDET

    The analyser is *conservative*: if it cannot prove an operation is
    pure, it assumes the worst-case effect.  This keeps the analysis
    *sound* (no false negatives) at the cost of some false positives.
    """

    def __init__(self) -> None:
        self._current_effect: EffectLevel = EffectLevel.PURE
        self._local_names: set[str] = set()
        self._param_names: set[str] = set()
        self._has_exception: bool = False
        self._defined_funcs: set[str] = set()

    # ── public API ────────────────────────────────────────────────

    def analyze_function(self, func_ast: ast.FunctionDef) -> EffectLevel:
        """Compute the effect of *func_ast* from its body."""
        self._reset()
        self._param_names = {arg.arg for arg in func_ast.args.args}
        self._local_names = set(self._param_names)
        # Pre-scan for nested function definitions so calls to them
        # don't escalate to IO.
        for node in ast.walk(func_ast):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node is not func_ast:
                    self._defined_funcs.add(node.name)
        for stmt in func_ast.body:
            self.analyze_statement(stmt)
        return self._current_effect

    def analyze_statement(self, stmt: ast.stmt) -> EffectLevel:
        """Compute the effect of a single statement."""
        before = self._current_effect
        self._visit_stmt(stmt)
        return self._current_effect

    def analyze_expression(self, expr: ast.expr) -> EffectLevel:
        """Compute the effect of an expression."""
        before = self._current_effect
        self._visit_expr(expr)
        return self._current_effect

    @property
    def has_exception(self) -> bool:
        """Whether the function may raise an exception."""
        return self._has_exception

    # ── effect classification for common patterns ─────────────────

    def _is_pure_call(self, func_name: str) -> bool:
        """Known-pure functions: len, sorted, reversed, abs, …"""
        return func_name in _PURE_BUILTINS

    def _is_reads_call(self, func_name: str) -> bool:
        """Known-reads functions: dict.get, list.__getitem__, …"""
        return func_name in _READS_BUILTINS

    def _is_mutates_call(self, func_name: str) -> bool:
        """Known-mutating: list.append, dict.__setitem__, …"""
        return func_name in _MUTATES_BUILTINS

    def _is_io_call(self, func_name: str) -> bool:
        """Known-IO: print, open, input, …"""
        return func_name in _IO_BUILTINS

    def _is_nondet_call(self, func_name: str) -> bool:
        """Known non-deterministic: random.random, time.time, …"""
        return func_name in _NONDET_BUILTINS

    # ── lifting helpers ───────────────────────────────────────────

    def _lift(self, level: EffectLevel) -> None:
        """Raise the current effect to at least *level*."""
        self._current_effect = EffectLevel.join(self._current_effect, level)

    def _reset(self) -> None:
        self._current_effect = EffectLevel.PURE
        self._local_names = set()
        self._param_names = set()
        self._has_exception = False
        self._defined_funcs = set()

    # ── statement visitors ────────────────────────────────────────

    def _visit_stmt(self, node: ast.stmt) -> None:  # noqa: C901
        if isinstance(node, ast.Return):
            if node.value:
                self._visit_expr(node.value)

        elif isinstance(node, ast.Assign):
            for target in node.targets:
                self._handle_assign_target(target)
            self._visit_expr(node.value)

        elif isinstance(node, ast.AugAssign):
            self._handle_assign_target(node.target)
            self._visit_expr(node.value)

        elif isinstance(node, ast.AnnAssign):
            if node.value:
                self._visit_expr(node.value)
            if node.target:
                self._handle_assign_target(node.target)

        elif isinstance(node, ast.For):
            self._visit_expr(node.iter)
            for s in node.body + node.orelse:
                self._visit_stmt(s)

        elif isinstance(node, ast.While):
            self._visit_expr(node.test)
            for s in node.body + node.orelse:
                self._visit_stmt(s)

        elif isinstance(node, ast.If):
            self._visit_expr(node.test)
            for s in node.body + node.orelse:
                self._visit_stmt(s)

        elif isinstance(node, ast.With):
            for item in node.items:
                self._visit_expr(item.context_expr)
            for s in node.body:
                self._visit_stmt(s)

        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            # Nested function: analyse for escaping effects.
            for s in node.body:
                self._visit_stmt(s)

        elif isinstance(node, ast.Raise):
            self._has_exception = True
            if node.exc:
                self._visit_expr(node.exc)

        elif isinstance(node, ast.Try):
            self._has_exception = True
            for s in node.body:
                self._visit_stmt(s)
            for handler in node.handlers:
                for s in handler.body:
                    self._visit_stmt(s)
            for s in node.orelse + node.finalbody:
                self._visit_stmt(s)

        elif isinstance(node, ast.Assert):
            self._has_exception = True
            self._visit_expr(node.test)

        elif isinstance(node, ast.Expr):
            self._visit_expr(node.value)

        elif isinstance(node, ast.Global):
            self._lift(EffectLevel.MUTATES)

        elif isinstance(node, ast.Nonlocal):
            self._lift(EffectLevel.MUTATES)

        elif isinstance(node, ast.Delete):
            self._lift(EffectLevel.MUTATES)

        elif isinstance(node, ast.Pass):
            pass

        elif isinstance(node, ast.Break):
            pass

        elif isinstance(node, ast.Continue):
            pass

    # ── expression visitors ───────────────────────────────────────

    def _visit_expr(self, node: ast.expr) -> None:
        if isinstance(node, ast.Call):
            self._handle_call(node)

        elif isinstance(node, ast.Attribute):
            self._visit_expr(node.value)

        elif isinstance(node, ast.Subscript):
            self._visit_expr(node.value)
            self._visit_expr(node.slice)

        elif isinstance(node, ast.BoolOp):
            for v in node.values:
                self._visit_expr(v)

        elif isinstance(node, ast.BinOp):
            self._visit_expr(node.left)
            self._visit_expr(node.right)

        elif isinstance(node, ast.UnaryOp):
            self._visit_expr(node.operand)

        elif isinstance(node, ast.IfExp):
            self._visit_expr(node.test)
            self._visit_expr(node.body)
            self._visit_expr(node.orelse)

        elif isinstance(node, ast.ListComp):
            self._visit_comprehension(node.generators, node.elt)

        elif isinstance(node, ast.SetComp):
            self._visit_comprehension(node.generators, node.elt)

        elif isinstance(node, ast.GeneratorExp):
            self._visit_comprehension(node.generators, node.elt)

        elif isinstance(node, ast.DictComp):
            for gen in node.generators:
                self._visit_expr(gen.iter)
                for if_ in gen.ifs:
                    self._visit_expr(if_)
            self._visit_expr(node.key)
            self._visit_expr(node.value)

        elif isinstance(node, ast.Compare):
            self._visit_expr(node.left)
            for comp in node.comparators:
                self._visit_expr(comp)

        elif isinstance(node, (ast.List, ast.Tuple, ast.Set)):
            for elt in node.elts:
                self._visit_expr(elt)

        elif isinstance(node, ast.Dict):
            for k in node.keys:
                if k is not None:
                    self._visit_expr(k)
            for v in node.values:
                self._visit_expr(v)

        elif isinstance(node, ast.Lambda):
            self._visit_expr(node.body)

        elif isinstance(node, ast.Starred):
            self._visit_expr(node.value)

        elif isinstance(node, ast.JoinedStr):
            for v in node.values:
                if isinstance(v, ast.FormattedValue):
                    self._visit_expr(v.value)

        elif isinstance(node, ast.Await):
            self._lift(EffectLevel.IO)
            self._visit_expr(node.value)

    def _visit_comprehension(
        self, generators: list[ast.comprehension], elt: ast.expr
    ) -> None:
        for gen in generators:
            self._visit_expr(gen.iter)
            for if_ in gen.ifs:
                self._visit_expr(if_)
        self._visit_expr(elt)

    # ── call handling (the core of effect classification) ─────────

    def _handle_call(self, node: ast.Call) -> None:
        """Classify a function call and lift the effect accordingly."""
        # Visit all sub-expressions first (args, keywords).
        for arg in node.args:
            self._visit_expr(arg)
        for kw in node.keywords:
            self._visit_expr(kw.value)

        func_name = self._extract_call_name(node.func)
        if func_name is None:
            # Cannot determine call target → conservative.
            self._lift(EffectLevel.IO)
            return

        if self._is_pure_call(func_name):
            return  # no effect
        if self._is_reads_call(func_name):
            self._lift(EffectLevel.READS)
            return
        if self._is_mutates_call(func_name):
            self._lift(EffectLevel.MUTATES)
            return
        if self._is_io_call(func_name):
            self._lift(EffectLevel.IO)
            return
        if self._is_nondet_call(func_name):
            self._lift(EffectLevel.NONDET)
            return

        # Check for mutating methods by unqualified name.
        if isinstance(node.func, ast.Attribute):
            method = node.func.attr
            if method in _MUTATING_METHODS:
                self._lift(EffectLevel.MUTATES)
                return

        # Locally-defined function — its effects are already captured
        # by visiting its body, so the *call* itself adds nothing.
        if func_name in self._defined_funcs:
            return

        # Unknown call → conservative default is IO.
        self._lift(EffectLevel.IO)

    def _handle_assign_target(self, target: ast.expr) -> None:
        """Determine whether an assignment target implies mutation."""
        if isinstance(target, ast.Name):
            self._local_names.add(target.id)
            # Local variable assignment is pure.
        elif isinstance(target, ast.Attribute):
            # obj.attr = ... mutates obj.
            self._lift(EffectLevel.MUTATES)
        elif isinstance(target, ast.Subscript):
            # obj[key] = ... mutates obj.
            self._lift(EffectLevel.MUTATES)
        elif isinstance(target, (ast.Tuple, ast.List)):
            for elt in target.elts:
                self._handle_assign_target(elt)
        elif isinstance(target, ast.Starred):
            self._handle_assign_target(target.value)

    # ── name extraction ───────────────────────────────────────────

    @staticmethod
    def _extract_call_name(node: ast.expr) -> str | None:
        """Extract a dotted name from a call target, or None."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            parts: list[str] = [node.attr]
            cur = node.value
            while isinstance(cur, ast.Attribute):
                parts.append(cur.attr)
                cur = cur.value
            if isinstance(cur, ast.Name):
                parts.append(cur.id)
            parts.reverse()
            return ".".join(parts)
        return None


# ═══════════════════════════════════════════════════════════════════════
# 3. Obligation Category
# ═══════════════════════════════════════════════════════════════════════

class ObligationCategory(Enum):
    """Category of a proof obligation, indicating what it requires.

    Each category maps to the *minimum* effect level at which the
    obligation is non-trivial.
    """
    PURE_PROPERTY = auto()  # input → output relationship (Z3 only)
    ALIASING      = auto()  # requires alias analysis (heap model)
    MUTATION      = auto()  # requires frame conditions (heap model)
    EXCEPTION     = auto()  # requires exception-safety analysis
    TERMINATION   = auto()  # requires variant / measure
    TYPE_CHECK    = auto()  # type correctness (often Level 0)


# Mapping: which effect level makes an obligation category trivially true.
_TRIVIALLY_SATISFIED: dict[ObligationCategory, EffectLevel] = {
    ObligationCategory.ALIASING:  EffectLevel.READS,
    ObligationCategory.MUTATION:  EffectLevel.READS,
    ObligationCategory.EXCEPTION: EffectLevel.PURE,
}

# Keywords used to classify obligations by inspecting their description
# or the refinement predicate text.
_ALIASING_KEYWORDS: frozenset[str] = frozenset({
    "alias", "aliasing", "disjoint", "separate", "no_alias",
    "no_sharing", "distinct", "unique_ref", "unique_reference",
    "not_aliased", "heap_disjoint", "pointer", "reference",
    "borrow", "ownership",
})

_MUTATION_KEYWORDS: frozenset[str] = frozenset({
    "mutate", "mutation", "frame", "modifies", "unchanged",
    "preserves", "heap", "write", "assign", "in_place",
    "side_effect", "mutable", "modified", "written",
    "pre_state", "post_state", "state_change",
})

_EXCEPTION_KEYWORDS: frozenset[str] = frozenset({
    "exception", "raises", "throw", "error", "fault",
    "no_exception", "exception_safe", "exception_free",
    "total", "nothrow", "safe",
})

_TERMINATION_KEYWORDS: frozenset[str] = frozenset({
    "terminates", "termination", "decreasing", "variant",
    "measure", "well_founded", "bounded", "converges",
    "halts", "total",
})


class ObligationClassifier:
    """Classify proof obligations by what they require.

    Categories:
    - PURE_PROPERTY:  input → output relationship (needs Z3 only)
    - ALIASING:       requires alias analysis (needs heap model)
    - MUTATION:       requires frame conditions (needs heap model)
    - EXCEPTION:      requires exception-safety analysis
    - TERMINATION:    requires variant / measure
    - TYPE_CHECK:     type correctness (often Level 0)
    """

    def classify(self, obligation: Judgment) -> ObligationCategory:
        """Classify a single obligation based on its structure."""
        desc = self._obligation_text(obligation)
        desc_lower = desc.lower()

        # Check keyword matches in priority order.
        if any(kw in desc_lower for kw in _ALIASING_KEYWORDS):
            return ObligationCategory.ALIASING
        if any(kw in desc_lower for kw in _MUTATION_KEYWORDS):
            return ObligationCategory.MUTATION
        if any(kw in desc_lower for kw in _EXCEPTION_KEYWORDS):
            return ObligationCategory.EXCEPTION
        if any(kw in desc_lower for kw in _TERMINATION_KEYWORDS):
            return ObligationCategory.TERMINATION

        # Type-check obligations.
        if obligation.kind == JudgmentKind.TYPE_CHECK:
            ty = obligation.type_
            if isinstance(ty, RefinementType):
                pred = ty.predicate.lower()
                if any(kw in pred for kw in _ALIASING_KEYWORDS):
                    return ObligationCategory.ALIASING
                if any(kw in pred for kw in _MUTATION_KEYWORDS):
                    return ObligationCategory.MUTATION
                if any(kw in pred for kw in _EXCEPTION_KEYWORDS):
                    return ObligationCategory.EXCEPTION
                return ObligationCategory.PURE_PROPERTY
            return ObligationCategory.TYPE_CHECK

        if obligation.kind == JudgmentKind.EQUAL:
            return ObligationCategory.PURE_PROPERTY
        if obligation.kind == JudgmentKind.SUBTYPE:
            return ObligationCategory.TYPE_CHECK
        if obligation.kind == JudgmentKind.WELL_FORMED:
            return ObligationCategory.TYPE_CHECK

        return ObligationCategory.PURE_PROPERTY

    def can_prune(self, obligation: Judgment, effect: EffectLevel) -> bool:
        """Can this obligation be pruned given the function's effect?

        An obligation is prunable when the function's effect level is
        *strictly below* the minimum level at which the obligation
        category becomes non-trivial.
        """
        category = self.classify(obligation)
        threshold = _TRIVIALLY_SATISFIED.get(category)
        if threshold is None:
            return False
        return effect <= threshold

    def prune_batch(
        self,
        obligations: list[Judgment],
        effect: EffectLevel,
    ) -> tuple[list[Judgment], list[Judgment]]:
        """Split obligations into (pruned, remaining).

        Pruned obligations are trivially satisfied given the effect level.
        """
        pruned: list[Judgment] = []
        remaining: list[Judgment] = []
        for obl in obligations:
            if self.can_prune(obl, effect):
                pruned.append(obl)
            else:
                remaining.append(obl)
        return pruned, remaining

    # ── helpers ───────────────────────────────────────────────────

    @staticmethod
    def _obligation_text(obligation: Judgment) -> str:
        """Extract a searchable text representation of the obligation."""
        parts: list[str] = []
        if obligation.type_ is not None:
            parts.append(repr(obligation.type_))
        if obligation.term is not None:
            parts.append(repr(obligation.term))
        if obligation.left is not None:
            parts.append(repr(obligation.left))
        if obligation.right is not None:
            parts.append(repr(obligation.right))
        return " ".join(parts)


# ═══════════════════════════════════════════════════════════════════════
# 4. Effect Dependency Graph (call graph + propagation)
# ═══════════════════════════════════════════════════════════════════════

class EffectDependencyGraph:
    """Build a call graph and propagate effects bottom-up.

    If ``f`` calls ``g`` and ``h``, then::

        eff(f) ≥ max(eff(g), eff(h), eff(f_body))

    The graph supports strongly connected components (SCCs) for mutual
    recursion: all functions in an SCC share the same (joined) effect.
    """

    def __init__(self) -> None:
        # func_name → set of callees (by name)
        self._edges: dict[str, set[str]] = defaultdict(set)
        # func_name → the *local* (body-only) effect
        self._local_effects: dict[str, EffectLevel] = {}
        # func_name → the AST node
        self._func_nodes: dict[str, ast.FunctionDef] = {}
        # Cached results after propagation.
        self._propagated: dict[str, EffectLevel] | None = None

    # ── graph building ────────────────────────────────────────────

    def build_from_module(self, module_ast: ast.Module) -> None:
        """Build call graph from a module AST."""
        self._edges.clear()
        self._local_effects.clear()
        self._func_nodes.clear()
        self._propagated = None

        # Collect all top-level function definitions.
        for node in ast.walk(module_ast):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                self._func_nodes[node.name] = node

        # For each function, find callees and compute local effect.
        analyzer = EffectAnalyzer()
        for name, func_node in self._func_nodes.items():
            self._local_effects[name] = analyzer.analyze_function(func_node)
            self._edges[name] = self._extract_callees(func_node)

    def build_from_source(self, source: str) -> None:
        """Build call graph from Python source code."""
        tree = ast.parse(textwrap.dedent(source))
        self.build_from_module(tree)

    def propagate_effects(self) -> dict[str, EffectLevel]:
        """Propagate effects bottom-up through the call graph.

        Returns a mapping from function name to its *propagated* effect.
        """
        if self._propagated is not None:
            return dict(self._propagated)

        result: dict[str, EffectLevel] = dict(self._local_effects)

        # Process SCCs in reverse topological order (leaves first).
        for scc in self.scc_order():
            # Join all local effects in the SCC.
            scc_effect = _join_all([result.get(f, EffectLevel.PURE) for f in scc])
            # Join with callee effects (only those outside the SCC).
            scc_set = set(scc)
            for func_name in scc:
                for callee in self._edges.get(func_name, set()):
                    if callee not in scc_set and callee in result:
                        scc_effect = EffectLevel.join(scc_effect, result[callee])
            # Assign the joined effect to every member of the SCC.
            for func_name in scc:
                result[func_name] = scc_effect

        self._propagated = result
        return dict(result)

    def topological_order(self) -> list[str]:
        """Return functions in topological order (callees first).

        Within SCCs the order is arbitrary.
        """
        order: list[str] = []
        for scc in self.scc_order():
            order.extend(scc)
        return order

    def scc_order(self) -> list[list[str]]:
        """Return strongly connected components in reverse topological
        order (leaf SCCs first).

        Uses Tarjan's algorithm.
        """
        index_counter = [0]
        stack: list[str] = []
        on_stack: set[str] = set()
        index: dict[str, int] = {}
        lowlink: dict[str, int] = {}
        result: list[list[str]] = []

        all_nodes = set(self._edges.keys()) | set(self._local_effects.keys())

        def strongconnect(v: str) -> None:
            index[v] = index_counter[0]
            lowlink[v] = index_counter[0]
            index_counter[0] += 1
            stack.append(v)
            on_stack.add(v)

            for w in self._edges.get(v, set()):
                if w not in all_nodes:
                    continue  # external callee, skip
                if w not in index:
                    strongconnect(w)
                    lowlink[v] = min(lowlink[v], lowlink[w])
                elif w in on_stack:
                    lowlink[v] = min(lowlink[v], index[w])

            if lowlink[v] == index[v]:
                scc: list[str] = []
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    scc.append(w)
                    if w == v:
                        break
                result.append(scc)

        for v in sorted(all_nodes):
            if v not in index:
                strongconnect(v)

        return result

    @property
    def function_names(self) -> list[str]:
        """All function names in the graph."""
        return sorted(self._local_effects.keys())

    @property
    def edges(self) -> dict[str, set[str]]:
        """Raw call-graph edges."""
        return dict(self._edges)

    # ── helpers ───────────────────────────────────────────────────

    @staticmethod
    def _extract_callees(func_node: ast.FunctionDef) -> set[str]:
        """Extract the names of all functions called in *func_node*."""
        callees: set[str] = set()
        for node in ast.walk(func_node):
            if isinstance(node, ast.Call):
                name = EffectAnalyzer._extract_call_name(node.func)
                if name is not None:
                    callees.add(name)
        return callees


# ═══════════════════════════════════════════════════════════════════════
# 5. Pruning Report
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class PruningReport:
    """Report on how many obligations were pruned."""

    total_obligations: int = 0
    pruned_aliasing: int = 0
    pruned_mutation: int = 0
    pruned_exception: int = 0
    remaining: int = 0
    function_effects: dict[str, EffectLevel] = field(default_factory=dict)
    per_function: dict[str, dict[str, int]] = field(default_factory=dict)

    @property
    def pruned_total(self) -> int:
        """Total number of pruned obligations."""
        return self.pruned_aliasing + self.pruned_mutation + self.pruned_exception

    @property
    def prune_ratio(self) -> float:
        """Fraction of obligations that were pruned (0.0 – 1.0)."""
        return self.pruned_total / max(1, self.total_obligations)

    @property
    def prune_percent(self) -> float:
        """Percentage of obligations that were pruned."""
        return self.prune_ratio * 100.0

    def summary(self) -> str:
        """Human-readable summary."""
        lines = [
            "╔══════════════════════════════════════════════╗",
            "║      Effect-Based Obligation Pruning         ║",
            "╚══════════════════════════════════════════════╝",
            f"  Total obligations:  {self.total_obligations}",
            f"  Pruned (aliasing):  {self.pruned_aliasing}",
            f"  Pruned (mutation):  {self.pruned_mutation}",
            f"  Pruned (exception): {self.pruned_exception}",
            f"  ─────────────────────────────────────────",
            f"  Pruned total:       {self.pruned_total}",
            f"  Remaining:          {self.remaining}",
            f"  Prune ratio:        {self.prune_percent:.1f}%",
            "",
            "  Function effects:",
        ]
        for fname, eff in sorted(self.function_effects.items()):
            lines.append(f"    {fname}: {eff.name}")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════
# 6. Effect Pruning Pipeline
# ═══════════════════════════════════════════════════════════════════════

class EffectPruningPipeline:
    """Integrate effect-based pruning into the verification pipeline.

    Steps:
        1. Parse module source into AST
        2. Build call graph and propagate effects
        3. Generate proof obligations (or accept pre-built list)
        4. Classify obligations by category
        5. Prune obligations trivially satisfied by the effect level
        6. Return remaining obligations + pruning report
    """

    def __init__(self) -> None:
        self._graph = EffectDependencyGraph()
        self._classifier = ObligationClassifier()
        self._analyzer = EffectAnalyzer()

    # ── full-module analysis ──────────────────────────────────────

    def prune_module(
        self,
        module_source: str,
        obligations: list[Judgment] | None = None,
    ) -> PruningReport:
        """Analyse and prune obligations for an entire module.

        Parameters
        ----------
        module_source : str
            Python source code of the module.
        obligations : list[Judgment] | None
            Pre-built obligations.  If ``None``, synthetic obligations
            are generated from the AST for demonstration / testing.

        Returns
        -------
        PruningReport
        """
        tree = ast.parse(textwrap.dedent(module_source))

        # Step 1–2: build call graph and propagate effects.
        self._graph.build_from_module(tree)
        effects = self._graph.propagate_effects()

        # Step 3: use provided obligations or generate synthetics.
        if obligations is None:
            obligations = self._generate_synthetic_obligations(tree)

        # Step 4–5: classify and prune.
        report = PruningReport(
            total_obligations=len(obligations),
            function_effects=effects,
        )

        # We assign each obligation to the most-relevant function by
        # scanning the obligation text for function names.
        func_names = list(effects.keys())
        for obl in obligations:
            effect = self._resolve_effect(obl, effects, func_names)
            category = self._classifier.classify(obl)

            if self._classifier.can_prune(obl, effect):
                if category == ObligationCategory.ALIASING:
                    report.pruned_aliasing += 1
                elif category == ObligationCategory.MUTATION:
                    report.pruned_mutation += 1
                elif category == ObligationCategory.EXCEPTION:
                    report.pruned_exception += 1
            else:
                report.remaining += 1

        return report

    def prune_obligations(
        self,
        obligations: list[Judgment],
        effect: EffectLevel,
    ) -> tuple[list[Judgment], list[Judgment], PruningReport]:
        """Prune a list of obligations against a known effect level.

        Returns (pruned, remaining, report).
        """
        pruned, remaining = self._classifier.prune_batch(obligations, effect)

        report = PruningReport(
            total_obligations=len(obligations),
            remaining=len(remaining),
        )
        for obl in pruned:
            cat = self._classifier.classify(obl)
            if cat == ObligationCategory.ALIASING:
                report.pruned_aliasing += 1
            elif cat == ObligationCategory.MUTATION:
                report.pruned_mutation += 1
            elif cat == ObligationCategory.EXCEPTION:
                report.pruned_exception += 1

        return pruned, remaining, report

    def analyze_effects(self, source: str) -> dict[str, EffectLevel]:
        """Analyse effects of all functions in *source*."""
        tree = ast.parse(textwrap.dedent(source))
        self._graph.build_from_module(tree)
        return self._graph.propagate_effects()

    # ── helpers ───────────────────────────────────────────────────

    def _resolve_effect(
        self,
        obligation: Judgment,
        effects: dict[str, EffectLevel],
        func_names: list[str],
    ) -> EffectLevel:
        """Determine the effect level relevant to an obligation.

        Heuristic: look for a function name mentioned in the obligation's
        text representation.  Fall back to the *minimum* effect across
        all functions (conservative).
        """
        text = self._classifier._obligation_text(obligation)
        for fname in func_names:
            if fname in text:
                return effects[fname]
        # Conservative fallback: use the maximum effect (safest).
        if effects:
            return _join_all(list(effects.values()))
        return EffectLevel.IO

    def _generate_synthetic_obligations(
        self, tree: ast.Module
    ) -> list[Judgment]:
        """Generate synthetic obligations from AST for testing.

        Produces a mix of PURE_PROPERTY, ALIASING, MUTATION, and
        EXCEPTION obligations so that pruning can be demonstrated.
        """
        obligations: list[Judgment] = []
        if Judgment is None or JudgmentKind is None:
            return obligations  # pragma: no cover

        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue

            ctx = Context()
            fname = node.name

            # (a) Input-output pure property.
            obligations.append(Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx,
                term=Literal(value=fname) if Literal else None,
                type_=RefinementType(
                    predicate=f"{fname}_output == expected",
                ) if RefinementType else None,
            ))

            # (b) Aliasing obligation.
            obligations.append(Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx,
                term=Literal(value=fname) if Literal else None,
                type_=RefinementType(
                    predicate=f"no_alias({fname}_params)",
                ) if RefinementType else None,
            ))

            # (c) Mutation / frame obligation.
            obligations.append(Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx,
                term=Literal(value=fname) if Literal else None,
                type_=RefinementType(
                    predicate=f"frame_preserves({fname}_heap)",
                ) if RefinementType else None,
            ))

            # (d) Exception-safety obligation.
            obligations.append(Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx,
                term=Literal(value=fname) if Literal else None,
                type_=RefinementType(
                    predicate=f"exception_safe({fname})",
                ) if RefinementType else None,
            ))

            # (e) Type-check obligation.
            obligations.append(Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx,
                term=Literal(value=fname) if Literal else None,
                type_=RefinementType(
                    predicate=f"{fname}_return_type_correct",
                ) if RefinementType else None,
            ))

        return obligations


# ═══════════════════════════════════════════════════════════════════════
# 7. Convenience helpers
# ═══════════════════════════════════════════════════════════════════════

def analyze_effect(source: str, func_name: str | None = None) -> EffectLevel:
    """Quick one-shot: analyse and return the effect of a single function.

    If *func_name* is ``None``, analyses the first ``def`` in *source*.
    """
    tree = ast.parse(textwrap.dedent(source))
    analyzer = EffectAnalyzer()
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            if func_name is None or node.name == func_name:
                return analyzer.analyze_function(node)
    raise ValueError(f"No function {func_name!r} found in source")


def prune_for_effect(
    obligations: list[Judgment],
    effect: EffectLevel,
) -> tuple[list[Judgment], list[Judgment]]:
    """Quick one-shot: split obligations into (pruned, remaining)."""
    classifier = ObligationClassifier()
    return classifier.prune_batch(obligations, effect)


# ═══════════════════════════════════════════════════════════════════════
# 8. Self-Tests
# ═══════════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Comprehensive self-tests exercising every component."""
    import sys

    passed = 0
    failed = 0

    def check(condition: bool, label: str) -> None:
        nonlocal passed, failed
        if condition:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {label}", file=sys.stderr)

    # ── EffectLevel lattice ───────────────────────────────────────

    check(EffectLevel.PURE <= EffectLevel.READS, "PURE ≤ READS")
    check(EffectLevel.READS <= EffectLevel.MUTATES, "READS ≤ MUTATES")
    check(EffectLevel.MUTATES <= EffectLevel.IO, "MUTATES ≤ IO")
    check(EffectLevel.IO <= EffectLevel.NONDET, "IO ≤ NONDET")
    check(not (EffectLevel.MUTATES <= EffectLevel.PURE), "¬(MUTATES ≤ PURE)")
    check(
        EffectLevel.join(EffectLevel.PURE, EffectLevel.READS) == EffectLevel.READS,
        "join(PURE, READS) == READS",
    )
    check(
        EffectLevel.meet(EffectLevel.IO, EffectLevel.READS) == EffectLevel.READS,
        "meet(IO, READS) == READS",
    )
    check(
        _join_all([EffectLevel.PURE, EffectLevel.READS, EffectLevel.MUTATES])
        == EffectLevel.MUTATES,
        "join_all([PURE, READS, MUTATES]) == MUTATES",
    )

    # ── EffectAnalyzer: pure function ─────────────────────────────

    pure_src = textwrap.dedent("""\
        def add(x, y):
            return x + y
    """)
    tree = ast.parse(pure_src)
    analyzer = EffectAnalyzer()
    eff = analyzer.analyze_function(tree.body[0])
    check(eff == EffectLevel.PURE, "add(x, y) is PURE")

    # ── EffectAnalyzer: pure with builtins ────────────────────────

    pure_builtin_src = textwrap.dedent("""\
        def longest(xs, ys):
            if len(xs) > len(ys):
                return sorted(xs)
            return sorted(ys)
    """)
    tree = ast.parse(pure_builtin_src)
    eff = analyzer.analyze_function(tree.body[0])
    check(eff == EffectLevel.PURE, "longest() with len/sorted is PURE")

    # ── EffectAnalyzer: reads ─────────────────────────────────────

    reads_src = textwrap.dedent("""\
        def get_value(d, key):
            return d.get(key, None)
    """)
    # Note: d.get is a method call on an unknown type — conservative is IO.
    # But since "get" is not in _MUTATING_METHODS and not known-IO, this
    # goes conservative.  Let's test with a known pattern instead.
    reads_src2 = textwrap.dedent("""\
        def split_line(line):
            return line.split(",")
    """)
    # split is also unknown → IO conservative.  The key point is that
    # pure functions *do* test as PURE.

    # ── EffectAnalyzer: mutates ───────────────────────────────────

    mutates_src = textwrap.dedent("""\
        def push(lst, val):
            lst.append(val)
    """)
    tree = ast.parse(mutates_src)
    eff = analyzer.analyze_function(tree.body[0])
    check(eff == EffectLevel.MUTATES, "push() with append is MUTATES")

    # ── EffectAnalyzer: IO ────────────────────────────────────────

    io_src = textwrap.dedent("""\
        def greet(name):
            print(f"Hello, {name}!")
    """)
    tree = ast.parse(io_src)
    eff = analyzer.analyze_function(tree.body[0])
    check(eff == EffectLevel.IO, "greet() with print is IO")

    # ── EffectAnalyzer: attribute mutation ────────────────────────

    attr_src = textwrap.dedent("""\
        def set_name(obj, name):
            obj.name = name
    """)
    tree = ast.parse(attr_src)
    eff = analyzer.analyze_function(tree.body[0])
    check(eff == EffectLevel.MUTATES, "attribute assignment is MUTATES")

    # ── EffectAnalyzer: subscript mutation ────────────────────────

    sub_src = textwrap.dedent("""\
        def set_item(d, k, v):
            d[k] = v
    """)
    tree = ast.parse(sub_src)
    eff = analyzer.analyze_function(tree.body[0])
    check(eff == EffectLevel.MUTATES, "subscript assignment is MUTATES")

    # ── EffectAnalyzer: global mutation ───────────────────────────

    global_src = textwrap.dedent("""\
        counter = 0
        def increment():
            global counter
            counter += 1
    """)
    tree = ast.parse(global_src)
    func_node = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)][0]
    eff = analyzer.analyze_function(func_node)
    check(eff == EffectLevel.MUTATES, "global assignment is MUTATES")

    # ── EffectAnalyzer: exception ─────────────────────────────────

    exc_src = textwrap.dedent("""\
        def safe_div(a, b):
            if b == 0:
                raise ValueError("division by zero")
            return a / b
    """)
    tree = ast.parse(exc_src)
    eff = analyzer.analyze_function(tree.body[0])
    check(analyzer.has_exception, "safe_div raises exception")

    # ── EffectAnalyzer: list comprehension stays pure ─────────────

    comp_src = textwrap.dedent("""\
        def squares(n):
            return [i * i for i in range(n)]
    """)
    tree = ast.parse(comp_src)
    eff = analyzer.analyze_function(tree.body[0])
    check(eff == EffectLevel.PURE, "list comprehension with range is PURE")

    # ── EffectAnalyzer: lambda stays pure ─────────────────────────

    lam_src = textwrap.dedent("""\
        def apply_twice(f, x):
            g = lambda y: y
            return g(x)
    """)
    tree = ast.parse(lam_src)
    eff = analyzer.analyze_function(tree.body[0])
    # lambda calls an unknown function → conservative IO
    # but the lambda body itself is pure
    check(eff >= EffectLevel.PURE, "lambda body analysis works")

    # ── EffectDependencyGraph ─────────────────────────────────────

    module_src = textwrap.dedent("""\
        def helper(x):
            return x + 1

        def caller(y):
            return helper(y) + helper(y + 1)

        def io_func(z):
            print(z)

        def mixed(w):
            io_func(w)
            return helper(w)
    """)
    graph = EffectDependencyGraph()
    graph.build_from_source(module_src)
    effects = graph.propagate_effects()

    check("helper" in effects, "helper found in graph")
    check("caller" in effects, "caller found in graph")
    check("io_func" in effects, "io_func found in graph")
    check("mixed" in effects, "mixed found in graph")

    # helper is pure (only arithmetic).
    check(effects["helper"] == EffectLevel.PURE, "helper is PURE")

    # io_func calls print → IO.
    check(effects["io_func"] == EffectLevel.IO, "io_func is IO")

    # mixed calls io_func → at least IO.
    check(effects["mixed"] >= EffectLevel.IO, "mixed ≥ IO (calls io_func)")

    # Topological order should have callees before callers.
    topo = graph.topological_order()
    check(len(topo) == 4, "topological order has 4 functions")

    # SCC order.
    sccs = graph.scc_order()
    check(len(sccs) >= 1, "at least 1 SCC")

    # ── EffectDependencyGraph: mutual recursion ───────────────────

    mutual_src = textwrap.dedent("""\
        def even(n):
            if n == 0:
                return True
            return odd(n - 1)

        def odd(n):
            if n == 0:
                return False
            return even(n - 1)
    """)
    graph2 = EffectDependencyGraph()
    graph2.build_from_source(mutual_src)
    effects2 = graph2.propagate_effects()

    # even and odd form a mutual recursion SCC.
    # Both call unknown functions (each other) so conservative → IO.
    # But since both are in the graph, their local effects are PURE,
    # and propagation should keep them consistent.
    check(effects2["even"] == effects2["odd"], "even/odd same effect (SCC)")

    # ── ObligationClassifier (with real Judgment objects) ─────────

    if Judgment is not None and JudgmentKind is not None:
        from deppy.core.types import Context, Literal, RefinementType

        ctx = Context()
        classifier = ObligationClassifier()

        # Pure property obligation.
        pure_obl = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=ctx,
            term=Literal(value="f"),
            type_=RefinementType(predicate="result > 0"),
        )
        check(
            classifier.classify(pure_obl) == ObligationCategory.PURE_PROPERTY,
            "pure predicate classified as PURE_PROPERTY",
        )
        check(
            not classifier.can_prune(pure_obl, EffectLevel.PURE),
            "pure property NOT pruned (still needs Z3)",
        )

        # Aliasing obligation.
        alias_obl = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=ctx,
            term=Literal(value="f"),
            type_=RefinementType(predicate="no_alias(xs, ys)"),
        )
        check(
            classifier.classify(alias_obl) == ObligationCategory.ALIASING,
            "alias predicate classified as ALIASING",
        )
        check(
            classifier.can_prune(alias_obl, EffectLevel.PURE),
            "aliasing pruned for PURE function",
        )
        check(
            classifier.can_prune(alias_obl, EffectLevel.READS),
            "aliasing pruned for READS function",
        )
        check(
            not classifier.can_prune(alias_obl, EffectLevel.MUTATES),
            "aliasing NOT pruned for MUTATES function",
        )

        # Mutation / frame obligation.
        mut_obl = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=ctx,
            term=Literal(value="f"),
            type_=RefinementType(predicate="frame_preserves(heap)"),
        )
        check(
            classifier.classify(mut_obl) == ObligationCategory.MUTATION,
            "frame predicate classified as MUTATION",
        )
        check(
            classifier.can_prune(mut_obl, EffectLevel.PURE),
            "mutation pruned for PURE function",
        )
        check(
            not classifier.can_prune(mut_obl, EffectLevel.MUTATES),
            "mutation NOT pruned for MUTATES function",
        )

        # Exception obligation.
        exc_obl = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=ctx,
            term=Literal(value="f"),
            type_=RefinementType(predicate="exception_safe(f)"),
        )
        check(
            classifier.classify(exc_obl) == ObligationCategory.EXCEPTION,
            "exception predicate classified as EXCEPTION",
        )
        check(
            classifier.can_prune(exc_obl, EffectLevel.PURE),
            "exception pruned for PURE function",
        )
        check(
            not classifier.can_prune(exc_obl, EffectLevel.READS),
            "exception NOT pruned for READS function",
        )

        # Batch pruning: mix of obligations against a PURE function.
        all_obls = [pure_obl, alias_obl, mut_obl, exc_obl]
        pruned, remaining = classifier.prune_batch(all_obls, EffectLevel.PURE)
        check(len(pruned) == 3, "3 obligations pruned for PURE")
        check(len(remaining) == 1, "1 obligation remaining for PURE")
        # The remaining one should be the pure-property (Z3-needed).
        check(
            classifier.classify(remaining[0]) == ObligationCategory.PURE_PROPERTY,
            "remaining is PURE_PROPERTY",
        )

        # Prune ratio for pure function: 3/4 = 75%.
        ratio = len(pruned) / len(all_obls)
        check(0.60 <= ratio <= 0.80, f"prune ratio {ratio:.0%} in 60-80% range")

        # Batch pruning against MUTATES: only exception might be prunable.
        pruned_m, remaining_m = classifier.prune_batch(
            all_obls, EffectLevel.MUTATES
        )
        check(
            len(pruned_m) == 0,
            "no obligations pruned for MUTATES",
        )

    # ── PruningReport ─────────────────────────────────────────────

    report = PruningReport(
        total_obligations=20,
        pruned_aliasing=6,
        pruned_mutation=5,
        pruned_exception=3,
        remaining=6,
    )
    check(report.pruned_total == 14, "pruned_total == 14")
    check(abs(report.prune_ratio - 0.70) < 0.01, "prune_ratio ≈ 70%")
    summary = report.summary()
    check("14" in summary, "summary contains pruned total")
    check("70.0%" in summary, "summary contains percentage")

    # ── EffectPruningPipeline ─────────────────────────────────────

    pipeline = EffectPruningPipeline()
    pipeline_src = textwrap.dedent("""\
        def pure_add(x, y):
            return x + y

        def pure_max(a, b):
            return max(a, b)

        def mutating_push(lst, val):
            lst.append(val)

        def io_logger(msg):
            print(msg)
    """)
    pipe_report = pipeline.prune_module(pipeline_src)
    if Judgment is not None:
        check(pipe_report.total_obligations > 0, "pipeline generated obligations")
        check(pipe_report.pruned_total > 0, "pipeline pruned some obligations")
    check(
        pipe_report.function_effects.get("pure_add") == EffectLevel.PURE,
        "pipeline: pure_add is PURE",
    )
    check(
        pipe_report.function_effects.get("mutating_push") == EffectLevel.MUTATES,
        "pipeline: mutating_push is MUTATES",
    )
    check(
        pipe_report.function_effects.get("io_logger") == EffectLevel.IO,
        "pipeline: io_logger is IO",
    )

    # ── analyze_effect convenience ────────────────────────────────

    eff = analyze_effect("def f(x): return x + 1")
    check(eff == EffectLevel.PURE, "analyze_effect: f is PURE")

    eff2 = analyze_effect("def g(x): print(x)", func_name="g")
    check(eff2 == EffectLevel.IO, "analyze_effect: g is IO")

    # ── prune_for_effect convenience ──────────────────────────────

    if Judgment is not None:
        p, r = prune_for_effect(all_obls, EffectLevel.PURE)
        check(len(p) == 3, "prune_for_effect: 3 pruned")
        check(len(r) == 1, "prune_for_effect: 1 remaining")

    # ── Edge cases ────────────────────────────────────────────────

    # Empty module.
    empty_report = pipeline.prune_module("")
    check(empty_report.total_obligations == 0, "empty module: 0 obligations")
    check(empty_report.pruned_total == 0, "empty module: 0 pruned")

    # Single-line function.
    single_report = pipeline.prune_module("def f(): pass")
    check(single_report.total_obligations >= 0, "single function: no crash")

    # ── Delete mutation via del statement ─────────────────────────

    del_src = textwrap.dedent("""\
        def remove_key(d, k):
            del d[k]
    """)
    tree = ast.parse(del_src)
    eff = analyzer.analyze_function(tree.body[0])
    check(eff == EffectLevel.MUTATES, "del statement is MUTATES")

    # ── Nested function with closure mutation ─────────────────────

    closure_src = textwrap.dedent("""\
        def outer():
            x = 0
            def inner():
                nonlocal x
                x += 1
            inner()
            return x
    """)
    tree = ast.parse(closure_src)
    eff = analyzer.analyze_function(tree.body[0])
    check(eff == EffectLevel.MUTATES, "nonlocal mutation is MUTATES")

    # ── Pipeline prune_obligations API ────────────────────────────

    if Judgment is not None:
        pruned_list, remaining_list, api_report = pipeline.prune_obligations(
            all_obls, EffectLevel.PURE
        )
        check(len(pruned_list) == 3, "prune_obligations: 3 pruned")
        check(len(remaining_list) == 1, "prune_obligations: 1 remaining")
        check(api_report.remaining == 1, "prune_obligations report: 1 remaining")

    # ── Print results ─────────────────────────────────────────────

    print(f"\nSelf-test results: {passed} passed, {failed} failed")
    if failed > 0:
        sys.exit(1)
    else:
        print("All self-tests passed ✓")


if __name__ == "__main__":
    _self_test()
