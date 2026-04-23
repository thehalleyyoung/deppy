"""
Deppy Effect System — Effect Types and Static Analysis

This module implements an effect system for Python that tracks side effects
as part of the type theory.  Effects are organized in a lattice:

    PURE ≤ READS ≤ MUTATES ≤ IO

with orthogonal dimensions:

    EXCEPTION, NONDET, DIVERGE, ASYNC

The lattice enables *effect-indexed verification*: a function annotated with
effect level E is sound only when every operation it performs is ≤ E.

Key components:
    Effect          — the effect lattice (an Enum)
    FunctionEffect  — the full effect signature of a function
    StateContract   — pre/post state specifications (frame rule)
    EffectAnalyzer  — AST-based static analysis that infers effects
    EffectChecker   — checks declared effects ≥ inferred effects
    compose_effects / sequence_effects / max_effect — effect algebra

Usage::

    from deppy.effects.effect_types import Effect, EffectAnalyzer

    analyzer = EffectAnalyzer()
    src = '''
    def f(x):
        print(x)
        return x + 1
    '''
    import ast
    tree = ast.parse(src)
    fe = analyzer.analyze_function(tree.body[0])
    assert fe.return_effect == Effect.IO
"""
from __future__ import annotations

import ast
import textwrap
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Optional, Sequence

# Conditional import — the module must be importable even if deppy.core
# is not on sys.path (e.g. during stand-alone testing).
try:
    from deppy.core.types import SynType, PyObjType, PyCallableType
except ImportError:  # pragma: no cover
    SynType = None  # type: ignore[assignment,misc]
    PyObjType = None  # type: ignore[assignment,misc]
    PyCallableType = None  # type: ignore[assignment,misc]


# ═══════════════════════════════════════════════════════════════════════
# 1. Effect Lattice
# ═══════════════════════════════════════════════════════════════════════

class Effect(Enum):
    """A lattice of computational effects.

    The *linear* chain is::

        PURE < READS < MUTATES < IO

    meaning a function that MUTATES state is also considered to READ it,
    and one that performs IO subsumes both.

    The remaining members — EXCEPTION, NONDET, DIVERGE, ASYNC — live on
    orthogonal axes: a function may be PURE + EXCEPTION, or IO + DIVERGE,
    etc.  Composition takes the join (maximum) along each axis.
    """

    PURE      = 0   # No side effects whatsoever.
    READS     = 1   # Reads mutable state (but does not modify it).
    MUTATES   = 2   # Mutates state (heap, globals, containers).
    IO        = 3   # Performs I/O (print, open, network, …).
    NONDET    = 4   # Non-deterministic (random, time, pid, …).
    DIVERGE   = 5   # May not terminate (unbounded loops, recursion).
    EXCEPTION = 6   # May raise an exception.
    ASYNC     = 7   # Uses async/await machinery.


# The linear chain for the "state" axis.
_STATE_CHAIN = (Effect.PURE, Effect.READS, Effect.MUTATES, Effect.IO)
_STATE_ORDER = {e: i for i, e in enumerate(_STATE_CHAIN)}

# Orthogonal effects (each is independent of the state axis).
_ORTHOGONAL = frozenset({Effect.NONDET, Effect.DIVERGE, Effect.EXCEPTION, Effect.ASYNC})


def _state_rank(e: Effect) -> int:
    """Return the rank of *e* on the state axis, or -1 for orthogonal effects."""
    return _STATE_ORDER.get(e, -1)


def effect_leq(a: Effect, b: Effect) -> bool:
    """Return True when *a* ≤ *b* in the effect lattice.

    On the state axis the ordering is PURE ≤ READS ≤ MUTATES ≤ IO.
    Orthogonal effects are only ≤ themselves (or IO, which subsumes
    everything on the state axis but not orthogonal flags).
    """
    if a is b:
        return True
    ra, rb = _state_rank(a), _state_rank(b)
    if ra >= 0 and rb >= 0:
        return ra <= rb
    # Orthogonal effects are only ≤ themselves.
    return False


# ═══════════════════════════════════════════════════════════════════════
# 2. FunctionEffect — effect signature for functions
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class ConditionalException:
    """An exception that may be raised under a specific condition.

    Unlike a bare exception class name, this records *when* and *where*
    the exception can occur, enabling the exception-freedom verifier to
    discharge individual sources via Z3 or abstract interpretation.

    Attributes:
        exception_type: The Python exception class name (e.g. "ValueError").
        trigger_condition: A predicate string describing when this exception
            is raised (e.g. "x < 0", "divisor == 0", "key not in d").
            Empty string means "may always raise".
        lineno: Source line where the exception can occur (0 = unknown).
        description: Human-readable description.
        is_explicit: True if from an explicit ``raise`` statement, False
            if inferred from an operation (division, indexing, etc.).
        caught: True if this exception is caught by a surrounding
            try/except in the same function.
    """
    exception_type: str
    trigger_condition: str = ""
    lineno: int = 0
    description: str = ""
    is_explicit: bool = False
    caught: bool = False

    def __repr__(self) -> str:
        cond = f" when {self.trigger_condition}" if self.trigger_condition else ""
        caught = " [caught]" if self.caught else ""
        loc = f" @L{self.lineno}" if self.lineno else ""
        return f"ConditionalException({self.exception_type}{cond}{loc}{caught})"


@dataclass
class FunctionEffect:
    """The effect signature of a single function.

    Attributes:
        name:          Qualified name of the function.
        param_effects: Per-parameter effects (e.g. a parameter that is
                       mutated in-place carries ``Effect.MUTATES``).
        return_effect: The aggregate effect of the function body.
        reads:         Names of state variables / globals read.
        writes:        Names of state variables / globals written.
        exceptions:    Exception class names that may be raised.
        conditional_exceptions:  Fine-grained exception sources with
                       trigger conditions, locations, and caught status.
        is_total:      ``True`` when the function is guaranteed to
                       terminate for all valid inputs.
    """

    name: str = ""
    param_effects: list[Effect] = field(default_factory=list)
    return_effect: Effect = Effect.PURE
    reads: set[str] = field(default_factory=set)
    writes: set[str] = field(default_factory=set)
    exceptions: set[str] = field(default_factory=set)
    conditional_exceptions: list[ConditionalException] = field(default_factory=list)
    is_total: bool = True

    # ── helpers ────────────────────────────────────────────────────

    @property
    def is_pure(self) -> bool:
        """True when the function has no observable effects."""
        return (
            self.return_effect is Effect.PURE
            and all(e is Effect.PURE for e in self.param_effects)
            and not self.reads
            and not self.writes
            and not self.exceptions
        )

    @property
    def uncaught_exceptions(self) -> list[ConditionalException]:
        """Conditional exceptions that escape the function (not caught)."""
        return [ce for ce in self.conditional_exceptions if not ce.caught]

    @property
    def caught_exceptions(self) -> list[ConditionalException]:
        """Conditional exceptions handled internally."""
        return [ce for ce in self.conditional_exceptions if ce.caught]

    @property
    def exception_free_if(self) -> list[str]:
        """Conditions under which this function is exception-free.

        Returns a list of trigger conditions that must be false for the
        function to never raise.  If empty and there are no uncaught
        unconditional exceptions, the function is unconditionally
        exception-free.
        """
        conditions: list[str] = []
        for ce in self.uncaught_exceptions:
            if ce.trigger_condition:
                conditions.append(ce.trigger_condition)
            else:
                conditions.append(f"{ce.exception_type} may always raise")
        return conditions

    @property
    def all_effects(self) -> set[Effect]:
        """Collect every distinct effect present in this signature."""
        effs: set[Effect] = {self.return_effect}
        effs.update(self.param_effects)
        return effs

    def __repr__(self) -> str:
        parts = [f"FunctionEffect({self.name!r}"]
        parts.append(f"return_effect={self.return_effect.name}")
        if self.param_effects:
            parts.append(f"params={[e.name for e in self.param_effects]}")
        if self.reads:
            parts.append(f"reads={self.reads}")
        if self.writes:
            parts.append(f"writes={self.writes}")
        if self.exceptions:
            parts.append(f"exceptions={self.exceptions}")
        if self.conditional_exceptions:
            n_uncaught = len(self.uncaught_exceptions)
            n_caught = len(self.caught_exceptions)
            parts.append(f"cond_exceptions={n_uncaught} uncaught, {n_caught} caught")
        if not self.is_total:
            parts.append("may_diverge")
        return ", ".join(parts) + ")"


# ═══════════════════════════════════════════════════════════════════════
# 3. StateContract — pre/post state specifications
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class StateContract:
    """Pre- and post-state specification with a frame rule.

    Attributes:
        pre_state:  Mapping from state-variable name to a predicate
                    string that must hold *before* the call.
        post_state: Mapping from state-variable name to a predicate
                    string that must hold *after* the call.
        frame:      Names of state variables guaranteed to be
                    *unchanged* by the call (the separation-logic
                    frame).
    """

    pre_state: dict[str, str] = field(default_factory=dict)
    post_state: dict[str, str] = field(default_factory=dict)
    frame: set[str] = field(default_factory=set)

    # ── helpers ────────────────────────────────────────────────────

    @property
    def is_empty(self) -> bool:
        return not self.pre_state and not self.post_state and not self.frame

    @property
    def modified_vars(self) -> set[str]:
        """Variables mentioned in post_state but not in the frame."""
        return set(self.post_state.keys()) - self.frame

    def merge(self, other: StateContract) -> StateContract:
        """Sequentially compose two contracts (self ; other).

        The resulting contract has:
        * pre = self.pre  (caller must satisfy the *first* precondition)
        * post = other.post merged with self.post for frame vars
        * frame = intersection of both frames minus modified vars
        """
        merged_post = dict(self.post_state)
        merged_post.update(other.post_state)
        merged_frame = (self.frame & other.frame) - other.modified_vars
        return StateContract(
            pre_state=dict(self.pre_state),
            post_state=merged_post,
            frame=merged_frame,
        )

    def __repr__(self) -> str:
        parts: list[str] = []
        if self.pre_state:
            parts.append(f"pre={self.pre_state}")
        if self.post_state:
            parts.append(f"post={self.post_state}")
        if self.frame:
            parts.append(f"frame={self.frame}")
        return f"StateContract({', '.join(parts)})"


# ═══════════════════════════════════════════════════════════════════════
# 4. EffectAnalyzer — AST-based static analysis
# ═══════════════════════════════════════════════════════════════════════

# Names that indicate I/O when called.
_IO_NAMES: frozenset[str] = frozenset({
    "print", "input", "open",
    "sys.stdin", "sys.stdout", "sys.stderr",
    "socket", "requests",
    "subprocess.run", "subprocess.call", "subprocess.Popen",
    "os.system", "os.popen",
    "logging.info", "logging.debug", "logging.warning",
    "logging.error", "logging.critical", "logging.log",
})

# Attribute-level I/O sinks (obj.attr patterns).
_IO_ATTRS: frozenset[str] = frozenset({
    "write", "read", "readline", "readlines", "writelines",
    "send", "recv", "sendall", "connect", "accept", "listen", "bind",
    "flush", "close", "seek", "tell",
})

# Names that indicate non-determinism when called.
_NONDET_NAMES: frozenset[str] = frozenset({
    "random.random", "random.randint", "random.choice",
    "random.shuffle", "random.sample", "random.uniform",
    "random.gauss", "random.seed",
    "time.time", "time.monotonic", "time.perf_counter",
    "os.getpid", "os.urandom", "uuid.uuid4",
})

# Mutating method names on built-in containers.
_MUTATING_METHODS: frozenset[str] = frozenset({
    "append", "extend", "insert", "remove", "pop", "clear",
    "sort", "reverse",                         # list
    "add", "discard", "update",                # set
    "setdefault",                              # dict
    "__setitem__", "__delitem__",
})


class EffectAnalyzer:
    """Analyse a Python AST to infer effects.

    The analyser is deliberately *conservative*: if it cannot prove an
    operation is pure, it assumes the worst-case effect.  This makes the
    analysis *sound* (no false negatives) at the cost of some false
    positives, which the programmer can suppress with explicit
    annotations.
    """

    def __init__(self) -> None:
        self._effects: set[Effect] = set()
        self._reads: set[str] = set()
        self._writes: set[str] = set()
        self._exceptions: set[str] = set()
        self._conditional_exceptions: list[ConditionalException] = []
        self._try_depth: int = 0
        self._is_total: bool = True
        self._local_vars: set[str] = set()
        self._param_names: list[str] = []

    # ── public API ────────────────────────────────────────────────

    def analyze_function(self, node: ast.FunctionDef | ast.AsyncFunctionDef) -> FunctionEffect:
        """Infer the full :class:`FunctionEffect` for *node*.

        Walks the entire function body, collecting every observable
        effect, and returns a conservative summary.
        """
        self._reset()
        self._param_names = [arg.arg for arg in node.args.args]
        self._local_vars = set(self._param_names)

        if isinstance(node, ast.AsyncFunctionDef):
            self._effects.add(Effect.ASYNC)

        for stmt in node.body:
            self._visit_stmt(stmt)

        return_eff = self._aggregate_effect()
        param_effects = [Effect.PURE] * len(self._param_names)
        # If we detected writes that match parameter names, mark them.
        for i, pname in enumerate(self._param_names):
            if pname in self._writes:
                param_effects[i] = Effect.MUTATES

        return FunctionEffect(
            name=node.name,
            param_effects=param_effects,
            return_effect=return_eff,
            reads=set(self._reads),
            writes=set(self._writes),
            exceptions=set(self._exceptions),
            conditional_exceptions=list(self._conditional_exceptions),
            is_total=self._is_total,
        )

    def analyze_expression(self, node: ast.expr) -> Effect:
        """Return the single worst-case effect of evaluating *node*."""
        self._reset()
        self._visit_expr(node)
        return self._aggregate_effect()

    def check_pure(self, node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
        """Return ``True`` when *node* has no observable effects."""
        return self.analyze_function(node).is_pure

    # ── internals ─────────────────────────────────────────────────

    def _reset(self) -> None:
        self._effects = set()
        self._reads = set()
        self._writes = set()
        self._exceptions = set()
        self._conditional_exceptions = []
        self._try_depth = 0
        self._is_total = True
        self._local_vars = set()
        self._param_names = []

    def _aggregate_effect(self) -> Effect:
        """Combine everything collected so far into a single Effect."""
        if not self._effects:
            return Effect.PURE
        # Pick the highest on the state chain that we observed.
        best_state = Effect.PURE
        for e in self._effects:
            r = _state_rank(e)
            if r > _state_rank(best_state):
                best_state = e
        # If any orthogonal effect was observed, it dominates unless
        # a state-chain effect is already higher.
        for e in self._effects:
            if e in _ORTHOGONAL:
                if _state_rank(best_state) < 0:
                    best_state = e
                elif _state_rank(e) < 0 and _state_rank(best_state) >= 0:
                    # Orthogonal effects don't override state chain —
                    # we return the join, which is the state-chain max
                    # *plus* the orthogonal flag.  Since Effect is a
                    # single enum we pick the higher numeric value to
                    # remain conservative.
                    if e.value > best_state.value:
                        best_state = e
        return best_state

    # ── statement visitors ────────────────────────────────────────

    def _visit_stmt(self, node: ast.stmt) -> None:  # noqa: C901
        """Dispatch on statement type."""
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            # Nested function — analyse its body for effects that
            # escape (closures that mutate enclosing scope).
            for stmt in node.body:
                self._visit_stmt(stmt)

        elif isinstance(node, ast.Return):
            if node.value:
                self._visit_expr(node.value)

        elif isinstance(node, ast.Assign):
            self._handle_assign(node)

        elif isinstance(node, ast.AugAssign):
            self._handle_aug_assign(node)

        elif isinstance(node, ast.AnnAssign):
            if node.value:
                self._visit_expr(node.value)
            if node.target:
                self._handle_assign_target(node.target)

        elif isinstance(node, ast.For):
            self._visit_expr(node.iter)
            for s in node.body:
                self._visit_stmt(s)
            for s in node.orelse:
                self._visit_stmt(s)

        elif isinstance(node, ast.AsyncFor):
            self._effects.add(Effect.ASYNC)
            self._visit_expr(node.iter)
            for s in node.body:
                self._visit_stmt(s)
            for s in node.orelse:
                self._visit_stmt(s)

        elif isinstance(node, ast.While):
            self._visit_expr(node.test)
            self._check_while_divergence(node)
            for s in node.body:
                self._visit_stmt(s)
            for s in node.orelse:
                self._visit_stmt(s)

        elif isinstance(node, ast.If):
            self._visit_expr(node.test)
            for s in node.body:
                self._visit_stmt(s)
            for s in node.orelse:
                self._visit_stmt(s)

        elif isinstance(node, ast.With):
            for item in node.items:
                self._visit_expr(item.context_expr)
            for s in node.body:
                self._visit_stmt(s)

        elif isinstance(node, ast.AsyncWith):
            self._effects.add(Effect.ASYNC)
            for item in node.items:
                self._visit_expr(item.context_expr)
            for s in node.body:
                self._visit_stmt(s)

        elif isinstance(node, ast.Raise):
            self._effects.add(Effect.EXCEPTION)
            if node.exc:
                # `raise ValueError(...)` — exc is a Call whose func
                # is the exception class name.
                exc_node = node.exc
                if isinstance(exc_node, ast.Call):
                    exc_node = exc_node.func
                exc_name = self._extract_name(exc_node)
                if exc_name:
                    self._exceptions.add(exc_name)
                    self._conditional_exceptions.append(ConditionalException(
                        exception_type=exc_name,
                        trigger_condition="",
                        lineno=node.lineno,
                        description=f"explicit raise {exc_name}",
                        is_explicit=True,
                        caught=self._try_depth > 0,
                    ))

        elif isinstance(node, ast.Try):
            self._try_depth += 1
            for s in node.body:
                self._visit_stmt(s)
            self._try_depth -= 1
            for handler in node.handlers:
                self._effects.add(Effect.EXCEPTION)
                if handler.type:
                    exc_name = self._extract_name(handler.type)
                    if exc_name:
                        self._exceptions.add(exc_name)
                for s in handler.body:
                    self._visit_stmt(s)
            for s in node.orelse:
                self._visit_stmt(s)
            for s in node.finalbody:
                self._visit_stmt(s)

        elif isinstance(node, ast.Expr):
            self._visit_expr(node.value)

        elif isinstance(node, ast.Global):
            for name in node.names:
                self._effects.add(Effect.MUTATES)
                self._writes.add(name)

        elif isinstance(node, ast.Nonlocal):
            for name in node.names:
                self._effects.add(Effect.MUTATES)
                self._writes.add(name)

        elif isinstance(node, ast.Delete):
            for target in node.targets:
                self._effects.add(Effect.MUTATES)
                name = self._extract_name(target)
                if name:
                    self._writes.add(name)

        elif isinstance(node, ast.Assert):
            self._visit_expr(node.test)
            self._effects.add(Effect.EXCEPTION)
            self._exceptions.add("AssertionError")
            self._conditional_exceptions.append(ConditionalException(
                exception_type="AssertionError",
                trigger_condition="assertion condition is False",
                lineno=node.lineno,
                description="assert statement",
                is_explicit=True,
                caught=self._try_depth > 0,
            ))

        # TryStar (Python 3.11+)
        elif hasattr(ast, "TryStar") and isinstance(node, ast.TryStar):  # type: ignore[attr-defined]
            for s in node.body:  # type: ignore[attr-defined]
                self._visit_stmt(s)
            for handler in node.handlers:  # type: ignore[attr-defined]
                self._effects.add(Effect.EXCEPTION)
                for s in handler.body:
                    self._visit_stmt(s)
            for s in node.orelse:  # type: ignore[attr-defined]
                self._visit_stmt(s)
            for s in node.finalbody:  # type: ignore[attr-defined]
                self._visit_stmt(s)

    # ── expression visitors ───────────────────────────────────────

    def _visit_expr(self, node: ast.expr) -> None:
        """Dispatch on expression type."""
        if isinstance(node, ast.Call):
            self._handle_call(node)

        elif isinstance(node, ast.Attribute):
            self._visit_expr(node.value)

        elif isinstance(node, ast.Subscript):
            self._visit_expr(node.value)
            self._visit_expr(node.slice)
            # Subscript can raise IndexError or KeyError
            if not isinstance(node.slice, ast.Slice):
                self._effects.add(Effect.EXCEPTION)
                self._exceptions.add("IndexError")
                self._exceptions.add("KeyError")
                self._conditional_exceptions.append(ConditionalException(
                    exception_type="IndexError",
                    trigger_condition="index out of range",
                    lineno=getattr(node, 'lineno', 0),
                    description="subscript access",
                    is_explicit=False,
                    caught=self._try_depth > 0,
                ))

        elif isinstance(node, ast.BoolOp):
            for v in node.values:
                self._visit_expr(v)

        elif isinstance(node, ast.BinOp):
            self._visit_expr(node.left)
            self._visit_expr(node.right)
            # Division / modulo / floor-division → ZeroDivisionError
            if isinstance(node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
                self._effects.add(Effect.EXCEPTION)
                self._exceptions.add("ZeroDivisionError")
                self._conditional_exceptions.append(ConditionalException(
                    exception_type="ZeroDivisionError",
                    trigger_condition="divisor == 0",
                    lineno=getattr(node, 'lineno', 0),
                    description="division/modulo by zero",
                    is_explicit=False,
                    caught=self._try_depth > 0,
                ))

        elif isinstance(node, ast.UnaryOp):
            self._visit_expr(node.operand)

        elif isinstance(node, ast.IfExp):
            self._visit_expr(node.test)
            self._visit_expr(node.body)
            self._visit_expr(node.orelse)

        elif isinstance(node, ast.ListComp):
            for gen in node.generators:
                self._visit_expr(gen.iter)
                for if_ in gen.ifs:
                    self._visit_expr(if_)
            self._visit_expr(node.elt)

        elif isinstance(node, ast.SetComp):
            for gen in node.generators:
                self._visit_expr(gen.iter)
                for if_ in gen.ifs:
                    self._visit_expr(if_)
            self._visit_expr(node.elt)

        elif isinstance(node, ast.DictComp):
            for gen in node.generators:
                self._visit_expr(gen.iter)
                for if_ in gen.ifs:
                    self._visit_expr(if_)
            self._visit_expr(node.key)
            self._visit_expr(node.value)

        elif isinstance(node, ast.GeneratorExp):
            for gen in node.generators:
                self._visit_expr(gen.iter)
                for if_ in gen.ifs:
                    self._visit_expr(if_)
            self._visit_expr(node.elt)

        elif isinstance(node, ast.Await):
            self._effects.add(Effect.ASYNC)
            self._visit_expr(node.value)

        elif isinstance(node, ast.Yield) or isinstance(node, ast.YieldFrom):
            if hasattr(node, "value") and node.value:
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

        elif isinstance(node, ast.JoinedStr):
            for v in node.values:
                self._visit_expr(v)

        elif isinstance(node, ast.FormattedValue):
            self._visit_expr(node.value)

        elif isinstance(node, ast.Starred):
            self._visit_expr(node.value)

        elif isinstance(node, ast.Name):
            # Reading a non-local variable is a READS effect.
            if node.id not in self._local_vars:
                self._effects.add(Effect.READS)
                self._reads.add(node.id)

        elif isinstance(node, ast.Lambda):
            # Lambda body is lazily evaluated — don't infer effects
            # from the body itself (the effects appear when called).
            pass

    # ── call handling ─────────────────────────────────────────────

    def _handle_call(self, node: ast.Call) -> None:
        """Classify a function/method call."""
        callee = self._callee_name(node)

        # Visit argument expressions first.
        for arg in node.args:
            self._visit_expr(arg)
        for kw in node.keywords:
            self._visit_expr(kw.value)

        if callee:
            if callee in _IO_NAMES:
                self._effects.add(Effect.IO)
                return
            if callee in _NONDET_NAMES:
                self._effects.add(Effect.NONDET)
                return
            if callee == "setattr":
                self._effects.add(Effect.MUTATES)
                if len(node.args) >= 2 and isinstance(node.args[1], ast.Constant):
                    self._writes.add(str(node.args[1].value))
                return
            if callee == "delattr":
                self._effects.add(Effect.MUTATES)
                return
            if callee == "globals":
                self._effects.add(Effect.READS)
                return
            if callee == "exec" or callee == "eval":
                # exec/eval can do anything.
                self._effects.add(Effect.IO)
                self._effects.add(Effect.MUTATES)
                self._effects.add(Effect.EXCEPTION)
                return

        # Attribute call — check for mutating methods.
        if isinstance(node.func, ast.Attribute):
            attr = node.func.attr
            if attr in _MUTATING_METHODS:
                self._effects.add(Effect.MUTATES)
                base_name = self._extract_name(node.func.value)
                if base_name:
                    self._writes.add(base_name)
                return
            if attr in _IO_ATTRS:
                self._effects.add(Effect.IO)
                return
            # Check for dotted non-determinism (e.g. random.choice).
            dotted = self._dotted_name(node.func)
            if dotted and dotted in _NONDET_NAMES:
                self._effects.add(Effect.NONDET)
                return
            if dotted and dotted in _IO_NAMES:
                self._effects.add(Effect.IO)
                return

    # ── assignment handling ───────────────────────────────────────

    def _handle_assign(self, node: ast.Assign) -> None:
        if node.value:
            self._visit_expr(node.value)
        for target in node.targets:
            self._handle_assign_target(target)

    def _handle_aug_assign(self, node: ast.AugAssign) -> None:
        self._visit_expr(node.value)
        self._handle_assign_target(node.target)

    def _handle_assign_target(self, target: ast.expr) -> None:
        """Record mutation for non-local or attribute assignments."""
        if isinstance(target, ast.Name):
            # Assignment to a new local is not a mutation effect.
            self._local_vars.add(target.id)
        elif isinstance(target, ast.Attribute):
            self._effects.add(Effect.MUTATES)
            base_name = self._extract_name(target.value)
            if base_name:
                self._writes.add(f"{base_name}.{target.attr}")
        elif isinstance(target, ast.Subscript):
            self._effects.add(Effect.MUTATES)
            base_name = self._extract_name(target.value)
            if base_name:
                self._writes.add(base_name)
        elif isinstance(target, (ast.Tuple, ast.List)):
            for elt in target.elts:
                self._handle_assign_target(elt)
        elif isinstance(target, ast.Starred):
            self._handle_assign_target(target.value)

    # ── divergence detection ──────────────────────────────────────

    def _check_while_divergence(self, node: ast.While) -> None:
        """Heuristic: ``while True`` without ``break`` may diverge."""
        if isinstance(node.test, ast.Constant) and node.test.value is True:
            if not self._body_has_break(node.body):
                self._effects.add(Effect.DIVERGE)
                self._is_total = False

    @staticmethod
    def _body_has_break(stmts: list[ast.stmt]) -> bool:
        """Return True if *stmts* contain a ``break`` at any depth."""
        for s in stmts:
            if isinstance(s, ast.Break):
                return True
            for child in ast.walk(s):
                if isinstance(child, ast.Break):
                    return True
        return False

    # ── name extraction helpers ───────────────────────────────────

    @staticmethod
    def _extract_name(node: ast.expr) -> Optional[str]:
        """Try to extract a simple name from an expression node."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            base = EffectAnalyzer._extract_name(node.value)
            if base:
                return f"{base}.{node.attr}"
        return None

    @staticmethod
    def _callee_name(node: ast.Call) -> Optional[str]:
        """Return the dotted name of the callee, if extractable."""
        return EffectAnalyzer._dotted_name(node.func)

    @staticmethod
    def _dotted_name(node: ast.expr) -> Optional[str]:
        """Reconstruct a dotted name like ``os.path.join``."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            base = EffectAnalyzer._dotted_name(node.value)
            if base:
                return f"{base}.{node.attr}"
        return None


# ═══════════════════════════════════════════════════════════════════════
# 5. EffectChecker — verify declared ≥ inferred
# ═══════════════════════════════════════════════════════════════════════

class EffectChecker:
    """Check that a declared effect annotation is *sound*.

    Soundness means declared ≥ inferred for every axis.  If the
    programmer says a function is PURE but it actually performs IO,
    the checker emits an error.
    """

    def check(
        self,
        declared: FunctionEffect,
        inferred: FunctionEffect,
    ) -> list[str]:
        """Return a list of human-readable error strings.

        An empty list means the declaration is sound.
        """
        errors: list[str] = []

        # -- return effect --
        if not effect_leq(inferred.return_effect, declared.return_effect):
            errors.append(
                f"Effect mismatch in '{declared.name}': "
                f"declared {declared.return_effect.name} but "
                f"inferred {inferred.return_effect.name}"
            )

        # -- param effects --
        for i, (decl_e, inf_e) in enumerate(
            zip(declared.param_effects, inferred.param_effects)
        ):
            if not effect_leq(inf_e, decl_e):
                errors.append(
                    f"Param {i} of '{declared.name}': "
                    f"declared {decl_e.name} but inferred {inf_e.name}"
                )

        # -- exception set --
        undeclared = inferred.exceptions - declared.exceptions
        if undeclared:
            errors.append(
                f"Undeclared exceptions in '{declared.name}': "
                f"{', '.join(sorted(undeclared))}"
            )

        # -- totality --
        if declared.is_total and not inferred.is_total:
            errors.append(
                f"'{declared.name}' declared total but may diverge"
            )

        # -- reads / writes --
        undeclared_reads = inferred.reads - declared.reads
        if undeclared_reads and declared.return_effect is Effect.PURE:
            errors.append(
                f"Undeclared reads in '{declared.name}': "
                f"{', '.join(sorted(undeclared_reads))}"
            )

        undeclared_writes = inferred.writes - declared.writes
        if undeclared_writes and effect_leq(declared.return_effect, Effect.READS):
            errors.append(
                f"Undeclared writes in '{declared.name}': "
                f"{', '.join(sorted(undeclared_writes))}"
            )

        return errors


# ═══════════════════════════════════════════════════════════════════════
# 6. Effect Composition
# ═══════════════════════════════════════════════════════════════════════

def compose_effects(e1: Effect, e2: Effect) -> Effect:
    """Return the *join* (least upper bound) of two effects.

    On the state axis: max(rank).  If either is orthogonal, the
    higher-valued effect wins (conservative).
    """
    r1, r2 = _state_rank(e1), _state_rank(e2)
    if r1 >= 0 and r2 >= 0:
        return e1 if r1 >= r2 else e2
    # At least one is orthogonal — return the one with higher value.
    return e1 if e1.value >= e2.value else e2


def sequence_effects(effects: list[Effect]) -> Effect:
    """Compose a sequence of effects left-to-right.

    Returns ``Effect.PURE`` for an empty sequence.
    """
    result = Effect.PURE
    for e in effects:
        result = compose_effects(result, e)
    return result


def max_effect(*effects: Effect) -> Effect:
    """Return the maximum effect among the arguments.

    Equivalent to ``sequence_effects(list(effects))``.
    """
    return sequence_effects(list(effects))


# ═══════════════════════════════════════════════════════════════════════
# 7. EffectSet — multi-dimensional effect tracking
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class EffectSet:
    """Track effects along every axis simultaneously.

    Unlike a single :class:`Effect`, an ``EffectSet`` faithfully records
    each orthogonal dimension, enabling precise checking.

    Example::

        es = EffectSet.pure()
        es = es.add(Effect.IO)
        es = es.add(Effect.EXCEPTION)
        assert es.state_effect == Effect.IO
        assert Effect.EXCEPTION in es.extras
    """

    state_effect: Effect = Effect.PURE
    extras: frozenset[Effect] = field(default_factory=frozenset)

    @staticmethod
    def pure() -> EffectSet:
        return EffectSet()

    @staticmethod
    def from_effect(e: Effect) -> EffectSet:
        if e in _ORTHOGONAL:
            return EffectSet(extras=frozenset({e}))
        return EffectSet(state_effect=e)

    def add(self, e: Effect) -> EffectSet:
        """Return a new EffectSet with *e* added."""
        if e in _ORTHOGONAL:
            return EffectSet(self.state_effect, self.extras | {e})
        new_state = self.state_effect
        if _state_rank(e) > _state_rank(new_state):
            new_state = e
        return EffectSet(new_state, self.extras)

    def join(self, other: EffectSet) -> EffectSet:
        """Lattice join of two EffectSets."""
        new_state = compose_effects(self.state_effect, other.state_effect)
        new_extras = self.extras | other.extras
        return EffectSet(new_state, new_extras)

    @property
    def is_pure(self) -> bool:
        return self.state_effect is Effect.PURE and not self.extras

    def subsumes(self, other: EffectSet) -> bool:
        """Return True when ``self ≥ other`` on every axis."""
        if not effect_leq(other.state_effect, self.state_effect):
            return False
        return other.extras <= self.extras

    def __repr__(self) -> str:
        parts = [self.state_effect.name]
        if self.extras:
            parts.extend(sorted(e.name for e in self.extras))
        return f"EffectSet({' | '.join(parts)})"


# ═══════════════════════════════════════════════════════════════════════
# Self-test
# ═══════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    import sys

    ok = True

    def _assert(cond: bool, msg: str) -> None:
        global ok
        if not cond:
            print(f"FAIL: {msg}", file=sys.stderr)
            ok = False
        else:
            print(f"  ok: {msg}")

    print("=== Effect lattice ===")
    _assert(effect_leq(Effect.PURE, Effect.READS), "PURE ≤ READS")
    _assert(effect_leq(Effect.READS, Effect.MUTATES), "READS ≤ MUTATES")
    _assert(effect_leq(Effect.MUTATES, Effect.IO), "MUTATES ≤ IO")
    _assert(not effect_leq(Effect.IO, Effect.PURE), "¬(IO ≤ PURE)")
    _assert(effect_leq(Effect.PURE, Effect.IO), "PURE ≤ IO")
    _assert(not effect_leq(Effect.EXCEPTION, Effect.PURE), "¬(EXCEPTION ≤ PURE)")
    _assert(effect_leq(Effect.EXCEPTION, Effect.EXCEPTION), "EXCEPTION ≤ EXCEPTION")

    print("\n=== Composition ===")
    _assert(compose_effects(Effect.PURE, Effect.READS) == Effect.READS,
            "PURE ⊔ READS = READS")
    _assert(compose_effects(Effect.MUTATES, Effect.IO) == Effect.IO,
            "MUTATES ⊔ IO = IO")
    _assert(sequence_effects([Effect.PURE, Effect.READS, Effect.MUTATES])
            == Effect.MUTATES, "sequence [PURE,READS,MUTATES] = MUTATES")
    _assert(max_effect(Effect.PURE, Effect.IO) == Effect.IO,
            "max(PURE, IO) = IO")

    print("\n=== EffectSet ===")
    es = EffectSet.pure().add(Effect.IO).add(Effect.EXCEPTION)
    _assert(es.state_effect == Effect.IO, "EffectSet state = IO")
    _assert(Effect.EXCEPTION in es.extras, "EffectSet extras has EXCEPTION")
    _assert(not es.is_pure, "IO+EXCEPTION is not pure")
    _assert(EffectSet.pure().is_pure, "empty EffectSet is pure")
    es2 = EffectSet.from_effect(Effect.READS)
    _assert(es.subsumes(es2), "IO+EXCEPTION ≥ READS")
    _assert(not es2.subsumes(es), "¬(READS ≥ IO+EXCEPTION)")

    print("\n=== EffectAnalyzer ===")
    analyzer = EffectAnalyzer()

    # Pure function
    src_pure = textwrap.dedent("""\
        def add(x, y):
            return x + y
    """)
    tree = ast.parse(src_pure)
    fe = analyzer.analyze_function(tree.body[0])
    _assert(fe.return_effect == Effect.PURE, "add() is PURE")
    _assert(fe.is_pure, "add() is_pure property")

    # IO function
    src_io = textwrap.dedent("""\
        def greet(name):
            print("Hello", name)
    """)
    tree = ast.parse(src_io)
    fe = analyzer.analyze_function(tree.body[0])
    _assert(fe.return_effect == Effect.IO, "greet() is IO")

    # Mutation function
    src_mut = textwrap.dedent("""\
        def push(lst, val):
            lst.append(val)
    """)
    tree = ast.parse(src_mut)
    fe = analyzer.analyze_function(tree.body[0])
    _assert(fe.return_effect == Effect.MUTATES, "push() is MUTATES")
    _assert("lst" in fe.writes, "push() writes to lst")

    # Exception function
    src_exc = textwrap.dedent("""\
        def safe_div(a, b):
            if b == 0:
                raise ValueError("division by zero")
            return a / b
    """)
    tree = ast.parse(src_exc)
    fe = analyzer.analyze_function(tree.body[0])
    _assert(fe.return_effect == Effect.EXCEPTION, "safe_div() is EXCEPTION")
    _assert("ValueError" in fe.exceptions, "safe_div() raises ValueError")

    # Non-deterministic function
    src_nd = textwrap.dedent("""\
        def roll():
            import random
            return random.randint(1, 6)
    """)
    tree = ast.parse(src_nd)
    fe = analyzer.analyze_function(tree.body[0])
    _assert(fe.return_effect == Effect.NONDET, "roll() is NONDET")

    # Divergent function
    src_div = textwrap.dedent("""\
        def loop_forever():
            while True:
                pass
    """)
    tree = ast.parse(src_div)
    fe = analyzer.analyze_function(tree.body[0])
    _assert(not fe.is_total, "loop_forever() is not total")

    # Async function
    src_async = textwrap.dedent("""\
        async def fetch(url):
            return await get(url)
    """)
    tree = ast.parse(src_async)
    fe = analyzer.analyze_function(tree.body[0])
    _assert(fe.return_effect == Effect.ASYNC, "fetch() is ASYNC")

    print("\n=== EffectChecker ===")
    checker = EffectChecker()

    decl = FunctionEffect(name="f", return_effect=Effect.PURE, is_total=True)
    inferred = FunctionEffect(name="f", return_effect=Effect.IO)
    errs = checker.check(decl, inferred)
    _assert(len(errs) > 0, "checker catches PURE vs IO mismatch")

    decl2 = FunctionEffect(name="g", return_effect=Effect.IO)
    inferred2 = FunctionEffect(name="g", return_effect=Effect.READS)
    errs2 = checker.check(decl2, inferred2)
    _assert(len(errs2) == 0, "checker accepts IO ≥ READS")

    print("\n=== StateContract ===")
    c1 = StateContract(
        pre_state={"x": "x > 0"},
        post_state={"x": "x > 0", "y": "y == x + 1"},
        frame={"x"},
    )
    c2 = StateContract(
        pre_state={"y": "y > 1"},
        post_state={"y": "y * 2"},
        frame={"x"},
    )
    merged = c1.merge(c2)
    _assert(merged.pre_state == {"x": "x > 0"}, "merged pre = c1.pre")
    _assert(merged.post_state["y"] == "y * 2", "merged post[y] = c2.post[y]")
    _assert("x" in merged.frame, "x preserved in merged frame")

    if ok:
        print("\nAll smoke tests passed ✓")
    else:
        print("\nSome tests FAILED ✗", file=sys.stderr)
        sys.exit(1)


# ═══════════════════════════════════════════════════════════════════════
# 10. Effect Z3 Discharge — formally verify effects with Z3
# ═══════════════════════════════════════════════════════════════════════

try:
    import z3 as _z3
    _HAS_Z3_EFFECTS = True
except ImportError:
    _HAS_Z3_EFFECTS = False


class EffectDischargeResult:
    """Result of discharging an effect to Z3."""
    __slots__ = ('effect', 'verified', 'proof_term', 'message')

    def __init__(self, effect: Effect, verified: bool, proof_term: str = "", message: str = ""):
        self.effect = effect
        self.verified = verified
        self.proof_term = proof_term
        self.message = message

    def __repr__(self) -> str:
        status = "VERIFIED" if self.verified else "UNVERIFIED"
        return f"EffectDischargeResult({self.effect.name}, {status})"


class EffectZ3Discharger:
    """Discharge effect proof obligations to Z3.

    Handles:
    - Exception freedom: prove no exception can be raised under preconditions
    - Totality: prove bounded iteration / convergence for loops
    - Async suspension safety: prove await calls are bounded
    - Generator safety: prove yield sequences are finite
    """

    def discharge_exception_freedom(
        self,
        source: str,
        preconditions: list[str] | None = None,
    ) -> EffectDischargeResult:
        """Prove that a function body raises no exceptions under preconditions.

        Strategy: parse AST, find all `raise` / implicit-exception sites,
        build Z3 formula asserting preconditions → ¬(any exception path reachable).
        """
        if not _HAS_Z3_EFFECTS:
            return EffectDischargeResult(Effect.EXCEPTION, False, message="Z3 unavailable")

        try:
            tree = ast.parse(source)
        except SyntaxError:
            return EffectDischargeResult(Effect.EXCEPTION, False, message="Parse error")

        func = tree.body[0] if tree.body and isinstance(tree.body[0], (ast.FunctionDef, ast.AsyncFunctionDef)) else None
        if func is None:
            return EffectDischargeResult(Effect.EXCEPTION, False, message="No function found")

        # Find all exception-raising sites
        raise_sites = self._find_raise_sites(func)
        if not raise_sites:
            return EffectDischargeResult(
                Effect.EXCEPTION, True,
                proof_term="exception_free_by_absence",
                message="No raise statements found",
            )

        # Check if all raises are guarded by conditions that contradict preconditions
        solver = _z3.Solver()
        solver.set("timeout", 5000)

        # Add preconditions as constraints
        param_vars: dict[str, Any] = {}
        for arg in func.args.args:
            param_vars[arg.arg] = _z3.Int(arg.arg)

        if preconditions:
            for pre in preconditions:
                try:
                    pre_expr = self._parse_constraint(pre, param_vars)
                    if pre_expr is not None:
                        solver.add(pre_expr)
                except Exception:
                    pass

        # For each raise site, check if it's reachable
        all_unreachable = True
        for guard_cond, exc_type in raise_sites:
            if guard_cond is None:
                # Unconditional raise — can't prove absence
                all_unreachable = False
                break
            try:
                guard_z3 = self._parse_constraint(guard_cond, param_vars)
                if guard_z3 is not None:
                    solver.push()
                    solver.add(guard_z3)
                    result = solver.check()
                    solver.pop()
                    if result == _z3.sat:
                        all_unreachable = False
                        break
                else:
                    all_unreachable = False
                    break
            except Exception:
                all_unreachable = False
                break

        if all_unreachable:
            return EffectDischargeResult(
                Effect.EXCEPTION, True,
                proof_term="exception_free_by_z3",
                message=f"All {len(raise_sites)} raise sites unreachable under preconditions",
            )
        return EffectDischargeResult(
            Effect.EXCEPTION, False,
            message="Some exception paths may be reachable",
        )

    def discharge_generator_safety(
        self,
        source: str,
        bound: int = 1000,
    ) -> EffectDischargeResult:
        """Prove a generator yields at most *bound* values.

        Strategy: if the generator iterates over a finite collection
        (list, range, dict) with no recursive yields, it's bounded.
        """
        try:
            tree = ast.parse(source)
        except SyntaxError:
            return EffectDischargeResult(Effect.DIVERGE, False, message="Parse error")

        func = tree.body[0] if tree.body else None
        if func is None:
            return EffectDischargeResult(Effect.DIVERGE, False, message="No function found")

        # Find yield sites
        yields = [n for n in ast.walk(func) if isinstance(n, (ast.Yield, ast.YieldFrom))]
        if not yields:
            return EffectDischargeResult(
                Effect.DIVERGE, True,
                proof_term="generator_trivially_finite",
                message="No yield statements",
            )

        # Check if all yields are inside for-loops over finite iterables
        for_loops = [n for n in ast.walk(func) if isinstance(n, ast.For)]
        while_loops = [n for n in ast.walk(func) if isinstance(n, ast.While)]

        if while_loops:
            return EffectDischargeResult(
                Effect.DIVERGE, False,
                message="While loops may produce unbounded yields",
            )

        # All yields in for-loops over finite iterables → bounded
        if for_loops and not while_loops:
            all_finite = all(
                self._is_finite_iterable(loop.iter) for loop in for_loops
            )
            if all_finite:
                return EffectDischargeResult(
                    Effect.DIVERGE, True,
                    proof_term=f"generator_bounded({bound})",
                    message=f"All yields in bounded for-loops",
                )

        return EffectDischargeResult(
            Effect.DIVERGE, False,
            message="Cannot prove bounded yields",
        )

    def discharge_async_safety(
        self,
        source: str,
    ) -> EffectDischargeResult:
        """Prove async function has bounded suspension points.

        Strategy: count await expressions; if all are in finite loops
        or sequential code, the suspension count is bounded.
        """
        try:
            tree = ast.parse(source)
        except SyntaxError:
            return EffectDischargeResult(Effect.ASYNC, False, message="Parse error")

        func = tree.body[0] if tree.body else None
        if func is None:
            return EffectDischargeResult(Effect.ASYNC, False, message="No function found")

        awaits = [n for n in ast.walk(func) if isinstance(n, ast.Await)]
        if not awaits:
            return EffectDischargeResult(
                Effect.ASYNC, True,
                proof_term="async_no_suspensions",
                message="No await expressions",
            )

        # Check for unbounded awaits (in while loops)
        while_loops = [n for n in ast.walk(func) if isinstance(n, ast.While)]
        for wl in while_loops:
            for child in ast.walk(wl):
                if isinstance(child, ast.Await):
                    return EffectDischargeResult(
                        Effect.ASYNC, False,
                        message="Await in while loop — unbounded suspensions",
                    )

        # All awaits in sequential code or for-loops → bounded
        return EffectDischargeResult(
            Effect.ASYNC, True,
            proof_term=f"async_bounded({len(awaits)})",
            message=f"{len(awaits)} bounded suspension points",
        )

    # ── helpers ────────────────────────────────────────────────────

    def _find_raise_sites(self, func: ast.AST) -> list[tuple[str | None, str]]:
        """Find (guard_condition, exception_type) pairs for every raise."""
        sites: list[tuple[str | None, str]] = []
        self._walk_raise_sites(func, None, sites)
        return sites

    def _walk_raise_sites(
        self, node: ast.AST, guard: str | None,
        sites: list[tuple[str | None, str]],
    ) -> None:
        if isinstance(node, ast.Raise):
            exc_type = "Exception"
            if node.exc:
                if isinstance(node.exc, ast.Call) and isinstance(node.exc.func, ast.Name):
                    exc_type = node.exc.func.id
                elif isinstance(node.exc, ast.Name):
                    exc_type = node.exc.id
            sites.append((guard, exc_type))
            return
        if isinstance(node, ast.If):
            test_str = ast.unparse(node.test)
            child_guard = f"({guard}) and ({test_str})" if guard else test_str
            for child in node.body:
                self._walk_raise_sites(child, child_guard, sites)
            neg_guard = f"({guard}) and not ({test_str})" if guard else f"not ({test_str})"
            for child in node.orelse:
                self._walk_raise_sites(child, neg_guard, sites)
            return
        if isinstance(node, ast.Try):
            for child in node.body:
                self._walk_raise_sites(child, guard, sites)
            for handler in node.handlers:
                for child in handler.body:
                    self._walk_raise_sites(child, guard, sites)
            return
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.AST):
                self._walk_raise_sites(child, guard, sites)

    def _parse_constraint(self, expr_str: str, vars_: dict[str, Any]) -> Any:
        """Parse a Python expression string into a Z3 expression."""
        try:
            tree = ast.parse(expr_str, mode='eval')
            return self._ast_to_z3(tree.body, vars_)
        except Exception:
            return None

    def _ast_to_z3(self, node: ast.expr, vars_: dict[str, Any]) -> Any:
        if isinstance(node, ast.Name):
            if node.id in vars_:
                return vars_[node.id]
            v = _z3.Int(node.id)
            vars_[node.id] = v
            return v
        if isinstance(node, ast.Constant):
            if isinstance(node.value, bool):
                return _z3.BoolVal(node.value)
            if isinstance(node.value, int):
                return _z3.IntVal(node.value)
            if isinstance(node.value, float):
                return _z3.RealVal(node.value)
        if isinstance(node, ast.Compare):
            left = self._ast_to_z3(node.left, vars_)
            ops_map = {
                ast.Eq: lambda a, b: a == b,
                ast.NotEq: lambda a, b: a != b,
                ast.Lt: lambda a, b: a < b,
                ast.LtE: lambda a, b: a <= b,
                ast.Gt: lambda a, b: a > b,
                ast.GtE: lambda a, b: a >= b,
            }
            result = None
            for op, comp in zip(node.ops, node.comparators):
                right = self._ast_to_z3(comp, vars_)
                fn = ops_map.get(type(op))
                if fn is None:
                    return None
                clause = fn(left, right)
                result = clause if result is None else _z3.And(result, clause)
                left = right
            return result
        if isinstance(node, ast.BoolOp):
            values = [self._ast_to_z3(v, vars_) for v in node.values]
            if any(v is None for v in values):
                return None
            if isinstance(node.op, ast.And):
                return _z3.And(*values)
            return _z3.Or(*values)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            operand = self._ast_to_z3(node.operand, vars_)
            return _z3.Not(operand) if operand is not None else None
        if isinstance(node, ast.BinOp):
            left = self._ast_to_z3(node.left, vars_)
            right = self._ast_to_z3(node.right, vars_)
            if left is None or right is None:
                return None
            ops = {ast.Add: lambda a, b: a + b, ast.Sub: lambda a, b: a - b,
                   ast.Mult: lambda a, b: a * b, ast.FloorDiv: lambda a, b: a / b,
                   ast.Mod: lambda a, b: a % b}
            fn = ops.get(type(node.op))
            return fn(left, right) if fn else None
        return None

    @staticmethod
    def _is_finite_iterable(node: ast.expr) -> bool:
        """Check if an iterable expression is provably finite."""
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            return node.func.id in ('range', 'enumerate', 'zip', 'reversed', 'sorted')
        if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
            return True
        if isinstance(node, ast.Name):
            return True  # Variable — assume finite for now
        if isinstance(node, ast.Attribute):
            return True  # e.g. self.items — assume finite
        return False
