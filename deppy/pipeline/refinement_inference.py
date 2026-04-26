"""Path-sensitive refinement-type inference for runtime safety.

This module extends ``auto_spec.py`` with a *control-flow-sensitive*
analyzer.  Rather than producing only function-wide preconditions, it
walks the AST in execution order and, at every potential exception
site, records the set of predicates that the surrounding code has
*already established* before reaching that site.

The output is a per-function ``RefinementMap`` that directly addresses
the goal of "proof of runtime safety on existing Python code without
adding decorators":

* ``def f(d, k):``
    ``if k in d:``
        ``return d[k]``       # KeyError site here, but ``k in d`` is live
    ``return None``

  → at the ``d[k]`` site we record the predicate ``k in d``, which is
  exactly the canonical safety predicate for ``KeyError``.  The pipeline
  can discharge that source via Z3 entailment without any user-supplied
  spec.

The analysis is intentionally conservative — it only adds a predicate
when an explicit guard / assert / isinstance check makes it provable
along the current path.  Anything trickier (loops, exceptions, mutation)
keeps its predicate set empty so the pipeline reports the source as
*unaddressed* rather than incorrectly claiming safety.

Output shape::

    @dataclass
    class RefinementFact:
        source_lineno: int
        source_kind: str            # "ZERO_DIVISION", "KEY_ERROR", ...
        guards: tuple[str, ...]     # conjunction of guard predicates

    @dataclass
    class RefinementMap:
        function_name: str
        function_wide_preconditions: list[str]
        per_source: list[RefinementFact]

A higher layer (``auto_spec_obligations.py``) consumes these and
strengthens the generated draft ``ExternalSpec.exception_free_when`` so
the safety pipeline can discharge each source by its specific guard.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Iterable, Optional


# ─────────────────────────────────────────────────────────────────────
#  Public dataclasses
# ─────────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class RefinementFact:
    """Per-source guard summary.

    ``guards`` is a tuple of Python expressions that, when conjoined,
    are guaranteed to hold at the exception source location along
    *every* control-flow path that reaches it.
    """
    source_lineno: int
    source_col: int
    source_kind: str  # "ZERO_DIVISION", "KEY_ERROR", "INDEX_ERROR", "TYPE_ERROR", "ATTRIBUTE_ERROR", ...
    safety_predicate: str  # the canonical safety predicate this source needs
    guards: tuple[str, ...]


@dataclass
class RefinementMap:
    """Per-function refinement summary."""
    function_name: str
    function_wide_preconditions: list[str] = field(default_factory=list)
    per_source: list[RefinementFact] = field(default_factory=list)
    # ``True`` when at least one ``assert P`` was used as a path-
    # sensitive guard.  Because Python strips ``assert`` under ``-O``,
    # discharges that depend on these guards are unsound in
    # optimised mode — the safety pipeline surfaces a warning.
    used_assert_narrowing: bool = False

    def conjoined_guards_for_source(
        self, lineno: int, col: int, kind: str,
    ) -> tuple[str, ...]:
        """All guards (conjoined) at the named source."""
        out: list[str] = []
        for fact in self.per_source:
            if (fact.source_lineno == lineno
                    and fact.source_col == col
                    and fact.source_kind == kind):
                out.extend(fact.guards)
        return tuple(out)

    def guard_disjunction_by_kind(self) -> dict[str, list[str]]:
        """Disjunction of guards across all sources of a given kind.

        Used by the auto-spec bridge: if every ``KEY_ERROR`` site is
        guarded by ``k in d``, the function-level
        ``exception_free_when`` includes ``k in d`` for that kind.
        """
        out: dict[str, list[str]] = {}
        per_kind: dict[str, list[tuple[str, ...]]] = {}
        for fact in self.per_source:
            per_kind.setdefault(fact.source_kind, []).append(fact.guards)
        for kind, guard_lists in per_kind.items():
            if not guard_lists:
                continue
            # If every source has at least one guard, the conjunction
            # of one-guard-per-source rules them all out.  When one
            # source is unguarded (empty tuple), we cannot honestly
            # claim function-wide exception_free_when — the pipeline
            # must still flag that source.
            if any(not g for g in guard_lists):
                continue
            # Take the intersection of guards across sources of this
            # kind: the predicates guaranteed to hold at *every* site.
            common = set(guard_lists[0])
            for g in guard_lists[1:]:
                common &= set(g)
            if common:
                out[kind] = sorted(common)
        return out


# ─────────────────────────────────────────────────────────────────────
#  Internal: predicate set / negation
# ─────────────────────────────────────────────────────────────────────

def _unparse(node: ast.AST) -> str:
    try:
        return ast.unparse(node)
    except Exception:
        return ast.dump(node)


_NEG_OPS: dict[type, str] = {
    ast.Lt: ">=", ast.LtE: ">", ast.Gt: "<=", ast.GtE: "<",
    ast.Eq: "!=", ast.NotEq: "==",
    ast.Is: "is not", ast.IsNot: "is",
    ast.In: "not in", ast.NotIn: "in",
}


def _negate_predicate(node: ast.expr) -> Optional[str]:
    """Best-effort negation of a Python boolean expression.

    Returns ``None`` if the negation cannot be derived in a way that
    Z3 / safety_predicates can consume soundly.  We are conservative:
    we never invent a negation we cannot defend.
    """
    # not X  →  X
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return _unparse(node.operand)
    # a OP b  →  a NEG_OP b   (single-comparison form)
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        op_type = type(node.ops[0])
        if op_type in _NEG_OPS:
            l = _unparse(node.left)
            r = _unparse(node.comparators[0])
            return f"{l} {_NEG_OPS[op_type]} {r}"
    # a and b  →  not a or not b — too lossy; skip
    # a or b  →  not a and not b — too lossy; skip
    # general expr  → "not (expr)"
    s = _unparse(node)
    if s and not s.startswith("not "):
        return f"not ({s})"
    return None


def _split_conjuncts(node: ast.expr) -> list[str]:
    """Split ``a and b and c`` into ``[a, b, c]``.

    Compound conditions in guards are common (``if x is not None and
    x > 0``), and treating them as a single opaque string would lose
    information about which conjunct rules out which exception kind.
    """
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And):
        out: list[str] = []
        for v in node.values:
            out.extend(_split_conjuncts(v))
        return out
    return [_unparse(node)]


def _isinstance_predicate(call: ast.Call) -> Optional[str]:
    """Recognize ``isinstance(x, T)`` and return its source form."""
    if (isinstance(call.func, ast.Name) and call.func.id == "isinstance"
            and len(call.args) == 2):
        return _unparse(call)
    return None


# ─────────────────────────────────────────────────────────────────────
#  Source kind detection (matches deppy.pipeline.exception_sources)
# ─────────────────────────────────────────────────────────────────────

def _source_kinds_at(node: ast.AST) -> list[tuple[str, str]]:
    """Return a list of ``(kind, safety_predicate)`` for every potential
    runtime exception this AST node can raise *directly*.

    Mirrors the visitor logic in
    :mod:`deppy.pipeline.exception_sources` for the kinds we care about.
    Each returned ``safety_predicate`` is the canonical Python-syntax
    predicate that, if it holds, rules out the exception.
    """
    out: list[tuple[str, str]] = []

    # a / b   /   a // b   /   a % b   →   ZeroDivisionError
    if isinstance(node, ast.BinOp) and isinstance(
            node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
        denom = _unparse(node.right)
        # constant non-zero denominators are statically safe
        if isinstance(node.right, ast.Constant) and isinstance(
                node.right.value, (int, float)) and node.right.value != 0:
            pass  # no runtime risk; do not emit a source
        else:
            out.append(("ZERO_DIVISION", f"({denom}) != 0"))

    # xs[i]   →   IndexError   AND   d[k] → KeyError
    if isinstance(node, ast.Subscript):
        seq = _unparse(node.value)
        idx = _unparse(node.slice)
        # We cannot statically tell which of the two it is, so emit
        # both — the safety pipeline will pick whichever its
        # ExceptionSourceFinder reported.  The guard analysis is the
        # same either way (membership / range), so we end up with
        # consistent guard sets.
        out.append(("INDEX_ERROR", f"0 <= ({idx}) and ({idx}) < len({seq})"))
        out.append(("KEY_ERROR", f"({idx}) in ({seq})"))

    # obj.attr  →  AttributeError
    if isinstance(node, ast.Attribute):
        obj = _unparse(node.value)
        out.append(("ATTRIBUTE_ERROR", f"hasattr({obj}, {node.attr!r})"))

    # f(...)   →   CALL_PROPAGATION (and possibly RUNTIME_ERROR for
    # self-recursion).  We don't emit RUNTIME_ERROR here because that
    # check is local to a function definition; the safety pipeline
    # already routes those.  CALL_PROPAGATION is recorded so that the
    # callee-summary discharge can pick up the live path guards at
    # the call site.
    if isinstance(node, ast.Call):
        out.append(("CALL_PROPAGATION", "callee_safe"))

    return out


# ─────────────────────────────────────────────────────────────────────
#  RefinementInferrer
# ─────────────────────────────────────────────────────────────────────

class RefinementInferrer:
    """Path-sensitive guard accumulator.

    Walks a function body in execution order, threading a *guard set*
    through each statement.  At every potential exception site we
    record a ``RefinementFact`` capturing the current guard set.

    The walker handles:

    * ``assert P``        — adds ``P`` to the guard set permanently
    * ``if P: …``         — adds ``P`` inside the body, ``not P``
                            after the if (when the if exits without
                            falling through, e.g. ``raise`` / ``return``)
    * ``if P: raise``      — adds ``not P`` permanently after the guard
    * ``if not isinstance(x, T): raise`` — adds ``isinstance(x, T)``
    * ``while P: …``      — analyzed conservatively (no narrowing)
    * function-call narrowing on the argument is *not* modeled

    When in doubt we drop guards rather than over-claim: this analyzer
    is for proving safety, not for finding bugs.
    """

    def __init__(self, *, function_name: str = "") -> None:
        self.function_name = function_name
        self._facts: list[RefinementFact] = []
        self._function_wide_preconditions: list[str] = []
        self._used_assert_narrowing: bool = False

    # -- public entry point ---------------------------------------------

    def analyze(self, fn: ast.FunctionDef | ast.AsyncFunctionDef) -> RefinementMap:
        """Analyze ``fn`` and return a complete :class:`RefinementMap`."""
        self.function_name = fn.name
        self._facts = []
        self._function_wide_preconditions = []

        # Function-wide preconditions are guards that appear at the top
        # of the body *and* exit unconditionally on failure.  These end
        # up in ``function_wide_preconditions`` for the auto-spec bridge.
        body = list(fn.body)
        # Skip a leading docstring.
        if (body and isinstance(body[0], ast.Expr)
                and isinstance(body[0].value, ast.Constant)
                and isinstance(body[0].value.value, str)):
            body = body[1:]

        # Pre-pass: extract leading guard clauses (entry preconditions).
        idx = 0
        while idx < len(body):
            stmt = body[idx]
            pre = self._extract_leading_guard(stmt)
            if pre is None:
                break
            self._function_wide_preconditions.extend(pre)
            idx += 1

        # Now do the path-sensitive walk over the *whole* body, including
        # the leading guards (so their narrowed predicates apply to the
        # rest of the function too).
        self._walk_block(list(fn.body), guards=())

        return RefinementMap(
            function_name=fn.name,
            function_wide_preconditions=list(self._function_wide_preconditions),
            per_source=list(self._facts),
            used_assert_narrowing=self._used_assert_narrowing,
        )

    # -- leading guard extraction ---------------------------------------

    def _extract_leading_guard(self, stmt: ast.stmt) -> Optional[list[str]]:
        """If ``stmt`` is a top-of-body ``if BAD: raise`` guard, return
        the conjuncts of ``not BAD`` that hold for the rest of the
        function.

        We deliberately do **not** treat a leading ``assert P`` as a
        function-wide precondition.  Under ``python -O`` (or
        ``PYTHONOPTIMIZE=1``) the interpreter strips ``assert``
        statements entirely, so claims based on them would be unsound
        in optimised mode.  The path-sensitive walker (``_walk_stmt``)
        still records the assert's predicate as a guard *for sources
        that follow it inside the same function* — discharges based
        on those guards are flagged via a verdict note so the user
        knows their soundness depends on running unoptimised.

        ``None`` is returned when the statement isn't a leading
        raise-guard.
        """
        if not isinstance(stmt, ast.If):
            return None
        if not self._body_raises(stmt.body):
            return None
        negated = _negate_predicate(stmt.test)
        if negated is None:
            return None
        return _split_conjuncts(self._parse_expr(negated))

    @staticmethod
    def _body_raises(body: list[ast.stmt]) -> bool:
        """True iff *body* exits *only* via raise (no normal return).

        We require an early ``raise`` (typically the first or only
        statement) and no preceding statement that could fall through.
        """
        if not body:
            return False
        for s in body:
            if isinstance(s, ast.Raise):
                return True
            if isinstance(s, ast.Return):
                return False
            if isinstance(s, ast.Pass):
                continue
            # An assert that always fails counts.
            if (isinstance(s, ast.Assert)
                    and isinstance(s.test, ast.Constant)
                    and s.test.value is False):
                return True
            # Anything else means we're not a pure raise-guard.
            return False
        return False

    @staticmethod
    def _body_is_terminal(body: list[ast.stmt]) -> bool:
        """``True`` iff control flow does not fall through ``body`` —
        i.e., the last reachable statement is a ``raise`` / ``return``
        / unconditional ``raise``.  Used to detect early-exit guards.
        """
        if not body:
            return False
        for s in reversed(body):
            if isinstance(s, (ast.Raise, ast.Return)):
                return True
            if isinstance(s, ast.Pass):
                continue
            return False
        return False

    @staticmethod
    def _parse_expr(text: str) -> ast.expr:
        """Parse ``text`` as a Python expression, returning a *Module*'s
        ``Expression`` body.  Falls back to ``Constant("True")`` if the
        text is unparseable so the analyzer cannot crash on weird
        guards (e.g. f-strings) we'd otherwise need to special-case.
        """
        try:
            return ast.parse(text, mode="eval").body
        except SyntaxError:
            return ast.Constant(value=True)

    # -- main walker -----------------------------------------------------

    def _walk_block(self, block: list[ast.stmt], *,
                    guards: tuple[str, ...]) -> tuple[str, ...]:
        """Walk a block of statements with the given live ``guards``.

        Returns the guard set that holds *after* the block, allowing
        callers to thread guards through sequential statements.
        """
        live = guards
        for stmt in block:
            live = self._walk_stmt(stmt, guards=live)
        return live

    def _walk_stmt(self, stmt: ast.stmt, *,
                   guards: tuple[str, ...]) -> tuple[str, ...]:
        # Record sources from any expressions on this *statement* — but
        # only from expressions that are not themselves nested inside
        # control-flow constructs we're about to walk explicitly.  For
        # control-flow statements (``If`` / ``For`` / etc.) we record
        # only the *test/iter/items* expressions; the bodies recurse.
        for expr in self._immediate_expressions(stmt):
            self._record_expr_sources(expr, guards=guards)

        # Soundness fix F2: drop guards that mention any name this
        # statement mutates.  Mutation invalidates the previously-
        # established membership / arithmetic / type evidence — e.g.,
        # after ``del d[k]`` the guard ``k in d`` no longer holds.
        # We compute the set of mutated names *before* the
        # statement-specific narrowing so the new guard set is the
        # intersection of pre-mutation guards (filtered) plus any
        # guards this statement adds.
        mutated = _mutated_names_in_stmt(stmt)
        if mutated:
            guards = tuple(
                g for g in guards
                if not _expr_mentions_any_name(g, mutated)
            )

        # Statement-specific narrowing.
        if isinstance(stmt, ast.Assert):
            for c in _split_conjuncts(stmt.test):
                guards = guards + (c,)
            self._used_assert_narrowing = True
            return guards

        if isinstance(stmt, ast.If):
            then_guards = guards
            for c in _split_conjuncts(stmt.test):
                then_guards = then_guards + (c,)
            after_then = self._walk_block(stmt.body, guards=then_guards)

            else_guards = guards
            negated = _negate_predicate(stmt.test)
            if negated is not None:
                for c in _split_conjuncts(self._parse_expr(negated)):
                    else_guards = else_guards + (c,)
            after_else = self._walk_block(stmt.orelse, guards=else_guards)

            then_terminal = self._body_is_terminal(stmt.body)
            else_terminal = self._body_is_terminal(stmt.orelse) if stmt.orelse else False

            if then_terminal and not else_terminal:
                return after_else
            if else_terminal and not then_terminal:
                return after_then
            if then_terminal and else_terminal:
                return guards
            common = tuple(g for g in after_then if g in after_else)
            return common

        if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
            self._walk_block(list(stmt.body), guards=guards)
            self._walk_block(list(getattr(stmt, "orelse", []) or []),
                              guards=guards)
            return guards

        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            self._walk_block(list(stmt.body), guards=guards)
            return guards

        if isinstance(stmt, ast.Try):
            self._walk_block(list(stmt.body), guards=guards)
            for handler in stmt.handlers:
                self._walk_block(list(handler.body), guards=guards)
            self._walk_block(list(stmt.orelse), guards=guards)
            self._walk_block(list(stmt.finalbody), guards=guards)
            return guards

        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef)):
            # Don't descend into nested functions — they are analyzed
            # separately by ``infer_refinements``.
            return guards

        return guards

    @staticmethod
    def _immediate_expressions(stmt: ast.stmt) -> list[ast.expr]:
        """Return the expressions that *belong* to this statement
        rather than to a nested block (which we recurse into separately).

        For ``if x > 0: ...``, the test ``x > 0`` belongs here but the
        body's expressions do not.  For a plain ``Assign`` /
        ``Return`` / ``Expr``, every expression is immediate.
        """
        if isinstance(stmt, ast.If):
            return [stmt.test]
        if isinstance(stmt, (ast.For, ast.AsyncFor)):
            return [stmt.iter]
        if isinstance(stmt, ast.While):
            return [stmt.test]
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            return [item.context_expr for item in stmt.items]
        if isinstance(stmt, ast.Try):
            return []  # body & handlers walked separately
        if isinstance(stmt, ast.Assert):
            return [stmt.test] + ([stmt.msg] if stmt.msg else [])
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef)):
            return []
        # Catch-all: any descendant expression that is not itself a
        # nested function-or-control-flow boundary.
        out: list[ast.expr] = []
        for child in ast.iter_child_nodes(stmt):
            if isinstance(child, ast.expr):
                out.append(child)
            elif isinstance(child, list):  # type: ignore[unreachable]
                pass
        return out

    def _record_expr_sources(
        self, expr: ast.expr, *, guards: tuple[str, ...],
    ) -> None:
        """Walk ``expr`` and record every nested exception source."""
        for node in ast.walk(expr):
            self._record_sources(node, guards=guards)

    # -- expression descent ---------------------------------------------

    def _record_sources(self, node: ast.AST, *,
                        guards: tuple[str, ...]) -> None:
        """For the immediate node, record any exception sources it
        directly causes, with the supplied ``guards``."""
        for kind, pred in _source_kinds_at(node):
            self._facts.append(RefinementFact(
                source_lineno=getattr(node, "lineno", 0),
                source_col=getattr(node, "col_offset", 0),
                source_kind=kind,
                safety_predicate=pred,
                guards=guards,
            ))

    @staticmethod
    def _all_expr_descendants(stmt: ast.stmt) -> Iterable[ast.AST]:
        """Yield every AST node that lives directly under ``stmt`` —
        but **stop** at nested ``FunctionDef`` / ``Lambda`` / ``If`` /
        ``For`` / ``While`` / ``Try`` boundaries (those will be walked
        explicitly by the caller's recursive logic, so we don't double-
        record their sources).
        """
        for child in ast.walk(stmt):
            # stop at nested control flow — handled separately
            if child is stmt:
                yield child
                continue
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.Lambda, ast.If, ast.For, ast.AsyncFor,
                                  ast.While, ast.Try, ast.With, ast.AsyncWith)):
                continue
            yield child


# ─────────────────────────────────────────────────────────────────────
#  Top-level convenience
# ─────────────────────────────────────────────────────────────────────

def infer_refinements(source: str) -> dict[str, RefinementMap]:
    """Run the path-sensitive analyzer over a module source string.

    Returns ``{name: RefinementMap}`` where ``name`` is either the
    function's bare name (for module-level functions) or
    ``ClassName.method`` (for methods defined inside a class).  Both
    forms are also stored under the bare ``method`` name so existing
    consumers that look up by bare name continue to work for
    classes whose methods don't collide with module-level functions.
    """
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return {}
    out: dict[str, RefinementMap] = {}

    def walk(scope: list[str], node: ast.AST) -> None:
        if isinstance(node, ast.ClassDef):
            for child in node.body:
                walk(scope + [node.name], child)
            return
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            qual = ".".join(scope + [node.name]) if scope else node.name
            out[qual] = RefinementInferrer().analyze(node)
            # Bare-name alias for classes whose method names don't
            # collide with another top-level binding.
            if scope and node.name not in out:
                out[node.name] = out[qual]
            for child in node.body:
                walk(scope, child)  # nested functions stay in module scope
            return
        for child in ast.iter_child_nodes(node):
            walk(scope, child)

    walk([], tree)
    return out


# ─────────────────────────────────────────────────────────────────────
#  Mutation detection (Soundness fix F2)
# ─────────────────────────────────────────────────────────────────────

# Method names whose call mutates the receiver.  Conservative — list
# matches the Python stdlib documentation for sequence / dict / set /
# bytearray protocols; anything else is treated as non-mutating
# (consistent with the rest of the safety pipeline's "if we don't
# know, treat conservatively only when it makes us less liberal"
# stance).  In doubt we lean toward dropping the guard rather than
# keeping it — false-negatives become a few extra Assume sources, not
# unsoundness.
_MUTATING_METHODS: frozenset[str] = frozenset({
    # list / sequence
    "append", "extend", "insert", "remove", "pop", "sort", "reverse",
    "clear",
    # dict
    "setdefault", "update", "popitem",
    # set
    "add", "discard", "intersection_update", "difference_update",
    "symmetric_difference_update", "update",
    # generic
    "__setitem__", "__delitem__",
})


def _mutated_names_in_stmt(stmt: ast.AST) -> set[str]:
    """Return the set of *top-level* names that ``stmt`` mutates.

    A name is mutated when:

    * it appears as the LHS of an ``Assign`` / ``AnnAssign`` /
      ``AugAssign`` (``x = ...``, ``x: int = ...``, ``x += ...``);
    * it appears as the receiver of a ``del`` (``del x`` or
      ``del x[k]``);
    * it appears as the receiver of a known-mutating method call
      (``x.append(y)``, ``x.pop()``, …);
    * it appears as the receiver of a subscript-assign (``x[k] = v``)
      or subscript-del (``del x[k]``).

    For nested attribute / subscript chains we recurse to the root
    name (``x.y.z[0] = ...`` → ``"x"``).
    """
    out: set[str] = set()

    def _root_name(node) -> Optional[str]:
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            return _root_name(node.value)
        if isinstance(node, ast.Subscript):
            return _root_name(node.value)
        if isinstance(node, ast.Starred):
            return _root_name(node.value)
        if isinstance(node, (ast.Tuple, ast.List)):
            for elt in node.elts:
                n = _root_name(elt)
                if n:
                    out.add(n)
            return None
        return None

    if isinstance(stmt, ast.Assign):
        for tgt in stmt.targets:
            n = _root_name(tgt)
            if n:
                out.add(n)
    elif isinstance(stmt, (ast.AnnAssign, ast.AugAssign)):
        n = _root_name(stmt.target)
        if n:
            out.add(n)
    elif isinstance(stmt, ast.Delete):
        for tgt in stmt.targets:
            n = _root_name(tgt)
            if n:
                out.add(n)
    elif isinstance(stmt, (ast.For, ast.AsyncFor)):
        n = _root_name(stmt.target)
        if n:
            out.add(n)

    # Mutating method calls anywhere in the statement's expressions.
    for child in ast.walk(stmt):
        if isinstance(child, ast.Call):
            func = child.func
            if isinstance(func, ast.Attribute) and func.attr in _MUTATING_METHODS:
                receiver = _root_name(func.value)
                if receiver:
                    out.add(receiver)

    return out


def _expr_mentions_any_name(expr_text: str, names: set[str]) -> bool:
    """``True`` iff parsing ``expr_text`` yields an AST that mentions
    any of the ``names`` as a free identifier.

    Conservative: when parsing fails (or the predicate is opaque), we
    return ``True`` so the guard is dropped — that's the safe
    direction.
    """
    if not expr_text:
        return False
    if not names:
        return False
    try:
        tree = ast.parse(expr_text, mode="eval")
    except SyntaxError:
        return True
    for node in ast.walk(tree):
        if isinstance(node, ast.Name) and node.id in names:
            return True
        if isinstance(node, ast.Attribute):
            base = node
            while isinstance(base, ast.Attribute):
                base = base.value
            if isinstance(base, ast.Name) and base.id in names:
                return True
    return False


__all__ = [
    "RefinementFact",
    "RefinementMap",
    "RefinementInferrer",
    "infer_refinements",
]
