"""
Deppy Formal Semantics for Python Control Flow
==================================================

Formal typing rules, operation terms, and axioms for Python's control-flow
features, grounded in the type-theoretic framework of the Deppy monograph.

Covered features:
    • Generators / iterators   (Ch 11 — free monad over yield, coinduction)
    • Exception handling       (Ch 10 — K(π,1) classifying space, chaining)
    • Context managers         (Ch 17 — bracket from Π-type, async with)
    • Async / await            (Ch 18 — Suspend effect, coroutine protocol)
    • For / while loops        (Appendix A — fold desugaring, termination)
    • Comprehensions           (Ch 20 — list monad bind, dict/set/genexpr)
    • Closures / scope         (Ch 12 — scope fiber bundle, nonlocal)

Each semantic class produces :class:`FormalAxiomEntry` instances whose
``conclusion`` field is a machine-checkable :class:`Judgment`.

References
----------
- Monograph Ch 10: Exceptions — K(π,1) classifying space
- Monograph Ch 11: Generators — Free monad over yield
- Monograph Ch 12: Closures — scope fiber bundle
- Monograph Ch 17: Context Managers — bracket from Π-type
- Monograph Ch 18: Async/Await — Suspend effect
- Monograph Ch 20: Comprehensions — list monad bind
- Appendix A: Statement typing rules
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyClassType, PyCallableType,
    PyListType, PyDictType, PySetType, PyBoolType,
    PyNoneType, PyIntType, PyStrType,
    PiType, SigmaType, RefinementType, UnionType,
    Var, Literal,
    Spec,
    Lam,
)
from deppy.core.formal_ops import (
    Op, OpCall, FormalAxiomEntry, formal_eq, formal_check,
    op_iter, op_next, op_send, op_throw, op_close,
    op_yield, op_yield_from,
    op_enter, op_exit, op_aenter, op_aexit,
    op_await, op_aiter, op_anext,
    op_raise, op_raise_from,
    op_fold, op_map, op_filter,
    op_listcomp, op_dictcomp, op_setcomp, op_genexpr,
    op_len, op_eq,
    formal_subtype,
)

# Module identifier used in all axiom entries produced here.
_MODULE = "python.control"


# ═══════════════════════════════════════════════════════════════════
# Helper — empty context
# ═══════════════════════════════════════════════════════════════════

def _ctx() -> Context:
    """Return a fresh empty context."""
    return Context()


# ═══════════════════════════════════════════════════════════════════
# 1. Generator Semantics — Ch 11: Free monad over yield
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class GeneratorType(SynType):
    """Generator[Y, S, T] — parameterized by yield, send, return types.

    A generator Gen(S, Y, T) is the free monad over the Yield effect:
        Free(Yield_Y ⊗ Read_S)(T)

    This captures the full coroutine protocol where:
    - Y is the type yielded out    (via ``yield expr``)
    - S is the type sent in        (via ``gen.send(value)``)
    - T is the final return type   (via ``return expr``, surfaced as
      ``StopIteration.value``)
    """
    yield_type: SynType = field(default_factory=PyObjType)
    send_type: SynType = field(default_factory=PyNoneType)
    return_type: SynType = field(default_factory=PyNoneType)

    def _repr(self) -> str:
        return (f"Generator[{self.yield_type._repr()}, "
                f"{self.send_type._repr()}, {self.return_type._repr()}]")


class GeneratorSemantics:
    """Generators as free monads over the yield effect.

    A generator ``Gen(S, Y, T)`` has:
    - S: send type (input via ``gen.send(v)``)
    - Y: yield type (output via ``yield``)
    - T: return type (final value via ``StopIteration.value``)

    The coinductive structure of generators allows lazy, potentially
    infinite sequences whose termination is witnessed by ``StopIteration``.
    """

    # ── type projections ──────────────────────────────────────────

    def yield_type(self, gen_type: SynType) -> SynType:
        """Extract the yield type from a generator type."""
        if isinstance(gen_type, GeneratorType):
            return gen_type.yield_type
        return PyObjType()

    def send_type(self, gen_type: SynType) -> SynType:
        """Extract the send type."""
        if isinstance(gen_type, GeneratorType):
            return gen_type.send_type
        return PyNoneType()

    def return_type(self, gen_type: SynType) -> SynType:
        """Extract the return type."""
        if isinstance(gen_type, GeneratorType):
            return gen_type.return_type
        return PyNoneType()

    # ── protocol axioms ───────────────────────────────────────────

    def generator_protocol_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for the generator protocol.

        These encode the operational semantics of Python generators as
        algebraic laws on the free-monad operations.

        Axioms:
        - next(g) ≡ g.send(None)
        - StopIteration.value is the generator's return value
        - yield from sub delegates to sub's protocol
        - list(gen) collects all yielded values
        - Generator iteration order is deterministic
        - send(v) resumes at the yield point with value v
        """
        g = Var("g")
        v = Var("v")
        sub = Var("sub")
        none = Literal(None, PyNoneType())
        ctx = _ctx()

        return [
            FormalAxiomEntry(
                name="next_is_send_none",
                module=_MODULE,
                params=[("g", PyObjType())],
                conclusion=formal_eq(ctx, op_next(g), op_send(g, none)),
                description="next(g) is equivalent to g.send(None)",
            ),
            FormalAxiomEntry(
                name="stopiteration_value",
                module=_MODULE,
                params=[("g", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("StopIteration.value"), (g,)),
                    PyObjType(),
                ),
                description=(
                    "StopIteration.value carries the generator's return value"
                ),
            ),
            FormalAxiomEntry(
                name="yield_from_delegation",
                module=_MODULE,
                params=[("g", PyObjType()), ("sub", PyObjType())],
                conclusion=formal_eq(
                    ctx,
                    op_yield_from(sub),
                    OpCall(Op("delegate"), (g, sub)),
                ),
                description=(
                    "yield from sub_gen delegates the full send/throw "
                    "protocol to sub_gen"
                ),
            ),
            FormalAxiomEntry(
                name="list_collects_yields",
                module=_MODULE,
                params=[("g", PyObjType())],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("list"), (g,)),
                    OpCall(Op("collect_yields"), (g,)),
                ),
                description="list(gen) collects all yielded values in order",
            ),
            FormalAxiomEntry(
                name="generator_deterministic_order",
                module=_MODULE,
                params=[("g", PyObjType())],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("list"), (g,)),
                    OpCall(Op("list"), (g,)),
                ),
                description="Generator iteration order is deterministic",
            ),
            FormalAxiomEntry(
                name="send_resumes_at_yield",
                module=_MODULE,
                params=[("g", PyObjType()), ("v", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    op_send(g, v),
                    PyObjType(),
                ),
                description=(
                    "send(v) resumes execution at the suspended yield "
                    "point, making v the value of the yield expression"
                ),
            ),
        ]

    def generator_composition_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms about composing generators.

        These correspond to the monoidal structure of the free monad —
        sequential composition (chain) is associative, and map/zip lift
        pointwise functions over the coinductive stream.

        Axioms:
        - chain(g1, g2) yields g1's values then g2's values
        - zip(g1, g2) yields pairs, stops at shorter
        - map(f, g) yields f(x) for each x from g
        """
        g1, g2 = Var("g1"), Var("g2")
        f = Var("f")
        ctx = _ctx()

        return [
            FormalAxiomEntry(
                name="chain_sequential",
                module=_MODULE,
                params=[("g1", PyObjType()), ("g2", PyObjType())],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("chain"), (g1, g2)),
                    OpCall(Op("concat_yields"), (g1, g2)),
                ),
                description=(
                    "chain(g1, g2) yields all of g1's values then all "
                    "of g2's values"
                ),
            ),
            FormalAxiomEntry(
                name="zip_shortest",
                module=_MODULE,
                params=[("g1", PyObjType()), ("g2", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("zip"), (g1, g2)),
                    PyObjType(),
                ),
                description=(
                    "zip(g1, g2) yields pairs and stops at the shorter "
                    "generator"
                ),
            ),
            FormalAxiomEntry(
                name="map_pointwise",
                module=_MODULE,
                params=[("f", PyObjType()), ("g1", PyObjType())],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("list"), (op_map(f, g1),)),
                    op_map(f, OpCall(Op("list"), (g1,))),
                ),
                description="map(f, g) yields f(x) for each x from g",
            ),
        ]


# ═══════════════════════════════════════════════════════════════════
# 2. Exception Semantics — Ch 10: K(π,1) classifying space
# ═══════════════════════════════════════════════════════════════════

class ExceptionSemantics:
    """Exception handling as K(π,1) classifying space.

    The exception hierarchy forms a tree rooted at ``BaseException``.
    Each exception type E defines a classifying space BE whose sections
    correspond to except-handlers.  A try/except block is a section of
    the exception bundle: it catches exactly those exceptions whose type
    lies on the fiber over the declared handler type.
    """

    def exception_hierarchy_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms encoding the Python exception lattice.

        Axioms:
        - BaseException is the root of the exception hierarchy
        - Exception <: BaseException
        - except E catches E and all subclasses of E
        - except (E1, E2) catches E1 or E2
        - bare except catches all Exception (not BaseException)
        - finally always executes
        - Exception chaining: raise X from Y sets __cause__
        - Re-raise (bare raise) in except preserves original traceback
        """
        ctx = _ctx()
        E = Var("E")
        E1, E2 = Var("E1"), Var("E2")
        X, Y = Var("X"), Var("Y")

        base_exc = PyClassType(name="BaseException")
        exc = PyClassType(name="Exception")

        return [
            FormalAxiomEntry(
                name="base_exception_root",
                module=_MODULE,
                params=[],
                conclusion=formal_check(
                    ctx, Literal("BaseException"), PyClassType(name="type"),
                ),
                description="BaseException is the root of the exception hierarchy",
            ),
            FormalAxiomEntry(
                name="exception_subtype_base",
                module=_MODULE,
                params=[],
                conclusion=formal_subtype(ctx, exc, base_exc),
                description="Exception <: BaseException",
            ),
            FormalAxiomEntry(
                name="except_catches_subclasses",
                module=_MODULE,
                params=[("E", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("catches"), (E, OpCall(Op("subclass_of"), (E,)))),
                    PyBoolType(),
                ),
                description="except E catches E and all subclasses of E",
            ),
            FormalAxiomEntry(
                name="except_tuple_catches_union",
                module=_MODULE,
                params=[("E1", PyObjType()), ("E2", PyObjType())],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("catches"), (
                        OpCall(Op("tuple"), (E1, E2)),
                        Var("exc"),
                    )),
                    OpCall(Op("__or__"), (
                        OpCall(Op("catches"), (E1, Var("exc"))),
                        OpCall(Op("catches"), (E2, Var("exc"))),
                    )),
                ),
                description="except (E1, E2) catches E1 or E2",
            ),
            FormalAxiomEntry(
                name="bare_except_catches_exception",
                module=_MODULE,
                params=[],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("bare_except_scope"), ()),
                    Literal(exc),
                ),
                description=(
                    "A bare except clause catches all Exception instances "
                    "(not BaseException)"
                ),
            ),
            FormalAxiomEntry(
                name="finally_always_executes",
                module=_MODULE,
                params=[],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("finally_guaranteed"), ()),
                    PyBoolType(),
                ),
                description=(
                    "The finally block always executes, regardless of "
                    "whether an exception was raised or not"
                ),
            ),
            FormalAxiomEntry(
                name="exception_chaining",
                module=_MODULE,
                params=[("X", PyObjType()), ("Y", PyObjType())],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("__cause__"), (op_raise_from(X, Y),)),
                    Y,
                ),
                description=(
                    "raise X from Y sets X.__cause__ = Y (explicit "
                    "exception chaining)"
                ),
            ),
            FormalAxiomEntry(
                name="reraise_preserves_traceback",
                module=_MODULE,
                params=[],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("bare_raise_preserves_tb"), ()),
                    PyBoolType(),
                ),
                description=(
                    "A bare 'raise' inside an except block re-raises the "
                    "active exception with its original traceback"
                ),
            ),
        ]

    def try_except_semantics(
        self,
        body: SynTerm,
        handlers: list[tuple[SynType, str, SynTerm]],
        finally_: SynTerm | None = None,
    ) -> SynTerm:
        """Construct the formal semantics of try/except/finally.

        The result is a term encoding::

            try:
                body
            except E1 as e1:
                handler1
            except E2 as e2:
                handler2
            finally:
                finalizer

        as a composition of the body with handler continuations
        dispatched via the exception classifying space.
        """
        handler_terms: list[SynTerm] = []
        for exc_type, bind_name, handler_body in handlers:
            handler_terms.append(
                OpCall(
                    Op("except_handler"),
                    (Literal(exc_type), Var(bind_name), handler_body),
                )
            )

        result: SynTerm = OpCall(
            Op("try_except"),
            (body, *handler_terms),
        )

        if finally_ is not None:
            result = OpCall(Op("try_finally"), (result, finally_))

        return result

    def exception_safety_obligations(
        self,
        func: SynTerm,
        declared_exceptions: list[SynType],
    ) -> list[Judgment]:
        """Generate proof obligations for exception safety.

        For each exception type that ``func`` might raise but that is NOT
        in ``declared_exceptions``, a proof obligation is emitted
        requiring that such an exception cannot actually occur.
        """
        ctx = _ctx()
        obligations: list[Judgment] = []

        for exc_ty in declared_exceptions:
            obligations.append(
                Judgment(
                    kind=JudgmentKind.TYPE_CHECK,
                    context=ctx,
                    term=OpCall(Op("may_raise"), (func, Literal(exc_ty))),
                    type_=PyBoolType(),
                )
            )

        # Obligation: function does not raise anything outside declared set
        obligations.append(
            Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx,
                term=OpCall(
                    Op("only_raises"),
                    (func, Literal(tuple(declared_exceptions))),
                ),
                type_=PyBoolType(),
            )
        )
        return obligations


# ═══════════════════════════════════════════════════════════════════
# 3. Context Manager Semantics — Ch 17: bracket from Π-type
# ═══════════════════════════════════════════════════════════════════

class ContextManagerSemantics:
    """Context managers as bracket from Π-type.

    The ``with`` statement desugars to::

        with mgr as x:
            body
        ≡
        x = mgr.__enter__()
        try:
            body
        finally:
            mgr.__exit__(exc_type, exc_val, exc_tb)

    This is the *bracket* pattern from functional programming, lifted
    to Python's object protocol.  The Π-type captures the dependency
    of the body's type on the value returned by ``__enter__``.
    """

    def with_statement_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms encoding ``with``-statement semantics.

        Axioms:
        - __enter__ is called exactly once before the body
        - __exit__ is called exactly once after the body (even on exception)
        - If __exit__ returns True, the exception is suppressed
        - Nested with statements compose
        - contextlib.contextmanager creates a valid context manager
        """
        ctx = _ctx()
        mgr = Var("mgr")
        body = Var("body")
        none = Literal(None, PyNoneType())

        return [
            FormalAxiomEntry(
                name="enter_before_body",
                module=_MODULE,
                params=[("mgr", PyObjType()), ("body", PyObjType())],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("with_stmt"), (mgr, body)),
                    OpCall(Op("bracket"), (
                        op_enter(mgr),
                        body,
                        op_exit(mgr, none, none, none),
                    )),
                ),
                description=(
                    "__enter__ is called exactly once before the body; "
                    "__exit__ is called exactly once after"
                ),
            ),
            FormalAxiomEntry(
                name="exit_on_exception",
                module=_MODULE,
                params=[("mgr", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("exit_guaranteed_on_exc"), (mgr,)),
                    PyBoolType(),
                ),
                description=(
                    "__exit__ is called even when the body raises an "
                    "exception"
                ),
            ),
            FormalAxiomEntry(
                name="exit_suppresses_exception",
                module=_MODULE,
                params=[("mgr", PyObjType())],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("exit_returns_true_suppresses"), (mgr,)),
                    Literal(True, PyBoolType()),
                ),
                description=(
                    "If __exit__ returns True the exception is suppressed "
                    "and execution continues after the with block"
                ),
            ),
            FormalAxiomEntry(
                name="nested_with_compose",
                module=_MODULE,
                params=[
                    ("a", PyObjType()),
                    ("b", PyObjType()),
                    ("body", PyObjType()),
                ],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("with_stmt"), (
                        Var("a"),
                        OpCall(Op("with_stmt"), (Var("b"), body)),
                    )),
                    OpCall(Op("with_stmt_multi"), (Var("a"), Var("b"), body)),
                ),
                description=(
                    "Nested with statements compose: "
                    "with a: with b: body ≡ with a, b: body"
                ),
            ),
            FormalAxiomEntry(
                name="contextmanager_valid",
                module=_MODULE,
                params=[("gen_func", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(
                        Op("contextmanager", "contextlib"),
                        (Var("gen_func"),),
                    ),
                    PyObjType(),
                ),
                description=(
                    "contextlib.contextmanager transforms a generator "
                    "function (with exactly one yield) into a valid "
                    "context manager"
                ),
            ),
        ]

    def resource_safety_obligations(self, mgr_type: SynType) -> list[Judgment]:
        """Generate proof obligations for resource safety.

        Ensures that resources acquired via ``__enter__`` are properly
        released by ``__exit__``, even in the presence of exceptions.
        """
        ctx = _ctx()
        mgr = Var("mgr")
        return [
            Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx.extend("mgr", mgr_type),
                term=OpCall(Op("resource_released"), (mgr,)),
                type_=PyBoolType(),
            ),
            Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx.extend("mgr", mgr_type),
                term=OpCall(Op("enter_exit_paired"), (mgr,)),
                type_=PyBoolType(),
            ),
        ]


# ═══════════════════════════════════════════════════════════════════
# 4. Async/Await Semantics — Ch 18: Suspend effect
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class CoroutineType(SynType):
    """Coroutine[Y, S, T] — the async counterpart of GeneratorType."""
    yield_type: SynType = field(default_factory=PyObjType)
    send_type: SynType = field(default_factory=PyNoneType)
    return_type: SynType = field(default_factory=PyNoneType)

    def _repr(self) -> str:
        return (f"Coroutine[{self.yield_type._repr()}, "
                f"{self.send_type._repr()}, {self.return_type._repr()}]")


@dataclass(frozen=True)
class AwaitableType(SynType):
    """Awaitable[T] — any object that can be used with ``await``."""
    result_type: SynType = field(default_factory=PyObjType)

    def _repr(self) -> str:
        return f"Awaitable[{self.result_type._repr()}]"


class AsyncSemantics:
    """Async/await as the Suspend effect.

    ``async def f(): ...`` creates a coroutine.
    ``await expr`` suspends until the awaitable completes.

    The Suspend effect turns a computation ``A`` into a suspended
    computation ``Suspend(A)`` that only progresses when the event-loop
    schedules it.  ``await`` is the elimination form:

        await : Awaitable(A) → A    (within an async context)
    """

    def coroutine_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for async coroutine semantics.

        Axioms:
        - await is the elimination form for Awaitable(A) → A
        - async for desugars to __aiter__ / __anext__ protocol
        - async with desugars to __aenter__ / __aexit__ protocol
        - asyncio.gather preserves results order
        - asyncio.create_task creates concurrent execution
        """
        ctx = _ctx()
        a = Var("a")
        mgr = Var("mgr")
        obj = Var("obj")
        none = Literal(None, PyNoneType())

        return [
            FormalAxiomEntry(
                name="await_elimination",
                module=_MODULE,
                params=[("a", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    op_await(a),
                    PyObjType(),
                ),
                description=(
                    "await is the elimination form: "
                    "Awaitable(A) → A within an async context"
                ),
            ),
            FormalAxiomEntry(
                name="async_for_desugar",
                module=_MODULE,
                params=[("obj", PyObjType()), ("body", PyObjType())],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("async_for"), (obj, Var("body"))),
                    OpCall(Op("async_for_desugar"), (
                        op_aiter(obj),
                        Var("body"),
                    )),
                ),
                description=(
                    "async for desugars to: "
                    "ait = obj.__aiter__(); "
                    "loop: x = await ait.__anext__()"
                ),
            ),
            FormalAxiomEntry(
                name="async_with_desugar",
                module=_MODULE,
                params=[("mgr", PyObjType()), ("body", PyObjType())],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("async_with"), (mgr, Var("body"))),
                    OpCall(Op("bracket"), (
                        op_await(op_aenter(mgr)),
                        Var("body"),
                        op_await(op_aexit(mgr, none, none, none)),
                    )),
                ),
                description=(
                    "async with desugars to: "
                    "x = await mgr.__aenter__(); try: body; "
                    "finally: await mgr.__aexit__(...)"
                ),
            ),
            FormalAxiomEntry(
                name="gather_preserves_order",
                module=_MODULE,
                params=[],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("gather_order_invariant", "asyncio"), ()),
                    PyBoolType(),
                ),
                description=(
                    "asyncio.gather returns results in the same order "
                    "as the awaitables were passed"
                ),
            ),
            FormalAxiomEntry(
                name="create_task_concurrent",
                module=_MODULE,
                params=[("a", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("create_task", "asyncio"), (a,)),
                    PyObjType(),
                ),
                description=(
                    "asyncio.create_task schedules a coroutine for "
                    "concurrent execution on the event loop"
                ),
            ),
        ]

    def concurrent_safety_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for concurrency safety under asyncio.

        Axioms:
        - Two coroutines sharing no mutable state are independent
        - asyncio.Lock prevents concurrent access
        - asyncio.Queue is task-safe
        """
        ctx = _ctx()
        c1, c2 = Var("c1"), Var("c2")

        return [
            FormalAxiomEntry(
                name="no_shared_state_independence",
                module=_MODULE,
                params=[("c1", PyObjType()), ("c2", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("independent_if_disjoint"), (c1, c2)),
                    PyBoolType(),
                ),
                description=(
                    "Two coroutines that share no mutable state are "
                    "independent — their interleaving does not affect "
                    "the result"
                ),
            ),
            FormalAxiomEntry(
                name="lock_mutual_exclusion",
                module=_MODULE,
                params=[],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("lock_ensures_mutex", "asyncio"), ()),
                    PyBoolType(),
                ),
                description=(
                    "asyncio.Lock ensures mutual exclusion: at most one "
                    "coroutine holds the lock at any time"
                ),
            ),
            FormalAxiomEntry(
                name="queue_task_safe",
                module=_MODULE,
                params=[],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("queue_task_safe", "asyncio"), ()),
                    PyBoolType(),
                ),
                description=(
                    "asyncio.Queue is safe for concurrent access by "
                    "multiple coroutines — put/get are atomic"
                ),
            ),
        ]


# ═══════════════════════════════════════════════════════════════════
# 5. Loop Semantics — Appendix A: For, While, break/continue
# ═══════════════════════════════════════════════════════════════════

class LoopSemantics:
    """For and while loops with termination checking.

    A ``for`` loop is desugared as a fold over an iterable, while a
    ``while`` loop requires an explicit termination measure (variant)
    that strictly decreases on each iteration.
    """

    def for_loop_as_fold(
        self,
        var: str,
        iterable: SynTerm,
        body: SynTerm,
        init: SynTerm,
    ) -> SynTerm:
        """Desugar a for-loop as fold.

        ``for x in iter: body`` ≡ ``fold(λacc x. body, init, iter)``

        The accumulator ``init`` is the initial state before the loop
        begins (often the unit value when the loop is used only for
        side-effects).
        """
        acc_var = Var("__acc")
        x_var = Var(var)
        step_fn = Lam(
            param="__acc",
            param_type=PyObjType(),
            body=Lam(param=var, param_type=PyObjType(), body=body),
        )
        return op_fold(step_fn, init, iterable)

    def while_loop_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for loop semantics.

        Axioms:
        - while cond: body terminates if variant decreases each iteration
        - for x in finite_iter: body always terminates
        - break exits the innermost loop
        - continue skips to next iteration
        - for/else: else runs iff loop completes without break
        """
        ctx = _ctx()
        cond = Var("cond")
        body = Var("body")
        variant = Var("variant")
        it = Var("iter")

        return [
            FormalAxiomEntry(
                name="while_terminates_with_variant",
                module=_MODULE,
                params=[
                    ("cond", PyObjType()),
                    ("body", PyObjType()),
                    ("variant", PyObjType()),
                ],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("while_terminates"), (cond, body, variant)),
                    PyBoolType(),
                ),
                description=(
                    "while cond: body terminates if the variant is a "
                    "natural number that strictly decreases each iteration"
                ),
            ),
            FormalAxiomEntry(
                name="for_finite_terminates",
                module=_MODULE,
                params=[("iter", PyObjType()), ("body", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("for_terminates"), (it, body)),
                    PyBoolType(),
                ),
                description=(
                    "for x in finite_iter: body always terminates "
                    "because the iterable is finite"
                ),
            ),
            FormalAxiomEntry(
                name="break_exits_innermost",
                module=_MODULE,
                params=[],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("break_scope"), ()),
                    PyBoolType(),
                ),
                description="break exits the innermost enclosing loop",
            ),
            FormalAxiomEntry(
                name="continue_skips_iteration",
                module=_MODULE,
                params=[],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("continue_scope"), ()),
                    PyBoolType(),
                ),
                description=(
                    "continue skips the rest of the current iteration "
                    "and jumps to the next"
                ),
            ),
            FormalAxiomEntry(
                name="for_else_no_break",
                module=_MODULE,
                params=[
                    ("iter", PyObjType()),
                    ("body", PyObjType()),
                ],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("for_else"), (it, body, Var("else_body"))),
                    PyObjType(),
                ),
                description=(
                    "for/else: the else clause executes if and only if "
                    "the loop completed without encountering a break"
                ),
            ),
        ]

    def termination_obligation(
        self, variant: SynTerm, body: SynTerm,
    ) -> Judgment:
        """Generate proof obligation: body decreases variant.

        The obligation states that after executing ``body`` the value
        of ``variant`` is strictly less than before, and ``variant``
        is bounded below by 0.
        """
        ctx = _ctx()
        return Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=ctx,
            term=OpCall(Op("variant_decreases"), (variant, body)),
            type_=RefinementType(
                base_type=PyIntType(),
                var_name="v",
                predicate="v >= 0 and v_after < v_before",
            ),
        )


# ═══════════════════════════════════════════════════════════════════
# 6. Comprehension Semantics — Ch 20: list monad bind
# ═══════════════════════════════════════════════════════════════════

class ComprehensionSemantics:
    """Comprehensions as monadic bind.

    ``[f(x) for x in xs if p(x)]``
    ≡ ``bind(filter(p, xs), λx. return(f(x)))``
    ≡ ``map(f, filter(p, xs))``

    Dict and set comprehensions are analogous, with the list monad
    replaced by the appropriate collection monad.
    """

    def comprehension_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for comprehension semantics.

        Axioms:
        - List comp is equivalent to map+filter
        - Dict comp produces unique keys (last wins)
        - Set comp removes duplicates
        - Generator expression is lazy (only evaluated on demand)
        - Nested comprehension flattening
        - len([f(x) for x in xs]) == len(xs)  (no filter)
        - len([f(x) for x in xs if p(x)]) <= len(xs)
        """
        ctx = _ctx()
        f = Var("f")
        p = Var("p")
        xs = Var("xs")
        x = Var("x")

        return [
            FormalAxiomEntry(
                name="listcomp_is_map_filter",
                module=_MODULE,
                params=[
                    ("f", PyObjType()),
                    ("p", PyObjType()),
                    ("xs", PyObjType()),
                ],
                conclusion=formal_eq(
                    ctx,
                    op_listcomp(OpCall(Op("__call__"), (f, x)), "x", xs, OpCall(Op("__call__"), (p, x))),
                    op_map(f, op_filter(p, xs)),
                ),
                description=(
                    "List comprehension [f(x) for x in xs if p(x)] is "
                    "equivalent to map(f, filter(p, xs))"
                ),
            ),
            FormalAxiomEntry(
                name="dictcomp_last_key_wins",
                module=_MODULE,
                params=[("xs", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("dictcomp_unique_keys"), (xs,)),
                    PyBoolType(),
                ),
                description=(
                    "Dict comprehension {k: v for ...} produces unique "
                    "keys; if a key appears multiple times the last "
                    "value wins"
                ),
            ),
            FormalAxiomEntry(
                name="setcomp_removes_duplicates",
                module=_MODULE,
                params=[("xs", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("setcomp_no_duplicates"), (xs,)),
                    PyBoolType(),
                ),
                description=(
                    "Set comprehension {f(x) for x in xs} removes "
                    "duplicate values"
                ),
            ),
            FormalAxiomEntry(
                name="genexpr_lazy",
                module=_MODULE,
                params=[
                    ("f", PyObjType()),
                    ("xs", PyObjType()),
                ],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("genexpr_is_lazy"), (f, xs)),
                    PyBoolType(),
                ),
                description=(
                    "A generator expression (f(x) for x in xs) is lazy: "
                    "elements are produced only on demand via next()"
                ),
            ),
            FormalAxiomEntry(
                name="nested_comp_flattening",
                module=_MODULE,
                params=[
                    ("f", PyObjType()),
                    ("xss", PyObjType()),
                ],
                conclusion=formal_eq(
                    ctx,
                    OpCall(Op("nested_listcomp"), (f, Var("xss"))),
                    OpCall(Op("flat_map"), (f, Var("xss"))),
                ),
                description=(
                    "Nested comprehension [f(x) for xs in xss for x in "
                    "xs] flattens via monadic bind (concatMap / flat_map)"
                ),
            ),
            FormalAxiomEntry(
                name="listcomp_len_no_filter",
                module=_MODULE,
                params=[
                    ("f", PyObjType()),
                    ("xs", PyObjType()),
                ],
                conclusion=formal_eq(
                    ctx,
                    op_len(op_listcomp(OpCall(Op("__call__"), (f, x)), "x", xs)),
                    op_len(xs),
                ),
                description=(
                    "len([f(x) for x in xs]) == len(xs) when there "
                    "is no filter clause"
                ),
            ),
            FormalAxiomEntry(
                name="listcomp_len_with_filter",
                module=_MODULE,
                params=[
                    ("f", PyObjType()),
                    ("p", PyObjType()),
                    ("xs", PyObjType()),
                ],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("__le__"), (
                        op_len(op_listcomp(OpCall(Op("__call__"), (f, x)), "x", xs, OpCall(Op("__call__"), (p, x)))),
                        op_len(xs),
                    )),
                    PyBoolType(),
                ),
                description=(
                    "len([f(x) for x in xs if p(x)]) <= len(xs)"
                ),
            ),
        ]


# ═══════════════════════════════════════════════════════════════════
# 7. Closure Semantics — Ch 12: scope fiber bundle
# ═══════════════════════════════════════════════════════════════════

class ClosureSemantics:
    """Closures and scope resolution via fiber-bundle model.

    Python's scoping (LEGB: Local, Enclosing, Global, Built-in) forms
    a fiber bundle where each function's local scope is a fiber over
    the enclosing scope.  ``nonlocal`` and ``global`` declarations
    specify which fiber a variable lives in.

    Closures capture variables *by reference* (late binding), which is
    a well-known source of bugs in loop-based closures.
    """

    def closure_axioms(self) -> list[FormalAxiomEntry]:
        """Axioms for closure / scope semantics.

        Axioms:
        - Closure captures variables by reference (late binding)
        - nonlocal declares variable is from enclosing scope
        - global declares variable is from module scope
        - Default arguments are evaluated at function definition time
        - Lambda closures share these semantics
        """
        ctx = _ctx()
        f = Var("f")
        x = Var("x")
        val = Var("val")

        return [
            FormalAxiomEntry(
                name="closure_late_binding",
                module=_MODULE,
                params=[("f", PyObjType()), ("x", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("closure_captures_by_ref"), (f, x)),
                    PyBoolType(),
                ),
                description=(
                    "A closure captures free variables by reference: "
                    "the value of x at call-time (not definition-time) "
                    "is used"
                ),
            ),
            FormalAxiomEntry(
                name="nonlocal_enclosing_scope",
                module=_MODULE,
                params=[("x", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("nonlocal_resolves_enclosing"), (x,)),
                    PyBoolType(),
                ),
                description=(
                    "nonlocal x declares that x refers to the binding "
                    "in the nearest enclosing function scope"
                ),
            ),
            FormalAxiomEntry(
                name="global_module_scope",
                module=_MODULE,
                params=[("x", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("global_resolves_module"), (x,)),
                    PyBoolType(),
                ),
                description=(
                    "global x declares that x refers to the module-level "
                    "binding, bypassing enclosing scopes"
                ),
            ),
            FormalAxiomEntry(
                name="default_arg_eval_at_def",
                module=_MODULE,
                params=[("f", PyObjType()), ("val", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("default_evaluated_at_def"), (f, val)),
                    PyBoolType(),
                ),
                description=(
                    "Default argument values are evaluated once at "
                    "function definition time, not at each call"
                ),
            ),
            FormalAxiomEntry(
                name="lambda_closure_shared",
                module=_MODULE,
                params=[("f", PyObjType())],
                conclusion=formal_check(
                    ctx,
                    OpCall(Op("lambda_same_closure_rules"), (f,)),
                    PyBoolType(),
                ),
                description=(
                    "Lambda expressions share the same closure and "
                    "scoping semantics as named function definitions"
                ),
            ),
        ]


# ═══════════════════════════════════════════════════════════════════
# 8. Aggregate: collect all control-flow axioms
# ═══════════════════════════════════════════════════════════════════

def all_control_axioms() -> list[FormalAxiomEntry]:
    """Return every control-flow axiom in a single list.

    The axioms are grouped by semantic domain and returned in a
    deterministic order suitable for registration in an axiom registry.
    """
    axioms: list[FormalAxiomEntry] = []

    gen = GeneratorSemantics()
    axioms.extend(gen.generator_protocol_axioms())
    axioms.extend(gen.generator_composition_axioms())

    exc = ExceptionSemantics()
    axioms.extend(exc.exception_hierarchy_axioms())

    cm = ContextManagerSemantics()
    axioms.extend(cm.with_statement_axioms())

    asyn = AsyncSemantics()
    axioms.extend(asyn.coroutine_axioms())
    axioms.extend(asyn.concurrent_safety_axioms())

    loop = LoopSemantics()
    axioms.extend(loop.while_loop_axioms())

    comp = ComprehensionSemantics()
    axioms.extend(comp.comprehension_axioms())

    clos = ClosureSemantics()
    axioms.extend(clos.closure_axioms())

    return axioms


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Run basic smoke tests for every semantic class."""
    errors: list[str] = []

    def _assert(condition: bool, msg: str) -> None:
        if not condition:
            errors.append(msg)

    # ── GeneratorType ─────────────────────────────────────────────
    gt = GeneratorType(
        yield_type=PyIntType(),
        send_type=PyNoneType(),
        return_type=PyStrType(),
    )
    _assert(gt._repr() == "Generator[int, None, str]",
            f"GeneratorType _repr failed: {gt._repr()}")

    gen = GeneratorSemantics()
    _assert(gen.yield_type(gt) == PyIntType(),
            "yield_type extraction failed")
    _assert(gen.send_type(gt) == PyNoneType(),
            "send_type extraction failed")
    _assert(gen.return_type(gt) == PyStrType(),
            "return_type extraction failed")
    # Fallback for non-generator types
    _assert(gen.yield_type(PyObjType()) == PyObjType(),
            "yield_type fallback failed")
    _assert(gen.send_type(PyObjType()) == PyNoneType(),
            "send_type fallback failed")

    proto_ax = gen.generator_protocol_axioms()
    _assert(len(proto_ax) == 6,
            f"Expected 6 generator protocol axioms, got {len(proto_ax)}")
    _assert(proto_ax[0].name == "next_is_send_none",
            f"First protocol axiom name wrong: {proto_ax[0].name}")
    for ax in proto_ax:
        _assert(ax.module == _MODULE,
                f"Axiom {ax.name} has wrong module: {ax.module}")
        _assert(isinstance(ax.conclusion, Judgment),
                f"Axiom {ax.name} conclusion is not a Judgment")

    comp_ax = gen.generator_composition_axioms()
    _assert(len(comp_ax) == 3,
            f"Expected 3 generator composition axioms, got {len(comp_ax)}")

    # ── ExceptionSemantics ────────────────────────────────────────
    exc = ExceptionSemantics()
    exc_ax = exc.exception_hierarchy_axioms()
    _assert(len(exc_ax) == 8,
            f"Expected 8 exception axioms, got {len(exc_ax)}")
    _assert(exc_ax[0].name == "base_exception_root",
            f"First exception axiom name wrong: {exc_ax[0].name}")
    _assert(exc_ax[1].name == "exception_subtype_base",
            f"Second exception axiom name wrong: {exc_ax[1].name}")

    # try_except_semantics
    body = Var("body")
    handler_body = Var("handle_it")
    result = exc.try_except_semantics(
        body,
        [(PyClassType(name="ValueError"), "e", handler_body)],
        finally_=Var("cleanup"),
    )
    _assert(isinstance(result, OpCall),
            f"try_except_semantics should return OpCall, got {type(result)}")

    # exception_safety_obligations
    obligations = exc.exception_safety_obligations(
        Var("my_func"),
        [PyClassType(name="ValueError"), PyClassType(name="TypeError")],
    )
    _assert(len(obligations) == 3,
            f"Expected 3 obligations, got {len(obligations)}")
    _assert(obligations[-1].kind == JudgmentKind.TYPE_CHECK,
            "Last obligation should be TYPE_CHECK")

    # ── ContextManagerSemantics ───────────────────────────────────
    cm = ContextManagerSemantics()
    cm_ax = cm.with_statement_axioms()
    _assert(len(cm_ax) == 5,
            f"Expected 5 context-manager axioms, got {len(cm_ax)}")
    _assert(cm_ax[0].name == "enter_before_body",
            f"First CM axiom wrong: {cm_ax[0].name}")

    # resource obligations
    res_obs = cm.resource_safety_obligations(PyObjType())
    _assert(len(res_obs) == 2,
            f"Expected 2 resource obligations, got {len(res_obs)}")

    # ── AsyncSemantics ────────────────────────────────────────────
    ct = CoroutineType(
        yield_type=PyNoneType(),
        send_type=PyNoneType(),
        return_type=PyIntType(),
    )
    _assert("Coroutine" in ct._repr(),
            f"CoroutineType _repr missing 'Coroutine': {ct._repr()}")
    at = AwaitableType(result_type=PyIntType())
    _assert("Awaitable" in at._repr(),
            f"AwaitableType _repr missing 'Awaitable': {at._repr()}")

    asyn = AsyncSemantics()
    cor_ax = asyn.coroutine_axioms()
    _assert(len(cor_ax) == 5,
            f"Expected 5 coroutine axioms, got {len(cor_ax)}")
    _assert(cor_ax[0].name == "await_elimination",
            f"First coroutine axiom wrong: {cor_ax[0].name}")

    conc_ax = asyn.concurrent_safety_axioms()
    _assert(len(conc_ax) == 3,
            f"Expected 3 concurrency axioms, got {len(conc_ax)}")

    # ── LoopSemantics ─────────────────────────────────────────────
    loop = LoopSemantics()
    fold_term = loop.for_loop_as_fold(
        var="x",
        iterable=Var("items"),
        body=Var("process"),
        init=Literal(0),
    )
    _assert(isinstance(fold_term, OpCall),
            f"for_loop_as_fold should return OpCall, got {type(fold_term)}")

    loop_ax = loop.while_loop_axioms()
    _assert(len(loop_ax) == 5,
            f"Expected 5 loop axioms, got {len(loop_ax)}")
    _assert(loop_ax[0].name == "while_terminates_with_variant",
            f"First loop axiom wrong: {loop_ax[0].name}")

    term_ob = loop.termination_obligation(Var("n"), Var("decrement"))
    _assert(term_ob.kind == JudgmentKind.TYPE_CHECK,
            "Termination obligation should be TYPE_CHECK")
    _assert(isinstance(term_ob.type_, RefinementType),
            "Termination obligation type should be RefinementType")

    # ── ComprehensionSemantics ────────────────────────────────────
    comp = ComprehensionSemantics()
    comp_ax = comp.comprehension_axioms()
    _assert(len(comp_ax) == 7,
            f"Expected 7 comprehension axioms, got {len(comp_ax)}")
    _assert(comp_ax[0].name == "listcomp_is_map_filter",
            f"First comp axiom wrong: {comp_ax[0].name}")

    # ── ClosureSemantics ──────────────────────────────────────────
    clos = ClosureSemantics()
    clos_ax = clos.closure_axioms()
    _assert(len(clos_ax) == 5,
            f"Expected 5 closure axioms, got {len(clos_ax)}")
    _assert(clos_ax[0].name == "closure_late_binding",
            f"First closure axiom wrong: {clos_ax[0].name}")

    # ── all_control_axioms ────────────────────────────────────────
    all_ax = all_control_axioms()
    expected_total = (
        6 + 3     # generator protocol + composition
        + 8       # exception hierarchy
        + 5       # context manager
        + 5 + 3   # async coroutine + concurrency
        + 5       # loop
        + 7       # comprehension
        + 5       # closure
    )
    _assert(len(all_ax) == expected_total,
            f"Expected {expected_total} total axioms, got {len(all_ax)}")

    # Every axiom has a non-empty name, module, and description
    for ax in all_ax:
        _assert(bool(ax.name),
                f"Axiom has empty name: {ax}")
        _assert(ax.module == _MODULE,
                f"Axiom {ax.name} has wrong module: {ax.module}")
        _assert(bool(ax.description),
                f"Axiom {ax.name} has empty description")
        _assert(isinstance(ax.conclusion, Judgment),
                f"Axiom {ax.name} conclusion is not a Judgment")

    # All axiom names are unique
    names = [ax.name for ax in all_ax]
    _assert(len(names) == len(set(names)),
            f"Duplicate axiom names: {[n for n in names if names.count(n) > 1]}")

    # Print results
    if errors:
        print(f"FAILED — {len(errors)} error(s):")
        for e in errors:
            print(f"  ✗ {e}")
        raise AssertionError(f"{len(errors)} self-test(s) failed")
    else:
        print(f"OK — all {len(all_ax)} axioms validated "
              f"({len(names)} unique names, 0 errors)")


if __name__ == "__main__":
    _self_test()
