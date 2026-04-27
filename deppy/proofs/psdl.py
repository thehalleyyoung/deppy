"""PSDL — Python-Semantic Deppy Language.

The proof script is **literal Python**: ``ast.parse`` reads it,
and each Python statement is mapped to a deppy :class:`ProofTerm`
plus a Lean tactic.  No new syntax to learn.  The tactic vocabulary
is just Python idioms whose *semantics* in PSDL are deppy's
cubical / cohomological / duck-typed / effect-modal proof primitives.

Design intent
=============

PSDL aims for **full CIC-level expressivity** (anything provable in
the Calculus of Inductive Constructions can be written here) **plus
primitives unique to reasoning about cubical-duck-typed effectful
Python**.  The two concerns are kept separate in the table below:

  * **CIC core** — Π / Σ / inductive types, path types, equivalences,
    quantifiers, induction principles, substitution.  Same expressive
    power as Lean / Coq.
  * **Cubical / duck / effect** — primitives that make sense only
    when the underlying language being reasoned about is Python:
    DuckPath dispatch, ◇ / □ effect modalities, isinstance fibration,
    exception fibres, Kan-filling, cocycle constructors.

Both are surfaced as Python idioms so the user never leaves Python.

Mapping table (Python syntax → deppy ProofTerm → Lean tactic)
============================================================

Control flow → cubical / fibration:
-----------------------------------

::

    if isinstance(x, T):            # Fibration on isinstance fibre
        <value-fibre body>
    else:
        <complement-fibre body>

  → Fiber(scrutinee=x, type_branches=[(T, body), (else, complement)])
  → by_cases h : isinstance x T

::

    try:                            # Effect-modal split
        <value-fibre body>
    except TypeError:               # exception fibre
        <handler body>

  → EffectWitness(value_proof) + ConditionalEffectWitness(exception_proof)
  → match h : ... with | ... | ...

::

    match x:                        # Case analysis
        case A: <body>
        case B: <body>

  → Cases(scrutinee=x, branches=[("A", body), ("B", body)])
  → cases x with | A => ... | B => ...

::

    for x in xs:                    # List induction (cons case)
        <step body>
    # marker: # nil: <nil body>

  → ListInduction(var=xs, nil=body, cons=step)
  → induction xs with | nil => ... | cons _ _ ih => ...

::

    while n:                        # Nat induction
        <step body>

  → NatInduction(var=n, base, step)

Logical / equality:
-------------------

::

    assert P                        # discharge P; default: Z3
    assert P, "z3"                  # explicit Z3
    assert P, "by F"                # by foundation F
    assert P, "by lemma L"          # by lemma L

  → Cut(P, lemma_proof, body_proof)
  → have h : P := <discharge>

::

    apply(F)                        # cite a foundation/axiom
    F                               # alias: bare-call form

  → AxiomInvocation(F)
  → exact F

::

    inline(method, expected_expr)   # body translation assertion
    unfold(method)                  # plain Unfold
    method.unfold()                 # alias: method-call form

  → Unfold(method, Refl(expected) | inner)
  → unfold method; rfl | tactic

::

    return expr                     # Reflexivity at expr

  → Refl(expr)
  → rfl

::

    rewrite(L)                      # rewrite using lemma L
    L.rewrite()                     # alias

  → Rewrite(L, body)
  → rw [L]; tactic

Path / homotopy:
---------------

::

    transport(p, value)             # Transport along a path
    funext(lambda x: body)          # function extensionality

  → TransportProof / FunExt
  → custom Lean

Modality / structural:
----------------------

::

    pure()                          # □A modality
    pass                            # trivial
    raise TypeError                 # exception fibre marker
    raise NotImplementedError       # vacuous (gated Structural)

LLM / debug:
-----------

::

    show_goal()                     # surface goal for LLM iteration
    hint("text")                    # inline hint
    lean("...raw lean...")          # raw Lean escape hatch

Compositional:
-------------

::

    h: T = expr                     # local lemma (type-annotated)
    L = lemma(name, statement, by)  # named local lemma

  → Cut(L, T, ...)
  → have L : T := tactic

CIC core — Π / Σ / quantifiers / induction (full CIC expressivity):
-------------------------------------------------------------------

::

    forall(x, T, body_proof)        # universal quantifier
    exists(x, T, witness, body)     # existential introduction

  → Cut(∀x:T, body) / Cut(∃x:T, body)
  → ∀ x : T, P / ⟨witness, body⟩

::

    Pi[x: T](B(x))                  # Π-type as a type expression
    Sigma[x: T](B(x))               # Σ-type
    Path[A, x, y]                   # identity / path type
    Equiv[A, B]                     # type of equivalences
    Diamond[A]                      # ◇A — may have effect
    Box[A]                          # □A — pure
    Refinement[T, P]                # {x : T // P x}

  → SynType-level decorations recognised at AnnAssign / lemma sites
  → Π / Σ / Eq / Equiv / ◇ / □ / Subtype  in Lean

::

    induction(n) on Nat:            # explicit well-founded induction
        case Z(): <base body>
        case S(k, ih): <step body>

  → NatInduction(base, step) (or ListInduction for List)
  → induction n with | Z => base | S k ih => step

::

    subst(eq, motive, body)         # substitution along an equation
    rew(eq, body)                   # bare rewrite (rew = subst with default motive)
    cong(f, eq)                     # congruence on f
    sym(eq)                         # symmetry
    trans(eq1, eq2)                 # transitivity

  → Rewrite / Sym / Trans / Cong wired through deppy.kernel
  → rw / Eq.symm / Eq.trans / congrArg in Lean

::

    refl(x)                         # Refl[x] as an explicit term
    Refl[x]                         # subscript form (pun on Path)
    path_concat(p, q)               # composite path
    path_inv(p)                     # inverse path
    path_ap(f, p)                   # functorial action

  → Refl / PathComp / PathInv / Ap
  → Eq.refl / Eq.trans / Eq.symm / congrArg

::

    J(motive, refl_case, x, y, p)   # path induction (Martin-Löf J)

  → PathInduction node (transports motive along p starting from refl_case)
  → @Eq.rec ...

Equivalences / univalence:
-------------------------

::

    iso(forward, backward, l_inv, r_inv)    # build an Equiv from iso
    equiv_to_path(e)                        # univalence axiom: Equiv → Path

  → Equiv constructor / UnivalenceAxiom
  → Equiv.mk / ua-style transport

User-defined inductives + theorems (top-level):
-----------------------------------------------

::

    @inductive
    class Tree:
        Leaf: int
        Node: (Tree, Tree)
    # → adds an inductive type to PSDL's local context.

    @axiom
    def magic() -> Path[Int, 0, 1]: ...
    # → extends the local axiom table.

    @theorem
    def my_lemma(x: Nat) -> Path[Nat, x + 0, x]:
        induction(x) on Nat:
            case Z(): refl(0)
            case S(k, ih): cong(succ, ih)
    # → emits a Lean theorem definition; PSDL then has it
    #   available for citation.

Cubical / duck / effect-Python primitives:
------------------------------------------

::

    dispatch(obj, "method")         # duck-path dispatch
    # → DuckPath: obj.method ≃ Class.method(obj) for the resolved class
    # → exact (DuckPath_resolve obj method)

::

    kan_fill(open_box, filling)     # Kan-fill a cubical box
    # → KanFiller node
    # → tactic: apply Kan.fill ...

::

    cocycle(level, witness)         # construct an n-cocycle (C⁰/C¹/C²)
    # → Cocycle node at the given level

::

    fibre_split(x, [(T1, body1), (T2, body2), ...])  # explicit fibration
    # → Fiber with explicit type indices
    # → cases on isinstance

::

    Diamond[A]                      # ◇A — value may raise / be partial
    Box[A]                          # □A — guaranteed pure
    pure(v)                         # □-introduction
    bind(m, k)                      # ◇ Kleisli composition
    expect(m, fallback)             # exception-fibre handler
    lift(v)                         # ◇-introduction (any value lifts)
    lower(m, witness)               # ◇-elimination (needs purity witness)
    # → Effect-modal proof primitives via EffectWitness /
    #   ConditionalEffectWitness

::

    homotopy(p, q)                  # proof p ~ q (paths between paths)
    square(top, bot, left, right)   # 2-square diagram (cubical)
    # → Path-between-paths nodes

Term-mode mixing:
----------------

::

    term[T](expr)                   # embed a term-mode subproof
    tactic[T](raw_lean)             # embed a raw Lean tactic block

Implicit-arg syntax:
-------------------

PSDL respects Python's keyword arguments::

    Path(A=Nat, x=0, y=0)           # equivalent to Path[Nat, 0, 0]
    forall(x=Nat, body=...)

Syntactic sugar (the "make it feel like Python" layer):
=======================================================

Operator-overloaded proof composition:
--------------------------------------

::

    p @ q                           # path composition: ``p ; q``
                                    # → PathComp(p, q)
    ~p                              # path inversion / equation symmetry
                                    # → Sym(p)
    f * p                           # functorial action / congruence
                                    # → Ap(f, p)  /  Cong(f, p)
    p ** k                          # k-fold path composition
    proof_a >> proof_b              # sequential chaining (Cut + body)

Walrus (named-expression) inline lemmas:
----------------------------------------

::

    (h := apply(Real_sqrt_nonneg))  # bind a sub-proof inline
    return cong(f, (eq2 := trans(p1, p2)))

Comprehensions over proofs:
---------------------------

::

    [refl(x) for x in xs]           # list of pointwise reflexivities
    [cong(f, p_i) for p_i in paths] # batch congruences
    all(P(x) for x in xs)           # universal closure proof

Context managers for goal scoping:
----------------------------------

::

    with goal("Point.distance(p, q) >= 0"):
        apply(Real_sqrt_nonneg)
        ...                         # Refines: emit a sub-goal block.

    with case("then-branch"):
        ...                         # Focus a Cases / Fiber arm.

    with hypothesis(h="p > 0"):
        ...                         # Introduce h locally.

Postfix sugar on equations / paths:
-----------------------------------

::

    eq.symm                         # Sym(eq)         (Lean: eq.symm)
    eq.trans(eq2)                   # Trans(eq, eq2)  (Lean: eq.trans eq2)
    eq.lhs / eq.rhs                 # left/right side projection
    path.inv                        # Sym(path)       (alias of .symm)
    path.unfold                     # already supported
    path.rewrite                    # already supported

Tuple unpacking on equations:
-----------------------------

::

    lhs, rhs = eq.sides             # extract sides
    (a, b) = pair                   # bind pair components

Lambda type families:
--------------------

::

    motive = lambda x: P(x)
    transport(motive, p, value)     # uses ``motive`` as the family

Conditional expressions for case-style proofs:
----------------------------------------------

::

    proof_a if cond else proof_b    # Cases on ``cond``

Closer sugar (any of these terminates a proof block):
----------------------------------------------------

::

    qed()                           # ``first | rfl | omega | decide | trivial``
    auto()                          # ``simp; first | rfl | omega | decide``
    done()                          # ``trivial`` / ``rfl``
    omega()                         # ``omega``
    rfl_()                          # ``rfl``  (underscore to dodge keyword)

Negation / conjunction / disjunction sugar (Lean-style):
--------------------------------------------------------

::

    not P                           # negation introduction
    P and Q                         # conjunction (And.intro)
    P or Q                          # disjunction (Or.intro)


Example
=======

Proving ``Point.distance(p, q) >= 0`` in PSDL:

::

    psdl_proof: |
      if isinstance(other, Point):
          # value-fibre: body returns sqrt(sum_zip_sub_sq(self, other))
          inline(Point.distance, sqrt(sum_zip_sub_sq(self, other)))
          # sqrt is non-negative for non-negative argument:
          apply(Real_sqrt_nonneg)
          # side condition discharged by Z3:
          assert sum_zip_sub_sq(self, other) >= 0, "z3"
      else:
          # exception-fibre: TypeError raised, vacuous
          raise NotImplementedError  # vacuous: value-fibre handles Points

Returns a :class:`PSDLCompileResult` with a deppy :class:`ProofTerm`
*and* a Lean tactic, both expressing the same derivation.
"""
from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from typing import Any, Optional

from deppy.core.kernel import (
    ProofTerm,
    Refl, Sym, Trans, Cong, Unfold, Rewrite, AxiomInvocation,
    Cases, Fiber, Structural, TransportProof, Z3Proof, LeanProof,
    NatInduction, ListInduction, DuckPath, ConditionalDuckPath,
    FiberedLookup, EffectWitness, ConditionalEffectWitness,
    Patch, PathComp, Ap, FunExt, Cocycle, Cut, Assume,
)
from deppy.core.types import (
    Context, Var, Literal, PyObjType, PyIntType, PyBoolType,
    RefinementType, SynTerm, SynType,
)


# ─────────────────────────────────────────────────────────────────────
#  Output dataclasses
# ─────────────────────────────────────────────────────────────────────

@dataclass
class PSDLError:
    line_no: int
    line_text: str
    message: str


@dataclass
class PSDLCompileResult:
    proof_term: Optional[ProofTerm] = None
    lean_tactic: str = ""
    term_repr: str = ""
    errors: list[PSDLError] = field(default_factory=list)
    hints: list[str] = field(default_factory=list)
    show_goal_requested: bool = False
    foundations_referenced: list[str] = field(default_factory=list)
    # Cubical heap+effect snapshot at the end of compilation.
    # ``final_epoch`` is the world's epoch after every statement has
    # been compiled (== number of mutations encountered).
    # ``effect_sequence`` lists each effect (mutate / raise / ...)
    # in source order — the world path from start to end.
    final_epoch: int = 0
    effect_sequence: list[tuple[int, str, str]] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return self.proof_term is not None and not self.errors


# ─────────────────────────────────────────────────────────────────────
#  Compiler — Python AST → ProofTerm + Lean tactic
# ─────────────────────────────────────────────────────────────────────

class _Compiler:
    def __init__(self, foundations: dict, ctx: Context):
        self.foundations = foundations or {}
        self.ctx = ctx
        self.errors: list[PSDLError] = []
        self.hints: list[str] = []
        self.show_goal_requested = False
        self.foundations_referenced: list[str] = []
        self.lean_lines: list[str] = []   # accumulated Lean tactic lines
        # Track whether the runtime-semantics lint pass has already
        # run for this compilation — we want to lint exactly once
        # per top-level block, not per recursive call.
        self._linted = False
        # Cubical heap + effect model.  Each statement may bump
        # ``self._world.epoch`` (a mutation); each pure expression
        # emits ``Refl`` on the current world.  Aliases are recorded
        # on assignment ``b = a``; mutations through any aliased
        # name invalidate proofs at the old epoch — re-using them
        # at a later epoch requires ``TransportProof`` along the
        # mutation path.
        from deppy.proofs.psdl_heap import (
            World, EffectSequence, looks_mutating, MUTATING_METHODS,
        )
        from deppy.proofs.psdl_generators import (
            GeneratorRegistry, emit_yield_witness, emit_advance_witness,
        )
        from deppy.proofs.psdl_async import (
            CoroutineRegistry, emit_await_witness, emit_resume_witness,
        )
        from deppy.proofs.psdl_descriptors import (
            DescriptorRegistry, emit_descriptor_fiber,
            emit_descriptor_set_patch,
        )
        from deppy.proofs.psdl_mro import (
            MROTable, emit_mro_dispatch_path, emit_mro_cocycle,
            emit_super_path,
        )
        from deppy.proofs.psdl_op_dispatch import (
            OperatorRegistry, emit_op_dispatch, emit_inplace_op_dispatch,
        )
        self._world = World()
        self._effects = EffectSequence()
        self._looks_mutating = looks_mutating
        self._MUTATING_METHODS = MUTATING_METHODS
        # Generator coalgebra: tracks every generator referenced
        # in the block.  ``yield`` inside a function body adds a
        # yield point; ``next(g)`` / ``g.send(v)`` advance.
        self._generators = GeneratorRegistry()
        self._emit_yield = emit_yield_witness
        self._emit_advance = emit_advance_witness
        # Async coroutine coalgebra: ``await`` adds suspension
        # points indexed by event identifiers; resumption is
        # transport along event paths.
        self._coroutines = CoroutineRegistry()
        self._emit_await = emit_await_witness
        self._emit_resume = emit_resume_witness
        # Descriptor protocol: per-class table of __get__/__set__
        # /__delete__ declarations.  ``obj.attr`` lookup emits a
        # Fiber over the four resolution paths.
        self._descriptors = DescriptorRegistry()
        self._emit_descriptor_fiber = emit_descriptor_fiber
        self._emit_descriptor_set_patch = emit_descriptor_set_patch
        # MRO table: inheritance graph + lazy C3 linearization.
        # Method-call dispatch through ``Cls.method`` walks the
        # linearization as a DuckPath; conflicts emit Cocycle.
        self._mro = MROTable()
        self._emit_mro_path = emit_mro_dispatch_path
        self._emit_mro_cocycle = emit_mro_cocycle
        self._emit_super = emit_super_path
        # Operator dispatch: forward/reverse dunder fallback.
        # Binary ops emit ConditionalDuckPath; subclass-priority
        # exception emits an outer Fiber.
        self._op_registry = OperatorRegistry()
        self._emit_op_dispatch = emit_op_dispatch
        self._emit_inplace_op_dispatch = emit_inplace_op_dispatch
        # Generator-fn context for nested defs.
        self._current_genfn: Optional[str] = None

    # ── Top-level entry ────────────────────────────────────────
    def compile_block(
        self, stmts: list[ast.stmt], indent: int = 0,
    ) -> ProofTerm:
        """Compile a list of Python statements into a single ProofTerm.

        Multiple statements are chained via Cut.  The last statement's
        proof is the body; earlier ones become local lemmas.
        """
        if not self._linted:
            self._linted = True
            self._lint_runtime_semantics(stmts)
        if not stmts:
            return Structural("empty proof block")
        if len(stmts) == 1:
            return self._compile_stmt(stmts[0], indent)
        # Chain: first stmt is a Cut; rest is the body.
        head, *rest = stmts
        head_term = self._compile_stmt(head, indent)
        rest_term = self.compile_block(rest, indent)
        # Don't double-wrap if head is purely structural noise.
        if isinstance(head_term, Structural) and head_term.description in (
            "show_goal", "show_term", "trivial", "pure",
        ):
            return rest_term
        return Cut(
            hyp_name=f"_psdl_step_{getattr(head, 'lineno', 0)}",
            hyp_type=PyObjType(),
            lemma_proof=head_term,
            body_proof=rest_term,
        )

    # ── Runtime-semantics lint pass ────────────────────────────
    def _lint_runtime_semantics(self, stmts: list[ast.stmt]) -> None:
        """Walk the AST and flag Python runtime-semantics patterns
        that PSDL doesn't model correctly.

        Each warning is registered in ``self.errors`` so callers
        cannot get a clean ``ok=True`` result while the proof body
        actually depends on Python behaviour PSDL ignores.

        Patterns flagged:

        1. **Late closure binding** in comprehensions/lambdas:
           ``[lambda: i for i in xs]`` returns N copies of the same
           lambda whose ``i`` is the *final* iteration value.  PSDL
           treats each lambda as binding its own ``i`` — soundness
           gap.

        2. **Mutable default arguments**: ``def f(x=[])`` — the
           default ``[]`` is created ONCE and persists across calls.
           PSDL's :class:`Cut` for the def doesn't model this.

        3. **Iterator exhaustion**: ``for x in <generator/zip/map/
           filter call>`` — the iterable is consumed; re-iterating
           gives empty.  PSDL's :class:`ListInduction` claims the
           body holds for every element, which is false the second
           time.

        4. **`is` vs `==` confusion**: ``x is 5`` / ``x is "hello"`` —
           CPython interning makes these *sometimes* True for small
           integers/short strings, *unspecified* for larger.  PSDL
           treats ``is`` and ``==`` interchangeably.

        5. **Truthiness on falsy literals**: ``if []:`` / ``if 0:``
           / ``if None:`` are always False, but PSDL's ``_compile_if``
           runs the body anyway.

        6. **Number tower divergence**: ``int / int`` returns
           ``float`` in Python 3 (true division), not ``int`` like
           PSDL's flat-Int mechanization assumes.  ``//`` is the
           integer-division Python operator that matches PSDL's
           model.

        7. **Mutation through alias**: ``a = b; a.append(x)`` (or
           any assignment-then-mutation pattern) leaves ``b``
           changed too.  PSDL's :class:`Cut` chain treats values as
           immutable; aliases break that assumption.
        """
        module = ast.Module(body=list(stmts), type_ignores=[])

        def _warn(node: ast.AST, msg: str) -> None:
            self.errors.append(PSDLError(
                line_no=getattr(node, "lineno", 0),
                line_text=ast.unparse(node) if isinstance(node, ast.AST) else str(node),
                message=f"runtime-semantics lint: {msg}",
            ))

        # ── 1. Late closure binding in comprehensions/lambdas ──
        for node in ast.walk(module):
            if isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
                bound_names: set[str] = set()
                for gen in node.generators:
                    if isinstance(gen.target, ast.Name):
                        bound_names.add(gen.target.id)
                # If the element expression contains a Lambda whose
                # body references a bound name, this is the late-
                # binding trap.  ``DictComp`` has no ``elt`` — it
                # has ``key`` and ``value``; treat both.
                if isinstance(node, ast.DictComp):
                    elt_nodes: list[ast.expr] = [node.key, node.value]
                else:
                    elt_nodes = [node.elt]
                triggered = False
                for elt in elt_nodes:
                    if triggered:
                        break
                    for sub in ast.walk(elt):
                        if isinstance(sub, ast.Lambda):
                            for ref in ast.walk(sub.body):
                                if (
                                    isinstance(ref, ast.Name)
                                    and ref.id in bound_names
                                ):
                                    _warn(
                                        node,
                                        f"late closure binding — lambda "
                                        f"references comprehension "
                                        f"variable ``{ref.id}`` which "
                                        f"is shared across iterations",
                                    )
                                    triggered = True
                                    break
                            if triggered:
                                break

        # ── 2. Mutable default arguments ──
        for node in ast.walk(module):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                for default in node.args.defaults:
                    if isinstance(default, (ast.List, ast.Dict, ast.Set)):
                        _warn(
                            default,
                            f"mutable default arg in ``{node.name}`` "
                            f"— Python evaluates this once at def "
                            f"time; PSDL doesn't model the shared state",
                        )
                    elif (
                        isinstance(default, ast.Call)
                        and isinstance(default.func, ast.Name)
                        and default.func.id in {"list", "dict", "set"}
                    ):
                        _warn(
                            default,
                            f"mutable default arg in ``{node.name}`` "
                            f"(via ``{default.func.id}()`` call) — "
                            f"shared across calls",
                        )

        # ── 3. Iterator exhaustion: for x in <one-shot iterable> ──
        ONE_SHOT = {"zip", "map", "filter", "enumerate", "reversed", "iter"}
        for node in ast.walk(module):
            if isinstance(node, (ast.For, ast.AsyncFor)):
                it = node.iter
                # Direct call to a one-shot builtin.
                if (
                    isinstance(it, ast.Call)
                    and isinstance(it.func, ast.Name)
                    and it.func.id in ONE_SHOT
                ):
                    _warn(
                        it,
                        f"``for x in {it.func.id}(...)`` — Python's "
                        f"``{it.func.id}`` returns a one-shot iterator; "
                        f"PSDL's ListInduction assumes a re-iterable list",
                    )
                # Generator expression inline: ``for x in (e for ...)``.
                if isinstance(it, ast.GeneratorExp):
                    _warn(
                        it,
                        "``for x in <generator expression>`` — "
                        "iterator is consumed; re-iteration yields "
                        "empty.  PSDL's ListInduction proves the body "
                        "holds for every element on every iteration",
                    )

        # ── 4. ``is`` vs ``==`` on literal numbers/strings ──
        for node in ast.walk(module):
            if isinstance(node, ast.Compare):
                for op, cmp_v in zip(node.ops, node.comparators):
                    if isinstance(op, (ast.Is, ast.IsNot)) and isinstance(
                        cmp_v, ast.Constant,
                    ) and isinstance(cmp_v.value, (int, str, float)):
                        _warn(
                            node,
                            f"``is``/``is not`` against a literal "
                            f"({type(cmp_v.value).__name__}) — CPython "
                            f"interning quirk; use ``==`` for value "
                            f"equality",
                        )

        # ── 5. Truthiness on falsy literals ──
        for node in ast.walk(module):
            if isinstance(node, (ast.If, ast.IfExp)):
                t = node.test
                if isinstance(t, ast.Constant):
                    if t.value in (0, "", None) or t.value is False:
                        _warn(
                            t,
                            f"``if {t.value!r}:`` always False — body "
                            f"never runs at runtime; PSDL still emits "
                            f"the proof for the body branch",
                        )
                if isinstance(t, (ast.List, ast.Dict, ast.Set)) and not (
                    getattr(t, "elts", None) or getattr(t, "keys", None)
                ):
                    _warn(
                        t,
                        f"``if <empty literal>:`` always False — body "
                        f"never runs at runtime",
                    )

        # ── 6. Number tower: int / int returns float in Py3 ──
        for node in ast.walk(module):
            if (
                isinstance(node, ast.BinOp)
                and isinstance(node.op, ast.Div)
            ):
                _warn(
                    node,
                    "``a / b`` is float division in Python 3 — PSDL's "
                    "Int-only mechanization treats this as integer "
                    "division.  Use ``//`` for explicit floor division",
                )

        # ── 7. Mutation-through-alias hazard, via the cubical heap ──
        # Detect: a name that's been aliased *and* later read after
        # a mutation through any of its aliases.  Unlike the previous
        # heuristic that fired on *any* mutation through an aliased
        # name, this version simulates the heap forward: each Assign
        # of ``b = a`` aliases the cell, each mutator-call on the
        # cell bumps the epoch.  A *read* (Name reference) at a later
        # epoch than the alias was established triggers the warning
        # only when intervening mutations actually broke the cell's
        # state — i.e. when ``World.transport_required`` reports a
        # non-empty bridging set.
        from deppy.proofs.psdl_heap import World as _W
        sim = _W()
        # Pre-bind every Name appearing on a Name = Name LHS so the
        # simulator has cells for them.
        for node in stmts:
            if (
                isinstance(node, ast.Assign)
                and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name)
                and isinstance(node.value, ast.Name)
            ):
                src = node.value.id
                dst = node.targets[0].id
                if src not in sim.name_to_cell:
                    sim.bind(src, sim.alloc())
                sim.alias(dst, src)
        # Walk in source order; for each step, simulate.
        alias_groups: dict[str, set[str]] = {}
        for node in stmts:
            if (
                isinstance(node, ast.Assign)
                and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name)
                and isinstance(node.value, ast.Name)
            ):
                src = node.value.id
                dst = node.targets[0].id
                grp = alias_groups.setdefault(src, {src})
                grp.add(dst)
                alias_groups[dst] = grp
                continue
            # Mutation calls bump the epoch.
            for sub in ast.walk(node):
                if (
                    isinstance(sub, ast.Call)
                    and isinstance(sub.func, ast.Attribute)
                    and isinstance(sub.func.value, ast.Name)
                ):
                    recv = sub.func.value.id
                    method = sub.func.attr
                    if recv in sim.name_to_cell and method in {
                        "append", "extend", "pop", "remove", "clear",
                        "insert", "sort", "reverse", "update", "add",
                        "discard", "popitem", "setdefault",
                    }:
                        affected = sim.mutate(
                            recv, line=getattr(sub, "lineno", 0),
                        )
                        # Only warn when the mutation crosses an
                        # alias group (i.e. there's at least one
                        # OTHER name pointing at the same cell).
                        if len(affected) > 1:
                            _warn(
                                sub,
                                f"mutation ``{recv}.{method}(...)`` "
                                f"crosses alias group {sorted(affected)} — "
                                f"the cubical heap path between epochs "
                                f"{sim.epoch - 1} → {sim.epoch} requires "
                                f"``TransportProof`` to use any prior "
                                f"invariant on these names",
                            )

    # ── Statement dispatcher ───────────────────────────────────
    def _compile_stmt(self, stmt: ast.stmt, indent: int) -> ProofTerm:
        if isinstance(stmt, ast.If):
            return self._compile_if(stmt, indent)
        if isinstance(stmt, ast.Try):
            return self._compile_try(stmt, indent)
        if isinstance(stmt, ast.For):
            return self._compile_for(stmt, indent)
        if isinstance(stmt, ast.While):
            return self._compile_while(stmt, indent)
        if isinstance(stmt, ast.Match):
            return self._compile_match(stmt, indent)
        if isinstance(stmt, ast.Assert):
            return self._compile_assert(stmt, indent)
        if isinstance(stmt, ast.Return):
            return self._compile_return(stmt, indent)
        if isinstance(stmt, ast.Raise):
            return self._compile_raise(stmt, indent)
        if isinstance(stmt, ast.AnnAssign):
            return self._compile_ann_assign(stmt, indent)
        if isinstance(stmt, ast.Assign):
            return self._compile_assign(stmt, indent)
        if isinstance(stmt, ast.Expr):
            return self._compile_expr_stmt(stmt, indent)
        if isinstance(stmt, ast.AugAssign):
            return self._compile_aug_assign(stmt, indent)
        if isinstance(stmt, ast.Pass):
            self._emit_lean(indent, "trivial")
            return Structural("trivial")
        if isinstance(stmt, ast.Break):
            # ``break`` exits the enclosing loop early.  The
            # surrounding ``ListInduction`` / ``NatInduction``
            # constructed by ``_compile_for`` / ``_compile_while``
            # implicitly assumes the body runs for every element /
            # every n until termination — that's no longer true.
            # Record an explicit non-totality marker so the kernel
            # can refuse to verify the induction shape.  We also
            # log an error so the verify pipeline reports it.
            self.errors.append(PSDLError(
                line_no=getattr(stmt, "lineno", 0),
                line_text="break",
                message=(
                    "PSDL ``break`` invalidates the surrounding "
                    "ListInduction/NatInduction shape — induction "
                    "assumes the body runs for every iteration"
                ),
            ))
            self._emit_lean(indent, "-- break (loop exit; non-total)")
            return Structural("break: non-total loop exit")
        if isinstance(stmt, ast.Continue):
            # ``continue`` skips to the next iteration.  The
            # induction shape can still hold (each iteration's
            # body is "this body OR a no-op for the skipped
            # cases"), but the per-iteration content the user
            # supplied is *partial*.  Record a structural note.
            self.errors.append(PSDLError(
                line_no=getattr(stmt, "lineno", 0),
                line_text="continue",
                message=(
                    "PSDL ``continue`` produces a partial body — "
                    "the induction step proof must hold for both "
                    "the executed and skipped branches"
                ),
            ))
            self._emit_lean(indent, "-- continue (skip iteration)")
            return Structural("continue: partial body")
        if isinstance(stmt, ast.With):
            return self._compile_with(stmt, indent)
        if isinstance(stmt, ast.ImportFrom):
            # ``from foundations import F1, F2`` — no-op, just records.
            for alias in stmt.names:
                self.foundations_referenced.append(alias.name)
            self._emit_lean(indent, f"-- import {ast.unparse(stmt)}")
            return Structural(f"import {[a.name for a in stmt.names]}")
        # CIC core: top-level user declarations recognised by decorator.
        if isinstance(stmt, ast.ClassDef):
            return self._compile_class_def(stmt, indent)
        if isinstance(stmt, ast.FunctionDef):
            return self._compile_function_def(stmt, indent)
        if isinstance(stmt, ast.AsyncFunctionDef):
            # Treat ``async def`` like ``def`` for the body, but
            # register it in the coroutine registry so awaits
            # inside the body get tagged.
            self._coroutines.declare(
                stmt.name, line=getattr(stmt, "lineno", 0),
            )
            prev = getattr(self, "_current_genfn", None)
            self._current_genfn = stmt.name
            self._emit_lean(
                indent,
                f"-- async def {stmt.name}: awaits tracked as ◇-effects",
            )
            try:
                return self.compile_block(stmt.body, indent + 1)
            finally:
                self._current_genfn = prev
        # Anything else: emit a sorry placeholder.
        self.errors.append(PSDLError(
            line_no=getattr(stmt, "lineno", 0),
            line_text=ast.unparse(stmt),
            message=f"unsupported PSDL statement: {type(stmt).__name__}",
        ))
        self._emit_lean(indent, "sorry")
        return Structural(f"unsupported {type(stmt).__name__}")

    # ── @inductive class T:  /  @axiom def X / @theorem def L ──
    def _compile_class_def(self, stmt: ast.ClassDef, indent: int) -> ProofTerm:
        """``@inductive class T: ctor: ...`` introduces a user
        inductive type; ``@protocol class P: method(args) -> T``
        introduces a protocol used by ``dispatch``."""
        decorators = {self._dec_name(d) for d in stmt.decorator_list}
        if "inductive" in decorators:
            self._emit_lean(indent, f"-- inductive {stmt.name}:")
            self._emit_lean(indent, f"inductive {_safe(stmt.name)} where")
            ctor_count = 0
            for member in stmt.body:
                if isinstance(member, ast.AnnAssign) and isinstance(
                    member.target, ast.Name,
                ):
                    cname = member.target.id
                    cty = ast.unparse(member.annotation)
                    self._emit_lean(
                        indent + 1, f"| {_safe(cname)} : {cty}",
                    )
                    ctor_count += 1
                elif isinstance(member, ast.FunctionDef):
                    cname = member.name
                    args = [a.arg for a in member.args.args]
                    arg_str = " → ".join(["..."] * len(args))
                    self._emit_lean(
                        indent + 1,
                        f"| {_safe(cname)} : {arg_str}{' → ' if args else ''}{_safe(stmt.name)}",
                    )
                    ctor_count += 1
            return Structural(
                f"inductive {stmt.name} ({ctor_count} ctors)"
            )
        if "protocol" in decorators:
            self._emit_lean(indent, f"-- protocol {stmt.name}:")
            methods = []
            for member in stmt.body:
                if isinstance(member, ast.FunctionDef):
                    methods.append(member.name)
            self._emit_lean(
                indent,
                f"-- protocol methods: {', '.join(methods)}",
            )
            return Structural(
                f"protocol {stmt.name} (methods: {methods})"
            )
        # Plain class body: treat as a sigma-type record.
        self._emit_lean(indent, f"-- record {stmt.name}:")
        self._emit_lean(indent, f"structure {_safe(stmt.name)} where")
        for member in stmt.body:
            if isinstance(member, ast.AnnAssign) and isinstance(
                member.target, ast.Name,
            ):
                self._emit_lean(
                    indent + 1,
                    f"{member.target.id} : {ast.unparse(member.annotation)}",
                )
        return Structural(f"record {stmt.name}")

    def _compile_function_def(self, stmt: ast.FunctionDef, indent: int) -> ProofTerm:
        """``@axiom def X() -> T: ...`` declares an axiom in the
        local PSDL context.  ``@theorem def L() -> T: <body>``
        compiles the body as a PSDL proof and exposes the result
        as a citable lemma.

        When the function body contains ``yield`` / ``yield from``,
        we treat it as a *generator* and record the function name
        in ``self._current_genfn`` so each yield in the body adds
        a yield-point to that generator's coalgebra entry.
        """
        # Detect generator-ness by walking the body for Yield nodes
        # (don't descend into nested defs).
        is_genfn = False
        stack = list(stmt.body)
        while stack:
            n = stack.pop()
            if isinstance(n, (ast.Yield, ast.YieldFrom)):
                is_genfn = True
                break
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)):
                continue  # don't descend
            for c in ast.iter_child_nodes(n):
                stack.append(c)
        prev_genfn = getattr(self, "_current_genfn", None)
        if is_genfn:
            self._generators.declare(
                stmt.name, line=getattr(stmt, "lineno", 0),
            )
            self._current_genfn = stmt.name
            self._emit_lean(
                indent,
                f"-- generator def {stmt.name}: yields tracked as ◇-effects",
            )
        decorators = {self._dec_name(d) for d in stmt.decorator_list}
        ret_ty = (
            ast.unparse(stmt.returns) if stmt.returns is not None else "Prop"
        )
        try:
            if "axiom" in decorators:
                self._emit_lean(
                    indent,
                    f"axiom {_safe(stmt.name)} : {ret_ty}",
                )
                self.foundations_referenced.append(stmt.name)
                return AxiomInvocation(
                    name=stmt.name, module="psdl_local",
                )
            if "theorem" in decorators:
                self._emit_lean(
                    indent, f"-- theorem {stmt.name}: {ret_ty}",
                )
                self._emit_lean(
                    indent,
                    f"theorem {_safe(stmt.name)} : {ret_ty} := by",
                )
                inner = self.compile_block(stmt.body, indent + 1)
                return Cut(
                    hyp_name=stmt.name,
                    hyp_type=RefinementType(
                        base_type=PyBoolType(), predicate=ret_ty,
                    ),
                    lemma_proof=inner,
                    body_proof=Refl(Var(f"_thm_{_safe(stmt.name)}")),
                )
            # Generic function.
            self._emit_lean(indent, f"-- def {stmt.name}: {ret_ty}")
            return self.compile_block(stmt.body, indent + 1)
        finally:
            # Restore previous generator-fn context (so nested gens
            # don't pollute the outer's yields).
            self._current_genfn = prev_genfn

    @staticmethod
    def _dec_name(d: ast.expr) -> str:
        if isinstance(d, ast.Name):
            return d.id
        if isinstance(d, ast.Attribute):
            return d.attr
        if isinstance(d, ast.Call) and isinstance(d.func, ast.Name):
            return d.func.id
        try:
            return ast.unparse(d)
        except Exception:
            return ""

    # ── Helpers ────────────────────────────────────────────────
    def _emit_lean(self, indent: int, text: str) -> None:
        spaces = "  " * indent
        for ln in text.splitlines():
            self.lean_lines.append(f"{spaces}{ln}")

    def _is_isinstance_test(
        self, node: ast.expr,
    ) -> Optional[tuple[str, str]]:
        """Return (var, type-name) when node is ``isinstance(var, T)``."""
        if not isinstance(node, ast.Call):
            return None
        f = node.func
        if not (isinstance(f, ast.Name) and f.id == "isinstance"):
            return None
        if len(node.args) != 2:
            return None
        var_node, ty_node = node.args
        var_name = var_node.id if isinstance(var_node, ast.Name) else ast.unparse(var_node)
        ty_name = ty_node.id if isinstance(ty_node, ast.Name) else ast.unparse(ty_node)
        return var_name, ty_name

    # ── with goal(...) / with case(...) / with hypothesis(...) ──
    def _compile_with(self, stmt: ast.With, indent: int) -> ProofTerm:
        """``with`` blocks scope a sub-proof.

        Three recognised heads (other heads pass through):
          * ``with goal(P):`` — ``show P; <body>`` in Lean
          * ``with case(label):`` — focus a Cases / Fiber arm
          * ``with hypothesis(h: T):`` — introduce a hypothesis
        """
        if not stmt.items:
            return self.compile_block(stmt.body, indent + 1)
        item = stmt.items[0]
        ctx = item.context_expr
        if isinstance(ctx, ast.Call) and isinstance(ctx.func, ast.Name):
            head = ctx.func.id
            if head == "goal":
                goal_text = ""
                if ctx.args:
                    if isinstance(ctx.args[0], ast.Constant):
                        goal_text = str(ctx.args[0].value)
                    else:
                        goal_text = ast.unparse(ctx.args[0])
                if goal_text:
                    self._emit_lean(indent, f"show {goal_text}")
                inner = self.compile_block(stmt.body, indent + 1)
                return inner
            if head == "case":
                label = ""
                if ctx.args:
                    if isinstance(ctx.args[0], ast.Constant):
                        label = str(ctx.args[0].value)
                    else:
                        label = ast.unparse(ctx.args[0])
                self._emit_lean(indent, f"case {_safe(label)} =>")
                inner = self.compile_block(stmt.body, indent + 1)
                return inner
            if head == "hypothesis":
                # ``with hypothesis(h="p > 0", T="Prop"):``
                hname = "h"
                htype = "Prop"
                for kw in ctx.keywords:
                    if kw.arg == "h" and isinstance(kw.value, ast.Constant):
                        hname = str(kw.value.value)
                    if kw.arg == "T" and isinstance(kw.value, ast.Constant):
                        htype = str(kw.value.value)
                self._emit_lean(
                    indent, f"intro ({hname} : {htype})",
                )
                inner = self.compile_block(stmt.body, indent + 1)
                return Cut(
                    hyp_name=hname,
                    hyp_type=RefinementType(
                        base_type=PyBoolType(), predicate=htype,
                    ),
                    lemma_proof=Assume(name=hname),
                    body_proof=inner,
                )
        # Default: pass through.
        self._emit_lean(indent, f"-- with {ast.unparse(ctx)}:")
        return self.compile_block(stmt.body, indent + 1)

    # ── if / isinstance → Fiber ────────────────────────────────
    def _compile_if(self, stmt: ast.If, indent: int) -> ProofTerm:
        ii = self._is_isinstance_test(stmt.test)
        if ii is None:
            # Generic if: treat as Cases on the test expression.
            test_text = ast.unparse(stmt.test)
            self._emit_lean(indent, f"by_cases h : {test_text}")
            self._emit_lean(indent, "· -- then branch")
            then_proof = self.compile_block(stmt.body, indent + 1)
            self._emit_lean(indent, "· -- else branch")
            else_proof = (
                self.compile_block(stmt.orelse, indent + 1)
                if stmt.orelse else Structural("no else branch")
            )
            return Cases(
                scrutinee=Var(test_text),
                branches=[("then", then_proof), ("else", else_proof)],
            )
        var, ty = ii
        self._emit_lean(indent, f"by_cases h : isinstance {var} {ty}")
        self._emit_lean(indent, f"· -- value-fibre: isinstance({var}, {ty})")
        then_proof = self.compile_block(stmt.body, indent + 1)
        self._emit_lean(indent, f"· -- complement-fibre: ¬ isinstance({var}, {ty})")
        else_proof = (
            self.compile_block(stmt.orelse, indent + 1)
            if stmt.orelse else Structural(f"no else for isinstance({var}, {ty})")
        )
        return Fiber(
            scrutinee=Var(var),
            type_branches=[
                (PyObjType(), then_proof),
                (PyObjType(), else_proof),
            ],
            exhaustive=bool(stmt.orelse),
        )

    # ── try / except → EffectWitness + ConditionalEffectWitness ─
    def _compile_try(self, stmt: ast.Try, indent: int) -> ProofTerm:
        """Translate ``try / except / else / finally`` into a chain
        of effect modalities.

        Shape:

          * The try body yields ``EffectWitness(effect="value")``.
          * Each ``except`` clause becomes a
            ``ConditionalEffectWitness(precondition=raises E, ...)``.
          * The ``else:`` clause (runs only if no exception)
            chains via ``Cut`` after the value witness — its proof
            depends on the value-fibre completing normally.
          * The ``finally:`` clause runs unconditionally and is
            chained at the OUTSIDE so its proof is required for
            both the value-fibre and exception-fibre paths.

        Previously ``finalbody`` and ``orelse`` were silently
        ignored; cleanup obligations were invisible to the kernel.
        """
        self._emit_lean(indent, "-- try block (effect modality)")
        value_proof = self.compile_block(stmt.body, indent + 1)
        handler_proofs: list[tuple[str, str, ProofTerm]] = []
        for h in stmt.handlers:
            exc_name = (
                ast.unparse(h.type) if h.type else "Exception"
            )
            # ``except E as e:`` binding — record the alias as a
            # local name in the handler.  When ``h.name`` is None
            # there's no binding.
            alias = h.name or ""
            self._emit_lean(
                indent,
                f"-- except {exc_name}"
                + (f" as {alias}" if alias else ""),
            )
            hp = self.compile_block(h.body, indent + 1)
            if alias:
                hp = Cut(
                    hyp_name=alias,
                    hyp_type=PyObjType(),
                    lemma_proof=Refl(Var(f"_exc_{_safe(exc_name)}")),
                    body_proof=hp,
                )
            handler_proofs.append((exc_name, alias, hp))
        # Else clause: runs after the value-fibre completes.
        else_proof: ProofTerm | None = None
        if stmt.orelse:
            self._emit_lean(
                indent, "-- try/else (runs after no-exception path)",
            )
            else_proof = self.compile_block(stmt.orelse, indent + 1)
        # Finally clause: runs unconditionally, chained at outside.
        finally_proof: ProofTerm | None = None
        if stmt.finalbody:
            self._emit_lean(
                indent, "-- try/finally (always runs)",
            )
            finally_proof = self.compile_block(
                stmt.finalbody, indent + 1,
            )
        # Build the chain.
        result: ProofTerm = EffectWitness(
            effect="value", proof=value_proof,
        )
        if else_proof is not None:
            result = Cut(
                hyp_name="_try_else",
                hyp_type=PyObjType(),
                lemma_proof=result,
                body_proof=else_proof,
            )
        for exc_name, alias, hp in handler_proofs:
            cew = ConditionalEffectWitness(
                precondition=f"raises {exc_name}",
                effect="exception_handled",
                proof=hp,
                target=exc_name,
            )
            result = Cut(
                hyp_name=f"_handler_{_safe(exc_name)}",
                hyp_type=PyObjType(),
                lemma_proof=cew,
                body_proof=result,
            )
        if finally_proof is not None:
            result = Cut(
                hyp_name="_try_finally",
                hyp_type=PyObjType(),
                lemma_proof=finally_proof,
                body_proof=result,
            )
        return result

    # ── for x in xs → ListInduction ────────────────────────────
    def _compile_for(self, stmt: ast.For, indent: int) -> ProofTerm:
        var = (
            stmt.target.id if isinstance(stmt.target, ast.Name) else "x"
        )
        iter_text = ast.unparse(stmt.iter)
        # Refuse to build a full ListInduction when the body
        # contains ``break``: the induction's "for every element"
        # promise is broken.  A ``continue`` is more nuanced (the
        # step proof must cover the skipped branch) — we still
        # build the induction but flag it for partial coverage.
        has_break = any(
            isinstance(n, ast.Break) for n in ast.walk(ast.Module(body=stmt.body, type_ignores=[]))
        )
        if has_break:
            self.errors.append(PSDLError(
                line_no=getattr(stmt, "lineno", 0),
                line_text=f"for {var} in {iter_text}: ... break",
                message=(
                    "PSDL ``for ... break`` cannot construct a "
                    "ListInduction — induction requires the body "
                    "to run for every element"
                ),
            ))
            self._emit_lean(
                indent,
                f"-- for {var} in {iter_text}: contains break — "
                "induction shape rejected",
            )
            cons_proof = self.compile_block(stmt.body, indent + 1)
            return Structural(
                f"for {var} in {iter_text}: non-total (break)"
            )
        # ``for/else`` clause runs only if the loop completed without
        # break.  Capture and chain via Cut so the else-block is
        # part of the proof when the iteration completes.
        else_proof: ProofTerm | None = None
        if stmt.orelse:
            else_proof = self.compile_block(stmt.orelse, indent + 1)
            self._emit_lean(
                indent, "-- for/else (runs after no-break completion)",
            )
        self._emit_lean(
            indent,
            f"induction {iter_text} with",
        )
        # Look for # nil: ... marker in the comments around stmt.body.
        # Without comment introspection, default to Refl in nil case.
        nil_proof: ProofTerm = Refl(Var("_nil"))
        cons_proof = self.compile_block(stmt.body, indent + 1)
        self._emit_lean(indent + 1, "| nil => rfl")
        self._emit_lean(indent + 1, "| cons _ _ ih =>")
        induction = ListInduction(
            var=var, nil_proof=nil_proof, cons_proof=cons_proof,
        )
        if else_proof is not None:
            return Cut(
                hyp_name="_for_else",
                hyp_type=PyObjType(),
                lemma_proof=induction,
                body_proof=else_proof,
            )
        return induction

    # ── while → NatInduction ───────────────────────────────────
    def _compile_while(self, stmt: ast.While, indent: int) -> ProofTerm:
        """``while <cond>:`` becomes Nat-induction on the variable
        whose decrease drives termination.  We extract the
        induction variable from the loop condition: ``while n:`` →
        var ``n``; ``while n > 0:`` → ``n``; ``while not done(x):``
        → ``x``.  Falls back to ``"n"`` only when no Name appears.

        Refuses to construct the induction when the body contains
        ``break`` (induction's "for all n" promise is invalid) and
        threads the ``while/else`` body through a Cut.
        """
        var_name = "n"
        for node in ast.walk(stmt.test):
            if isinstance(node, ast.Name):
                var_name = node.id
                break
        cond_text = ast.unparse(stmt.test)
        has_break = any(
            isinstance(n, ast.Break)
            for n in ast.walk(
                ast.Module(body=stmt.body, type_ignores=[])
            )
        )
        if has_break:
            self.errors.append(PSDLError(
                line_no=getattr(stmt, "lineno", 0),
                line_text=f"while {cond_text}: ... break",
                message=(
                    "PSDL ``while ... break`` cannot construct a "
                    "NatInduction — induction requires the body "
                    "to run for every n down to the base case"
                ),
            ))
            self._emit_lean(
                indent,
                f"-- while {cond_text}: contains break — "
                "induction shape rejected",
            )
            self.compile_block(stmt.body, indent + 1)
            return Structural(
                f"while {cond_text}: non-total (break)"
            )
        else_proof: ProofTerm | None = None
        if stmt.orelse:
            else_proof = self.compile_block(stmt.orelse, indent + 1)
            self._emit_lean(
                indent, "-- while/else (runs after no-break completion)",
            )
        self._emit_lean(
            indent, f"-- while {cond_text} → induction on {var_name}",
        )
        body_proof = self.compile_block(stmt.body, indent + 1)
        induction = NatInduction(
            var=var_name,
            base_proof=Refl(Var(f"_zero_{var_name}")),
            step_proof=body_proof,
        )
        if else_proof is not None:
            return Cut(
                hyp_name="_while_else",
                hyp_type=PyObjType(),
                lemma_proof=induction,
                body_proof=else_proof,
            )
        return induction

    # ── match → Cases ──────────────────────────────────────────
    def _compile_match(self, stmt: ast.Match, indent: int) -> ProofTerm:
        """Translate ``match`` into ``Cases``.

        Honours ``case <pat> if <guard>:`` by wrapping the case body
        in a ``Cut(<guard>, ..., body)`` — the guard becomes a
        precondition the body proof depends on.  Without this, a
        guarded case would be admitted as if unguarded, which would
        let the kernel verify a Cases proof for an arm that only
        applies under a stronger condition.
        """
        scrutinee = ast.unparse(stmt.subject)
        self._emit_lean(indent, f"match {scrutinee} with")
        branches = []
        for case in stmt.cases:
            pat = ast.unparse(case.pattern)
            guard_text = ast.unparse(case.guard) if case.guard is not None else ""
            label = (
                f"{pat} if {guard_text}" if guard_text else pat
            )
            self._emit_lean(
                indent + 1,
                f"| {pat}{f' if {guard_text}' if guard_text else ''} =>",
            )
            cp = self.compile_block(case.body, indent + 2)
            if guard_text:
                # Wrap the body with a Cut expressing the guard
                # precondition: the case proof requires the guard
                # to hold.  ``Z3Proof`` discharges arithmetic
                # guards; non-arithmetic guards become structural.
                cp = Cut(
                    hyp_name=f"_guard_{getattr(case, 'lineno', 0)}",
                    hyp_type=RefinementType(
                        base_type=PyBoolType(),
                        predicate=guard_text,
                    ),
                    lemma_proof=Z3Proof(
                        formula=guard_text, binders={},
                    ),
                    body_proof=cp,
                )
            branches.append((label, cp))
        return Cases(scrutinee=Var(scrutinee), branches=branches)

    # ── assert → Cut + (Z3 / foundation / lemma) ──────────────
    def _compile_assert(self, stmt: ast.Assert, indent: int) -> ProofTerm:
        # Determine the discharge mode from the optional msg arg.
        # Pythonic sugar: ``assert P, "qed"`` / ``"auto"`` / ``"omega"``
        # / ``"rfl"`` / ``"trivial"`` / ``"decide"`` / ``"simp"`` use
        # the corresponding Lean closer, mirroring the closer-sugar
        # in :meth:`_compile_func_call`.  Anything else becomes a
        # foundation citation.  Bare ``assert P`` defaults to z3.
        mode = "z3"
        cite = ""
        if stmt.msg is not None:
            if isinstance(stmt.msg, ast.Constant) and isinstance(
                stmt.msg.value, str,
            ):
                tag = stmt.msg.value.strip()
                if tag == "z3":
                    mode = "z3"
                elif tag in {
                    "qed", "auto", "done", "omega", "rfl",
                    "trivial", "decide", "simp",
                }:
                    mode = "closer"
                    cite = tag
                elif tag.startswith("by "):
                    rest = tag[3:].strip()
                    if rest.startswith("lemma "):
                        mode = "lemma"
                        cite = rest[len("lemma "):].strip()
                    else:
                        mode = "foundation"
                        cite = rest
                else:
                    mode = "z3"
                    cite = tag
        claim = ast.unparse(stmt.test)
        if mode == "z3":
            self._emit_lean(
                indent,
                f"have h_{stmt.lineno} : {claim} := by omega "
                f"-- z3-discharged",
            )
            return Cut(
                hyp_name=f"h_{stmt.lineno}",
                hyp_type=RefinementType(
                    base_type=PyBoolType(), predicate=claim,
                ),
                lemma_proof=Z3Proof(formula=claim, binders={}),
                body_proof=Refl(Var("_assert_body")),
            )
        if mode == "foundation":
            if cite in self.foundations:
                self.foundations_referenced.append(cite)
            self._emit_lean(
                indent,
                f"have h_{stmt.lineno} : {claim} := "
                f"Foundation_{_safe(cite)}",
            )
            return Cut(
                hyp_name=f"h_{stmt.lineno}",
                hyp_type=RefinementType(
                    base_type=PyBoolType(), predicate=claim,
                ),
                lemma_proof=AxiomInvocation(
                    name=cite, module="foundations",
                ),
                body_proof=Refl(Var("_assert_body")),
            )
        if mode == "lemma":
            self._emit_lean(
                indent, f"have h_{stmt.lineno} : {claim} := {_safe(cite)}",
            )
            return Cut(
                hyp_name=f"h_{stmt.lineno}",
                hyp_type=RefinementType(
                    base_type=PyBoolType(), predicate=claim,
                ),
                lemma_proof=AxiomInvocation(name=cite, module=""),
                body_proof=Refl(Var("_assert_body")),
            )
        if mode == "closer":
            # ``assert P, "qed"`` etc. — discharge with the named
            # closer tactic; the kernel-side artefact is a Refl
            # placeholder, the trust signal lives in Lean.
            closer_text = {
                "qed": "first | rfl | omega | decide | trivial",
                "auto": "simp; first | rfl | omega | decide | trivial",
                "done": "trivial",
                "omega": "omega",
                "rfl": "rfl",
                "trivial": "trivial",
                "decide": "decide",
                "simp": "simp",
            }.get(cite, "trivial")
            self._emit_lean(
                indent,
                f"have h_{stmt.lineno} : {claim} := by {closer_text}",
            )
            return Cut(
                hyp_name=f"h_{stmt.lineno}",
                hyp_type=RefinementType(
                    base_type=PyBoolType(), predicate=claim,
                ),
                lemma_proof=Refl(Var(f"_closer_{cite}")),
                body_proof=Refl(Var("_assert_body")),
            )
        return Structural("unknown assert mode")

    # ── return → Refl ──────────────────────────────────────────
    def _compile_return(self, stmt: ast.Return, indent: int) -> ProofTerm:
        if stmt.value is None:
            self._emit_lean(indent, "rfl")
            return Refl(Var("_unit"))
        text = ast.unparse(stmt.value)
        self._emit_lean(indent, f"-- return {text}\n  rfl")
        return Refl(Var(_safe(text)))

    # ── raise → exception fibre / vacuous ──────────────────────
    def _compile_raise(self, stmt: ast.Raise, indent: int) -> ProofTerm:
        if stmt.exc is None:
            self._emit_lean(indent, "-- bare raise")
            return Structural("bare raise")
        exc_text = ast.unparse(stmt.exc)
        if "NotImplementedError" in exc_text:
            self._emit_lean(
                indent, f"-- vacuous: {exc_text}\n  exact absurd ‹_› (by simp)",
            )
            return Structural(f"vacuous: {exc_text}")
        self._emit_lean(indent, f"-- raise {exc_text} (exception fibre)")
        # The kernel's ``ConditionalEffectWitness`` proves an effect
        # is **absent** under a precondition (kernel.py:560-581) —
        # not present.  A ``raise`` statement is the dual: it
        # proves the exception effect is **present** on this branch.
        # Use ``EffectWitness(effect="exception", ...)`` instead;
        # the inner ``Structural`` records which exception is raised.
        return EffectWitness(
            effect=f"exception:{exc_text}",
            proof=Structural(f"raises {exc_text}"),
        )

    # ── annotated assign → typed local lemma (Cut) ────────────
    def _compile_ann_assign(self, stmt: ast.AnnAssign, indent: int) -> ProofTerm:
        if not isinstance(stmt.target, ast.Name):
            return Structural("non-name annotated target")
        h = stmt.target.id
        ty = ast.unparse(stmt.annotation)
        if stmt.value is None:
            self._emit_lean(indent, f"-- decl {h} : {ty}")
            return Structural(f"decl {h} : {ty}")
        rhs = ast.unparse(stmt.value)
        self._emit_lean(indent, f"have {h} : {ty} := {rhs}")
        # Try to compile rhs as a known tactic-call.
        inner = self._compile_expr(stmt.value, indent)
        return Cut(
            hyp_name=h,
            hyp_type=RefinementType(
                base_type=PyBoolType(), predicate=ty,
            ),
            lemma_proof=inner,
            body_proof=Refl(Var("_ann_body")),
        )

    # ── augmented assign ``h += rhs`` etc. — re-bind ──────────
    def _compile_aug_assign(self, stmt: ast.AugAssign, indent: int) -> ProofTerm:
        """``h += rhs`` rebinds ``h`` to ``h + rhs``.

        We translate this as ``h = h <op> rhs`` — a fresh Cut that
        shadows the previous binding of ``h``.  The shadowing is
        what Python actually does (numeric ``+=`` doesn't mutate
        in place for immutable values).  For mutable LHS (lists,
        sets), this loses the in-place mutation semantics — see
        the runtime-semantics audit.
        """
        if not isinstance(stmt.target, ast.Name):
            return Structural("non-name aug-assign target")
        h = stmt.target.id
        op_map = {
            ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
            ast.Div: "/", ast.FloorDiv: "/", ast.Mod: "%",
            ast.Pow: "^", ast.MatMult: "·",
            ast.LShift: "<<", ast.RShift: ">>",
            ast.BitAnd: "&&", ast.BitOr: "||", ast.BitXor: "^^",
        }
        op_text = op_map.get(type(stmt.op), "?")
        rhs = ast.unparse(stmt.value)
        # Cubical heap step: ``h += rhs`` mutates ``h``'s cell when
        # ``h`` is a list/set/dict/object (Python's ``__iadd__`` is
        # in-place).  Bump the epoch and record the mutation; the
        # following Cut binding sits on top of the new world.
        if h in self._world.name_to_cell:
            affected = self._world.mutate(
                h, line=getattr(stmt, "lineno", 0),
            )
            self._emit_lean(
                indent,
                f"-- mutate ◇: {h} {op_text}= {rhs}  "
                f"epoch={self._world.epoch}  "
                f"affects={sorted(affected)}",
            )
        self._emit_lean(
            indent, f"-- {h} {op_text}= {rhs}  (rebind {h})",
        )
        # Build a Z3-checkable equation ``h_new = h_old <op> rhs``
        # the kernel can verify.
        return Cut(
            hyp_name=h,
            hyp_type=PyObjType(),
            lemma_proof=Z3Proof(
                formula=f"{h} {op_text} {rhs}",
                binders={},
            ),
            body_proof=Refl(Var(f"_aug_{h}_body")),
        )

    # ── plain assign — local definition ───────────────────────
    def _compile_assign(self, stmt: ast.Assign, indent: int) -> ProofTerm:
        if not stmt.targets:
            return Structural("non-name assign")
        target = stmt.targets[0]
        # Generator binding: ``g = my_gen()`` where ``my_gen`` is a
        # function previously declared with a yielding body.  Alias
        # ``g`` to the generator-registry entry for ``my_gen`` so
        # later ``next(g)`` / ``g.send(v)`` advance the right
        # generator.
        if (
            isinstance(target, ast.Name)
            and isinstance(stmt.value, ast.Call)
            and isinstance(stmt.value.func, ast.Name)
        ):
            fn_name = stmt.value.func.id
            if fn_name in self._generators.generators:
                self._generators.alias(target.id, fn_name)
                self._emit_lean(
                    indent,
                    f"-- {target.id} = {fn_name}(): aliased to "
                    f"generator coalgebra",
                )
        # Cubical heap step: ``b = a`` (Name = Name) registers an
        # alias and emits a ``DuckPath`` recording read-equivalence
        # at the cell level.  This is the cubical primitive that
        # later mutation-detection uses to determine which proofs
        # are invalidated.  Only fire for the simple Name = Name
        # form; richer RHS expressions allocate fresh cells.
        if (
            isinstance(target, ast.Name)
            and isinstance(stmt.value, ast.Name)
        ):
            dst = target.id
            src = stmt.value.id
            if self._world.alias(dst, src):
                self._emit_lean(
                    indent,
                    f"-- alias: {dst} = {src}  (DuckPath at cell level)",
                )
                # Record the alias path as a kernel artefact.
                # Don't return early — fall through to the regular
                # Cut emission below so the body proof still chains.
                duck = DuckPath(
                    type_a=PyObjType(),
                    type_b=PyObjType(),
                    method_proofs=[
                        ("read", Refl(Var(_safe(src)))),
                    ],
                )
                self._emit_lean(indent, f"-- let {dst} := {src}")
                inner = self._compile_expr(stmt.value, indent)
                return Cut(
                    hyp_name=dst,
                    hyp_type=PyObjType(),
                    lemma_proof=duck,
                    body_proof=inner,
                )
        # Tuple-unpacking assignment: ``lhs, rhs = eq.sides`` and
        # ``(a, b) = pair``.  Bind each component of the tuple as
        # a separate Cut — the RHS is computed once, then each
        # name in the tuple gets a Cut wrapper.
        if isinstance(target, (ast.Tuple, ast.List)):
            names = [
                e.id for e in target.elts
                if isinstance(e, ast.Name)
            ]
            if not names:
                return Structural("non-name tuple assign")
            rhs_text = ast.unparse(stmt.value)
            self._emit_lean(
                indent,
                f"-- let ({', '.join(names)}) := {rhs_text}",
            )
            self._emit_lean(
                indent,
                f"obtain ⟨{', '.join(names)}⟩ := {rhs_text}",
            )
            inner = self._compile_expr(stmt.value, indent)
            # Build the Cut chain so each name binds in order.
            body: ProofTerm = Refl(Var("_unpack_body"))
            for n in reversed(names):
                body = Cut(
                    hyp_name=n,
                    hyp_type=PyObjType(),
                    lemma_proof=inner,
                    body_proof=body,
                )
                # Subsequent names share the same RHS — that matches
                # tuple-unpack semantics where each component is
                # a projection of the same value.
            return body
        if not isinstance(target, ast.Name):
            return Structural("non-name assign")
        h = target.id
        rhs = ast.unparse(stmt.value)
        self._emit_lean(indent, f"-- let {h} := {rhs}")
        inner = self._compile_expr(stmt.value, indent)
        return Cut(
            hyp_name=h,
            hyp_type=PyObjType(),
            lemma_proof=inner,
            body_proof=Refl(Var("_let_body")),
        )

    # ── expression statement — the main tactic call site ─────
    def _compile_expr_stmt(self, stmt: ast.Expr, indent: int) -> ProofTerm:
        return self._compile_expr(stmt.value, indent)

    # ── Expression compiler ────────────────────────────────────
    def _compile_expr(self, node: ast.expr, indent: int) -> ProofTerm:
        # Function calls — the main tactic surface.
        if isinstance(node, ast.Call):
            return self._compile_call(node, indent)
        # Bare names — could be a foundation citation.
        if isinstance(node, ast.Name):
            return self._compile_name_ref(node, indent)
        # Postfix attribute sugar: ``eq.symm`` / ``path.inv`` /
        # ``eq.lhs`` / ``eq.rhs``.  Only handles the no-args form;
        # ``eq.trans(eq2)`` is a Call → goes through _compile_call.
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
            recv = node.value.id
            attr = node.attr
            if attr in {"symm", "inv"}:
                self._emit_lean(indent, f"exact ({recv}).symm")
                return Sym(
                    proof=AxiomInvocation(name=recv, module=""),
                )
            if attr == "lhs":
                self._emit_lean(indent, f"-- {recv}.lhs (left side)")
                return Structural(f"{recv}.lhs")
            if attr == "rhs":
                self._emit_lean(indent, f"-- {recv}.rhs (right side)")
                return Structural(f"{recv}.rhs")
            if attr == "sides":
                self._emit_lean(
                    indent, f"-- {recv}.sides (lhs, rhs)",
                )
                return Structural(f"{recv}.sides")
            if attr == "unfold":
                self._emit_lean(indent, f"unfold {_safe(recv)}")
                return Unfold(
                    func_name=recv, proof=Refl(Var(recv)),
                )
            if attr == "rewrite":
                self._emit_lean(indent, f"rw [{_safe(recv)}]")
                return Rewrite(
                    lemma=AxiomInvocation(name=recv, module=""),
                    proof=Refl(Var(recv)),
                )
        # Walrus / named expression: ``(h := proof_expr)``.
        if isinstance(node, ast.NamedExpr):
            target = node.target
            value = node.value
            if isinstance(target, ast.Name):
                inner = self._compile_expr(value, indent)
                self._emit_lean(
                    indent, f"have {target.id} := {ast.unparse(value)}",
                )
                return Cut(
                    hyp_name=target.id,
                    hyp_type=PyObjType(),
                    lemma_proof=inner,
                    body_proof=Refl(Var(_safe(target.id))),
                )
        # Operator-overloaded proof composition.
        if isinstance(node, ast.UnaryOp):
            # ``~p`` → ``Sym(p)`` (path inversion / eq symmetry).
            if isinstance(node.op, ast.Invert):
                inner = self._compile_expr(node.operand, indent)
                self._emit_lean(
                    indent,
                    f"exact ({ast.unparse(node.operand)}).symm",
                )
                return Sym(proof=inner)
            # ``not P`` → negation.
            if isinstance(node.op, ast.Not):
                inner = self._compile_expr(node.operand, indent)
                self._emit_lean(
                    indent, f"-- ¬ ({ast.unparse(node.operand)})",
                )
                return Structural(
                    f"negation of {ast.unparse(node.operand)}"
                )
        # Compare operators (``a == b``, ``a < b``, ``a is b``, etc.)
        # — at expression position, treat as a Z3-discharged claim
        # (the predicate Z3 will prove).  This is the bridge from
        # Python's surface comparison syntax to a kernel proof.
        if isinstance(node, ast.Compare):
            text = ast.unparse(node)
            self._emit_lean(indent, f"-- compare: {text}")
            return Z3Proof(formula=text, binders={})
        # ``yield x`` / ``yield from xs`` — coalgebraic effect.
        # In a generator's body, each ``yield`` is one path step:
        # the kernel sees ``EffectWitness("yield:N@epoch_M", ...)``.
        # We add the yield point to the *enclosing function*'s
        # generator entry (tracked by ``self._current_genfn``); if
        # no enclosing genfn exists we still emit the witness so
        # the kernel sees the yield as a free-standing effect.
        if isinstance(node, ast.Yield):
            value_text = (
                ast.unparse(node.value) if node.value is not None else "None"
            )
            owner = getattr(self, "_current_genfn", None)
            if owner:
                yp = self._generators.add_yield_to(
                    owner, value_text,
                    line=getattr(node, "lineno", 0),
                    world_epoch=self._world.epoch,
                )
                index = yp.index
            else:
                # Free-standing yield — index 0 in an anonymous
                # generator.
                index = 0
            self._emit_lean(
                indent,
                f"-- yield {value_text} (index {index}, "
                f"epoch {self._world.epoch})",
            )
            return self._emit_yield(
                value_text, index, world_epoch=self._world.epoch,
            )
        if isinstance(node, ast.YieldFrom):
            it_text = ast.unparse(node.value)
            self._emit_lean(
                indent, f"-- yield from {it_text}",
            )
            # ``yield from`` delegates: emit a placeholder yield
            # witness whose value is the entire delegated iterator.
            return self._emit_yield(
                it_text, 0, world_epoch=self._world.epoch,
            )
        # ``await x`` — async coroutine suspension point.
        if isinstance(node, ast.Await):
            target_text = ast.unparse(node.value)
            owner = getattr(self, "_current_genfn", None)
            # When inside an ``async def`` we tag against that name.
            ap = None
            if owner:
                ap = self._coroutines.add_await_to(
                    owner, target_text,
                    line=getattr(node, "lineno", 0),
                    world_epoch=self._world.epoch,
                )
            self._emit_lean(
                indent,
                f"-- await {target_text} (epoch {self._world.epoch})",
            )
            return self._emit_await(
                target_text, ap.index if ap else 0,
                world_epoch=self._world.epoch,
            )
        if isinstance(node, ast.BinOp):
            # ``p @ q`` → path composition (PathComp).
            if isinstance(node.op, ast.MatMult):
                left = self._compile_expr(node.left, indent)
                right = self._compile_expr(node.right, indent)
                self._emit_lean(
                    indent,
                    f"exact ({ast.unparse(node.left)}).trans "
                    f"({ast.unparse(node.right)})",
                )
                return PathComp(left_path=left, right_path=right)
            # ``f * p`` → ``Ap(f, p)`` / functorial action / congruence.
            # Recognised when the left operand is a Name and the
            # right is a Call/Name (i.e. function applied to a path).
            if isinstance(node.op, ast.Mult) and isinstance(node.left, ast.Name):
                fn_text = node.left.id
                p = self._compile_expr(node.right, indent)
                self._emit_lean(
                    indent,
                    f"exact congrArg {fn_text} {ast.unparse(node.right)}",
                )
                return Ap(function=Var(_safe(fn_text)), path_proof=p)
            # ``p ** k`` → k-fold path composition.  When ``k`` is a
            # constant integer ≥ 1, unfold to ``PathComp(p, p, ..., p)``
            # k times.  Non-constant exponents fall back to a single
            # composition with the path on both sides.
            if isinstance(node.op, ast.Pow):
                left = self._compile_expr(node.left, indent)
                k_text = ast.unparse(node.right)
                k_int = 1
                if isinstance(node.right, ast.Constant) and isinstance(
                    node.right.value, int,
                ):
                    k_int = max(node.right.value, 1)
                self._emit_lean(
                    indent,
                    f"-- {ast.unparse(node.left)} ** {k_text}: "
                    f"{k_int}-fold composition",
                )
                acc = left
                for _ in range(k_int - 1):
                    acc = PathComp(left_path=acc, right_path=left)
                return acc
            # ``proof_a >> proof_b`` → sequential chaining.
            if isinstance(node.op, ast.RShift):
                left = self._compile_expr(node.left, indent)
                right = self._compile_expr(node.right, indent)
                return Cut(
                    hyp_name=f"_chain_{getattr(node, 'lineno', 0)}",
                    hyp_type=PyObjType(),
                    lemma_proof=left,
                    body_proof=right,
                )
            # Arithmetic / bitwise BinOps fall through to a Z3
            # claim: the user is expressing an arithmetic identity.
            # Bool-valued ops (``a & b`` for short-circuit-style)
            # are also Z3 claims under the placeholder semantics.
            if isinstance(node.op, (
                ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv,
                ast.Mod, ast.LShift, ast.BitAnd, ast.BitOr, ast.BitXor,
            )):
                text = ast.unparse(node)
                self._emit_lean(indent, f"-- arithmetic: {text}")
                return Z3Proof(formula=text, binders={})
        # Conditional expression: ``a if cond else b`` → Cases.
        if isinstance(node, ast.IfExp):
            cond_text = ast.unparse(node.test)
            self._emit_lean(indent, f"by_cases h : {cond_text}")
            self._emit_lean(indent, "· -- then")
            then_pf = self._compile_expr(node.body, indent + 1)
            self._emit_lean(indent, "· -- else")
            else_pf = self._compile_expr(node.orelse, indent + 1)
            return Cases(
                scrutinee=Var(cond_text),
                branches=[("then", then_pf), ("else", else_pf)],
            )
        # List / generator comprehensions over proofs.
        if isinstance(node, ast.DictComp):
            self._emit_lean(
                indent,
                f"-- dict comprehension: {ast.unparse(node)}",
            )
            # Compile the value expression as a sample proof —
            # treat key/value pair as a tuple of refls.
            v_pf = self._compile_expr(node.value, indent + 1)
            return v_pf
        if isinstance(node, (ast.ListComp, ast.GeneratorExp, ast.SetComp)):
            self._emit_lean(
                indent,
                f"-- comprehension proof: {ast.unparse(node)}",
            )
            # Compile the element expression once as a sample proof —
            # the caller (e.g. ``all(...)``) wraps with ListInduction.
            elt_pf = self._compile_expr(node.elt, indent + 1)
            # If the comprehension iterates a single name binder, we
            # treat it as a list-induction of the element proof.
            gen = node.generators[0] if node.generators else None
            if gen is not None and isinstance(gen.target, ast.Name):
                return ListInduction(
                    var=gen.target.id,
                    nil_proof=Refl(Var("_nil")),
                    cons_proof=elt_pf,
                )
            return elt_pf
        # Subscript types are PSDL's type-level vocabulary.  Each
        # form corresponds to a kernel ProofTerm or to a structural
        # type description.  We accept tuples in the slice
        # (``Path[A, x, y]``) by unwrapping the elements.
        if isinstance(node, ast.Subscript):
            head = ast.unparse(node.value) if hasattr(node, "value") else ""
            slice_node = node.slice
            # Py < 3.9 compat: unwrap ``ast.Index`` if present.
            if isinstance(slice_node, ast.Index):  # type: ignore[attr-defined]
                slice_node = slice_node.value  # type: ignore[attr-defined]
            slice_args: list[ast.expr]
            if isinstance(slice_node, ast.Tuple):
                slice_args = list(slice_node.elts)
            else:
                slice_args = [slice_node]
            if head == "Refl":
                tx = ast.unparse(slice_args[0]) if slice_args else "_x"
                self._emit_lean(indent, "rfl")
                return Refl(Var(_safe(tx)))
            if head == "Path":
                # Path[A, x, y] — equality at type A between x and y.
                # When all three are present, emit a Refl wrapping x
                # (asserts x = x; the elaborator unifies via the
                # surrounding goal's actual endpoints).  Two-arg
                # ``Path[A, x]`` falls back to Refl(x).
                target = ast.unparse(slice_args[1]) if len(slice_args) > 1 else "_x"
                self._emit_lean(
                    indent, f"-- Path[{', '.join(ast.unparse(s) for s in slice_args)}]",
                )
                self._emit_lean(indent, "rfl")
                return Refl(Var(_safe(target)))
            if head in {"Pi", "Π"}:
                # Pi[x: T] — universal binder.  In expression
                # position, treat as a structural placeholder; the
                # interesting form is via ``forall(...)``.
                self._emit_lean(
                    indent, f"-- Π-type: {ast.unparse(node)}",
                )
                return Structural(f"Pi {ast.unparse(node)}")
            if head in {"Sigma", "Σ"}:
                # Sigma[x: T] — existential binder; structural here.
                self._emit_lean(
                    indent, f"-- Σ-type: {ast.unparse(node)}",
                )
                return Structural(f"Sigma {ast.unparse(node)}")
            if head == "Equiv":
                # Equiv[A, B] — structural; the constructor is
                # ``iso(forward, backward, l_inv, r_inv)``.
                self._emit_lean(
                    indent, f"-- Equiv: {ast.unparse(node)}",
                )
                return Structural(f"Equiv {ast.unparse(node)}")
            if head in {"Diamond", "◇"}:
                # ◇A — may have effect.  Empty-witness placeholder.
                self._emit_lean(indent, f"-- ◇{ast.unparse(node)}")
                return EffectWitness(
                    effect=f"diamond:{ast.unparse(node)}",
                    proof=Refl(Var("_diamond")),
                )
            if head in {"Box", "□"}:
                # □A — pure / guaranteed.
                self._emit_lean(indent, f"-- □{ast.unparse(node)}")
                return EffectWitness(
                    effect="value",
                    proof=Refl(Var("_box")),
                )
            if head == "Refinement":
                # Refinement[T, P] — structural.
                self._emit_lean(
                    indent, f"-- {ast.unparse(node)}",
                )
                return Structural(f"refinement {ast.unparse(node)}")
            # Generic subscript types — a type-level form, no tactic.
            self._emit_lean(
                indent, f"-- type-level: {ast.unparse(node)}",
            )
            return Structural(f"type-level {ast.unparse(node)}")
        # ``proof_a if False else proof_b``-style; also Tuple expr.
        if isinstance(node, ast.Tuple):
            # A bare tuple in proof position is rare; treat as
            # composition of subproofs, returning the last one.
            inners = [self._compile_expr(e, indent) for e in node.elts]
            return inners[-1] if inners else Structural("empty tuple")
        # Boolean operators on proofs: ``P and Q`` → conjunction;
        # ``P or Q`` → disjunction recorded via ``Cases`` so neither
        # branch is silently dropped.
        if isinstance(node, ast.BoolOp):
            inners = [self._compile_expr(v, indent) for v in node.values]
            if isinstance(node.op, ast.And):
                self._emit_lean(
                    indent,
                    "exact ⟨" + ", ".join(
                        ast.unparse(v) for v in node.values
                    ) + "⟩",
                )
                # Conjunction: chain via Cut so trust composes.
                acc = inners[-1]
                for inner in reversed(inners[:-1]):
                    acc = Cut(
                        hyp_name="_and",
                        hyp_type=PyObjType(),
                        lemma_proof=inner,
                        body_proof=acc,
                    )
                return acc
            if isinstance(node.op, ast.Or):
                # Disjunction: encode as a ``Cases`` keyed on which
                # disjunct is intended.  Both witnesses are
                # preserved in the kernel-side artefact (so neither
                # half is silently dropped).  The Lean side emits a
                # ``Or.inl <left> <|> Or.inr <right>`` alternation
                # so the elaborator can pick whichever one matches
                # the goal.
                if not inners:
                    return Structural("empty or")
                lean_alts = " <|> ".join(
                    f"(Or.inl {ast.unparse(v)})" if i == 0
                    else f"(Or.inr {ast.unparse(v)})"
                    for i, v in enumerate(node.values)
                )
                self._emit_lean(
                    indent,
                    f"first | exact {lean_alts}  -- ∨-intro",
                )
                branches: list[tuple[str, ProofTerm]] = [
                    (f"or_{i}", inner) for i, inner in enumerate(inners)
                ]
                return Cases(
                    scrutinee=Var(f"_or_{getattr(node, 'lineno', 0)}"),
                    branches=branches,
                )
        # ``...`` (Ellipsis) — Pythonic placeholder; emit ``sorry``
        # explicitly so the user gets a visible warning rather than
        # silent failure.  Records ``hint`` so audits can list the
        # placeholders.
        if isinstance(node, ast.Constant) and node.value is Ellipsis:
            self._emit_lean(indent, "sorry  -- ellipsis placeholder")
            self.hints.append(
                f"PSDL ellipsis at L{getattr(node, 'lineno', 0)}: "
                "fill in the proof body"
            )
            return Structural("ellipsis placeholder")
        # String literals — docstrings / hints / Lean escape.
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            self._emit_lean(indent, f"-- {node.value}")
            return Structural(f"comment: {node.value[:40]}")
        # Numeric / bool constants — used in tactics like
        # ``apply(F, 0)`` for argument passing.
        if isinstance(node, ast.Constant):
            self._emit_lean(indent, f"-- const {node.value!r}")
            return Refl(Var(f"_const_{_safe(repr(node.value))}"))
        # ``{"left": p, "right": q}`` — dict-literal And-intro.
        # Produces a ``Cut`` chain plus a Lean ``⟨p, q, ...⟩`` term.
        if isinstance(node, ast.Dict):
            keys = [
                k.value if isinstance(k, ast.Constant) else ast.unparse(k)
                for k in node.keys if k is not None
            ]
            value_pfs = [self._compile_expr(v, indent) for v in node.values]
            value_texts = [ast.unparse(v) for v in node.values]
            self._emit_lean(
                indent,
                "exact ⟨" + ", ".join(value_texts) + "⟩",
            )
            acc: ProofTerm = (
                value_pfs[-1] if value_pfs else Structural("empty dict")
            )
            for inner, k in zip(reversed(value_pfs[:-1]), reversed(keys[:-1])):
                acc = Cut(
                    hyp_name=str(k),
                    hyp_type=PyObjType(),
                    lemma_proof=inner,
                    body_proof=acc,
                )
            return acc
        # ``f"goal text {expr}"`` — JoinedStr (f-string) — emit as
        # a Lean ``show`` rendering, with the format-spec substituted.
        if isinstance(node, ast.JoinedStr):
            try:
                rendered = ast.unparse(node)
            except Exception:
                rendered = "<f-string>"
            self._emit_lean(indent, f"-- f-string: {rendered}")
            return Structural(f"f-string {rendered[:40]}")
        # Lambda: standalone (no funext wrapper) — record as a
        # type-family-shaped Structural; the caller (transport / J)
        # picks it up.
        if isinstance(node, ast.Lambda):
            arg_names = [a.arg for a in node.args.args]
            self._emit_lean(
                indent,
                f"-- lambda type family: ({', '.join(arg_names)}) ↦ "
                f"{ast.unparse(node.body)}",
            )
            return Structural(f"lambda({arg_names})")
        # Starred expressions ``*paths`` in argument position —
        # carry through; the enclosing Call handler turns them into
        # iterated proof composition.
        if isinstance(node, ast.Starred):
            return self._compile_expr(node.value, indent)
        # Anything else — bail.
        text = ast.unparse(node)
        self.errors.append(PSDLError(
            line_no=getattr(node, "lineno", 0),
            line_text=text,
            message=f"unsupported PSDL expression: {type(node).__name__}",
        ))
        self._emit_lean(indent, f"sorry  -- unsupported: {text}")
        return Structural(f"unsupported expr {type(node).__name__}")

    def _compile_name_ref(self, node: ast.Name, indent: int) -> ProofTerm:
        nm = node.id
        if nm in self.foundations:
            self.foundations_referenced.append(nm)
            self._emit_lean(indent, f"exact Foundation_{_safe(nm)}")
            return AxiomInvocation(name=nm, module="foundations")
        # Cubical heap step: when ``nm`` references a cell that has
        # been mutated since some earlier proof was registered, the
        # citation needs a ``TransportProof`` along the mutation
        # path.  We detect "has been mutated" via the cell's
        # ``mutated_at`` list — if it's non-empty, transport is
        # required.  We emit a ``TransportProof`` wrapping a
        # placeholder ``AxiomInvocation`` so the kernel sees the
        # transport obligation.
        cell = self._world.cell_of(nm)
        if cell is not None and cell.mutated_at:
            self._emit_lean(
                indent,
                f"-- {nm}: transport along mutation path "
                f"(epochs {cell.mutated_at}); cubical-heap requires "
                f"the invariant be re-established",
            )
            self._emit_lean(indent, f"exact {_safe(nm)}")
            return TransportProof(
                type_family=Var(f"_inv_{_safe(nm)}"),
                path_proof=AxiomInvocation(
                    name=f"mutate_path_{nm}_e{cell.mutated_at[-1]}",
                    module="cubical_heap",
                ),
                base_proof=AxiomInvocation(name=nm, module=""),
            )
        # Pure read: no world change, just cite the axiom.
        self._emit_lean(indent, f"exact {_safe(nm)}")
        return AxiomInvocation(name=nm, module="")

    def _compile_call(self, call: ast.Call, indent: int) -> ProofTerm:
        # Method calls: ``method.action(args)``
        if isinstance(call.func, ast.Attribute):
            return self._compile_method_call(call, indent)
        # Plain function calls
        if isinstance(call.func, ast.Name):
            return self._compile_func_call(call, indent)
        text = ast.unparse(call)
        self._emit_lean(indent, f"sorry  -- unsupported call: {text}")
        # Soundness signal: unsupported calls must surface as errors
        # so callers can detect the proof is incomplete.  Without
        # this, ``compile_psdl`` would return ``ok=True`` even when
        # the proof body is a sorry placeholder.
        self.errors.append(PSDLError(
            line_no=getattr(call, "lineno", 0),
            line_text=text,
            message=f"unsupported PSDL call: {type(call.func).__name__} head",
        ))
        return Structural(f"unsupported call {text}")

    def _compile_method_call(self, call: ast.Call, indent: int) -> ProofTerm:
        f = call.func
        attr = f.attr  # type: ignore[attr-defined]
        recv = ast.unparse(f.value)  # type: ignore[attr-defined]
        # ── g.send(v) — comonad coalgebra: TransportProof along input ──
        if (
            attr == "send"
            and isinstance(f.value, ast.Name)  # type: ignore[attr-defined]
        ):
            gname = f.value.id  # type: ignore[attr-defined]
            input_text = ast.unparse(call.args[0]) if call.args else "None"
            g = self._generators.get(gname)
            if g is None:
                g = self._generators.declare(
                    gname, line=getattr(call, "lineno", 0),
                )
            yp = self._generators.advance(gname)
            self._emit_lean(
                indent,
                f"-- {gname}.send({input_text}) — transport along input path",
            )
            if yp is None:
                self.errors.append(PSDLError(
                    line_no=getattr(call, "lineno", 0),
                    line_text=ast.unparse(call),
                    message=(
                        f"PSDL ``{gname}.send(...)`` on exhausted "
                        f"generator — no path to transport along"
                    ),
                ))
                return Structural(
                    f"{gname}.send: exhausted"
                )
            return TransportProof(
                type_family=Var(f"_yielded_of_{gname}"),
                path_proof=AxiomInvocation(
                    name=f"input_{_safe(input_text)}",
                    module="generator",
                ),
                base_proof=Refl(Var(yp.value_repr[:24] or "_y")),
            )
        # ── g.close() — path inversion at the current yield ──
        if (
            attr == "close"
            and isinstance(f.value, ast.Name)  # type: ignore[attr-defined]
        ):
            gname = f.value.id  # type: ignore[attr-defined]
            g = self._generators.get(gname)
            if g is None or g.exhausted:
                self._emit_lean(
                    indent,
                    f"-- {gname}.close(): no-op (exhausted or unknown)",
                )
                return Structural(f"{gname}.close: no-op")
            cur = g.current_index if g.current_index >= 0 else 0
            yp = g.yields[cur] if cur < len(g.yields) else None
            self._emit_lean(
                indent,
                f"-- {gname}.close() — Sym(yield path) at index {cur}",
            )
            g.exhausted = True
            return Sym(
                proof=EffectWitness(
                    effect=(
                        f"yield:{cur}@epoch{yp.world_epoch if yp else 0}"
                    ),
                    proof=Refl(Var(
                        yp.value_repr[:24] if yp else "_y"
                    )),
                ),
            )
        # Cubical heap step: when ``attr`` is a known mutator, this
        # call is a path between worlds.  We bump the epoch, record
        # the mutation on the cell, and emit an ``EffectWitness`` in
        # the ◇ modality keyed by the mutated name and new epoch.
        # All proof terms produced *before* this mutation that
        # depended on the cell's invariants now require transport;
        # the lint pass / kernel detect that.
        if (
            self._looks_mutating(attr)
            and isinstance(f.value, ast.Name)  # type: ignore[attr-defined]
        ):
            recv_name = f.value.id  # type: ignore[attr-defined]
            affected = self._world.mutate(
                recv_name, line=getattr(call, "lineno", 0),
            )
            self._effects.append(
                __import__(
                    "deppy.proofs.psdl_heap", fromlist=["Effect"],
                ).Effect(
                    line_no=getattr(call, "lineno", 0),
                    kind="mutate",
                    locator=f"{recv_name}.{attr}",
                    epoch=self._world.epoch,
                )
            )
            self._emit_lean(
                indent,
                f"-- mutate ◇: {recv_name}.{attr}(...)  "
                f"epoch={self._world.epoch}  "
                f"affects={sorted(affected)}",
            )
            # Emit the cubical effect: a world path indexed by the
            # cell + new epoch.  Inner proof of the EffectWitness is
            # the actual call's effect (recorded as a Refl placeholder
            # — what the call returns is irrelevant for the heap path).
            return EffectWitness(
                effect=(
                    f"mutate:{recv_name}.{attr}@epoch{self._world.epoch}"
                ),
                proof=Refl(Var(_safe(recv_name))),
            )
        # ── method.unfold() / method.rewrite() ──
        if attr == "unfold":
            self._emit_lean(indent, f"unfold {_safe(recv)}")
            return Unfold(func_name=recv, proof=Refl(Var(recv)))
        if attr == "rewrite":
            self._emit_lean(indent, f"rw [{_safe(recv)}]")
            return Rewrite(
                lemma=AxiomInvocation(name=recv, module=""),
                proof=Refl(Var(recv)),
            )
        # ── eq.trans(eq2) ──
        if attr == "trans":
            other = (
                ast.unparse(call.args[0]) if call.args else "_other"
            )
            self._emit_lean(
                indent, f"exact ({recv}).trans ({other})",
            )
            return Trans(
                left=AxiomInvocation(name=recv, module=""),
                right=AxiomInvocation(name=other, module=""),
            )
        # ── path.cong(f) — congruence on a path with given function ──
        if attr == "cong":
            fn_text = ast.unparse(call.args[0]) if call.args else "_f"
            self._emit_lean(
                indent, f"exact congrArg {fn_text} {recv}",
            )
            return Cong(
                func=Var(_safe(fn_text)),
                proof=AxiomInvocation(name=recv, module=""),
            )
        # ── eq.subst / eq.rew ──
        if attr in {"subst", "rew", "rewrite_then"}:
            self._emit_lean(indent, f"rw [{recv}]")
            return Rewrite(
                lemma=AxiomInvocation(name=recv, module=""),
                proof=(
                    self._compile_expr(call.args[0], indent)
                    if call.args else Refl(Var("_b"))
                ),
            )
        # Generic: treat as opaque tactic.
        text = ast.unparse(call)
        self._emit_lean(indent, f"-- {text}")
        return Structural(f"method-call: {text}")

    def _compile_func_call(self, call: ast.Call, indent: int) -> ProofTerm:
        fname = call.func.id  # type: ignore[union-attr]
        args = call.args
        # ── apply(F) ──
        if fname == "apply":
            if not args:
                return Structural("apply with no args")
            target = ast.unparse(args[0])
            if target in self.foundations:
                self.foundations_referenced.append(target)
                self._emit_lean(indent, f"exact Foundation_{_safe(target)}")
                return AxiomInvocation(name=target, module="foundations")
            self._emit_lean(indent, f"exact {_safe(target)}")
            return AxiomInvocation(name=target, module="")
        # ── unfold(method) ──
        if fname == "unfold":
            if not args:
                return Structural("unfold with no args")
            target = ast.unparse(args[0])
            inner: ProofTerm = Refl(Var("_b"))
            self._emit_lean(indent, f"unfold {_safe(target)}")
            return Unfold(func_name=target, proof=inner)
        # ── inline(method, expected_expr) ──
        if fname == "inline":
            if len(args) < 1:
                return Structural("inline with no args")
            target = ast.unparse(args[0])
            expected = ast.unparse(args[1]) if len(args) > 1 else ""
            self._emit_lean(
                indent,
                f"unfold {_safe(target)}  -- expected: {expected}",
            )
            return Unfold(
                func_name=target,
                proof=Refl(Var(_safe(expected) if expected else "_b")),
            )
        # ── rewrite(L) ──
        if fname == "rewrite":
            target = ast.unparse(args[0]) if args else ""
            self._emit_lean(indent, f"rw [{_safe(target)}]")
            return Rewrite(
                lemma=AxiomInvocation(name=target, module=""),
                proof=Refl(Var(_safe(target) or "_a")),
            )
        # ── transport(p, value) ──
        if fname == "transport":
            p = ast.unparse(args[0]) if args else "p"
            v = ast.unparse(args[1]) if len(args) > 1 else "v"
            self._emit_lean(indent, f"-- transport along {p} of {v}")
            return TransportProof(
                type_family=Var(f"motive_{p}"),
                path_proof=AxiomInvocation(
                    name=p,
                    module="foundations" if p in self.foundations else "",
                ),
                base_proof=Refl(Var(_safe(v))),
            )
        # ── funext(lambda x: body) ──
        if fname == "funext":
            self._emit_lean(indent, "funext x")
            return FunExt(var="x", pointwise_proof=Refl(Var("_p")))
        # ── show_goal() ──
        if fname == "show_goal":
            self.show_goal_requested = True
            self._emit_lean(indent, "-- show_goal requested")
            return Structural("show_goal")
        # ── show_term() ──
        if fname == "show_term":
            self._emit_lean(indent, "-- show_term requested")
            return Structural("show_term")
        # ── hint("text") ──
        if fname == "hint":
            txt = ast.unparse(args[0]).strip("\"'") if args else ""
            self.hints.append(txt)
            self._emit_lean(indent, f"-- hint: {txt}")
            return Structural(f"hint: {txt}")
        # ── lean("...raw...") ──
        if fname == "lean":
            raw = ""
            if args and isinstance(args[0], ast.Constant):
                raw = str(args[0].value)
            self._emit_lean(indent, raw)
            return LeanProof(
                theorem="", proof_script=raw,
                expected_goal="", binders=(), theorem_name="",
                imports=(),
            )
        # ── pure() ──
        if fname == "pure":
            self._emit_lean(indent, "-- pure (□A modality)")
            return Structural("pure modality")
        # ── lemma(name, statement, by) ──
        if fname == "lemma":
            lname = ast.unparse(args[0]).strip("\"'") if args else "L"
            stmt = ast.unparse(args[1]).strip("\"'") if len(args) > 1 else "True"
            by_clause = (
                ast.unparse(args[2]).strip("\"'") if len(args) > 2 else ""
            )
            self._emit_lean(
                indent, f"have {_safe(lname)} : {stmt} := {by_clause}",
            )
            inner = (
                AxiomInvocation(name=by_clause, module="")
                if by_clause else Structural("unknown lemma")
            )
            return Cut(
                hyp_name=lname,
                hyp_type=RefinementType(
                    base_type=PyBoolType(), predicate=stmt,
                ),
                lemma_proof=inner,
                body_proof=Refl(Var("_lem_body")),
            )
        # ── pass ── (just in case)
        if fname == "pass":
            self._emit_lean(indent, "trivial")
            return Structural("trivial")
        # ── mro_lookup(Cls, "method") — DuckPath through C3 ──
        if fname == "mro_lookup" and len(args) >= 2:
            cls_text = ast.unparse(args[0])
            attr_text = (
                args[1].value if isinstance(args[1], ast.Constant)
                else ast.unparse(args[1])
            )
            attr_text = str(attr_text).strip("\"'")
            self._emit_lean(
                indent,
                f"-- mro_lookup({cls_text}, {attr_text!r})  "
                f"linearization={self._mro.linearize(cls_text)}",
            )
            return self._emit_mro_path(self._mro, cls_text, attr_text)
        # ── super_call("Cls", "method") — PathComp ──
        if fname == "super_call" and len(args) >= 2:
            cls_text = ast.unparse(args[0])
            attr_text = (
                args[1].value if isinstance(args[1], ast.Constant)
                else ast.unparse(args[1])
            )
            attr_text = str(attr_text).strip("\"'")
            self._emit_lean(
                indent, f"-- super({cls_text}).{attr_text}()",
            )
            return self._emit_super(self._mro, cls_text, attr_text)
        # ── op_dispatch("+", a, b) — ConditionalDuckPath ──
        if fname == "op_dispatch" and len(args) >= 3:
            op_text = (
                args[0].value if isinstance(args[0], ast.Constant)
                else ast.unparse(args[0])
            )
            op_text = str(op_text).strip("\"'")
            lhs = ast.unparse(args[1])
            rhs = ast.unparse(args[2])
            lhs_cls = (
                ast.unparse(call.keywords[0].value)
                if call.keywords and call.keywords[0].arg == "lhs_class"
                else None
            )
            rhs_cls = next(
                (
                    ast.unparse(kw.value)
                    for kw in call.keywords if kw.arg == "rhs_class"
                ),
                None,
            )
            self._emit_lean(
                indent,
                f"-- op_dispatch({op_text!r}, {lhs}, {rhs})",
            )
            return self._emit_op_dispatch(
                op_text, lhs, rhs,
                lhs_class=lhs_cls, rhs_class=rhs_cls,
                registry=self._op_registry,
            )
        # ── descriptor_get(obj, "Cls", "attr") — Fiber ──
        if fname == "descriptor_get" and len(args) >= 3:
            obj_text = ast.unparse(args[0])
            cls_text = (
                args[1].value if isinstance(args[1], ast.Constant)
                else ast.unparse(args[1])
            )
            attr_text = (
                args[2].value if isinstance(args[2], ast.Constant)
                else ast.unparse(args[2])
            )
            cls_text = str(cls_text).strip("\"'")
            attr_text = str(attr_text).strip("\"'")
            self._emit_lean(
                indent,
                f"-- descriptor_get({obj_text}, {cls_text}, {attr_text})",
            )
            return self._emit_descriptor_fiber(
                obj_text, cls_text, attr_text,
                registry=self._descriptors,
            )
        # ── descriptor_set(obj, "Cls", "attr", value) — Patch ──
        if fname == "descriptor_set" and len(args) >= 4:
            obj_text = ast.unparse(args[0])
            cls_text = (
                args[1].value if isinstance(args[1], ast.Constant)
                else ast.unparse(args[1])
            )
            attr_text = (
                args[2].value if isinstance(args[2], ast.Constant)
                else ast.unparse(args[2])
            )
            value_text = ast.unparse(args[3])
            cls_text = str(cls_text).strip("\"'")
            attr_text = str(attr_text).strip("\"'")
            self._emit_lean(
                indent,
                f"-- descriptor_set({obj_text}, {cls_text}, "
                f"{attr_text}, {value_text})",
            )
            return self._emit_descriptor_set_patch(
                obj_text, cls_text, attr_text, value_text,
            )
        # ── next(g) — comonad counit / generator advance ──
        if fname == "next" and args and isinstance(args[0], ast.Name):
            gname = args[0].id
            g = self._generators.get(gname)
            if g is None:
                # Caller expected a generator but PSDL never saw
                # the yields — declare the generator on the fly so
                # downstream uses don't NPE.
                g = self._generators.declare(
                    gname, line=getattr(call, "lineno", 0),
                )
            yp = self._generators.advance(gname)
            if yp is None:
                self._emit_lean(
                    indent,
                    f"-- next({gname}): exhausted",
                )
                self.errors.append(PSDLError(
                    line_no=getattr(call, "lineno", 0),
                    line_text=ast.unparse(call),
                    message=(
                        f"PSDL ``next({gname})`` on an exhausted "
                        f"generator — no fresh path to extract; "
                        f"re-iteration is forbidden by the cubical "
                        f"coalgebra"
                    ),
                ))
                return Structural(
                    f"next({gname}): exhausted (StopIteration)"
                )
            self._emit_lean(
                indent,
                f"-- next({gname}) → yield {yp.index} "
                f"(value {yp.value_repr[:24]})",
            )
            return self._emit_advance(
                g, line=getattr(call, "lineno", 0),
            )
        # ── Closer-sugar: qed() / auto() / done() / omega() / rfl_() ──
        # Each emits a different terminal tactic so the user can pick
        # the closer in Pythonic syntax without writing Lean directly.
        if fname == "qed":
            self._emit_lean(
                indent,
                "first | rfl | omega | decide | trivial",
            )
            return Refl(Var("_qed"))
        if fname == "auto":
            self._emit_lean(
                indent,
                "simp; first | rfl | omega | decide | trivial",
            )
            return Refl(Var("_auto"))
        if fname == "done":
            self._emit_lean(indent, "trivial")
            return Refl(Var("_done"))
        if fname == "omega":
            self._emit_lean(indent, "omega")
            return Refl(Var("_omega"))
        if fname in {"rfl_", "refl_"}:
            self._emit_lean(indent, "rfl")
            return Refl(Var("_rfl"))
        if fname == "simp":
            args_text = ", ".join(ast.unparse(a) for a in args)
            self._emit_lean(
                indent, f"simp [{args_text}]" if args else "simp",
            )
            return Refl(Var("_simp"))
        if fname == "decide":
            self._emit_lean(indent, "decide")
            return Refl(Var("_decide"))
        if fname == "trivial":
            self._emit_lean(indent, "trivial")
            return Refl(Var("_trivial"))
        # ``all(P(x) for x in xs)`` — wrap the comprehension as a
        # ListInduction-style universal.
        if fname == "all" and args and isinstance(
            args[0], (ast.GeneratorExp, ast.ListComp, ast.SetComp),
        ):
            self._emit_lean(
                indent,
                f"-- universal closure over {ast.unparse(args[0])}",
            )
            return self._compile_expr(args[0], indent + 1)
        # ``any(P(x) for x in xs)`` — disjunctive.
        if fname == "any" and args and isinstance(
            args[0], (ast.GeneratorExp, ast.ListComp, ast.SetComp),
        ):
            self._emit_lean(
                indent,
                f"-- existential closure over {ast.unparse(args[0])}",
            )
            return self._compile_expr(args[0], indent + 1)
        # ──────────────────────────────────────────────────────────
        #  CIC core: quantifiers, induction, substitution, paths
        # ──────────────────────────────────────────────────────────
        # ── forall(x, T, body) ──
        if fname == "forall":
            if len(args) >= 3:
                xv = ast.unparse(args[0])
                tt = ast.unparse(args[1])
                self._emit_lean(indent, f"intro ({xv} : {tt})")
                body = self._compile_expr(args[2], indent + 1)
                # Pass the type as the hypothesis type directly.
                # Previously we wrapped it in ``RefinementType(
                #   base_type=PyObjType(), predicate=<TYPE>)`` —
                # that placed a TYPE in the predicate field, which
                # the kernel doesn't interpret meaningfully.
                return Cut(
                    hyp_name=xv,
                    hyp_type=_typename_to_syntype(tt),
                    lemma_proof=Assume(name=xv),
                    body_proof=body,
                )
            return Structural("forall with insufficient args")
        # ── exists(x, T, witness, body) ──
        if fname == "exists":
            if len(args) >= 4:
                xv = ast.unparse(args[0])
                tt = ast.unparse(args[1])
                wn = ast.unparse(args[2])
                self._emit_lean(
                    indent, f"refine ⟨{wn}, ?_⟩  -- ∃ ({xv} : {tt})",
                )
                body = self._compile_expr(args[3], indent + 1)
                return Cut(
                    hyp_name=xv,
                    hyp_type=_typename_to_syntype(tt),
                    lemma_proof=Refl(Var(_safe(wn))),
                    body_proof=body,
                )
            return Structural("exists with insufficient args")
        # ── refl(x) ──
        if fname == "refl":
            if args:
                tx = ast.unparse(args[0])
                self._emit_lean(indent, "rfl")
                return Refl(Var(_safe(tx)))
            self._emit_lean(indent, "rfl")
            return Refl(Var("_x"))
        # ── sym(eq) ──
        if fname == "sym":
            if args:
                self._emit_lean(indent, f"exact ({ast.unparse(args[0])}).symm")
                inner = self._compile_expr(args[0], indent)
                return Sym(proof=inner)
            return Structural("sym with no args")
        # ── trans(eq1, eq2) ──
        if fname == "trans":
            if len(args) >= 2:
                a = self._compile_expr(args[0], indent)
                b = self._compile_expr(args[1], indent)
                self._emit_lean(
                    indent,
                    f"exact ({ast.unparse(args[0])}).trans ({ast.unparse(args[1])})",
                )
                return Trans(left=a, right=b)
            return Structural("trans with insufficient args")
        # ── cong(f, eq) ──
        if fname == "cong":
            if len(args) >= 2:
                fn_text = ast.unparse(args[0])
                eq_text = ast.unparse(args[1])
                self._emit_lean(indent, f"exact congrArg {fn_text} {eq_text}")
                inner_eq = self._compile_expr(args[1], indent)
                return Cong(func=Var(_safe(fn_text)), proof=inner_eq)
            return Structural("cong with insufficient args")
        # ── subst(eq, motive, body) / rew(eq, body) ──
        if fname == "subst":
            if len(args) >= 3:
                eq_text = ast.unparse(args[0])
                self._emit_lean(indent, f"rw [{eq_text}]")
                inner = self._compile_expr(args[2], indent)
                return Rewrite(
                    lemma=AxiomInvocation(name=eq_text, module=""),
                    proof=inner,
                )
            return Structural("subst with insufficient args")
        if fname == "rew":
            if len(args) >= 1:
                eq_text = ast.unparse(args[0])
                self._emit_lean(indent, f"rw [{eq_text}]")
                inner = (
                    self._compile_expr(args[1], indent)
                    if len(args) > 1 else Refl(Var("_b"))
                )
                return Rewrite(
                    lemma=AxiomInvocation(name=eq_text, module=""),
                    proof=inner,
                )
            return Structural("rew with no args")
        # ── induction(scrutinee) — explicit form via Cases ──
        if fname == "induction":
            if args:
                target = ast.unparse(args[0])
                self._emit_lean(indent, f"induction {target} with")
                base_pf: ProofTerm = Refl(Var("_base"))
                step_pf: ProofTerm = Refl(Var("_step"))
                # When called with kwargs base= / step=, use those.
                for kw in call.keywords:
                    if kw.arg == "base":
                        base_pf = self._compile_expr(kw.value, indent + 1)
                    elif kw.arg == "step":
                        step_pf = self._compile_expr(kw.value, indent + 1)
                return NatInduction(
                    var=target,
                    base_proof=base_pf,
                    step_proof=step_pf,
                )
            return Structural("induction with no args")
        # ── path_concat(p, q) / path_inv(p) / path_ap(f, p) ──
        if fname == "path_concat":
            if len(args) >= 2:
                a = self._compile_expr(args[0], indent)
                b = self._compile_expr(args[1], indent)
                self._emit_lean(
                    indent,
                    f"exact ({ast.unparse(args[0])}).trans ({ast.unparse(args[1])})",
                )
                return PathComp(left_path=a, right_path=b)
            return Structural("path_concat needs two paths")
        if fname == "path_inv":
            if args:
                a = self._compile_expr(args[0], indent)
                self._emit_lean(
                    indent, f"exact ({ast.unparse(args[0])}).symm",
                )
                return Sym(proof=a)
            return Structural("path_inv needs path")
        if fname == "path_ap":
            if len(args) >= 2:
                fn_text = ast.unparse(args[0])
                p = self._compile_expr(args[1], indent)
                self._emit_lean(
                    indent,
                    f"exact congrArg {fn_text} {ast.unparse(args[1])}",
                )
                return Ap(function=Var(_safe(fn_text)), path_proof=p)
            return Structural("path_ap needs (f, path)")
        # ── J(motive, refl_case, x, y, p) — path induction ──
        if fname == "J":
            if len(args) >= 5:
                motive_text = ast.unparse(args[0])
                refl_pf = self._compile_expr(args[1], indent)
                p_text = ast.unparse(args[4])
                self._emit_lean(
                    indent,
                    f"exact @Eq.rec _ _ {motive_text} "
                    f"{ast.unparse(args[1])} _ {p_text}",
                )
                # Approximate as a transport (motive is the family).
                return TransportProof(
                    type_family=Var(_safe(motive_text)),
                    path_proof=AxiomInvocation(name=p_text, module=""),
                    base_proof=refl_pf,
                )
            return Structural("J needs (motive, refl, x, y, p)")
        # ──────────────────────────────────────────────────────────
        #  Equivalences / univalence
        # ──────────────────────────────────────────────────────────
        # ── iso(forward, backward, l_inv, r_inv) ──
        if fname == "iso":
            if len(args) >= 4:
                self._emit_lean(
                    indent,
                    f"exact Equiv.mk {ast.unparse(args[0])} "
                    f"{ast.unparse(args[1])} "
                    f"{ast.unparse(args[2])} {ast.unparse(args[3])}",
                )
                return Cut(
                    hyp_name="iso",
                    hyp_type=PyObjType(),
                    lemma_proof=Refl(Var("_iso")),
                    body_proof=Refl(Var("_iso_body")),
                )
            return Structural("iso needs (fwd, bwd, l_inv, r_inv)")
        # ── equiv_to_path(e) — univalence axiom ──
        if fname == "equiv_to_path":
            if args:
                self._emit_lean(
                    indent,
                    f"-- univalence: Equiv → Path of types",
                )
                inner = self._compile_expr(args[0], indent)
                return TransportProof(
                    type_family=Var("_motive"),
                    path_proof=AxiomInvocation(
                        name="ua", module="psdl_local",
                    ),
                    base_proof=inner,
                )
            return Structural("equiv_to_path needs Equiv")
        # ──────────────────────────────────────────────────────────
        #  Cubical / duck / effect-Python primitives
        # ──────────────────────────────────────────────────────────
        # ── dispatch(receiver, "method") — DuckPath ──
        if fname == "dispatch":
            if len(args) >= 2:
                recv = ast.unparse(args[0])
                meth_text = ast.unparse(args[1]).strip("\"'")
                self._emit_lean(
                    indent,
                    f"-- duck dispatch: {recv}.{meth_text}\n  "
                    f"exact DuckPath_resolve {recv} \"{meth_text}\"",
                )
                return DuckPath(
                    type_a=PyObjType(),
                    type_b=PyObjType(),
                    method_proofs=[(meth_text, Refl(Var(_safe(recv))))],
                )
            return Structural("dispatch needs (receiver, method)")
        # ── kan_fill(open_box, filling) ──
        if fname == "kan_fill":
            if args:
                self._emit_lean(
                    indent,
                    f"-- Kan filler over {ast.unparse(args[0])}\n  "
                    f"apply Kan.fill",
                )
                # The kernel's ``Patch`` term (kernel.py:707-716)
                # carries (cls, method_name, new_impl, contract).
                # ``kan_fill(box, filling)`` is exactly this: ``box``
                # supplies the class+method context, ``filling`` is
                # the contract proof that the new implementation
                # preserves the open-box constraints.
                box_text = ast.unparse(args[0])
                filling = (
                    self._compile_expr(args[1], indent)
                    if len(args) > 1 else Refl(Var("_fill"))
                )
                return Patch(
                    cls=Var(f"_kan_box_{_safe(box_text)}"),
                    method_name="fill",
                    new_impl=Var(_safe(box_text)),
                    contract_proof=filling,
                )
            return Structural("kan_fill needs an open box")
        # ── cocycle(level, witness) ──
        if fname == "cocycle":
            if len(args) >= 2:
                lvl_text = ast.unparse(args[0])
                try:
                    lvl_int = int(lvl_text)
                except ValueError:
                    lvl_int = 0
                wit_text = ast.unparse(args[1])
                self._emit_lean(
                    indent,
                    f"-- cocycle level {lvl_int}, witness {wit_text}",
                )
                return Cocycle(
                    level=lvl_int,
                    components=[Refl(Var(_safe(wit_text)))],
                )
            return Structural("cocycle needs (level, witness)")
        # ── fibre_split(scrutinee, [(T1, body1), ...]) ──
        if fname == "fibre_split":
            if len(args) >= 2:
                scrut = ast.unparse(args[0])
                self._emit_lean(
                    indent, f"-- explicit fibration on {scrut}",
                )
                # Best-effort: collect type/branch pairs from a List.
                branches: list[tuple[str, ProofTerm]] = []
                if isinstance(args[1], (ast.List, ast.Tuple)):
                    for elt in args[1].elts:
                        if isinstance(elt, ast.Tuple) and len(elt.elts) == 2:
                            tt = ast.unparse(elt.elts[0])
                            branches.append((
                                tt,
                                self._compile_expr(elt.elts[1], indent + 1),
                            ))
                return Fiber(
                    scrutinee=Var(scrut),
                    type_branches=[
                        (PyObjType(), pf) for _, pf in branches
                    ],
                    exhaustive=True,
                )
            return Structural("fibre_split needs (scrutinee, branches)")
        # ── Diamond / Box / pure / bind / expect / lift / lower ──
        if fname == "bind":
            if len(args) >= 2:
                self._emit_lean(
                    indent,
                    f"-- ◇ bind: {ast.unparse(args[0])} ; "
                    f"{ast.unparse(args[1])}",
                )
                a = self._compile_expr(args[0], indent)
                b = self._compile_expr(args[1], indent)
                return Cut(
                    hyp_name="m",
                    hyp_type=PyObjType(),
                    lemma_proof=a,
                    body_proof=b,
                )
            return Structural("bind needs (m, k)")
        if fname == "expect":
            if len(args) >= 2:
                self._emit_lean(
                    indent,
                    f"-- ◇ expect (exception fibre handler)",
                )
                value_pf = self._compile_expr(args[0], indent)
                fallback_pf = self._compile_expr(args[1], indent)
                ew = EffectWitness(effect="value", proof=value_pf)
                return ConditionalEffectWitness(
                    precondition="raises",
                    effect="exception",
                    proof=fallback_pf,
                    target="Exception",
                )
            return Structural("expect needs (m, fallback)")
        if fname == "lift":
            if args:
                self._emit_lean(
                    indent, f"-- ◇ lift {ast.unparse(args[0])}",
                )
                return EffectWitness(
                    effect="value",
                    proof=self._compile_expr(args[0], indent),
                )
            return Structural("lift needs a value")
        if fname == "lower":
            if args:
                self._emit_lean(
                    indent, f"-- ◇-elim (purity witness required)",
                )
                return self._compile_expr(args[0], indent)
            return Structural("lower needs (m, witness)")
        # ── homotopy(p, q) / square(top, bot, left, right) ──
        if fname == "homotopy":
            if len(args) >= 2:
                self._emit_lean(
                    indent,
                    f"-- homotopy {ast.unparse(args[0])} ~ "
                    f"{ast.unparse(args[1])}",
                )
                return PathComp(
                    left_path=self._compile_expr(args[0], indent),
                    right_path=self._compile_expr(args[1], indent),
                )
            return Structural("homotopy needs (p, q)")
        if fname == "square":
            if len(args) >= 4:
                self._emit_lean(
                    indent, "-- 2-square diagram",
                )
                t = self._compile_expr(args[0], indent)
                b = self._compile_expr(args[1], indent)
                l = self._compile_expr(args[2], indent)
                r = self._compile_expr(args[3], indent)
                # No native Square node — chain via PathComp.
                return PathComp(
                    left_path=PathComp(left_path=t, right_path=b),
                    right_path=PathComp(left_path=l, right_path=r),
                )
            return Structural("square needs (top, bot, left, right)")
        # ── term[T](expr) / tactic[T](raw) — escape hatches ──
        if fname == "term":
            if args:
                self._emit_lean(indent, f"exact {ast.unparse(args[0])}")
                return self._compile_expr(args[0], indent)
            return Structural("term needs an expression")
        if fname == "tactic":
            raw = ""
            if args and isinstance(args[0], ast.Constant):
                raw = str(args[0].value)
            self._emit_lean(indent, raw)
            return LeanProof(
                theorem="", proof_script=raw,
                expected_goal="", binders=(), theorem_name="",
                imports=(),
            )
        # ── Foundation/axiom citation by bare call: F(args) ──
        if fname in self.foundations:
            self.foundations_referenced.append(fname)
            self._emit_lean(indent, f"exact Foundation_{_safe(fname)}")
            return AxiomInvocation(name=fname, module="foundations")
        # Unknown function — best-effort fallback, but record an
        # error so the caller knows the proof has a sorry hole.
        text = ast.unparse(call)
        self._emit_lean(indent, f"-- {text}\n  sorry")
        self.errors.append(PSDLError(
            line_no=getattr(call, "lineno", 0),
            line_text=text,
            message=(
                f"unknown PSDL primitive ``{fname}`` — proof body "
                f"contains a ``sorry`` placeholder"
            ),
        ))
        return Structural(f"unknown function {fname}")


def _typename_to_syntype(name: str):
    """Map a Python-style type-name string to a kernel ``SynType``.

    Recognised:
      ``int`` / ``Int``   → :class:`PyIntType`
      ``bool`` / ``Bool`` → :class:`PyBoolType`
      anything else       → :class:`PyObjType` with a structural tag.

    The string form gets preserved as a structural-tag attribute on
    PyObjType so downstream code can recover the user's original
    intent (e.g., the verify-block emitter records this in its
    binders dict).
    """
    n = (name or "").strip()
    if n in {"int", "Int", "Nat", "nat"}:
        return PyIntType()
    if n in {"bool", "Bool"}:
        return PyBoolType()
    return PyObjType()


def _safe(s: str) -> str:
    """Lean-safe identifier."""
    if not s:
        return "anon"
    out = []
    for ch in s:
        if ch.isalnum() or ch == "_":
            out.append(ch)
        else:
            out.append("_")
    s2 = "".join(out)
    if s2 and s2[0].isdigit():
        s2 = "i" + s2
    s2 = re.sub(r"_+", "_", s2)
    return s2.strip("_") or "anon"


# ─────────────────────────────────────────────────────────────────────
#  Public API
# ─────────────────────────────────────────────────────────────────────

def parse_psdl(
    source: str,
) -> tuple[Optional[ast.Module], list[PSDLError]]:
    """Parse PSDL source as a Python module."""
    src = source
    try:
        tree = ast.parse(src, mode="exec")
        return tree, []
    except SyntaxError as e:
        return None, [PSDLError(
            line_no=e.lineno or 0,
            line_text=e.text or "",
            message=f"syntax error: {e.msg}",
        )]


def compile_psdl(
    source: str,
    *,
    foundations: dict | None = None,
    ctx: Context | None = None,
) -> PSDLCompileResult:
    """Parse + compile a PSDL block into a deppy ProofTerm + Lean tactic.

    The source is a Python module whose top-level statements are
    PSDL tactics (Python-shaped).  Each statement is mapped to a
    deppy ProofTerm subclass and a Lean tactic line; the whole
    block is chained into a single Cut-rooted ProofTerm and a
    single Lean tactic block.
    """
    tree, parse_errors = parse_psdl(source)
    if tree is None:
        return PSDLCompileResult(
            errors=parse_errors,
            term_repr="parse failed",
        )
    comp = _Compiler(
        foundations=foundations or {},
        ctx=ctx or Context(),
    )
    try:
        proof_term = comp.compile_block(tree.body, indent=1)
    except Exception as e:  # pragma: no cover
        return PSDLCompileResult(
            errors=[PSDLError(
                line_no=0, line_text="",
                message=f"compiler error: {e}",
            )],
        )
    lean_tactic = "by\n" + "\n".join(comp.lean_lines)
    # Expose the cubical heap+effect snapshot.
    effect_seq = [
        (e.line_no, e.kind, e.locator) for e in comp._effects
    ]
    return PSDLCompileResult(
        proof_term=proof_term,
        lean_tactic=lean_tactic,
        term_repr=_short_repr(proof_term),
        errors=parse_errors + comp.errors,
        hints=comp.hints,
        show_goal_requested=comp.show_goal_requested,
        foundations_referenced=list(set(comp.foundations_referenced)),
        final_epoch=comp._world.epoch,
        effect_sequence=effect_seq,
    )


def _short_repr(pt: ProofTerm, depth: int = 0) -> str:
    cls = type(pt).__name__
    if depth > 5:
        return f"{cls}(…)"
    if isinstance(pt, AxiomInvocation):
        return f"AxiomInvocation({pt.name})"
    if isinstance(pt, Refl):
        return "Refl"
    if isinstance(pt, Cong):
        return f"Cong({pt.func}, {_short_repr(pt.proof, depth+1)})"
    if isinstance(pt, Unfold):
        inner = _short_repr(pt.proof, depth+1) if pt.proof else "_"
        return f"Unfold({pt.func_name}, {inner})"
    if isinstance(pt, Cut):
        return (
            f"Cut({pt.hyp_name}, "
            f"{_short_repr(pt.lemma_proof, depth+1)}, "
            f"{_short_repr(pt.body_proof, depth+1)})"
        )
    if isinstance(pt, Cases):
        return f"Cases({pt.scrutinee}, {len(pt.branches)} branches)"
    if isinstance(pt, Fiber):
        return f"Fiber({pt.scrutinee}, {len(pt.type_branches)} fibres)"
    if isinstance(pt, Structural):
        return f"Structural({pt.description!r})"
    if isinstance(pt, EffectWitness):
        return f"EffectWitness({pt.effect}, {_short_repr(pt.proof, depth+1)})"
    if isinstance(pt, ConditionalEffectWitness):
        return f"CondEffectWitness({pt.effect}, target={pt.target})"
    if isinstance(pt, Z3Proof):
        return f"Z3({pt.formula[:40]})"
    if isinstance(pt, ListInduction):
        return (
            f"ListInduction({pt.var}, "
            f"nil={_short_repr(pt.nil_proof, depth+1)}, "
            f"cons={_short_repr(pt.cons_proof, depth+1)})"
        )
    if isinstance(pt, NatInduction):
        return f"NatInduction({pt.var}, …)"
    if isinstance(pt, TransportProof):
        return f"TransportProof({_short_repr(pt.path_proof, depth+1)}, …)"
    if isinstance(pt, FunExt):
        return f"FunExt({pt.var}, {_short_repr(pt.pointwise_proof, depth+1)})"
    if isinstance(pt, LeanProof):
        return f"LeanProof({pt.proof_script[:30]!r})"
    return f"{cls}(…)"


__all__ = [
    "PSDLError",
    "PSDLCompileResult",
    "parse_psdl",
    "compile_psdl",
]
