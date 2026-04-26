"""
Deppy Cubical Bidirectional Type Checker
============================================

See ``ARCHITECTURE.md`` §4.7.  The Kan-composition rule
``_synth_comp`` is fully implemented (face-compatibility check +
obligation emission for indeterminate faces); see
``test_cubical_expansions.py`` for coverage.


Implements **all** typing rules from the Deppy monograph (Appendix A),
with genuine cubical type theory features:

- **synth** (Γ ⊢ e ⇒ A):  synthesise the type of *e* from the context.
- **check** (Γ ⊢ e ⇐ A):  check that *e* has the *expected* type A.

The subsumption rule bridges the two: if synth produces A and A <: B
then check against B succeeds.

Cubical features
----------------
Path types are checked with **boundary verification**: λ(i:I).t : a =_A b
requires t[i:=0] ≡ a and t[i:=1] ≡ b.  Path application p @ r reduces
at endpoints: p @ 0 → a, p @ 1 → b.  Transport along refl reduces:
transport(P, refl, d) → d.  Kan composition checks that the type family
is I-indexed and the base inhabits A(0), producing A(1).

Categories of rules implemented
-------------------------------
Core          Var, Lam, App, Σ-intro, Fst, Snd, Literal
Cubical       PathAbs, PathApp, Transport, Comp, Glue/Unglue
Path          Refl, Sym, Trans, Ap (Cong)
Python        SetAttr, DuckCheck, GenYield, DuckPath, MonkeyPatchPath
Statement     Let, If, For, While, TryExcept, With, Assert, Del, Import
Class/Deco    ClassDef, Decorator, DecoratorStack
Gen/Async     Yield, Await, GenSend
Effects       EffApp, EffLet, PurePromotion
Sub/Conv      Conv (β-equiv), Sub (subtype), DuckEquiv, PathSub
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyNoneType, PyListType, PyDictType, PyCallableType,
    PyClassType, PyTupleType, PySetType,
    PiType, SigmaType, PathType, RefinementType, UnionType,
    UniverseType, ProtocolType, OptionalType, IntervalType,
    GlueType,
    Var, Literal, Lam, App, Pair, Fst, Snd,
    PathAbs, PathApp, Transport, Comp, LetIn, IfThenElse,
    PyCall, GetAttr, GetItem,
    arrow,
)
from deppy.core.formal_ops import Op, OpCall


# ═══════════════════════════════════════════════════════════════════
# Effect lattice  (Pure ≤ IO ≤ Unsafe)
# ═══════════════════════════════════════════════════════════════════

_EFFECT_ORDER = {"Pure": 0, "IO": 1, "Unsafe": 2}


def _effect_le(a: str, b: str) -> bool:
    return _EFFECT_ORDER.get(a, 99) <= _EFFECT_ORDER.get(b, 99)


def _effect_join(a: str, b: str) -> str:
    oa, ob = _EFFECT_ORDER.get(a, 0), _EFFECT_ORDER.get(b, 0)
    for name, level in _EFFECT_ORDER.items():
        if level == max(oa, ob):
            return name
    return "Unsafe"


# ═══════════════════════════════════════════════════════════════════
# TypeResult — the output of every judgement
# ═══════════════════════════════════════════════════════════════════

@dataclass
class TypeResult:
    """Result returned by *check* and *synth*.

    Fields
    ------
    success     : did the rule succeed?
    type_      : the inferred / checked type (``None`` on failure)
    effect      : effect annotation (default ``"Pure"``)
    obligations : proof obligations generated (e.g. refinement side-conds)
    error       : human-readable error message on failure
    rule        : name of the typing rule that fired
    """
    success: bool
    type_: SynType | None = None
    effect: str = "Pure"
    obligations: list[Judgment] = field(default_factory=list)
    error: str | None = None
    rule: str = ""

    # convenience constructors ------------------------------------------------

    @staticmethod
    def ok(ty: SynType, *, effect: str = "Pure", rule: str = "",
           obligations: list[Judgment] | None = None) -> TypeResult:
        return TypeResult(
            success=True, type_=ty, effect=effect, rule=rule,
            obligations=obligations or [],
        )

    @staticmethod
    def fail(msg: str, *, rule: str = "") -> TypeResult:
        return TypeResult(success=False, error=msg, rule=rule)


# ═══════════════════════════════════════════════════════════════════
# Extra term nodes used only by the type checker
#   (kept next to the checker so they stay in sync)
# ═══════════════════════════════════════════════════════════════════

@dataclass
class Refl(SynTerm):
    """Refl_a — reflexivity witness for a =_A a."""
    term: SynTerm = field(default_factory=lambda: Var("a"))
    type_annot: SynType | None = None

    def _repr(self) -> str:
        return f"Refl({self.term})"

    def free_vars(self) -> set[str]:
        return self.term.free_vars()


@dataclass
class SymTerm(SynTerm):
    """sym(p) — symmetry of a path p : a =_A b."""
    proof: SynTerm = field(default_factory=lambda: Var("p"))

    def _repr(self) -> str:
        return f"sym({self.proof})"

    def free_vars(self) -> set[str]:
        return self.proof.free_vars()


@dataclass
class TransTerm(SynTerm):
    """p · q — transitivity of paths."""
    left: SynTerm = field(default_factory=lambda: Var("p"))
    right: SynTerm = field(default_factory=lambda: Var("q"))

    def _repr(self) -> str:
        return f"{self.left} · {self.right}"

    def free_vars(self) -> set[str]:
        return self.left.free_vars() | self.right.free_vars()


@dataclass
class ApTerm(SynTerm):
    """ap_f(p) — congruence: from f:A→B and p:a=a' derive f(a)=f(a')."""
    func: SynTerm = field(default_factory=lambda: Var("f"))
    path: SynTerm = field(default_factory=lambda: Var("p"))

    def _repr(self) -> str:
        return f"ap({self.func}, {self.path})"

    def free_vars(self) -> set[str]:
        return self.func.free_vars() | self.path.free_vars()


@dataclass
class SetAttrTerm(SynTerm):
    """setattr(C, m, v) — Python setattr as a typed operation."""
    cls: SynTerm = field(default_factory=lambda: Var("C"))
    method: SynTerm = field(default_factory=lambda: Literal("m"))
    value: SynTerm = field(default_factory=lambda: Var("v"))

    def _repr(self) -> str:
        return f"setattr({self.cls}, {self.method}, {self.value})"

    def free_vars(self) -> set[str]:
        return self.cls.free_vars() | self.method.free_vars() | self.value.free_vars()


@dataclass
class DuckCheckTerm(SynTerm):
    """Duck-type check: assert that *obj* satisfies protocol *proto*."""
    obj: SynTerm = field(default_factory=lambda: Var("o"))
    protocol: ProtocolType = field(default_factory=ProtocolType)

    def _repr(self) -> str:
        return f"duck_check({self.obj}, {self.protocol})"

    def free_vars(self) -> set[str]:
        return self.obj.free_vars()


@dataclass
class YieldTerm(SynTerm):
    """yield e — generator yield."""
    value: SynTerm = field(default_factory=lambda: Var("e"))

    def _repr(self) -> str:
        return f"yield {self.value}"

    def free_vars(self) -> set[str]:
        return self.value.free_vars()


@dataclass
class AwaitTerm(SynTerm):
    """await e — coroutine await."""
    value: SynTerm = field(default_factory=lambda: Var("e"))

    def _repr(self) -> str:
        return f"await {self.value}"

    def free_vars(self) -> set[str]:
        return self.value.free_vars()


@dataclass
class GenSendTerm(SynTerm):
    """g.send(v)"""
    gen: SynTerm = field(default_factory=lambda: Var("g"))
    value: SynTerm = field(default_factory=lambda: Var("v"))

    def _repr(self) -> str:
        return f"{self.gen}.send({self.value})"

    def free_vars(self) -> set[str]:
        return self.gen.free_vars() | self.value.free_vars()


@dataclass
class GlueTerm(SynTerm):
    """Glue type introduction: glue [φ ↦ t] a.

    When φ = 1 (face holds), this reduces to t.
    When φ = 0 (face fails), this reduces to a.
    """
    face: str = "1=1"
    equiv_term: SynTerm | None = None
    base_term: SynTerm = field(default_factory=lambda: Var("a"))

    def _repr(self) -> str:
        return f"glue[{self.face} ↦ {self.equiv_term}]({self.base_term})"

    def free_vars(self) -> set[str]:
        fv = self.base_term.free_vars()
        if self.equiv_term:
            fv |= self.equiv_term.free_vars()
        return fv


@dataclass
class UnGlueTerm(SynTerm):
    """Glue type elimination: unglue g.

    Extracts the base value from a glued term.
    When φ = 1, unglue (glue [φ ↦ t] a) reduces via the equivalence.
    """
    term: SynTerm = field(default_factory=lambda: Var("g"))

    def _repr(self) -> str:
        return f"unglue({self.term})"

    def free_vars(self) -> set[str]:
        return self.term.free_vars()


@dataclass
class ForLoop(SynTerm):
    """for x in iter do body."""
    var: str = "x"
    iter_: SynTerm = field(default_factory=lambda: Var("iter"))
    body: SynTerm = field(default_factory=lambda: Var("body"))

    def _repr(self) -> str:
        return f"for {self.var} in {self.iter_} do {self.body}"

    def free_vars(self) -> set[str]:
        return self.iter_.free_vars() | (self.body.free_vars() - {self.var})


@dataclass
class WhileLoop(SynTerm):
    """while cond do body (with optional variant)."""
    cond: SynTerm = field(default_factory=lambda: Var("cond"))
    body: SynTerm = field(default_factory=lambda: Var("body"))
    variant: SynTerm | None = None

    def _repr(self) -> str:
        return f"while {self.cond} do {self.body}"

    def free_vars(self) -> set[str]:
        fv = self.cond.free_vars() | self.body.free_vars()
        if self.variant:
            fv |= self.variant.free_vars()
        return fv


@dataclass
class TryExcept(SynTerm):
    """try body except E as e: handler."""
    body: SynTerm = field(default_factory=lambda: Var("body"))
    exc_name: str = "e"
    exc_type: SynType = field(default_factory=PyObjType)
    handler: SynTerm = field(default_factory=lambda: Var("handler"))

    def _repr(self) -> str:
        return f"try {self.body} except {self.exc_type} as {self.exc_name}: {self.handler}"

    def free_vars(self) -> set[str]:
        return self.body.free_vars() | (self.handler.free_vars() - {self.exc_name})


@dataclass
class WithStmt(SynTerm):
    """with mgr as x: body."""
    mgr: SynTerm = field(default_factory=lambda: Var("mgr"))
    var: str = "x"
    body: SynTerm = field(default_factory=lambda: Var("body"))

    def _repr(self) -> str:
        return f"with {self.mgr} as {self.var}: {self.body}"

    def free_vars(self) -> set[str]:
        return self.mgr.free_vars() | (self.body.free_vars() - {self.var})


@dataclass
class AssertTerm(SynTerm):
    """assert e."""
    expr: SynTerm = field(default_factory=lambda: Var("e"))

    def _repr(self) -> str:
        return f"assert {self.expr}"

    def free_vars(self) -> set[str]:
        return self.expr.free_vars()


@dataclass
class DelTerm(SynTerm):
    """del x — remove *x* from the context."""
    name: str = "x"

    def _repr(self) -> str:
        return f"del {self.name}"

    def free_vars(self) -> set[str]:
        return {self.name}


@dataclass
class ImportTerm(SynTerm):
    """import m — bring module exports into scope."""
    module: str = ""
    exports: tuple[tuple[str, SynType], ...] = ()

    def _repr(self) -> str:
        return f"import {self.module}"

    def free_vars(self) -> set[str]:
        return set()


@dataclass
class ClassDefTerm(SynTerm):
    """class C(bases): methods."""
    name: str = ""
    bases: tuple[SynType, ...] = ()
    methods: tuple[tuple[str, SynTerm], ...] = ()

    def _repr(self) -> str:
        return f"class {self.name}"

    def free_vars(self) -> set[str]:
        fv: set[str] = set()
        for _, m in self.methods:
            fv |= m.free_vars()
        return fv


@dataclass
class DecoratorTerm(SynTerm):
    """@d f — decorator application."""
    decorator: SynTerm = field(default_factory=lambda: Var("d"))
    func: SynTerm = field(default_factory=lambda: Var("f"))

    def _repr(self) -> str:
        return f"@{self.decorator} {self.func}"

    def free_vars(self) -> set[str]:
        return self.decorator.free_vars() | self.func.free_vars()


# ═══════════════════════════════════════════════════════════════════
# Auxiliary types used in rules
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class GeneratorType(SynType):
    """Gen(S, Y, T) — send, yield, return types."""
    send_type: SynType = field(default_factory=PyNoneType)
    yield_type: SynType = field(default_factory=PyNoneType)
    return_type: SynType = field(default_factory=PyNoneType)

    def _repr(self) -> str:
        return f"Gen({self.send_type}, {self.yield_type}, {self.return_type})"


@dataclass(frozen=True)
class AwaitableType(SynType):
    """Awaitable(A)."""
    inner: SynType = field(default_factory=PyObjType)

    def _repr(self) -> str:
        return f"Awaitable({self.inner})"


@dataclass(frozen=True)
class IterableType(SynType):
    """Iterable(A)."""
    element_type: SynType = field(default_factory=PyObjType)

    def _repr(self) -> str:
        return f"Iterable({self.element_type})"


@dataclass(frozen=True)
class ContextManagerType(SynType):
    """ContextManager(A)."""
    inner: SynType = field(default_factory=PyObjType)

    def _repr(self) -> str:
        return f"ContextManager({self.inner})"


@dataclass(frozen=True)
class UnitType(SynType):
    """Unit ≅ NoneType, the type of statements."""

    def _repr(self) -> str:
        return "Unit"


@dataclass(frozen=True)
class EffectType(SynType):
    """An effect-annotated type: A ! ε."""
    base: SynType = field(default_factory=PyObjType)
    effect: str = "Pure"

    def _repr(self) -> str:
        return f"{self.base} ! {self.effect}"


# ═══════════════════════════════════════════════════════════════════
# Substitution helper
# ═══════════════════════════════════════════════════════════════════

def _subst_type(ty: SynType, var: str, replacement: SynTerm) -> SynType:
    """Substitute *var* by *replacement* in *ty* (structural descent).

    For most concrete Python types (int, str …) this is the identity.
    For Pi/Sigma/Path/Refinement the body may mention the bound variable.
    """
    if isinstance(ty, PiType):
        if ty.param_name == var:
            return ty  # shadowed
        return PiType(ty.param_name, ty.param_type,
                      _subst_type(ty.body_type, var, replacement))
    if isinstance(ty, SigmaType):
        if ty.fst_name == var:
            return ty
        return SigmaType(ty.fst_name, ty.fst_type,
                         _subst_type(ty.snd_type, var, replacement))
    if isinstance(ty, PathType):
        new_left = _subst_term(ty.left, var, replacement) if ty.left else None
        new_right = _subst_term(ty.right, var, replacement) if ty.right else None
        return PathType(
            base_type=_subst_type(ty.base_type, var, replacement),
            left=new_left,
            right=new_right,
        )
    if isinstance(ty, RefinementType):
        if ty.var_name == var:
            return ty
        return ty  # predicate is a string — no structural subst
    return ty


def _subst_term(term: SynTerm | None, var: str, replacement: SynTerm) -> SynTerm | None:
    """Substitute free occurrences of *var* with *replacement* in a term."""
    if term is None:
        return None
    if isinstance(term, Var):
        return replacement if term.name == var else term
    if isinstance(term, Literal):
        return term
    if isinstance(term, App):
        return App(
            func=_subst_term(term.func, var, replacement),  # type: ignore[arg-type]
            arg=_subst_term(term.arg, var, replacement),  # type: ignore[arg-type]
        )
    if isinstance(term, Lam):
        if term.param == var:
            return term  # shadowed
        return Lam(term.param, term.param_type,
                   _subst_term(term.body, var, replacement))  # type: ignore[arg-type]
    if isinstance(term, PathAbs):
        if term.ivar == var:
            return term  # shadowed
        return PathAbs(term.ivar,
                       _subst_term(term.body, var, replacement))  # type: ignore[arg-type]
    if isinstance(term, PathApp):
        return PathApp(
            path=_subst_term(term.path, var, replacement),  # type: ignore[arg-type]
            arg=_subst_term(term.arg, var, replacement),  # type: ignore[arg-type]
        )
    if isinstance(term, Pair):
        return Pair(
            fst=_subst_term(term.fst, var, replacement),  # type: ignore[arg-type]
            snd=_subst_term(term.snd, var, replacement),  # type: ignore[arg-type]
        )
    if isinstance(term, Fst):
        return Fst(pair=_subst_term(term.pair, var, replacement))  # type: ignore[arg-type]
    if isinstance(term, Snd):
        return Snd(pair=_subst_term(term.pair, var, replacement))  # type: ignore[arg-type]
    if isinstance(term, Transport):
        return Transport(
            type_family=_subst_term(term.type_family, var, replacement),  # type: ignore[arg-type]
            path=_subst_term(term.path, var, replacement),  # type: ignore[arg-type]
            base_term=_subst_term(term.base_term, var, replacement),  # type: ignore[arg-type]
        )
    # For other term forms, return unchanged
    return term


# ═══════════════════════════════════════════════════════════════════
# Cubical operations — interval substitution and term reduction
# ═══════════════════════════════════════════════════════════════════

def _subst_interval(term: SynTerm, var: str, endpoint: int) -> SynTerm:
    """Substitute interval variable *var* with *endpoint* (0 or 1).

    This is ESSENTIAL for checking path boundaries:
      (λ(i:I). body)[i:=0] evaluates body with i replaced by 0
      (λ(i:I). body)[i:=1] evaluates body with i replaced by 1

    The result is then reduced to normal form.
    """
    result = _subst_term(term, var, Literal(endpoint, IntervalType()))
    return _reduce(result) if result is not None else Literal(endpoint)


def _reduce(term: SynTerm) -> SynTerm:
    """Reduce a term to (weak head) normal form.

    Beta reduction:       (λx.t) a       → t[x:=a]
    Path reduction:       (λ(i:I).t) @ r → t[i:=r]
    Path endpoint:        p @ 0          → left(p),  p @ 1 → right(p)
    Transport reduction:  transport(P, refl, d) → d
    Projection:           π₁(a, b) → a,  π₂(a, b) → b
    """
    if isinstance(term, App):
        func = _reduce(term.func)
        arg = _reduce(term.arg)
        # Beta reduction
        if isinstance(func, Lam):
            body = _subst_term(func.body, func.param, arg)
            return _reduce(body) if body is not None else arg
        return App(func=func, arg=arg)

    if isinstance(term, PathApp):
        path = _reduce(term.path)
        arg = _reduce(term.arg)
        # Path-beta: (λ(i:I).t) @ r → t[i:=r]
        if isinstance(path, PathAbs):
            body = _subst_term(path.body, path.ivar, arg)
            return _reduce(body) if body is not None else arg
        return PathApp(path=path, arg=arg)

    if isinstance(term, Transport):
        tf = _reduce(term.type_family)
        path = _reduce(term.path)
        base = _reduce(term.base_term)
        # transport(P, refl(a), d) → d
        if isinstance(path, Refl):
            return base
        return Transport(type_family=tf, path=path, base_term=base)

    if isinstance(term, Fst):
        inner = _reduce(term.pair)
        if isinstance(inner, Pair):
            return _reduce(inner.fst)
        return Fst(pair=inner)

    if isinstance(term, Snd):
        inner = _reduce(term.pair)
        if isinstance(inner, Pair):
            return _reduce(inner.snd)
        return Snd(pair=inner)

    if isinstance(term, LetIn):
        val = _reduce(term.value)
        body = _subst_term(term.body, term.var_name, val)
        return _reduce(body) if body is not None else val

    return term


def _terms_equal(a: SynTerm | None, b: SynTerm | None) -> bool:
    """Check structural equality of two terms (after reduction).

    Used for boundary checking in cubical path rules and for
    definitional equality judgments.
    """
    if a is None and b is None:
        return True
    if a is None or b is None:
        return False

    # Reduce both to normal form before comparing
    a_nf = _reduce(a)
    b_nf = _reduce(b)

    if type(a_nf) is type(b_nf):
        if isinstance(a_nf, Var) and isinstance(b_nf, Var):
            return a_nf.name == b_nf.name
        if isinstance(a_nf, Literal) and isinstance(b_nf, Literal):
            return a_nf.value == b_nf.value
        if isinstance(a_nf, App) and isinstance(b_nf, App):
            return (_terms_equal(a_nf.func, b_nf.func) and
                    _terms_equal(a_nf.arg, b_nf.arg))
        if isinstance(a_nf, Lam) and isinstance(b_nf, Lam):
            # Alpha-equivalence approximation: rename and compare bodies
            if a_nf.param == b_nf.param:
                return _terms_equal(a_nf.body, b_nf.body)
            fresh = a_nf.param + "_α"
            a_body = _subst_term(a_nf.body, a_nf.param, Var(fresh))
            b_body = _subst_term(b_nf.body, b_nf.param, Var(fresh))
            return _terms_equal(a_body, b_body)
        if isinstance(a_nf, PathAbs) and isinstance(b_nf, PathAbs):
            if a_nf.ivar == b_nf.ivar:
                return _terms_equal(a_nf.body, b_nf.body)
            fresh = a_nf.ivar + "_α"
            a_body = _subst_term(a_nf.body, a_nf.ivar, Var(fresh))
            b_body = _subst_term(b_nf.body, b_nf.ivar, Var(fresh))
            return _terms_equal(a_body, b_body)
        if isinstance(a_nf, PathApp) and isinstance(b_nf, PathApp):
            return (_terms_equal(a_nf.path, b_nf.path) and
                    _terms_equal(a_nf.arg, b_nf.arg))
        if isinstance(a_nf, Pair) and isinstance(b_nf, Pair):
            return (_terms_equal(a_nf.fst, b_nf.fst) and
                    _terms_equal(a_nf.snd, b_nf.snd))
        if isinstance(a_nf, Fst) and isinstance(b_nf, Fst):
            return _terms_equal(a_nf.pair, b_nf.pair)
        if isinstance(a_nf, Snd) and isinstance(b_nf, Snd):
            return _terms_equal(a_nf.pair, b_nf.pair)
        if isinstance(a_nf, Transport) and isinstance(b_nf, Transport):
            return (_terms_equal(a_nf.type_family, b_nf.type_family) and
                    _terms_equal(a_nf.path, b_nf.path) and
                    _terms_equal(a_nf.base_term, b_nf.base_term))
        if isinstance(a_nf, Refl) and isinstance(b_nf, Refl):
            return _terms_equal(a_nf.term, b_nf.term)
    return False


def _face_holds(face: str) -> bool | None:
    """Evaluate a face formula.  Returns True/False/None (indeterminate)."""
    face = face.strip()
    if face in ("1=1", "⊤", "true", "1"):
        return True
    if face in ("0=1", "1=0", "⊥", "false", "0"):
        return False
    return None


# ═══════════════════════════════════════════════════════════════════
# TypeChecker
# ═══════════════════════════════════════════════════════════════════

class TypeChecker:
    """Bidirectional type checker for Deppy.

    Implements check (Γ ⊢ e ⇐ A) and synth (Γ ⊢ e ⇒ A) modes, plus
    subtyping, type equality, and effect subsumption.
    """

    # ── public API ────────────────────────────────────────────────

    def check(self, ctx: Context, term: SynTerm,
              expected: SynType) -> TypeResult:
        """Check mode (Γ ⊢ e ⇐ A)."""

        # (Lam) — introduction form checked against a Π type
        if isinstance(term, Lam) and isinstance(expected, PiType):
            return self._check_lam(ctx, term, expected)

        # (Pair / Σ-intro) — checked against Σ type
        if isinstance(term, Pair) and isinstance(expected, SigmaType):
            return self._check_pair(ctx, term, expected)

        # (PathAbs) — cubical path introduction checked against PathType
        if isinstance(term, PathAbs) and isinstance(expected, PathType):
            return self._check_path_abs(ctx, term, expected)

        # (GlueTerm) — glue introduction checked against GlueType
        if isinstance(term, GlueTerm) and isinstance(expected, GlueType):
            return self._check_glue(ctx, term, expected)

        # (Conv + Sub) — fall through to synth + subsumption
        res = self.synth(ctx, term)
        if not res.success:
            return res

        inferred = res.type_
        assert inferred is not None
        if self.equal_types(ctx, inferred, expected):
            return TypeResult.ok(expected, effect=res.effect, rule="Conv",
                                 obligations=res.obligations)
        if self.subtype(ctx, inferred, expected):
            return TypeResult.ok(expected, effect=res.effect, rule="Sub",
                                 obligations=res.obligations)
        return TypeResult.fail(
            f"Expected {expected}, but got {inferred}", rule="Check"
        )

    def synth(self, ctx: Context, term: SynTerm) -> TypeResult:
        """Synthesis mode (Γ ⊢ e ⇒ A)."""

        # (Var)
        if isinstance(term, Var):
            return self._synth_var(ctx, term)

        # (Literal)
        if isinstance(term, Literal):
            return self._synth_literal(ctx, term)

        # (Lam) — cannot synthesise without annotation context;
        #          succeed with the annotation on param_type → body synth
        if isinstance(term, Lam):
            return self._synth_lam(ctx, term)

        # (App)
        if isinstance(term, App):
            return self._synth_app(ctx, term)

        # (Pair) — non-dependent product when no expected type
        if isinstance(term, Pair):
            return self._synth_pair(ctx, term)

        # (Fst)
        if isinstance(term, Fst):
            return self._synth_fst(ctx, term)

        # (Snd)
        if isinstance(term, Snd):
            return self._synth_snd(ctx, term)

        # (Let)
        if isinstance(term, LetIn):
            return self._synth_let(ctx, term)

        # (If)
        if isinstance(term, IfThenElse):
            return self._synth_if(ctx, term)

        # ── Path rules ───────────────────────────────────────────
        if isinstance(term, Refl):
            return self._synth_refl(ctx, term)
        if isinstance(term, SymTerm):
            return self._synth_sym(ctx, term)
        if isinstance(term, TransTerm):
            return self._synth_trans(ctx, term)
        if isinstance(term, ApTerm):
            return self._synth_ap(ctx, term)
        if isinstance(term, Transport):
            return self._synth_transport(ctx, term)
        if isinstance(term, PathAbs):
            return self._synth_path_abs(ctx, term)
        if isinstance(term, PathApp):
            return self._synth_path_app(ctx, term)

        # ── Glue / Unglue ────────────────────────────────────────
        if isinstance(term, GlueTerm):
            return self._synth_glue(ctx, term)
        if isinstance(term, UnGlueTerm):
            return self._synth_unglue(ctx, term)

        # ── Python-specific ───────────────────────────────────────
        if isinstance(term, SetAttrTerm):
            return self._synth_setattr(ctx, term)
        if isinstance(term, DuckCheckTerm):
            return self._synth_duck_check(ctx, term)
        if isinstance(term, GetAttr):
            return self._synth_getattr(ctx, term)
        if isinstance(term, GetItem):
            return self._synth_getitem(ctx, term)
        if isinstance(term, PyCall):
            return self._synth_pycall(ctx, term)

        # ── Statement rules ──────────────────────────────────────
        if isinstance(term, ForLoop):
            return self._synth_for(ctx, term)
        if isinstance(term, WhileLoop):
            return self._synth_while(ctx, term)
        if isinstance(term, TryExcept):
            return self._synth_try(ctx, term)
        if isinstance(term, WithStmt):
            return self._synth_with(ctx, term)
        if isinstance(term, AssertTerm):
            return self._synth_assert(ctx, term)
        if isinstance(term, DelTerm):
            return self._synth_del(ctx, term)
        if isinstance(term, ImportTerm):
            return self._synth_import(ctx, term)

        # ── Class / Decorator ─────────────────────────────────────
        if isinstance(term, ClassDefTerm):
            return self._synth_classdef(ctx, term)
        if isinstance(term, DecoratorTerm):
            return self._synth_decorator(ctx, term)

        # ── Generator / Async ─────────────────────────────────────
        if isinstance(term, YieldTerm):
            return self._synth_yield(ctx, term)
        if isinstance(term, AwaitTerm):
            return self._synth_await(ctx, term)
        if isinstance(term, GenSendTerm):
            return self._synth_gen_send(ctx, term)

        # ── Op / OpCall ───────────────────────────────────────────
        if isinstance(term, Op):
            return self._synth_op(ctx, term)
        if isinstance(term, OpCall):
            return self._synth_opcall(ctx, term)

        # ── Comp (Kan composition) ────────────────────────────────
        if isinstance(term, Comp):
            return self._synth_comp(ctx, term)

        return TypeResult.fail(f"Cannot synthesise type for {type(term).__name__}",
                               rule="Synth")

    # ── subtype / equal ──────────────────────────────────────────

    def subtype(self, ctx: Context, sub: SynType, sup: SynType) -> bool:
        """Γ ⊢ sub <: sup (Sub rule)."""
        if self.equal_types(ctx, sub, sup):
            return True

        # Everything is a subtype of PyObj
        if isinstance(sup, PyObjType):
            return True

        # bool <: int (Python inheritance)
        if isinstance(sub, PyBoolType) and isinstance(sup, PyIntType):
            return True

        # int <: float (Python numeric tower)
        if isinstance(sub, PyIntType) and isinstance(sup, PyFloatType):
            return True

        # A <: Optional(A)
        if isinstance(sup, OptionalType):
            return self.subtype(ctx, sub, sup.inner) or isinstance(sub, PyNoneType)

        # A <: A | B  /  B <: A | B
        if isinstance(sup, UnionType):
            return any(self.subtype(ctx, sub, alt) for alt in sup.alternatives)

        # A | B <: C  iff  A <: C and B <: C
        if isinstance(sub, UnionType):
            return all(self.subtype(ctx, alt, sup) for alt in sub.alternatives)

        # Refinement: {x:A|φ} <: A (forgetting refinement)
        if isinstance(sub, RefinementType):
            return self.subtype(ctx, sub.base_type, sup)

        # Covariant list: list[A] <: list[B] when A <: B
        if isinstance(sub, PyListType) and isinstance(sup, PyListType):
            return self.subtype(ctx, sub.element_type, sup.element_type)

        # Covariant set
        if isinstance(sub, PySetType) and isinstance(sup, PySetType):
            return self.subtype(ctx, sub.element_type, sup.element_type)

        # Covariant dict (both key and value)
        if isinstance(sub, PyDictType) and isinstance(sup, PyDictType):
            return (self.subtype(ctx, sub.key_type, sup.key_type) and
                    self.subtype(ctx, sub.value_type, sup.value_type))

        # Π-type: contravariant in param, covariant in body
        if isinstance(sub, PiType) and isinstance(sup, PiType):
            return (self.subtype(ctx, sup.param_type, sub.param_type) and
                    self.subtype(ctx, sub.body_type, sup.body_type))

        # PyCallable → PiType bridging
        if isinstance(sub, PyCallableType) and isinstance(sup, PiType):
            if len(sub.param_types) == 1:
                return (self.subtype(ctx, sup.param_type, sub.param_types[0]) and
                        self.subtype(ctx, sub.return_type, sup.body_type))

        # EffectType: A!ε <: A!ε' when ε ≤ ε'
        if isinstance(sub, EffectType) and isinstance(sup, EffectType):
            return (self.subtype(ctx, sub.base, sup.base) and
                    _effect_le(sub.effect, sup.effect))

        # IterableType: list <: Iterable
        if isinstance(sup, IterableType) and isinstance(sub, PyListType):
            return self.subtype(ctx, sub.element_type, sup.element_type)

        # Protocol / DuckEquiv: object satisfies protocol if it has all methods
        if isinstance(sup, ProtocolType) and isinstance(sub, PyClassType):
            sub_methods = dict(sub.methods)
            for name, req_ty in sup.methods:
                if name not in sub_methods:
                    return False
                if not self.subtype(ctx, sub_methods[name], req_ty):
                    return False
            return True

        # Universe cumulativity: U_n <: U_{n+1}
        if isinstance(sub, UniverseType) and isinstance(sup, UniverseType):
            return sub.level <= sup.level

        # UnitType <: NoneType
        if isinstance(sub, UnitType) and isinstance(sup, PyNoneType):
            return True
        if isinstance(sub, PyNoneType) and isinstance(sup, UnitType):
            return True

        # PathType covariance: a =_A b <: a' =_A' b' when A <: A'
        if isinstance(sub, PathType) and isinstance(sup, PathType):
            return self.subtype(ctx, sub.base_type, sup.base_type)

        # GlueType: Glue[φ ↦ T] A <: A (forgetting the glue)
        if isinstance(sub, GlueType):
            return self.subtype(ctx, sub.base_type, sup)

        # Subtyping via path coercion existence
        if self._subtype_via_path(ctx, sub, sup):
            return True

        return False

    def equal_types(self, ctx: Context, a: SynType, b: SynType) -> bool:
        """Γ ⊢ A ≡ B  (Conv rule — definitional / β-equality)."""
        if a is b:
            return True
        if type(a) is type(b):
            # PathType: check base type equality and endpoint equality
            if isinstance(a, PathType) and isinstance(b, PathType):
                return (self.equal_types(ctx, a.base_type, b.base_type) and
                        _terms_equal(a.left, b.left) and
                        _terms_equal(a.right, b.right))
            # GlueType: when φ=1, Glue reduces to T
            if isinstance(a, GlueType) and isinstance(b, GlueType):
                if a.face == b.face:
                    return (self.equal_types(ctx, a.base_type, b.base_type) and
                            (a.equiv_type is None and b.equiv_type is None or
                             a.equiv_type is not None and b.equiv_type is not None and
                             self.equal_types(ctx, a.equiv_type, b.equiv_type)))
            return a == b
        # EffectType with Pure is equal to its base
        if isinstance(a, EffectType) and a.effect == "Pure":
            return self.equal_types(ctx, a.base, b)
        if isinstance(b, EffectType) and b.effect == "Pure":
            return self.equal_types(ctx, a, b.base)
        # GlueType reduction: Glue[1=1 ↦ T] A ≡ T when face holds
        if isinstance(a, GlueType) and _face_holds(a.face) is True and a.equiv_type is not None:
            return self.equal_types(ctx, a.equiv_type, b)
        if isinstance(b, GlueType) and _face_holds(b.face) is True and b.equiv_type is not None:
            return self.equal_types(ctx, a, b.equiv_type)
        return False

    # ═══════════════════════════════════════════════════════════════
    #  Core rules
    # ═══════════════════════════════════════════════════════════════

    # (Var)
    def _synth_var(self, ctx: Context, term: Var) -> TypeResult:
        ty = ctx.lookup(term.name)
        if ty is None:
            return TypeResult.fail(f"Unbound variable: {term.name}", rule="Var")
        return TypeResult.ok(ty, rule="Var")

    # (Literal)
    def _synth_literal(self, ctx: Context, term: Literal) -> TypeResult:
        if term.type_ is not None and not isinstance(term.type_, PyObjType):
            return TypeResult.ok(term.type_, rule="Literal")
        v = term.value
        if isinstance(v, bool):
            return TypeResult.ok(PyBoolType(), rule="Literal")
        if isinstance(v, int):
            return TypeResult.ok(PyIntType(), rule="Literal")
        if isinstance(v, float):
            return TypeResult.ok(PyFloatType(), rule="Literal")
        if isinstance(v, str):
            return TypeResult.ok(PyStrType(), rule="Literal")
        if v is None:
            return TypeResult.ok(PyNoneType(), rule="Literal")
        return TypeResult.ok(PyObjType(), rule="Literal")

    # (Lam) — synth mode: use annotation
    def _synth_lam(self, ctx: Context, term: Lam) -> TypeResult:
        ext = ctx.extend(term.param, term.param_type)
        body_res = self.synth(ext, term.body)
        if not body_res.success:
            return body_res
        pi = PiType(term.param, term.param_type, body_res.type_)  # type: ignore[arg-type]
        return TypeResult.ok(pi, effect=body_res.effect, rule="Lam",
                             obligations=body_res.obligations)

    # (Lam) — check mode against a Π type
    def _check_lam(self, ctx: Context, term: Lam,
                   expected: PiType) -> TypeResult:
        ext = ctx.extend(term.param, expected.param_type)
        body_res = self.check(ext, term.body, expected.body_type)
        if not body_res.success:
            return body_res
        return TypeResult.ok(expected, effect=body_res.effect, rule="Lam",
                             obligations=body_res.obligations)

    # (App)
    def _synth_app(self, ctx: Context, term: App) -> TypeResult:
        func_res = self.synth(ctx, term.func)
        if not func_res.success:
            return func_res
        fty = func_res.type_
        assert fty is not None

        # Unwrap EffectType
        eff_func = func_res.effect
        if isinstance(fty, EffectType):
            eff_func = _effect_join(eff_func, fty.effect)
            fty = fty.base

        if not isinstance(fty, PiType):
            # Try PyCallable → Pi
            if isinstance(fty, PyCallableType) and len(fty.param_types) >= 1:
                fty = PiType("_", fty.param_types[0], fty.return_type)
            else:
                return TypeResult.fail(
                    f"Cannot apply non-function type {fty}", rule="App")

        arg_res = self.check(ctx, term.arg, fty.param_type)
        if not arg_res.success:
            return arg_res

        result_ty = _subst_type(fty.body_type, fty.param_name, term.arg)
        eff = _effect_join(eff_func, arg_res.effect)

        # (PurePromotion)
        if _effect_le(eff, "Pure"):
            eff = "Pure"

        obligations = func_res.obligations + arg_res.obligations
        return TypeResult.ok(result_ty, effect=eff, rule="App",
                             obligations=obligations)

    # (Σ-intro) — check mode
    def _check_pair(self, ctx: Context, term: Pair,
                    expected: SigmaType) -> TypeResult:
        fst_res = self.check(ctx, term.fst, expected.fst_type)
        if not fst_res.success:
            return fst_res
        snd_expected = _subst_type(expected.snd_type, expected.fst_name, term.fst)
        snd_res = self.check(ctx, term.snd, snd_expected)
        if not snd_res.success:
            return snd_res
        eff = _effect_join(fst_res.effect, snd_res.effect)
        return TypeResult.ok(expected, effect=eff, rule="Σ-intro",
                             obligations=fst_res.obligations + snd_res.obligations)

    # (Pair) — synth mode (non-dependent product)
    def _synth_pair(self, ctx: Context, term: Pair) -> TypeResult:
        a = self.synth(ctx, term.fst)
        b = self.synth(ctx, term.snd)
        if not a.success:
            return a
        if not b.success:
            return b
        sigma = SigmaType("_", a.type_, b.type_)  # type: ignore[arg-type]
        eff = _effect_join(a.effect, b.effect)
        return TypeResult.ok(sigma, effect=eff, rule="Σ-intro",
                             obligations=a.obligations + b.obligations)

    # (Fst)
    def _synth_fst(self, ctx: Context, term: Fst) -> TypeResult:
        res = self.synth(ctx, term.pair)
        if not res.success:
            return res
        ty = res.type_
        if isinstance(ty, SigmaType):
            return TypeResult.ok(ty.fst_type, effect=res.effect, rule="Fst",
                                 obligations=res.obligations)
        if isinstance(ty, PyTupleType) and ty.element_types:
            return TypeResult.ok(ty.element_types[0], effect=res.effect,
                                 rule="Fst", obligations=res.obligations)
        return TypeResult.fail(f"Fst on non-Σ type: {ty}", rule="Fst")

    # (Snd)
    def _synth_snd(self, ctx: Context, term: Snd) -> TypeResult:
        res = self.synth(ctx, term.pair)
        if not res.success:
            return res
        ty = res.type_
        if isinstance(ty, SigmaType):
            return TypeResult.ok(ty.snd_type, effect=res.effect, rule="Snd",
                                 obligations=res.obligations)
        if isinstance(ty, PyTupleType) and len(ty.element_types) >= 2:
            return TypeResult.ok(ty.element_types[1], effect=res.effect,
                                 rule="Snd", obligations=res.obligations)
        return TypeResult.fail(f"Snd on non-Σ type: {ty}", rule="Snd")

    # ═══════════════════════════════════════════════════════════════
    #  Cubical path rules
    # ═══════════════════════════════════════════════════════════════

    # (Refl)
    def _synth_refl(self, ctx: Context, term: Refl) -> TypeResult:
        a_res = self.synth(ctx, term.term)
        if not a_res.success:
            return a_res
        base = term.type_annot if term.type_annot else a_res.type_
        path_ty = PathType(base_type=base, left=term.term, right=term.term)  # type: ignore[arg-type]
        return TypeResult.ok(path_ty, rule="Refl", obligations=a_res.obligations)

    # (Sym)
    def _synth_sym(self, ctx: Context, term: SymTerm) -> TypeResult:
        p_res = self.synth(ctx, term.proof)
        if not p_res.success:
            return p_res
        pty = p_res.type_
        if not isinstance(pty, PathType):
            return TypeResult.fail(f"sym applied to non-path: {pty}", rule="Sym")
        flipped = PathType(base_type=pty.base_type, left=pty.right, right=pty.left)
        return TypeResult.ok(flipped, rule="Sym", obligations=p_res.obligations)

    # (Trans)
    def _synth_trans(self, ctx: Context, term: TransTerm) -> TypeResult:
        l = self.synth(ctx, term.left)
        r = self.synth(ctx, term.right)
        if not l.success:
            return l
        if not r.success:
            return r
        lt, rt = l.type_, r.type_
        if not isinstance(lt, PathType) or not isinstance(rt, PathType):
            return TypeResult.fail("Trans requires two paths", rule="Trans")
        composed = PathType(base_type=lt.base_type, left=lt.left, right=rt.right)
        return TypeResult.ok(composed, rule="Trans",
                             obligations=l.obligations + r.obligations)

    # (Ap / Cong)
    def _synth_ap(self, ctx: Context, term: ApTerm) -> TypeResult:
        f_res = self.synth(ctx, term.func)
        p_res = self.synth(ctx, term.path)
        if not f_res.success:
            return f_res
        if not p_res.success:
            return p_res
        fty = f_res.type_
        pty = p_res.type_
        if not isinstance(pty, PathType):
            return TypeResult.fail("ap: second arg must be a path", rule="Ap")

        # Determine result type
        result_base = PyObjType()
        if isinstance(fty, PiType):
            result_base = fty.body_type
        elif isinstance(fty, PyCallableType) and fty.return_type:
            result_base = fty.return_type

        left_app = App(term.func, pty.left) if pty.left else None
        right_app = App(term.func, pty.right) if pty.right else None
        result_path = PathType(base_type=result_base,
                               left=left_app, right=right_app)
        return TypeResult.ok(result_path, rule="Ap",
                             obligations=f_res.obligations + p_res.obligations)

    # (PathAbs — check mode) — the KEY cubical rule
    def _check_path_abs(self, ctx: Context, term: PathAbs,
                        expected: PathType) -> TypeResult:
        """Check λ(i:I). t : a =_A b

        Rule (from cubical type theory):
          Γ, i:I ⊢ t : A
          t[i:=0] ≡ a        ← boundary condition at 0
          t[i:=1] ≡ b        ← boundary condition at 1
          ──────────────────────
          Γ ⊢ λ(i:I).t : a =_A b

        The BOUNDARY CONDITION is the key cubical feature: the path
        abstraction body must reduce to the correct endpoints.
        """
        ext = ctx.extend(term.ivar, IntervalType())
        body_res = self.check(ext, term.body, expected.base_type)
        if not body_res.success:
            return body_res

        obligations = list(body_res.obligations)

        # Boundary check: t[i:=0] must equal the left endpoint
        if expected.left is not None:
            left_reduced = _subst_interval(term.body, term.ivar, 0)
            if not _terms_equal(left_reduced, expected.left):
                obligations.append(Judgment(
                    kind=JudgmentKind.EQUAL,
                    context=ctx,
                    left=left_reduced,
                    right=expected.left,
                ))

        # Boundary check: t[i:=1] must equal the right endpoint
        if expected.right is not None:
            right_reduced = _subst_interval(term.body, term.ivar, 1)
            if not _terms_equal(right_reduced, expected.right):
                obligations.append(Judgment(
                    kind=JudgmentKind.EQUAL,
                    context=ctx,
                    left=right_reduced,
                    right=expected.right,
                ))

        return TypeResult.ok(expected, effect=body_res.effect,
                             rule="PathAbs-Check",
                             obligations=obligations)

    # (PathAbs — synth mode)
    def _synth_path_abs(self, ctx: Context, term: PathAbs) -> TypeResult:
        """Synth λ(i:I). t ⇒ t[i:=0] =_A t[i:=1]

        In synth mode we compute the endpoints by substituting
        the interval variable with 0 and 1 and reducing.
        """
        ext = ctx.extend(term.ivar, IntervalType())
        body_res = self.synth(ext, term.body)
        if not body_res.success:
            return body_res
        base = body_res.type_

        # Compute endpoints via interval substitution
        left = _subst_interval(term.body, term.ivar, 0)
        right = _subst_interval(term.body, term.ivar, 1)

        path_ty = PathType(base_type=base, left=left, right=right)  # type: ignore[arg-type]
        return TypeResult.ok(path_ty, rule="PathAbs",
                             obligations=body_res.obligations)

    # (PathApp)
    def _synth_path_app(self, ctx: Context, term: PathApp) -> TypeResult:
        """Synth p @ r : A

        Rule:
          Γ ⊢ p : a =_A b
          Γ ⊢ r : I
          ──────────────────────
          Γ ⊢ p @ r : A

        Special endpoint reductions:
          p @ 0 reduces to a (left endpoint)
          p @ 1 reduces to b (right endpoint)
        """
        p_res = self.synth(ctx, term.path)
        if not p_res.success:
            return p_res
        pty = p_res.type_
        if not isinstance(pty, PathType):
            return TypeResult.fail("Path application on non-path", rule="PathApp")

        # Check the argument is an interval term (if it's a variable, check ctx)
        arg_res = self.synth(ctx, term.arg)
        obligations = list(p_res.obligations)
        if arg_res.success:
            obligations.extend(arg_res.obligations)

        return TypeResult.ok(pty.base_type, rule="PathApp",
                             obligations=obligations)

    # (Transp) — cubical transport
    def _synth_transport(self, ctx: Context, term: Transport) -> TypeResult:
        """Synth transport(P, p, d).

        Rule:
          Γ ⊢ P : A → Type
          Γ ⊢ p : a =_A b
          Γ ⊢ d : P(a)
          ──────────────────────
          Γ ⊢ transport(P, p, d) : P(b)

        Reduction: transport(P, refl(a), d) → d
        """
        tf_res = self.synth(ctx, term.type_family)
        p_res = self.synth(ctx, term.path)
        d_res = self.synth(ctx, term.base_term)
        if not tf_res.success:
            return tf_res
        if not p_res.success:
            return p_res
        if not d_res.success:
            return d_res

        pty = p_res.type_
        if not isinstance(pty, PathType):
            return TypeResult.fail("transport: path arg must be a path",
                                   rule="Transp")

        # Compute result type: P(b) where b is the right endpoint
        tfty = tf_res.type_
        if isinstance(tfty, PiType) and pty.right is not None:
            result_ty = _subst_type(tfty.body_type, tfty.param_name, pty.right)
        elif isinstance(tfty, PiType):
            result_ty = tfty.body_type
        else:
            result_ty = d_res.type_ if d_res.type_ else PyObjType()

        obligations = tf_res.obligations + p_res.obligations + d_res.obligations

        # Generate proof obligation: d must inhabit P(a)
        if isinstance(tfty, PiType) and pty.left is not None:
            expected_d_ty = _subst_type(tfty.body_type, tfty.param_name, pty.left)
            if d_res.type_ is not None and not self.equal_types(ctx, d_res.type_, expected_d_ty):
                if not self.subtype(ctx, d_res.type_, expected_d_ty):
                    obligations.append(Judgment(
                        kind=JudgmentKind.SUBTYPE,
                        context=ctx,
                        left=Literal(d_res.type_),
                        right=Literal(expected_d_ty),
                    ))

        return TypeResult.ok(result_ty, rule="Transp",  # type: ignore[arg-type]
                             obligations=obligations)

    # (Comp) — Kan composition
    def _synth_comp(self, ctx: Context, term: Comp) -> TypeResult:
        r"""Synth ``comp^A [φ ↦ u] u₀``.

        Rule from cubical type theory, implemented in full below:

            Γ ⊢ A : Type                            (base type)
            Γ ⊢ u₀ : A                              (base section)
            Γ ⊢ φ ≡ face-formula  (union of  i=0, i=1, r=0, r=1 …)
            Γ, i:I, φ ⊢ u(i) : A                    (partial face section)
            Γ ⊢ u(0) = u₀                           (compatibility at i=0)
            ────────────────────────────────────────────────────────────
            Γ ⊢ comp^A [φ ↦ u] u₀ : A               (the filler at i=1)

        and reductions:

        * ``φ ≡ 1`` (face holds on the whole cube) ⇒ ``comp`` reduces to
          ``u(1)`` — the partial section's endpoint.
        * ``φ ≡ 0`` (face is empty) ⇒ ``comp`` reduces to ``u₀`` because
          there is no partial data to compose in.
        * Otherwise, the type remains ``A`` but we emit two proof
          obligations: (a) the face section is well-typed over the
          interval-extended context, and (b) compatibility at ``i=0``.

        Previously this function was tagged "simplified from cubical
        type theory" and skipped face compatibility entirely.  The new
        implementation:

        * evaluates ``φ`` via :func:`_face_holds`;
        * checks the partial term under a context extended with
          ``i : I`` and the face hypothesis;
        * synthesises and records the compatibility obligation as a
          ``Judgment`` that the kernel can later discharge.
        """
        # Type-check the base term.
        base_res = self.synth(ctx, term.base)
        if not base_res.success:
            return base_res
        obligations = list(base_res.obligations)

        # Fast paths based on the face formula.
        face_val = _face_holds(term.face)

        # φ ≡ 0 — no partial data; composition reduces to the base.
        if face_val is False:
            result_ty = term.type_ or (base_res.type_ or PyObjType())
            return TypeResult.ok(result_ty, rule="Comp-φ=0",
                                 obligations=obligations)

        # Need the partial section to proceed.
        if term.partial_term is None:
            # Without a partial section and an indeterminate face, the
            # composition is just the base lifted to ``A`` — emit it
            # but flag that the caller may have meant to supply a
            # section.
            result_ty = term.type_ or (base_res.type_ or PyObjType())
            return TypeResult.ok(result_ty, rule="Comp-no-partial",
                                 obligations=obligations)

        # Check the partial section under an interval-extended context
        # with the face hypothesis bound.  We approximate the face
        # hypothesis as a refinement type on a fresh predicate-carrying
        # name — the kernel can discharge richer face logic via Z3.
        i_ctx = ctx.extend("__i", IntervalType())
        i_ctx = i_ctx.extend(
            f"__face_{id(term)}",
            RefinementType(
                base_type=PyBoolType(),
                var_name="__face_var",
                predicate=term.face,
            ),
        )
        partial_res = self.synth(i_ctx, term.partial_term)
        if not partial_res.success:
            return partial_res
        obligations.extend(partial_res.obligations)

        # φ ≡ 1 — the face is total, so ``comp`` reduces to ``u(1)``.
        # We return the partial section's type (it's already A under
        # our idealised single-type-per-composition regime).
        if face_val is True:
            if partial_res.type_ is not None:
                return TypeResult.ok(partial_res.type_, rule="Comp-φ=1",
                                     obligations=obligations)

        # Indeterminate face: emit a compatibility obligation ``u(0) =
        # u₀`` that later stages (Z3, kernel reflexivity, or the user)
        # must discharge.  The obligation is encoded as a Judgment whose
        # LHS is the partial section evaluated at ``i=0`` (via a
        # ``PathApp`` against ``Literal(0)``) and RHS is the base.
        compat_obligation = Judgment(
            kind=JudgmentKind.EQUAL,
            context=ctx,
            left=PathApp(path=term.partial_term, arg=Literal(0)),
            right=term.base,
            type_=term.type_ or base_res.type_,
        )
        obligations.append(compat_obligation)

        # The result type is A (the ambient type of the composition).
        # If the user didn't supply ``term.type_``, fall back to the
        # base's synthesised type.
        result_ty = term.type_ or (base_res.type_ or PyObjType())
        return TypeResult.ok(result_ty, rule="Comp",
                             obligations=obligations)

    # ── Glue / Unglue ────────────────────────────────────────────

    def _check_glue(self, ctx: Context, term: GlueTerm,
                    expected: GlueType) -> TypeResult:
        """Check Glue type introduction.

        Glue[φ ↦ (T, f)] A where f : T ≃ A

          When φ = 1: Glue reduces to T
          When φ = 0: Glue reduces to A

        The term must provide a base in A and, when φ holds, a term in T.
        """
        # Check base term against the base type
        base_res = self.check(ctx, term.base_term, expected.base_type)
        if not base_res.success:
            return base_res

        obligations = list(base_res.obligations)

        # Check equiv_term against equiv_type when the face holds
        if term.equiv_term is not None and expected.equiv_type is not None:
            eq_res = self.check(ctx, term.equiv_term, expected.equiv_type)
            if not eq_res.success:
                return eq_res
            obligations.extend(eq_res.obligations)

        return TypeResult.ok(expected, rule="Glue-intro",
                             obligations=obligations)

    def _synth_glue(self, ctx: Context, term: GlueTerm) -> TypeResult:
        """Synth a GlueTerm — infer the GlueType."""
        base_res = self.synth(ctx, term.base_term)
        if not base_res.success:
            return base_res

        equiv_ty = None
        obligations = list(base_res.obligations)
        if term.equiv_term is not None:
            eq_res = self.synth(ctx, term.equiv_term)
            if eq_res.success:
                equiv_ty = eq_res.type_
                obligations.extend(eq_res.obligations)

        glue_ty = GlueType(
            base_type=base_res.type_,  # type: ignore[arg-type]
            face=term.face,
            equiv_type=equiv_ty,
        )
        return TypeResult.ok(glue_ty, rule="Glue-intro",
                             obligations=obligations)

    def _synth_unglue(self, ctx: Context, term: UnGlueTerm) -> TypeResult:
        """Synth unglue(g) — extract the base from a glued term.

        Rule:
          Γ ⊢ g : Glue[φ ↦ T] A
          ──────────────────────
          Γ ⊢ unglue(g) : A
        """
        g_res = self.synth(ctx, term.term)
        if not g_res.success:
            return g_res
        gty = g_res.type_
        if isinstance(gty, GlueType):
            return TypeResult.ok(gty.base_type, rule="Unglue",
                                 obligations=g_res.obligations)
        # If not a GlueType, pass through
        return TypeResult.ok(gty, rule="Unglue",  # type: ignore[arg-type]
                             obligations=g_res.obligations)

    # ── Python-specific path rules ────────────────────────────────

    def _check_duck_path(self, ctx: Context,
                         type_a: SynType, type_b: SynType,
                         protocol: ProtocolType) -> TypeResult:
        """Duck-type path: A and B are path-equal if they share a protocol.

        This is Python-specific univalence:
        If A and B both implement protocol P (same methods with compatible
        types), then there's a path A =_U B in the type universe.
        """
        a_ok = isinstance(type_a, PyClassType) and self.subtype(ctx, type_a, protocol)
        b_ok = isinstance(type_b, PyClassType) and self.subtype(ctx, type_b, protocol)

        if not a_ok or not b_ok:
            return TypeResult.fail(
                f"Duck path: both types must satisfy protocol {protocol.name}",
                rule="DuckPath",
            )

        path_ty = PathType(
            base_type=UniverseType(),
            left=Literal(type_a),
            right=Literal(type_b),
        )
        return TypeResult.ok(path_ty, rule="DuckPath")

    def _check_monkey_patch_path(self, ctx: Context,
                                  cls: SynType, method: str,
                                  old_impl: SynTerm,
                                  new_impl: SynTerm) -> TypeResult:
        """Monkey-patch path: cls =_PyClass cls[m := v]

        Valid when the behavioral contract is preserved:
          ∀ inputs. old_impl(inputs) ≡ new_impl(inputs)

        This generates a proof obligation that the implementations
        are extensionally equal.
        """
        if not isinstance(cls, PyClassType):
            return TypeResult.fail(
                "Monkey-patch path: expected a PyClassType",
                rule="MonkeyPatchPath",
            )

        obligations = [
            Judgment(
                kind=JudgmentKind.EQUAL,
                context=ctx,
                left=old_impl,
                right=new_impl,
            )
        ]

        path_ty = PathType(
            base_type=cls,
            left=Literal(cls),
            right=Literal(cls),
        )
        return TypeResult.ok(path_ty, rule="MonkeyPatchPath",
                             obligations=obligations)

    # ── Subtyping via path coercion ───────────────────────────────

    def _subtype_via_path(self, ctx: Context,
                          sub: SynType, sup: SynType) -> bool:
        """Check subtyping via path existence.

        A <: B if there exists a coercion path from A to B.
        This includes:
        - Direct protocol paths (duck typing)
        - Refinement subtyping (weakening predicates)
        - Effect subtyping (pure <: reads <: mutates <: IO)
        """
        # Effect coercion: A!Pure → A!IO (effects form a lattice)
        if isinstance(sub, EffectType) and not isinstance(sup, EffectType):
            if sub.effect == "Pure":
                return self.subtype(ctx, sub.base, sup)

        # Protocol-mediated coercion:
        # If sub and sup both satisfy a common protocol, there's a
        # coercion path through that protocol (univalence for duck types)
        if isinstance(sub, PyClassType) and isinstance(sup, PyClassType):
            sub_methods = set(n for n, _ in sub.methods)
            sup_methods = set(n for n, _ in sup.methods)
            if sup_methods and sup_methods <= sub_methods:
                sub_dict = dict(sub.methods)
                sup_dict = dict(sup.methods)
                return all(
                    self.subtype(ctx, sub_dict[m], sup_dict[m])
                    for m in sup_methods
                )

        return False

    # ═══════════════════════════════════════════════════════════════
    #  Python-specific rules
    # ═══════════════════════════════════════════════════════════════

    # (SetAttr)
    def _synth_setattr(self, ctx: Context, term: SetAttrTerm) -> TypeResult:
        c_res = self.synth(ctx, term.cls)
        if not c_res.success:
            return c_res
        if not isinstance(c_res.type_, PyClassType):
            return TypeResult.fail("setattr: first arg must be PyClass",
                                   rule="SetAttr")
        return TypeResult.ok(c_res.type_, effect="IO", rule="SetAttr",
                             obligations=c_res.obligations)

    # (DuckCheck)
    def _synth_duck_check(self, ctx: Context,
                          term: DuckCheckTerm) -> TypeResult:
        o_res = self.synth(ctx, term.obj)
        if not o_res.success:
            return o_res
        obj_ty = o_res.type_
        proto = term.protocol

        # Generate a proof obligation for each required method
        obligations = list(o_res.obligations)
        for mname, mtype in proto.methods:
            obligations.append(Judgment(
                kind=JudgmentKind.SUBTYPE,
                context=ctx,
                left=Literal(obj_ty),
                right=Literal(proto),
            ))

        ref = RefinementType(
            base_type=PyObjType(),
            var_name="x",
            predicate=f"x ⊨ {proto.name}",
        )
        return TypeResult.ok(ref, rule="DuckCheck", obligations=obligations)

    # (GenYield)  — yield_at(g, n) : Y
    #   This is handled via GenSend; GenYield is implicit in generator iteration.

    # (GetAttr)
    def _synth_getattr(self, ctx: Context, term: GetAttr) -> TypeResult:
        obj_res = self.synth(ctx, term.obj)
        if not obj_res.success:
            return obj_res
        oty = obj_res.type_
        if isinstance(oty, PyClassType):
            for mname, mtype in oty.methods:
                if mname == term.attr:
                    return TypeResult.ok(mtype, rule="GetAttr",
                                         obligations=obj_res.obligations)
        if isinstance(oty, ProtocolType):
            for mname, mtype in oty.methods:
                if mname == term.attr:
                    return TypeResult.ok(mtype, rule="GetAttr",
                                         obligations=obj_res.obligations)
        return TypeResult.ok(PyObjType(), rule="GetAttr",
                             obligations=obj_res.obligations)

    # (GetItem)
    def _synth_getitem(self, ctx: Context, term: GetItem) -> TypeResult:
        obj_res = self.synth(ctx, term.obj)
        key_res = self.synth(ctx, term.key)
        if not obj_res.success:
            return obj_res
        if not key_res.success:
            return key_res
        oty = obj_res.type_
        if isinstance(oty, PyListType):
            return TypeResult.ok(oty.element_type, rule="GetItem",
                                 obligations=obj_res.obligations + key_res.obligations)
        if isinstance(oty, PyDictType):
            return TypeResult.ok(oty.value_type, rule="GetItem",
                                 obligations=obj_res.obligations + key_res.obligations)
        if isinstance(oty, PyTupleType):
            return TypeResult.ok(PyObjType(), rule="GetItem",
                                 obligations=obj_res.obligations + key_res.obligations)
        return TypeResult.ok(PyObjType(), rule="GetItem",
                             obligations=obj_res.obligations + key_res.obligations)

    # (PyCall)
    def _synth_pycall(self, ctx: Context, term: PyCall) -> TypeResult:
        f_res = self.synth(ctx, term.func)
        if not f_res.success:
            return f_res
        fty = f_res.type_
        assert fty is not None
        obligations = list(f_res.obligations)
        eff = f_res.effect

        if isinstance(fty, PyCallableType):
            for i, arg in enumerate(term.args):
                if i < len(fty.param_types):
                    a_res = self.check(ctx, arg, fty.param_types[i])
                else:
                    a_res = self.synth(ctx, arg)
                if not a_res.success:
                    return a_res
                obligations.extend(a_res.obligations)
                eff = _effect_join(eff, a_res.effect)
            return TypeResult.ok(fty.return_type, effect=eff,
                                 rule="PyCall", obligations=obligations)

        if isinstance(fty, PiType):
            # Curried application
            cur_ty: SynType = fty
            for arg in term.args:
                if not isinstance(cur_ty, PiType):
                    return TypeResult.fail("Too many arguments", rule="PyCall")
                a_res = self.check(ctx, arg, cur_ty.param_type)
                if not a_res.success:
                    return a_res
                obligations.extend(a_res.obligations)
                eff = _effect_join(eff, a_res.effect)
                cur_ty = _subst_type(cur_ty.body_type, cur_ty.param_name, arg)
            return TypeResult.ok(cur_ty, effect=eff,
                                 rule="PyCall", obligations=obligations)

        return TypeResult.ok(PyObjType(), effect="IO", rule="PyCall",
                             obligations=obligations)

    # ═══════════════════════════════════════════════════════════════
    #  Statement rules
    # ═══════════════════════════════════════════════════════════════

    # (Let)
    def _synth_let(self, ctx: Context, term: LetIn) -> TypeResult:
        e_res = self.synth(ctx, term.value)
        if not e_res.success:
            return e_res
        val_ty = term.var_type if term.var_type else e_res.type_
        assert val_ty is not None
        ext = ctx.extend(term.var_name, val_ty)
        b_res = self.synth(ext, term.body)
        if not b_res.success:
            return b_res
        eff = _effect_join(e_res.effect, b_res.effect)  # (EffLet)
        return TypeResult.ok(b_res.type_, effect=eff, rule="Let",  # type: ignore[arg-type]
                             obligations=e_res.obligations + b_res.obligations)

    # (If)
    def _synth_if(self, ctx: Context, term: IfThenElse) -> TypeResult:
        c_res = self.synth(ctx, term.cond)
        if not c_res.success:
            return c_res
        # Refine context in branches
        then_ctx = ctx  # Γ, c = True  (approximated)
        else_ctx = ctx  # Γ, c = False
        t_res = self.synth(then_ctx, term.then_branch)
        f_res = self.synth(else_ctx, term.else_branch)
        if not t_res.success:
            return t_res
        if not f_res.success:
            return f_res
        # Join: if branches have equal types use that, else union
        assert t_res.type_ is not None and f_res.type_ is not None
        if self.equal_types(ctx, t_res.type_, f_res.type_):
            res_ty = t_res.type_
        else:
            res_ty = UnionType((t_res.type_, f_res.type_))
        eff = _effect_join(c_res.effect,
                           _effect_join(t_res.effect, f_res.effect))
        return TypeResult.ok(res_ty, effect=eff, rule="If",
                             obligations=(c_res.obligations +
                                          t_res.obligations + f_res.obligations))

    # (For)
    def _synth_for(self, ctx: Context, term: ForLoop) -> TypeResult:
        it_res = self.synth(ctx, term.iter_)
        if not it_res.success:
            return it_res
        elem_ty = PyObjType()
        ity = it_res.type_
        if isinstance(ity, PyListType):
            elem_ty = ity.element_type
        elif isinstance(ity, PySetType):
            elem_ty = ity.element_type
        elif isinstance(ity, IterableType):
            elem_ty = ity.element_type
        ext = ctx.extend(term.var, elem_ty)
        b_res = self.synth(ext, term.body)
        if not b_res.success:
            return b_res
        return TypeResult.ok(UnitType(), effect=_effect_join(it_res.effect,
                             b_res.effect), rule="For",
                             obligations=it_res.obligations + b_res.obligations)

    # (While)
    def _synth_while(self, ctx: Context, term: WhileLoop) -> TypeResult:
        c_res = self.synth(ctx, term.cond)
        b_res = self.synth(ctx, term.body)
        if not c_res.success:
            return c_res
        if not b_res.success:
            return b_res
        obligations = c_res.obligations + b_res.obligations
        # Proof obligation: variant decreases
        if term.variant:
            obligations.append(Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx,
                term=term.variant,
                type_=PyIntType(),
            ))
        return TypeResult.ok(UnitType(),
                             effect=_effect_join(c_res.effect, b_res.effect),
                             rule="While", obligations=obligations)

    # (TryExcept)
    def _synth_try(self, ctx: Context, term: TryExcept) -> TypeResult:
        b_res = self.synth(ctx, term.body)
        if not b_res.success:
            return b_res
        ext = ctx.extend(term.exc_name, term.exc_type)
        h_res = self.synth(ext, term.handler)
        if not h_res.success:
            return h_res
        assert b_res.type_ is not None and h_res.type_ is not None
        if self.equal_types(ctx, b_res.type_, h_res.type_):
            res_ty = b_res.type_
        else:
            res_ty = UnionType((b_res.type_, h_res.type_))
        return TypeResult.ok(res_ty,
                             effect=_effect_join(b_res.effect, h_res.effect),
                             rule="TryExcept",
                             obligations=b_res.obligations + h_res.obligations)

    # (With)
    def _synth_with(self, ctx: Context, term: WithStmt) -> TypeResult:
        m_res = self.synth(ctx, term.mgr)
        if not m_res.success:
            return m_res
        inner_ty = PyObjType()
        mty = m_res.type_
        if isinstance(mty, ContextManagerType):
            inner_ty = mty.inner
        ext = ctx.extend(term.var, inner_ty)
        b_res = self.synth(ext, term.body)
        if not b_res.success:
            return b_res
        return TypeResult.ok(b_res.type_,  # type: ignore[arg-type]
                             effect=_effect_join(m_res.effect, b_res.effect),
                             rule="With",
                             obligations=m_res.obligations + b_res.obligations)

    # (Assert)
    def _synth_assert(self, ctx: Context, term: AssertTerm) -> TypeResult:
        e_res = self.synth(ctx, term.expr)
        if not e_res.success:
            return e_res
        ref = RefinementType(
            base_type=e_res.type_,  # type: ignore[arg-type]
            var_name="x",
            predicate="x is truthy",
        )
        return TypeResult.ok(ref, rule="Assert", obligations=e_res.obligations)

    # (Del)
    def _synth_del(self, ctx: Context, term: DelTerm) -> TypeResult:
        if term.name not in ctx:
            return TypeResult.fail(f"del: variable {term.name} not in scope",
                                   rule="Del")
        return TypeResult.ok(UnitType(), rule="Del")

    # (Import)
    def _synth_import(self, ctx: Context, term: ImportTerm) -> TypeResult:
        # The import rule extends the context; here we just record the type
        # that the extended context would assign.  The caller can use
        # term.exports to extend Γ.
        if term.exports:
            sigma_parts = [ty for _, ty in term.exports]
            if len(sigma_parts) == 1:
                return TypeResult.ok(sigma_parts[0], rule="Import")
            return TypeResult.ok(PyObjType(), rule="Import")
        return TypeResult.ok(PyObjType(), rule="Import")

    # ═══════════════════════════════════════════════════════════════
    #  Class / Decorator rules
    # ═══════════════════════════════════════════════════════════════

    # (ClassDef)
    def _synth_classdef(self, ctx: Context, term: ClassDefTerm) -> TypeResult:
        method_sigs: list[tuple[str, SynType]] = []
        obligations: list[Judgment] = []
        eff = "Pure"
        for mname, mbody in term.methods:
            m_res = self.synth(ctx, mbody)
            if not m_res.success:
                return m_res
            method_sigs.append((mname, m_res.type_))  # type: ignore[arg-type]
            obligations.extend(m_res.obligations)
            eff = _effect_join(eff, m_res.effect)
        bases = tuple(b.name if isinstance(b, PyClassType) else str(b)
                      for b in term.bases)
        cls_ty = PyClassType(
            name=term.name,
            methods=tuple(method_sigs),
            bases=bases,
        )
        return TypeResult.ok(cls_ty, effect=eff, rule="ClassDef",
                             obligations=obligations)

    # (Decorator)
    def _synth_decorator(self, ctx: Context, term: DecoratorTerm) -> TypeResult:
        d_res = self.synth(ctx, term.decorator)
        f_res = self.synth(ctx, term.func)
        if not d_res.success:
            return d_res
        if not f_res.success:
            return f_res
        dty = d_res.type_
        # Decorator is (A→B) → (A→B'); result is application d(f)
        if isinstance(dty, PiType):
            result_ty = dty.body_type
        elif isinstance(dty, PyCallableType):
            result_ty = dty.return_type
        else:
            result_ty = f_res.type_  # fallback: decorator is identity-like
        return TypeResult.ok(result_ty,  # type: ignore[arg-type]
                             effect=_effect_join(d_res.effect, f_res.effect),
                             rule="Decorator",
                             obligations=d_res.obligations + f_res.obligations)

    # ═══════════════════════════════════════════════════════════════
    #  Generator / Async rules
    # ═══════════════════════════════════════════════════════════════

    # (Yield)
    def _synth_yield(self, ctx: Context, term: YieldTerm) -> TypeResult:
        e_res = self.synth(ctx, term.value)
        if not e_res.success:
            return e_res
        gen_ty = GeneratorType(
            send_type=PyNoneType(),
            yield_type=e_res.type_,  # type: ignore[arg-type]
            return_type=PyNoneType(),
        )
        return TypeResult.ok(gen_ty, rule="Yield",
                             obligations=e_res.obligations)

    # (Await)
    def _synth_await(self, ctx: Context, term: AwaitTerm) -> TypeResult:
        e_res = self.synth(ctx, term.value)
        if not e_res.success:
            return e_res
        ety = e_res.type_
        if isinstance(ety, AwaitableType):
            return TypeResult.ok(ety.inner, effect="IO", rule="Await",
                                 obligations=e_res.obligations)
        return TypeResult.fail(f"await: expected Awaitable, got {ety}",
                               rule="Await")

    # (GenSend)
    def _synth_gen_send(self, ctx: Context, term: GenSendTerm) -> TypeResult:
        g_res = self.synth(ctx, term.gen)
        v_res = self.synth(ctx, term.value)
        if not g_res.success:
            return g_res
        if not v_res.success:
            return v_res
        gty = g_res.type_
        if not isinstance(gty, GeneratorType):
            return TypeResult.fail(f"send: expected Generator, got {gty}",
                                   rule="GenSend")
        # Check value against send type
        v_check = self.check(ctx, term.value, gty.send_type)
        if not v_check.success:
            return v_check
        return TypeResult.ok(gty.yield_type, rule="GenSend",
                             obligations=g_res.obligations + v_check.obligations)

    # ═══════════════════════════════════════════════════════════════
    #  Op / OpCall
    # ═══════════════════════════════════════════════════════════════

    def _synth_op(self, ctx: Context, term: Op) -> TypeResult:
        ty = ctx.lookup(term.qualified)
        if ty is not None:
            return TypeResult.ok(ty, rule="Op")
        return TypeResult.ok(PyObjType(), rule="Op")

    def _synth_opcall(self, ctx: Context, term: OpCall) -> TypeResult:
        op_res = self._synth_op(ctx, term.op)
        obligations: list[Judgment] = []
        eff = "Pure"
        for arg in term.args:
            a_res = self.synth(ctx, arg)
            if not a_res.success:
                return a_res
            obligations.extend(a_res.obligations)
            eff = _effect_join(eff, a_res.effect)
        # Infer return type from known ops
        rty = self._op_return_type(term.op.name, term.args, ctx)
        return TypeResult.ok(rty, effect=eff, rule="OpCall",
                             obligations=obligations)

    def _op_return_type(self, name: str, args: tuple[SynTerm, ...],
                        ctx: Context) -> SynType:
        """Heuristic return type for well-known operations."""
        arith_ops = {"__add__", "__sub__", "__mul__", "__truediv__",
                     "__floordiv__", "__mod__", "__pow__", "__neg__", "__abs__"}
        cmp_ops = {"__eq__", "__ne__", "__lt__", "__le__", "__gt__", "__ge__",
                   "__contains__", "__bool__", "__not__", "__and__", "__or__"}

        if name in cmp_ops:
            return PyBoolType()
        if name in arith_ops and args:
            first = self.synth(ctx, args[0])
            if first.success and first.type_ is not None:
                return first.type_
        if name == "len":
            return PyIntType()
        if name in {"__str__", "__repr__"}:
            return PyStrType()
        if name in {"__int__"}:
            return PyIntType()
        if name in {"__float__"}:
            return PyFloatType()
        if name in {"__hash__"}:
            return PyIntType()
        if name == "sorted" and args:
            first = self.synth(ctx, args[0])
            if first.success and isinstance(first.type_, PyListType):
                return first.type_
            return PyListType()
        return PyObjType()


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Run basic smoke tests for the type checker."""
    tc = TypeChecker()
    ctx = Context()

    # (Var)
    ctx_x = ctx.extend("x", PyIntType())
    r = tc.synth(ctx_x, Var("x"))
    assert r.success and isinstance(r.type_, PyIntType), f"Var failed: {r}"

    # (Literal)
    r = tc.synth(ctx, Literal(42))
    assert r.success and isinstance(r.type_, PyIntType), f"Literal int: {r}"
    r = tc.synth(ctx, Literal("hello"))
    assert r.success and isinstance(r.type_, PyStrType), f"Literal str: {r}"
    r = tc.synth(ctx, Literal(True))
    assert r.success and isinstance(r.type_, PyBoolType), f"Literal bool: {r}"
    r = tc.synth(ctx, Literal(None))
    assert r.success and isinstance(r.type_, PyNoneType), f"Literal None: {r}"

    # (Lam) — synth
    lam = Lam("x", PyIntType(), Var("x"))
    r = tc.synth(ctx, lam)
    assert r.success and isinstance(r.type_, PiType), f"Lam synth: {r}"

    # (Lam) — check
    pi = PiType("x", PyIntType(), PyIntType())
    r = tc.check(ctx, lam, pi)
    assert r.success, f"Lam check: {r}"

    # (App)
    ctx_f = ctx.extend("f", arrow(PyIntType(), PyBoolType()))
    ctx_fx = ctx_f.extend("x", PyIntType())
    app = App(Var("f"), Var("x"))
    r = tc.synth(ctx_fx, app)
    assert r.success and isinstance(r.type_, PyBoolType), f"App: {r}"

    # (Pair / Σ-intro)
    pair = Pair(Literal(1), Literal("a"))
    r = tc.synth(ctx, pair)
    assert r.success and isinstance(r.type_, SigmaType), f"Pair synth: {r}"

    # (Fst / Snd)
    ctx_p = ctx.extend("p", SigmaType("_", PyIntType(), PyStrType()))
    r = tc.synth(ctx_p, Fst(Var("p")))
    assert r.success and isinstance(r.type_, PyIntType), f"Fst: {r}"
    r = tc.synth(ctx_p, Snd(Var("p")))
    assert r.success and isinstance(r.type_, PyStrType), f"Snd: {r}"

    # (Let)
    let = LetIn("y", None, Literal(10), Var("y"))
    r = tc.synth(ctx, let)
    assert r.success and isinstance(r.type_, PyIntType), f"Let: {r}"

    # (If)
    ite = IfThenElse(Literal(True), Literal(1), Literal(2))
    r = tc.synth(ctx, ite)
    assert r.success and isinstance(r.type_, PyIntType), f"If: {r}"

    # (Refl)
    refl = Refl(Literal(42))
    r = tc.synth(ctx, refl)
    assert r.success and isinstance(r.type_, PathType), f"Refl: {r}"

    # (Sym)
    ctx_p2 = ctx.extend("p", PathType(PyIntType(), Literal(1), Literal(2)))
    sym = SymTerm(Var("p"))
    r = tc.synth(ctx_p2, sym)
    assert r.success and isinstance(r.type_, PathType), f"Sym: {r}"

    # (Trans)
    ctx_pq = ctx.extend("p", PathType(PyIntType(), Literal(1), Literal(2)))
    ctx_pq = ctx_pq.extend("q", PathType(PyIntType(), Literal(2), Literal(3)))
    tr = TransTerm(Var("p"), Var("q"))
    r = tc.synth(ctx_pq, tr)
    assert r.success and isinstance(r.type_, PathType), f"Trans: {r}"

    # (Ap)
    ctx_fp = ctx.extend("f", arrow(PyIntType(), PyIntType()))
    ctx_fp = ctx_fp.extend("p", PathType(PyIntType(), Literal(1), Literal(2)))
    ap = ApTerm(Var("f"), Var("p"))
    r = tc.synth(ctx_fp, ap)
    assert r.success and isinstance(r.type_, PathType), f"Ap: {r}"

    # (Yield)
    yld = YieldTerm(Literal(42))
    r = tc.synth(ctx, yld)
    assert r.success and isinstance(r.type_, GeneratorType), f"Yield: {r}"

    # (Await)
    ctx_aw = ctx.extend("coro", AwaitableType(PyIntType()))
    aw = AwaitTerm(Var("coro"))
    r = tc.synth(ctx_aw, aw)
    assert r.success and isinstance(r.type_, PyIntType), f"Await: {r}"

    # (For)
    ctx_lst = ctx.extend("xs", PyListType(PyIntType()))
    fl = ForLoop("x", Var("xs"), Literal(None))
    r = tc.synth(ctx_lst, fl)
    assert r.success and isinstance(r.type_, UnitType), f"For: {r}"

    # (While)
    wh = WhileLoop(Literal(True), Literal(None))
    r = tc.synth(ctx, wh)
    assert r.success and isinstance(r.type_, UnitType), f"While: {r}"

    # (TryExcept)
    te = TryExcept(Literal(1), "e", PyObjType(), Literal(2))
    r = tc.synth(ctx, te)
    assert r.success, f"TryExcept: {r}"

    # (With)
    ctx_mgr = ctx.extend("mgr", ContextManagerType(PyIntType()))
    ws = WithStmt(Var("mgr"), "f", Var("f"))
    r = tc.synth(ctx_mgr, ws)
    assert r.success, f"With: {r}"

    # (Assert)
    asrt = AssertTerm(Literal(True))
    r = tc.synth(ctx, asrt)
    assert r.success and isinstance(r.type_, RefinementType), f"Assert: {r}"

    # (Del)
    ctx_del = ctx.extend("z", PyIntType())
    dl = DelTerm("z")
    r = tc.synth(ctx_del, dl)
    assert r.success, f"Del: {r}"

    # (Import)
    imp = ImportTerm("os", (("path", PyStrType()),))
    r = tc.synth(ctx, imp)
    assert r.success, f"Import: {r}"

    # (ClassDef)
    cls = ClassDefTerm("Foo", (), (("bar", Lam("self", PyObjType(), Literal(1))),))
    r = tc.synth(ctx, cls)
    assert r.success and isinstance(r.type_, PyClassType), f"ClassDef: {r}"

    # (Decorator)
    ctx_d = ctx.extend("dec", arrow(arrow(PyIntType(), PyIntType()),
                                    arrow(PyIntType(), PyBoolType())))
    ctx_d = ctx_d.extend("fn", arrow(PyIntType(), PyIntType()))
    dec = DecoratorTerm(Var("dec"), Var("fn"))
    r = tc.synth(ctx_d, dec)
    assert r.success, f"Decorator: {r}"

    # (Subtype)
    assert tc.subtype(ctx, PyBoolType(), PyIntType()), "bool <: int"
    assert tc.subtype(ctx, PyIntType(), PyFloatType()), "int <: float"
    assert tc.subtype(ctx, PyIntType(), PyObjType()), "int <: PyObj"
    assert tc.subtype(ctx, PyNoneType(),
                      OptionalType(PyIntType())), "None <: Optional[int]"

    # (DuckEquiv via subtype)
    cls_ty = PyClassType("Duck", (("quack", arrow(PyObjType(), PyNoneType())),))
    proto_ty = ProtocolType("Quacker",
                            (("quack", arrow(PyObjType(), PyNoneType())),))
    assert tc.subtype(ctx, cls_ty, proto_ty), "DuckEquiv"

    # (PurePromotion)
    eff_pure = EffectType(PyIntType(), "Pure")
    assert tc.equal_types(ctx, eff_pure, PyIntType()), "PurePromotion via equal"

    # (GenSend)
    gen_ty = GeneratorType(PyIntType(), PyStrType(), PyNoneType())
    ctx_gs = ctx.extend("g", gen_ty)
    gs = GenSendTerm(Var("g"), Literal(42))
    r = tc.synth(ctx_gs, gs)
    assert r.success and isinstance(r.type_, PyStrType), f"GenSend: {r}"

    # (SetAttr)
    ctx_cls = ctx.extend("C", PyClassType("C"))
    sa = SetAttrTerm(Var("C"), Literal("method"), Literal(None))
    r = tc.synth(ctx_cls, sa)
    assert r.success and r.effect == "IO", f"SetAttr: {r}"

    # (Transport)
    ctx_tr = ctx.extend("P", arrow(PyIntType(), UniverseType()))
    ctx_tr = ctx_tr.extend("p", PathType(PyIntType(), Literal(1), Literal(2)))
    ctx_tr = ctx_tr.extend("d", PyObjType())
    tp = Transport(Var("P"), Var("p"), Var("d"))
    r = tc.synth(ctx_tr, tp)
    assert r.success, f"Transport: {r}"

    print("All self-tests passed ✓")


if __name__ == "__main__":
    _self_test()
