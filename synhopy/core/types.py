"""
SynHoPy Core Type System

The foundational types of the cubical homotopy type theory for Python.
Every Python value, type, and specification is represented using these types.

Architecture:
    SynType          — base class for all types
    ├── PyObjType     — the universe of Python objects
    ├── PiType        — dependent function types (Π)
    ├── SigmaType     — dependent pair types (Σ)
    ├── PathType      — identity/path types (a =_A b)
    ├── UniverseType  — type universe hierarchy (U_0, U_1, ...)
    ├── RefinementType — refinement types ({x : A | φ(x)})
    ├── UnionType     — sum types (A | B)
    ├── IntervalType  — the cubical interval I
    ├── GlueType      — glue types for univalence
    └── EffectType    — effect-indexed types

    SynTerm          — base class for all terms
    ├── Var           — variable reference
    ├── App           — function application
    ├── Lam           — lambda abstraction
    ├── Pair          — dependent pair constructor
    ├── Fst / Snd     — pair projections
    ├── PathAbs       — path abstraction (λ(i:I). t)
    ├── PathApp       — path application (p @ r)
    ├── Transport     — transport along a path
    ├── Comp          — Kan composition
    ├── Glue / Unglue — glue type constructors
    └── Literal       — Python literal values
"""
from __future__ import annotations

import ast
import hashlib
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Optional, Sequence

# ═══════════════════════════════════════════════════════════════════
# Type Universe
# ═══════════════════════════════════════════════════════════════════

class SynType:
    """Base class for all SynHoPy types."""

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, SynType):
            return NotImplemented
        return self._structural_eq(other)

    def _structural_eq(self, other: SynType) -> bool:
        return type(self) is type(other)

    def __hash__(self) -> int:
        return hash(type(self).__name__)

    def __repr__(self) -> str:
        return self._repr()

    def _repr(self) -> str:
        return type(self).__name__


@dataclass(frozen=True)
class PyObjType(SynType):
    """The type of all Python objects — the top type."""

    def _repr(self) -> str:
        return "PyObj"


@dataclass(frozen=True)
class PyIntType(SynType):
    """Python int type."""

    def _repr(self) -> str:
        return "int"


@dataclass(frozen=True)
class PyFloatType(SynType):
    """Python float type."""

    def _repr(self) -> str:
        return "float"


@dataclass(frozen=True)
class PyStrType(SynType):
    """Python str type."""

    def _repr(self) -> str:
        return "str"


@dataclass(frozen=True)
class PyBoolType(SynType):
    """Python bool type."""

    def _repr(self) -> str:
        return "bool"


@dataclass(frozen=True)
class PyNoneType(SynType):
    """Python NoneType."""

    def _repr(self) -> str:
        return "None"


@dataclass(frozen=True)
class PyListType(SynType):
    """Python list[T] type."""
    element_type: SynType = field(default_factory=PyObjType)

    def _repr(self) -> str:
        return f"list[{self.element_type}]"


@dataclass(frozen=True)
class PyDictType(SynType):
    """Python dict[K, V] type."""
    key_type: SynType = field(default_factory=PyObjType)
    value_type: SynType = field(default_factory=PyObjType)

    def _repr(self) -> str:
        return f"dict[{self.key_type}, {self.value_type}]"


@dataclass(frozen=True)
class PyTupleType(SynType):
    """Python tuple type."""
    element_types: tuple[SynType, ...] = ()

    def _repr(self) -> str:
        inner = ", ".join(str(t) for t in self.element_types)
        return f"tuple[{inner}]"


@dataclass(frozen=True)
class PySetType(SynType):
    """Python set[T] type."""
    element_type: SynType = field(default_factory=PyObjType)

    def _repr(self) -> str:
        return f"set[{self.element_type}]"


@dataclass(frozen=True)
class PyClassType(SynType):
    """A specific Python class, identified by name + methods."""
    name: str = ""
    methods: tuple[tuple[str, SynType], ...] = ()
    bases: tuple[str, ...] = ()

    def _repr(self) -> str:
        return f"class:{self.name}"


@dataclass(frozen=True)
class PyCallableType(SynType):
    """Python callable type Callable[[A1,...,An], R]."""
    param_types: tuple[SynType, ...] = ()
    return_type: SynType = field(default_factory=PyObjType)

    def _repr(self) -> str:
        params = ", ".join(str(t) for t in self.param_types)
        return f"Callable[[{params}], {self.return_type}]"


# ═══════════════════════════════════════════════════════════════════
# HoTT Type Formers
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class UniverseType(SynType):
    """Type universe U_n. U_0 : U_1 : U_2 : ..."""
    level: int = 0

    def _repr(self) -> str:
        return f"U_{self.level}"


@dataclass(frozen=True)
class PiType(SynType):
    """Dependent function type Π(x : A). B(x).
    When B doesn't depend on x, this is just A → B.
    """
    param_name: str = "x"
    param_type: SynType = field(default_factory=PyObjType)
    body_type: SynType = field(default_factory=PyObjType)

    def _repr(self) -> str:
        return f"Π({self.param_name} : {self.param_type}). {self.body_type}"


@dataclass(frozen=True)
class SigmaType(SynType):
    """Dependent pair type Σ(x : A). B(x).
    When B doesn't depend on x, this is just A × B.
    """
    fst_name: str = "x"
    fst_type: SynType = field(default_factory=PyObjType)
    snd_type: SynType = field(default_factory=PyObjType)

    def _repr(self) -> str:
        return f"Σ({self.fst_name} : {self.fst_type}). {self.snd_type}"


@dataclass(frozen=True)
class PathType(SynType):
    """Path type: a =_A b.
    In HoTT, a path is a proof of equality.
    """
    base_type: SynType = field(default_factory=PyObjType)
    left: SynTerm | None = None
    right: SynTerm | None = None

    def _repr(self) -> str:
        l = str(self.left) if self.left else "?"
        r = str(self.right) if self.right else "?"
        return f"{l} =_{{{self.base_type}}} {r}"


@dataclass(frozen=True)
class RefinementType(SynType):
    """Refinement type {x : A | φ(x)}.
    The predicate φ is stored as a string (parsed later by Z3 or LLM).
    """
    base_type: SynType = field(default_factory=PyObjType)
    var_name: str = "x"
    predicate: str = "True"

    def _repr(self) -> str:
        return f"{{{self.var_name} : {self.base_type} | {self.predicate}}}"


@dataclass(frozen=True)
class UnionType(SynType):
    """Union type A | B | C (Python's int | str)."""
    alternatives: tuple[SynType, ...] = ()

    def _repr(self) -> str:
        return " | ".join(str(t) for t in self.alternatives)


@dataclass(frozen=True)
class OptionalType(SynType):
    """Optional[A] = A | None."""
    inner: SynType = field(default_factory=PyObjType)

    def _repr(self) -> str:
        return f"Optional[{self.inner}]"


@dataclass(frozen=True)
class IntervalType(SynType):
    """The cubical interval type I with endpoints 0 and 1."""

    def _repr(self) -> str:
        return "I"


@dataclass(frozen=True)
class GlueType(SynType):
    """Glue type for univalence.
    Glue [φ ↦ (T, f)] A
    """
    base_type: SynType = field(default_factory=PyObjType)
    face: str = "1=1"
    equiv_type: SynType | None = None

    def _repr(self) -> str:
        return f"Glue[{self.face} ↦ {self.equiv_type}]({self.base_type})"


@dataclass(frozen=True)
class ProtocolType(SynType):
    """Duck-type protocol: a set of required method signatures."""
    name: str = ""
    methods: tuple[tuple[str, SynType], ...] = ()

    def _repr(self) -> str:
        meths = ", ".join(f"{n}: {t}" for n, t in self.methods)
        return f"Protocol({self.name})[{meths}]"


# ═══════════════════════════════════════════════════════════════════
# Terms
# ═══════════════════════════════════════════════════════════════════

class SynTerm:
    """Base class for all SynHoPy terms."""

    def __repr__(self) -> str:
        return self._repr()

    def _repr(self) -> str:
        return type(self).__name__

    def free_vars(self) -> set[str]:
        """Return the set of free variable names in this term."""
        return set()


@dataclass
class Var(SynTerm):
    """Variable reference."""
    name: str = ""

    def _repr(self) -> str:
        return self.name

    def free_vars(self) -> set[str]:
        return {self.name}


@dataclass
class Literal(SynTerm):
    """Python literal value."""
    value: Any = None
    type_: SynType = field(default_factory=PyObjType)

    def _repr(self) -> str:
        return repr(self.value)


@dataclass
class Lam(SynTerm):
    """Lambda abstraction λ(x : A). body."""
    param: str = "x"
    param_type: SynType = field(default_factory=PyObjType)
    body: SynTerm = field(default_factory=lambda: Var("x"))

    def _repr(self) -> str:
        return f"λ({self.param} : {self.param_type}). {self.body}"

    def free_vars(self) -> set[str]:
        return self.body.free_vars() - {self.param}


@dataclass
class App(SynTerm):
    """Function application f(a)."""
    func: SynTerm = field(default_factory=lambda: Var("f"))
    arg: SynTerm = field(default_factory=lambda: Var("x"))

    def _repr(self) -> str:
        return f"{self.func}({self.arg})"

    def free_vars(self) -> set[str]:
        return self.func.free_vars() | self.arg.free_vars()


@dataclass
class Pair(SynTerm):
    """Dependent pair (a, b) : Σ(x:A).B(x)."""
    fst: SynTerm = field(default_factory=lambda: Var("a"))
    snd: SynTerm = field(default_factory=lambda: Var("b"))

    def _repr(self) -> str:
        return f"({self.fst}, {self.snd})"

    def free_vars(self) -> set[str]:
        return self.fst.free_vars() | self.snd.free_vars()


@dataclass
class Fst(SynTerm):
    """First projection π₁(p)."""
    pair: SynTerm = field(default_factory=lambda: Var("p"))

    def _repr(self) -> str:
        return f"π₁({self.pair})"

    def free_vars(self) -> set[str]:
        return self.pair.free_vars()


@dataclass
class Snd(SynTerm):
    """Second projection π₂(p)."""
    pair: SynTerm = field(default_factory=lambda: Var("p"))

    def _repr(self) -> str:
        return f"π₂({self.pair})"

    def free_vars(self) -> set[str]:
        return self.pair.free_vars()


@dataclass
class PathAbs(SynTerm):
    """Path abstraction λ(i:I). t — a path between t[0/i] and t[1/i]."""
    ivar: str = "i"
    body: SynTerm = field(default_factory=lambda: Var("x"))

    def _repr(self) -> str:
        return f"<{self.ivar}> {self.body}"

    def free_vars(self) -> set[str]:
        return self.body.free_vars() - {self.ivar}


@dataclass
class PathApp(SynTerm):
    """Path application p @ r — apply a path at a dimension value."""
    path: SynTerm = field(default_factory=lambda: Var("p"))
    arg: SynTerm = field(default_factory=lambda: Literal(0))

    def _repr(self) -> str:
        return f"{self.path} @ {self.arg}"

    def free_vars(self) -> set[str]:
        return self.path.free_vars() | self.arg.free_vars()


@dataclass
class Transport(SynTerm):
    """Transport along a path: transp(P, p, d).
    Given P : A → Type, p : a =_A b, d : P(a), produces P(b).
    """
    type_family: SynTerm = field(default_factory=lambda: Var("P"))
    path: SynTerm = field(default_factory=lambda: Var("p"))
    base_term: SynTerm = field(default_factory=lambda: Var("d"))

    def _repr(self) -> str:
        return f"transp({self.type_family}, {self.path}, {self.base_term})"

    def free_vars(self) -> set[str]:
        return (self.type_family.free_vars() |
                self.path.free_vars() |
                self.base_term.free_vars())


@dataclass
class Comp(SynTerm):
    """Kan composition: comp^A [φ ↦ u] u0.
    The composition operation of cubical type theory.
    """
    type_: SynType = field(default_factory=PyObjType)
    face: str = "1=1"
    partial_term: SynTerm | None = None
    base: SynTerm = field(default_factory=lambda: Var("u0"))

    def _repr(self) -> str:
        return f"comp^{{{self.type_}}}[{self.face}]({self.base})"

    def free_vars(self) -> set[str]:
        fv = self.base.free_vars()
        if self.partial_term:
            fv |= self.partial_term.free_vars()
        return fv


@dataclass
class LetIn(SynTerm):
    """Let binding: let x = e in body."""
    var_name: str = "x"
    var_type: SynType | None = None
    value: SynTerm = field(default_factory=lambda: Var("e"))
    body: SynTerm = field(default_factory=lambda: Var("x"))

    def _repr(self) -> str:
        ty = f" : {self.var_type}" if self.var_type else ""
        return f"let {self.var_name}{ty} = {self.value} in {self.body}"

    def free_vars(self) -> set[str]:
        return self.value.free_vars() | (self.body.free_vars() - {self.var_name})


@dataclass
class IfThenElse(SynTerm):
    """Conditional: if cond then t else f."""
    cond: SynTerm = field(default_factory=lambda: Var("c"))
    then_branch: SynTerm = field(default_factory=lambda: Var("t"))
    else_branch: SynTerm = field(default_factory=lambda: Var("f"))

    def _repr(self) -> str:
        return f"if {self.cond} then {self.then_branch} else {self.else_branch}"

    def free_vars(self) -> set[str]:
        return (self.cond.free_vars() |
                self.then_branch.free_vars() |
                self.else_branch.free_vars())


@dataclass
class PyCall(SynTerm):
    """Python function call with positional and keyword args."""
    func: SynTerm = field(default_factory=lambda: Var("f"))
    args: tuple[SynTerm, ...] = ()
    kwargs: tuple[tuple[str, SynTerm], ...] = ()

    def _repr(self) -> str:
        parts = [str(a) for a in self.args]
        parts += [f"{k}={v}" for k, v in self.kwargs]
        return f"{self.func}({', '.join(parts)})"

    def free_vars(self) -> set[str]:
        fv = self.func.free_vars()
        for a in self.args:
            fv |= a.free_vars()
        for _, v in self.kwargs:
            fv |= v.free_vars()
        return fv


@dataclass
class GetAttr(SynTerm):
    """Attribute access: obj.attr."""
    obj: SynTerm = field(default_factory=lambda: Var("obj"))
    attr: str = ""

    def _repr(self) -> str:
        return f"{self.obj}.{self.attr}"

    def free_vars(self) -> set[str]:
        return self.obj.free_vars()


@dataclass
class GetItem(SynTerm):
    """Subscript access: obj[key]."""
    obj: SynTerm = field(default_factory=lambda: Var("obj"))
    key: SynTerm = field(default_factory=lambda: Var("key"))

    def _repr(self) -> str:
        return f"{self.obj}[{self.key}]"

    def free_vars(self) -> set[str]:
        return self.obj.free_vars() | self.key.free_vars()


# ═══════════════════════════════════════════════════════════════════
# Contexts
# ═══════════════════════════════════════════════════════════════════

@dataclass
class Context:
    """Typing context Γ = x₁:A₁, x₂:A₂, ..."""
    bindings: dict[str, SynType] = field(default_factory=dict)
    parent: Context | None = None

    def extend(self, name: str, ty: SynType) -> Context:
        """Create a new context with an additional binding."""
        return Context(bindings={**self.bindings, name: ty}, parent=self)

    def lookup(self, name: str) -> SynType | None:
        """Look up a variable's type."""
        if name in self.bindings:
            return self.bindings[name]
        if self.parent:
            return self.parent.lookup(name)
        return None

    def __contains__(self, name: str) -> bool:
        return self.lookup(name) is not None

    def all_bindings(self) -> dict[str, SynType]:
        """Get all bindings including from parent contexts."""
        result = {}
        if self.parent:
            result.update(self.parent.all_bindings())
        result.update(self.bindings)
        return result


# ═══════════════════════════════════════════════════════════════════
# Judgments
# ═══════════════════════════════════════════════════════════════════

class JudgmentKind(Enum):
    """Kinds of judgments in the type theory."""
    TYPE_CHECK = auto()      # Γ ⊢ a : A
    TYPE_SYNTH = auto()      # Γ ⊢ a ⇒ A
    EQUAL = auto()           # Γ ⊢ a = b : A
    SUBTYPE = auto()         # Γ ⊢ A <: B
    WELL_FORMED = auto()     # Γ ⊢ A type


@dataclass
class Judgment:
    """A type-theoretic judgment."""
    kind: JudgmentKind
    context: Context
    term: SynTerm | None = None
    type_: SynType | None = None
    # For equality judgments
    left: SynTerm | None = None
    right: SynTerm | None = None

    def __repr__(self) -> str:
        ctx = ", ".join(f"{k}:{v}" for k, v in self.context.all_bindings().items())
        if self.kind == JudgmentKind.TYPE_CHECK:
            return f"{ctx} ⊢ {self.term} : {self.type_}"
        elif self.kind == JudgmentKind.EQUAL:
            return f"{ctx} ⊢ {self.left} = {self.right} : {self.type_}"
        elif self.kind == JudgmentKind.SUBTYPE:
            return f"{ctx} ⊢ {self.left} <: {self.right}"
        elif self.kind == JudgmentKind.WELL_FORMED:
            return f"{ctx} ⊢ {self.type_} type"
        return f"Judgment({self.kind})"


# ═══════════════════════════════════════════════════════════════════
# Specifications
# ═══════════════════════════════════════════════════════════════════

class SpecKind(Enum):
    """Kinds of specifications."""
    GUARANTEE = auto()     # postcondition (@guarantee)
    ASSUME = auto()        # precondition (assume())
    CHECK = auto()         # internal invariant (check())
    AXIOM = auto()         # library axiom (given())
    EQUIVALENCE = auto()   # f ≡ g


@dataclass
class Spec:
    """A specification attached to a Python function or expression."""
    kind: SpecKind
    description: str                   # NL description
    formal: str | None = None          # Formalized predicate (optional)
    source_func: str | None = None     # Python function name
    source_file: str | None = None     # Source file path
    source_line: int | None = None     # Source line number

    def __repr__(self) -> str:
        return f"@{self.kind.name.lower()}(\"{self.description}\")"


@dataclass
class FunctionSpec:
    """Complete specification for a Python function."""
    name: str
    params: list[tuple[str, SynType]]
    return_type: SynType
    guarantees: list[Spec] = field(default_factory=list)
    assumptions: list[Spec] = field(default_factory=list)
    checks: list[Spec] = field(default_factory=list)
    effect: str = "Pure"  # Effect annotation

    def proof_obligations(self) -> list[Judgment]:
        """Generate the proof obligations for this function."""
        obligations = []
        ctx = Context()
        for pname, ptype in self.params:
            ctx = ctx.extend(pname, ptype)
        for g in self.guarantees:
            obligations.append(Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx,
                term=Var(self.name),
                type_=RefinementType(
                    base_type=self.return_type,
                    predicate=g.description,
                ),
            ))
        return obligations


# ═══════════════════════════════════════════════════════════════════
# Helper constructors
# ═══════════════════════════════════════════════════════════════════

def arrow(a: SynType, b: SynType) -> PiType:
    """Non-dependent function type A → B."""
    return PiType(param_name="_", param_type=a, body_type=b)


def product(a: SynType, b: SynType) -> SigmaType:
    """Non-dependent pair type A × B."""
    return SigmaType(fst_name="_", fst_type=a, snd_type=b)


def nat_type() -> RefinementType:
    """Natural numbers: {n : int | n ≥ 0}."""
    return RefinementType(base_type=PyIntType(), var_name="n", predicate="n >= 0")


def pos_int_type() -> RefinementType:
    """Positive integers: {n : int | n > 0}."""
    return RefinementType(base_type=PyIntType(), var_name="n", predicate="n > 0")
