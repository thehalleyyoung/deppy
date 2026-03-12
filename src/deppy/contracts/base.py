"""Base contract types for DepPy's sheaf-descent semantic typing system.

Contracts are boundary seeds — they seed the input/output boundaries of
the site cover.  A ``requires`` is an input-boundary seed; an ``ensures``
is an output-boundary seed.  This module defines the abstract contract
base, lightweight predicate/term/type representations used across the
contracts layer, and the ContractSet that aggregates contracts per scope.
"""

from __future__ import annotations

import ast
import enum
import inspect
import textwrap
import uuid
from abc import ABC, abstractmethod
from dataclasses import dataclass, field, replace
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterable,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

if TYPE_CHECKING:
    from deppy.core._protocols import (
        BoundarySection,
        LocalSection,
        SiteId,
        SiteKind,
        TrustLevel,
    )

from deppy.core._protocols import TrustLevel  # noqa: E402 – runtime import


# ---------------------------------------------------------------------------
# Lightweight foundational types
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SourceLocation:
    """A location in Python source code."""

    file: str
    line: int
    col: int = 0
    end_line: Optional[int] = None
    end_col: Optional[int] = None

    def __str__(self) -> str:
        loc = f"{self.file}:{self.line}"
        if self.col:
            loc += f":{self.col}"
        return loc

    def contains(self, other: SourceLocation) -> bool:
        """Return True if *other* is within this span."""
        if self.file != other.file:
            return False
        if self.end_line is None:
            return self.line == other.line
        return self.line <= other.line and (
            self.end_line >= other.line
            if other.end_line is None
            else self.end_line >= other.end_line
        )


# ---------------------------------------------------------------------------
# Term: expression tree for predicate operands
# ---------------------------------------------------------------------------


class TermKind(enum.Enum):
    """Kind of a term node."""

    VARIABLE = "variable"
    CONSTANT = "constant"
    UNARY_OP = "unary_op"
    BINARY_OP = "binary_op"
    CALL = "call"
    ATTRIBUTE = "attribute"
    SUBSCRIPT = "subscript"


@dataclass(frozen=True)
class Term:
    """Symbolic expression tree used in predicates.

    Rather than storing raw Python AST everywhere, we normalise into a
    small expression language that is easier to manipulate, serialise, and
    transport across sites.
    """

    kind: TermKind
    value: Any = None
    children: Tuple[Term, ...] = ()
    _source: Optional[str] = None  # original source fragment

    # -- constructors -------------------------------------------------------

    @classmethod
    def var(cls, name: str) -> Term:
        return cls(kind=TermKind.VARIABLE, value=name)

    @classmethod
    def const(cls, value: object) -> Term:
        return cls(kind=TermKind.CONSTANT, value=value)

    @classmethod
    def unary(cls, op: str, operand: Term) -> Term:
        return cls(kind=TermKind.UNARY_OP, value=op, children=(operand,))

    @classmethod
    def binary(cls, op: str, left: Term, right: Term) -> Term:
        return cls(kind=TermKind.BINARY_OP, value=op, children=(left, right))

    @classmethod
    def call(cls, func: Term, args: Sequence[Term]) -> Term:
        return cls(kind=TermKind.CALL, children=(func, *args))

    @classmethod
    def attr(cls, obj: Term, attribute: str) -> Term:
        return cls(kind=TermKind.ATTRIBUTE, value=attribute, children=(obj,))

    @classmethod
    def subscript(cls, obj: Term, index: Term) -> Term:
        return cls(kind=TermKind.SUBSCRIPT, children=(obj, index))

    # -- queries ------------------------------------------------------------

    def free_variables(self) -> FrozenSet[str]:
        """Return all free variable names in this term."""
        if self.kind is TermKind.VARIABLE:
            return frozenset({self.value})
        result: Set[str] = set()
        for child in self.children:
            result |= child.free_variables()
        return frozenset(result)

    def substitute(self, bindings: Mapping[str, Term]) -> Term:
        """Return a new term with variables replaced per *bindings*."""
        if self.kind is TermKind.VARIABLE:
            return bindings.get(self.value, self)
        if not self.children:
            return self
        new_children = tuple(c.substitute(bindings) for c in self.children)
        return replace(self, children=new_children)

    # -- display ------------------------------------------------------------

    def pretty(self) -> str:
        if self._source is not None:
            return self._source
        if self.kind is TermKind.VARIABLE:
            return str(self.value)
        if self.kind is TermKind.CONSTANT:
            return repr(self.value)
        if self.kind is TermKind.UNARY_OP:
            return f"({self.value} {self.children[0].pretty()})"
        if self.kind is TermKind.BINARY_OP:
            return f"({self.children[0].pretty()} {self.value} {self.children[1].pretty()})"
        if self.kind is TermKind.CALL:
            func_str = self.children[0].pretty()
            args_str = ", ".join(c.pretty() for c in self.children[1:])
            return f"{func_str}({args_str})"
        if self.kind is TermKind.ATTRIBUTE:
            return f"{self.children[0].pretty()}.{self.value}"
        if self.kind is TermKind.SUBSCRIPT:
            return f"{self.children[0].pretty()}[{self.children[1].pretty()}]"
        return f"<Term {self.kind.value}>"  # pragma: no cover

    def __str__(self) -> str:
        return self.pretty()


# ---------------------------------------------------------------------------
# Predicate: a logical assertion composed of terms
# ---------------------------------------------------------------------------


class PredicateKind(enum.Enum):
    ATOMIC = "atomic"
    COMPARISON = "comparison"
    CONJUNCTION = "conjunction"
    DISJUNCTION = "disjunction"
    NEGATION = "negation"
    IMPLICATION = "implication"
    FORALL = "forall"
    EXISTS = "exists"
    CALLABLE = "callable"
    TRUE = "true"
    FALSE = "false"


@dataclass(frozen=True)
class Predicate:
    """A logical predicate used in contracts.

    Predicates form a Boolean algebra with conjunction (``&``),
    disjunction (``|``), negation (``~``), and implication
    (``.implies()``).  They can also wrap raw Python callables for
    runtime checking.
    """

    kind: PredicateKind
    terms: Tuple[Term, ...] = ()
    children: Tuple[Predicate, ...] = ()
    quantified_vars: Tuple[str, ...] = ()
    callable_fn: Optional[Callable[..., bool]] = field(default=None, hash=False)
    description: Optional[str] = None
    _source_text: Optional[str] = None

    # -- constructors -------------------------------------------------------

    @classmethod
    def true_(cls) -> Predicate:
        return cls(kind=PredicateKind.TRUE, description="true")

    @classmethod
    def false_(cls) -> Predicate:
        return cls(kind=PredicateKind.FALSE, description="false")

    @classmethod
    def atomic(cls, term: Term, *, description: Optional[str] = None) -> Predicate:
        return cls(kind=PredicateKind.ATOMIC, terms=(term,), description=description)

    @classmethod
    def comparison(
        cls, op: str, left: Term, right: Term, *, description: Optional[str] = None,
    ) -> Predicate:
        comp_term = Term.binary(op, left, right)
        return cls(
            kind=PredicateKind.COMPARISON,
            terms=(comp_term,),
            description=description or comp_term.pretty(),
        )

    @classmethod
    def from_callable(
        cls,
        fn: Callable[..., bool],
        *,
        param_names: Optional[List[str]] = None,
        description: Optional[str] = None,
    ) -> Predicate:
        """Wrap a Python callable as a predicate."""
        if param_names is None:
            try:
                sig = inspect.signature(fn)
                param_names = list(sig.parameters.keys())
            except (ValueError, TypeError):
                param_names = []
        terms = tuple(Term.var(n) for n in param_names)
        desc = description or _callable_source(fn)
        return cls(
            kind=PredicateKind.CALLABLE,
            terms=terms,
            callable_fn=fn,
            description=desc,
        )

    @classmethod
    def conjunction(cls, *children: Predicate) -> Predicate:
        """Flatten nested conjunctions and absorb identity (TRUE)."""
        flat: list[Predicate] = []
        for child in children:
            if child.kind is PredicateKind.FALSE:
                return cls.false_()
            if child.kind is PredicateKind.TRUE:
                continue
            if child.kind is PredicateKind.CONJUNCTION:
                flat.extend(child.children)
            else:
                flat.append(child)
        if not flat:
            return cls.true_()
        if len(flat) == 1:
            return flat[0]
        return cls(kind=PredicateKind.CONJUNCTION, children=tuple(flat))

    @classmethod
    def disjunction(cls, *children: Predicate) -> Predicate:
        """Flatten nested disjunctions and absorb identity (FALSE)."""
        flat: list[Predicate] = []
        for child in children:
            if child.kind is PredicateKind.TRUE:
                return cls.true_()
            if child.kind is PredicateKind.FALSE:
                continue
            if child.kind is PredicateKind.DISJUNCTION:
                flat.extend(child.children)
            else:
                flat.append(child)
        if not flat:
            return cls.false_()
        if len(flat) == 1:
            return flat[0]
        return cls(kind=PredicateKind.DISJUNCTION, children=tuple(flat))

    @classmethod
    def negation(cls, child: Predicate) -> Predicate:
        if child.kind is PredicateKind.TRUE:
            return cls.false_()
        if child.kind is PredicateKind.FALSE:
            return cls.true_()
        if child.kind is PredicateKind.NEGATION:
            return child.children[0]  # double negation elimination
        return cls(kind=PredicateKind.NEGATION, children=(child,))

    @classmethod
    def implication(cls, antecedent: Predicate, consequent: Predicate) -> Predicate:
        if antecedent.kind is PredicateKind.FALSE:
            return cls.true_()  # vacuous truth
        if antecedent.kind is PredicateKind.TRUE:
            return consequent
        if consequent.kind is PredicateKind.TRUE:
            return cls.true_()
        return cls(
            kind=PredicateKind.IMPLICATION,
            children=(antecedent, consequent),
        )

    @classmethod
    def forall(cls, var: str, body: Predicate) -> Predicate:
        return cls(
            kind=PredicateKind.FORALL,
            children=(body,),
            quantified_vars=(var,),
        )

    @classmethod
    def exists(cls, var: str, body: Predicate) -> Predicate:
        return cls(
            kind=PredicateKind.EXISTS,
            children=(body,),
            quantified_vars=(var,),
        )

    # -- operators ----------------------------------------------------------

    def __and__(self, other: Predicate) -> Predicate:
        return Predicate.conjunction(self, other)

    def __or__(self, other: Predicate) -> Predicate:
        return Predicate.disjunction(self, other)

    def __invert__(self) -> Predicate:
        return Predicate.negation(self)

    def implies(self, other: Predicate) -> Predicate:
        return Predicate.implication(self, other)

    # -- queries ------------------------------------------------------------

    def free_variables(self) -> FrozenSet[str]:
        """All free variable names in this predicate."""
        bound: set[str] = set(self.quantified_vars)
        result: set[str] = set()
        for t in self.terms:
            result |= t.free_variables()
        for child in self.children:
            result |= child.free_variables()
        return frozenset(result - bound)

    def substitute(self, bindings: Mapping[str, Term]) -> Predicate:
        """Return predicate with term-level variable substitutions."""
        safe = {k: v for k, v in bindings.items() if k not in self.quantified_vars}
        new_terms = tuple(t.substitute(safe) for t in self.terms)
        new_children = tuple(c.substitute(safe) for c in self.children)
        return replace(self, terms=new_terms, children=new_children)

    @property
    def is_trivially_true(self) -> bool:
        return self.kind is PredicateKind.TRUE

    @property
    def is_trivially_false(self) -> bool:
        return self.kind is PredicateKind.FALSE

    # -- evaluation ---------------------------------------------------------

    def evaluate(self, env: Mapping[str, Any]) -> bool:
        """Evaluate the predicate in the given variable environment.

        For callable predicates this invokes the wrapped function; for
        structural predicates it evaluates recursively.  Returns True if
        evaluation is inconclusive (e.g. missing variables) — we err on
        the side of accepting.
        """
        if self.kind is PredicateKind.TRUE:
            return True
        if self.kind is PredicateKind.FALSE:
            return False
        if self.kind is PredicateKind.CALLABLE and self.callable_fn is not None:
            try:
                args = [env[t.value] for t in self.terms if t.kind is TermKind.VARIABLE]
                return bool(self.callable_fn(*args))
            except (KeyError, TypeError, Exception):
                return True  # inconclusive → accept
        if self.kind is PredicateKind.CONJUNCTION:
            return all(c.evaluate(env) for c in self.children)
        if self.kind is PredicateKind.DISJUNCTION:
            return any(c.evaluate(env) for c in self.children)
        if self.kind is PredicateKind.NEGATION:
            return not self.children[0].evaluate(env)
        if self.kind is PredicateKind.IMPLICATION:
            ant = self.children[0].evaluate(env)
            if not ant:
                return True
            return self.children[1].evaluate(env)
        # Atomic / comparison / quantified — can't evaluate structurally
        return True

    # -- display ------------------------------------------------------------

    def pretty(self) -> str:
        if self._source_text is not None:
            return self._source_text
        if self.description is not None:
            return self.description
        if self.kind is PredicateKind.TRUE:
            return "⊤"
        if self.kind is PredicateKind.FALSE:
            return "⊥"
        if self.kind is PredicateKind.ATOMIC:
            return self.terms[0].pretty() if self.terms else "?"
        if self.kind is PredicateKind.COMPARISON:
            return self.terms[0].pretty() if self.terms else "?"
        if self.kind is PredicateKind.CALLABLE:
            if self.description:
                return self.description
            return f"<callable({', '.join(t.pretty() for t in self.terms)})>"
        if self.kind is PredicateKind.CONJUNCTION:
            parts = " ∧ ".join(c.pretty() for c in self.children)
            return f"({parts})"
        if self.kind is PredicateKind.DISJUNCTION:
            parts = " ∨ ".join(c.pretty() for c in self.children)
            return f"({parts})"
        if self.kind is PredicateKind.NEGATION:
            return f"¬{self.children[0].pretty()}"
        if self.kind is PredicateKind.IMPLICATION:
            return f"({self.children[0].pretty()} → {self.children[1].pretty()})"
        if self.kind in (PredicateKind.FORALL, PredicateKind.EXISTS):
            q = "∀" if self.kind is PredicateKind.FORALL else "∃"
            var = ", ".join(self.quantified_vars)
            return f"{q}{var}. {self.children[0].pretty()}"
        return "<Predicate>"  # pragma: no cover

    def __str__(self) -> str:
        return self.pretty()


def _callable_source(fn: Callable[..., Any]) -> str:
    """Best-effort one-liner source for a callable."""
    try:
        src = inspect.getsource(fn).strip()
        # Handle lambda on one line
        if "lambda" in src:
            idx = src.index("lambda")
            return src[idx:].rstrip(" ,)")
        return src
    except (OSError, TypeError):
        return repr(fn)


# ---------------------------------------------------------------------------
# TypeBase: lightweight type representation
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TypeBase:
    """Lightweight stand-in for type information used by contracts.

    Full dependent types live in ``deppy.types``; this is the minimal
    surface needed by the contract layer to record type bounds on
    parameters and results.
    """

    name: str
    module: Optional[str] = None
    parameters: Tuple[TypeBase, ...] = ()
    refinement: Optional[Predicate] = None

    @classmethod
    def from_annotation(cls, annotation: Any) -> TypeBase:
        """Build a TypeBase from a runtime annotation value."""
        if isinstance(annotation, cls):
            return annotation
        if isinstance(annotation, type):
            return cls(name=annotation.__qualname__, module=getattr(annotation, "__module__", None))
        if isinstance(annotation, str):
            return cls(name=annotation)
        return cls(name=repr(annotation))

    def with_refinement(self, pred: Predicate) -> TypeBase:
        return replace(self, refinement=pred)

    def pretty(self) -> str:
        base = self.name
        if self.parameters:
            params = ", ".join(p.pretty() for p in self.parameters)
            base = f"{base}[{params}]"
        if self.refinement is not None:
            base = f"{{{base} | {self.refinement.pretty()}}}"
        return base

    def __str__(self) -> str:
        return self.pretty()


# ---------------------------------------------------------------------------
# Contract ABC
# ---------------------------------------------------------------------------


class Contract(ABC):
    """Base class for all DepPy contracts.

    Every contract can be projected to a :class:`Predicate` (its logical
    content) and to a :class:`~deppy.contracts.seed.BoundarySeed` (its
    role in the sheaf cover).
    """

    source_location: Optional[SourceLocation]
    trust: TrustLevel
    provenance: str  # "user_annotation", "synthesized", "proof_backed", …

    def __init__(
        self,
        *,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.RESIDUAL,
        provenance: str = "user_annotation",
    ) -> None:
        self.source_location = source_location
        self.trust = trust
        self.provenance = provenance
        self._uid: str = uuid.uuid4().hex[:12]

    @property
    def uid(self) -> str:
        """Stable unique id for this contract instance."""
        return self._uid

    @abstractmethod
    def to_predicate(self) -> Predicate:
        """Project to the logical predicate content."""

    @abstractmethod
    def to_boundary_seed(self) -> Any:
        """Project to a BoundarySeed for cover synthesis.

        Returns ``Any`` here to avoid circular imports; concrete
        subclasses return the appropriate seed type from ``seed.py``.
        """

    @abstractmethod
    def pretty(self) -> str:
        """Human-readable rendering."""

    def with_trust(self, trust: TrustLevel) -> Contract:
        """Return a copy with a different trust level."""
        import copy

        new = copy.copy(self)
        new.trust = trust
        return new

    def with_provenance(self, provenance: str) -> Contract:
        """Return a copy with different provenance."""
        import copy

        new = copy.copy(self)
        new.provenance = provenance
        return new

    def __repr__(self) -> str:
        return f"<{type(self).__name__} trust={self.trust.value} prov={self.provenance}>"


# ---------------------------------------------------------------------------
# ContractSet
# ---------------------------------------------------------------------------


class ContractSet:
    """Aggregate of contracts attached to a single scope (function, class, module).

    A ``ContractSet`` splits its contents by role:

    * **requires** — input preconditions (input boundary seeds)
    * **ensures** — output postconditions (output boundary seeds)
    * **invariants** — loop / class / module invariants
    * **witnesses** — witness-carrying contracts
    * **theorems** — theorem / lemma / transport / assumption declarations
    """

    __slots__ = ("requires", "ensures", "invariants", "witnesses", "theorems", "_scope_name")

    def __init__(
        self,
        *,
        requires: Optional[List[Any]] = None,
        ensures: Optional[List[Any]] = None,
        invariants: Optional[List[Any]] = None,
        witnesses: Optional[List[Any]] = None,
        theorems: Optional[List[Any]] = None,
        scope_name: str = "",
    ) -> None:
        self.requires: List[Any] = requires if requires is not None else []
        self.ensures: List[Any] = ensures if ensures is not None else []
        self.invariants: List[Any] = invariants if invariants is not None else []
        self.witnesses: List[Any] = witnesses if witnesses is not None else []
        self.theorems: List[Any] = theorems if theorems is not None else []
        self._scope_name = scope_name

    @property
    def scope_name(self) -> str:
        return self._scope_name

    # -- queries ------------------------------------------------------------

    def is_empty(self) -> bool:
        return not (
            self.requires or self.ensures or self.invariants or self.witnesses or self.theorems
        )

    def __len__(self) -> int:
        return (
            len(self.requires)
            + len(self.ensures)
            + len(self.invariants)
            + len(self.witnesses)
            + len(self.theorems)
        )

    def all_contracts(self) -> List[Contract]:
        """Flat list of every contract in the set."""
        result: List[Contract] = []
        for bucket in (self.requires, self.ensures, self.invariants, self.witnesses, self.theorems):
            result.extend(bucket)
        return result

    # -- seeds --------------------------------------------------------------

    def input_seeds(self) -> List[Any]:
        """Collect input-boundary seeds from all requires contracts."""
        seeds: List[Any] = []
        for req in self.requires:
            seed = req.to_boundary_seed()
            if seed is not None:
                seeds.append(seed)
        return seeds

    def output_seeds(self) -> List[Any]:
        """Collect output-boundary seeds from all ensures contracts."""
        seeds: List[Any] = []
        for ens in self.ensures:
            seed = ens.to_boundary_seed()
            if seed is not None:
                seeds.append(seed)
        return seeds

    # -- combinators --------------------------------------------------------

    def merge(self, other: ContractSet) -> ContractSet:
        """Return a new ContractSet merging *self* and *other*.

        Contracts are concatenated per role; no deduplication is performed
        at this stage (dedup happens when seeds are collected).
        """
        return ContractSet(
            requires=self.requires + other.requires,
            ensures=self.ensures + other.ensures,
            invariants=self.invariants + other.invariants,
            witnesses=self.witnesses + other.witnesses,
            theorems=self.theorems + other.theorems,
            scope_name=self._scope_name or other._scope_name,
        )

    def filter_by_trust(self, min_trust: TrustLevel) -> ContractSet:
        """Return a new ContractSet containing only contracts at or above *min_trust*.

        Trust ordering (most to least trusted):
        PROOF_BACKED > TRUSTED_AUTO > BOUNDED_AUTO > TRACE_BACKED > ASSUMED > RESIDUAL
        """
        order = _TRUST_ORDER
        threshold = order.get(min_trust, 0)

        def _keep(c: Contract) -> bool:
            return order.get(c.trust, 0) >= threshold

        return ContractSet(
            requires=[c for c in self.requires if _keep(c)],
            ensures=[c for c in self.ensures if _keep(c)],
            invariants=[c for c in self.invariants if _keep(c)],
            witnesses=[c for c in self.witnesses if _keep(c)],
            theorems=[c for c in self.theorems if _keep(c)],
            scope_name=self._scope_name,
        )

    def with_scope(self, name: str) -> ContractSet:
        """Return a copy with the scope name updated."""
        return ContractSet(
            requires=list(self.requires),
            ensures=list(self.ensures),
            invariants=list(self.invariants),
            witnesses=list(self.witnesses),
            theorems=list(self.theorems),
            scope_name=name,
        )

    # -- display ------------------------------------------------------------

    def pretty(self) -> str:
        lines: List[str] = []
        if self._scope_name:
            lines.append(f"Contracts for {self._scope_name}:")
        for label, bucket in [
            ("requires", self.requires),
            ("ensures", self.ensures),
            ("invariant", self.invariants),
            ("witness", self.witnesses),
            ("theorem", self.theorems),
        ]:
            for c in bucket:
                lines.append(f"  @{label}: {c.pretty()}")
        return "\n".join(lines) if lines else "<empty ContractSet>"

    def __repr__(self) -> str:
        counts = (
            f"req={len(self.requires)} ens={len(self.ensures)} "
            f"inv={len(self.invariants)} wit={len(self.witnesses)} thm={len(self.theorems)}"
        )
        return f"<ContractSet {counts}>"


# Trust ordering for filtering — higher number = more trusted.
_TRUST_ORDER: Dict[TrustLevel, int] = {
    TrustLevel.RESIDUAL: 0,
    TrustLevel.ASSUMED: 1,
    TrustLevel.TRACE_BACKED: 2,
    TrustLevel.BOUNDED_AUTO: 3,
    TrustLevel.TRUSTED_AUTO: 4,
    TrustLevel.PROOF_BACKED: 5,
}
