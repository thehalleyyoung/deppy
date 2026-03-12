"""Boolean / compound predicates and simplification.

Provides:

- Logical connectives: ``And``, ``Or``, ``Not``, ``Implies``, ``Iff``.
- Quantifiers: ``ForAll``, ``Exists``.
- ``BooleanSimplifier`` with CNF, DNF, and NNF conversions.

Module-level sentinels ``_TRUE`` and ``_FALSE`` represent tautology /
contradiction as ``And([])`` and ``Or([])`` respectively, following the
convention that an empty conjunction is *true* and an empty disjunction
is *false*.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    Iterator,
    List,
    Optional,
    Sequence,
    Set,
)

from deppy.predicates.base import (
    Predicate,
    SourceLocation,
    Term,
    Var,
)


# ===================================================================
#  And / Or
# ===================================================================

@dataclass(frozen=True)
class And(Predicate):
    """Conjunction of zero or more predicates.

    An empty ``And([])`` is the logical constant **True**.
    """

    conjuncts: tuple[Predicate, ...] = field(default_factory=tuple)
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def __init__(
        self,
        conjuncts: Sequence[Predicate] = (),
        source_location: Optional[SourceLocation] = None,
    ) -> None:
        object.__setattr__(self, "conjuncts", tuple(conjuncts))
        object.__setattr__(self, "source_location", source_location)

    def free_variables(self) -> Set[str]:
        result: Set[str] = set()
        for c in self.conjuncts:
            result |= c.free_variables()
        return result

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return And(
            [c.substitute(mapping) for c in self.conjuncts],
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return Or([c.negate() for c in self.conjuncts],
                  source_location=self.source_location)

    def simplify(self) -> Predicate:
        simplified: List[Predicate] = []
        for c in self.conjuncts:
            s = c.simplify()
            if isinstance(s, Or) and len(s.disjuncts) == 0:
                return _FALSE  # anything ∧ False = False
            if isinstance(s, And) and len(s.conjuncts) == 0:
                continue  # skip True
            if isinstance(s, And):
                simplified.extend(s.conjuncts)
            else:
                simplified.append(s)
        # Deduplicate while preserving order
        seen: set[Predicate] = set()
        deduped: List[Predicate] = []
        for p in simplified:
            if p not in seen:
                seen.add(p)
                deduped.append(p)
        if not deduped:
            return _TRUE
        if len(deduped) == 1:
            return deduped[0]
        return And(deduped, source_location=self.source_location)

    def pretty(self) -> str:
        if not self.conjuncts:
            return "True"
        parts = [c.pretty() for c in self.conjuncts]
        return " ∧ ".join(f"({p})" if " " in p else p for p in parts)

    def walk(self) -> Iterator[Predicate]:
        yield self
        for c in self.conjuncts:
            yield from c.walk()

    def walk_terms(self) -> Iterator[Term]:
        for c in self.conjuncts:
            yield from c.walk_terms()

    def __repr__(self) -> str:
        return f"And({list(self.conjuncts)!r})"


@dataclass(frozen=True)
class Or(Predicate):
    """Disjunction of zero or more predicates.

    An empty ``Or([])`` is the logical constant **False**.
    """

    disjuncts: tuple[Predicate, ...] = field(default_factory=tuple)
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def __init__(
        self,
        disjuncts: Sequence[Predicate] = (),
        source_location: Optional[SourceLocation] = None,
    ) -> None:
        object.__setattr__(self, "disjuncts", tuple(disjuncts))
        object.__setattr__(self, "source_location", source_location)

    def free_variables(self) -> Set[str]:
        result: Set[str] = set()
        for d in self.disjuncts:
            result |= d.free_variables()
        return result

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Or(
            [d.substitute(mapping) for d in self.disjuncts],
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return And([d.negate() for d in self.disjuncts],
                   source_location=self.source_location)

    def simplify(self) -> Predicate:
        simplified: List[Predicate] = []
        for d in self.disjuncts:
            s = d.simplify()
            if isinstance(s, And) and len(s.conjuncts) == 0:
                return _TRUE  # anything ∨ True = True
            if isinstance(s, Or) and len(s.disjuncts) == 0:
                continue  # skip False
            if isinstance(s, Or):
                simplified.extend(s.disjuncts)
            else:
                simplified.append(s)
        seen: set[Predicate] = set()
        deduped: List[Predicate] = []
        for p in simplified:
            if p not in seen:
                seen.add(p)
                deduped.append(p)
        if not deduped:
            return _FALSE
        if len(deduped) == 1:
            return deduped[0]
        return Or(deduped, source_location=self.source_location)

    def pretty(self) -> str:
        if not self.disjuncts:
            return "False"
        parts = [d.pretty() for d in self.disjuncts]
        return " ∨ ".join(f"({p})" if " " in p else p for p in parts)

    def walk(self) -> Iterator[Predicate]:
        yield self
        for d in self.disjuncts:
            yield from d.walk()

    def walk_terms(self) -> Iterator[Term]:
        for d in self.disjuncts:
            yield from d.walk_terms()

    def __repr__(self) -> str:
        return f"Or({list(self.disjuncts)!r})"


# ===================================================================
#  Not
# ===================================================================

@dataclass(frozen=True)
class Not(Predicate):
    """Logical negation."""

    operand: Predicate
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.operand.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Not(
            self.operand.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return self.operand

    def simplify(self) -> Predicate:
        inner = self.operand.simplify()
        if isinstance(inner, Not):
            return inner.operand
        if isinstance(inner, And) and len(inner.conjuncts) == 0:
            return _FALSE  # ¬True = False
        if isinstance(inner, Or) and len(inner.disjuncts) == 0:
            return _TRUE  # ¬False = True
        return Not(inner, source_location=self.source_location)

    def pretty(self) -> str:
        inner = self.operand.pretty()
        return f"¬({inner})"

    def walk(self) -> Iterator[Predicate]:
        yield self
        yield from self.operand.walk()

    def walk_terms(self) -> Iterator[Term]:
        yield from self.operand.walk_terms()

    def __repr__(self) -> str:
        return f"Not({self.operand!r})"


# ===================================================================
#  Implies / Iff
# ===================================================================

@dataclass(frozen=True)
class Implies(Predicate):
    """Logical implication: ``antecedent → consequent``."""

    antecedent: Predicate
    consequent: Predicate
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.antecedent.free_variables() | self.consequent.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Implies(
            self.antecedent.substitute(mapping),
            self.consequent.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        # ¬(A → B) ⟺ A ∧ ¬B
        return And(
            [self.antecedent, self.consequent.negate()],
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        a = self.antecedent.simplify()
        b = self.consequent.simplify()
        # False → anything = True
        if isinstance(a, Or) and len(a.disjuncts) == 0:
            return _TRUE
        # anything → True = True
        if isinstance(b, And) and len(b.conjuncts) == 0:
            return _TRUE
        # True → B = B
        if isinstance(a, And) and len(a.conjuncts) == 0:
            return b
        return Implies(a, b, source_location=self.source_location)

    def pretty(self) -> str:
        return f"({self.antecedent.pretty()}) → ({self.consequent.pretty()})"

    def walk(self) -> Iterator[Predicate]:
        yield self
        yield from self.antecedent.walk()
        yield from self.consequent.walk()

    def walk_terms(self) -> Iterator[Term]:
        yield from self.antecedent.walk_terms()
        yield from self.consequent.walk_terms()

    def __repr__(self) -> str:
        return f"Implies({self.antecedent!r}, {self.consequent!r})"


@dataclass(frozen=True)
class Iff(Predicate):
    """Logical biconditional: ``left ↔ right``."""

    left: Predicate
    right: Predicate
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Iff(
            self.left.substitute(mapping),
            self.right.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        # ¬(A ↔ B) ⟺ (A ∧ ¬B) ∨ (¬A ∧ B)
        return Or([
            And([self.left, self.right.negate()]),
            And([self.left.negate(), self.right]),
        ], source_location=self.source_location)

    def simplify(self) -> Predicate:
        a = self.left.simplify()
        b = self.right.simplify()
        if a == b:
            return _TRUE
        return Iff(a, b, source_location=self.source_location)

    def pretty(self) -> str:
        return f"({self.left.pretty()}) ↔ ({self.right.pretty()})"

    def walk(self) -> Iterator[Predicate]:
        yield self
        yield from self.left.walk()
        yield from self.right.walk()

    def walk_terms(self) -> Iterator[Term]:
        yield from self.left.walk_terms()
        yield from self.right.walk_terms()

    def __repr__(self) -> str:
        return f"Iff({self.left!r}, {self.right!r})"


# ===================================================================
#  Quantifiers
# ===================================================================

@dataclass(frozen=True)
class ForAll(Predicate):
    """Universal quantification: ``∀ var : domain . body``."""

    var: str
    body: Predicate
    domain: Any = None  # Optional type constraint (string annotation to avoid circular import)
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.body.free_variables() - {self.var}

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        if self.var in mapping:
            # Avoid capture: skip bound variable
            new_mapping = {k: v for k, v in mapping.items() if k != self.var}
        else:
            new_mapping = mapping
        return ForAll(
            var=self.var,
            body=self.body.substitute(new_mapping),
            domain=self.domain,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return Exists(
            var=self.var, body=self.body.negate(),
            domain=self.domain,
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        inner = self.body.simplify()
        # If the bound variable is not free in the body, drop quantifier
        if self.var not in inner.free_variables():
            return inner
        return ForAll(
            var=self.var, body=inner, domain=self.domain,
            source_location=self.source_location,
        )

    def pretty(self) -> str:
        dom = f" : {self.domain}" if self.domain is not None else ""
        return f"∀ {self.var}{dom} . {self.body.pretty()}"

    def walk(self) -> Iterator[Predicate]:
        yield self
        yield from self.body.walk()

    def walk_terms(self) -> Iterator[Term]:
        yield from self.body.walk_terms()

    def __repr__(self) -> str:
        return f"ForAll({self.var!r}, {self.body!r})"


@dataclass(frozen=True)
class Exists(Predicate):
    """Existential quantification: ``∃ var : domain . body``."""

    var: str
    body: Predicate
    domain: Any = None
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return self.body.free_variables() - {self.var}

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        if self.var in mapping:
            new_mapping = {k: v for k, v in mapping.items() if k != self.var}
        else:
            new_mapping = mapping
        return Exists(
            var=self.var,
            body=self.body.substitute(new_mapping),
            domain=self.domain,
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return ForAll(
            var=self.var, body=self.body.negate(),
            domain=self.domain,
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        inner = self.body.simplify()
        if self.var not in inner.free_variables():
            return inner
        return Exists(
            var=self.var, body=inner, domain=self.domain,
            source_location=self.source_location,
        )

    def pretty(self) -> str:
        dom = f" : {self.domain}" if self.domain is not None else ""
        return f"∃ {self.var}{dom} . {self.body.pretty()}"

    def walk(self) -> Iterator[Predicate]:
        yield self
        yield from self.body.walk()

    def walk_terms(self) -> Iterator[Term]:
        yield from self.body.walk_terms()

    def __repr__(self) -> str:
        return f"Exists({self.var!r}, {self.body!r})"


# ===================================================================
#  Canonical singletons
# ===================================================================

_TRUE: And = And([])
"""Logical *True*: empty conjunction."""

_FALSE: Or = Or([])
"""Logical *False*: empty disjunction."""


def is_true(pred: Predicate) -> bool:
    """Check whether *pred* is the canonical True."""
    return isinstance(pred, And) and len(pred.conjuncts) == 0


def is_false(pred: Predicate) -> bool:
    """Check whether *pred* is the canonical False."""
    return isinstance(pred, Or) and len(pred.disjuncts) == 0


# ===================================================================
#  Boolean simplifier
# ===================================================================

class BooleanSimplifier:
    """Simplifies boolean predicate trees and converts to normal forms.

    Implements NNF (negation normal form), CNF (conjunctive normal form),
    and DNF (disjunctive normal form) transformations, as well as a
    general ``simplify`` pass that folds constants and flattens nesting.
    """

    def simplify(self, pred: Predicate) -> Predicate:
        """Apply iterative simplification until a fixpoint."""
        current = pred
        for _ in range(20):  # bounded iteration
            next_ = current.simplify()
            if next_ == current:
                return current
            current = next_
        return current

    def to_nnf(self, pred: Predicate) -> Predicate:
        """Convert *pred* to negation normal form.

        In NNF, negation only appears directly in front of atomic
        predicates.  Implications and biconditionals are eliminated.
        """
        if isinstance(pred, And):
            return And([self.to_nnf(c) for c in pred.conjuncts])
        if isinstance(pred, Or):
            return Or([self.to_nnf(d) for d in pred.disjuncts])
        if isinstance(pred, Implies):
            # A → B ⟺ ¬A ∨ B
            return Or([self.to_nnf(pred.antecedent.negate()), self.to_nnf(pred.consequent)])
        if isinstance(pred, Iff):
            # A ↔ B ⟺ (A → B) ∧ (B → A)
            return And([
                self.to_nnf(Implies(pred.left, pred.right)),
                self.to_nnf(Implies(pred.right, pred.left)),
            ])
        if isinstance(pred, Not):
            return self._push_negation(pred.operand)
        return pred

    def _push_negation(self, pred: Predicate) -> Predicate:
        """Push a negation inward (De Morgan + quantifier duality)."""
        if isinstance(pred, And):
            return Or([self._push_negation(c) for c in pred.conjuncts])
        if isinstance(pred, Or):
            return And([self._push_negation(d) for d in pred.disjuncts])
        if isinstance(pred, Not):
            return self.to_nnf(pred.operand)
        if isinstance(pred, Implies):
            # ¬(A → B) ⟺ A ∧ ¬B
            return And([self.to_nnf(pred.antecedent), self._push_negation(pred.consequent)])
        if isinstance(pred, Iff):
            return self.to_nnf(pred.negate())
        if isinstance(pred, ForAll):
            return Exists(
                var=pred.var,
                body=self._push_negation(pred.body),
                domain=pred.domain,
            )
        if isinstance(pred, Exists):
            return ForAll(
                var=pred.var,
                body=self._push_negation(pred.body),
                domain=pred.domain,
            )
        # Atomic predicate — just negate it
        return pred.negate()

    def to_cnf(self, pred: Predicate) -> And:
        """Convert *pred* to conjunctive normal form (AND of ORs).

        Warning: CNF conversion can cause exponential blowup.
        """
        nnf = self.to_nnf(pred)
        cnf = self._distribute_cnf(nnf)
        simplified = self.simplify(cnf)
        if isinstance(simplified, And):
            return simplified
        return And([simplified])

    def to_dnf(self, pred: Predicate) -> Or:
        """Convert *pred* to disjunctive normal form (OR of ANDs).

        Warning: DNF conversion can cause exponential blowup.
        """
        nnf = self.to_nnf(pred)
        dnf = self._distribute_dnf(nnf)
        simplified = self.simplify(dnf)
        if isinstance(simplified, Or):
            return simplified
        return Or([simplified])

    def _distribute_cnf(self, pred: Predicate) -> Predicate:
        """Distribute Or over And to produce CNF."""
        if isinstance(pred, And):
            return And([self._distribute_cnf(c) for c in pred.conjuncts])
        if isinstance(pred, Or):
            children = [self._distribute_cnf(d) for d in pred.disjuncts]
            # Flatten And children into clause lists
            clause_groups: List[List[Predicate]] = [[]]
            for child in children:
                if isinstance(child, And):
                    new_groups: List[List[Predicate]] = []
                    for clause in child.conjuncts:
                        for existing in clause_groups:
                            new_groups.append(existing + [clause])
                    clause_groups = new_groups
                else:
                    for group in clause_groups:
                        group.append(child)
            return And([Or(g) for g in clause_groups])
        return pred

    def _distribute_dnf(self, pred: Predicate) -> Predicate:
        """Distribute And over Or to produce DNF."""
        if isinstance(pred, Or):
            return Or([self._distribute_dnf(d) for d in pred.disjuncts])
        if isinstance(pred, And):
            children = [self._distribute_dnf(c) for c in pred.conjuncts]
            term_groups: List[List[Predicate]] = [[]]
            for child in children:
                if isinstance(child, Or):
                    new_groups: List[List[Predicate]] = []
                    for disj in child.disjuncts:
                        for existing in term_groups:
                            new_groups.append(existing + [disj])
                    term_groups = new_groups
                else:
                    for group in term_groups:
                        group.append(child)
            return Or([And(g) for g in term_groups])
        return pred
