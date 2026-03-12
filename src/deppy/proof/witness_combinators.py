"""Witness combinators: compose witness / proof terms.

Provides structured proof term constructors that extend the ProofTerm
hierarchy from types/witnesses.py. Each combinator class is a frozen
dataclass extending ProofTerm, supporting composition of proofs by
transitivity, symmetry, congruence, existential packing/unpacking,
universal instantiation, and pairing/projection.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Tuple,
    Union,
)

from deppy.types.base import TypeBase, AnyType, ANY_TYPE, NeverType, NEVER_TYPE
from deppy.types.witnesses import (
    ProofTerm,
    ReflProof,
    AssumptionProof,
    CompositeProof,
    TransitivityProof,
    SymmetryProof,
    CongruenceProof,
    WitnessCarrier,
    TransportWitness,
    ExistentialWitness,
)


# ---------------------------------------------------------------------------
# Transitivity witness
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TransitivityWitness(ProofTerm):
    """Proof by transitivity: from a = b and b = c, derive a = c.

    Extends ProofTerm to represent a chain of equalities. The chain
    can be of length 2 (standard transitivity) or longer (multi-step).

    Attributes:
        _left: Proof of a = b (or a chain endpoint).
        _right: Proof of b = c (or a chain endpoint).
        _chain: Full chain of intermediate proof steps.
        _left_term: The term on the left side of the equality.
        _middle_term: The intermediate term.
        _right_term: The term on the right side.
    """

    _left: ProofTerm = field(default_factory=lambda: ReflProof())
    _right: ProofTerm = field(default_factory=lambda: ReflProof())
    _chain: Tuple[ProofTerm, ...] = ()
    _left_term: Any = None
    _middle_term: Any = None
    _right_term: Any = None

    @property
    def left(self) -> ProofTerm:
        return self._left

    @property
    def right(self) -> ProofTerm:
        return self._right

    @property
    def chain(self) -> Tuple[ProofTerm, ...]:
        if self._chain:
            return self._chain
        return (self._left, self._right)

    def description(self) -> str:
        parts = " ; ".join(p.description() for p in self.chain)
        return f"trans({parts})"

    def to_transitivity_proof(self) -> TransitivityProof:
        """Convert to the base TransitivityProof from witnesses module."""
        return TransitivityProof(left=self._left, right=self._right)

    def extend(self, next_proof: ProofTerm) -> "TransitivityWitness":
        """Extend the transitivity chain with another step."""
        new_chain = self.chain + (next_proof,)
        return TransitivityWitness(
            _left=self._left,
            _right=next_proof,
            _chain=new_chain,
            _left_term=self._left_term,
            _right_term=None,
        )


# ---------------------------------------------------------------------------
# Symmetry witness
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SymmetryWitness(ProofTerm):
    """Proof by symmetry: from a = b, derive b = a.

    Attributes:
        _inner: The proof of a = b to be reversed.
        _left_term: The left-side term.
        _right_term: The right-side term.
    """

    _inner: ProofTerm = field(default_factory=lambda: ReflProof())
    _left_term: Any = None
    _right_term: Any = None

    @property
    def inner(self) -> ProofTerm:
        return self._inner

    def description(self) -> str:
        return f"sym({self._inner.description()})"

    def to_symmetry_proof(self) -> SymmetryProof:
        """Convert to the base SymmetryProof from witnesses module."""
        return SymmetryProof(inner=self._inner)

    def double_negate(self) -> ProofTerm:
        """sym(sym(p)) = p: double negation elimination."""
        if isinstance(self._inner, SymmetryWitness):
            return self._inner._inner
        if isinstance(self._inner, SymmetryProof):
            return self._inner.inner
        return self


# ---------------------------------------------------------------------------
# Congruence witness
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CongruenceWitness(ProofTerm):
    """Proof by congruence: from a = b, derive f(a) = f(b).

    Attributes:
        _inner: The proof of a = b.
        _function_name: Name of the function f.
        _function_arity: Number of arguments to f.
        _argument_index: Which argument position the equality applies to.
    """

    _inner: ProofTerm = field(default_factory=lambda: ReflProof())
    _function_name: str = ""
    _function_arity: int = 1
    _argument_index: int = 0

    @property
    def inner(self) -> ProofTerm:
        return self._inner

    @property
    def function_name(self) -> str:
        return self._function_name

    def description(self) -> str:
        return f"cong({self._function_name}, {self._inner.description()})"

    def to_congruence_proof(self) -> CongruenceProof:
        """Convert to the base CongruenceProof from witnesses module."""
        return CongruenceProof(
            inner=self._inner, function_name=self._function_name
        )

    def compose_congruence(
        self, outer_func: str
    ) -> "CongruenceWitness":
        """Compose congruences: cong(g, cong(f, p)) = cong(g.f, p)."""
        composed_name = f"{outer_func}({self._function_name})"
        return CongruenceWitness(
            _inner=self._inner,
            _function_name=composed_name,
            _function_arity=1,
            _argument_index=0,
        )


# ---------------------------------------------------------------------------
# Existential witness
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ExistentialPackWitness(ProofTerm):
    """Witness for packing an existential: from t:A and P(t), derive exists x:A. P(x).

    Attributes:
        _witness_term: The concrete term witnessing the existential.
        _witness_type: The type of the witness term.
        _property_proof: Proof that the property holds for the witness.
        _binder_name: The name of the existential variable.
        _property_description: Description of the property P.
    """

    _witness_term: Any = None
    _witness_type: Optional[TypeBase] = None
    _property_proof: ProofTerm = field(default_factory=lambda: ReflProof())
    _binder_name: str = "x"
    _property_description: str = ""

    @property
    def witness_term(self) -> Any:
        return self._witness_term

    @property
    def witness_type(self) -> Optional[TypeBase]:
        return self._witness_type

    @property
    def property_proof(self) -> ProofTerm:
        return self._property_proof

    def description(self) -> str:
        return (
            f"pack({self._binder_name}, {self._witness_term!r}, "
            f"{self._property_proof.description()})"
        )

    def to_existential_witness(self) -> ExistentialWitness:
        """Convert to the ExistentialWitness from witnesses module."""
        return ExistentialWitness(
            witness_term=self._witness_term,
            witness_type=self._witness_type or ANY_TYPE,
            property_satisfied=self._property_description,
        )


# ---------------------------------------------------------------------------
# Universal witness
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class UniversalWitness(ProofTerm):
    """Witness for a universal statement: forall x:A. P(x).

    Represents a proof that works for all values of the bound variable.

    Attributes:
        _binder_name: The universally quantified variable.
        _binder_type: The type of the bound variable.
        _body_proof: A proof of P(x) parametric in x.
        _property_description: Description of the property P.
    """

    _binder_name: str = "x"
    _binder_type: Optional[TypeBase] = None
    _body_proof: ProofTerm = field(default_factory=lambda: ReflProof())
    _property_description: str = ""

    @property
    def binder_name(self) -> str:
        return self._binder_name

    @property
    def binder_type(self) -> Optional[TypeBase]:
        return self._binder_type

    @property
    def body_proof(self) -> ProofTerm:
        return self._body_proof

    def description(self) -> str:
        type_str = repr(self._binder_type) if self._binder_type else "?"
        return (
            f"forall({self._binder_name}: {type_str}, "
            f"{self._body_proof.description()})"
        )

    def instantiate(self, term: Any) -> ProofTerm:
        """Instantiate the universal with a specific term.

        Returns the body proof, conceptually with the bound variable
        replaced by the given term.
        """
        # The actual substitution is symbolic; we wrap it
        return _InstantiatedUniversal(
            _universal=self,
            _instantiation_term=term,
        )


@dataclass(frozen=True)
class _InstantiatedUniversal(ProofTerm):
    """Result of instantiating a UniversalWitness at a specific term."""

    _universal: UniversalWitness = field(
        default_factory=lambda: UniversalWitness()
    )
    _instantiation_term: Any = None

    def description(self) -> str:
        return (
            f"{self._universal.description()}"
            f"[{self._universal.binder_name} := {self._instantiation_term!r}]"
        )


# ---------------------------------------------------------------------------
# Pair witness
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class PairWitness(ProofTerm):
    """Witness for a conjunction (pair): from P and Q, derive P /\\ Q.

    Attributes:
        _first: Proof of the first component P.
        _second: Proof of the second component Q.
        _first_prop: Description of the first proposition.
        _second_prop: Description of the second proposition.
    """

    _first: ProofTerm = field(default_factory=lambda: ReflProof())
    _second: ProofTerm = field(default_factory=lambda: ReflProof())
    _first_prop: str = ""
    _second_prop: str = ""

    @property
    def first(self) -> ProofTerm:
        return self._first

    @property
    def second(self) -> ProofTerm:
        return self._second

    def description(self) -> str:
        return (
            f"pair({self._first.description()}, "
            f"{self._second.description()})"
        )

    def to_composite_proof(self) -> CompositeProof:
        """Convert to a CompositeProof from witnesses module."""
        return CompositeProof(
            sub_proofs=(self._first, self._second),
            combiner="conjunction",
        )

    def fst(self) -> ProofTerm:
        """Project the first component."""
        return self._first

    def snd(self) -> ProofTerm:
        """Project the second component."""
        return self._second


# ---------------------------------------------------------------------------
# Projection witness
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ProjectionWitness(ProofTerm):
    """Witness for projecting a component from a conjunction.

    Attributes:
        _pair: The pair/conjunction proof to project from.
        _index: Which component to project (0 = first, 1 = second).
        _pair_description: Description of the pair being projected.
    """

    _pair: ProofTerm = field(default_factory=lambda: ReflProof())
    _index: int = 0
    _pair_description: str = ""

    @property
    def pair(self) -> ProofTerm:
        return self._pair

    @property
    def index(self) -> int:
        return self._index

    def description(self) -> str:
        proj_name = "fst" if self._index == 0 else "snd"
        return f"{proj_name}({self._pair.description()})"

    def resolve(self) -> ProofTerm:
        """Resolve the projection if the pair is known.

        If the underlying proof is a PairWitness or CompositeProof,
        extract the appropriate component directly.
        """
        if isinstance(self._pair, PairWitness):
            if self._index == 0:
                return self._pair.first
            return self._pair.second
        if isinstance(self._pair, CompositeProof):
            if self._index < len(self._pair.sub_proofs):
                return self._pair.sub_proofs[self._index]
        return self


# ---------------------------------------------------------------------------
# Modus ponens witness
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ModusPonensWitness(ProofTerm):
    """Witness for modus ponens: from P => Q and P, derive Q.

    Attributes:
        _implication: Proof of P => Q.
        _antecedent: Proof of P.
        _consequent_description: Description of Q.
    """

    _implication: ProofTerm = field(default_factory=lambda: ReflProof())
    _antecedent: ProofTerm = field(default_factory=lambda: ReflProof())
    _consequent_description: str = ""

    @property
    def implication(self) -> ProofTerm:
        return self._implication

    @property
    def antecedent(self) -> ProofTerm:
        return self._antecedent

    def description(self) -> str:
        return (
            f"mp({self._implication.description()}, "
            f"{self._antecedent.description()})"
        )


# ---------------------------------------------------------------------------
# Disjunction witnesses
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class LeftInjectionWitness(ProofTerm):
    """Witness for left injection: from P, derive P \\/ Q.

    Attributes:
        _inner: Proof of P.
        _right_prop: Description of Q (the other disjunct).
    """

    _inner: ProofTerm = field(default_factory=lambda: ReflProof())
    _right_prop: str = ""

    @property
    def inner(self) -> ProofTerm:
        return self._inner

    def description(self) -> str:
        return f"inl({self._inner.description()})"


@dataclass(frozen=True)
class RightInjectionWitness(ProofTerm):
    """Witness for right injection: from Q, derive P \\/ Q.

    Attributes:
        _inner: Proof of Q.
        _left_prop: Description of P (the other disjunct).
    """

    _inner: ProofTerm = field(default_factory=lambda: ReflProof())
    _left_prop: str = ""

    @property
    def inner(self) -> ProofTerm:
        return self._inner

    def description(self) -> str:
        return f"inr({self._inner.description()})"


@dataclass(frozen=True)
class CaseAnalysisWitness(ProofTerm):
    """Witness for case analysis on a disjunction.

    From P \\/ Q, P => R, Q => R, derive R.

    Attributes:
        _disjunction: Proof of P \\/ Q.
        _left_case: Proof of P => R.
        _right_case: Proof of Q => R.
        _result_description: Description of R.
    """

    _disjunction: ProofTerm = field(default_factory=lambda: ReflProof())
    _left_case: ProofTerm = field(default_factory=lambda: ReflProof())
    _right_case: ProofTerm = field(default_factory=lambda: ReflProof())
    _result_description: str = ""

    def description(self) -> str:
        return (
            f"cases({self._disjunction.description()}, "
            f"{self._left_case.description()}, "
            f"{self._right_case.description()})"
        )


# ---------------------------------------------------------------------------
# Absurdity witness
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class AbsurdityWitness(ProofTerm):
    """Witness for ex falso quodlibet: from False, derive anything.

    Attributes:
        _false_proof: Proof of False.
        _target_description: Description of what is being derived.
    """

    _false_proof: ProofTerm = field(default_factory=lambda: ReflProof())
    _target_description: str = ""

    def description(self) -> str:
        return f"absurd({self._false_proof.description()})"


# ---------------------------------------------------------------------------
# Transport witness combinator
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TransportProofWitness(ProofTerm):
    """Witness for type transport along an equality path.

    From a proof of A = B and a value of type A, derive a value of type B.

    Attributes:
        _equality_proof: Proof of A = B.
        _source_type: The source type A.
        _target_type: The target type B.
        _value_proof: Proof that the value has type A.
    """

    _equality_proof: ProofTerm = field(default_factory=lambda: ReflProof())
    _source_type: Optional[TypeBase] = None
    _target_type: Optional[TypeBase] = None
    _value_proof: Optional[ProofTerm] = None

    def description(self) -> str:
        src = repr(self._source_type) if self._source_type else "?"
        tgt = repr(self._target_type) if self._target_type else "?"
        return f"transport({src} -> {tgt}, {self._equality_proof.description()})"

    def to_transport_witness(self) -> Optional[TransportWitness]:
        """Convert to a TransportWitness from witnesses module."""
        if self._source_type is not None and self._target_type is not None:
            return TransportWitness(
                source_type=self._source_type,
                target_type=self._target_type,
                path=self._equality_proof,
            )
        return None


# ---------------------------------------------------------------------------
# Composition functions
# ---------------------------------------------------------------------------


def compose_transitivity(w1: ProofTerm, w2: ProofTerm) -> ProofTerm:
    """Compose two proofs by transitivity.

    Given w1: a = b and w2: b = c, produces a proof of a = c.
    Handles simplification when either proof is reflexivity.
    """
    # Simplify: refl . p = p
    if isinstance(w1, ReflProof):
        return w2
    # Simplify: p . refl = p
    if isinstance(w2, ReflProof):
        return w1
    # Flatten nested transitivity chains
    chain: List[ProofTerm] = []
    if isinstance(w1, TransitivityWitness):
        chain.extend(w1.chain)
    elif isinstance(w1, TransitivityProof):
        chain.extend([w1.left, w1.right])
    else:
        chain.append(w1)
    if isinstance(w2, TransitivityWitness):
        chain.extend(w2.chain)
    elif isinstance(w2, TransitivityProof):
        chain.extend([w2.left, w2.right])
    else:
        chain.append(w2)
    # Remove intermediate refl proofs
    filtered = [p for p in chain if not isinstance(p, ReflProof)]
    if not filtered:
        return ReflProof()
    if len(filtered) == 1:
        return filtered[0]
    return TransitivityWitness(
        _left=filtered[0],
        _right=filtered[-1],
        _chain=tuple(filtered),
    )


def compose_symmetry(w: ProofTerm) -> ProofTerm:
    """Apply symmetry to a proof.

    Given w: a = b, produces a proof of b = a.
    Simplifies sym(sym(p)) = p and sym(refl) = refl.
    """
    if isinstance(w, ReflProof):
        return w
    if isinstance(w, SymmetryWitness):
        return w._inner
    if isinstance(w, SymmetryProof):
        return w.inner
    return SymmetryWitness(_inner=w)


def lift_congruence(eq_proof: ProofTerm, func: str) -> ProofTerm:
    """Lift an equality proof through a function by congruence.

    Given eq_proof: a = b, produces a proof of f(a) = f(b).
    Simplifies cong(f, refl) = refl.
    """
    if isinstance(eq_proof, ReflProof):
        return ReflProof()
    return CongruenceWitness(
        _inner=eq_proof,
        _function_name=func,
    )


def lift_congruence_multi(
    eq_proofs: List[ProofTerm], func: str
) -> ProofTerm:
    """Lift multiple equality proofs through a multi-argument function.

    Given proofs a_i = b_i, produces a proof of f(a_1,...,a_n) = f(b_1,...,b_n).
    """
    if all(isinstance(p, ReflProof) for p in eq_proofs):
        return ReflProof()
    if len(eq_proofs) == 1:
        return lift_congruence(eq_proofs[0], func)
    # Compose congruences for each argument position
    combined = eq_proofs[0]
    for i, proof in enumerate(eq_proofs[1:], start=1):
        if not isinstance(proof, ReflProof):
            cong = CongruenceWitness(
                _inner=proof,
                _function_name=f"{func}[arg{i}]",
                _argument_index=i,
            )
            combined = compose_transitivity(combined, cong)
    return CongruenceWitness(
        _inner=combined,
        _function_name=func,
    )


def pack_witness(components: List[ProofTerm]) -> ProofTerm:
    """Pack multiple proof components into a single proof term.

    For 0 components: returns refl (trivial proof).
    For 1 component: returns it as-is.
    For 2 components: creates a PairWitness.
    For 3+ components: creates nested pairs (right-associated).
    """
    if not components:
        return ReflProof()
    if len(components) == 1:
        return components[0]
    if len(components) == 2:
        return PairWitness(_first=components[0], _second=components[1])
    # Right-associated nesting: (a, (b, (c, d)))
    result = components[-1]
    for component in reversed(components[:-1]):
        result = PairWitness(_first=component, _second=result)
    return result


def unpack_witness(proof: ProofTerm, count: int) -> List[ProofTerm]:
    """Unpack a packed witness into its components.

    Reverses the operation of pack_witness.
    """
    if count <= 0:
        return []
    if count == 1:
        return [proof]
    result: List[ProofTerm] = []
    current = proof
    for _ in range(count - 1):
        if isinstance(current, PairWitness):
            result.append(current.first)
            current = current.second
        elif isinstance(current, CompositeProof) and len(current.sub_proofs) >= 2:
            result.append(current.sub_proofs[0])
            remaining = current.sub_proofs[1:]
            if len(remaining) == 1:
                current = remaining[0]
            else:
                current = CompositeProof(
                    sub_proofs=remaining, combiner=current.combiner
                )
        else:
            result.append(current)
            for _ in range(count - len(result)):
                result.append(ReflProof())
            return result
    result.append(current)
    return result


def make_modus_ponens(
    implication: ProofTerm, antecedent: ProofTerm
) -> ProofTerm:
    """Build a modus ponens proof: from P => Q and P, derive Q."""
    return ModusPonensWitness(
        _implication=implication,
        _antecedent=antecedent,
    )


def make_universal(
    binder: str, binder_type: Optional[TypeBase], body: ProofTerm
) -> ProofTerm:
    """Build a universal proof: forall x:A. P(x)."""
    return UniversalWitness(
        _binder_name=binder,
        _binder_type=binder_type,
        _body_proof=body,
    )


def make_existential(
    binder: str,
    witness_term: Any,
    witness_type: Optional[TypeBase],
    property_proof: ProofTerm,
) -> ProofTerm:
    """Build an existential proof by packing a witness."""
    return ExistentialPackWitness(
        _witness_term=witness_term,
        _witness_type=witness_type,
        _property_proof=property_proof,
        _binder_name=binder,
    )


def make_case_analysis(
    disjunction: ProofTerm,
    left_case: ProofTerm,
    right_case: ProofTerm,
) -> ProofTerm:
    """Build a case analysis proof from a disjunction and two branches."""
    return CaseAnalysisWitness(
        _disjunction=disjunction,
        _left_case=left_case,
        _right_case=right_case,
    )


def make_absurdity(false_proof: ProofTerm) -> ProofTerm:
    """Build an absurdity elimination (ex falso quodlibet)."""
    return AbsurdityWitness(_false_proof=false_proof)


def make_transport(
    eq_proof: ProofTerm,
    source_type: Optional[TypeBase] = None,
    target_type: Optional[TypeBase] = None,
) -> ProofTerm:
    """Build a transport proof along an equality path."""
    return TransportProofWitness(
        _equality_proof=eq_proof,
        _source_type=source_type,
        _target_type=target_type,
    )


def make_left_injection(proof: ProofTerm) -> ProofTerm:
    """Build a left injection into a disjunction."""
    return LeftInjectionWitness(_inner=proof)


def make_right_injection(proof: ProofTerm) -> ProofTerm:
    """Build a right injection into a disjunction."""
    return RightInjectionWitness(_inner=proof)


# ---------------------------------------------------------------------------
# Proof simplification
# ---------------------------------------------------------------------------


def simplify_proof(proof: ProofTerm) -> ProofTerm:
    """Simplify a proof term by removing redundant steps.

    Applies the following reductions:
    - sym(sym(p)) = p
    - trans(refl, p) = p
    - trans(p, refl) = p
    - cong(f, refl) = refl
    - fst(pair(a, b)) = a
    - snd(pair(a, b)) = b
    """
    if isinstance(proof, SymmetryWitness):
        inner = simplify_proof(proof._inner)
        if isinstance(inner, SymmetryWitness):
            return simplify_proof(inner._inner)
        if isinstance(inner, SymmetryProof):
            return simplify_proof(inner.inner)
        if isinstance(inner, ReflProof):
            return inner
        return SymmetryWitness(_inner=inner)

    if isinstance(proof, TransitivityWitness):
        left = simplify_proof(proof._left)
        right = simplify_proof(proof._right)
        if isinstance(left, ReflProof):
            return right
        if isinstance(right, ReflProof):
            return left
        return TransitivityWitness(_left=left, _right=right)

    if isinstance(proof, CongruenceWitness):
        inner = simplify_proof(proof._inner)
        if isinstance(inner, ReflProof):
            return ReflProof()
        return CongruenceWitness(
            _inner=inner,
            _function_name=proof._function_name,
            _function_arity=proof._function_arity,
            _argument_index=proof._argument_index,
        )

    if isinstance(proof, ProjectionWitness):
        pair = simplify_proof(proof._pair)
        if isinstance(pair, PairWitness):
            if proof._index == 0:
                return simplify_proof(pair._first)
            return simplify_proof(pair._second)
        return ProjectionWitness(_pair=pair, _index=proof._index)

    if isinstance(proof, PairWitness):
        first = simplify_proof(proof._first)
        second = simplify_proof(proof._second)
        return PairWitness(_first=first, _second=second)

    if isinstance(proof, TransitivityProof):
        left = simplify_proof(proof.left)
        right = simplify_proof(proof.right)
        if isinstance(left, ReflProof):
            return right
        if isinstance(right, ReflProof):
            return left
        return TransitivityProof(left=left, right=right)

    if isinstance(proof, SymmetryProof):
        inner = simplify_proof(proof.inner)
        if isinstance(inner, SymmetryProof):
            return simplify_proof(inner.inner)
        if isinstance(inner, ReflProof):
            return inner
        return SymmetryProof(inner=inner)

    if isinstance(proof, CongruenceProof):
        inner = simplify_proof(proof.inner)
        if isinstance(inner, ReflProof):
            return ReflProof()
        return CongruenceProof(
            inner=inner, function_name=proof.function_name
        )

    return proof


def proof_size(proof: ProofTerm) -> int:
    """Count the number of nodes in a proof term tree."""
    if isinstance(proof, ReflProof):
        return 1
    if isinstance(proof, (AssumptionProof,)):
        return 1
    if isinstance(proof, TransitivityWitness):
        return 1 + sum(proof_size(p) for p in proof.chain)
    if isinstance(proof, TransitivityProof):
        return 1 + proof_size(proof.left) + proof_size(proof.right)
    if isinstance(proof, (SymmetryWitness, SymmetryProof)):
        inner = getattr(proof, "_inner", None) or getattr(proof, "inner", None)
        if inner is not None:
            return 1 + proof_size(inner)
        return 1
    if isinstance(proof, (CongruenceWitness, CongruenceProof)):
        inner = getattr(proof, "_inner", None) or getattr(proof, "inner", None)
        if inner is not None:
            return 1 + proof_size(inner)
        return 1
    if isinstance(proof, PairWitness):
        return 1 + proof_size(proof._first) + proof_size(proof._second)
    if isinstance(proof, ProjectionWitness):
        return 1 + proof_size(proof._pair)
    if isinstance(proof, CompositeProof):
        return 1 + sum(proof_size(p) for p in proof.sub_proofs)
    if isinstance(proof, ModusPonensWitness):
        return 1 + proof_size(proof._implication) + proof_size(proof._antecedent)
    if isinstance(proof, ExistentialPackWitness):
        return 1 + proof_size(proof._property_proof)
    if isinstance(proof, UniversalWitness):
        return 1 + proof_size(proof._body_proof)
    if isinstance(proof, CaseAnalysisWitness):
        return (
            1
            + proof_size(proof._disjunction)
            + proof_size(proof._left_case)
            + proof_size(proof._right_case)
        )
    return 1
