"""Predicate classification and decidability-fragment analysis.

Provides:

- **PredicateKind**: A fine-grained tag describing *what sort* of logical
  condition a predicate represents (comparison, membership, tensor, …).
- **DecidabilityFragment**: Which SMT-LIB logic fragment a predicate falls
  into (QF_LIA, QF_LRA, propositional, …).
- **FragmentClassifier**: Walks a predicate tree and returns the tightest
  decidability fragment that contains it.
"""

from __future__ import annotations

import enum
from typing import FrozenSet, Set

from deppy.predicates.base import (
    Attr,
    BinOp,
    BoolLit,
    Call,
    FloatLit,
    IfExpr,
    Index,
    IntLit,
    NoneLit,
    Predicate,
    StrLit,
    Term,
    TupleLit,
    UnaryOp,
    Var,
)


# ===================================================================
#  Predicate kind
# ===================================================================

class PredicateKind(enum.Enum):
    """High-level semantic tag for a predicate."""

    COMPARISON = "comparison"
    EQUALITY = "equality"
    MEMBERSHIP = "membership"
    TYPE_CHECK = "type_check"
    NONE_CHECK = "none_check"
    TRUTHINESS = "truthiness"
    LENGTH = "length"
    ATTRIBUTE = "attribute"
    CALLABLE_CHECK = "callable"
    COMPOUND = "compound"
    QUANTIFIED = "quantified"
    ARITHMETIC = "arithmetic"
    TENSOR = "tensor"
    HEAP = "heap"
    CUSTOM = "custom"


# ===================================================================
#  Decidability fragment
# ===================================================================

class DecidabilityFragment(enum.Enum):
    """SMT-LIB decidability fragment label."""

    QF_LIA = "QF_LIA"
    QF_LRA = "QF_LRA"
    QF_NIA = "QF_NIA"
    QF_BV = "QF_BV"
    QF_UF = "QF_UF"
    QF_AX = "QF_AX"
    FINITE_DOMAIN = "finite"
    PROPOSITIONAL = "propositional"
    UNDECIDABLE = "undecidable"
    UNKNOWN = "unknown"


# Fragment ordering: fragments that are *sub-theories* of others.
_FRAGMENT_STRENGTH: dict[DecidabilityFragment, int] = {
    DecidabilityFragment.PROPOSITIONAL: 0,
    DecidabilityFragment.FINITE_DOMAIN: 1,
    DecidabilityFragment.QF_LIA: 2,
    DecidabilityFragment.QF_LRA: 3,
    DecidabilityFragment.QF_BV: 3,
    DecidabilityFragment.QF_UF: 3,
    DecidabilityFragment.QF_AX: 4,
    DecidabilityFragment.QF_NIA: 5,
    DecidabilityFragment.UNKNOWN: 6,
    DecidabilityFragment.UNDECIDABLE: 7,
}

_DECIDABLE_FRAGMENTS: frozenset[DecidabilityFragment] = frozenset({
    DecidabilityFragment.PROPOSITIONAL,
    DecidabilityFragment.FINITE_DOMAIN,
    DecidabilityFragment.QF_LIA,
    DecidabilityFragment.QF_LRA,
    DecidabilityFragment.QF_BV,
    DecidabilityFragment.QF_UF,
    DecidabilityFragment.QF_AX,
    DecidabilityFragment.QF_NIA,
})


def _join_fragment(
    a: DecidabilityFragment,
    b: DecidabilityFragment,
) -> DecidabilityFragment:
    """Return the *least upper bound* (weakest) of two fragments."""
    if a is b:
        return a
    sa = _FRAGMENT_STRENGTH.get(a, 6)
    sb = _FRAGMENT_STRENGTH.get(b, 6)
    return a if sa >= sb else b


# ===================================================================
#  Term-level fragment inference
# ===================================================================

def _term_fragment(term: Term) -> DecidabilityFragment:
    """Classify a single *term* into a decidability fragment."""
    if isinstance(term, (IntLit, BoolLit)):
        return DecidabilityFragment.QF_LIA
    if isinstance(term, FloatLit):
        return DecidabilityFragment.QF_LRA
    if isinstance(term, (StrLit, NoneLit)):
        return DecidabilityFragment.FINITE_DOMAIN
    if isinstance(term, Var):
        # A bare variable has no inherent theory; its use determines fragment.
        return DecidabilityFragment.PROPOSITIONAL
    if isinstance(term, UnaryOp):
        child = _term_fragment(term.operand)
        if term.op == "~":
            return _join_fragment(child, DecidabilityFragment.QF_BV)
        return child
    if isinstance(term, BinOp):
        base = _join_fragment(
            _term_fragment(term.left), _term_fragment(term.right)
        )
        if term.op in {"*", "**", "%"}:
            # Non-linear unless one side is a literal
            if isinstance(term.left, (IntLit, FloatLit)) or isinstance(
                term.right, (IntLit, FloatLit)
            ):
                return base
            return _join_fragment(base, DecidabilityFragment.QF_NIA)
        if term.op in {"&", "|", "^", "<<", ">>"}:
            return _join_fragment(base, DecidabilityFragment.QF_BV)
        return base  # +, -, //
    if isinstance(term, Call):
        child = DecidabilityFragment.PROPOSITIONAL
        for a in term.args:
            child = _join_fragment(child, _term_fragment(a))
        return _join_fragment(child, DecidabilityFragment.QF_UF)
    if isinstance(term, Attr):
        return _join_fragment(
            _term_fragment(term.obj), DecidabilityFragment.QF_UF
        )
    if isinstance(term, Index):
        return _join_fragment(
            _join_fragment(_term_fragment(term.obj), _term_fragment(term.idx)),
            DecidabilityFragment.QF_AX,
        )
    if isinstance(term, TupleLit):
        frag = DecidabilityFragment.PROPOSITIONAL
        for e in term.elements:
            frag = _join_fragment(frag, _term_fragment(e))
        return frag
    if isinstance(term, IfExpr):
        frag = _pred_fragment(term.cond)
        frag = _join_fragment(frag, _term_fragment(term.then_))
        frag = _join_fragment(frag, _term_fragment(term.else_))
        return frag
    return DecidabilityFragment.UNKNOWN


# ===================================================================
#  Predicate-level fragment inference
# ===================================================================

def _pred_fragment(pred: Predicate) -> DecidabilityFragment:
    """Classify a single predicate into a decidability fragment."""
    # Lazy imports to avoid circular dependency at module level.
    from deppy.predicates.arithmetic import (
        Comparison,
        Divisibility,
        IntRange,
        LinearInequality,
    )
    from deppy.predicates.boolean import (
        And,
        Exists,
        ForAll,
        Iff,
        Implies,
        Not,
        Or,
    )
    from deppy.predicates.collection import (
        Contains,
        Disjoint,
        LengthPred,
        NonEmpty,
        Permutation,
        Sorted,
        Subset,
        Unique,
    )
    from deppy.predicates.heap import (
        AliasRelation,
        FieldValue,
        HasField,
        Initialized,
        NotMutated,
        OwnershipPred,
        ProtocolConformance,
    )
    from deppy.predicates.nullability import (
        Falsy,
        IsInstance,
        IsNone,
        IsNotInstance,
        IsNotNone,
        Truthy,
    )
    from deppy.predicates.tensor import (
        BroadcastCompatible,
        ContiguousPred,
        DtypePred,
        DevicePred,
        RankPred,
        ShapePred,
        ShapeRelation,
        SortedTensor,
        ValidIndex,
    )

    # --- Arithmetic ---
    if isinstance(pred, Comparison):
        return _join_fragment(
            _term_fragment(pred.left), _term_fragment(pred.right)
        )
    if isinstance(pred, LinearInequality):
        return DecidabilityFragment.QF_LIA
    if isinstance(pred, Divisibility):
        return DecidabilityFragment.QF_LIA
    if isinstance(pred, IntRange):
        return DecidabilityFragment.QF_LIA

    # --- Boolean ---
    if isinstance(pred, (And, Or)):
        children = pred.conjuncts if isinstance(pred, And) else pred.disjuncts
        frag = DecidabilityFragment.PROPOSITIONAL
        for c in children:
            frag = _join_fragment(frag, _pred_fragment(c))
        return frag
    if isinstance(pred, Not):
        return _pred_fragment(pred.operand)
    if isinstance(pred, Implies):
        return _join_fragment(
            _pred_fragment(pred.antecedent),
            _pred_fragment(pred.consequent),
        )
    if isinstance(pred, Iff):
        return _join_fragment(
            _pred_fragment(pred.left), _pred_fragment(pred.right)
        )
    if isinstance(pred, (ForAll, Exists)):
        return _join_fragment(
            _pred_fragment(pred.body), DecidabilityFragment.UNDECIDABLE
        )

    # --- Nullability / type checks ---
    if isinstance(pred, (IsNone, IsNotNone)):
        return DecidabilityFragment.FINITE_DOMAIN
    if isinstance(pred, (IsInstance, IsNotInstance)):
        return DecidabilityFragment.FINITE_DOMAIN
    if isinstance(pred, (Truthy, Falsy)):
        return DecidabilityFragment.PROPOSITIONAL

    # --- Collections ---
    if isinstance(pred, (LengthPred, NonEmpty)):
        frag = DecidabilityFragment.QF_LIA
        if isinstance(pred, LengthPred):
            frag = _join_fragment(frag, _term_fragment(pred.bound))
        return _join_fragment(frag, _term_fragment(pred.collection))
    if isinstance(pred, Contains):
        return _join_fragment(
            _term_fragment(pred.element),
            _join_fragment(
                _term_fragment(pred.collection), DecidabilityFragment.QF_AX
            ),
        )
    if isinstance(pred, (Sorted, Unique, Subset, Disjoint, Permutation)):
        return DecidabilityFragment.UNDECIDABLE

    # --- Tensor ---
    if isinstance(pred, (ShapePred, RankPred)):
        return DecidabilityFragment.QF_LIA
    if isinstance(pred, (DtypePred, DevicePred, ContiguousPred)):
        return DecidabilityFragment.FINITE_DOMAIN
    if isinstance(pred, (BroadcastCompatible, ShapeRelation, ValidIndex)):
        return DecidabilityFragment.QF_LIA
    if isinstance(pred, SortedTensor):
        return DecidabilityFragment.UNDECIDABLE

    # --- Heap ---
    if isinstance(pred, (HasField, Initialized, NotMutated)):
        return DecidabilityFragment.QF_UF
    if isinstance(pred, FieldValue):
        return _join_fragment(
            _pred_fragment(pred.predicate), DecidabilityFragment.QF_UF
        )
    if isinstance(pred, ProtocolConformance):
        return DecidabilityFragment.QF_UF
    if isinstance(pred, (OwnershipPred, AliasRelation)):
        return DecidabilityFragment.UNDECIDABLE

    return DecidabilityFragment.UNKNOWN


# ===================================================================
#  Public classifier
# ===================================================================

class FragmentClassifier:
    """Classifies predicates into decidability fragments.

    The classifier walks a predicate tree bottom-up, assigning each
    leaf its tightest fragment, then joins fragments at each internal
    node to derive the overall theory.
    """

    def classify(self, pred: Predicate) -> DecidabilityFragment:
        """Return the single tightest decidability fragment for *pred*."""
        return _pred_fragment(pred)

    def classify_theory(self, pred: Predicate) -> Set[DecidabilityFragment]:
        """Return the *set* of atomic theories used inside *pred*."""
        theories: Set[DecidabilityFragment] = set()
        for sub in pred.walk():
            frag = _pred_fragment(sub)
            if frag not in {
                DecidabilityFragment.PROPOSITIONAL,
                DecidabilityFragment.UNKNOWN,
            }:
                theories.add(frag)
        if not theories:
            theories.add(DecidabilityFragment.PROPOSITIONAL)
        return theories

    def is_decidable(self, pred: Predicate) -> bool:
        """Return ``True`` when the predicate belongs to a decidable fragment."""
        return self.classify(pred) in _DECIDABLE_FRAGMENTS

    def is_linear(self, pred: Predicate) -> bool:
        """Return ``True`` when the predicate stays within linear arithmetic."""
        frag = self.classify(pred)
        return frag in {
            DecidabilityFragment.QF_LIA,
            DecidabilityFragment.QF_LRA,
            DecidabilityFragment.PROPOSITIONAL,
            DecidabilityFragment.FINITE_DOMAIN,
        }


# ===================================================================
#  Predicate kind tagger
# ===================================================================

def predicate_kind(pred: Predicate) -> PredicateKind:
    """Assign a *PredicateKind* tag to *pred*."""
    from deppy.predicates.arithmetic import (
        Comparison,
        Divisibility,
        IntRange,
        LinearInequality,
    )
    from deppy.predicates.boolean import (
        And,
        Exists,
        ForAll,
        Iff,
        Implies,
        Not,
        Or,
    )
    from deppy.predicates.collection import (
        Contains,
        Disjoint,
        LengthPred,
        NonEmpty,
        Permutation,
        Sorted,
        Subset,
        Unique,
    )
    from deppy.predicates.heap import (
        AliasRelation,
        FieldValue,
        HasField,
        Initialized,
        NotMutated,
        OwnershipPred,
        ProtocolConformance,
    )
    from deppy.predicates.nullability import (
        Falsy,
        IsInstance,
        IsNone,
        IsNotInstance,
        IsNotNone,
        Truthy,
    )
    from deppy.predicates.tensor import (
        BroadcastCompatible,
        ContiguousPred,
        DtypePred,
        DevicePred,
        RankPred,
        ShapePred,
        ShapeRelation,
        SortedTensor,
        ValidIndex,
    )

    if isinstance(pred, Comparison):
        if pred.op in {"==", "!="}:
            return PredicateKind.EQUALITY
        return PredicateKind.COMPARISON
    if isinstance(pred, (LinearInequality, Divisibility, IntRange)):
        return PredicateKind.ARITHMETIC
    if isinstance(pred, (And, Or, Not, Implies, Iff)):
        return PredicateKind.COMPOUND
    if isinstance(pred, (ForAll, Exists)):
        return PredicateKind.QUANTIFIED
    if isinstance(pred, (IsNone, IsNotNone)):
        return PredicateKind.NONE_CHECK
    if isinstance(pred, (IsInstance, IsNotInstance)):
        return PredicateKind.TYPE_CHECK
    if isinstance(pred, (Truthy, Falsy)):
        return PredicateKind.TRUTHINESS
    if isinstance(pred, (LengthPred, NonEmpty)):
        return PredicateKind.LENGTH
    if isinstance(pred, Contains):
        return PredicateKind.MEMBERSHIP
    if isinstance(pred, (Sorted, Unique, Subset, Disjoint, Permutation)):
        return PredicateKind.MEMBERSHIP
    if isinstance(
        pred,
        (
            ShapePred, RankPred, DtypePred, DevicePred,
            BroadcastCompatible, ShapeRelation, SortedTensor,
            ValidIndex, ContiguousPred,
        ),
    ):
        return PredicateKind.TENSOR
    if isinstance(
        pred,
        (
            HasField, FieldValue, ProtocolConformance,
            Initialized, NotMutated, OwnershipPred, AliasRelation,
        ),
    ):
        return PredicateKind.HEAP

    return PredicateKind.CUSTOM
