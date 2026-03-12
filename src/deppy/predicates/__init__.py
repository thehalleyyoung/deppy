"""DepPy predicates — logical vocabulary for refinement types.

This package provides the predicate AST used throughout DepPy for
refinement types ``{v: τ | φ}``, guards, assertions, contracts,
and verification conditions.

Sub-modules
-----------
- **base**: Abstract ``Predicate`` / ``Term`` classes and concrete terms.
- **arithmetic**: ``Comparison``, ``LinearInequality``, ``IntRange``, etc.
- **boolean**: ``And``, ``Or``, ``Not``, ``Implies``, quantifiers.
- **collection**: ``LengthPred``, ``Contains``, ``Sorted``, ``Subset``, …
- **tensor**: ``ShapePred``, ``RankPred``, ``DtypePred``, ``BroadcastCompatible``, …
- **heap**: ``HasField``, ``FieldValue``, ``ProtocolConformance``, …
- **nullability**: ``IsNone``, ``IsNotNone``, ``IsInstance``, ``Truthy``, …
- **kinds**: ``PredicateKind``, ``DecidabilityFragment``, ``FragmentClassifier``.
- **normalization**: ``PredicateNormalizer``.
- **builder**: ``PredicateBuilder``, ``TermBuilder``.
"""

from __future__ import annotations

# -- base ------------------------------------------------------------------
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
    SourceLocation,
    StrLit,
    Term,
    TupleLit,
    UnaryOp,
    Var,
)

# -- arithmetic ------------------------------------------------------------
from deppy.predicates.arithmetic import (
    ArithmeticNormalizer,
    Comparison,
    Divisibility,
    IntRange,
    LinearInequality,
)

# -- boolean ---------------------------------------------------------------
from deppy.predicates.boolean import (
    And,
    BooleanSimplifier,
    Exists,
    ForAll,
    Iff,
    Implies,
    Not,
    Or,
    is_false,
    is_true,
)

# -- collection ------------------------------------------------------------
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

# -- tensor ----------------------------------------------------------------
from deppy.predicates.tensor import (
    BroadcastCompatible,
    ContiguousPred,
    DevicePred,
    DtypePred,
    RankPred,
    ShapePred,
    ShapeRelation,
    SortedTensor,
    ValidIndex,
)

# -- heap ------------------------------------------------------------------
from deppy.predicates.heap import (
    AliasRelation,
    FieldValue,
    HasField,
    Initialized,
    NotMutated,
    OwnershipPred,
    ProtocolConformance,
)

# -- nullability -----------------------------------------------------------
from deppy.predicates.nullability import (
    Falsy,
    IsInstance,
    IsNone,
    IsNotInstance,
    IsNotNone,
    Truthy,
    TypeNarrowing,
)

# -- kinds -----------------------------------------------------------------
from deppy.predicates.kinds import (
    DecidabilityFragment,
    FragmentClassifier,
    PredicateKind,
    predicate_kind,
)

# -- normalization ---------------------------------------------------------
from deppy.predicates.normalization import PredicateNormalizer

# -- builder ---------------------------------------------------------------
from deppy.predicates.builder import PredicateBuilder, TermBuilder

__all__ = [
    # base
    "Predicate",
    "Term",
    "SourceLocation",
    "Var",
    "IntLit",
    "FloatLit",
    "BoolLit",
    "StrLit",
    "NoneLit",
    "BinOp",
    "UnaryOp",
    "Call",
    "Attr",
    "Index",
    "TupleLit",
    "IfExpr",
    # arithmetic
    "Comparison",
    "LinearInequality",
    "Divisibility",
    "IntRange",
    "ArithmeticNormalizer",
    # boolean
    "And",
    "Or",
    "Not",
    "Implies",
    "Iff",
    "ForAll",
    "Exists",
    "BooleanSimplifier",
    "is_true",
    "is_false",
    # collection
    "LengthPred",
    "NonEmpty",
    "Contains",
    "Sorted",
    "Unique",
    "Subset",
    "Disjoint",
    "Permutation",
    # tensor
    "ShapePred",
    "RankPred",
    "DtypePred",
    "DevicePred",
    "BroadcastCompatible",
    "ShapeRelation",
    "SortedTensor",
    "ValidIndex",
    "ContiguousPred",
    # heap
    "HasField",
    "FieldValue",
    "ProtocolConformance",
    "Initialized",
    "NotMutated",
    "OwnershipPred",
    "AliasRelation",
    # nullability
    "IsNone",
    "IsNotNone",
    "IsInstance",
    "IsNotInstance",
    "Truthy",
    "Falsy",
    "TypeNarrowing",
    # kinds
    "PredicateKind",
    "DecidabilityFragment",
    "FragmentClassifier",
    "predicate_kind",
    # normalization
    "PredicateNormalizer",
    # builder
    "PredicateBuilder",
    "TermBuilder",
]
