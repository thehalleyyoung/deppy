"""Core IR term language for the sheaf-theoretic frontend.

This module defines the frozen-dataclass IR nodes that the AST lowering
visitor produces.  Every node carries a ``SourceSpan`` so that later stages
(cover synthesis, local solving, rendering) can trace IR fragments back to
original Python source locations.

The IR is **not** a classical compiler IR.  It is a structured representation
of Python program fragments whose sole purpose is to feed the observation
site cover synthesis (Algorithm 1).  In particular:

- ``IRModule`` is the top-level container for a single Python file.
- ``IRFunction`` and ``IRClass`` are first-class entities that map directly
  to argument-boundary / return-boundary / module-summary sites.
- ``IRStatement`` variants correspond to control-flow and data-flow patterns
  that give rise to branch-guard, SSA-value, loop-invariant, call-result,
  error, and proof sites.
- ``IRExpr`` variants describe expressions whose evaluation produces local
  semantic information (carrier types, refinements, witnesses).

No mutation, no SSA renaming, no CFG construction happens here.  The IR is
a faithful, immutable mirror of the source AST enriched with span data.
"""

from __future__ import annotations

import enum
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.static_analysis.observation_sites import SourceSpan


# ═══════════════════════════════════════════════════════════════════════════════
# Source span sentinel
# ═══════════════════════════════════════════════════════════════════════════════

UNKNOWN_SPAN = SourceSpan(file="<unknown>", start_line=0, start_col=0)


# ═══════════════════════════════════════════════════════════════════════════════
# Operator enumerations
# ═══════════════════════════════════════════════════════════════════════════════


class BinOpKind(enum.Enum):
    """Binary operator kinds mirroring Python's AST operator set."""
    ADD = "+"
    SUB = "-"
    MULT = "*"
    DIV = "/"
    FLOOR_DIV = "//"
    MOD = "%"
    POW = "**"
    LSHIFT = "<<"
    RSHIFT = ">>"
    BIT_OR = "|"
    BIT_XOR = "^"
    BIT_AND = "&"
    MAT_MULT = "@"


class UnaryOpKind(enum.Enum):
    """Unary operator kinds."""
    INVERT = "~"
    NOT = "not"
    UADD = "+"
    USUB = "-"


class CmpOpKind(enum.Enum):
    """Comparison operator kinds."""
    EQ = "=="
    NOT_EQ = "!="
    LT = "<"
    LT_EQ = "<="
    GT = ">"
    GT_EQ = ">="
    IS = "is"
    IS_NOT = "is not"
    IN = "in"
    NOT_IN = "not in"


class BoolOpKind(enum.Enum):
    """Boolean operator kinds."""
    AND = "and"
    OR = "or"


# ═══════════════════════════════════════════════════════════════════════════════
# IR expression nodes
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class IRName:
    """A variable reference.

    In the sheaf view, each IRName contributes a potential SSA-value site
    at the point of use, and its lineage traces back to the defining
    assignment or parameter site.
    """
    name: str
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRConstant:
    """A literal constant value.

    Constants contribute carrier-type information directly: their type is
    known precisely (e.g., ``Literal[42]``), and they require no upstream
    site for resolution.
    """
    value: Any
    kind: str = ""  # e.g. "int", "str", "float", "bool", "None", "bytes", "ellipsis"
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRCall:
    """A function or method call expression.

    Each call becomes a call-result observation site.  The callee's boundary
    sections are imported via actual-to-formal reindexing morphisms.
    """
    func: IRExpr
    args: Tuple[IRExpr, ...] = ()
    keywords: Tuple[Tuple[Optional[str], IRExpr], ...] = ()
    starargs: Tuple[IRExpr, ...] = ()
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRBinOp:
    """A binary operation.

    Binary operations over numeric types may trigger error sites (e.g.,
    ZeroDivisionError for ``/``, ``//``, ``%``) and produce carrier-type
    information through the numeric widening lattice.
    """
    left: IRExpr
    op: BinOpKind
    right: IRExpr
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRUnaryOp:
    """A unary operation."""
    op: UnaryOpKind
    operand: IRExpr
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRBoolOp:
    """A boolean operation (and / or) with short-circuit semantics.

    In the sheaf view, short-circuit evaluation produces branch-guard-like
    refinements on the operands.
    """
    op: BoolOpKind
    values: Tuple[IRExpr, ...]
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRCompare:
    """A comparison chain ``a < b < c``.

    Comparison chains produce branch-guard refinements when used as
    if-test or assert-test conditions.
    """
    left: IRExpr
    ops: Tuple[CmpOpKind, ...]
    comparators: Tuple[IRExpr, ...]
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRSubscript:
    """A subscript expression ``value[slice]``.

    Subscript operations create error sites (IndexError / KeyError) and
    tensor-indexing sites when the value is a tensor.
    """
    value: IRExpr
    slice: IRExpr
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRAttribute:
    """An attribute access ``value.attr``.

    Attribute accesses create heap/protocol sites and may trigger
    AttributeError error sites.
    """
    value: IRExpr
    attr: str
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRTuple:
    """A tuple literal ``(a, b, c)``.

    Tuple construction is important for multi-return patterns and for
    pack/unpack operations that create lineage chains.
    """
    elts: Tuple[IRExpr, ...]
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRList:
    """A list literal ``[a, b, c]``."""
    elts: Tuple[IRExpr, ...]
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRDict:
    """A dict literal ``{k: v, ...}``."""
    keys: Tuple[Optional[IRExpr], ...]
    values: Tuple[IRExpr, ...]
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRSet:
    """A set literal ``{a, b, c}``."""
    elts: Tuple[IRExpr, ...]
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRLambda:
    """A lambda expression.

    Lambdas are small anonymous functions.  They produce argument-boundary
    and return-boundary sites just like full functions, but are inlined
    into the enclosing cover.
    """
    args: Tuple[IRParam, ...]
    body: IRExpr
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRIfExpr:
    """A conditional expression ``a if test else b``.

    The ternary operator produces branch-guard refinements on the test
    and contributes to phi-merge overlap sites at the join point.
    """
    test: IRExpr
    body: IRExpr
    orelse: IRExpr
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRComprehension:
    """A comprehension expression (list/set/dict/generator).

    Comprehensions introduce loop-invariant sites for the iteration
    variable and filter guards that act as branch-guard refinements.
    """
    element: IRExpr
    generators: Tuple[IRComprehensionGenerator, ...]
    is_list: bool = True
    is_set: bool = False
    is_dict: bool = False
    is_generator: bool = False
    value: Optional[IRExpr] = None  # for dict comprehensions: the value expression
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRComprehensionGenerator:
    """A single ``for ... in ... if ...`` clause in a comprehension."""
    target: IRExpr
    iter: IRExpr
    ifs: Tuple[IRExpr, ...] = ()
    is_async: bool = False
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRStarred:
    """A starred expression ``*expr`` in a call or assignment."""
    value: IRExpr
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRFString:
    """An f-string expression."""
    values: Tuple[IRExpr, ...]
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRYield:
    """A yield expression."""
    value: Optional[IRExpr] = None
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRYieldFrom:
    """A yield-from expression."""
    value: IRExpr = None  # type: ignore[assignment]
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRAwait:
    """An await expression."""
    value: IRExpr = None  # type: ignore[assignment]
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRSlice:
    """A slice expression ``lower:upper:step``."""
    lower: Optional[IRExpr] = None
    upper: Optional[IRExpr] = None
    step: Optional[IRExpr] = None
    span: SourceSpan = UNKNOWN_SPAN


# The IRExpr union type covering all expression variants
IRExpr = Union[
    IRName,
    IRConstant,
    IRCall,
    IRBinOp,
    IRUnaryOp,
    IRBoolOp,
    IRCompare,
    IRSubscript,
    IRAttribute,
    IRTuple,
    IRList,
    IRDict,
    IRSet,
    IRLambda,
    IRIfExpr,
    IRComprehension,
    IRComprehensionGenerator,
    IRStarred,
    IRFString,
    IRYield,
    IRYieldFrom,
    IRAwait,
    IRSlice,
]


# ═══════════════════════════════════════════════════════════════════════════════
# IR statement nodes
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class IRAssign:
    """An assignment statement ``targets = value``.

    Assignments create SSA-value sites for each target variable, with
    lineage morphisms from the value expression's contributing sites.
    """
    targets: Tuple[IRExpr, ...]
    value: IRExpr
    type_annotation: Optional[IRExpr] = None  # for annotated assignments
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRAugAssign:
    """An augmented assignment ``target op= value``."""
    target: IRExpr
    op: BinOpKind
    value: IRExpr
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRReturn:
    """A return statement.

    Returns create return/output-boundary sites.  The returned expression's
    carrier type flows to the output boundary via an output-projection
    morphism.
    """
    value: Optional[IRExpr] = None
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRIf:
    """An if/elif/else statement.

    If-statements create branch-guard sites.  The guard predicate narrows
    types in the true/false arms via control restriction morphisms.
    """
    test: IRExpr
    body: Tuple[IRStatement, ...]
    orelse: Tuple[IRStatement, ...] = ()
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRFor:
    """A for-loop statement.

    For-loops create loop-header/invariant sites.  The iteration variable
    receives a fresh SSA-value site at each conceptual iteration, and the
    loop body contributes to the invariant site's local section.
    """
    target: IRExpr
    iter: IRExpr
    body: Tuple[IRStatement, ...]
    orelse: Tuple[IRStatement, ...] = ()
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRWhile:
    """A while-loop statement.

    While-loops create loop-header/invariant sites with an associated
    guard predicate.  The decreases expression (if present via decorator)
    feeds the ranking function for termination.
    """
    test: IRExpr
    body: Tuple[IRStatement, ...]
    orelse: Tuple[IRStatement, ...] = ()
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRRaise:
    """A raise statement.

    Raise statements create exceptional output-boundary sites.  The
    exception type contributes to error-site classification.
    """
    exc: Optional[IRExpr] = None
    cause: Optional[IRExpr] = None
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRExceptHandler:
    """A single except clause in a try statement."""
    type: Optional[IRExpr] = None
    name: Optional[str] = None
    body: Tuple[IRStatement, ...] = ()
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRTry:
    """A try/except/else/finally statement.

    Try blocks create error sites for each except handler and
    contribute to exception flow analysis.
    """
    body: Tuple[IRStatement, ...]
    handlers: Tuple[IRExceptHandler, ...] = ()
    orelse: Tuple[IRStatement, ...] = ()
    finalbody: Tuple[IRStatement, ...] = ()
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRWith:
    """A with/async-with statement.

    Context managers create heap/protocol sites for ``__enter__`` and
    ``__exit__`` protocol methods.
    """
    items: Tuple[Tuple[IRExpr, Optional[IRExpr]], ...]  # (context_expr, optional_var)
    body: Tuple[IRStatement, ...]
    is_async: bool = False
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRAssert:
    """An assert statement.

    Assertions create branch-guard sites with ``is_assertion=True``.
    The guard predicate is assumed to hold after the assert, providing
    refinements to downstream sites.
    """
    test: IRExpr
    msg: Optional[IRExpr] = None
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRExprStmt:
    """A standalone expression statement.

    Expression statements that are function calls still create call-result
    sites even though their return value is discarded.
    """
    value: IRExpr
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRDelete:
    """A delete statement ``del target``."""
    targets: Tuple[IRExpr, ...]
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRImport:
    """An import statement."""
    names: Tuple[Tuple[str, Optional[str]], ...]  # (module, alias)
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRImportFrom:
    """A from-import statement."""
    module: Optional[str]
    names: Tuple[Tuple[str, Optional[str]], ...]  # (name, alias)
    level: int = 0  # relative import level
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRGlobal:
    """A global declaration."""
    names: Tuple[str, ...]
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRNonlocal:
    """A nonlocal declaration."""
    names: Tuple[str, ...]
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRPass:
    """A pass statement."""
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRBreak:
    """A break statement."""
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRContinue:
    """A continue statement."""
    span: SourceSpan = UNKNOWN_SPAN


# The IRStatement union type covering all statement variants
IRStatement = Union[
    IRAssign,
    IRAugAssign,
    IRReturn,
    IRIf,
    IRFor,
    IRWhile,
    IRRaise,
    IRTry,
    IRWith,
    IRAssert,
    IRExprStmt,
    IRDelete,
    IRImport,
    IRImportFrom,
    IRGlobal,
    IRNonlocal,
    IRPass,
    IRBreak,
    IRContinue,
]


# ═══════════════════════════════════════════════════════════════════════════════
# IR parameter, function, class, and module nodes
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class IRParam:
    """A function parameter.

    Each parameter becomes an argument-boundary observation site.
    The annotation (if present) seeds the carrier type at that site.
    """
    name: str
    index: int
    annotation: Optional[IRExpr] = None
    default: Optional[IRExpr] = None
    is_self: bool = False
    is_cls: bool = False
    is_vararg: bool = False
    is_kwarg: bool = False
    is_keyword_only: bool = False
    is_positional_only: bool = False
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRDecorator:
    """A decorator application.

    Decorators that match ``@deppy.*`` patterns are parsed separately
    by the DecoratorParser to produce ContractSeed / ProofSeed objects.
    Other decorators are preserved for downstream analysis.
    """
    expr: IRExpr
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRFunction:
    """An IR function definition.

    Each function maps to a cover fragment containing:
    - Argument-boundary sites (one per parameter)
    - Return/output-boundary sites (one per return point)
    - Interior sites (SSA values, branch guards, calls, errors, etc.)
    - Morphisms connecting these sites

    The function's boundary sections (input and output) define the
    interface for interprocedural analysis.
    """
    name: str
    params: Tuple[IRParam, ...]
    body: Tuple[IRStatement, ...]
    decorators: Tuple[IRDecorator, ...] = ()
    return_annotation: Optional[IRExpr] = None
    is_async: bool = False
    is_method: bool = False
    is_classmethod: bool = False
    is_staticmethod: bool = False
    is_property: bool = False
    docstring: Optional[str] = None
    enclosing_class: Optional[str] = None
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRClass:
    """An IR class definition.

    Classes map to:
    - A module-summary site for the class itself
    - Heap/protocol sites for field initialization in ``__init__``
    - Method-level cover fragments for each method

    The class's protocol (set of required methods and attributes)
    feeds structural subtyping checks.
    """
    name: str
    bases: Tuple[IRExpr, ...]
    keywords: Tuple[Tuple[str, IRExpr], ...] = ()
    body: Tuple[Union[IRFunction, IRStatement], ...] = ()
    decorators: Tuple[IRDecorator, ...] = ()
    docstring: Optional[str] = None
    span: SourceSpan = UNKNOWN_SPAN


@dataclass(frozen=True)
class IRModule:
    """The top-level IR container for a single Python source file.

    An IRModule contains:
    - All function definitions (including nested ones)
    - All class definitions
    - Top-level statements (imports, assignments, expressions)

    The module corresponds to a module-summary observation site and
    defines the public API boundary for interprocedural analysis.
    """
    name: str
    filename: str
    functions: Tuple[IRFunction, ...] = ()
    classes: Tuple[IRClass, ...] = ()
    statements: Tuple[IRStatement, ...] = ()
    docstring: Optional[str] = None
    imports: Tuple[Union[IRImport, IRImportFrom], ...] = ()
    span: SourceSpan = UNKNOWN_SPAN
