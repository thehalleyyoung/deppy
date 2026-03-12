"""Frontend IR subpackage: Core term language and pretty-printing.

The IR is the sheaf-theoretic frontend's intermediate representation.
It exists solely to feed Algorithm 1 (Cover Synthesis) -- it is NOT
a classical compiler IR with CFG or SSA infrastructure.

Core modules:
- ``core_term``: Frozen dataclasses for all IR nodes (IRModule, IRFunction,
  IRClass, IRStatement variants, IRExpr variants).
- ``pretty_printer``: Human-readable rendering of IR trees for debugging.
"""

from deppy.frontend.ir.core_term import (
    # Operator enums
    BinOpKind,
    BoolOpKind,
    CmpOpKind,
    UnaryOpKind,
    # Expression nodes
    IRAttribute,
    IRAwait,
    IRBinOp,
    IRBoolOp,
    IRCall,
    IRCompare,
    IRComprehension,
    IRComprehensionGenerator,
    IRConstant,
    IRDict,
    IRExpr,
    IRFString,
    IRIfExpr,
    IRLambda,
    IRList,
    IRName,
    IRSet,
    IRSlice,
    IRStarred,
    IRSubscript,
    IRTuple,
    IRUnaryOp,
    IRYield,
    IRYieldFrom,
    # Statement nodes
    IRAssert,
    IRAssign,
    IRAugAssign,
    IRBreak,
    IRContinue,
    IRDelete,
    IRExceptHandler,
    IRExprStmt,
    IRFor,
    IRGlobal,
    IRIf,
    IRImport,
    IRImportFrom,
    IRNonlocal,
    IRPass,
    IRRaise,
    IRReturn,
    IRStatement,
    IRTry,
    IRWhile,
    IRWith,
    # Top-level nodes
    IRClass,
    IRDecorator,
    IRFunction,
    IRModule,
    IRParam,
    # Utility
    UNKNOWN_SPAN,
)

from deppy.frontend.ir.pretty_printer import (
    PrettyPrinter,
    pretty_print,
    pretty_print_expr,
    pretty_print_stmt,
)

__all__ = [
    # Operator enums
    "BinOpKind",
    "BoolOpKind",
    "CmpOpKind",
    "UnaryOpKind",
    # Expression nodes
    "IRAttribute",
    "IRAwait",
    "IRBinOp",
    "IRBoolOp",
    "IRCall",
    "IRCompare",
    "IRComprehension",
    "IRComprehensionGenerator",
    "IRConstant",
    "IRDict",
    "IRExpr",
    "IRFString",
    "IRIfExpr",
    "IRLambda",
    "IRList",
    "IRName",
    "IRSet",
    "IRSlice",
    "IRStarred",
    "IRSubscript",
    "IRTuple",
    "IRUnaryOp",
    "IRYield",
    "IRYieldFrom",
    # Statement nodes
    "IRAssert",
    "IRAssign",
    "IRAugAssign",
    "IRBreak",
    "IRContinue",
    "IRDelete",
    "IRExceptHandler",
    "IRExprStmt",
    "IRFor",
    "IRGlobal",
    "IRIf",
    "IRImport",
    "IRImportFrom",
    "IRNonlocal",
    "IRPass",
    "IRRaise",
    "IRReturn",
    "IRStatement",
    "IRTry",
    "IRWhile",
    "IRWith",
    # Top-level nodes
    "IRClass",
    "IRDecorator",
    "IRFunction",
    "IRModule",
    "IRParam",
    # Pretty-printing
    "PrettyPrinter",
    "pretty_print",
    "pretty_print_expr",
    "pretty_print_stmt",
    # Utility
    "UNKNOWN_SPAN",
]
