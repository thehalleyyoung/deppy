"""Python AST to deppy IR lowering visitor.

This is the core of the sheaf-theoretic frontend.  The ``IRLowering`` visitor
walks a Python AST (produced by ``ast.parse``) and produces an ``IRModule``
containing function definitions, class definitions, and top-level statements.

The lowering is a faithful translation: no optimisation, no SSA renaming, no
type inference.  The only enrichment is the attachment of ``SourceSpan`` data
to every IR node so that later stages (cover synthesis, observation site
construction) can trace IR fragments back to their original source locations.

The IR is designed to feed into Algorithm 1 (Cover Synthesis).  Each IR
construct maps to one or more observation site patterns:

- ``IRFunction`` -> argument-boundary + return-boundary sites
- ``IRAssign``   -> SSA-value sites with lineage morphisms
- ``IRIf``       -> branch-guard sites with control restriction morphisms
- ``IRFor/While``-> loop-header/invariant sites
- ``IRCall``     -> call-result sites with actual-to-formal reindexing
- ``IRRaise``    -> exceptional output-boundary sites
- ``IRTry``      -> error/exception flow sites
- ``IRWith``     -> heap/protocol sites (__enter__/__exit__)
- ``IRAssert``   -> branch-guard sites with is_assertion=True
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.static_analysis.observation_sites import SourceSpan
from deppy.frontend.ir.core_term import (
    BinOpKind,
    BoolOpKind,
    CmpOpKind,
    IRAssert,
    IRAssign,
    IRAttribute,
    IRAugAssign,
    IRAwait,
    IRBinOp,
    IRBoolOp,
    IRBreak,
    IRCall,
    IRClass,
    IRCompare,
    IRComprehension,
    IRComprehensionGenerator,
    IRConstant,
    IRContinue,
    IRDecorator,
    IRDelete,
    IRDict,
    IRExceptHandler,
    IRExpr,
    IRExprStmt,
    IRFor,
    IRFString,
    IRFunction,
    IRGlobal,
    IRIf,
    IRIfExpr,
    IRImport,
    IRImportFrom,
    IRLambda,
    IRList,
    IRModule,
    IRName,
    IRNonlocal,
    IRParam,
    IRPass,
    IRRaise,
    IRReturn,
    IRSet,
    IRSlice,
    IRStarred,
    IRStatement,
    IRSubscript,
    IRTry,
    IRTuple,
    IRUnaryOp,
    IRWhile,
    IRWith,
    IRYield,
    IRYieldFrom,
    UnaryOpKind,
    UNKNOWN_SPAN,
)


# ═══════════════════════════════════════════════════════════════════════════════
# AST operator mappings
# ═══════════════════════════════════════════════════════════════════════════════

_BINOP_MAP: Dict[type, BinOpKind] = {
    ast.Add: BinOpKind.ADD,
    ast.Sub: BinOpKind.SUB,
    ast.Mult: BinOpKind.MULT,
    ast.Div: BinOpKind.DIV,
    ast.FloorDiv: BinOpKind.FLOOR_DIV,
    ast.Mod: BinOpKind.MOD,
    ast.Pow: BinOpKind.POW,
    ast.LShift: BinOpKind.LSHIFT,
    ast.RShift: BinOpKind.RSHIFT,
    ast.BitOr: BinOpKind.BIT_OR,
    ast.BitXor: BinOpKind.BIT_XOR,
    ast.BitAnd: BinOpKind.BIT_AND,
    ast.MatMult: BinOpKind.MAT_MULT,
}

_UNARYOP_MAP: Dict[type, UnaryOpKind] = {
    ast.Invert: UnaryOpKind.INVERT,
    ast.Not: UnaryOpKind.NOT,
    ast.UAdd: UnaryOpKind.UADD,
    ast.USub: UnaryOpKind.USUB,
}

_CMPOP_MAP: Dict[type, CmpOpKind] = {
    ast.Eq: CmpOpKind.EQ,
    ast.NotEq: CmpOpKind.NOT_EQ,
    ast.Lt: CmpOpKind.LT,
    ast.LtE: CmpOpKind.LT_EQ,
    ast.Gt: CmpOpKind.GT,
    ast.GtE: CmpOpKind.GT_EQ,
    ast.Is: CmpOpKind.IS,
    ast.IsNot: CmpOpKind.IS_NOT,
    ast.In: CmpOpKind.IN,
    ast.NotIn: CmpOpKind.NOT_IN,
}

_BOOLOP_MAP: Dict[type, BoolOpKind] = {
    ast.And: BoolOpKind.AND,
    ast.Or: BoolOpKind.OR,
}


# ═══════════════════════════════════════════════════════════════════════════════
# Helper: extract docstring from a body
# ═══════════════════════════════════════════════════════════════════════════════

def _extract_docstring(body: Sequence[ast.stmt]) -> Optional[str]:
    """Extract a docstring from the first statement of a body, if present."""
    if body and isinstance(body[0], ast.Expr):
        val = body[0].value
        if isinstance(val, ast.Constant) and isinstance(val.value, str):
            return val.value
    return None


def _body_without_docstring(body: Sequence[ast.stmt]) -> Sequence[ast.stmt]:
    """Return body statements with the docstring removed (if present)."""
    if body and isinstance(body[0], ast.Expr):
        val = body[0].value
        if isinstance(val, ast.Constant) and isinstance(val.value, str):
            return body[1:]
    return body


# ═══════════════════════════════════════════════════════════════════════════════
# IR Lowering visitor
# ═══════════════════════════════════════════════════════════════════════════════

class IRLowering(ast.NodeVisitor):
    """Walks a Python AST and produces an IRModule.

    This is the main entry point for lowering Python source to the
    sheaf-theoretic frontend IR.  Usage::

        tree = ast.parse(source)
        lowering = IRLowering(filename="my_module.py")
        ir_module = lowering.lower_module(tree, module_name="my_module")

    The resulting ``IRModule`` contains all function definitions, class
    definitions, and top-level statements, each annotated with source
    spans for traceability.
    """

    def __init__(self, filename: str = "<unknown>") -> None:
        self._filename = filename
        self._enclosing_class: Optional[str] = None

    def _span(self, node: ast.AST) -> SourceSpan:
        """Create a SourceSpan from an AST node."""
        return SourceSpan.from_ast(node, self._filename)

    # ── Module lowering ───────────────────────────────────────────────────

    def lower_module(
        self,
        tree: ast.Module,
        module_name: str = "<module>",
    ) -> IRModule:
        """Lower an entire ``ast.Module`` to an ``IRModule``."""
        functions: List[IRFunction] = []
        classes: List[IRClass] = []
        statements: List[IRStatement] = []
        imports: List[Union[IRImport, IRImportFrom]] = []

        docstring = _extract_docstring(tree.body)
        body = _body_without_docstring(tree.body) if docstring else tree.body

        for node in body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                functions.append(self._lower_function(node))
            elif isinstance(node, ast.ClassDef):
                classes.append(self._lower_class(node))
            elif isinstance(node, ast.Import):
                imp = self._lower_import(node)
                imports.append(imp)
                statements.append(imp)
            elif isinstance(node, ast.ImportFrom):
                imp = self._lower_import_from(node)
                imports.append(imp)
                statements.append(imp)
            else:
                stmt = self._lower_stmt(node)
                if stmt is not None:
                    statements.append(stmt)

        return IRModule(
            name=module_name,
            filename=self._filename,
            functions=tuple(functions),
            classes=tuple(classes),
            statements=tuple(statements),
            docstring=docstring,
            imports=tuple(imports),
            span=SourceSpan(self._filename, 1, 0),
        )

    # ── Function lowering ─────────────────────────────────────────────────

    def _lower_function(
        self,
        node: Union[ast.FunctionDef, ast.AsyncFunctionDef],
    ) -> IRFunction:
        """Lower a function/method definition to an IRFunction."""
        is_async = isinstance(node, ast.AsyncFunctionDef)
        params = self._lower_arguments(node.args)
        decorators = tuple(
            IRDecorator(expr=self._lower_expr(d), span=self._span(d))
            for d in node.decorator_list
        )
        return_annotation = (
            self._lower_expr(node.returns) if node.returns else None
        )

        docstring = _extract_docstring(node.body)
        body_nodes = _body_without_docstring(node.body) if docstring else node.body
        body = self._lower_body(body_nodes)

        # Detect method-like properties from decorators
        is_method = self._enclosing_class is not None
        is_classmethod = False
        is_staticmethod = False
        is_property = False
        for d in node.decorator_list:
            if isinstance(d, ast.Name):
                if d.id == "classmethod":
                    is_classmethod = True
                elif d.id == "staticmethod":
                    is_staticmethod = True
                elif d.id == "property":
                    is_property = True

        return IRFunction(
            name=node.name,
            params=params,
            body=body,
            decorators=decorators,
            return_annotation=return_annotation,
            is_async=is_async,
            is_method=is_method,
            is_classmethod=is_classmethod,
            is_staticmethod=is_staticmethod,
            is_property=is_property,
            docstring=docstring,
            enclosing_class=self._enclosing_class,
            span=self._span(node),
        )

    def _lower_arguments(self, args: ast.arguments) -> Tuple[IRParam, ...]:
        """Lower function arguments to IRParam tuples."""
        params: List[IRParam] = []
        idx = 0

        # Positional-only args (Python 3.8+)
        for i, arg in enumerate(args.posonlyargs):
            params.append(self._lower_one_arg(arg, idx, is_positional_only=True))
            idx += 1

        # Regular positional args
        defaults_offset = len(args.args) - len(args.defaults)
        for i, arg in enumerate(args.args):
            default = None
            if i >= defaults_offset:
                default = self._lower_expr(args.defaults[i - defaults_offset])
            is_self = (
                idx == 0
                and self._enclosing_class is not None
                and arg.arg == "self"
            )
            is_cls = (
                idx == 0
                and self._enclosing_class is not None
                and arg.arg == "cls"
            )
            params.append(self._lower_one_arg(
                arg, idx, default=default, is_self=is_self, is_cls=is_cls,
            ))
            idx += 1

        # *args
        if args.vararg:
            params.append(self._lower_one_arg(args.vararg, idx, is_vararg=True))
            idx += 1

        # Keyword-only args
        for i, arg in enumerate(args.kwonlyargs):
            default = None
            if i < len(args.kw_defaults) and args.kw_defaults[i] is not None:
                default = self._lower_expr(args.kw_defaults[i])
            params.append(self._lower_one_arg(
                arg, idx, default=default, is_keyword_only=True,
            ))
            idx += 1

        # **kwargs
        if args.kwarg:
            params.append(self._lower_one_arg(args.kwarg, idx, is_kwarg=True))
            idx += 1

        return tuple(params)

    def _lower_one_arg(
        self,
        arg: ast.arg,
        index: int,
        *,
        default: Optional[IRExpr] = None,
        is_self: bool = False,
        is_cls: bool = False,
        is_vararg: bool = False,
        is_kwarg: bool = False,
        is_keyword_only: bool = False,
        is_positional_only: bool = False,
    ) -> IRParam:
        annotation = self._lower_expr(arg.annotation) if arg.annotation else None
        return IRParam(
            name=arg.arg,
            index=index,
            annotation=annotation,
            default=default,
            is_self=is_self,
            is_cls=is_cls,
            is_vararg=is_vararg,
            is_kwarg=is_kwarg,
            is_keyword_only=is_keyword_only,
            is_positional_only=is_positional_only,
            span=self._span(arg),
        )

    # ── Class lowering ────────────────────────────────────────────────────

    def _lower_class(self, node: ast.ClassDef) -> IRClass:
        """Lower a class definition to an IRClass."""
        bases = tuple(self._lower_expr(b) for b in node.bases)
        keywords = tuple(
            (kw.arg or "", self._lower_expr(kw.value))
            for kw in node.keywords
        )
        decorators = tuple(
            IRDecorator(expr=self._lower_expr(d), span=self._span(d))
            for d in node.decorator_list
        )

        docstring = _extract_docstring(node.body)
        body_nodes = _body_without_docstring(node.body) if docstring else node.body

        # Save and set enclosing class context
        prev_class = self._enclosing_class
        self._enclosing_class = node.name

        body: List[Union[IRFunction, IRStatement]] = []
        for stmt_node in body_nodes:
            if isinstance(stmt_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                body.append(self._lower_function(stmt_node))
            else:
                lowered = self._lower_stmt(stmt_node)
                if lowered is not None:
                    body.append(lowered)

        self._enclosing_class = prev_class

        return IRClass(
            name=node.name,
            bases=bases,
            keywords=keywords,
            body=tuple(body),
            decorators=decorators,
            docstring=docstring,
            span=self._span(node),
        )

    # ── Statement lowering ────────────────────────────────────────────────

    def _lower_body(self, body: Sequence[ast.stmt]) -> Tuple[IRStatement, ...]:
        """Lower a sequence of AST statements to IR statements."""
        result: List[IRStatement] = []
        for node in body:
            stmt = self._lower_stmt(node)
            if stmt is not None:
                result.append(stmt)
        return tuple(result)

    def _lower_stmt(self, node: ast.stmt) -> Optional[IRStatement]:
        """Lower a single AST statement to an IR statement."""

        if isinstance(node, ast.Assign):
            return self._lower_assign(node)

        if isinstance(node, ast.AnnAssign):
            return self._lower_ann_assign(node)

        if isinstance(node, ast.AugAssign):
            return self._lower_aug_assign(node)

        if isinstance(node, ast.Return):
            value = self._lower_expr(node.value) if node.value else None
            return IRReturn(value=value, span=self._span(node))

        if isinstance(node, ast.If):
            return self._lower_if(node)

        if isinstance(node, ast.For):
            return self._lower_for(node)

        if isinstance(node, ast.AsyncFor):
            return self._lower_for(node, is_async=True)

        if isinstance(node, ast.While):
            return self._lower_while(node)

        if isinstance(node, ast.Raise):
            return self._lower_raise(node)

        if isinstance(node, ast.Try):
            return self._lower_try(node)

        if hasattr(ast, "TryStar") and isinstance(node, ast.TryStar):
            return self._lower_try(node)

        if isinstance(node, ast.With):
            return self._lower_with(node)

        if isinstance(node, ast.AsyncWith):
            return self._lower_with(node, is_async=True)

        if isinstance(node, ast.Assert):
            return self._lower_assert(node)

        if isinstance(node, ast.Expr):
            return IRExprStmt(
                value=self._lower_expr(node.value),
                span=self._span(node),
            )

        if isinstance(node, ast.Delete):
            return IRDelete(
                targets=tuple(self._lower_expr(t) for t in node.targets),
                span=self._span(node),
            )

        if isinstance(node, ast.Import):
            return self._lower_import(node)

        if isinstance(node, ast.ImportFrom):
            return self._lower_import_from(node)

        if isinstance(node, ast.Global):
            return IRGlobal(
                names=tuple(node.names),
                span=self._span(node),
            )

        if isinstance(node, ast.Nonlocal):
            return IRNonlocal(
                names=tuple(node.names),
                span=self._span(node),
            )

        if isinstance(node, ast.Pass):
            return IRPass(span=self._span(node))

        if isinstance(node, ast.Break):
            return IRBreak(span=self._span(node))

        if isinstance(node, ast.Continue):
            return IRContinue(span=self._span(node))

        # FunctionDef and ClassDef in a body are handled at the module/class level
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            # Nested functions: lower inline and wrap in an expression statement
            func = self._lower_function(node)
            # Represent as an assignment of the function to its name
            return IRAssign(
                targets=(IRName(name=func.name, span=func.span),),
                value=IRConstant(value=f"<function {func.name}>", kind="function", span=func.span),
                span=func.span,
            )

        if isinstance(node, ast.ClassDef):
            cls = self._lower_class(node)
            return IRAssign(
                targets=(IRName(name=cls.name, span=cls.span),),
                value=IRConstant(value=f"<class {cls.name}>", kind="class", span=cls.span),
                span=cls.span,
            )

        # Fallback: pass (should not happen for well-formed ASTs)
        return IRPass(span=self._span(node))

    def _lower_assign(self, node: ast.Assign) -> IRAssign:
        targets = tuple(self._lower_expr(t) for t in node.targets)
        value = self._lower_expr(node.value)
        return IRAssign(targets=targets, value=value, span=self._span(node))

    def _lower_ann_assign(self, node: ast.AnnAssign) -> IRAssign:
        target = self._lower_expr(node.target)
        annotation = self._lower_expr(node.annotation)
        value = self._lower_expr(node.value) if node.value else IRConstant(value=None, kind="None", span=self._span(node))
        return IRAssign(
            targets=(target,),
            value=value,
            type_annotation=annotation,
            span=self._span(node),
        )

    def _lower_aug_assign(self, node: ast.AugAssign) -> IRAugAssign:
        target = self._lower_expr(node.target)
        op = _BINOP_MAP.get(type(node.op), BinOpKind.ADD)
        value = self._lower_expr(node.value)
        return IRAugAssign(target=target, op=op, value=value, span=self._span(node))

    def _lower_if(self, node: ast.If) -> IRIf:
        test = self._lower_expr(node.test)
        body = self._lower_body(node.body)
        orelse = self._lower_body(node.orelse)
        return IRIf(test=test, body=body, orelse=orelse, span=self._span(node))

    def _lower_for(
        self,
        node: Union[ast.For, ast.AsyncFor],
        is_async: bool = False,
    ) -> IRFor:
        target = self._lower_expr(node.target)
        iter_expr = self._lower_expr(node.iter)
        body = self._lower_body(node.body)
        orelse = self._lower_body(node.orelse)
        return IRFor(
            target=target, iter=iter_expr,
            body=body, orelse=orelse,
            span=self._span(node),
        )

    def _lower_while(self, node: ast.While) -> IRWhile:
        test = self._lower_expr(node.test)
        body = self._lower_body(node.body)
        orelse = self._lower_body(node.orelse)
        return IRWhile(test=test, body=body, orelse=orelse, span=self._span(node))

    def _lower_raise(self, node: ast.Raise) -> IRRaise:
        exc = self._lower_expr(node.exc) if node.exc else None
        cause = self._lower_expr(node.cause) if node.cause else None
        return IRRaise(exc=exc, cause=cause, span=self._span(node))

    def _lower_try(self, node: ast.Try) -> IRTry:
        body = self._lower_body(node.body)
        handlers = tuple(
            self._lower_except_handler(h) for h in node.handlers
        )
        orelse = self._lower_body(node.orelse)
        finalbody = self._lower_body(node.finalbody)
        return IRTry(
            body=body, handlers=handlers,
            orelse=orelse, finalbody=finalbody,
            span=self._span(node),
        )

    def _lower_except_handler(self, node: ast.ExceptHandler) -> IRExceptHandler:
        type_expr = self._lower_expr(node.type) if node.type else None
        body = self._lower_body(node.body)
        return IRExceptHandler(
            type=type_expr, name=node.name,
            body=body, span=self._span(node),
        )

    def _lower_with(
        self,
        node: Union[ast.With, ast.AsyncWith],
        is_async: bool = False,
    ) -> IRWith:
        items: List[Tuple[IRExpr, Optional[IRExpr]]] = []
        for item in node.items:
            ctx = self._lower_expr(item.context_expr)
            var = self._lower_expr(item.optional_vars) if item.optional_vars else None
            items.append((ctx, var))
        body = self._lower_body(node.body)
        return IRWith(
            items=tuple(items), body=body,
            is_async=is_async or isinstance(node, ast.AsyncWith),
            span=self._span(node),
        )

    def _lower_assert(self, node: ast.Assert) -> IRAssert:
        test = self._lower_expr(node.test)
        msg = self._lower_expr(node.msg) if node.msg else None
        return IRAssert(test=test, msg=msg, span=self._span(node))

    def _lower_import(self, node: ast.Import) -> IRImport:
        names = tuple((alias.name, alias.asname) for alias in node.names)
        return IRImport(names=names, span=self._span(node))

    def _lower_import_from(self, node: ast.ImportFrom) -> IRImportFrom:
        names = tuple((alias.name, alias.asname) for alias in node.names)
        return IRImportFrom(
            module=node.module,
            names=names,
            level=node.level or 0,
            span=self._span(node),
        )

    # ── Expression lowering ───────────────────────────────────────────────

    def _lower_expr(self, node: ast.expr) -> IRExpr:
        """Lower a single AST expression to an IR expression."""

        if isinstance(node, ast.Name):
            return IRName(name=node.id, span=self._span(node))

        if isinstance(node, ast.Constant):
            return self._lower_constant(node)

        if isinstance(node, ast.Call):
            return self._lower_call(node)

        if isinstance(node, ast.BinOp):
            op = _BINOP_MAP.get(type(node.op), BinOpKind.ADD)
            return IRBinOp(
                left=self._lower_expr(node.left),
                op=op,
                right=self._lower_expr(node.right),
                span=self._span(node),
            )

        if isinstance(node, ast.UnaryOp):
            op = _UNARYOP_MAP.get(type(node.op), UnaryOpKind.USUB)
            return IRUnaryOp(
                op=op,
                operand=self._lower_expr(node.operand),
                span=self._span(node),
            )

        if isinstance(node, ast.BoolOp):
            op = _BOOLOP_MAP.get(type(node.op), BoolOpKind.AND)
            return IRBoolOp(
                op=op,
                values=tuple(self._lower_expr(v) for v in node.values),
                span=self._span(node),
            )

        if isinstance(node, ast.Compare):
            return IRCompare(
                left=self._lower_expr(node.left),
                ops=tuple(_CMPOP_MAP.get(type(o), CmpOpKind.EQ) for o in node.ops),
                comparators=tuple(self._lower_expr(c) for c in node.comparators),
                span=self._span(node),
            )

        if isinstance(node, ast.Subscript):
            return IRSubscript(
                value=self._lower_expr(node.value),
                slice=self._lower_expr(node.slice),
                span=self._span(node),
            )

        if isinstance(node, ast.Attribute):
            return IRAttribute(
                value=self._lower_expr(node.value),
                attr=node.attr,
                span=self._span(node),
            )

        if isinstance(node, ast.Tuple):
            return IRTuple(
                elts=tuple(self._lower_expr(e) for e in node.elts),
                span=self._span(node),
            )

        if isinstance(node, ast.List):
            return IRList(
                elts=tuple(self._lower_expr(e) for e in node.elts),
                span=self._span(node),
            )

        if isinstance(node, ast.Dict):
            keys = tuple(
                self._lower_expr(k) if k is not None else None
                for k in node.keys
            )
            values = tuple(self._lower_expr(v) for v in node.values)
            return IRDict(keys=keys, values=values, span=self._span(node))

        if isinstance(node, ast.Set):
            return IRSet(
                elts=tuple(self._lower_expr(e) for e in node.elts),
                span=self._span(node),
            )

        if isinstance(node, ast.Lambda):
            params = self._lower_arguments(node.args)
            body = self._lower_expr(node.body)
            return IRLambda(args=params, body=body, span=self._span(node))

        if isinstance(node, ast.IfExp):
            return IRIfExpr(
                test=self._lower_expr(node.test),
                body=self._lower_expr(node.body),
                orelse=self._lower_expr(node.orelse),
                span=self._span(node),
            )

        if isinstance(node, ast.ListComp):
            return self._lower_comprehension(node, is_list=True)

        if isinstance(node, ast.SetComp):
            return self._lower_comprehension(node, is_set=True)

        if isinstance(node, ast.DictComp):
            return self._lower_dict_comprehension(node)

        if isinstance(node, ast.GeneratorExp):
            return self._lower_comprehension(node, is_generator=True)

        if isinstance(node, ast.Starred):
            return IRStarred(
                value=self._lower_expr(node.value),
                span=self._span(node),
            )

        if isinstance(node, ast.Yield):
            value = self._lower_expr(node.value) if node.value else None
            return IRYield(value=value, span=self._span(node))

        if isinstance(node, ast.YieldFrom):
            return IRYieldFrom(
                value=self._lower_expr(node.value),
                span=self._span(node),
            )

        if isinstance(node, ast.Await):
            return IRAwait(
                value=self._lower_expr(node.value),
                span=self._span(node),
            )

        if isinstance(node, ast.Slice):
            lower = self._lower_expr(node.lower) if node.lower else None
            upper = self._lower_expr(node.upper) if node.upper else None
            step = self._lower_expr(node.step) if node.step else None
            return IRSlice(lower=lower, upper=upper, step=step, span=self._span(node))

        if isinstance(node, ast.JoinedStr):
            return IRFString(
                values=tuple(self._lower_expr(v) for v in node.values),
                span=self._span(node),
            )

        if isinstance(node, ast.FormattedValue):
            return self._lower_expr(node.value)

        if isinstance(node, ast.NamedExpr):
            # Walrus operator: treat as an assignment-like expression
            # Lower the value; the name can be extracted from target
            return IRBinOp(
                left=self._lower_expr(node.target),
                op=BinOpKind.ADD,  # Placeholder; walrus is really assignment
                right=self._lower_expr(node.value),
                span=self._span(node),
            )

        # Fallback for unknown expression types
        return IRConstant(
            value=f"<unsupported: {type(node).__name__}>",
            kind="unknown",
            span=self._span(node),
        )

    def _lower_constant(self, node: ast.Constant) -> IRConstant:
        """Lower an ast.Constant to an IRConstant."""
        value = node.value
        if value is None:
            kind = "None"
        elif isinstance(value, bool):
            kind = "bool"
        elif isinstance(value, int):
            kind = "int"
        elif isinstance(value, float):
            kind = "float"
        elif isinstance(value, complex):
            kind = "complex"
        elif isinstance(value, str):
            kind = "str"
        elif isinstance(value, bytes):
            kind = "bytes"
        elif value is ...:
            kind = "ellipsis"
        else:
            kind = type(value).__name__
        return IRConstant(value=value, kind=kind, span=self._span(node))

    def _lower_call(self, node: ast.Call) -> IRCall:
        """Lower an ast.Call to an IRCall."""
        func = self._lower_expr(node.func)
        args = tuple(self._lower_expr(a) for a in node.args)
        keywords: List[Tuple[Optional[str], IRExpr]] = []
        starargs: List[IRExpr] = []

        for kw in node.keywords:
            if kw.arg is None:
                # **kwargs expansion
                keywords.append((None, self._lower_expr(kw.value)))
            else:
                keywords.append((kw.arg, self._lower_expr(kw.value)))

        # Separate starred args from positional args
        filtered_args: List[IRExpr] = []
        for a in args:
            if isinstance(a, IRStarred):
                starargs.append(a.value)
            else:
                filtered_args.append(a)

        return IRCall(
            func=func,
            args=tuple(filtered_args),
            keywords=tuple(keywords),
            starargs=tuple(starargs),
            span=self._span(node),
        )

    def _lower_comprehension(
        self,
        node: Union[ast.ListComp, ast.SetComp, ast.GeneratorExp],
        *,
        is_list: bool = False,
        is_set: bool = False,
        is_generator: bool = False,
    ) -> IRComprehension:
        element = self._lower_expr(node.elt)
        generators = tuple(
            self._lower_comp_generator(g) for g in node.generators
        )
        return IRComprehension(
            element=element,
            generators=generators,
            is_list=is_list,
            is_set=is_set,
            is_generator=is_generator,
            span=self._span(node),
        )

    def _lower_dict_comprehension(self, node: ast.DictComp) -> IRComprehension:
        key_expr = self._lower_expr(node.key)
        value_expr = self._lower_expr(node.value)
        generators = tuple(
            self._lower_comp_generator(g) for g in node.generators
        )
        return IRComprehension(
            element=key_expr,
            generators=generators,
            is_dict=True,
            value=value_expr,
            span=self._span(node),
        )

    def _lower_comp_generator(
        self, gen: ast.comprehension
    ) -> IRComprehensionGenerator:
        return IRComprehensionGenerator(
            target=self._lower_expr(gen.target),
            iter=self._lower_expr(gen.iter),
            ifs=tuple(self._lower_expr(c) for c in gen.ifs),
            is_async=gen.is_async != 0,
            span=self._span(gen.target),
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Convenience functions
# ═══════════════════════════════════════════════════════════════════════════════


def lower_source(
    source: str,
    filename: str = "<string>",
    module_name: str = "<module>",
) -> IRModule:
    """Parse Python source and lower to IR in one step.

    This is the main entry point for turning Python source text into
    the sheaf-theoretic frontend IR::

        ir = lower_source("def f(x: int) -> int: return x + 1")
    """
    tree = ast.parse(source, filename=filename)
    lowering = IRLowering(filename=filename)
    return lowering.lower_module(tree, module_name=module_name)


def lower_file(
    filepath: str,
    module_name: Optional[str] = None,
) -> IRModule:
    """Read a Python file and lower to IR.

    If *module_name* is not given, it is derived from the filename.
    """
    with open(filepath, "r") as f:
        source = f.read()
    name = module_name or filepath.rsplit("/", 1)[-1].replace(".py", "")
    return lower_source(source, filename=filepath, module_name=name)
