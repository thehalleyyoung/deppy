"""Pretty-printing for the sheaf-theoretic frontend IR.

Renders IR nodes as indented text for debugging and inspection.
Every IR node type has a corresponding rendering method that produces
human-readable output showing the structure of the lowered program.

Usage::

    from deppy.frontend.ir.pretty_printer import pretty_print
    text = pretty_print(ir_module)
    print(text)
"""

from __future__ import annotations

from io import StringIO
from typing import (
    Any,
    List,
    Optional,
    Sequence,
    Tuple,
    Union,
)

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
)
from deppy.static_analysis.observation_sites import SourceSpan


class PrettyPrinter:
    """Renders IR nodes as indented text.

    The printer maintains an indentation level and emits one logical
    construct per line, with sub-expressions rendered inline or on
    subsequent indented lines depending on complexity.
    """

    def __init__(self, indent_width: int = 2) -> None:
        self._indent_width = indent_width
        self._buf = StringIO()
        self._level = 0

    def _indent(self) -> str:
        return " " * (self._level * self._indent_width)

    def _write(self, text: str) -> None:
        self._buf.write(text)

    def _writeln(self, text: str) -> None:
        self._buf.write(self._indent() + text + "\n")

    def _span_str(self, span: SourceSpan) -> str:
        if span.file == "<unknown>" and span.start_line == 0:
            return ""
        if span.end_line > 0 and span.end_line != span.start_line:
            return f"  # {span.file}:{span.start_line}-{span.end_line}"
        return f"  # {span.file}:{span.start_line}"

    # ── Module ────────────────────────────────────────────────────────────

    def print_module(self, mod: IRModule) -> str:
        """Render an entire IR module."""
        self._writeln(f"IRModule {mod.name!r} ({mod.filename})")
        if mod.docstring:
            self._level += 1
            self._writeln(f'"""{mod.docstring}"""')
            self._level -= 1

        if mod.imports:
            self._level += 1
            self._writeln("--- imports ---")
            for imp in mod.imports:
                self._print_stmt(imp)
            self._level -= 1

        if mod.statements:
            self._level += 1
            self._writeln("--- top-level statements ---")
            for stmt in mod.statements:
                self._print_stmt(stmt)
            self._level -= 1

        if mod.classes:
            self._level += 1
            for cls in mod.classes:
                self._print_class(cls)
            self._level -= 1

        if mod.functions:
            self._level += 1
            for func in mod.functions:
                self._print_function(func)
            self._level -= 1

        return self._buf.getvalue()

    # ── Function ──────────────────────────────────────────────────────────

    def _print_function(self, func: IRFunction) -> None:
        for dec in func.decorators:
            self._writeln(f"@{self._expr_str(dec.expr)}")

        prefix = "async " if func.is_async else ""
        params = ", ".join(self._param_str(p) for p in func.params)
        ret = ""
        if func.return_annotation is not None:
            ret = f" -> {self._expr_str(func.return_annotation)}"
        self._writeln(f"{prefix}def {func.name}({params}){ret}:{self._span_str(func.span)}")

        self._level += 1
        if func.docstring:
            self._writeln(f'"""{func.docstring}"""')
        for stmt in func.body:
            self._print_stmt(stmt)
        self._level -= 1

    def _param_str(self, param: IRParam) -> str:
        parts: List[str] = []
        if param.is_vararg:
            parts.append("*")
        elif param.is_kwarg:
            parts.append("**")
        parts.append(param.name)
        if param.annotation is not None:
            parts.append(f": {self._expr_str(param.annotation)}")
        if param.default is not None:
            parts.append(f" = {self._expr_str(param.default)}")
        return "".join(parts)

    # ── Class ─────────────────────────────────────────────────────────────

    def _print_class(self, cls: IRClass) -> None:
        for dec in cls.decorators:
            self._writeln(f"@{self._expr_str(dec.expr)}")

        bases = ", ".join(self._expr_str(b) for b in cls.bases)
        kw_parts = [f"{k}={self._expr_str(v)}" for k, v in cls.keywords]
        all_args = bases
        if kw_parts:
            if all_args:
                all_args += ", "
            all_args += ", ".join(kw_parts)
        self._writeln(f"class {cls.name}({all_args}):{self._span_str(cls.span)}")

        self._level += 1
        if cls.docstring:
            self._writeln(f'"""{cls.docstring}"""')
        for item in cls.body:
            if isinstance(item, IRFunction):
                self._print_function(item)
            else:
                self._print_stmt(item)
        self._level -= 1

    # ── Statements ────────────────────────────────────────────────────────

    def _print_stmt(self, stmt: IRStatement) -> None:
        if isinstance(stmt, IRAssign):
            targets = " = ".join(self._expr_str(t) for t in stmt.targets)
            ann = ""
            if stmt.type_annotation is not None:
                ann = f": {self._expr_str(stmt.type_annotation)} "
            self._writeln(f"{targets}{ann} = {self._expr_str(stmt.value)}{self._span_str(stmt.span)}")

        elif isinstance(stmt, IRAugAssign):
            self._writeln(
                f"{self._expr_str(stmt.target)} {stmt.op.value}= "
                f"{self._expr_str(stmt.value)}{self._span_str(stmt.span)}"
            )

        elif isinstance(stmt, IRReturn):
            val = f" {self._expr_str(stmt.value)}" if stmt.value is not None else ""
            self._writeln(f"return{val}{self._span_str(stmt.span)}")

        elif isinstance(stmt, IRIf):
            self._writeln(f"if {self._expr_str(stmt.test)}:{self._span_str(stmt.span)}")
            self._level += 1
            for s in stmt.body:
                self._print_stmt(s)
            self._level -= 1
            if stmt.orelse:
                # Check if the else is an elif
                if len(stmt.orelse) == 1 and isinstance(stmt.orelse[0], IRIf):
                    self._writeln("elif ...")
                    self._level += 1
                    self._print_stmt(stmt.orelse[0])
                    self._level -= 1
                else:
                    self._writeln("else:")
                    self._level += 1
                    for s in stmt.orelse:
                        self._print_stmt(s)
                    self._level -= 1

        elif isinstance(stmt, IRFor):
            self._writeln(
                f"for {self._expr_str(stmt.target)} in "
                f"{self._expr_str(stmt.iter)}:{self._span_str(stmt.span)}"
            )
            self._level += 1
            for s in stmt.body:
                self._print_stmt(s)
            self._level -= 1
            if stmt.orelse:
                self._writeln("else:")
                self._level += 1
                for s in stmt.orelse:
                    self._print_stmt(s)
                self._level -= 1

        elif isinstance(stmt, IRWhile):
            self._writeln(f"while {self._expr_str(stmt.test)}:{self._span_str(stmt.span)}")
            self._level += 1
            for s in stmt.body:
                self._print_stmt(s)
            self._level -= 1
            if stmt.orelse:
                self._writeln("else:")
                self._level += 1
                for s in stmt.orelse:
                    self._print_stmt(s)
                self._level -= 1

        elif isinstance(stmt, IRRaise):
            parts = ["raise"]
            if stmt.exc is not None:
                parts.append(f" {self._expr_str(stmt.exc)}")
            if stmt.cause is not None:
                parts.append(f" from {self._expr_str(stmt.cause)}")
            self._writeln("".join(parts) + self._span_str(stmt.span))

        elif isinstance(stmt, IRTry):
            self._writeln(f"try:{self._span_str(stmt.span)}")
            self._level += 1
            for s in stmt.body:
                self._print_stmt(s)
            self._level -= 1
            for handler in stmt.handlers:
                type_str = ""
                if handler.type is not None:
                    type_str = f" {self._expr_str(handler.type)}"
                name_str = ""
                if handler.name is not None:
                    name_str = f" as {handler.name}"
                self._writeln(f"except{type_str}{name_str}:")
                self._level += 1
                for s in handler.body:
                    self._print_stmt(s)
                self._level -= 1
            if stmt.orelse:
                self._writeln("else:")
                self._level += 1
                for s in stmt.orelse:
                    self._print_stmt(s)
                self._level -= 1
            if stmt.finalbody:
                self._writeln("finally:")
                self._level += 1
                for s in stmt.finalbody:
                    self._print_stmt(s)
                self._level -= 1

        elif isinstance(stmt, IRWith):
            prefix = "async " if stmt.is_async else ""
            items_str = ", ".join(
                self._expr_str(ctx) + (f" as {self._expr_str(var)}" if var else "")
                for ctx, var in stmt.items
            )
            self._writeln(f"{prefix}with {items_str}:{self._span_str(stmt.span)}")
            self._level += 1
            for s in stmt.body:
                self._print_stmt(s)
            self._level -= 1

        elif isinstance(stmt, IRAssert):
            msg = ""
            if stmt.msg is not None:
                msg = f", {self._expr_str(stmt.msg)}"
            self._writeln(f"assert {self._expr_str(stmt.test)}{msg}{self._span_str(stmt.span)}")

        elif isinstance(stmt, IRExprStmt):
            self._writeln(f"{self._expr_str(stmt.value)}{self._span_str(stmt.span)}")

        elif isinstance(stmt, IRDelete):
            targets = ", ".join(self._expr_str(t) for t in stmt.targets)
            self._writeln(f"del {targets}{self._span_str(stmt.span)}")

        elif isinstance(stmt, IRImport):
            names = ", ".join(
                f"{mod} as {alias}" if alias else mod
                for mod, alias in stmt.names
            )
            self._writeln(f"import {names}{self._span_str(stmt.span)}")

        elif isinstance(stmt, IRImportFrom):
            mod = stmt.module or ""
            dots = "." * stmt.level
            names = ", ".join(
                f"{name} as {alias}" if alias else name
                for name, alias in stmt.names
            )
            self._writeln(f"from {dots}{mod} import {names}{self._span_str(stmt.span)}")

        elif isinstance(stmt, IRGlobal):
            self._writeln(f"global {', '.join(stmt.names)}{self._span_str(stmt.span)}")

        elif isinstance(stmt, IRNonlocal):
            self._writeln(f"nonlocal {', '.join(stmt.names)}{self._span_str(stmt.span)}")

        elif isinstance(stmt, IRPass):
            self._writeln(f"pass{self._span_str(stmt.span)}")

        elif isinstance(stmt, IRBreak):
            self._writeln(f"break{self._span_str(stmt.span)}")

        elif isinstance(stmt, IRContinue):
            self._writeln(f"continue{self._span_str(stmt.span)}")

        else:
            self._writeln(f"<unknown statement: {type(stmt).__name__}>")

    # ── Expressions ───────────────────────────────────────────────────────

    def _expr_str(self, expr: IRExpr) -> str:
        """Render an expression as a single-line string."""
        if isinstance(expr, IRName):
            return expr.name

        if isinstance(expr, IRConstant):
            return repr(expr.value)

        if isinstance(expr, IRCall):
            func_str = self._expr_str(expr.func)
            args: List[str] = [self._expr_str(a) for a in expr.args]
            for key, val in expr.keywords:
                if key is not None:
                    args.append(f"{key}={self._expr_str(val)}")
                else:
                    args.append(f"**{self._expr_str(val)}")
            for sa in expr.starargs:
                args.append(f"*{self._expr_str(sa)}")
            return f"{func_str}({', '.join(args)})"

        if isinstance(expr, IRBinOp):
            return f"({self._expr_str(expr.left)} {expr.op.value} {self._expr_str(expr.right)})"

        if isinstance(expr, IRUnaryOp):
            if expr.op == UnaryOpKind.NOT:
                return f"(not {self._expr_str(expr.operand)})"
            return f"({expr.op.value}{self._expr_str(expr.operand)})"

        if isinstance(expr, IRBoolOp):
            sep = f" {expr.op.value} "
            return f"({sep.join(self._expr_str(v) for v in expr.values)})"

        if isinstance(expr, IRCompare):
            parts = [self._expr_str(expr.left)]
            for op, comp in zip(expr.ops, expr.comparators):
                parts.append(op.value)
                parts.append(self._expr_str(comp))
            return f"({' '.join(parts)})"

        if isinstance(expr, IRSubscript):
            return f"{self._expr_str(expr.value)}[{self._expr_str(expr.slice)}]"

        if isinstance(expr, IRAttribute):
            return f"{self._expr_str(expr.value)}.{expr.attr}"

        if isinstance(expr, IRTuple):
            elts = ", ".join(self._expr_str(e) for e in expr.elts)
            if len(expr.elts) == 1:
                return f"({elts},)"
            return f"({elts})"

        if isinstance(expr, IRList):
            return f"[{', '.join(self._expr_str(e) for e in expr.elts)}]"

        if isinstance(expr, IRDict):
            pairs: List[str] = []
            for k, v in zip(expr.keys, expr.values):
                if k is not None:
                    pairs.append(f"{self._expr_str(k)}: {self._expr_str(v)}")
                else:
                    pairs.append(f"**{self._expr_str(v)}")
            return "{" + ", ".join(pairs) + "}"

        if isinstance(expr, IRSet):
            return "{" + ", ".join(self._expr_str(e) for e in expr.elts) + "}"

        if isinstance(expr, IRLambda):
            params = ", ".join(self._param_str(p) for p in expr.args)
            return f"(lambda {params}: {self._expr_str(expr.body)})"

        if isinstance(expr, IRIfExpr):
            return (
                f"({self._expr_str(expr.body)} if {self._expr_str(expr.test)} "
                f"else {self._expr_str(expr.orelse)})"
            )

        if isinstance(expr, IRComprehension):
            if expr.is_dict:
                elem = f"{self._expr_str(expr.element)}: {self._expr_str(expr.value)}"
            else:
                elem = self._expr_str(expr.element)
            gens = " ".join(self._gen_str(g) for g in expr.generators)
            if expr.is_list:
                return f"[{elem} {gens}]"
            if expr.is_set:
                return "{" + f"{elem} {gens}" + "}"
            if expr.is_dict:
                return "{" + f"{elem} {gens}" + "}"
            return f"({elem} {gens})"

        if isinstance(expr, IRComprehensionGenerator):
            return self._gen_str(expr)

        if isinstance(expr, IRStarred):
            return f"*{self._expr_str(expr.value)}"

        if isinstance(expr, IRFString):
            parts = []
            for v in expr.values:
                if isinstance(v, IRConstant) and isinstance(v.value, str):
                    parts.append(v.value)
                else:
                    parts.append(f"{{{self._expr_str(v)}}}")
            return 'f"' + "".join(parts) + '"'

        if isinstance(expr, IRYield):
            if expr.value is not None:
                return f"(yield {self._expr_str(expr.value)})"
            return "(yield)"

        if isinstance(expr, IRYieldFrom):
            return f"(yield from {self._expr_str(expr.value)})"

        if isinstance(expr, IRAwait):
            return f"(await {self._expr_str(expr.value)})"

        if isinstance(expr, IRSlice):
            lower = self._expr_str(expr.lower) if expr.lower is not None else ""
            upper = self._expr_str(expr.upper) if expr.upper is not None else ""
            if expr.step is not None:
                return f"{lower}:{upper}:{self._expr_str(expr.step)}"
            return f"{lower}:{upper}"

        return f"<unknown expr: {type(expr).__name__}>"

    def _gen_str(self, gen: IRComprehensionGenerator) -> str:
        prefix = "async " if gen.is_async else ""
        result = f"{prefix}for {self._expr_str(gen.target)} in {self._expr_str(gen.iter)}"
        for cond in gen.ifs:
            result += f" if {self._expr_str(cond)}"
        return result

    def result(self) -> str:
        """Return the accumulated output text."""
        return self._buf.getvalue()


# ═══════════════════════════════════════════════════════════════════════════════
# Convenience functions
# ═══════════════════════════════════════════════════════════════════════════════


def pretty_print(ir_node: Union[IRModule, IRFunction, IRClass]) -> str:
    """Pretty-print an IR node to a string.

    Accepts an IRModule, IRFunction, or IRClass and returns a
    human-readable text representation.
    """
    pp = PrettyPrinter()
    if isinstance(ir_node, IRModule):
        return pp.print_module(ir_node)
    elif isinstance(ir_node, IRFunction):
        pp._print_function(ir_node)
        return pp.result()
    elif isinstance(ir_node, IRClass):
        pp._print_class(ir_node)
        return pp.result()
    else:
        return f"<unsupported IR node: {type(ir_node).__name__}>"


def pretty_print_stmt(stmt: IRStatement) -> str:
    """Pretty-print a single IR statement."""
    pp = PrettyPrinter()
    pp._print_stmt(stmt)
    return pp.result()


def pretty_print_expr(expr: IRExpr) -> str:
    """Pretty-print a single IR expression."""
    pp = PrettyPrinter()
    return pp._expr_str(expr)
