"""Tests for deppy.frontend.ast_visitor -- AST lowering to IR.

Exercises every major syntactic construct: functions, classes, if/else,
for/while, try/except, imports, decorators, comprehensions, and assorted
expression forms.  Verifies IR node types, field values, and structural
relationships.
"""

from __future__ import annotations

import ast
import pytest

from deppy.frontend.ast_visitor import IRLowering, lower_source, lower_file
from deppy.frontend.ir.core_term import (
    BinOpKind,
    BoolOpKind,
    CmpOpKind,
    IRAssert,
    IRAssign,
    IRAttribute,
    IRAugAssign,
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


# ===================================================================
# Helpers
# ===================================================================

def _lower(source: str) -> IRModule:
    """Parse source and lower to IR."""
    return lower_source(source, filename="test.py", module_name="test_mod")


# ===================================================================
# TestBasicFunctionLowering
# ===================================================================

class TestBasicFunctionLowering:
    """Test lowering of function definitions."""

    def test_simple_function(self):
        ir = _lower("def f(x): return x")
        assert ir.name == "test_mod"
        assert len(ir.functions) == 1
        func = ir.functions[0]
        assert func.name == "f"
        assert len(func.params) == 1
        assert func.params[0].name == "x"

    def test_function_with_annotations(self):
        ir = _lower("def f(x: int, y: str) -> bool: return True")
        func = ir.functions[0]
        assert func.params[0].name == "x"
        assert isinstance(func.params[0].annotation, IRName)
        assert func.params[0].annotation.name == "int"
        assert isinstance(func.return_annotation, IRName)
        assert func.return_annotation.name == "bool"

    def test_function_with_default(self):
        ir = _lower("def f(x, y=10): pass")
        func = ir.functions[0]
        assert func.params[1].default is not None
        assert isinstance(func.params[1].default, IRConstant)
        assert func.params[1].default.value == 10

    def test_async_function(self):
        ir = _lower("async def g(): pass")
        func = ir.functions[0]
        assert func.is_async is True
        assert func.name == "g"

    def test_function_with_varargs(self):
        ir = _lower("def f(*args, **kwargs): pass")
        func = ir.functions[0]
        vararg = [p for p in func.params if p.is_vararg]
        kwarg = [p for p in func.params if p.is_kwarg]
        assert len(vararg) == 1
        assert vararg[0].name == "args"
        assert len(kwarg) == 1
        assert kwarg[0].name == "kwargs"

    def test_function_with_keyword_only(self):
        ir = _lower("def f(*, kw1, kw2=5): pass")
        func = ir.functions[0]
        kw_params = [p for p in func.params if p.is_keyword_only]
        assert len(kw_params) == 2
        assert kw_params[0].name == "kw1"
        assert kw_params[1].name == "kw2"

    def test_function_docstring(self):
        ir = _lower('def f():\n    """My docstring"""\n    pass')
        func = ir.functions[0]
        assert func.docstring == "My docstring"

    def test_method_detection(self):
        ir = _lower("""
class C:
    def method(self):
        pass
    @classmethod
    def cmeth(cls):
        pass
    @staticmethod
    def smeth():
        pass
    @property
    def prop(self):
        return 1
""")
        cls = ir.classes[0]
        methods = [b for b in cls.body if isinstance(b, IRFunction)]
        assert len(methods) == 4
        m = methods[0]
        assert m.is_method is True
        assert m.params[0].is_self is True
        cm = methods[1]
        assert cm.is_classmethod is True
        assert cm.params[0].is_cls is True
        sm = methods[2]
        assert sm.is_staticmethod is True
        pr = methods[3]
        assert pr.is_property is True

    def test_return_statement(self):
        ir = _lower("def f(): return 42")
        func = ir.functions[0]
        assert len(func.body) == 1
        ret = func.body[0]
        assert isinstance(ret, IRReturn)
        assert isinstance(ret.value, IRConstant)
        assert ret.value.value == 42

    def test_empty_return(self):
        ir = _lower("def f(): return")
        func = ir.functions[0]
        ret = func.body[0]
        assert isinstance(ret, IRReturn)
        assert ret.value is None

    def test_multiple_returns(self):
        ir = _lower("def f(x):\n    if x:\n        return 1\n    return 2")
        func = ir.functions[0]
        # body has if + return
        assert len(func.body) == 2


# ===================================================================
# TestClassLowering
# ===================================================================

class TestClassLowering:
    """Test lowering of class definitions."""

    def test_simple_class(self):
        ir = _lower("class A: pass")
        assert len(ir.classes) == 1
        cls = ir.classes[0]
        assert cls.name == "A"
        assert cls.bases == ()

    def test_class_with_bases(self):
        ir = _lower("class B(A, C): pass")
        cls = ir.classes[0]
        assert len(cls.bases) == 2
        assert isinstance(cls.bases[0], IRName)
        assert cls.bases[0].name == "A"

    def test_class_with_methods(self):
        ir = _lower("""
class MyClass:
    def __init__(self):
        self.x = 1
    def get_x(self):
        return self.x
""")
        cls = ir.classes[0]
        methods = [b for b in cls.body if isinstance(b, IRFunction)]
        assert len(methods) == 2
        assert methods[0].name == "__init__"
        assert methods[1].name == "get_x"

    def test_class_docstring(self):
        ir = _lower('class D:\n    """Doc"""\n    pass')
        cls = ir.classes[0]
        assert cls.docstring == "Doc"

    def test_class_decorators(self):
        ir = _lower("@dataclass\nclass E: pass")
        cls = ir.classes[0]
        assert len(cls.decorators) == 1

    def test_class_enclosing_context(self):
        ir = _lower("""
class Outer:
    def method(self):
        pass
""")
        cls = ir.classes[0]
        methods = [b for b in cls.body if isinstance(b, IRFunction)]
        assert methods[0].enclosing_class == "Outer"


# ===================================================================
# TestIfElseLowering
# ===================================================================

class TestIfElseLowering:
    """Test lowering of if/elif/else statements."""

    def test_simple_if(self):
        ir = _lower("def f(x):\n    if x > 0:\n        return 1")
        func = ir.functions[0]
        if_stmt = func.body[0]
        assert isinstance(if_stmt, IRIf)
        assert isinstance(if_stmt.test, IRCompare)
        assert len(if_stmt.body) == 1
        assert len(if_stmt.orelse) == 0

    def test_if_else(self):
        ir = _lower("def f(x):\n    if x:\n        a=1\n    else:\n        a=2")
        func = ir.functions[0]
        if_stmt = func.body[0]
        assert isinstance(if_stmt, IRIf)
        assert len(if_stmt.body) == 1
        assert len(if_stmt.orelse) == 1

    def test_if_elif_else(self):
        ir = _lower("""
def f(x):
    if x > 0:
        return 1
    elif x < 0:
        return -1
    else:
        return 0
""")
        func = ir.functions[0]
        if_stmt = func.body[0]
        assert isinstance(if_stmt, IRIf)
        # The elif becomes an IRIf nested in orelse
        assert len(if_stmt.orelse) == 1
        elif_stmt = if_stmt.orelse[0]
        assert isinstance(elif_stmt, IRIf)

    def test_nested_if(self):
        ir = _lower("""
def f(x, y):
    if x:
        if y:
            return 1
""")
        func = ir.functions[0]
        outer_if = func.body[0]
        assert isinstance(outer_if, IRIf)
        inner_if = outer_if.body[0]
        assert isinstance(inner_if, IRIf)

    def test_compare_operators(self):
        ir = _lower("def f(a,b): return a == b")
        func = ir.functions[0]
        ret = func.body[0]
        assert isinstance(ret, IRReturn)
        assert isinstance(ret.value, IRCompare)
        assert ret.value.ops == (CmpOpKind.EQ,)


# ===================================================================
# TestForWhileLowering
# ===================================================================

class TestForWhileLowering:
    """Test lowering of for and while loops."""

    def test_for_loop(self):
        ir = _lower("def f():\n    for i in range(10):\n        pass")
        func = ir.functions[0]
        for_stmt = func.body[0]
        assert isinstance(for_stmt, IRFor)
        assert isinstance(for_stmt.target, IRName)
        assert for_stmt.target.name == "i"
        assert isinstance(for_stmt.iter, IRCall)

    def test_for_with_else(self):
        ir = _lower("def f():\n    for i in x:\n        pass\n    else:\n        return")
        func = ir.functions[0]
        for_stmt = func.body[0]
        assert isinstance(for_stmt, IRFor)
        assert len(for_stmt.orelse) == 1

    def test_while_loop(self):
        ir = _lower("def f():\n    while True:\n        break")
        func = ir.functions[0]
        while_stmt = func.body[0]
        assert isinstance(while_stmt, IRWhile)
        assert isinstance(while_stmt.test, IRConstant)
        assert len(while_stmt.body) == 1
        assert isinstance(while_stmt.body[0], IRBreak)

    def test_while_with_else(self):
        ir = _lower("def f():\n    while x:\n        pass\n    else:\n        pass")
        func = ir.functions[0]
        while_stmt = func.body[0]
        assert isinstance(while_stmt, IRWhile)
        assert len(while_stmt.orelse) == 1

    def test_continue_in_loop(self):
        ir = _lower("def f():\n    for i in x:\n        continue")
        func = ir.functions[0]
        for_stmt = func.body[0]
        assert isinstance(for_stmt.body[0], IRContinue)

    def test_nested_loops(self):
        ir = _lower("def f():\n    for i in a:\n        for j in b:\n            pass")
        func = ir.functions[0]
        outer = func.body[0]
        assert isinstance(outer, IRFor)
        inner = outer.body[0]
        assert isinstance(inner, IRFor)


# ===================================================================
# TestTryExceptLowering
# ===================================================================

class TestTryExceptLowering:
    """Test lowering of try/except/else/finally."""

    def test_try_except(self):
        ir = _lower("""
def f():
    try:
        x = 1
    except ValueError:
        pass
""")
        func = ir.functions[0]
        try_stmt = func.body[0]
        assert isinstance(try_stmt, IRTry)
        assert len(try_stmt.body) == 1
        assert len(try_stmt.handlers) == 1
        handler = try_stmt.handlers[0]
        assert isinstance(handler, IRExceptHandler)
        assert isinstance(handler.type, IRName)
        assert handler.type.name == "ValueError"

    def test_try_except_as(self):
        ir = _lower("""
def f():
    try:
        pass
    except Exception as e:
        print(e)
""")
        func = ir.functions[0]
        try_stmt = func.body[0]
        handler = try_stmt.handlers[0]
        assert handler.name == "e"

    def test_try_multiple_except(self):
        ir = _lower("""
def f():
    try:
        pass
    except TypeError:
        pass
    except ValueError:
        pass
""")
        func = ir.functions[0]
        try_stmt = func.body[0]
        assert len(try_stmt.handlers) == 2

    def test_try_else_finally(self):
        ir = _lower("""
def f():
    try:
        pass
    except:
        pass
    else:
        x = 1
    finally:
        y = 2
""")
        func = ir.functions[0]
        try_stmt = func.body[0]
        assert len(try_stmt.orelse) == 1
        assert len(try_stmt.finalbody) == 1

    def test_raise_statement(self):
        ir = _lower("def f(): raise ValueError('bad')")
        func = ir.functions[0]
        raise_stmt = func.body[0]
        assert isinstance(raise_stmt, IRRaise)
        assert isinstance(raise_stmt.exc, IRCall)

    def test_raise_from(self):
        ir = _lower("def f():\n    raise TypeError() from e")
        func = ir.functions[0]
        raise_stmt = func.body[0]
        assert isinstance(raise_stmt, IRRaise)
        assert raise_stmt.cause is not None

    def test_bare_raise(self):
        ir = _lower("def f():\n    raise")
        func = ir.functions[0]
        raise_stmt = func.body[0]
        assert isinstance(raise_stmt, IRRaise)
        assert raise_stmt.exc is None


# ===================================================================
# TestImportLowering
# ===================================================================

class TestImportLowering:
    """Test lowering of import statements."""

    def test_simple_import(self):
        ir = _lower("import os")
        assert len(ir.imports) == 1
        imp = ir.imports[0]
        assert isinstance(imp, IRImport)
        assert imp.names == (("os", None),)

    def test_import_as(self):
        ir = _lower("import numpy as np")
        imp = ir.imports[0]
        assert imp.names == (("numpy", "np"),)

    def test_from_import(self):
        ir = _lower("from os.path import join, exists")
        imp = ir.imports[0]
        assert isinstance(imp, IRImportFrom)
        assert imp.module == "os.path"
        assert len(imp.names) == 2
        assert imp.names[0] == ("join", None)

    def test_relative_import(self):
        ir = _lower("from ..sibling import foo")
        imp = ir.imports[0]
        assert isinstance(imp, IRImportFrom)
        assert imp.level == 2
        assert imp.module == "sibling"

    def test_multiple_imports(self):
        ir = _lower("import os\nimport sys")
        assert len(ir.imports) == 2


# ===================================================================
# TestDecoratorLowering
# ===================================================================

class TestDecoratorLowering:
    """Test lowering of decorators."""

    def test_simple_decorator(self):
        ir = _lower("@staticmethod\ndef f(): pass")
        func = ir.functions[0]
        assert len(func.decorators) == 1
        dec = func.decorators[0]
        assert isinstance(dec, IRDecorator)
        assert isinstance(dec.expr, IRName)
        assert dec.expr.name == "staticmethod"

    def test_decorator_with_args(self):
        ir = _lower("@app.route('/path')\ndef f(): pass")
        func = ir.functions[0]
        assert len(func.decorators) == 1
        dec = func.decorators[0]
        assert isinstance(dec.expr, IRCall)

    def test_multiple_decorators(self):
        ir = _lower("@a\n@b\n@c\ndef f(): pass")
        func = ir.functions[0]
        assert len(func.decorators) == 3


# ===================================================================
# TestComprehensionLowering
# ===================================================================

class TestComprehensionLowering:
    """Test lowering of list/set/dict/generator comprehensions."""

    def test_list_comprehension(self):
        ir = _lower("x = [i*2 for i in range(10)]")
        assign = ir.statements[0]
        assert isinstance(assign, IRAssign)
        comp = assign.value
        assert isinstance(comp, IRComprehension)
        assert comp.is_list is True
        assert len(comp.generators) == 1

    def test_set_comprehension(self):
        ir = _lower("x = {i for i in a}")
        assign = ir.statements[0]
        comp = assign.value
        assert isinstance(comp, IRComprehension)
        assert comp.is_set is True

    def test_dict_comprehension(self):
        ir = _lower("x = {k: v for k, v in items}")
        assign = ir.statements[0]
        comp = assign.value
        assert isinstance(comp, IRComprehension)
        assert comp.is_dict is True
        assert comp.value is not None

    def test_generator_expression(self):
        ir = _lower("x = sum(i for i in a)")
        assign = ir.statements[0]
        call = assign.value
        assert isinstance(call, IRCall)
        # The generator is an argument to sum()
        assert len(call.args) == 1
        assert isinstance(call.args[0], IRComprehension)
        assert call.args[0].is_generator is True

    def test_comprehension_with_filter(self):
        ir = _lower("x = [i for i in a if i > 0]")
        assign = ir.statements[0]
        comp = assign.value
        gen = comp.generators[0]
        assert isinstance(gen, IRComprehensionGenerator)
        assert len(gen.ifs) == 1

    def test_nested_comprehension(self):
        ir = _lower("x = [i+j for i in a for j in b]")
        assign = ir.statements[0]
        comp = assign.value
        assert len(comp.generators) == 2


# ===================================================================
# TestExpressionLowering
# ===================================================================

class TestExpressionLowering:
    """Test lowering of various expressions."""

    def test_binary_op(self):
        ir = _lower("x = 1 + 2")
        assign = ir.statements[0]
        assert isinstance(assign.value, IRBinOp)
        assert assign.value.op == BinOpKind.ADD

    def test_unary_op(self):
        ir = _lower("x = -a")
        assign = ir.statements[0]
        assert isinstance(assign.value, IRUnaryOp)
        assert assign.value.op == UnaryOpKind.USUB

    def test_bool_op(self):
        ir = _lower("x = a and b")
        assign = ir.statements[0]
        assert isinstance(assign.value, IRBoolOp)
        assert assign.value.op == BoolOpKind.AND

    def test_compare_chain(self):
        ir = _lower("x = 0 < a < 10")
        assign = ir.statements[0]
        cmp = assign.value
        assert isinstance(cmp, IRCompare)
        assert len(cmp.ops) == 2
        assert cmp.ops == (CmpOpKind.LT, CmpOpKind.LT)

    def test_subscript(self):
        ir = _lower("x = a[0]")
        assign = ir.statements[0]
        assert isinstance(assign.value, IRSubscript)

    def test_attribute_access(self):
        ir = _lower("x = obj.attr")
        assign = ir.statements[0]
        assert isinstance(assign.value, IRAttribute)
        assert assign.value.attr == "attr"

    def test_tuple_literal(self):
        ir = _lower("x = (1, 2, 3)")
        assign = ir.statements[0]
        assert isinstance(assign.value, IRTuple)
        assert len(assign.value.elts) == 3

    def test_list_literal(self):
        ir = _lower("x = [1, 2]")
        assign = ir.statements[0]
        assert isinstance(assign.value, IRList)
        assert len(assign.value.elts) == 2

    def test_dict_literal(self):
        ir = _lower("x = {'a': 1, 'b': 2}")
        assign = ir.statements[0]
        assert isinstance(assign.value, IRDict)
        assert len(assign.value.keys) == 2

    def test_set_literal(self):
        ir = _lower("x = {1, 2, 3}")
        assign = ir.statements[0]
        assert isinstance(assign.value, IRSet)
        assert len(assign.value.elts) == 3

    def test_lambda(self):
        ir = _lower("f = lambda x, y: x + y")
        assign = ir.statements[0]
        lam = assign.value
        assert isinstance(lam, IRLambda)
        assert len(lam.args) == 2

    def test_if_expr(self):
        ir = _lower("x = a if cond else b")
        assign = ir.statements[0]
        assert isinstance(assign.value, IRIfExpr)

    def test_call_with_keywords(self):
        ir = _lower("x = f(1, key=2)")
        assign = ir.statements[0]
        call = assign.value
        assert isinstance(call, IRCall)
        assert len(call.args) == 1
        assert len(call.keywords) == 1
        assert call.keywords[0] == ("key", call.keywords[0][1])

    def test_fstring(self):
        ir = _lower("x = f'hello {name}'")
        assign = ir.statements[0]
        assert isinstance(assign.value, IRFString)

    def test_yield_expression(self):
        ir = _lower("def g():\n    yield 42")
        func = ir.functions[0]
        expr_stmt = func.body[0]
        assert isinstance(expr_stmt, IRExprStmt)
        assert isinstance(expr_stmt.value, IRYield)
        assert isinstance(expr_stmt.value.value, IRConstant)

    def test_yield_from(self):
        ir = _lower("def g():\n    yield from other()")
        func = ir.functions[0]
        expr_stmt = func.body[0]
        assert isinstance(expr_stmt, IRExprStmt)
        assert isinstance(expr_stmt.value, IRYieldFrom)


# ===================================================================
# TestStatementLowering
# ===================================================================

class TestStatementLowering:
    """Test lowering of various statements."""

    def test_assignment(self):
        ir = _lower("x = 5")
        stmt = ir.statements[0]
        assert isinstance(stmt, IRAssign)
        assert isinstance(stmt.targets[0], IRName)
        assert stmt.targets[0].name == "x"

    def test_annotated_assignment(self):
        ir = _lower("x: int = 5")
        stmt = ir.statements[0]
        assert isinstance(stmt, IRAssign)
        assert stmt.type_annotation is not None
        assert isinstance(stmt.type_annotation, IRName)

    def test_aug_assign(self):
        ir = _lower("def f():\n    x += 1")
        func = ir.functions[0]
        stmt = func.body[0]
        assert isinstance(stmt, IRAugAssign)
        assert stmt.op == BinOpKind.ADD

    def test_delete_statement(self):
        ir = _lower("del x")
        stmt = ir.statements[0]
        assert isinstance(stmt, IRDelete)

    def test_assert_statement(self):
        ir = _lower("def f():\n    assert x > 0, 'bad'")
        func = ir.functions[0]
        stmt = func.body[0]
        assert isinstance(stmt, IRAssert)
        assert isinstance(stmt.test, IRCompare)
        assert stmt.msg is not None

    def test_global_statement(self):
        ir = _lower("def f():\n    global x, y")
        func = ir.functions[0]
        stmt = func.body[0]
        assert isinstance(stmt, IRGlobal)
        assert stmt.names == ("x", "y")

    def test_nonlocal_statement(self):
        ir = _lower("def f():\n    def g():\n        nonlocal x")
        # nonlocal is inside nested function, which becomes an assignment
        func = ir.functions[0]
        # The nested function is lowered as an IRAssign placeholder
        assert len(func.body) >= 1

    def test_pass_statement(self):
        ir = _lower("def f(): pass")
        func = ir.functions[0]
        assert isinstance(func.body[0], IRPass)

    def test_with_statement(self):
        ir = _lower("def f():\n    with open('x') as fp:\n        pass")
        func = ir.functions[0]
        with_stmt = func.body[0]
        assert isinstance(with_stmt, IRWith)
        assert len(with_stmt.items) == 1
        assert with_stmt.items[0][1] is not None  # optional_var 'fp'

    def test_expr_statement(self):
        ir = _lower("def f():\n    print('hello')")
        func = ir.functions[0]
        stmt = func.body[0]
        assert isinstance(stmt, IRExprStmt)
        assert isinstance(stmt.value, IRCall)


# ===================================================================
# TestModuleLowering
# ===================================================================

class TestModuleLowering:
    """Test module-level lowering features."""

    def test_module_name(self):
        ir = _lower("x = 1")
        assert ir.name == "test_mod"
        assert ir.filename == "test.py"

    def test_module_docstring(self):
        ir = _lower('"""Module doc"""\nx = 1')
        assert ir.docstring == "Module doc"

    def test_module_no_docstring(self):
        ir = _lower("x = 1")
        assert ir.docstring is None

    def test_module_span(self):
        ir = _lower("x = 1")
        assert ir.span.file == "test.py"
        assert ir.span.start_line == 1

    def test_mixed_module(self):
        ir = _lower("""
import os

x = 1

def f():
    pass

class C:
    pass
""")
        assert len(ir.functions) == 1
        assert len(ir.classes) == 1
        assert len(ir.imports) == 1
        assert any(isinstance(s, IRAssign) for s in ir.statements)

    def test_constant_kinds(self):
        ir = _lower("a = 1\nb = 'hi'\nc = 3.14\nd = True\ne = None\nf = b'bytes'")
        stmts = ir.statements
        assert isinstance(stmts[0], IRAssign) and stmts[0].value.kind == "int"
        assert isinstance(stmts[1], IRAssign) and stmts[1].value.kind == "str"
        assert isinstance(stmts[2], IRAssign) and stmts[2].value.kind == "float"
        assert isinstance(stmts[3], IRAssign) and stmts[3].value.kind == "bool"
        assert isinstance(stmts[4], IRAssign) and stmts[4].value.kind == "None"
        assert isinstance(stmts[5], IRAssign) and stmts[5].value.kind == "bytes"

    def test_source_spans_present(self):
        ir = _lower("def f(x):\n    return x + 1")
        func = ir.functions[0]
        assert func.span.file == "test.py"
        assert func.span.start_line >= 1

    def test_slice_expression(self):
        ir = _lower("x = a[1:10:2]")
        assign = ir.statements[0]
        sub = assign.value
        assert isinstance(sub, IRSubscript)
        assert isinstance(sub.slice, IRSlice)
        assert isinstance(sub.slice.lower, IRConstant)
        assert sub.slice.lower.value == 1
