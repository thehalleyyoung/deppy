"""Interpretation of Python syntax constructs in the motive framework.

This module covers the structural syntax of Python — how expressions
and statements combine. The semantic content is in other modules;
this module captures the *syntactic* form.
"""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

# ── Expression syntax operations ─────────────────────────────────
# These capture the *form* of expressions, not their semantic content.

EXPRESSION_SYNTAX_OPS = {
    # Literals
    'int_literal': ('Literal.num', (), Sort.NUM, frozenset(), Effect.PURE),
    'float_literal': ('Literal.num', (), Sort.NUM, frozenset(), Effect.PURE),
    'complex_literal': ('Literal.num', (), Sort.NUM, frozenset(), Effect.PURE),
    'str_literal': ('Literal.str', (), Sort.STR, frozenset(), Effect.PURE),
    'bytes_literal': ('Literal.str', (), Sort.STR, frozenset(), Effect.PURE),
    'bool_literal': ('Literal.bool', (), Sort.BOOL, frozenset(), Effect.PURE),
    'none_literal': ('Literal.none', (), Sort.NONE, frozenset(), Effect.PURE),
    'ellipsis_literal': ('Literal.ellipsis', (), Sort.TOP, frozenset(), Effect.PURE),

    # Collection displays
    'list_display': ('Display.list', (), Sort.SEQ, frozenset(), Effect.ALLOCATE),
    'tuple_display': ('Display.tuple', (), Sort.SEQ, frozenset(), Effect.ALLOCATE),
    'dict_display': ('Display.dict', (), Sort.MAP, frozenset(), Effect.ALLOCATE),
    'set_display': ('Display.set', (), Sort.SET, frozenset(), Effect.ALLOCATE),

    # Name access
    'name_load': ('Name.load', (), Sort.TOP, frozenset(), Effect.PURE),
    'name_store': ('Name.store', (Sort.TOP,), Sort.NONE, frozenset(), Effect.PURE),
    'name_del': ('Name.del', (), Sort.NONE, frozenset(), Effect.MUTATE),

    # Attribute access
    'attr_load': ('Attr.load', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),
    'attr_store': ('Attr.store', (Sort.TOP, Sort.TOP), Sort.NONE, frozenset(), Effect.MUTATE),
    'attr_del': ('Attr.del', (Sort.TOP,), Sort.NONE, frozenset(), Effect.MUTATE),

    # Subscript access
    'subscript_load': ('Container.index', (Sort.TOP, Sort.TOP), Sort.TOP, frozenset(), Effect.PURE),
    'subscript_store': ('Container.store', (Sort.TOP, Sort.TOP, Sort.TOP), Sort.NONE, frozenset(), Effect.MUTATE),
    'subscript_del': ('Container.del', (Sort.TOP, Sort.TOP), Sort.NONE, frozenset(), Effect.MUTATE),
    'slice': ('Container.slice', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),

    # Starred expressions
    'starred': ('Destructure.splat', (Sort.SEQ,), Sort.SEQ, frozenset(), Effect.PURE),

    # F-strings
    'fstring': ('Str.format', (), Sort.STR, frozenset(), Effect.PURE),
    'fstring_value': ('Cast.to_str', (Sort.TOP,), Sort.STR, frozenset(), Effect.PURE),
    'fstring_conversion': ('Cast.to_str', (Sort.TOP,), Sort.STR, frozenset(), Effect.PURE),

    # Walrus operator
    'named_expr': ('Assign.walrus', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),
}

# ── Statement syntax operations ──────────────────────────────────

STATEMENT_SYNTAX_OPS = {
    # Simple statements
    'expression_stmt': ('Stmt.expr', (Sort.TOP,), Sort.NONE, frozenset(), Effect.PURE),
    'assert_stmt': ('Assert.check', (Sort.BOOL,), Sort.NONE, frozenset(), Effect.PURE),
    'pass_stmt': ('Noop', (), Sort.NONE, frozenset(), Effect.PURE),
    'del_stmt': ('Mem.free', (Sort.TOP,), Sort.NONE, frozenset(), Effect.MUTATE),

    # Return/yield/raise
    'return_stmt': ('Func.return', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),
    'yield_stmt': ('Func.yield', (Sort.TOP,), Sort.TOP, frozenset(), Effect.ITERATE),
    'yield_from_stmt': ('Func.yield_from', (Sort.ITER,), Sort.TOP, frozenset(), Effect.ITERATE),
    'raise_stmt': ('Exception.raise', (Sort.TOP,), Sort.NONE, frozenset(), Effect.IO),

    # Import
    'import_stmt': ('Module.import', (), Sort.TOP, frozenset(), Effect.IO),
    'from_import_stmt': ('Module.from_import', (), Sort.TOP, frozenset(), Effect.IO),

    # Global/nonlocal
    'global_stmt': ('Scope.global', (), Sort.NONE, frozenset(), Effect.PURE),
    'nonlocal_stmt': ('Scope.nonlocal', (), Sort.NONE, frozenset(), Effect.PURE),

    # Type alias (Python 3.12+)
    'type_alias': ('Type.alias', (), Sort.FUNC, frozenset(), Effect.PURE),
}

# ── Decorator syntax ─────────────────────────────────────────────

DECORATOR_OPS = {
    'decorator': ('Func.decorate', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'property': ('Func.property', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'staticmethod': ('Func.staticmethod', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'classmethod': ('Func.classmethod', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'abstractmethod': ('Func.abstractmethod', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'dataclass': ('Type.dataclass', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
    'total_ordering': ('Type.total_ordering', (Sort.FUNC,), Sort.FUNC, frozenset(), Effect.PURE),
}

# ── Argument syntax ──────────────────────────────────────────────

ARGUMENT_OPS = {
    'positional_arg': ('Arg.positional', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),
    'keyword_arg': ('Arg.keyword', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),
    'star_arg': ('Arg.star', (Sort.SEQ,), Sort.SEQ, frozenset(), Effect.PURE),
    'double_star_arg': ('Arg.double_star', (Sort.MAP,), Sort.MAP, frozenset(), Effect.PURE),
    'default_value': ('Arg.default', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),
    'annotation': ('Arg.annotation', (), Sort.TOP, frozenset(), Effect.PURE),
}
