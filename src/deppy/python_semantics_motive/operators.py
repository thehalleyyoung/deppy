"""Interpretation of Python operators in the motive framework.

Every Python binary operator, unary operator, comparison operator, and
augmented assignment operator is mapped to a TypedOp specification.
"""

from __future__ import annotations

import ast
from typing import FrozenSet, Tuple

from deppy.motive.sorts import Sort
from deppy.motive.operations import Refinement


def binop_to_typed_op(
        op: ast.operator,
        left_sort: Sort,
        right_sort: Sort,
) -> Tuple[str, FrozenSet[Refinement]]:
    """Return (op_name, refinements) for a binary operator."""
    t = type(op).__name__

    _BINOP_TABLE = {
        'Add': ('Arith.add', frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE})),
        'Sub': ('Arith.sub', frozenset()),
        'Mult': ('Arith.mul', frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE})),
        'Div': ('Arith.div', frozenset()),
        'FloorDiv': ('Arith.floordiv', frozenset()),
        'Mod': ('Arith.mod', frozenset()),
        'Pow': ('Arith.pow', frozenset()),
        'LShift': ('Bitwise.lshift', frozenset()),
        'RShift': ('Bitwise.rshift', frozenset()),
        'BitOr': ('Bitwise.or', frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT})),
        'BitXor': ('Bitwise.xor', frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE})),
        'BitAnd': ('Bitwise.and', frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT})),
        'MatMult': ('Arith.matmul', frozenset({Refinement.ASSOCIATIVE})),
    }

    base = _BINOP_TABLE.get(t, (f'Arith.{t.lower()}', frozenset()))
    name, refs = base

    # Polymorphic overloading: + and * on sequences/strings
    if t == 'Add':
        if left_sort == Sort.STR or right_sort == Sort.STR:
            return ('Str.concat', frozenset({Refinement.ASSOCIATIVE}))
        if left_sort == Sort.SEQ or right_sort == Sort.SEQ:
            return ('Seq.concat', frozenset({Refinement.ASSOCIATIVE}))
    if t == 'Mult':
        if left_sort == Sort.STR or right_sort == Sort.STR:
            return ('Str.repeat', frozenset())
        if left_sort == Sort.SEQ or right_sort == Sort.SEQ:
            return ('Seq.repeat', frozenset())

    return (name, refs)


def cmpop_to_name(op: ast.cmpop) -> str:
    """Return the abstract operation name for a comparison operator."""
    _CMP_TABLE = {
        'Eq': 'Compare.eq',
        'NotEq': 'Compare.ne',
        'Lt': 'Compare.lt',
        'LtE': 'Compare.le',
        'Gt': 'Compare.gt',
        'GtE': 'Compare.ge',
        'Is': 'Compare.is',
        'IsNot': 'Compare.is_not',
        'In': 'Container.contains',
        'NotIn': 'Container.not_contains',
    }
    return _CMP_TABLE.get(type(op).__name__, f'Compare.{type(op).__name__.lower()}')


def unaryop_to_name(op: ast.unaryop) -> str:
    """Return the abstract operation name for a unary operator."""
    _UNARY_TABLE = {
        'UAdd': 'Unary.pos',
        'USub': 'Unary.neg',
        'Not': 'Logic.not',
        'Invert': 'Bitwise.invert',
    }
    return _UNARY_TABLE.get(type(op).__name__, f'Unary.{type(op).__name__.lower()}')


def augop_to_name(op: ast.operator) -> str:
    """Return the abstract operation name for an augmented assignment op."""
    _AUG_TABLE = {
        'Add': 'Accum.add',
        'Sub': 'Accum.sub',
        'Mult': 'Accum.mul',
        'Div': 'Accum.div',
        'FloorDiv': 'Accum.floordiv',
        'Mod': 'Accum.mod',
        'Pow': 'Accum.pow',
        'LShift': 'Accum.lshift',
        'RShift': 'Accum.rshift',
        'BitOr': 'Accum.bitor',
        'BitXor': 'Accum.bitxor',
        'BitAnd': 'Accum.bitand',
        'MatMult': 'Accum.matmul',
    }
    return _AUG_TABLE.get(type(op).__name__, f'Accum.{type(op).__name__.lower()}')
