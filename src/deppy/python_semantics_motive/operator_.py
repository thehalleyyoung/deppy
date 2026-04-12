"""Interpretation of Python operator module in the motive framework."""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

OPERATOR_OPS = {
    # Comparison
    'lt': ('Compare.lt', (Sort.TOP, Sort.TOP), Sort.BOOL, frozenset(), Effect.PURE),
    'le': ('Compare.le', (Sort.TOP, Sort.TOP), Sort.BOOL, frozenset(), Effect.PURE),
    'eq': ('Compare.eq', (Sort.TOP, Sort.TOP), Sort.BOOL,
           frozenset({Refinement.COMMUTATIVE}), Effect.PURE),
    'ne': ('Compare.ne', (Sort.TOP, Sort.TOP), Sort.BOOL,
           frozenset({Refinement.COMMUTATIVE}), Effect.PURE),
    'ge': ('Compare.ge', (Sort.TOP, Sort.TOP), Sort.BOOL, frozenset(), Effect.PURE),
    'gt': ('Compare.gt', (Sort.TOP, Sort.TOP), Sort.BOOL, frozenset(), Effect.PURE),

    # Logical
    'not_': ('Logic.not', (Sort.BOOL,), Sort.BOOL, frozenset(), Effect.PURE),
    'truth': ('Cast.to_bool', (Sort.TOP,), Sort.BOOL, frozenset(), Effect.PURE),
    'is_': ('Compare.is', (Sort.TOP, Sort.TOP), Sort.BOOL, frozenset(), Effect.PURE),
    'is_not': ('Compare.is_not', (Sort.TOP, Sort.TOP), Sort.BOOL, frozenset(), Effect.PURE),

    # Arithmetic
    'abs': ('Num.abs', (Sort.NUM,), Sort.NUM, frozenset({Refinement.IDEMPOTENT}), Effect.PURE),
    'add': ('Arith.add', (Sort.TOP, Sort.TOP), Sort.TOP,
            frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'and_': ('Bitwise.and', (Sort.NUM, Sort.NUM), Sort.NUM,
             frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'floordiv': ('Arith.floordiv', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'index': ('Cast.to_num', (Sort.TOP,), Sort.NUM, frozenset(), Effect.PURE),
    'inv': ('Bitwise.invert', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'invert': ('Bitwise.invert', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'lshift': ('Bitwise.lshift', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'mod': ('Arith.mod', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'mul': ('Arith.mul', (Sort.TOP, Sort.TOP), Sort.TOP,
            frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'matmul': ('Arith.matmul', (Sort.TOP, Sort.TOP), Sort.TOP,
               frozenset({Refinement.ASSOCIATIVE}), Effect.PURE),
    'neg': ('Unary.neg', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'or_': ('Bitwise.or', (Sort.NUM, Sort.NUM), Sort.NUM,
            frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'pos': ('Unary.pos', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'pow': ('Arith.pow', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'rshift': ('Bitwise.rshift', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'sub': ('Arith.sub', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'truediv': ('Arith.div', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'xor': ('Bitwise.xor', (Sort.NUM, Sort.NUM), Sort.NUM,
            frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),

    # Sequence operations
    'concat': ('Seq.concat', (Sort.SEQ, Sort.SEQ), Sort.SEQ,
               frozenset({Refinement.ASSOCIATIVE}), Effect.PURE),
    'contains': ('Container.contains', (Sort.TOP, Sort.TOP), Sort.BOOL, frozenset(), Effect.PURE),
    'countOf': ('Seq.count', (Sort.SEQ, Sort.TOP), Sort.NUM, frozenset(), Effect.PURE),
    'delitem': ('Container.del', (Sort.TOP, Sort.TOP), Sort.NONE, frozenset(), Effect.MUTATE),
    'getitem': ('Container.index', (Sort.TOP, Sort.TOP), Sort.TOP, frozenset(), Effect.PURE),
    'indexOf': ('Seq.index', (Sort.SEQ, Sort.TOP), Sort.NUM, frozenset(), Effect.PURE),
    'setitem': ('Container.store', (Sort.TOP, Sort.TOP, Sort.TOP), Sort.NONE, frozenset(), Effect.MUTATE),
    'length_hint': ('Measure.length', (Sort.TOP,), Sort.NUM, frozenset(), Effect.PURE),

    # Attribute access
    'attrgetter': ('Func.attrgetter', (Sort.STR,), Sort.FUNC, frozenset(), Effect.PURE),
    'itemgetter': ('Func.itemgetter', (Sort.TOP,), Sort.FUNC, frozenset(), Effect.PURE),
    'methodcaller': ('Func.methodcaller', (Sort.STR,), Sort.FUNC, frozenset(), Effect.PURE),

    # In-place operations
    'iadd': ('Accum.add', (Sort.TOP, Sort.TOP), Sort.TOP, frozenset(), Effect.MUTATE),
    'iand': ('Accum.bitand', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.MUTATE),
    'iconcat': ('Accum.concat', (Sort.SEQ, Sort.SEQ), Sort.SEQ, frozenset(), Effect.MUTATE),
    'ifloordiv': ('Accum.floordiv', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.MUTATE),
    'ilshift': ('Accum.lshift', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.MUTATE),
    'imod': ('Accum.mod', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.MUTATE),
    'imul': ('Accum.mul', (Sort.TOP, Sort.TOP), Sort.TOP, frozenset(), Effect.MUTATE),
    'imatmul': ('Accum.matmul', (Sort.TOP, Sort.TOP), Sort.TOP, frozenset(), Effect.MUTATE),
    'ior': ('Accum.bitor', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.MUTATE),
    'ipow': ('Accum.pow', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.MUTATE),
    'irshift': ('Accum.rshift', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.MUTATE),
    'isub': ('Accum.sub', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.MUTATE),
    'itruediv': ('Accum.div', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.MUTATE),
    'ixor': ('Accum.bitxor', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.MUTATE),
}
