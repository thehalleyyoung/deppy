"""Interpretation of Python method calls in the motive framework.

Maps method names on known container/string/numeric types to their
abstract TypedOp specifications.
"""

from __future__ import annotations

from typing import FrozenSet, Tuple

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement
from deppy.python_semantics_motive.builtin_types import (
    STR_OPS, LIST_OPS, DICT_OPS, SET_OPS, DEQUE_OPS, COUNTER_OPS,
    ALL_METHOD_OPS, INT_OPS, FLOAT_OPS,
)


# Sort-specific method tables for disambiguation
_SORT_METHOD_TABLES = {
    Sort.STR: STR_OPS,
    Sort.SEQ: {**LIST_OPS, **DEQUE_OPS},
    Sort.MAP: {**DICT_OPS, **COUNTER_OPS},
    Sort.SET: SET_OPS,
    Sort.NUM: {**INT_OPS, **FLOAT_OPS},
}


def method_to_typed_op(
        method_name: str,
        obj_sort: Sort,
        arg_sorts: Tuple[Sort, ...],
) -> Tuple[str, FrozenSet[Refinement], Effect]:
    """Return (op_name, refinements, effect) for a method call.

    First checks the sort-specific table, then falls back to the
    unified ALL_METHOD_OPS table.
    """
    # Check sort-specific table first
    sort_table = _SORT_METHOD_TABLES.get(obj_sort)
    if sort_table and method_name in sort_table:
        op_name, _result_sort, refs, effect = sort_table[method_name]
        return (op_name, refs, effect)

    # Fall back to unified table
    if method_name in ALL_METHOD_OPS:
        op_name, _result_sort, refs, effect = ALL_METHOD_OPS[method_name]
        return (op_name, refs, effect)

    # Unknown method — use generic name
    return (f'Method.{method_name}', frozenset(), Effect.PURE)
