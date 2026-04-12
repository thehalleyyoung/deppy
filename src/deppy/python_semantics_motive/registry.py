"""Central registry for Python semantic operations.

Aggregates all operation tables from sub-modules into a single
lookup registry. Used for dynamic resolution when the specific
module/type context is unknown.
"""

from __future__ import annotations

from typing import Dict, FrozenSet, Optional, Tuple

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

# Import all operation tables
from deppy.python_semantics_motive.builtin_types import ALL_METHOD_OPS
from deppy.python_semantics_motive.builtin_funcs import _FUNC_OPS
from deppy.python_semantics_motive.operators import (
    binop_to_typed_op, cmpop_to_name, unaryop_to_name, augop_to_name,
)
from deppy.python_semantics_motive.control_flow import CONTROL_FLOW_OPS
from deppy.python_semantics_motive.comprehensions import COMPREHENSION_OPS
from deppy.python_semantics_motive.collections_ import ALL_COLLECTIONS_OPS
from deppy.python_semantics_motive.itertools_ import ITERTOOLS_OPS
from deppy.python_semantics_motive.functools_ import FUNCTOOLS_OPS
from deppy.python_semantics_motive.math_ import MATH_OPS
from deppy.python_semantics_motive.operator_ import OPERATOR_OPS
from deppy.python_semantics_motive.heapq_ import HEAPQ_OPS
from deppy.python_semantics_motive.bisect_ import BISECT_OPS
from deppy.python_semantics_motive.copy_ import COPY_OPS
from deppy.python_semantics_motive.re_ import RE_OPS
from deppy.python_semantics_motive.io_ import IO_OPS


# ── Build unified registry ──────────────────────────────────────

# Method name → (op_name, result_sort, refinements, effect)
METHOD_REGISTRY: Dict[str, Tuple[str, Sort, FrozenSet[Refinement], Effect]] = {}
METHOD_REGISTRY.update(ALL_METHOD_OPS)
METHOD_REGISTRY.update(ALL_COLLECTIONS_OPS)

# Function name → (op_name, refinements, effect)
FUNCTION_REGISTRY: Dict[str, Tuple[str, FrozenSet[Refinement], Effect]] = dict(_FUNC_OPS)

# Module-specific function tables
MODULE_REGISTRIES = {
    'math': MATH_OPS,
    'operator': OPERATOR_OPS,
    'heapq': HEAPQ_OPS,
    'bisect': BISECT_OPS,
    'copy': COPY_OPS,
    're': RE_OPS,
    'io': IO_OPS,
    'itertools': ITERTOOLS_OPS,
    'functools': FUNCTOOLS_OPS,
}


def lookup_function(name: str, module: Optional[str] = None
                    ) -> Optional[Tuple[str, FrozenSet[Refinement], Effect]]:
    """Look up a function's TypedOp specification.

    Args:
        name: Function name
        module: Optional module name (e.g., 'math', 'heapq')

    Returns:
        (op_name, refinements, effect) or None
    """
    if module and module in MODULE_REGISTRIES:
        table = MODULE_REGISTRIES[module]
        if name in table:
            entry = table[name]
            return (entry[0], entry[3], entry[4]) if len(entry) == 5 else (entry[0], frozenset(), Effect.PURE)
    if name in FUNCTION_REGISTRY:
        return FUNCTION_REGISTRY[name]
    return None


def lookup_method(name: str) -> Optional[Tuple[str, Sort, FrozenSet[Refinement], Effect]]:
    """Look up a method's TypedOp specification.

    Returns:
        (op_name, result_sort, refinements, effect) or None
    """
    return METHOD_REGISTRY.get(name)
