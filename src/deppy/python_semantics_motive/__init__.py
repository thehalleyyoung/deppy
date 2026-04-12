"""python_semantics_motive — Interpretation of Python's semantics in the motive framework.

This package provides the formal interpretation of every Python builtin
type, function, method, operator, and syntactic construct as typed operations
in the computational motive framework.

Each module exports tables mapping concrete Python constructs to their
abstract algebraic representations: (op_name, input_sorts, output_sort,
refinements, effect).

Usage:
    from deppy.python_semantics_motive import PythonSemantics

    sem = PythonSemantics()
    sort = sem.infer_sort(ast_node, var_sorts, func_name)
"""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    import ast
    from typing import Dict, Optional
    from deppy.motive.sorts import Sort


class PythonSemantics:
    """Unified interface to Python semantic interpretation.

    Delegates to the sub-modules for specific constructs.
    """

    def __init__(self) -> None:
        from deppy.python_semantics_motive.builtin_types import (
            BUILTIN_NAME_SORTS, METHOD_RESULT_SORTS,
        )
        from deppy.python_semantics_motive.builtin_funcs import (
            BUILTIN_FUNC_SORTS,
        )
        self._name_sorts = BUILTIN_NAME_SORTS
        self._method_sorts = METHOD_RESULT_SORTS
        self._func_sorts = BUILTIN_FUNC_SORTS

    def infer_sort(self, node: "ast.expr",
                   var_sorts: "Dict[str, Sort]",
                   func_name: str) -> "Optional[Sort]":
        """Infer the sort of an expression using full Python semantics.

        Returns None to fall back to the extractor's built-in inference.
        """
        return None  # The extractor handles inference, we supply tables

    def infer_param_sort(self, arg: "ast.arg",
                         func: "ast.FunctionDef") -> "Optional[Sort]":
        """Infer parameter sort from annotation."""
        return None  # Fall back to extractor


__all__ = ['PythonSemantics']
