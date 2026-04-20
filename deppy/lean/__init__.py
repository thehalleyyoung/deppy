"""Deppy Lean 4 integration — AST rendering, spec translation, compilation, and utilities."""

from __future__ import annotations

try:
    from deppy.lean.renderer import render_expr, render_decl, render_file
except ImportError:
    pass

from deppy.lean.spec_translator import (  # noqa: F401
    LeanTheorem,
    LeanFunctionSig,
    translate_python_type,
    translate_guarantee,
    translate_requires,
    translate_function_sig,
)

from deppy.lean.compiler import compile_to_lean, LeanCertificate  # noqa: F401
