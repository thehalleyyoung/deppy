"""SynHoPy Lean 4 integration — AST rendering, spec translation, compilation, and utilities."""

from __future__ import annotations

try:
    from synhopy.lean.renderer import render_expr, render_decl, render_file
except ImportError:
    pass

from synhopy.lean.spec_translator import (  # noqa: F401
    LeanTheorem,
    LeanFunctionSig,
    translate_python_type,
    translate_guarantee,
    translate_requires,
    translate_function_sig,
)

from synhopy.lean.compiler import compile_to_lean, LeanCertificate  # noqa: F401
