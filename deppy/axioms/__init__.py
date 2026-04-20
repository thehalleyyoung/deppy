"""Deppy axioms — library axiom declarations."""
from __future__ import annotations

from deppy.axioms.library_axioms import (  # noqa: F401
    LibraryAxiom,
    AxiomRegistry,
    AxiomTester,
    TestResult,
    TestVerdict,
    SympyAxioms,
    NumpyAxioms,
    TorchAxioms,
    BuiltinAxioms,
    default_registry,
    library,
    axiom,
)
