"""deppy.hybrid.research — self-verifying research framework.

This package turns deppy's own correctness claims into hybrid types that the
system can verify about itself.  The central module is
:pymod:`verified_foundations`, which houses the theorem registry, self-
verifier, and the formal correspondence between algebraic geometry, dependent
type theory, and controlled-oracle theory.

Lazy-loaded public API
~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

    from deppy.hybrid.research import (
        ResearchClaim,
        TheoremRegistry,
        SelfVerifier,
        FormalCorrespondence,
        AlgebraicGeometryConnection,
        ControlledOracleTheory,
        ResearchPaperGenerator,
        BootstrapVerification,
    )
"""

from __future__ import annotations

__all__ = [
    "ResearchClaim",
    "TheoremRegistry",
    "SelfVerifier",
    "FormalCorrespondence",
    "AlgebraicGeometryConnection",
    "ControlledOracleTheory",
    "ResearchPaperGenerator",
    "BootstrapVerification",
]

_IMPORTS = {
    "ResearchClaim": "deppy.hybrid.research.verified_foundations",
    "TheoremRegistry": "deppy.hybrid.research.verified_foundations",
    "SelfVerifier": "deppy.hybrid.research.verified_foundations",
    "FormalCorrespondence": "deppy.hybrid.research.verified_foundations",
    "AlgebraicGeometryConnection": "deppy.hybrid.research.verified_foundations",
    "ControlledOracleTheory": "deppy.hybrid.research.verified_foundations",
    "ResearchPaperGenerator": "deppy.hybrid.research.verified_foundations",
    "BootstrapVerification": "deppy.hybrid.research.verified_foundations",
}


def __getattr__(name: str):
    if name in _IMPORTS:
        import importlib

        module = importlib.import_module(_IMPORTS[name])
        return getattr(module, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
