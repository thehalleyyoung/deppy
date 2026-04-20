"""
synhopy.homotopy — High-level homotopy proof interface.

Re-exports homotopy primitives for ``from synhopy.homotopy import path, transport``.
"""
from __future__ import annotations

from synhopy.proofs.sugar import (         # noqa: F401
    path, path_chain, funext,
    transport_proof as transport,
    transport_from,
    path_equivalent,
    by_transport, by_cech_proof, by_fiber_proof,
)
from synhopy.core.kernel import (          # noqa: F401
    PathComp, Ap, FunExt, CechGlue, Univalence,
    TransportProof, Fiber, Patch, DuckPath,
    Refl, Sym, Trans, Cong,
)
from synhopy.core.types import PathType    # noqa: F401
