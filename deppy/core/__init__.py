"""Deppy core — type system, proof kernel, Z3 bridge."""
from __future__ import annotations

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyNoneType, PyListType, PyDictType, PyCallableType,
    PiType, SigmaType, PathType, RefinementType, UnionType,
    UniverseType, ProtocolType, OptionalType, IntervalType,
    Var, Literal, Lam, App, Pair, Fst, Snd,
    PathAbs, PathApp, Transport, Comp, LetIn, IfThenElse,
    PyCall, GetAttr, GetItem,
    arrow,
)
from deppy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Sym, Trans, Cong, Cut, Assume, Z3Proof,
    NatInduction, ListInduction, Cases, DuckPath,
    EffectWitness, AxiomInvocation, Ext, Unfold, Rewrite,
    Structural, TransportProof, Patch, Fiber,
    PathComp, Ap, FunExt, CechGlue, Univalence,
)

try:
    from deppy.core.z3_bridge import (
        Z3Context, PredicateTranslator, RefinementChecker, Z3Prover,
    )
except ImportError:
    pass
from deppy.core.z3_bridge import (
    Z3Context, PredicateTranslator, RefinementChecker,
    Z3Prover, Z3ProofResult, ArithmeticEncoder,
    quick_check, quick_prove, extract_free_vars,
    _HAS_Z3,
)

# ── Lazy convenience re-exports (avoid circular imports) ──
univalence = Univalence  # alias: the axiom constructor


def __getattr__(name):
    """Lazy imports for ``from deppy.core import funext/transport/...``."""
    _lazy = {
        "funext": ("deppy.proofs.sugar", "funext"),
        "transport": ("deppy.proofs.sugar", "transport_proof"),
        "path": ("deppy.proofs.sugar", "path"),
        "path_chain": ("deppy.proofs.sugar", "path_chain"),
        "path_equivalent": ("deppy.proofs.sugar", "path_equivalent"),
        "Equiv": ("deppy.hott", "Equiv"),
        "Fibration": ("deppy.hott", "Fibration"),
        "TotalSpace": ("deppy.hott", "TotalSpace"),
        "Section": ("deppy.hott", "Section"),
    }
    if name in _lazy:
        mod_name, attr = _lazy[name]
        import importlib
        mod = importlib.import_module(mod_name)
        return getattr(mod, attr)
    raise AttributeError(f"module 'deppy.core' has no attribute {name!r}")
