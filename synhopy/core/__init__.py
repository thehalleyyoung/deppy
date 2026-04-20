"""SynHoPy core — type system, proof kernel, Z3 bridge."""
from __future__ import annotations

from synhopy.core.types import (
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
from synhopy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Sym, Trans, Cong, Cut, Assume, Z3Proof,
    NatInduction, ListInduction, Cases, DuckPath,
    EffectWitness, AxiomInvocation, Ext, Unfold, Rewrite,
    Structural, TransportProof, Patch, Fiber,
    PathComp, Ap, FunExt, CechGlue, Univalence,
)

try:
    from synhopy.core.z3_bridge import (
        Z3Context, PredicateTranslator, RefinementChecker, Z3Prover,
    )
except ImportError:
    pass
from synhopy.core.z3_bridge import (
    Z3Context, PredicateTranslator, RefinementChecker,
    Z3Prover, Z3ProofResult, ArithmeticEncoder,
    quick_check, quick_prove, extract_free_vars,
    _HAS_Z3,
)

# ── Lazy convenience re-exports (avoid circular imports) ──
univalence = Univalence  # alias: the axiom constructor


def __getattr__(name):
    """Lazy imports for ``from synhopy.core import funext/transport/...``."""
    _lazy = {
        "funext": ("synhopy.proofs.sugar", "funext"),
        "transport": ("synhopy.proofs.sugar", "transport_proof"),
        "path": ("synhopy.proofs.sugar", "path"),
        "path_chain": ("synhopy.proofs.sugar", "path_chain"),
        "path_equivalent": ("synhopy.proofs.sugar", "path_equivalent"),
        "Equiv": ("synhopy.hott", "Equiv"),
        "Fibration": ("synhopy.hott", "Fibration"),
        "TotalSpace": ("synhopy.hott", "TotalSpace"),
        "Section": ("synhopy.hott", "Section"),
    }
    if name in _lazy:
        mod_name, attr = _lazy[name]
        import importlib
        mod = importlib.import_module(mod_name)
        return getattr(mod, attr)
    raise AttributeError(f"module 'synhopy.core' has no attribute {name!r}")
