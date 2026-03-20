"""deppy.hybrid — Hybrid Dependent Types for Trustworthy Software.

Extends deppy's sheaf-descent semantic typing with:
- 5-layer product site (INTENT × STRUCTURAL × SEMANTIC × PROOF × CODE)
- LLM-as-controlled-oracle with trust monad T_O
- Anti-hallucination type checking
- Python→Lean translation with proof obligations
- Type expansion for large-scale code generation from NL specs

Builds on top of the existing deppy infrastructure:
- deppy.core (presheaves, sites, sections, morphisms)
- deppy.types (refinement, dependent, identity types)
- deppy.solver (Z3, fragment dispatcher)
- deppy.kernel (fixed-point engine, trust classifier)
- deppy.pipeline (analysis pipeline)
- deppy.contracts (requires, ensures, invariant)

Usage::

    from deppy.hybrid import (
        # Extensions of existing types
        HybridLayer, HybridTrustLevel,
        HybridPiType, HybridSigmaType, HybridRefinementType,
        HybridPresheaf, HybridPipeline,

        # New capabilities
        TypeExpander, CodeGenPlan, LargeScaleGenerator,
        HallucinationChecker, IntentBridge,

        # Quick API
        hybrid_check, hybrid_analyze, hybrid_expand,
    )

    # Check existing code (zero-change entry point)
    result = hybrid_check("myfile.py")

    # Expand a spec into a typed code generation plan
    plan = hybrid_expand("write me a trading app with risk management")
"""
from __future__ import annotations

# --- Layer and Trust (always available) ---
# These are defined inline to avoid circular imports

import enum
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple


class HybridLayer(enum.Enum):
    INTENT = "intent"
    STRUCTURAL = "structural"
    SEMANTIC = "semantic"
    PROOF = "proof"
    CODE = "code"


class HybridTrustLevel(enum.IntEnum):
    UNTRUSTED = 0
    LLM_RAW = 1
    LLM_JUDGED = 2
    PROPERTY_CHECKED = 3
    Z3_PROVEN = 4
    LEAN_VERIFIED = 5
    HUMAN_VERIFIED = 6

    def __le__(self, other):
        if isinstance(other, HybridTrustLevel):
            return self.value <= other.value
        return NotImplemented

    def meet(self, other: 'HybridTrustLevel') -> 'HybridTrustLevel':
        return min(self, other, key=lambda x: x.value)

    def join(self, other: 'HybridTrustLevel') -> 'HybridTrustLevel':
        return max(self, other, key=lambda x: x.value)


# --- Map to existing deppy TrustLevel ---
try:
    from deppy.core._protocols import TrustLevel as CoreTrustLevel
    # Actual core enum: TRUSTED_AUTO, BOUNDED_AUTO, PROOF_BACKED, TRACE_BACKED, RESIDUAL, ASSUMED
    _HYBRID_TO_CORE = {
        HybridTrustLevel.UNTRUSTED: CoreTrustLevel.ASSUMED,
        HybridTrustLevel.LLM_RAW: CoreTrustLevel.RESIDUAL,
        HybridTrustLevel.LLM_JUDGED: CoreTrustLevel.TRACE_BACKED,
        HybridTrustLevel.PROPERTY_CHECKED: CoreTrustLevel.BOUNDED_AUTO,
        HybridTrustLevel.Z3_PROVEN: CoreTrustLevel.PROOF_BACKED,
        HybridTrustLevel.LEAN_VERIFIED: CoreTrustLevel.TRUSTED_AUTO,
        HybridTrustLevel.HUMAN_VERIFIED: CoreTrustLevel.TRUSTED_AUTO,
    }
    _CORE_TO_HYBRID = {v: k for k, v in _HYBRID_TO_CORE.items()}
    _HAS_CORE = True
except (ImportError, AttributeError):
    _HAS_CORE = False


# --- Lazy imports for submodules ---
def __getattr__(name):
    """Lazy import to avoid circular dependencies and heavy startup."""
    _IMPORTS = {
        # Extensions of existing types
        'HybridPiType': 'deppy.hybrid.extensions',
        'HybridSigmaType': 'deppy.hybrid.extensions',
        'HybridRefinementType': 'deppy.hybrid.extensions',
        'HybridIdentityType': 'deppy.hybrid.extensions',
        'HybridPresheaf': 'deppy.hybrid.extensions',
        'HybridSheafChecker': 'deppy.hybrid.extensions',
        'HybridTrustClassifier': 'deppy.hybrid.extensions',
        'HybridPipeline': 'deppy.hybrid.extensions',
        'HybridLocalSection': 'deppy.hybrid.extensions',
        'OracleResult': 'deppy.hybrid.extensions',
        'HybridCheckResult': 'deppy.hybrid.extensions',

        # Core (Pillar 1)
        'TrustLattice': 'deppy.hybrid.core.trust',
        'Evidence': 'deppy.hybrid.core.trust',
        'ProvenanceTracker': 'deppy.hybrid.core.provenance',
        'HybridContract': 'deppy.hybrid.core.contracts',
        'HybridTypeChecker': 'deppy.hybrid.core.checker',
        'IntentBridge': 'deppy.hybrid.core.intent_bridge',

        # Mixed-mode surface language
        'hole': 'deppy.hybrid.mixed_mode.syntax',
        'spec': 'deppy.hybrid.mixed_mode.syntax',
        'guarantee': 'deppy.hybrid.mixed_mode.syntax',
        'assume': 'deppy.hybrid.mixed_mode.syntax',
        'check': 'deppy.hybrid.mixed_mode.syntax',
        'MixedModeParser': 'deppy.hybrid.mixed_mode.parser',

        # Type expansion (Pillar 10)
        'TypeExpander': 'deppy.hybrid.type_expansion.expander',
        'CodeGenPlan': 'deppy.hybrid.type_expansion.codegen_plan',
        'LargeScaleGenerator': 'deppy.hybrid.type_expansion.large_scale',
        'PlanVerifier': 'deppy.hybrid.type_expansion.plan_verifier',

        # Anti-hallucination (Pillar 4)
        'HallucinationChecker': 'deppy.hybrid.anti_hallucination.checker',

        # Diagnostics (Pillar 11)
        'LocalizationFunctor': 'deppy.hybrid.diagnostics.localization',
        'TrustDashboard': 'deppy.hybrid.diagnostics.trust_dashboard',

        # Discharge (Pillar 5)
        'DischargeCascade': 'deppy.hybrid.discharge.cascade',

        # Pipeline (Pillar 6)
        'PipelineOrchestrator': 'deppy.hybrid.pipeline.orchestrator',

        # Ideation (Pillar 12)
        'DomainSite': 'deppy.hybrid.ideation.domain_site',
        'AnalogyChecker': 'deppy.hybrid.ideation.analogy_types',

        # Bridge to existing deppy
        'PresheafBridge': 'deppy.hybrid.bridge',
        'CohomologyBridge': 'deppy.hybrid.bridge',
        'SolverBridge': 'deppy.hybrid.bridge',
        'BridgeIntentCompiler': 'deppy.hybrid.bridge',

        # Zero-change adoption
        'ImplicitPresheafExtractor': 'deppy.hybrid.zero_change.implicit_presheaf',

        # Lean translation
        'LeanEmitter': 'deppy.hybrid.lean_translation.lean_emitter',
        'LeanArtifact': 'deppy.hybrid.lean_translation.lean_emitter',

        # Research foundations
        'TheoremRegistry': 'deppy.hybrid.research.verified_foundations',
        'SelfVerifier': 'deppy.hybrid.research.verified_foundations',
    }
    if name in _IMPORTS:
        import importlib
        module = importlib.import_module(_IMPORTS[name])
        return getattr(module, name)
    raise AttributeError(f"module 'deppy.hybrid' has no attribute {name!r}")


# --- Quick API functions ---
def hybrid_check(file_path: str, mode: str = "cheap") -> Dict:
    """Check a Python file with hybrid type analysis. Zero annotations required."""
    from deppy.hybrid.diagnostics.localization import ExistingCodeChecker
    checker = ExistingCodeChecker()
    return checker.check_file(file_path)


def hybrid_analyze(source: str, file_path: str = "<string>") -> Dict:
    """Run full hybrid analysis on Python source code."""
    from deppy.hybrid.extensions import HybridPipeline
    pipeline = HybridPipeline()
    return pipeline.run_hybrid(source, file_path)


def hybrid_expand(spec: str, target_loc: int = 50000, oracle_fn=None) -> Dict:
    """Expand a NL spec into a typed code generation plan."""
    from deppy.hybrid.type_expansion.expander import TypeExpander
    expander = TypeExpander()
    return expander.expand(spec, oracle_fn=oracle_fn, target_loc=target_loc)


__all__ = [
    'HybridLayer', 'HybridTrustLevel',
    'hybrid_check', 'hybrid_analyze', 'hybrid_expand',
]
