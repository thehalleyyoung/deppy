"""Core hybrid foundations."""

from deppy.hybrid.core.intent_bridge import (
    IntentBridge,
    IntentBridgeResult,
    IntentClaim,
    bridge_intent,
)
from deppy.hybrid.core.types import (
    HybridType,
    IntentSection,
    Layer,
    StructuralSection,
    SemanticSection,
    ProofSection,
    CodeSection,
)

__all__ = [
    "Layer",
    "HybridType",
    "IntentSection",
    "StructuralSection",
    "SemanticSection",
    "ProofSection",
    "CodeSection",
    "IntentClaim",
    "IntentBridgeResult",
    "IntentBridge",
    "bridge_intent",
]
