"""Intent-to-hybrid bridge utilities.

This module turns natural-language intent (docstrings/comments/spec text) into
typed hybrid sections that can participate in structural checks, semantic
oracle checks, and downstream proof emission.
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Optional, Protocol

from deppy.hybrid.core.types import (
    HybridType,
    IntentSection,
    SemanticPredicate,
    SemanticSection,
    StructuralPredicate,
    StructuralSection,
    TrustLevel,
)

_SPLIT_RE = re.compile(r"[.;\n]+")


class IntentSource(Protocol):
    """Protocol for intent-bearing objects."""

    def source_text(self) -> str:
        """Return NL source text."""


@dataclass(frozen=True)
class IntentClaim:
    """Structured claim extracted from NL intent."""

    claim: str
    kind: str
    confidence: float = 0.6
    formula: Optional[str] = None
    metadata: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {
            "claim": self.claim,
            "kind": self.kind,
            "confidence": self.confidence,
        }
        if self.formula:
            d["formula"] = self.formula
        d.update(self.metadata)
        return d


@dataclass
class IntentBridgeResult:
    """Typed result of bridging NL intent into a :class:`HybridType`."""

    intent: IntentSection
    structural: StructuralSection
    semantic: SemanticSection
    hybrid_type: HybridType
    claims: List[IntentClaim] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)


class IntentBridge:
    """Bridge natural-language intent to typed hybrid sections."""

    def extract_claims(self, text: str) -> List[IntentClaim]:
        claims: List[IntentClaim] = []
        for raw in (p.strip() for p in _SPLIT_RE.split(text) if p.strip()):
            lower = raw.lower()
            if any(k in lower for k in ("must", "shall", "require", "always")):
                claims.append(
                    IntentClaim(raw, kind="structural", confidence=0.8, formula=self._guess_formula(raw))
                )
            elif any(k in lower for k in ("returns", "return", "output")):
                claims.append(IntentClaim(raw, kind="postcondition", confidence=0.75))
            elif any(k in lower for k in ("fast", "efficient", "readable", "safe", "robust")):
                claims.append(IntentClaim(raw, kind="semantic", confidence=0.65))
            elif any(k in lower for k in ("if ", "when ", "unless ", "raise", "error")):
                claims.append(IntentClaim(raw, kind="guard", confidence=0.7, formula=self._guess_formula(raw)))
            else:
                claims.append(IntentClaim(raw, kind="general", confidence=0.55))
        return claims

    def from_text(self, text: str, *, type_name: str = "") -> IntentBridgeResult:
        claims = self.extract_claims(text)
        intent = IntentSection(text=text, parsed_claims=[c.to_dict() for c in claims])
        structural = self._build_structural(claims)
        semantic = self._build_semantic(claims)
        hybrid = HybridType(
            name=type_name or "IntentDerivedType",
            description="Derived from natural-language intent",
            intent=intent,
            structural=structural,
            semantic=semantic,
            trust_level=TrustLevel.LLM_JUDGED if semantic.predicates else TrustLevel.RUNTIME_CHECKED,
        )
        warnings: List[str] = []
        if not claims:
            warnings.append("No claims extracted from input intent text")
        return IntentBridgeResult(
            intent=intent,
            structural=structural,
            semantic=semantic,
            hybrid_type=hybrid,
            claims=claims,
            warnings=warnings,
        )

    def from_function_source(self, source: str, *, function_name: Optional[str] = None) -> IntentBridgeResult:
        module = ast.parse(source)
        target: Optional[ast.FunctionDef] = None
        for node in module.body:
            if isinstance(node, ast.FunctionDef):
                if function_name is None or node.name == function_name:
                    target = node
                    break
        if target is None:
            raise ValueError("No function definition found in source")
        doc = ast.get_docstring(target) or ""
        if not doc:
            doc = f"Function {target.name} has no docstring; infer from signature."
        bridged = self.from_text(doc, type_name=f"{target.name}_intent")
        for arg in target.args.args:
            ann = ast.unparse(arg.annotation) if arg.annotation is not None else "Any"
            bridged.structural.add_predicate(
                StructuralPredicate(
                    name=f"arg_{arg.arg}_typed",
                    formula=f"isinstance({arg.arg}, {ann})" if ann != "Any" else "True",
                    variables={arg.arg: ann},
                    description=f"Argument {arg.arg} annotation",
                )
            )
        if target.returns is not None:
            ret = ast.unparse(target.returns)
            bridged.intent.add_claim(f"Return type should satisfy annotation {ret}", kind="postcondition")
        bridged.hybrid_type.name = f"{target.name}_hybrid"
        bridged.hybrid_type.structural = bridged.structural
        bridged.hybrid_type.semantic = bridged.semantic
        return bridged

    def bridge_many(self, intent_texts: Iterable[str]) -> List[IntentBridgeResult]:
        return [self.from_text(text, type_name=f"Intent_{i}") for i, text in enumerate(intent_texts)]

    def _build_structural(self, claims: List[IntentClaim]) -> StructuralSection:
        preds: List[StructuralPredicate] = []
        for i, claim in enumerate(claims):
            if claim.kind in {"structural", "guard"}:
                preds.append(
                    StructuralPredicate(
                        name=f"intent_structural_{i}",
                        formula=claim.formula or "True",
                        description=claim.claim,
                    )
                )
        return StructuralSection(predicates=preds)

    def _build_semantic(self, claims: List[IntentClaim]) -> SemanticSection:
        preds: List[SemanticPredicate] = []
        for i, claim in enumerate(claims):
            if claim.kind in {"semantic", "postcondition", "general"}:
                preds.append(
                    SemanticPredicate(
                        name=f"intent_semantic_{i}",
                        prompt=f"Determine whether the implementation satisfies: {claim.claim}",
                        rubric={"claim": claim.claim, "kind": claim.kind},
                        confidence_threshold=max(0.5, min(0.95, claim.confidence)),
                        description=claim.claim,
                    )
                )
        return SemanticSection(predicates=preds)

    @staticmethod
    def _guess_formula(text: str) -> str:
        lower = text.lower()
        if "non-empty" in lower or "not empty" in lower:
            return "len(x) > 0"
        if "positive" in lower:
            return "x > 0"
        if "non-negative" in lower:
            return "x >= 0"
        if "sorted" in lower:
            return "all(x[i] <= x[i+1] for i in range(len(x)-1))"
        return "True"


def bridge_intent(text: str, *, type_name: str = "") -> IntentBridgeResult:
    """Convenience wrapper for one-shot bridging."""
    return IntentBridge().from_text(text, type_name=type_name)


__all__ = [
    "IntentSource",
    "IntentClaim",
    "IntentBridgeResult",
    "IntentBridge",
    "bridge_intent",
]

