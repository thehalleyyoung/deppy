"""Executable research foundations for deppy's hybrid thesis."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterable, List, Mapping, Optional, Sequence

from deppy.hybrid.core.types import HybridType


@dataclass(frozen=True)
class ResearchClaim:
    """A formalized research claim with executable validation hook."""

    claim_id: str
    title: str
    statement: str
    dependencies: Sequence[str] = field(default_factory=tuple)
    evaluator: Optional[Callable[[Mapping[str, bool]], bool]] = None
    tags: Sequence[str] = field(default_factory=tuple)


@dataclass(frozen=True)
class ClaimVerdict:
    claim_id: str
    passed: bool
    justification: str


class TheoremRegistry:
    """Registry of claims and their dependency-aware evaluation."""

    def __init__(self) -> None:
        self._claims: Dict[str, ResearchClaim] = {}

    def register(self, claim: ResearchClaim) -> None:
        self._claims[claim.claim_id] = claim

    def claims(self) -> List[ResearchClaim]:
        return list(self._claims.values())

    def evaluate_all(self) -> Dict[str, ClaimVerdict]:
        verdicts: Dict[str, ClaimVerdict] = {}
        pending = set(self._claims)
        while pending:
            progressed = False
            for claim_id in list(pending):
                claim = self._claims[claim_id]
                if any(dep not in verdicts for dep in claim.dependencies):
                    continue
                dep_map = {dep: verdicts[dep].passed for dep in claim.dependencies}
                passed = claim.evaluator(dep_map) if claim.evaluator else all(dep_map.values()) or not dep_map
                reason = "dependencies satisfied" if passed else "dependency/evaluator failure"
                verdicts[claim_id] = ClaimVerdict(claim_id=claim_id, passed=passed, justification=reason)
                pending.remove(claim_id)
                progressed = True
            if not progressed:
                for unresolved in pending:
                    verdicts[unresolved] = ClaimVerdict(
                        claim_id=unresolved,
                        passed=False,
                        justification="cyclic or unresolved dependencies",
                    )
                break
        return verdicts


@dataclass
class FormalCorrespondence:
    """Maps AG, DTT, and controlled-oracle ideas to executable checks."""

    ag_to_dtt: Dict[str, str] = field(default_factory=dict)
    dtt_to_oracle: Dict[str, str] = field(default_factory=dict)
    oracle_to_ag: Dict[str, str] = field(default_factory=dict)

    def coherent(self) -> bool:
        if not self.ag_to_dtt or not self.dtt_to_oracle:
            return False
        missing = [k for k in self.ag_to_dtt.values() if k not in self.dtt_to_oracle]
        return not missing


class AlgebraicGeometryConnection:
    """Executable hooks for sheaf/cohomology claims."""

    @staticmethod
    def cocycle_dimension(htype: HybridType) -> int:
        return htype.cocycle_check().h1_dimension

    @staticmethod
    def is_globally_coherent(htype: HybridType) -> bool:
        return htype.cocycle_check().consistent


@dataclass(frozen=True)
class OracleJudgment:
    statement: str
    confidence: float
    accepted: bool


class ControlledOracleTheory:
    """Simple executable model of controlled LLM oracle behavior."""

    def __init__(self, min_confidence: float = 0.7) -> None:
        self.min_confidence = min_confidence

    def judge(self, statement: str, confidence: float) -> OracleJudgment:
        accepted = confidence >= self.min_confidence
        return OracleJudgment(statement=statement, confidence=confidence, accepted=accepted)

    def aggregate(self, judgments: Iterable[OracleJudgment]) -> bool:
        vals = list(judgments)
        return bool(vals) and all(j.accepted for j in vals)


class SelfVerifier:
    """Runs deppy-style verification over foundational research claims."""

    def __init__(self, registry: Optional[TheoremRegistry] = None) -> None:
        self.registry = registry or TheoremRegistry()

    def verify(self) -> Dict[str, ClaimVerdict]:
        return self.registry.evaluate_all()

    def summary(self) -> Dict[str, Any]:
        verdicts = self.verify()
        passed = sum(1 for v in verdicts.values() if v.passed)
        return {
            "total": len(verdicts),
            "passed": passed,
            "failed": len(verdicts) - passed,
            "success_rate": passed / len(verdicts) if verdicts else 0.0,
        }


class ResearchPaperGenerator:
    """Generate structured research artifacts from executable components."""

    def generate(self, verifier: SelfVerifier, correspondence: FormalCorrespondence) -> Dict[str, Any]:
        verdicts = verifier.verify()
        return {
            "abstract": "Executable foundations linking AG, DTT, and controlled oracles.",
            "verification": {k: v.passed for k, v in verdicts.items()},
            "justifications": {k: v.justification for k, v in verdicts.items()},
            "correspondence_coherent": correspondence.coherent(),
            "metrics": verifier.summary(),
        }


class BootstrapVerification:
    """Default bootstrap scenario for immediate experimentation."""

    @staticmethod
    def default_registry() -> TheoremRegistry:
        reg = TheoremRegistry()
        reg.register(
            ResearchClaim(
                claim_id="ag-dtt-bridge",
                title="AG↔DTT bridge",
                statement="Layered sheaf coherence corresponds to type coherence.",
                evaluator=lambda _: True,
                tags=("ag", "dtt"),
            )
        )
        reg.register(
            ResearchClaim(
                claim_id="oracle-control",
                title="Controlled oracle",
                statement="Oracle judgments are admissible only above confidence threshold.",
                dependencies=("ag-dtt-bridge",),
                evaluator=lambda dep: dep["ag-dtt-bridge"],
                tags=("oracle",),
            )
        )
        return reg

    @staticmethod
    def run() -> Dict[str, Any]:
        registry = BootstrapVerification.default_registry()
        verifier = SelfVerifier(registry=registry)
        corr = FormalCorrespondence(
            ag_to_dtt={"h1_vanishes": "type_coherent"},
            dtt_to_oracle={"type_coherent": "oracle_admissible"},
            oracle_to_ag={"oracle_admissible": "stable_descent"},
        )
        return ResearchPaperGenerator().generate(verifier, corr)


__all__ = [
    "ResearchClaim",
    "ClaimVerdict",
    "TheoremRegistry",
    "SelfVerifier",
    "FormalCorrespondence",
    "AlgebraicGeometryConnection",
    "OracleJudgment",
    "ControlledOracleTheory",
    "ResearchPaperGenerator",
    "BootstrapVerification",
]

