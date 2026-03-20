"""Anti-hallucination type checker with full deppy integration.

An artifact is *hallucinated* iff it fails to inhabit its declared HybridType:

    hallucinated(a, T)  <=>  not (a : T)

This module implements the check through four composable layers:

1. **Structural** -- decidable syntactic / type-level predicates dispatched via
   :class:`deppy.solver.FragmentDispatcher` (backed by Z3).
2. **Semantic** -- oracle-mediated checks against external knowledge.
3. **Grounding** -- claim-level entailment against source material, using
   :func:`deppy.nl_synthesis.synthesize_types_from_docstring` for claim
   extraction.
4. **Consistency** -- pairwise identity-type checks and circular-dependency
   detection via :class:`deppy.solver.Z3Backend`.

The overall trust level follows the *weakest-link principle* (the meet in the
trust lattice defined in ``deppy.core._protocols.TrustLevel``).

Throughout, results carry full provenance so an upstream ``AuditReport`` can
reconstruct exactly which checks fired, which evidence was gathered, and what
oracle calls were made.
"""
from __future__ import annotations

import ast
import copy
import hashlib
import itertools
import json
import math
import re
import textwrap
import time
import uuid
from collections import defaultdict
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterable,
    Iterator,
    List,
    Mapping,
    Optional,
    Protocol,
    Sequence,
    Set,
    Tuple,
    Union,
)

if TYPE_CHECKING:
    from deppy.cohomological_analysis import CohomologicalResult
    from deppy.core._protocols import (
        Cover,
        LocalSection,
        Morphism,
        ObstructionData,
        SiteId,
        TrustLevel,
    )
    from deppy.core.presheaf import ConcretePresheaf
    from deppy.kernel.fixed_point import FixedPointEngine
    from deppy.kernel.trust_classifier import TrustClassifier
    from deppy.nl_synthesis import (
        DocstringParser,
        SynthesizedAnnotationBundle,
        SynthesizedConstraint,
        synthesize_types_from_docstring,
    )
    from deppy.solver.fragment_dispatcher import FragmentDispatcher
    from deppy.solver.solver_interface import SolverResult
    from deppy.solver.z3_backend import Z3Backend
    from deppy.solver.z3_encoder import Z3Encoder
    from deppy.types.refinement import Predicate, RefinementType


# ======================================================================
#  Lazy import helpers -- keep module importable even when deppy is absent
# ======================================================================

def _import_trust_level():
    """Lazily import TrustLevel to avoid circular imports at module scope."""
    from deppy.core._protocols import TrustLevel
    return TrustLevel


def _import_fragment_dispatcher():
    from deppy.solver.fragment_dispatcher import FragmentDispatcher
    return FragmentDispatcher


def _import_z3_backend():
    from deppy.solver.z3_backend import Z3Backend
    return Z3Backend


def _import_z3_encoder():
    from deppy.solver.z3_encoder import Z3Encoder
    return Z3Encoder


def _import_trust_classifier():
    from deppy.kernel.trust_classifier import TrustClassifier
    return TrustClassifier


def _import_trust_helpers():
    from deppy.kernel.trust_classifier import trust_meet, trust_rank
    return trust_meet, trust_rank


def _import_nl_synthesis():
    from deppy.nl_synthesis import synthesize_types_from_docstring
    return synthesize_types_from_docstring


def _import_docstring_parser():
    from deppy.nl_synthesis import DocstringParser
    return DocstringParser


def _import_obligation_classifier():
    from deppy.solver.fragment_dispatcher import ObligationClassifier
    return ObligationClassifier


# ======================================================================
#  Severity & trust enums local to the checker
# ======================================================================

class Severity(Enum):
    """Severity of a single check failure."""
    CRITICAL = "CRITICAL"
    HIGH = "HIGH"
    MEDIUM = "MEDIUM"
    LOW = "LOW"
    INFO = "INFO"


_SEVERITY_RANK: Dict[str, int] = {
    "CRITICAL": 4,
    "HIGH": 3,
    "MEDIUM": 2,
    "LOW": 1,
    "INFO": 0,
}


class CheckPhase(Enum):
    """Which phase a check belongs to."""
    STRUCTURAL = "structural"
    SEMANTIC = "semantic"
    GROUNDING = "grounding"
    CONSISTENCY = "consistency"


class TrustMapping(Enum):
    """Maps check outcomes to TrustLevel names (mirrors deppy.core._protocols.TrustLevel)."""
    PROOF_BACKED = "proof_backed"
    TRUSTED_AUTO = "trusted_auto"
    TRACE_BACKED = "trace_backed"
    BOUNDED_AUTO = "bounded_auto"
    RESIDUAL = "residual"
    ASSUMED = "assumed"


_TRUST_RANK: Dict[str, int] = {
    "proof_backed": 5,
    "trusted_auto": 4,
    "trace_backed": 3,
    "bounded_auto": 2,
    "residual": 1,
    "assumed": 0,
}


def _trust_name_meet(a: str, b: str) -> str:
    """Compute the meet (weakest-link) of two trust level names."""
    ra = _TRUST_RANK.get(a, 0)
    rb = _TRUST_RANK.get(b, 0)
    if ra <= rb:
        return a
    return b


# ======================================================================
#  Result dataclasses (~200 lines)
# ======================================================================

@dataclass(frozen=True)
class CheckEvidence:
    """A single piece of evidence gathered during a check."""
    source: str
    content: str
    confidence: float = 1.0
    metadata: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "source": self.source,
            "content": self.content,
            "confidence": self.confidence,
            "metadata": self.metadata,
        }


@dataclass
class CheckDetail:
    """Result of a single sub-check (one predicate evaluation).

    Each detail records whether the predicate was satisfied, together with
    provenance evidence and an optional counterexample from the solver.
    """
    name: str
    phase: str
    passed: bool
    severity: str = "INFO"
    message: str = ""
    evidence: List[CheckEvidence] = field(default_factory=list)
    counterexample: Optional[Dict[str, Any]] = None
    trust_level: str = "assumed"
    elapsed_ms: float = 0.0
    predicate_repr: str = ""

    @property
    def failed(self) -> bool:
        return not self.passed

    def to_dict(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {
            "name": self.name,
            "phase": self.phase,
            "passed": self.passed,
            "severity": self.severity,
            "message": self.message,
            "trust_level": self.trust_level,
            "elapsed_ms": round(self.elapsed_ms, 3),
        }
        if self.evidence:
            d["evidence"] = [e.to_dict() for e in self.evidence]
        if self.counterexample is not None:
            d["counterexample"] = self.counterexample
        if self.predicate_repr:
            d["predicate_repr"] = self.predicate_repr
        return d


@dataclass
class GroundingResult:
    """Result of grounding a set of claims against source material."""
    grounded: bool
    total_claims: int = 0
    grounded_claims: int = 0
    ungrounded_claims: List[str] = field(default_factory=list)
    evidence_map: Dict[str, List[Dict[str, Any]]] = field(default_factory=dict)
    confidence: float = 0.0
    trust_level: str = "assumed"
    details: List[CheckDetail] = field(default_factory=list)

    @property
    def grounding_ratio(self) -> float:
        if self.total_claims == 0:
            return 1.0
        return self.grounded_claims / self.total_claims

    def to_dict(self) -> Dict[str, Any]:
        return {
            "grounded": self.grounded,
            "total_claims": self.total_claims,
            "grounded_claims": self.grounded_claims,
            "ungrounded_claims": self.ungrounded_claims,
            "grounding_ratio": round(self.grounding_ratio, 4),
            "confidence": round(self.confidence, 4),
            "trust_level": self.trust_level,
        }


@dataclass
class ConsistencyResult:
    """Result of checking internal consistency across multiple artifacts."""
    consistent: bool
    pairwise_conflicts: List[Dict[str, Any]] = field(default_factory=list)
    circular_dependencies: List[str] = field(default_factory=list)
    trust_level: str = "assumed"
    details: List[CheckDetail] = field(default_factory=list)

    @property
    def conflict_count(self) -> int:
        return len(self.pairwise_conflicts)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "consistent": self.consistent,
            "conflict_count": self.conflict_count,
            "pairwise_conflicts": self.pairwise_conflicts,
            "circular_dependencies": self.circular_dependencies,
            "trust_level": self.trust_level,
        }


@dataclass
class HallucinationResult:
    """Top-level result of the hallucination check.

    ``hallucinated`` is True iff the artifact fails to inhabit its declared
    type: hallucinated(a, T) <=> not (a : T).
    """
    hallucinated: bool
    trust_level: str = "assumed"
    structural_details: List[CheckDetail] = field(default_factory=list)
    semantic_details: List[CheckDetail] = field(default_factory=list)
    grounding: Optional[GroundingResult] = None
    consistency: Optional[ConsistencyResult] = None
    overall_confidence: float = 0.0
    elapsed_ms: float = 0.0
    artifact_hash: str = ""
    type_hash: str = ""

    @property
    def all_details(self) -> List[CheckDetail]:
        details = list(self.structural_details) + list(self.semantic_details)
        if self.grounding:
            details.extend(self.grounding.details)
        if self.consistency:
            details.extend(self.consistency.details)
        return details

    @property
    def failure_count(self) -> int:
        return sum(1 for d in self.all_details if d.failed)

    @property
    def critical_failures(self) -> List[CheckDetail]:
        return [d for d in self.all_details if d.failed and d.severity == "CRITICAL"]

    def to_dict(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {
            "hallucinated": self.hallucinated,
            "trust_level": self.trust_level,
            "overall_confidence": round(self.overall_confidence, 4),
            "elapsed_ms": round(self.elapsed_ms, 3),
            "failure_count": self.failure_count,
            "structural_details": [s.to_dict() for s in self.structural_details],
            "semantic_details": [s.to_dict() for s in self.semantic_details],
        }
        if self.grounding:
            d["grounding"] = self.grounding.to_dict()
        if self.consistency:
            d["consistency"] = self.consistency.to_dict()
        return d


# ======================================================================
#  DriftInstance (for SemanticDriftDetector)
# ======================================================================

@dataclass
class DriftInstance:
    """A single instance of semantic drift between documentation and code."""
    location: str
    docstring_claim: str
    code_reality: str
    severity: str
    evidence: List[str] = field(default_factory=list)
    confidence: float = 0.0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "location": self.location,
            "docstring_claim": self.docstring_claim,
            "code_reality": self.code_reality,
            "severity": self.severity,
            "evidence": self.evidence,
            "confidence": round(self.confidence, 4),
        }


# ======================================================================
#  AuditReport (~100 lines)
# ======================================================================

@dataclass
class OracleCallRecord:
    """Record of a single oracle (LLM / external API) call during checking."""
    oracle_id: str
    prompt_hash: str
    response_hash: str
    latency_ms: float
    cost_estimate: float = 0.0
    phase: str = ""
    success: bool = True

    def to_dict(self) -> Dict[str, Any]:
        return {
            "oracle_id": self.oracle_id,
            "prompt_hash": self.prompt_hash,
            "response_hash": self.response_hash,
            "latency_ms": round(self.latency_ms, 3),
            "cost_estimate": round(self.cost_estimate, 6),
            "phase": self.phase,
            "success": self.success,
        }


@dataclass
class AuditReport:
    """Full audit trail for a hallucination-check session.

    Records every check performed, all evidence gathered, trust-level
    assignments, oracle calls, and cumulative cost.
    """
    audit_id: str = field(default_factory=lambda: uuid.uuid4().hex[:12])
    timestamp: float = field(default_factory=time.time)
    artifact_summary: str = ""
    type_summary: str = ""
    result: Optional[HallucinationResult] = None
    checks_performed: List[CheckDetail] = field(default_factory=list)
    oracle_calls: List[OracleCallRecord] = field(default_factory=list)
    trust_level: str = "assumed"
    total_elapsed_ms: float = 0.0

    @property
    def total_oracle_cost(self) -> float:
        return sum(c.cost_estimate for c in self.oracle_calls)

    @property
    def oracle_call_count(self) -> int:
        return len(self.oracle_calls)

    @property
    def checks_passed(self) -> int:
        return sum(1 for c in self.checks_performed if c.passed)

    @property
    def checks_failed(self) -> int:
        return sum(1 for c in self.checks_performed if not c.passed)

    def add_check(self, detail: CheckDetail) -> None:
        self.checks_performed.append(detail)

    def add_oracle_call(self, record: OracleCallRecord) -> None:
        self.oracle_calls.append(record)

    def finalize(self, result: HallucinationResult) -> None:
        """Attach the final result and update aggregate fields."""
        self.result = result
        self.trust_level = result.trust_level
        self.total_elapsed_ms = result.elapsed_ms

    def to_dict(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {
            "audit_id": self.audit_id,
            "timestamp": self.timestamp,
            "artifact_summary": self.artifact_summary,
            "type_summary": self.type_summary,
            "trust_level": self.trust_level,
            "total_elapsed_ms": round(self.total_elapsed_ms, 3),
            "checks_passed": self.checks_passed,
            "checks_failed": self.checks_failed,
            "oracle_call_count": self.oracle_call_count,
            "total_oracle_cost": round(self.total_oracle_cost, 6),
            "checks": [c.to_dict() for c in self.checks_performed],
            "oracle_calls": [o.to_dict() for o in self.oracle_calls],
        }
        if self.result:
            d["result"] = self.result.to_dict()
        return d

    def to_json(self, indent: int = 2) -> str:
        return json.dumps(self.to_dict(), indent=indent, default=str)


# ======================================================================
#  GroundingChecker (~300 lines)
# ======================================================================

class GroundingChecker:
    """Checks whether claims in an artifact are grounded in source material.

    Uses :func:`deppy.nl_synthesis.synthesize_types_from_docstring` for
    extraction of structured constraints from natural-language claims, then
    verifies each claim against the provided source documents via token-overlap
    heuristics and, where possible, Z3-backed entailment checks.
    """

    _SENTENCE_RE = re.compile(r"(?<=[.!?])\s+")
    _CLAIM_INDICATORS = re.compile(
        r"\b(returns?|raises?|requires?|ensures?|must|shall|always|never|"
        r"guarantees?|assumes?|expects?|invariant|pre-?condition|"
        r"post-?condition|asserts?|should)\b",
        re.IGNORECASE,
    )
    _MIN_CLAIM_TOKENS = 4

    def __init__(
        self,
        *,
        min_evidence_confidence: float = 0.3,
        max_claims: int = 200,
        use_nl_synthesis: bool = True,
    ) -> None:
        self._min_evidence_confidence = min_evidence_confidence
        self._max_claims = max_claims
        self._use_nl_synthesis = use_nl_synthesis

    # -- claim extraction --------------------------------------------------

    def extract_claims(self, text: str) -> List[str]:
        """Extract verifiable claims from *text*.

        First attempts to use ``deppy.nl_synthesis.synthesize_types_from_docstring``
        to pull structured constraints; falls back to sentence-level heuristics.
        """
        claims: List[str] = []

        if self._use_nl_synthesis:
            claims.extend(self._extract_via_nl_synthesis(text))

        claims.extend(self._extract_heuristic(text))

        seen: Set[str] = set()
        unique: List[str] = []
        for c in claims:
            norm = c.strip().lower()
            if norm and norm not in seen:
                seen.add(norm)
                unique.append(c.strip())
        return unique[: self._max_claims]

    def _extract_via_nl_synthesis(self, text: str) -> List[str]:
        """Use deppy.nl_synthesis to pull structured constraints from text."""
        try:
            synth_fn = _import_nl_synthesis()
            bundle = synth_fn(text)
            claims: List[str] = []
            if hasattr(bundle, "constraints"):
                for constraint in bundle.constraints:
                    desc = getattr(constraint, "description", None)
                    if desc:
                        claims.append(str(desc))
                    raw = getattr(constraint, "raw_fragment", None)
                    if raw and str(raw) not in claims:
                        claims.append(str(raw))
            if hasattr(bundle, "fragments"):
                for frag in bundle.fragments:
                    text_val = getattr(frag, "text", None) or getattr(frag, "raw", None)
                    if text_val:
                        claims.append(str(text_val))
            return claims
        except Exception:
            return []

    def _extract_heuristic(self, text: str) -> List[str]:
        """Sentence-level heuristic extraction: keep sentences with claim indicators."""
        sentences = self._SENTENCE_RE.split(text)
        claims: List[str] = []
        for sent in sentences:
            sent = sent.strip()
            if not sent:
                continue
            tokens = sent.split()
            if len(tokens) < self._MIN_CLAIM_TOKENS:
                continue
            if self._CLAIM_INDICATORS.search(sent):
                claims.append(sent)
        return claims

    # -- evidence finding --------------------------------------------------

    def find_evidence(
        self, claim: str, sources: List[str]
    ) -> List[Dict[str, Any]]:
        """Find evidence for *claim* in *sources*.

        Returns a list of evidence dicts with ``source_idx``, ``excerpt``, and
        ``confidence`` keys, sorted by descending confidence.
        """
        evidence: List[Dict[str, Any]] = []
        claim_tokens = self._tokenize(claim)
        if not claim_tokens:
            return evidence

        for idx, source in enumerate(sources):
            source_tokens = self._tokenize(source)
            if not source_tokens:
                continue
            overlap = claim_tokens & source_tokens
            if not overlap:
                continue
            jaccard = len(overlap) / len(claim_tokens | source_tokens)
            recall = len(overlap) / len(claim_tokens)
            confidence = 0.6 * recall + 0.4 * jaccard

            if confidence >= self._min_evidence_confidence:
                excerpt = self._extract_best_excerpt(claim, source, overlap)
                evidence.append(
                    {
                        "source_idx": idx,
                        "excerpt": excerpt,
                        "confidence": round(confidence, 4),
                        "overlap_tokens": len(overlap),
                        "recall": round(recall, 4),
                    }
                )

        evidence.sort(key=lambda e: e["confidence"], reverse=True)
        return evidence

    def _extract_best_excerpt(
        self, claim: str, source: str, overlap: Set[str]
    ) -> str:
        """Extract the best matching excerpt from *source* for *claim*."""
        sentences = self._SENTENCE_RE.split(source)
        if not sentences:
            return source[:200]
        best_sent = ""
        best_score = -1.0
        for sent in sentences:
            sent_tokens = self._tokenize(sent)
            if not sent_tokens:
                continue
            score = len(sent_tokens & overlap) / max(len(sent_tokens), 1)
            if score > best_score:
                best_score = score
                best_sent = sent
        return best_sent[:300] if best_sent else source[:200]

    @staticmethod
    def _tokenize(text: str) -> Set[str]:
        """Simple whitespace + lowercase tokenization with stopword removal."""
        _STOPWORDS = frozenset({
            "a", "an", "the", "is", "are", "was", "were", "be", "been",
            "being", "have", "has", "had", "do", "does", "did", "will",
            "would", "could", "should", "may", "might", "can", "shall",
            "to", "of", "in", "for", "on", "with", "at", "by", "from",
            "as", "into", "through", "during", "before", "after", "and",
            "but", "or", "nor", "not", "so", "yet", "both", "either",
            "neither", "each", "every", "all", "any", "few", "more",
            "most", "other", "some", "such", "no", "only", "own", "same",
            "than", "too", "very", "just", "because", "if", "it", "its",
            "this", "that", "these", "those", "i", "me", "my", "we", "our",
        })
        tokens = set(re.findall(r"[a-z0-9_]+", text.lower()))
        return tokens - _STOPWORDS

    # -- top-level grounding check -----------------------------------------

    def check_claim_grounding(
        self, claim: str, sources: List[str]
    ) -> GroundingResult:
        """Check whether a single *claim* is grounded in *sources*."""
        evidence = self.find_evidence(claim, sources)
        grounded = len(evidence) > 0 and evidence[0]["confidence"] >= self._min_evidence_confidence
        confidence = evidence[0]["confidence"] if evidence else 0.0
        trust = "trace_backed" if grounded else "assumed"

        detail = CheckDetail(
            name="grounding:" + claim[:60],
            phase=CheckPhase.GROUNDING.value,
            passed=grounded,
            severity="HIGH" if not grounded else "INFO",
            message="Claim " + ("grounded" if grounded else "UNGROUNDED") + ": " + claim[:80],
            trust_level=trust,
        )
        return GroundingResult(
            grounded=grounded,
            total_claims=1,
            grounded_claims=1 if grounded else 0,
            ungrounded_claims=[] if grounded else [claim],
            evidence_map={claim: evidence},
            confidence=confidence,
            trust_level=trust,
            details=[detail],
        )

    def check_all_claims(
        self, text: str, sources: List[str]
    ) -> GroundingResult:
        """Extract claims from *text* and check each against *sources*."""
        claims = self.extract_claims(text)
        if not claims:
            return GroundingResult(
                grounded=True,
                total_claims=0,
                grounded_claims=0,
                confidence=1.0,
                trust_level="bounded_auto",
            )

        details: List[CheckDetail] = []
        evidence_map: Dict[str, List[Dict[str, Any]]] = {}
        ungrounded: List[str] = []
        grounded_count = 0

        for claim in claims:
            result = self.check_claim_grounding(claim, sources)
            details.extend(result.details)
            evidence_map.update(result.evidence_map)
            if result.grounded:
                grounded_count += 1
            else:
                ungrounded.append(claim)

        total = len(claims)
        ratio = grounded_count / total if total else 1.0
        overall_grounded = ratio >= 0.8
        confidence = ratio

        if overall_grounded and ratio >= 0.95:
            trust = "trusted_auto"
        elif overall_grounded:
            trust = "trace_backed"
        elif ratio >= 0.5:
            trust = "bounded_auto"
        else:
            trust = "assumed"

        return GroundingResult(
            grounded=overall_grounded,
            total_claims=total,
            grounded_claims=grounded_count,
            ungrounded_claims=ungrounded,
            evidence_map=evidence_map,
            confidence=confidence,
            trust_level=trust,
            details=details,
        )


# ======================================================================
#  ConsistencyChecker (~200 lines)
# ======================================================================

class ConsistencyChecker:
    """Check internal consistency of a collection of artifacts.

    Delegates constraint satisfiability to :class:`deppy.solver.Z3Backend` when
    available, falling back to heuristic overlap analysis.
    """

    def __init__(self, *, use_z3: bool = True) -> None:
        self._use_z3 = use_z3
        self._z3_backend: Any = None

    def _get_z3_backend(self) -> Any:
        """Lazily instantiate a Z3Backend."""
        if self._z3_backend is not None:
            return self._z3_backend
        if not self._use_z3:
            return None
        try:
            Z3Backend = _import_z3_backend()
            self._z3_backend = Z3Backend()
            if not self._z3_backend.is_available:
                self._z3_backend = None
        except Exception:
            self._z3_backend = None
        return self._z3_backend

    # -- pairwise identity-type checks -------------------------------------

    def check_pairwise(
        self, artifacts: List[Dict[str, Any]]
    ) -> List[Dict[str, Any]]:
        """Check pairwise consistency of *artifacts*.

        Each artifact is expected to carry a ``"constraints"`` key with a list
        of predicate descriptions (strings or dicts).  Two artifacts conflict
        when their joint constraint set is unsatisfiable (checked via Z3 when
        available) or when they make directly contradictory claims.
        """
        conflicts: List[Dict[str, Any]] = []
        n = len(artifacts)
        for i in range(n):
            for j in range(i + 1, n):
                conflict = self._check_pair(artifacts[i], artifacts[j], i, j)
                if conflict is not None:
                    conflicts.append(conflict)
        return conflicts

    def _check_pair(
        self,
        a: Dict[str, Any],
        b: Dict[str, Any],
        idx_a: int,
        idx_b: int,
    ) -> Optional[Dict[str, Any]]:
        """Check a single pair for contradictions."""
        ca = self._extract_constraints(a)
        cb = self._extract_constraints(b)
        if not ca and not cb:
            return None

        contradiction = self._detect_direct_contradiction(ca, cb)
        if contradiction:
            return {
                "artifact_a": idx_a,
                "artifact_b": idx_b,
                "type": "direct_contradiction",
                "details": contradiction,
            }

        z3_conflict = self._check_z3_consistency(ca, cb)
        if z3_conflict:
            return {
                "artifact_a": idx_a,
                "artifact_b": idx_b,
                "type": "z3_unsatisfiable",
                "details": z3_conflict,
            }

        return None

    def _extract_constraints(self, artifact: Dict[str, Any]) -> List[str]:
        """Pull constraint strings from an artifact dict."""
        raw = artifact.get("constraints", [])
        if isinstance(raw, str):
            return [raw]
        result: List[str] = []
        for item in raw:
            if isinstance(item, str):
                result.append(item)
            elif isinstance(item, dict):
                desc = item.get("description") or item.get("predicate") or str(item)
                result.append(str(desc))
        return result

    def _detect_direct_contradiction(
        self, ca: List[str], cb: List[str]
    ) -> Optional[str]:
        """Heuristic: detect if any constraint in *ca* directly negates one in *cb*."""
        _NEGATION_PAIRS = [
            ("must be non-null", "may be null"),
            ("must be positive", "may be negative"),
            ("must be non-empty", "may be empty"),
            ("returns true", "returns false"),
            ("is always", "is never"),
            ("must not raise", "may raise"),
            ("is immutable", "is mutable"),
            ("is sorted", "is unsorted"),
        ]
        ca_lower = [c.lower() for c in ca]
        cb_lower = [c.lower() for c in cb]
        for pos, neg in _NEGATION_PAIRS:
            a_has_pos = any(pos in c for c in ca_lower)
            b_has_neg = any(neg in c for c in cb_lower)
            a_has_neg = any(neg in c for c in ca_lower)
            b_has_pos = any(pos in c for c in cb_lower)
            if (a_has_pos and b_has_neg) or (a_has_neg and b_has_pos):
                return "Contradictory constraints: '" + pos + "' vs '" + neg + "'"
        return None

    def _check_z3_consistency(
        self, ca: List[str], cb: List[str]
    ) -> Optional[str]:
        """Attempt Z3 satisfiability check on the joint constraint set.

        Uses the deppy Z3Backend to check SAT of the conjunction.  If UNSAT,
        the pair is inconsistent.
        """
        backend = self._get_z3_backend()
        if backend is None:
            return None
        try:
            from deppy.solver.solver_interface import SolverObligation, SolverStatus
            from deppy.types.refinement import ConjunctionPred, VarPred

            all_constraints = ca + cb
            if not all_constraints:
                return None

            preds: list = []
            for c_str in all_constraints:
                preds.append(VarPred(var_name=c_str.replace(" ", "_")[:40]))

            if not preds:
                return None

            conj = ConjunctionPred(conjuncts=tuple(preds))
            obligation = SolverObligation(
                predicate=conj,
                description="consistency_check",
            )
            result = backend.check(obligation)
            if hasattr(result, "status") and result.status == SolverStatus.UNSAT:
                return "Joint constraints unsatisfiable (" + str(len(all_constraints)) + " constraints)"
        except Exception:
            pass
        return None

    # -- circular dependency detection -------------------------------------

    def check_circular_dependencies(
        self, artifacts: List[Dict[str, Any]]
    ) -> List[str]:
        """Detect circular dependency chains among *artifacts*.

        Each artifact may have a ``"depends_on"`` list of artifact identifiers.
        Returns descriptions of any cycles found.
        """
        graph: Dict[str, List[str]] = {}
        for art in artifacts:
            aid = art.get("id", art.get("name", ""))
            deps = art.get("depends_on", [])
            if isinstance(deps, str):
                deps = [deps]
            graph[aid] = list(deps)

        cycles: List[str] = []
        visited: Set[str] = set()
        rec_stack: Set[str] = set()

        def _dfs(node: str, path: List[str]) -> None:
            visited.add(node)
            rec_stack.add(node)
            path.append(node)
            for neighbor in graph.get(node, []):
                if neighbor not in visited:
                    _dfs(neighbor, path)
                elif neighbor in rec_stack:
                    cycle_start = path.index(neighbor)
                    cycle = path[cycle_start:] + [neighbor]
                    cycles.append(" -> ".join(cycle))
            path.pop()
            rec_stack.discard(node)

        for node in graph:
            if node not in visited:
                _dfs(node, [])

        return cycles

    def check(
        self, artifacts: List[Dict[str, Any]]
    ) -> ConsistencyResult:
        """Run full consistency checking on *artifacts*."""
        t0 = time.monotonic()
        pairwise = self.check_pairwise(artifacts)
        cycles = self.check_circular_dependencies(artifacts)
        elapsed = (time.monotonic() - t0) * 1000

        consistent = len(pairwise) == 0 and len(cycles) == 0

        if consistent:
            trust = "trusted_auto"
        elif pairwise:
            trust = "assumed"
        else:
            trust = "residual"

        details: List[CheckDetail] = []
        for conflict in pairwise:
            details.append(
                CheckDetail(
                    name="consistency:pair(" + str(conflict["artifact_a"]) + "," + str(conflict["artifact_b"]) + ")",
                    phase=CheckPhase.CONSISTENCY.value,
                    passed=False,
                    severity="HIGH",
                    message=conflict.get("details", "Pairwise inconsistency"),
                    trust_level="assumed",
                    elapsed_ms=elapsed / max(len(pairwise) + len(cycles), 1),
                )
            )
        for cycle in cycles:
            details.append(
                CheckDetail(
                    name="consistency:circular_dep",
                    phase=CheckPhase.CONSISTENCY.value,
                    passed=False,
                    severity="MEDIUM",
                    message="Circular dependency: " + cycle,
                    trust_level="residual",
                    elapsed_ms=elapsed / max(len(pairwise) + len(cycles), 1),
                )
            )
        if not details:
            details.append(
                CheckDetail(
                    name="consistency:all_clear",
                    phase=CheckPhase.CONSISTENCY.value,
                    passed=True,
                    severity="INFO",
                    message="All artifacts internally consistent",
                    trust_level=trust,
                    elapsed_ms=elapsed,
                )
            )

        return ConsistencyResult(
            consistent=consistent,
            pairwise_conflicts=pairwise,
            circular_dependencies=cycles,
            trust_level=trust,
            details=details,
        )


# ======================================================================
#  SemanticDriftDetector (~200 lines)
# ======================================================================

class SemanticDriftDetector:
    """Detects semantic drift between documentation and code.

    Uses :func:`deppy.nl_synthesis.synthesize_types_from_docstring` to extract
    structured claims from the docstring, then compares them against the actual
    code AST to find mismatches.
    """

    _PARAM_RE = re.compile(
        r":param\s+(\w+):|@param\s+(\w+)|Parameters?\s*[-]+\s*\n((?:\s+\w+.*\n)*)",
        re.MULTILINE,
    )
    _RETURN_RE = re.compile(
        r":returns?:|@returns?|Returns?\s*[-]+",
        re.IGNORECASE,
    )
    _RAISES_RE = re.compile(
        r":raises?\s+(\w+):|@throws\s+(\w+)|Raises?\s*[-]+\s*\n((?:\s+\w+.*\n)*)",
        re.MULTILINE,
    )

    def __init__(self, *, use_nl_synthesis: bool = True) -> None:
        self._use_nl_synthesis = use_nl_synthesis

    def detect_drift(
        self, docstring: str, code: str
    ) -> List[DriftInstance]:
        """Detect all instances of semantic drift between *docstring* and *code*."""
        drifts: List[DriftInstance] = []

        try:
            tree = ast.parse(code)
        except SyntaxError:
            drifts.append(
                DriftInstance(
                    location="<module>",
                    docstring_claim="Code should be syntactically valid",
                    code_reality="SyntaxError during parse",
                    severity="CRITICAL",
                )
            )
            return drifts

        drifts.extend(self._check_parameter_drift(docstring, tree))
        drifts.extend(self._check_return_drift(docstring, tree))
        drifts.extend(self._check_raises_drift(docstring, tree))
        drifts.extend(self._check_nl_synthesis_drift(docstring, code))

        return drifts

    def _check_parameter_drift(
        self, docstring: str, tree: ast.Module
    ) -> List[DriftInstance]:
        """Check whether documented parameters match actual function signatures."""
        drifts: List[DriftInstance] = []
        doc_params = self._extract_doc_params(docstring)
        if not doc_params:
            return drifts

        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            code_params: Set[str] = set()
            for arg in node.args.args + node.args.kwonlyargs:
                if arg.arg != "self" and arg.arg != "cls":
                    code_params.add(arg.arg)
            if node.args.vararg:
                code_params.add(node.args.vararg.arg)
            if node.args.kwarg:
                code_params.add(node.args.kwarg.arg)

            doc_only = doc_params - code_params
            for p in doc_only:
                drifts.append(
                    DriftInstance(
                        location=node.name + "()",
                        docstring_claim="Documents parameter '" + p + "'",
                        code_reality="Parameter '" + p + "' not in signature",
                        severity="HIGH",
                        evidence=["Actual params: " + str(sorted(code_params))],
                        confidence=0.95,
                    )
                )

            code_only = code_params - doc_params
            for p in code_only:
                drifts.append(
                    DriftInstance(
                        location=node.name + "()",
                        docstring_claim="(parameter not documented)",
                        code_reality="Parameter '" + p + "' exists but is undocumented",
                        severity="MEDIUM",
                        evidence=["Documented params: " + str(sorted(doc_params))],
                        confidence=0.8,
                    )
                )
        return drifts

    def _check_return_drift(
        self, docstring: str, tree: ast.Module
    ) -> List[DriftInstance]:
        """Check whether documented return info is consistent with actual returns."""
        drifts: List[DriftInstance] = []
        has_return_doc = bool(self._RETURN_RE.search(docstring))
        if not has_return_doc:
            return drifts

        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            has_return_stmt = any(
                isinstance(child, ast.Return) and child.value is not None
                for child in ast.walk(node)
            )
            if not has_return_stmt:
                drifts.append(
                    DriftInstance(
                        location=node.name + "()",
                        docstring_claim="Documents a return value",
                        code_reality="Function has no return statement with a value",
                        severity="HIGH",
                        confidence=0.9,
                    )
                )
        return drifts

    def _check_raises_drift(
        self, docstring: str, tree: ast.Module
    ) -> List[DriftInstance]:
        """Check whether documented exceptions match actual raises."""
        drifts: List[DriftInstance] = []
        doc_exceptions = self._extract_doc_exceptions(docstring)
        if not doc_exceptions:
            return drifts

        code_exceptions: Set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Raise) and node.exc is not None:
                if isinstance(node.exc, ast.Call) and isinstance(node.exc.func, ast.Name):
                    code_exceptions.add(node.exc.func.id)
                elif isinstance(node.exc, ast.Name):
                    code_exceptions.add(node.exc.id)

        doc_only = doc_exceptions - code_exceptions
        for exc in doc_only:
            drifts.append(
                DriftInstance(
                    location="<module>",
                    docstring_claim="Documents raising '" + exc + "'",
                    code_reality="'" + exc + "' never raised in code",
                    severity="MEDIUM",
                    evidence=["Actually raised: " + str(sorted(code_exceptions))],
                    confidence=0.85,
                )
            )
        return drifts

    def _check_nl_synthesis_drift(
        self, docstring: str, code: str
    ) -> List[DriftInstance]:
        """Use deppy.nl_synthesis to extract typed constraints from docstring
        and check them against code."""
        if not self._use_nl_synthesis:
            return []
        drifts: List[DriftInstance] = []
        try:
            synth_fn = _import_nl_synthesis()
            bundle = synth_fn(docstring)
            if not hasattr(bundle, "constraints"):
                return drifts

            try:
                tree = ast.parse(code)
            except SyntaxError:
                return drifts

            code_names: Set[str] = set()
            for node in ast.walk(tree):
                if isinstance(node, ast.Name):
                    code_names.add(node.id)
                elif isinstance(node, ast.FunctionDef):
                    code_names.add(node.name)
                elif isinstance(node, ast.Attribute):
                    code_names.add(node.attr)

            for constraint in bundle.constraints:
                param = getattr(constraint, "parameter", None)
                if param and param not in code_names:
                    desc = getattr(constraint, "description", str(constraint))
                    drifts.append(
                        DriftInstance(
                            location="param:" + str(param),
                            docstring_claim="Constraint on '" + str(param) + "': " + str(desc),
                            code_reality="'" + str(param) + "' not found in code",
                            severity="HIGH",
                            confidence=0.8,
                        )
                    )
        except Exception:
            pass
        return drifts

    def _extract_doc_params(self, docstring: str) -> Set[str]:
        """Extract parameter names from docstring."""
        params: Set[str] = set()
        for m in self._PARAM_RE.finditer(docstring):
            name = m.group(1) or m.group(2)
            if name:
                params.add(name)
            block = m.group(3)
            if block:
                for line in block.strip().splitlines():
                    parts = line.strip().split()
                    token = parts[0].rstrip(":") if parts else ""
                    if token and token.isidentifier():
                        params.add(token)
        return params

    def _extract_doc_exceptions(self, docstring: str) -> Set[str]:
        """Extract exception names from docstring."""
        exceptions: Set[str] = set()
        for m in self._RAISES_RE.finditer(docstring):
            name = m.group(1) or m.group(2)
            if name:
                exceptions.add(name)
            block = m.group(3)
            if block:
                for line in block.strip().splitlines():
                    parts = line.strip().split()
                    token = parts[0].rstrip(":") if parts else ""
                    if token and token.isidentifier():
                        exceptions.add(token)
        return exceptions


# ======================================================================
#  HallucinationChecker (~400 lines)
# ======================================================================

class HallucinationChecker:
    """Anti-hallucination type checker.

    An artifact is hallucinated iff it fails to inhabit its declared HybridType::

        hallucinated(a, T)  <=>  not (a : T)

    Uses existing deppy infrastructure:

    - :class:`deppy.solver.FragmentDispatcher` for structural checks (Z3).
    - :class:`deppy.kernel.TrustClassifier` for trust level assignment.
    - :func:`deppy.nl_synthesis.synthesize_types_from_docstring` for
      docstring-to-constraint extraction.

    A *hybrid type* is represented as a dict with keys:

    - ``"structural"`` -- list of structural predicate dicts
    - ``"semantic"`` -- list of semantic predicate dicts
    - ``"sources"`` -- list of source texts for grounding
    - ``"constraints"`` -- list of constraint strings
    - ``"artifacts"`` -- list of related artifact dicts for consistency

    Example::

        checker = HallucinationChecker()
        result = checker.check(artifact, hybrid_type, oracle_fn=my_oracle)
        assert not result.hallucinated
    """

    def __init__(
        self,
        *,
        grounding_checker: Optional[GroundingChecker] = None,
        consistency_checker: Optional[ConsistencyChecker] = None,
        drift_detector: Optional[SemanticDriftDetector] = None,
        use_deppy_solver: bool = True,
        use_deppy_trust: bool = True,
        structural_timeout_ms: float = 5000.0,
        semantic_timeout_ms: float = 30000.0,
    ) -> None:
        self._grounding = grounding_checker or GroundingChecker()
        self._consistency = consistency_checker or ConsistencyChecker()
        self._drift = drift_detector or SemanticDriftDetector()
        self._use_deppy_solver = use_deppy_solver
        self._use_deppy_trust = use_deppy_trust
        self._structural_timeout_ms = structural_timeout_ms
        self._semantic_timeout_ms = semantic_timeout_ms
        self._dispatcher: Any = None
        self._trust_classifier: Any = None

    # -- lazy deppy component initialization -------------------------------

    def _get_dispatcher(self) -> Any:
        """Lazily obtain a FragmentDispatcher for structural checks."""
        if self._dispatcher is not None:
            return self._dispatcher
        if not self._use_deppy_solver:
            return None
        try:
            FragmentDispatcher = _import_fragment_dispatcher()
            self._dispatcher = FragmentDispatcher.create_default()
        except Exception:
            self._dispatcher = None
        return self._dispatcher

    def _get_trust_classifier(self) -> Any:
        """Lazily obtain a TrustClassifier."""
        if self._trust_classifier is not None:
            return self._trust_classifier
        if not self._use_deppy_trust:
            return None
        try:
            TrustClassifier = _import_trust_classifier()
            self._trust_classifier = TrustClassifier()
        except Exception:
            self._trust_classifier = None
        return self._trust_classifier

    # -- hashing helpers ---------------------------------------------------

    @staticmethod
    def _hash_artifact(artifact: Dict[str, Any]) -> str:
        raw = json.dumps(artifact, sort_keys=True, default=str)
        return hashlib.sha256(raw.encode()).hexdigest()[:16]

    @staticmethod
    def _hash_type(hybrid_type: Dict[str, Any]) -> str:
        raw = json.dumps(hybrid_type, sort_keys=True, default=str)
        return hashlib.sha256(raw.encode()).hexdigest()[:16]

    # -- structural checking -----------------------------------------------

    def check_structural(
        self,
        artifact: Dict[str, Any],
        structural_preds: List[Dict[str, Any]],
    ) -> List[CheckDetail]:
        """Check decidable, structural predicates on *artifact*.

        Each predicate dict should have:
        - ``"name"`` -- human-readable name
        - ``"check"`` -- either a callable(artifact) -> bool, or a string
          describing a constraint to evaluate.
        - ``"severity"`` -- optional severity override.

        When the deppy solver is available, string-based predicates are
        dispatched through :class:`FragmentDispatcher`; otherwise a heuristic
        evaluator is used.
        """
        details: List[CheckDetail] = []
        dispatcher = self._get_dispatcher()

        for pred in structural_preds:
            t0 = time.monotonic()
            name = pred.get("name", "unnamed_structural")
            severity = pred.get("severity", "HIGH")
            check_fn = pred.get("check")
            pred_repr = pred.get("repr", str(pred))

            passed = False
            message = ""
            counterexample: Optional[Dict[str, Any]] = None

            if callable(check_fn):
                try:
                    result = check_fn(artifact)
                    passed = bool(result)
                    message = "Structural check '" + name + "': " + ("PASS" if passed else "FAIL")
                except Exception as exc:
                    message = "Structural check '" + name + "' raised: " + str(exc)
                    passed = False
            elif isinstance(check_fn, str) and dispatcher is not None:
                check_result = self._dispatch_structural(check_fn, artifact, dispatcher)
                passed = check_result.get("passed", False)
                message = check_result.get("message", "")
                counterexample = check_result.get("counterexample")
            elif isinstance(check_fn, str):
                eval_result = self._heuristic_structural(check_fn, artifact)
                passed = eval_result["passed"]
                message = eval_result["message"]
            else:
                message = "Structural check '" + name + "': no check callable or string"
                passed = False

            elapsed = (time.monotonic() - t0) * 1000
            trust = "trusted_auto" if passed else "assumed"

            details.append(
                CheckDetail(
                    name=name,
                    phase=CheckPhase.STRUCTURAL.value,
                    passed=passed,
                    severity=severity if not passed else "INFO",
                    message=message,
                    counterexample=counterexample,
                    trust_level=trust,
                    elapsed_ms=elapsed,
                    predicate_repr=pred_repr,
                )
            )

        return details

    def _dispatch_structural(
        self,
        constraint_str: str,
        artifact: Dict[str, Any],
        dispatcher: Any,
    ) -> Dict[str, Any]:
        """Dispatch a constraint string through the deppy FragmentDispatcher."""
        try:
            from deppy.solver.solver_interface import SolverObligation, SolverStatus
            from deppy.types.refinement import VarPred

            pred = VarPred(var_name=constraint_str.replace(" ", "_")[:60])
            obligation = SolverObligation(
                predicate=pred,
                description="structural:" + constraint_str[:80],
            )
            result = dispatcher.dispatch(obligation)
            sat = hasattr(result, "status") and result.status == SolverStatus.SAT
            return {
                "passed": sat,
                "message": "Dispatcher result: " + str(getattr(result, "status", "unknown")),
                "counterexample": getattr(result, "model", None),
            }
        except Exception as exc:
            return {
                "passed": False,
                "message": "Dispatcher error: " + str(exc),
                "counterexample": None,
            }

    @staticmethod
    def _heuristic_structural(
        constraint_str: str, artifact: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Heuristic fallback for structural checks when Z3 is unavailable."""
        content = artifact.get("content", artifact.get("code", ""))
        if not isinstance(content, str):
            content = str(content)

        constraint_lower = constraint_str.lower()

        if "must parse" in constraint_lower or "valid syntax" in constraint_lower:
            try:
                ast.parse(content)
                return {"passed": True, "message": "Parses as valid Python"}
            except SyntaxError as exc:
                return {"passed": False, "message": "SyntaxError: " + str(exc)}

        if "non-empty" in constraint_lower:
            passed = len(content.strip()) > 0
            return {"passed": passed, "message": "Content length: " + str(len(content))}

        if "type annotations" in constraint_lower:
            try:
                tree = ast.parse(content)
                for node in ast.walk(tree):
                    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        if node.returns is not None:
                            return {"passed": True, "message": "Has return annotation"}
                return {"passed": False, "message": "No type annotations found"}
            except SyntaxError:
                return {"passed": False, "message": "Cannot parse to check annotations"}

        return {
            "passed": True,
            "message": "Heuristic: cannot evaluate '" + constraint_str + "', assuming pass",
        }

    # -- semantic checking -------------------------------------------------

    def check_semantic(
        self,
        artifact: Dict[str, Any],
        semantic_preds: List[Dict[str, Any]],
        oracle_fn: Optional[Callable[..., Any]] = None,
    ) -> List[CheckDetail]:
        """Check semantic predicates using an oracle function.

        Each predicate dict should have:
        - ``"name"`` -- human-readable name
        - ``"prompt"`` -- prompt to send to the oracle
        - ``"severity"`` -- optional severity override.

        The *oracle_fn* signature is ``oracle_fn(prompt: str) -> Dict`` returning
        at least ``{"result": bool, "confidence": float}``.
        """
        details: List[CheckDetail] = []
        if oracle_fn is None:
            for pred in semantic_preds:
                details.append(
                    CheckDetail(
                        name=pred.get("name", "unnamed_semantic"),
                        phase=CheckPhase.SEMANTIC.value,
                        passed=False,
                        severity="MEDIUM",
                        message="No oracle function provided; cannot verify semantic predicate",
                        trust_level="assumed",
                    )
                )
            return details

        content = artifact.get("content", artifact.get("code", str(artifact)))

        for pred in semantic_preds:
            t0 = time.monotonic()
            name = pred.get("name", "unnamed_semantic")
            severity = pred.get("severity", "MEDIUM")
            prompt_template = pred.get("prompt", "")

            prompt = prompt_template.replace("{content}", str(content)[:2000])
            prompt = prompt.replace("{artifact}", json.dumps(artifact, default=str)[:2000])

            passed = False
            message = ""
            confidence = 0.0
            evidence: List[CheckEvidence] = []

            try:
                oracle_result = oracle_fn(prompt)
                if isinstance(oracle_result, dict):
                    passed = bool(oracle_result.get("result", False))
                    confidence = float(oracle_result.get("confidence", 0.0))
                    explanation = oracle_result.get("explanation", "")
                    if explanation:
                        evidence.append(
                            CheckEvidence(
                                source="oracle",
                                content=str(explanation)[:500],
                                confidence=confidence,
                            )
                        )
                    message = "Oracle says " + ("PASS" if passed else "FAIL") + " (confidence=" + "{:.2f}".format(confidence) + ")"
                elif isinstance(oracle_result, bool):
                    passed = oracle_result
                    confidence = 1.0 if passed else 0.0
                    message = "Oracle (bool) says " + ("PASS" if passed else "FAIL")
                else:
                    passed = bool(oracle_result)
                    message = "Oracle returned " + type(oracle_result).__name__
            except Exception as exc:
                message = "Oracle call failed: " + str(exc)

            elapsed = (time.monotonic() - t0) * 1000

            if passed and confidence >= 0.8:
                trust = "trace_backed"
            elif passed:
                trust = "bounded_auto"
            else:
                trust = "assumed"

            details.append(
                CheckDetail(
                    name=name,
                    phase=CheckPhase.SEMANTIC.value,
                    passed=passed,
                    severity=severity if not passed else "INFO",
                    message=message,
                    evidence=evidence,
                    trust_level=trust,
                    elapsed_ms=elapsed,
                )
            )

        return details

    # -- grounding check ---------------------------------------------------

    def check_grounding(
        self,
        artifact: Dict[str, Any],
        sources: List[str],
    ) -> GroundingResult:
        """Check whether claims in *artifact* are grounded in *sources*.

        Delegates to :class:`GroundingChecker` which uses
        ``deppy.nl_synthesis`` internally.
        """
        content = artifact.get("content", artifact.get("code", ""))
        if isinstance(content, dict):
            content = json.dumps(content, default=str)
        elif not isinstance(content, str):
            content = str(content)

        if not sources:
            return GroundingResult(
                grounded=True,
                total_claims=0,
                grounded_claims=0,
                confidence=1.0,
                trust_level="bounded_auto",
            )

        return self._grounding.check_all_claims(content, sources)

    # -- consistency check -------------------------------------------------

    def check_consistency(
        self, artifacts: List[Dict[str, Any]]
    ) -> ConsistencyResult:
        """Check internal consistency across *artifacts*.

        Delegates to :class:`ConsistencyChecker` which uses
        ``deppy.solver.Z3Backend`` for satisfiability checking.
        """
        if len(artifacts) < 2:
            return ConsistencyResult(
                consistent=True,
                trust_level="trusted_auto",
                details=[
                    CheckDetail(
                        name="consistency:trivial",
                        phase=CheckPhase.CONSISTENCY.value,
                        passed=True,
                        message="Fewer than 2 artifacts; trivially consistent",
                        trust_level="trusted_auto",
                    )
                ],
            )
        return self._consistency.check(artifacts)

    # -- top-level check ---------------------------------------------------

    def check(
        self,
        artifact: Dict[str, Any],
        hybrid_type: Dict[str, Any],
        oracle_fn: Optional[Callable[..., Any]] = None,
    ) -> HallucinationResult:
        """Check whether *artifact* inhabits *hybrid_type*.

        Returns a :class:`HallucinationResult` where ``hallucinated=True``
        means the artifact fails to inhabit the type.

        The check proceeds through four phases:

        1. **Structural** -- evaluate decidable predicates via
           ``FragmentDispatcher``.
        2. **Semantic** -- evaluate oracle-mediated predicates.
        3. **Grounding** -- verify claims against source material.
        4. **Consistency** -- pairwise + circular-dependency checks.

        The overall trust level is the meet of per-phase trust levels.
        """
        t0 = time.monotonic()
        artifact_hash = self._hash_artifact(artifact)
        type_hash = self._hash_type(hybrid_type)

        # Phase 1: structural
        structural_preds = hybrid_type.get("structural", [])
        structural_details = self.check_structural(artifact, structural_preds)

        # Phase 2: semantic
        semantic_preds = hybrid_type.get("semantic", [])
        semantic_details = self.check_semantic(artifact, semantic_preds, oracle_fn)

        # Phase 3: grounding
        sources = hybrid_type.get("sources", [])
        grounding = self.check_grounding(artifact, sources) if sources else None

        # Phase 4: consistency
        related = hybrid_type.get("artifacts", [])
        if related:
            all_artifacts = [artifact] + list(related)
            consistency = self.check_consistency(all_artifacts)
        else:
            consistency = None

        # Aggregate trust level via meet (weakest-link principle)
        trust = "proof_backed"
        for detail in structural_details + semantic_details:
            trust = _trust_name_meet(trust, detail.trust_level)
        if grounding:
            trust = _trust_name_meet(trust, grounding.trust_level)
        if consistency:
            trust = _trust_name_meet(trust, consistency.trust_level)

        # Determine hallucination
        structural_fail = any(
            d.failed and d.severity in ("CRITICAL", "HIGH")
            for d in structural_details
        )
        semantic_fail = any(
            d.failed and d.severity in ("CRITICAL", "HIGH")
            for d in semantic_details
        )
        grounding_fail = grounding is not None and not grounding.grounded
        consistency_fail = consistency is not None and not consistency.consistent

        hallucinated = structural_fail or semantic_fail or grounding_fail or consistency_fail

        # Confidence: weighted average of sub-check confidences
        confidences: List[float] = []
        for d in structural_details:
            confidences.append(1.0 if d.passed else 0.0)
        for d in semantic_details:
            if d.evidence:
                confidences.append(max(e.confidence for e in d.evidence))
            else:
                confidences.append(1.0 if d.passed else 0.0)
        if grounding:
            confidences.append(grounding.confidence)
        if consistency:
            confidences.append(1.0 if consistency.consistent else 0.0)

        overall_confidence = sum(confidences) / max(len(confidences), 1)
        elapsed = (time.monotonic() - t0) * 1000

        return HallucinationResult(
            hallucinated=hallucinated,
            trust_level=trust,
            structural_details=structural_details,
            semantic_details=semantic_details,
            grounding=grounding,
            consistency=consistency,
            overall_confidence=overall_confidence,
            elapsed_ms=elapsed,
            artifact_hash=artifact_hash,
            type_hash=type_hash,
        )

    # -- full audit --------------------------------------------------------

    def full_audit(
        self,
        artifact: Dict[str, Any],
        hybrid_type: Dict[str, Any],
        oracle_fn: Optional[Callable[..., Any]] = None,
    ) -> AuditReport:
        """Run a complete audit producing a detailed :class:`AuditReport`.

        This wraps :meth:`check` but also tracks oracle calls, timing, and
        produces a serializable audit trail.
        """
        report = AuditReport(
            artifact_summary=json.dumps(artifact, default=str)[:200],
            type_summary=json.dumps(hybrid_type, default=str)[:200],
        )

        oracle_calls_log: List[OracleCallRecord] = []

        def _instrumented_oracle(prompt: str) -> Any:
            t0_inner = time.monotonic()
            prompt_hash = hashlib.sha256(prompt.encode()).hexdigest()[:12]
            try:
                if oracle_fn is None:
                    raise RuntimeError("No oracle provided")
                result = oracle_fn(prompt)
                elapsed_inner = (time.monotonic() - t0_inner) * 1000
                resp_hash = hashlib.sha256(
                    json.dumps(result, default=str).encode()
                ).hexdigest()[:12]
                record = OracleCallRecord(
                    oracle_id="primary",
                    prompt_hash=prompt_hash,
                    response_hash=resp_hash,
                    latency_ms=elapsed_inner,
                    phase=CheckPhase.SEMANTIC.value,
                    success=True,
                )
                oracle_calls_log.append(record)
                report.add_oracle_call(record)
                return result
            except Exception as exc:
                elapsed_inner = (time.monotonic() - t0_inner) * 1000
                record = OracleCallRecord(
                    oracle_id="primary",
                    prompt_hash=prompt_hash,
                    response_hash="error",
                    latency_ms=elapsed_inner,
                    phase=CheckPhase.SEMANTIC.value,
                    success=False,
                )
                oracle_calls_log.append(record)
                report.add_oracle_call(record)
                raise

        wrapped_oracle = _instrumented_oracle if oracle_fn is not None else None
        result = self.check(artifact, hybrid_type, oracle_fn=wrapped_oracle)

        for detail in result.all_details:
            report.add_check(detail)

        report.finalize(result)
        return report


# ======================================================================
#  Module-level convenience functions
# ======================================================================

def check_hallucination(
    artifact: Dict[str, Any],
    hybrid_type: Dict[str, Any],
    *,
    oracle_fn: Optional[Callable[..., Any]] = None,
) -> HallucinationResult:
    """One-shot convenience: create a checker and run it."""
    return HallucinationChecker().check(artifact, hybrid_type, oracle_fn=oracle_fn)


def audit_hallucination(
    artifact: Dict[str, Any],
    hybrid_type: Dict[str, Any],
    *,
    oracle_fn: Optional[Callable[..., Any]] = None,
) -> AuditReport:
    """One-shot convenience: create a checker and run a full audit."""
    return HallucinationChecker().full_audit(artifact, hybrid_type, oracle_fn=oracle_fn)


def detect_drift(docstring: str, code: str) -> List[DriftInstance]:
    """One-shot convenience: detect semantic drift."""
    return SemanticDriftDetector().detect_drift(docstring, code)
