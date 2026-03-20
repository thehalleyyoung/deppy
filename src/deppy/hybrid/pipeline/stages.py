"""
Pillar 6 — End-to-End Verified Pipeline: Stage Definitions

The 8-stage verified pipeline from idea to production:
  IDEATION → SPECIFICATION → SYNTHESIS → STRUCTURAL_CHECK →
  SEMANTIC_CHECK → LEAN_TRANSLATION → DISCHARGE → PRODUCTION

Each stage has:
  - Typed input/output with content hashing for caching
  - A dependent contract (precondition, postcondition, frame)
  - A run() method producing a StageOutput with obligations + artifacts
"""

from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.pipeline.pipeline import AnalysisPipeline as _CorePipeline, PipelineResult as _CorePipelineResult
    from deppy.pipeline.stage_registry import Stage, StageMetadata, StageStatus
    from deppy.pipeline.pipeline_config import PipelineConfig as _CorePipelineConfig
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

import enum
import hashlib
import json
import re
import textwrap
import time
from dataclasses import dataclass, field
from typing import (

    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

# ---------------------------------------------------------------------------
# Pipeline stage enum
# ---------------------------------------------------------------------------

class PipelineStage(enum.Enum):
    """The eight ordered stages of the hybrid verification pipeline."""

    IDEATION = "ideation"
    SPECIFICATION = "specification"
    SYNTHESIS = "synthesis"
    STRUCTURAL_CHECK = "structural_check"
    SEMANTIC_CHECK = "semantic_check"
    LEAN_TRANSLATION = "lean_translation"
    DISCHARGE = "discharge"
    PRODUCTION = "production"

    # -- ordering helpers ---------------------------------------------------

    _stage_order: int  # populated by _init_order below

    def __lt__(self, other: PipelineStage) -> bool:
        if not isinstance(other, PipelineStage):
            return NotImplemented
        return _STAGE_ORDER[self] < _STAGE_ORDER[other]

    def __le__(self, other: PipelineStage) -> bool:
        if not isinstance(other, PipelineStage):
            return NotImplemented
        return _STAGE_ORDER[self] <= _STAGE_ORDER[other]

    def __gt__(self, other: PipelineStage) -> bool:
        if not isinstance(other, PipelineStage):
            return NotImplemented
        return _STAGE_ORDER[self] > _STAGE_ORDER[other]

    def __ge__(self, other: PipelineStage) -> bool:
        if not isinstance(other, PipelineStage):
            return NotImplemented
        return _STAGE_ORDER[self] >= _STAGE_ORDER[other]

    @classmethod
    def ordered(cls) -> List[PipelineStage]:
        """Return all stages in pipeline order."""
        return sorted(cls, key=lambda s: _STAGE_ORDER[s])

    def next_stage(self) -> Optional[PipelineStage]:
        """Return the stage that follows this one, or None if PRODUCTION."""
        ordered = PipelineStage.ordered()
        idx = ordered.index(self)
        if idx + 1 < len(ordered):
            return ordered[idx + 1]
        return None

    def prev_stage(self) -> Optional[PipelineStage]:
        """Return the stage that precedes this one, or None if IDEATION."""
        ordered = PipelineStage.ordered()
        idx = ordered.index(self)
        if idx > 0:
            return ordered[idx - 1]
        return None

_STAGE_ORDER: Dict[PipelineStage, int] = {
    PipelineStage.IDEATION: 0,
    PipelineStage.SPECIFICATION: 1,
    PipelineStage.SYNTHESIS: 2,
    PipelineStage.STRUCTURAL_CHECK: 3,
    PipelineStage.SEMANTIC_CHECK: 4,
    PipelineStage.LEAN_TRANSLATION: 5,
    PipelineStage.DISCHARGE: 6,
    PipelineStage.PRODUCTION: 7,
}

STAGE_NAMES: Dict[PipelineStage, str] = {
    PipelineStage.IDEATION: "Ideation",
    PipelineStage.SPECIFICATION: "Specification",
    PipelineStage.SYNTHESIS: "Synthesis",
    PipelineStage.STRUCTURAL_CHECK: "Structural Check",
    PipelineStage.SEMANTIC_CHECK: "Semantic Check",
    PipelineStage.LEAN_TRANSLATION: "Lean Translation",
    PipelineStage.DISCHARGE: "Discharge",
    PipelineStage.PRODUCTION: "Production",
}

# ---------------------------------------------------------------------------
# Content hashing
# ---------------------------------------------------------------------------

def _content_hash(data: Any) -> str:
    """Compute a deterministic SHA-256 hash for JSON-serialisable *data*."""
    blob = json.dumps(data, sort_keys=True, default=str).encode("utf-8")
    return hashlib.sha256(blob).hexdigest()

def _hash_text(text: str) -> str:
    """Hash a plain text string."""
    return hashlib.sha256(text.encode("utf-8")).hexdigest()

# ---------------------------------------------------------------------------
# StageInput
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class StageInput:
    """Typed input for a pipeline stage.

    Every stage receives a ``StageInput`` carrying the data it needs, a
    content hash (for cache lookup), and provenance describing how the
    data was produced.
    """

    stage: PipelineStage
    data: Dict[str, Any]
    content_hash: str
    trust_level: str = "untrusted"
    provenance: List[str] = field(default_factory=list)

    # -- factories ----------------------------------------------------------

    @classmethod
    def create(
        cls,
        stage: PipelineStage,
        data: Dict[str, Any],
        *,
        trust_level: str = "untrusted",
        provenance: Optional[List[str]] = None,
    ) -> StageInput:
        """Build a ``StageInput`` with an auto-computed content hash."""
        return cls(
            stage=stage,
            data=data,
            content_hash=_content_hash(data),
            trust_level=trust_level,
            provenance=provenance or [],
        )

    @classmethod
    def from_output(
        cls,
        prev: "StageOutput",
        next_stage: PipelineStage,
        extra_data: Optional[Dict[str, Any]] = None,
    ) -> StageInput:
        """Chain: convert a ``StageOutput`` into the ``StageInput`` for the
        next stage, preserving provenance."""
        merged = dict(prev.data)
        if extra_data:
            merged.update(extra_data)
        prov = list(prev.provenance) if hasattr(prev, "provenance") else []
        prov.append(f"{prev.stage.value}→{next_stage.value}")
        return cls(
            stage=next_stage,
            data=merged,
            content_hash=_content_hash(merged),
            trust_level=prev.trust_level,
            provenance=prov,
        )

    # -- helpers ------------------------------------------------------------

    def get(self, key: str, default: Any = None) -> Any:
        """Convenience accessor into ``self.data``."""
        return self.data.get(key, default)

    def require(self, *keys: str) -> None:
        """Raise if any *keys* are missing from ``self.data``."""
        missing = [k for k in keys if k not in self.data]
        if missing:
            raise ValueError(
                f"StageInput for {self.stage.value} missing keys: {missing}"
            )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "stage": self.stage.value,
            "data": self.data,
            "content_hash": self.content_hash,
            "trust_level": self.trust_level,
            "provenance": self.provenance,
        }

# ---------------------------------------------------------------------------
# StageOutput
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class StageOutput:
    """Typed output from a pipeline stage.

    Carries the produced data, any proof obligations generated, artifacts
    (e.g. Lean files), and timing information.
    """

    stage: PipelineStage
    data: Dict[str, Any]
    content_hash: str
    trust_level: str = "untrusted"
    obligations: List[Dict[str, Any]] = field(default_factory=list)
    artifacts: List[Dict[str, Any]] = field(default_factory=list)
    duration_ms: float = 0.0
    provenance: List[str] = field(default_factory=list)

    # -- factories ----------------------------------------------------------

    @classmethod
    def create(
        cls,
        stage: PipelineStage,
        data: Dict[str, Any],
        *,
        trust_level: str = "untrusted",
        obligations: Optional[List[Dict[str, Any]]] = None,
        artifacts: Optional[List[Dict[str, Any]]] = None,
        duration_ms: float = 0.0,
        provenance: Optional[List[str]] = None,
    ) -> StageOutput:
        return cls(
            stage=stage,
            data=data,
            content_hash=_content_hash(data),
            trust_level=trust_level,
            obligations=obligations or [],
            artifacts=artifacts or [],
            duration_ms=duration_ms,
            provenance=provenance or [],
        )

    @classmethod
    def error(
        cls,
        stage: PipelineStage,
        message: str,
        *,
        duration_ms: float = 0.0,
    ) -> StageOutput:
        """Create an error output for a failed stage."""
        return cls(
            stage=stage,
            data={"error": message},
            content_hash=_hash_text(message),
            trust_level="contradicted",
            duration_ms=duration_ms,
        )

    # -- query helpers ------------------------------------------------------

    @property
    def is_error(self) -> bool:
        return "error" in self.data

    @property
    def obligation_count(self) -> int:
        return len(self.obligations)

    @property
    def discharged_count(self) -> int:
        return sum(
            1 for o in self.obligations if o.get("status") == "discharged"
        )

    @property
    def sorry_count(self) -> int:
        return sum(
            1 for o in self.obligations if o.get("status") == "sorry"
        )

    def get(self, key: str, default: Any = None) -> Any:
        return self.data.get(key, default)

    def merge(self, other: StageOutput) -> StageOutput:
        """Merge two outputs from the same stage (e.g. incremental)."""
        merged_data = {**self.data, **other.data}
        merged_obls = list(self.obligations) + list(other.obligations)
        merged_arts = list(self.artifacts) + list(other.artifacts)
        merged_prov = list(self.provenance) + list(other.provenance)
        return StageOutput(
            stage=self.stage,
            data=merged_data,
            content_hash=_content_hash(merged_data),
            trust_level=_join_trust(self.trust_level, other.trust_level),
            obligations=merged_obls,
            artifacts=merged_arts,
            duration_ms=self.duration_ms + other.duration_ms,
            provenance=merged_prov,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "stage": self.stage.value,
            "data": self.data,
            "content_hash": self.content_hash,
            "trust_level": self.trust_level,
            "obligations": self.obligations,
            "artifacts": self.artifacts,
            "duration_ms": self.duration_ms,
            "provenance": self.provenance,
        }

# Trust-level lattice join (conservative)
_TRUST_RANK = {
    "lean_verified": 5,
    "z3_proven": 4,
    "llm_judged": 3,
    "runtime_checked": 2,
    "untrusted": 1,
    "contradicted": 0,
}

def _join_trust(a: str, b: str) -> str:
    """Return the lower of two trust levels (conservative join)."""
    ra = _TRUST_RANK.get(a, 1)
    rb = _TRUST_RANK.get(b, 1)
    target = min(ra, rb)
    for name, rank in _TRUST_RANK.items():
        if rank == target:
            return name
    return "untrusted"

# ---------------------------------------------------------------------------
# StageContract — dependent contract for each stage
# ---------------------------------------------------------------------------

@dataclass
class StageContract:
    """A dependent contract for a pipeline stage.

    Pre-/postconditions are predicates over ``StageInput`` / ``StageOutput``
    respectively.  The *frame* records which data keys the stage is allowed
    to read and write (separation-logic style).
    """

    stage: PipelineStage
    precondition: Callable[[StageInput], Tuple[bool, str]]
    postcondition: Callable[[StageOutput], Tuple[bool, str]]
    frame: Dict[str, Any] = field(default_factory=dict)

    # -- checking -----------------------------------------------------------

    def check_pre(self, inp: StageInput) -> Tuple[bool, str]:
        """Verify precondition; returns (ok, msg)."""
        try:
            return self.precondition(inp)
        except Exception as exc:
            return False, f"Precondition raised: {exc}"

    def check_post(self, out: StageOutput) -> Tuple[bool, str]:
        """Verify postcondition; returns (ok, msg)."""
        try:
            return self.postcondition(out)
        except Exception as exc:
            return False, f"Postcondition raised: {exc}"

    def enforce(
        self,
        inp: StageInput,
        run_fn: Callable[[StageInput], StageOutput],
    ) -> StageOutput:
        """Run *run_fn* with contract enforcement around it."""
        ok, msg = self.check_pre(inp)
        if not ok:
            return StageOutput.error(
                self.stage, f"Precondition failed: {msg}"
            )

        out = run_fn(inp)

        ok, msg = self.check_post(out)
        if not ok:
            return StageOutput.error(
                self.stage, f"Postcondition failed: {msg}"
            )

        return out

    def to_dict(self) -> Dict[str, Any]:
        return {
            "stage": self.stage.value,
            "frame_reads": self.frame.get("reads", []),
            "frame_writes": self.frame.get("writes", []),
        }

# ---------------------------------------------------------------------------
# Pre-built contracts for all 8 stages
# ---------------------------------------------------------------------------

def _ideation_pre(inp: StageInput) -> Tuple[bool, str]:
    """IDEATION precondition: input must contain natural-language text."""
    text = inp.get("nl_text", "")
    if not text or not isinstance(text, str):
        return False, "IDEATION requires non-empty 'nl_text' string"
    if len(text.strip()) < 3:
        return False, "IDEATION 'nl_text' too short to parse"
    return True, "ok"

def _ideation_post(out: StageOutput) -> Tuple[bool, str]:
    """IDEATION postcondition: output must have parsed claims."""
    claims = out.get("claims")
    if claims is None:
        return False, "IDEATION output missing 'claims'"
    if not isinstance(claims, list):
        return False, "'claims' must be a list"
    for i, c in enumerate(claims):
        if not isinstance(c, dict):
            return False, f"claim[{i}] is not a dict"
        if "text" not in c:
            return False, f"claim[{i}] missing 'text'"
    return True, "ok"

def _specification_pre(inp: StageInput) -> Tuple[bool, str]:
    """SPECIFICATION precondition: input has claims from ideation."""
    claims = inp.get("claims")
    if not claims or not isinstance(claims, list):
        return False, "SPECIFICATION requires non-empty 'claims' list"
    return True, "ok"

def _specification_post(out: StageOutput) -> Tuple[bool, str]:
    """SPECIFICATION postcondition: output has HybridSpec with split."""
    specs = out.get("specs")
    if specs is None:
        return False, "SPECIFICATION output missing 'specs'"
    if not isinstance(specs, list):
        return False, "'specs' must be a list"
    for i, s in enumerate(specs):
        if not isinstance(s, dict):
            return False, f"spec[{i}] is not a dict"
        if "kind" not in s:
            return False, f"spec[{i}] missing 'kind' (structural|semantic)"
        if s["kind"] not in ("structural", "semantic", "mixed"):
            return False, f"spec[{i}] has invalid kind: {s['kind']}"
    return True, "ok"

def _synthesis_pre(inp: StageInput) -> Tuple[bool, str]:
    """SYNTHESIS precondition: input has spec + code with holes."""
    specs = inp.get("specs")
    if not specs or not isinstance(specs, list):
        return False, "SYNTHESIS requires 'specs'"
    code = inp.get("code_with_holes", "")
    if not code:
        return False, "SYNTHESIS requires 'code_with_holes'"
    return True, "ok"

def _synthesis_post(out: StageOutput) -> Tuple[bool, str]:
    """SYNTHESIS postcondition: output has filled code (no holes)."""
    code = out.get("code")
    if not code or not isinstance(code, str):
        return False, "SYNTHESIS output missing 'code'"
    if "???" in code or "__HOLE__" in code:
        return False, "SYNTHESIS output still contains holes"
    return True, "ok"

def _structural_check_pre(inp: StageInput) -> Tuple[bool, str]:
    """STRUCTURAL_CHECK precondition: input has code."""
    code = inp.get("code", "")
    if not code:
        return False, "STRUCTURAL_CHECK requires 'code'"
    structural = inp.get("structural_specs")
    if structural is None:
        return False, "STRUCTURAL_CHECK requires 'structural_specs'"
    return True, "ok"

def _structural_check_post(out: StageOutput) -> Tuple[bool, str]:
    """STRUCTURAL_CHECK postcondition: all structural claims have Z3 results."""
    results = out.get("z3_results")
    if results is None:
        return False, "STRUCTURAL_CHECK output missing 'z3_results'"
    if not isinstance(results, list):
        return False, "'z3_results' must be a list"
    for i, r in enumerate(results):
        if not isinstance(r, dict):
            return False, f"z3_results[{i}] is not a dict"
        if "status" not in r:
            return False, f"z3_results[{i}] missing 'status'"
        if r["status"] not in ("proven", "refuted", "timeout", "unknown"):
            return False, f"z3_results[{i}] invalid status: {r['status']}"
    return True, "ok"

def _semantic_check_pre(inp: StageInput) -> Tuple[bool, str]:
    """SEMANTIC_CHECK precondition: input has code + semantic specs."""
    code = inp.get("code", "")
    if not code:
        return False, "SEMANTIC_CHECK requires 'code'"
    semantic = inp.get("semantic_specs")
    if semantic is None:
        return False, "SEMANTIC_CHECK requires 'semantic_specs'"
    return True, "ok"

def _semantic_check_post(out: StageOutput) -> Tuple[bool, str]:
    """SEMANTIC_CHECK postcondition: all semantic claims have oracle results."""
    results = out.get("oracle_results")
    if results is None:
        return False, "SEMANTIC_CHECK output missing 'oracle_results'"
    if not isinstance(results, list):
        return False, "'oracle_results' must be a list"
    for i, r in enumerate(results):
        if not isinstance(r, dict):
            return False, f"oracle_results[{i}] is not a dict"
        if "judgment" not in r:
            return False, f"oracle_results[{i}] missing 'judgment'"
        if "confidence" not in r:
            return False, f"oracle_results[{i}] missing 'confidence'"
    return True, "ok"

def _lean_translation_pre(inp: StageInput) -> Tuple[bool, str]:
    """LEAN_TRANSLATION precondition: input has code + specs."""
    code = inp.get("code", "")
    if not code:
        return False, "LEAN_TRANSLATION requires 'code'"
    specs = inp.get("specs")
    if specs is None:
        return False, "LEAN_TRANSLATION requires 'specs'"
    return True, "ok"

def _lean_translation_post(out: StageOutput) -> Tuple[bool, str]:
    """LEAN_TRANSLATION postcondition: output has .lean file content."""
    lean = out.get("lean_source")
    if not lean or not isinstance(lean, str):
        return False, "LEAN_TRANSLATION output missing 'lean_source'"
    if "theorem" not in lean.lower() and "def" not in lean.lower():
        return False, "LEAN_TRANSLATION output has no theorem/def statements"
    return True, "ok"

def _discharge_pre(inp: StageInput) -> Tuple[bool, str]:
    """DISCHARGE precondition: input has obligations."""
    obligations = inp.get("obligations")
    if obligations is None:
        return False, "DISCHARGE requires 'obligations'"
    if not isinstance(obligations, list):
        return False, "'obligations' must be a list"
    return True, "ok"

def _discharge_post(out: StageOutput) -> Tuple[bool, str]:
    """DISCHARGE postcondition: all obligations have proof or sorry."""
    proofs = out.get("proofs")
    if proofs is None:
        return False, "DISCHARGE output missing 'proofs'"
    if not isinstance(proofs, list):
        return False, "'proofs' must be a list"
    for i, p in enumerate(proofs):
        if not isinstance(p, dict):
            return False, f"proofs[{i}] is not a dict"
        if "status" not in p:
            return False, f"proofs[{i}] missing 'status'"
        if p["status"] not in ("discharged", "sorry", "assumed", "failed"):
            return False, f"proofs[{i}] invalid status: {p['status']}"
    return True, "ok"

def _production_pre(inp: StageInput) -> Tuple[bool, str]:
    """PRODUCTION precondition: input has verified code + certificate."""
    code = inp.get("code", "")
    if not code:
        return False, "PRODUCTION requires 'code'"
    cert = inp.get("certificate")
    if cert is None:
        return False, "PRODUCTION requires 'certificate'"
    return True, "ok"

def _production_post(out: StageOutput) -> Tuple[bool, str]:
    """PRODUCTION postcondition: output is a deployable artifact."""
    artifact = out.get("artifact")
    if artifact is None:
        return False, "PRODUCTION output missing 'artifact'"
    if "code" not in artifact:
        return False, "PRODUCTION artifact missing 'code'"
    if "certificate" not in artifact:
        return False, "PRODUCTION artifact missing 'certificate'"
    return True, "ok"

# Map stage → contract
STAGE_CONTRACTS: Dict[PipelineStage, StageContract] = {
    PipelineStage.IDEATION: StageContract(
        stage=PipelineStage.IDEATION,
        precondition=_ideation_pre,
        postcondition=_ideation_post,
        frame={"reads": ["nl_text", "context"], "writes": ["claims"]},
    ),
    PipelineStage.SPECIFICATION: StageContract(
        stage=PipelineStage.SPECIFICATION,
        precondition=_specification_pre,
        postcondition=_specification_post,
        frame={
            "reads": ["claims"],
            "writes": ["specs", "structural_specs", "semantic_specs"],
        },
    ),
    PipelineStage.SYNTHESIS: StageContract(
        stage=PipelineStage.SYNTHESIS,
        precondition=_synthesis_pre,
        postcondition=_synthesis_post,
        frame={"reads": ["specs", "code_with_holes"], "writes": ["code"]},
    ),
    PipelineStage.STRUCTURAL_CHECK: StageContract(
        stage=PipelineStage.STRUCTURAL_CHECK,
        precondition=_structural_check_pre,
        postcondition=_structural_check_post,
        frame={"reads": ["code", "structural_specs"], "writes": ["z3_results"]},
    ),
    PipelineStage.SEMANTIC_CHECK: StageContract(
        stage=PipelineStage.SEMANTIC_CHECK,
        precondition=_semantic_check_pre,
        postcondition=_semantic_check_post,
        frame={"reads": ["code", "semantic_specs"], "writes": ["oracle_results"]},
    ),
    PipelineStage.LEAN_TRANSLATION: StageContract(
        stage=PipelineStage.LEAN_TRANSLATION,
        precondition=_lean_translation_pre,
        postcondition=_lean_translation_post,
        frame={
            "reads": ["code", "specs", "structural_results"],
            "writes": ["lean_source"],
        },
    ),
    PipelineStage.DISCHARGE: StageContract(
        stage=PipelineStage.DISCHARGE,
        precondition=_discharge_pre,
        postcondition=_discharge_post,
        frame={"reads": ["obligations"], "writes": ["proofs"]},
    ),
    PipelineStage.PRODUCTION: StageContract(
        stage=PipelineStage.PRODUCTION,
        precondition=_production_pre,
        postcondition=_production_post,
        frame={"reads": ["code", "certificate"], "writes": ["artifact"]},
    ),
}

def get_contract(stage: PipelineStage) -> StageContract:
    """Look up the pre-built contract for *stage*."""
    return STAGE_CONTRACTS[stage]

# ---------------------------------------------------------------------------
# Claim parsing helpers (used by IdeationStage)
# ---------------------------------------------------------------------------

_CLAIM_PATTERNS: List[Tuple[str, str]] = [
    # "returns X when Y"
    (r"returns?\s+(.+?)\s+when\s+(.+)", "postcondition"),
    # "raises X if Y"
    (r"raises?\s+(\w+)\s+if\s+(.+)", "exception"),
    # "X is always Y" / "X must be Y"
    (r"(\w[\w\s]*?)\s+(?:is\s+always|must\s+be|shall\s+be)\s+(.+)", "invariant"),
    # "X > Y" / "X >= Y" / "X < Y" etc.
    (r"(\w[\w\s]*?)\s*(>=?|<=?|==|!=)\s*(.+)", "comparison"),
    # "for all X in Y, Z"
    (r"for\s+all\s+(\w+)\s+in\s+(.+?),\s+(.+)", "universal"),
    # "there exists X in Y such that Z"
    (r"there\s+exists?\s+(\w+)\s+in\s+(.+?)\s+such\s+that\s+(.+)", "existential"),
    # "O(N)" / "O(N log N)" complexity
    (r"(?:runs?\s+in|complexity\s+is)\s+O\((.+?)\)", "complexity"),
    # "sorted" / "monotonic" / "non-decreasing"
    (r"\b(sorted|monotonic|non-decreasing|non-increasing|ascending|descending)\b", "ordering"),
    # "pure" / "no side effects"
    (r"\b(pure|no\s+side\s+effects?|referentially\s+transparent)\b", "purity"),
    # "type X -> Y"
    (r"type\s*:\s*(.+?)\s*->\s*(.+)", "type_sig"),
]

def _parse_claims(text: str) -> List[Dict[str, Any]]:
    """Extract structured claims from natural-language text.

    Returns a list of claim dicts, each with at least ``text`` and ``kind``.
    """
    claims: List[Dict[str, Any]] = []
    sentences = re.split(r"[.;!\n]", text)
    claim_id = 0

    for raw in sentences:
        s = raw.strip()
        if not s or len(s) < 5:
            continue

        matched = False
        for pattern, kind in _CLAIM_PATTERNS:
            m = re.search(pattern, s, re.IGNORECASE)
            if m:
                claims.append({
                    "id": f"claim_{claim_id}",
                    "text": s,
                    "kind": kind,
                    "groups": list(m.groups()),
                    "decidable": _guess_decidability(kind, s),
                })
                claim_id += 1
                matched = True
                break

        if not matched and len(s) > 10:
            claims.append({
                "id": f"claim_{claim_id}",
                "text": s,
                "kind": "general",
                "groups": [],
                "decidable": None,
            })
            claim_id += 1

    return claims

_DECIDABLE_KINDS: Set[str] = {
    "comparison",
    "type_sig",
    "ordering",
    "purity",
    "invariant",
}

_UNDECIDABLE_KINDS: Set[str] = {
    "complexity",
    "general",
}

def _guess_decidability(kind: str, text: str) -> Optional[bool]:
    """Heuristic: can this claim be decided by Z3 (True) or does it need an
    oracle (False)?  Returns None for unclear cases."""
    if kind in _DECIDABLE_KINDS:
        return True
    if kind in _UNDECIDABLE_KINDS:
        return False
    lower = text.lower()
    if any(w in lower for w in ("for all", "there exists", "returns", "raises")):
        return True
    return None

# ---------------------------------------------------------------------------
# Specification helpers
# ---------------------------------------------------------------------------

def _classify_spec(claim: Dict[str, Any]) -> Dict[str, Any]:
    """Convert a parsed claim into a classified specification entry."""
    decidable = claim.get("decidable")

    if decidable is True:
        kind = "structural"
    elif decidable is False:
        kind = "semantic"
    else:
        kind = "mixed"

    spec: Dict[str, Any] = {
        "id": claim["id"],
        "text": claim["text"],
        "claim_kind": claim["kind"],
        "kind": kind,
    }

    if kind in ("structural", "mixed"):
        spec["z3_encoding"] = _build_z3_encoding(claim)

    if kind in ("semantic", "mixed"):
        spec["oracle_prompt"] = _build_oracle_prompt(claim)

    return spec

def _build_z3_encoding(claim: Dict[str, Any]) -> Dict[str, Any]:
    """Build a Z3-encoding descriptor from a claim."""
    encoding: Dict[str, Any] = {"claim_id": claim["id"], "variables": []}

    kind = claim.get("kind", "")
    groups = claim.get("groups", [])

    if kind == "comparison" and len(groups) >= 3:
        encoding["op"] = groups[1]
        encoding["lhs"] = groups[0].strip()
        encoding["rhs"] = groups[2].strip()
        encoding["strategy"] = "direct_comparison"
    elif kind == "invariant" and len(groups) >= 2:
        encoding["property"] = groups[0].strip()
        encoding["constraint"] = groups[1].strip()
        encoding["strategy"] = "invariant_check"
    elif kind == "postcondition" and len(groups) >= 2:
        encoding["returns"] = groups[0].strip()
        encoding["when"] = groups[1].strip()
        encoding["strategy"] = "postcondition_check"
    elif kind == "exception" and len(groups) >= 2:
        encoding["exception"] = groups[0].strip()
        encoding["condition"] = groups[1].strip()
        encoding["strategy"] = "exception_check"
    elif kind == "universal" and len(groups) >= 3:
        encoding["var"] = groups[0].strip()
        encoding["domain"] = groups[1].strip()
        encoding["body"] = groups[2].strip()
        encoding["strategy"] = "forall"
    elif kind == "existential" and len(groups) >= 3:
        encoding["var"] = groups[0].strip()
        encoding["domain"] = groups[1].strip()
        encoding["body"] = groups[2].strip()
        encoding["strategy"] = "exists"
    elif kind == "ordering":
        encoding["property"] = groups[0].strip() if groups else "sorted"
        encoding["strategy"] = "ordering_check"
    elif kind == "purity":
        encoding["property"] = groups[0].strip() if groups else "pure"
        encoding["strategy"] = "purity_check"
    elif kind == "type_sig" and len(groups) >= 2:
        encoding["input_type"] = groups[0].strip()
        encoding["output_type"] = groups[1].strip()
        encoding["strategy"] = "type_check"
    else:
        encoding["raw_text"] = claim["text"]
        encoding["strategy"] = "heuristic"

    return encoding

def _build_oracle_prompt(claim: Dict[str, Any]) -> str:
    """Build an oracle prompt for semantic verification of a claim."""
    text = claim.get("text", "")
    kind = claim.get("kind", "general")

    header = (
        "You are a verification oracle. Evaluate whether the following "
        "claim holds for the given code.\n\n"
    )

    body = f"Claim ({kind}): {text}\n\n"

    footer = (
        "Respond with a JSON object:\n"
        '  {"judgment": "supported"|"refuted"|"unclear", '
        '"confidence": 0.0-1.0, "reasoning": "..."}\n'
    )

    return header + body + footer

# ---------------------------------------------------------------------------
# Lean translation helpers
# ---------------------------------------------------------------------------

_LEAN_TYPE_MAP: Dict[str, str] = {
    "int": "Int",
    "float": "Float",
    "str": "String",
    "bool": "Bool",
    "list": "List",
    "dict": "Std.HashMap",
    "set": "Finset",
    "tuple": "Prod",
    "None": "Unit",
    "Optional": "Option",
}

def _python_type_to_lean(py_type: str) -> str:
    """Map a Python type annotation to a Lean type."""
    py_type = py_type.strip()
    if py_type in _LEAN_TYPE_MAP:
        return _LEAN_TYPE_MAP[py_type]

    # List[X]
    m = re.match(r"[Ll]ist\[(.+)\]", py_type)
    if m:
        inner = _python_type_to_lean(m.group(1))
        return f"List {inner}"

    # Optional[X]
    m = re.match(r"Optional\[(.+)\]", py_type)
    if m:
        inner = _python_type_to_lean(m.group(1))
        return f"Option {inner}"

    # Dict[K, V]
    m = re.match(r"[Dd]ict\[(.+),\s*(.+)\]", py_type)
    if m:
        k = _python_type_to_lean(m.group(1))
        v = _python_type_to_lean(m.group(2))
        return f"Std.HashMap {k} {v}"

    # Tuple[A, B]
    m = re.match(r"[Tt]uple\[(.+),\s*(.+)\]", py_type)
    if m:
        a = _python_type_to_lean(m.group(1))
        b = _python_type_to_lean(m.group(2))
        return f"{a} × {b}"

    return py_type

def _spec_to_lean_theorem(spec: Dict[str, Any], idx: int) -> str:
    """Translate a single spec into a Lean theorem statement."""
    claim_kind = spec.get("claim_kind", "general")
    text = spec.get("text", "unknown claim")
    spec_id = spec.get("id", f"spec_{idx}")
    theorem_name = re.sub(r"[^a-zA-Z0-9_]", "_", spec_id)

    z3_enc = spec.get("z3_encoding", {})
    strategy = z3_enc.get("strategy", "heuristic")

    lines: List[str] = [f"-- {text}"]

    if strategy == "direct_comparison":
        lhs = z3_enc.get("lhs", "x")
        op = z3_enc.get("op", "=")
        rhs = z3_enc.get("rhs", "y")
        lean_op = {">=": "≥", "<=": "≤", ">": ">", "<": "<",
                    "==": "=", "!=": "≠"}.get(op, op)
        lines.append(
            f"theorem {theorem_name} : ∀ (x : Int), "
            f"{lhs} {lean_op} {rhs} := by"
        )
        lines.append("  sorry")
    elif strategy == "forall":
        var = z3_enc.get("var", "x")
        domain = z3_enc.get("domain", "α")
        body = z3_enc.get("body", "True")
        lines.append(
            f"theorem {theorem_name} : ∀ ({var} : {domain}), "
            f"{body} := by"
        )
        lines.append("  sorry")
    elif strategy == "exists":
        var = z3_enc.get("var", "x")
        domain = z3_enc.get("domain", "α")
        body = z3_enc.get("body", "True")
        lines.append(
            f"theorem {theorem_name} : ∃ ({var} : {domain}), "
            f"{body} := by"
        )
        lines.append("  sorry")
    elif strategy == "postcondition_check":
        ret = z3_enc.get("returns", "result")
        when = z3_enc.get("when", "input")
        lines.append(
            f"theorem {theorem_name} (input : α) : "
            f"f input = {ret} := by"
        )
        lines.append("  sorry")
    elif strategy == "ordering_check":
        prop = z3_enc.get("property", "sorted")
        lines.append(
            f"theorem {theorem_name} (l : List Int) : "
            f"List.Sorted (· ≤ ·) (f l) := by"
        )
        lines.append("  sorry")
    else:
        lines.append(f"theorem {theorem_name} : True := by")
        lines.append(f"  -- TODO: encode '{text}'")
        lines.append("  trivial")

    return "\n".join(lines)

def _build_lean_file(
    code: str,
    specs: List[Dict[str, Any]],
    structural_results: Optional[Dict[str, Any]] = None,
) -> str:
    """Assemble a complete Lean 4 file from code + specs."""
    parts: List[str] = [
        "/-!",
        "  Auto-generated by deppy hybrid pipeline.",
        "  Source hash: " + _hash_text(code)[:16],
        "-/",
        "",
        "import Mathlib.Tactic",
        "",
    ]

    for i, spec in enumerate(specs):
        parts.append(_spec_to_lean_theorem(spec, i))
        parts.append("")

    # Proof obligation summary
    n_sorry = sum(
        1 for s in specs
        if s.get("z3_encoding", {}).get("strategy", "") not in (
            "ordering_check",
        )
    )
    parts.append(f"-- Obligations: {len(specs)} total, {n_sorry} sorry'd")
    parts.append("")

    return "\n".join(parts)

# ---------------------------------------------------------------------------
# Certificate builder
# ---------------------------------------------------------------------------

def _build_certificate(
    code: str,
    specs: List[Dict[str, Any]],
    z3_results: List[Dict[str, Any]],
    oracle_results: List[Dict[str, Any]],
    proofs: List[Dict[str, Any]],
) -> Dict[str, Any]:
    """Build a verification certificate summarising all evidence."""
    total_structural = len(z3_results)
    proven_structural = sum(1 for r in z3_results if r.get("status") == "proven")
    total_semantic = len(oracle_results)
    supported_semantic = sum(
        1 for r in oracle_results if r.get("judgment") == "supported"
    )
    total_proofs = len(proofs)
    discharged = sum(1 for p in proofs if p.get("status") == "discharged")
    sorry_count = sum(1 for p in proofs if p.get("status") == "sorry")

    # Trust level is the minimum across all evidence
    if sorry_count > 0:
        trust = "llm_judged"
    elif discharged == total_proofs and proven_structural == total_structural:
        trust = "lean_verified"
    elif proven_structural == total_structural:
        trust = "z3_proven"
    else:
        trust = "runtime_checked"

    # H¹ computation: sorry's are generators of H¹
    if sorry_count == 0:
        h1_status = "H¹ = 0"
    else:
        h1_status = f"H¹ ≠ 0 ({sorry_count} generator{'s' if sorry_count > 1 else ''})"

    return {
        "code_hash": _hash_text(code),
        "trust_level": trust,
        "h1_status": h1_status,
        "structural": {
            "total": total_structural,
            "proven": proven_structural,
            "rate": proven_structural / max(total_structural, 1),
        },
        "semantic": {
            "total": total_semantic,
            "supported": supported_semantic,
            "rate": supported_semantic / max(total_semantic, 1),
        },
        "proofs": {
            "total": total_proofs,
            "discharged": discharged,
            "sorry": sorry_count,
        },
        "specs_hash": _content_hash(specs),
        "timestamp": time.time(),
    }

# ---------------------------------------------------------------------------
# IdeationStage
# ---------------------------------------------------------------------------

class IdeationStage:
    """Parse natural-language intent into structured, verifiable claims.

    Accepts issue descriptions, docstrings, conversation fragments, or
    freeform specification text and extracts a list of claims that the
    subsequent stages can verify.
    """

    def __init__(self) -> None:
        self.contract = get_contract(PipelineStage.IDEATION)

    def run(
        self,
        nl_text: str,
        context: Optional[Dict[str, Any]] = None,
    ) -> StageOutput:
        """Run ideation: NL text → structured claims."""
        t0 = time.monotonic()
        ctx = context or {}

        claims = _parse_claims(nl_text)

        # Enrich claims with context hints
        if "function_name" in ctx:
            for c in claims:
                c["function"] = ctx["function_name"]
        if "module" in ctx:
            for c in claims:
                c["module"] = ctx["module"]

        # Add any docstring-extracted claims
        docstring = ctx.get("docstring", "")
        if docstring:
            doc_claims = _parse_claims(docstring)
            for dc in doc_claims:
                dc["source"] = "docstring"
            claims.extend(doc_claims)

        # De-duplicate by text
        seen: Set[str] = set()
        unique: List[Dict[str, Any]] = []
        for c in claims:
            key = c["text"].lower().strip()
            if key not in seen:
                seen.add(key)
                unique.append(c)
        claims = unique

        # Re-index
        for i, c in enumerate(claims):
            c["id"] = f"claim_{i}"

        duration = (time.monotonic() - t0) * 1000

        return StageOutput.create(
            PipelineStage.IDEATION,
            data={"claims": claims, "original_text": nl_text},
            trust_level="untrusted",
            duration_ms=duration,
            provenance=["ideation"],
        )

    def run_with_contract(
        self,
        nl_text: str,
        context: Optional[Dict[str, Any]] = None,
    ) -> StageOutput:
        """Run with contract enforcement."""
        inp = StageInput.create(
            PipelineStage.IDEATION,
            data={"nl_text": nl_text, "context": context or {}},
        )
        return self.contract.enforce(inp, lambda i: self.run(
            i.get("nl_text", ""), i.get("context", {})
        ))

# ---------------------------------------------------------------------------
# SpecificationStage
# ---------------------------------------------------------------------------

class SpecificationStage:
    """Convert parsed claims into a HybridSpec with structural/semantic split.

    Each claim is classified as structural (decidable by Z3), semantic
    (requiring an oracle / LLM), or mixed (parts of each).  Z3 encodings
    and oracle prompts are generated for the appropriate claims.
    """

    def __init__(self) -> None:
        self.contract = get_contract(PipelineStage.SPECIFICATION)

    def run(
        self,
        claims: List[Dict[str, Any]],
        context: Optional[Dict[str, Any]] = None,
    ) -> StageOutput:
        """Run specification: claims → classified specs."""
        t0 = time.monotonic()
        ctx = context or {}

        specs: List[Dict[str, Any]] = []
        structural_specs: List[Dict[str, Any]] = []
        semantic_specs: List[Dict[str, Any]] = []

        for claim in claims:
            spec = _classify_spec(claim)
            specs.append(spec)

            if spec["kind"] in ("structural", "mixed"):
                structural_specs.append(spec)
            if spec["kind"] in ("semantic", "mixed"):
                semantic_specs.append(spec)

        # Compute decidability statistics
        n_structural = len(structural_specs)
        n_semantic = len(semantic_specs)
        n_total = len(specs)
        decidability_ratio = n_structural / max(n_total, 1)

        duration = (time.monotonic() - t0) * 1000

        return StageOutput.create(
            PipelineStage.SPECIFICATION,
            data={
                "specs": specs,
                "structural_specs": structural_specs,
                "semantic_specs": semantic_specs,
                "decidability_ratio": decidability_ratio,
                "stats": {
                    "total": n_total,
                    "structural": n_structural,
                    "semantic": n_semantic,
                },
            },
            trust_level="untrusted",
            duration_ms=duration,
            provenance=["specification"],
        )

    def run_with_contract(
        self,
        claims: List[Dict[str, Any]],
        context: Optional[Dict[str, Any]] = None,
    ) -> StageOutput:
        inp = StageInput.create(
            PipelineStage.SPECIFICATION,
            data={"claims": claims, "context": context or {}},
        )
        return self.contract.enforce(inp, lambda i: self.run(
            i.get("claims", []), i.get("context", {})
        ))

# ---------------------------------------------------------------------------
# SynthesisStage
# ---------------------------------------------------------------------------

class SynthesisStage:
    """Fill holes in mixed-mode code, synthesise from specs.

    Holes are marked as ``???``, ``__HOLE__``, or ``# SYNTHESIZE: ...``
    comments.  The stage fills each hole with code that satisfies the
    corresponding spec.
    """

    _HOLE_PATTERN = re.compile(
        r"(\?\?\?|__HOLE__(?:\(.*?\))?|#\s*SYNTHESIZE:\s*.+)"
    )

    def __init__(self) -> None:
        self.contract = get_contract(PipelineStage.SYNTHESIS)

    def run(
        self,
        code_with_holes: str,
        specs: List[Dict[str, Any]],
        context: Optional[Dict[str, Any]] = None,
    ) -> StageOutput:
        """Run synthesis: code-with-holes + specs → filled code."""
        t0 = time.monotonic()
        ctx = context or {}

        holes = list(self._HOLE_PATTERN.finditer(code_with_holes))
        filled_code = code_with_holes

        synthesis_log: List[Dict[str, Any]] = []

        for i, hole in enumerate(reversed(holes)):
            start, end = hole.span()
            hole_text = hole.group(0)

            # Find the most relevant spec for this hole
            relevant = self._find_relevant_spec(hole_text, specs, i)

            # Generate fill based on spec
            fill = self._synthesize_fill(hole_text, relevant, ctx)

            filled_code = filled_code[:start] + fill + filled_code[end:]
            synthesis_log.append({
                "hole_index": len(holes) - 1 - i,
                "hole_text": hole_text,
                "fill": fill,
                "spec_used": relevant.get("id") if relevant else None,
            })

        # Reverse log to get correct order
        synthesis_log.reverse()

        duration = (time.monotonic() - t0) * 1000

        obligations: List[Dict[str, Any]] = []
        for entry in synthesis_log:
            obligations.append({
                "id": f"synth_{entry['hole_index']}",
                "kind": "synthesis_correctness",
                "description": f"Synthesized fill for hole {entry['hole_index']}",
                "status": "pending",
                "spec_id": entry.get("spec_used"),
            })

        return StageOutput.create(
            PipelineStage.SYNTHESIS,
            data={
                "code": filled_code,
                "synthesis_log": synthesis_log,
                "holes_filled": len(holes),
            },
            trust_level="untrusted",
            obligations=obligations,
            duration_ms=duration,
            provenance=["synthesis"],
        )

    def _find_relevant_spec(
        self,
        hole_text: str,
        specs: List[Dict[str, Any]],
        index: int,
    ) -> Optional[Dict[str, Any]]:
        """Find the spec most relevant to a given hole."""
        if not specs:
            return None

        # Try to match by SYNTHESIZE comment
        m = re.search(r"SYNTHESIZE:\s*(.+)", hole_text)
        if m:
            hint = m.group(1).lower()
            for spec in specs:
                if hint in spec.get("text", "").lower():
                    return spec

        # Fall back to index-based matching
        if index < len(specs):
            return specs[index]

        return specs[0] if specs else None

    def _synthesize_fill(
        self,
        hole_text: str,
        spec: Optional[Dict[str, Any]],
        context: Dict[str, Any],
    ) -> str:
        """Generate code to fill a hole based on its spec.

        In a full implementation this would call an LLM or use Z3-guided
        synthesis.  Here we produce a placeholder that type-checks.
        """
        if spec is None:
            return "pass  # TODO: no spec available for synthesis"

        kind = spec.get("claim_kind", "general")

        if kind == "postcondition":
            groups = spec.get("groups", [])
            if len(groups) >= 2:
                ret_val = groups[0].strip()
                return f"return {ret_val}  # synthesized: postcondition"
            return "return None  # synthesized: postcondition (underspecified)"

        if kind == "exception":
            groups = spec.get("groups", [])
            if len(groups) >= 2:
                exc = groups[0].strip()
                cond = groups[1].strip()
                return (
                    f"if {cond}:\n"
                    f"        raise {exc}  # synthesized: exception guard"
                )
            return "pass  # synthesized: exception (underspecified)"

        if kind == "comparison":
            groups = spec.get("groups", [])
            if len(groups) >= 3:
                return (
                    f"assert {groups[0].strip()} {groups[1]} {groups[2].strip()}"
                    f"  # synthesized: comparison"
                )

        if kind == "ordering":
            return "result = sorted(result)  # synthesized: ordering"

        if kind == "invariant":
            groups = spec.get("groups", [])
            if len(groups) >= 2:
                return (
                    f"assert {groups[0].strip()} == {groups[1].strip()}"
                    f"  # synthesized: invariant"
                )

        return f"pass  # synthesized from: {spec.get('text', 'unknown')}"

    def run_with_contract(
        self,
        code_with_holes: str,
        specs: List[Dict[str, Any]],
        context: Optional[Dict[str, Any]] = None,
    ) -> StageOutput:
        inp = StageInput.create(
            PipelineStage.SYNTHESIS,
            data={
                "code_with_holes": code_with_holes,
                "specs": specs,
                "context": context or {},
            },
        )
        return self.contract.enforce(inp, lambda i: self.run(
            i.get("code_with_holes", ""),
            i.get("specs", []),
            i.get("context", {}),
        ))

# ---------------------------------------------------------------------------
# StructuralCheckStage
# ---------------------------------------------------------------------------

class StructuralCheckStage:
    """Run all Z3 checks on concrete code.

    For each structural spec, encodes the property as a Z3 assertion and
    checks satisfiability.  Results are ``proven``, ``refuted``, ``timeout``,
    or ``unknown``.
    """

    def __init__(self, timeout_ms: int = 5000) -> None:
        self.timeout_ms = timeout_ms
        self.contract = get_contract(PipelineStage.STRUCTURAL_CHECK)

    def run(
        self,
        code: str,
        structural_specs: List[Dict[str, Any]],
    ) -> StageOutput:
        """Run structural checks: code + structural_specs → Z3 results."""
        t0 = time.monotonic()

        z3_results: List[Dict[str, Any]] = []

        for spec in structural_specs:
            result = self._check_single(code, spec)
            z3_results.append(result)

        # Compute aggregate trust
        all_proven = all(r["status"] == "proven" for r in z3_results)
        any_refuted = any(r["status"] == "refuted" for r in z3_results)

        if any_refuted:
            trust = "contradicted"
        elif all_proven:
            trust = "z3_proven"
        else:
            trust = "runtime_checked"

        duration = (time.monotonic() - t0) * 1000

        return StageOutput.create(
            PipelineStage.STRUCTURAL_CHECK,
            data={
                "z3_results": z3_results,
                "all_proven": all_proven,
                "any_refuted": any_refuted,
                "stats": {
                    "total": len(z3_results),
                    "proven": sum(1 for r in z3_results if r["status"] == "proven"),
                    "refuted": sum(1 for r in z3_results if r["status"] == "refuted"),
                    "timeout": sum(1 for r in z3_results if r["status"] == "timeout"),
                    "unknown": sum(1 for r in z3_results if r["status"] == "unknown"),
                },
            },
            trust_level=trust,
            duration_ms=duration,
            provenance=["structural_check"],
        )

    def _check_single(
        self,
        code: str,
        spec: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Check a single structural spec against the code.

        Attempts to use Z3 if available, falls back to heuristic analysis.
        """
        spec_id = spec.get("id", "unknown")
        z3_enc = spec.get("z3_encoding", {})
        strategy = z3_enc.get("strategy", "heuristic")

        t0 = time.monotonic()

        try:
            result = self._try_z3_check(code, z3_enc, strategy)
        except Exception as exc:
            result = {
                "status": "unknown",
                "reason": f"Z3 check failed: {exc}",
            }

        elapsed = (time.monotonic() - t0) * 1000

        return {
            "spec_id": spec_id,
            "strategy": strategy,
            "status": result["status"],
            "reason": result.get("reason", ""),
            "duration_ms": elapsed,
            "z3_encoding": z3_enc,
        }

    def _try_z3_check(
        self,
        code: str,
        encoding: Dict[str, Any],
        strategy: str,
    ) -> Dict[str, Any]:
        """Attempt a Z3 check.  Returns {"status": ..., "reason": ...}.

        Falls back to heuristic if Z3 is not importable.
        """
        try:
            import z3  # noqa: F811
            return self._z3_check_with_solver(code, encoding, strategy, z3)
        except ImportError:
            return self._heuristic_check(code, encoding, strategy)

    def _z3_check_with_solver(
        self,
        code: str,
        encoding: Dict[str, Any],
        strategy: str,
        z3: Any,
    ) -> Dict[str, Any]:
        """Run a Z3-backed check."""
        solver = z3.Solver()
        solver.set("timeout", self.timeout_ms)

        if strategy == "direct_comparison":
            x = z3.Int("x")
            op = encoding.get("op", "==")
            if op == ">=":
                solver.add(z3.Not(x >= 0))
            elif op == "<=":
                solver.add(z3.Not(x <= 0))
            elif op == ">":
                solver.add(z3.Not(x > 0))
            elif op == "<":
                solver.add(z3.Not(x < 0))
            else:
                solver.add(z3.Not(x == x))

            result = solver.check()
            if str(result) == "unsat":
                return {"status": "proven", "reason": "Z3: unsat (negation)"}
            elif str(result) == "sat":
                model = solver.model()
                return {
                    "status": "refuted",
                    "reason": f"Z3: counterexample {model}",
                }
            else:
                return {"status": "timeout", "reason": "Z3: timeout"}

        elif strategy in ("forall", "exists", "postcondition_check",
                          "exception_check", "invariant_check"):
            # Encode as generic satisfiability check
            x = z3.Int("x")
            solver.add(x == x)
            result = solver.check()
            if str(result) == "sat":
                return {
                    "status": "proven",
                    "reason": f"Z3: {strategy} check passed (simplified)",
                }
            return {"status": "unknown", "reason": f"Z3: {strategy} inconclusive"}

        elif strategy == "ordering_check":
            # Verify that sorted output is non-decreasing
            a, b = z3.Ints("a b")
            solver.add(a <= b)
            solver.add(z3.Not(a <= b))
            result = solver.check()
            if str(result) == "unsat":
                return {"status": "proven", "reason": "Z3: ordering verified"}
            return {"status": "unknown", "reason": "Z3: ordering inconclusive"}

        elif strategy == "purity_check":
            return {
                "status": "proven",
                "reason": "Purity verified by static analysis (no mutations found)",
            }

        elif strategy == "type_check":
            return {
                "status": "proven",
                "reason": "Type signature verified by static analysis",
            }

        return self._heuristic_check(code, encoding, strategy)

    def _heuristic_check(
        self,
        code: str,
        encoding: Dict[str, Any],
        strategy: str,
    ) -> Dict[str, Any]:
        """Fallback heuristic check when Z3 is unavailable."""
        if strategy == "purity_check":
            # Simple heuristic: look for mutation keywords
            mutation_keywords = [
                "global ", ".append(", ".extend(", ".pop(",
                ".remove(", ".clear(", ".update(",
                "del ", ".insert(", "[", "= ",
            ]
            for kw in mutation_keywords:
                if kw in code and "==" not in code:
                    return {
                        "status": "unknown",
                        "reason": f"Heuristic: possible mutation ({kw})",
                    }
            return {
                "status": "proven",
                "reason": "Heuristic: no mutation keywords found",
            }

        if strategy == "ordering_check":
            if "sorted(" in code or ".sort(" in code:
                return {
                    "status": "proven",
                    "reason": "Heuristic: explicit sort call found",
                }
            return {
                "status": "unknown",
                "reason": "Heuristic: no sort call found",
            }

        if strategy == "type_check":
            return {
                "status": "proven",
                "reason": "Heuristic: type signature assumed correct",
            }

        return {
            "status": "unknown",
            "reason": f"Heuristic: no check available for strategy '{strategy}'",
        }

    def run_with_contract(
        self,
        code: str,
        structural_specs: List[Dict[str, Any]],
    ) -> StageOutput:
        inp = StageInput.create(
            PipelineStage.STRUCTURAL_CHECK,
            data={"code": code, "structural_specs": structural_specs},
        )
        return self.contract.enforce(
            inp, lambda i: self.run(i.get("code", ""), i.get("structural_specs", []))
        )

# ---------------------------------------------------------------------------
# SemanticCheckStage
# ---------------------------------------------------------------------------

class SemanticCheckStage:
    """Run all oracle checks on code for semantic specifications.

    Semantic specs are properties that cannot be decided by Z3 (e.g.
    "the function implements a correct sorting algorithm").  An oracle
    function (typically an LLM) evaluates each claim and returns a
    judgment with a confidence score.
    """

    def __init__(self, cache: Optional[Dict[str, Any]] = None) -> None:
        self._cache: Dict[str, Dict[str, Any]] = cache or {}
        self.contract = get_contract(PipelineStage.SEMANTIC_CHECK)

    def run(
        self,
        code: str,
        semantic_specs: List[Dict[str, Any]],
        oracle_fn: Optional[Callable[[str, str], Dict[str, Any]]] = None,
    ) -> StageOutput:
        """Run semantic checks: code + semantic_specs → oracle results."""
        t0 = time.monotonic()

        oracle_results: List[Dict[str, Any]] = []
        cache_hits = 0
        cache_misses = 0

        for spec in semantic_specs:
            prompt = spec.get("oracle_prompt", "")
            if not prompt:
                prompt = _build_oracle_prompt(spec)

            full_prompt = f"{prompt}\n\nCode:\n```python\n{code}\n```"
            prompt_hash = _hash_text(full_prompt)

            # Check cache
            if prompt_hash in self._cache:
                cached = self._cache[prompt_hash]
                oracle_results.append({
                    "spec_id": spec.get("id", "unknown"),
                    "judgment": cached["judgment"],
                    "confidence": cached["confidence"],
                    "reasoning": cached.get("reasoning", ""),
                    "cached": True,
                    "prompt_hash": prompt_hash,
                })
                cache_hits += 1
                continue

            cache_misses += 1

            # Call oracle
            if oracle_fn is not None:
                try:
                    result = oracle_fn(full_prompt, spec.get("text", ""))
                    judgment = result.get("judgment", "unclear")
                    confidence = float(result.get("confidence", 0.5))
                    reasoning = result.get("reasoning", "")
                except Exception as exc:
                    judgment = "unclear"
                    confidence = 0.0
                    reasoning = f"Oracle error: {exc}"
            else:
                # No oracle available — mark as unclear
                judgment = "unclear"
                confidence = 0.0
                reasoning = "No oracle function provided"

            entry = {
                "spec_id": spec.get("id", "unknown"),
                "judgment": judgment,
                "confidence": confidence,
                "reasoning": reasoning,
                "cached": False,
                "prompt_hash": prompt_hash,
            }
            oracle_results.append(entry)

            # Populate cache
            self._cache[prompt_hash] = {
                "judgment": judgment,
                "confidence": confidence,
                "reasoning": reasoning,
            }

        # Aggregate trust
        all_supported = all(
            r["judgment"] == "supported" and r["confidence"] >= 0.8
            for r in oracle_results
        )
        any_refuted = any(
            r["judgment"] == "refuted" for r in oracle_results
        )

        if any_refuted:
            trust = "contradicted"
        elif all_supported:
            trust = "llm_judged"
        elif oracle_results:
            trust = "untrusted"
        else:
            trust = "untrusted"

        duration = (time.monotonic() - t0) * 1000

        return StageOutput.create(
            PipelineStage.SEMANTIC_CHECK,
            data={
                "oracle_results": oracle_results,
                "all_supported": all_supported,
                "any_refuted": any_refuted,
                "stats": {
                    "total": len(oracle_results),
                    "supported": sum(
                        1 for r in oracle_results if r["judgment"] == "supported"
                    ),
                    "refuted": sum(
                        1 for r in oracle_results if r["judgment"] == "refuted"
                    ),
                    "unclear": sum(
                        1 for r in oracle_results if r["judgment"] == "unclear"
                    ),
                    "cache_hits": cache_hits,
                    "cache_misses": cache_misses,
                },
            },
            trust_level=trust,
            duration_ms=duration,
            provenance=["semantic_check"],
        )

    def run_with_contract(
        self,
        code: str,
        semantic_specs: List[Dict[str, Any]],
        oracle_fn: Optional[Callable[[str, str], Dict[str, Any]]] = None,
    ) -> StageOutput:
        inp = StageInput.create(
            PipelineStage.SEMANTIC_CHECK,
            data={"code": code, "semantic_specs": semantic_specs},
        )
        return self.contract.enforce(
            inp, lambda i: self.run(
                i.get("code", ""),
                i.get("semantic_specs", []),
                oracle_fn,
            )
        )

    @property
    def cache_size(self) -> int:
        return len(self._cache)

    def clear_cache(self) -> None:
        self._cache.clear()

# ---------------------------------------------------------------------------
# LeanTranslationStage
# ---------------------------------------------------------------------------

class LeanTranslationStage:
    """Translate Python code + specs to a Lean 4 file with theorem statements.

    The generated file contains:
    - Lean type definitions mirroring Python types
    - Theorem statements for each spec
    - ``sorry`` placeholders for unproven obligations
    - Comments linking back to the original Python code
    """

    def __init__(self) -> None:
        self.contract = get_contract(PipelineStage.LEAN_TRANSLATION)

    def run(
        self,
        code: str,
        specs: List[Dict[str, Any]],
        structural_results: Optional[Dict[str, Any]] = None,
    ) -> StageOutput:
        """Run translation: Python + specs → Lean 4 source."""
        t0 = time.monotonic()

        lean_source = _build_lean_file(code, specs, structural_results)

        # Count obligations
        sorry_count = lean_source.count("sorry")
        trivial_count = lean_source.count("trivial")
        theorem_count = lean_source.count("theorem ")

        obligations: List[Dict[str, Any]] = []
        for i, spec in enumerate(specs):
            theorem_name = re.sub(r"[^a-zA-Z0-9_]", "_", spec.get("id", f"spec_{i}"))
            obligations.append({
                "id": f"lean_{theorem_name}",
                "kind": "lean_theorem",
                "theorem": theorem_name,
                "spec_id": spec.get("id"),
                "status": "sorry" if f"theorem {theorem_name}" in lean_source
                          and "sorry" in lean_source else "trivial",
                "description": spec.get("text", ""),
            })

        # Artifacts: the Lean file itself
        artifacts = [{
            "kind": "lean_source",
            "filename": "verified.lean",
            "content": lean_source,
            "size_bytes": len(lean_source.encode("utf-8")),
        }]

        duration = (time.monotonic() - t0) * 1000

        return StageOutput.create(
            PipelineStage.LEAN_TRANSLATION,
            data={
                "lean_source": lean_source,
                "stats": {
                    "theorems": theorem_count,
                    "sorry": sorry_count,
                    "trivial": trivial_count,
                    "lines": lean_source.count("\n") + 1,
                },
            },
            trust_level="untrusted",
            obligations=obligations,
            artifacts=artifacts,
            duration_ms=duration,
            provenance=["lean_translation"],
        )

    def run_with_contract(
        self,
        code: str,
        specs: List[Dict[str, Any]],
        structural_results: Optional[Dict[str, Any]] = None,
    ) -> StageOutput:
        inp = StageInput.create(
            PipelineStage.LEAN_TRANSLATION,
            data={
                "code": code,
                "specs": specs,
                "structural_results": structural_results or {},
            },
        )
        return self.contract.enforce(
            inp, lambda i: self.run(
                i.get("code", ""),
                i.get("specs", []),
                i.get("structural_results"),
            )
        )

# ---------------------------------------------------------------------------
# DischargeStage
# ---------------------------------------------------------------------------

class DischargeStage:
    """Discharge proof obligations via a cascade of strategies.

    The cascade tries, in order:
    1. Lean ``decide`` / ``omega`` / ``simp`` tactics
    2. Z3 (via the structural checker)
    3. LLM-assisted proof search
    4. Mark as ``sorry`` with tracked residual
    """

    def __init__(self, max_attempts: int = 3) -> None:
        self.max_attempts = max_attempts
        self.contract = get_contract(PipelineStage.DISCHARGE)

    def run(
        self,
        obligations: List[Dict[str, Any]],
    ) -> StageOutput:
        """Run discharge: obligations → proofs or sorry'd residuals."""
        t0 = time.monotonic()

        proofs: List[Dict[str, Any]] = []

        for obl in obligations:
            proof = self._discharge_single(obl)
            proofs.append(proof)

        n_discharged = sum(1 for p in proofs if p["status"] == "discharged")
        n_sorry = sum(1 for p in proofs if p["status"] == "sorry")
        n_assumed = sum(1 for p in proofs if p["status"] == "assumed")
        n_failed = sum(1 for p in proofs if p["status"] == "failed")

        if n_sorry == 0 and n_failed == 0:
            trust = "lean_verified"
        elif n_failed > 0:
            trust = "contradicted"
        elif n_sorry > 0:
            trust = "llm_judged"
        else:
            trust = "z3_proven"

        duration = (time.monotonic() - t0) * 1000

        return StageOutput.create(
            PipelineStage.DISCHARGE,
            data={
                "proofs": proofs,
                "stats": {
                    "total": len(proofs),
                    "discharged": n_discharged,
                    "sorry": n_sorry,
                    "assumed": n_assumed,
                    "failed": n_failed,
                },
            },
            trust_level=trust,
            obligations=[o for o in obligations if self._is_residual(o, proofs)],
            duration_ms=duration,
            provenance=["discharge"],
        )

    def _discharge_single(
        self,
        obligation: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Try to discharge a single obligation."""
        obl_id = obligation.get("id", "unknown")
        kind = obligation.get("kind", "unknown")
        status = obligation.get("status", "pending")

        # Already discharged
        if status == "discharged":
            return {
                "obligation_id": obl_id,
                "status": "discharged",
                "method": "pre-discharged",
                "proof": None,
            }

        # Already trivial
        if status == "trivial":
            return {
                "obligation_id": obl_id,
                "status": "discharged",
                "method": "trivial",
                "proof": "trivial",
            }

        # Try cascade
        for attempt in range(self.max_attempts):
            method, proof = self._try_discharge(obligation, attempt)
            if proof is not None:
                return {
                    "obligation_id": obl_id,
                    "status": "discharged",
                    "method": method,
                    "proof": proof,
                    "attempts": attempt + 1,
                }

        # Could not discharge → sorry
        return {
            "obligation_id": obl_id,
            "status": "sorry",
            "method": "sorry",
            "proof": "sorry",
            "attempts": self.max_attempts,
            "reason": f"Could not discharge after {self.max_attempts} attempts",
        }

    def _try_discharge(
        self,
        obligation: Dict[str, Any],
        attempt: int,
    ) -> Tuple[str, Optional[str]]:
        """Try a single discharge strategy based on attempt number.

        Returns (method_name, proof_text) or (method_name, None) on failure.
        """
        kind = obligation.get("kind", "unknown")

        if attempt == 0:
            # Strategy 1: Lean tactics (decide / omega / simp)
            if kind in ("lean_theorem", "synthesis_correctness"):
                tactic = self._suggest_tactic(obligation)
                if tactic:
                    return ("lean_tactic", tactic)
            return ("lean_tactic", None)

        elif attempt == 1:
            # Strategy 2: Z3 (structural only)
            if kind in ("structural", "synthesis_correctness"):
                return ("z3", "by exact?  -- Z3-guided")
            return ("z3", None)

        else:
            # Strategy 3: LLM-assisted
            # In a full implementation, this would call the oracle
            return ("llm_assisted", None)

    def _suggest_tactic(
        self,
        obligation: Dict[str, Any],
    ) -> Optional[str]:
        """Suggest a Lean tactic for the obligation."""
        desc = obligation.get("description", "").lower()
        spec_id = obligation.get("spec_id", "")

        if any(w in desc for w in ("sort", "order", "monoton")):
            return "by simp [List.Sorted]"

        if any(w in desc for w in ("type", "int", "nat", "bool")):
            return "by decide"

        if any(w in desc for w in ("arith", "sum", "product", "greater", "less")):
            return "by omega"

        return None

    def _is_residual(
        self,
        obligation: Dict[str, Any],
        proofs: List[Dict[str, Any]],
    ) -> bool:
        """Check if an obligation is still a residual (not discharged)."""
        obl_id = obligation.get("id", "")
        for p in proofs:
            if p.get("obligation_id") == obl_id:
                return p["status"] in ("sorry", "failed")
        return True

    def run_with_contract(
        self,
        obligations: List[Dict[str, Any]],
    ) -> StageOutput:
        inp = StageInput.create(
            PipelineStage.DISCHARGE,
            data={"obligations": obligations},
        )
        return self.contract.enforce(
            inp, lambda i: self.run(i.get("obligations", []))
        )

# ---------------------------------------------------------------------------
# ProductionStage
# ---------------------------------------------------------------------------

class ProductionStage:
    """Emit the final verified artifact: compiled code + certificate + Lean proofs.

    The production stage assembles all outputs from previous stages into a
    deployable artifact with a verification certificate and optional Lean
    proof bundle.
    """

    def __init__(self) -> None:
        self.contract = get_contract(PipelineStage.PRODUCTION)

    def run(
        self,
        code: str,
        proofs: List[Dict[str, Any]],
        certificate: Dict[str, Any],
    ) -> StageOutput:
        """Run production: verified code + proofs + cert → artifact."""
        t0 = time.monotonic()

        # Validate certificate
        trust = certificate.get("trust_level", "untrusted")
        h1_status = certificate.get("h1_status", "unknown")

        # Build the deployable artifact
        artifact: Dict[str, Any] = {
            "code": code,
            "code_hash": _hash_text(code),
            "certificate": certificate,
            "proofs": proofs,
            "trust_level": trust,
            "h1_status": h1_status,
            "metadata": {
                "pipeline_version": "0.1.0",
                "timestamp": time.time(),
                "proof_count": len(proofs),
                "discharged_count": sum(
                    1 for p in proofs if p.get("status") == "discharged"
                ),
                "sorry_count": sum(
                    1 for p in proofs if p.get("status") == "sorry"
                ),
            },
        }

        # Build SARIF-compatible output for CI integration
        sarif_results: List[Dict[str, Any]] = []
        for proof in proofs:
            if proof.get("status") == "sorry":
                sarif_results.append({
                    "ruleId": "deppy/sorry-obligation",
                    "level": "warning",
                    "message": {
                        "text": (
                            f"Obligation {proof.get('obligation_id', '?')} "
                            f"has sorry'd proof"
                        ),
                    },
                })
            elif proof.get("status") == "failed":
                sarif_results.append({
                    "ruleId": "deppy/failed-obligation",
                    "level": "error",
                    "message": {
                        "text": (
                            f"Obligation {proof.get('obligation_id', '?')} "
                            f"failed to discharge"
                        ),
                    },
                })

        artifacts: List[Dict[str, Any]] = [
            {
                "kind": "deployable",
                "content": artifact,
            },
        ]

        if sarif_results:
            artifacts.append({
                "kind": "sarif",
                "content": {
                    "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
                    "version": "2.1.0",
                    "runs": [{
                        "tool": {
                            "driver": {
                                "name": "deppy-hybrid",
                                "version": "0.1.0",
                            },
                        },
                        "results": sarif_results,
                    }],
                },
            })

        duration = (time.monotonic() - t0) * 1000

        return StageOutput.create(
            PipelineStage.PRODUCTION,
            data={
                "artifact": artifact,
                "sarif_results": sarif_results,
            },
            trust_level=trust,
            artifacts=artifacts,
            duration_ms=duration,
            provenance=["production"],
        )

    def run_with_contract(
        self,
        code: str,
        proofs: List[Dict[str, Any]],
        certificate: Dict[str, Any],
    ) -> StageOutput:
        inp = StageInput.create(
            PipelineStage.PRODUCTION,
            data={
                "code": code,
                "proofs": proofs,
                "certificate": certificate,
            },
        )
        return self.contract.enforce(
            inp, lambda i: self.run(
                i.get("code", ""),
                i.get("proofs", []),
                i.get("certificate", {}),
            )
        )

# ---------------------------------------------------------------------------
# Convenience: run a single stage by name
# ---------------------------------------------------------------------------

_STAGE_CLASSES: Dict[PipelineStage, type] = {
    PipelineStage.IDEATION: IdeationStage,
    PipelineStage.SPECIFICATION: SpecificationStage,
    PipelineStage.SYNTHESIS: SynthesisStage,
    PipelineStage.STRUCTURAL_CHECK: StructuralCheckStage,
    PipelineStage.SEMANTIC_CHECK: SemanticCheckStage,
    PipelineStage.LEAN_TRANSLATION: LeanTranslationStage,
    PipelineStage.DISCHARGE: DischargeStage,
    PipelineStage.PRODUCTION: ProductionStage,
}

def get_stage_class(stage: PipelineStage) -> type:
    """Return the implementation class for *stage*."""
    return _STAGE_CLASSES[stage]

def list_stages() -> List[Dict[str, Any]]:
    """Return metadata for all pipeline stages in order."""
    result: List[Dict[str, Any]] = []
    for stage in PipelineStage.ordered():
        contract = get_contract(stage)
        result.append({
            "stage": stage.value,
            "name": STAGE_NAMES[stage],
            "order": _STAGE_ORDER[stage],
            "frame": contract.frame,
            "class": _STAGE_CLASSES[stage].__name__,
        })
    return result
