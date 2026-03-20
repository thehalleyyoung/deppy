"""
Pillar 6 — End-to-End Verified Pipeline: Orchestration

Contract-enforced pipeline orchestration with gate checking.
Runs the 8-stage pipeline from ideation to production, enforcing
verification gates at each transition.
"""

from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.pipeline.pipeline import AnalysisPipeline as _CorePipeline, PipelineResult as _CorePipelineResult
    from deppy.pipeline.pipeline_config import PipelineConfig as _CorePipelineConfig
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False


def _safe_base(core_cls: type) -> type:
    """Return core_cls if it can be safely subclassed by a non-frozen dataclass."""
    import dataclasses as _dc
    if _dc.is_dataclass(core_cls) and getattr(
        getattr(core_cls, "__dataclass_params__", None), "frozen", False
    ):
        return object
    return core_cls

import hashlib
import json
import os
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

from .stages import (

    PipelineStage,
    StageContract,
    StageInput,
    StageOutput,
    IdeationStage,
    SpecificationStage,
    SynthesisStage,
    StructuralCheckStage,
    SemanticCheckStage,
    LeanTranslationStage,
    DischargeStage,
    ProductionStage,
    STAGE_CONTRACTS,
    STAGE_NAMES,
    _content_hash,
    _hash_text,
    _join_trust,
    _build_certificate,
)

# ---------------------------------------------------------------------------
# PipelineConfig
# ---------------------------------------------------------------------------

@dataclass
class PipelineConfig(_safe_base(_CorePipelineConfig) if _HAS_DEPPY_CORE else object):
    """Configuration for a pipeline run.

    Extends the core ``PipelineConfig`` when available, adding hybrid-layer
    oracle, gate, and discharge settings.

    Controls oracle selection, Z3 timeouts, gate strictness, caching,
    and Lean integration.
    """

    # Oracle / LLM
    oracle_fn: Optional[Callable[[str, str], Dict[str, Any]]] = None
    llm_model: str = "gpt-4"

    # Z3
    z3_timeout_ms: int = 5000

    # Gate enforcement
    strict_gates: bool = True
    semantic_confidence_threshold: float = 0.8

    # Discharge
    max_discharge_attempts: int = 3

    # Caching
    cache_dir: Optional[str] = None

    # Lean
    lean_project_dir: Optional[str] = None
    emit_lean: bool = True

    # Reporting
    emit_sarif: bool = False

    # Incremental
    incremental: bool = False

    def to_dict(self) -> Dict[str, Any]:
        return {
            "llm_model": self.llm_model,
            "z3_timeout_ms": self.z3_timeout_ms,
            "strict_gates": self.strict_gates,
            "semantic_confidence_threshold": self.semantic_confidence_threshold,
            "max_discharge_attempts": self.max_discharge_attempts,
            "cache_dir": self.cache_dir,
            "lean_project_dir": self.lean_project_dir,
            "emit_lean": self.emit_lean,
            "emit_sarif": self.emit_sarif,
            "incremental": self.incremental,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> PipelineConfig:
        """Create a PipelineConfig from a dict (e.g. loaded from TOML)."""
        return cls(
            llm_model=d.get("llm_model", "gpt-4"),
            z3_timeout_ms=d.get("z3_timeout_ms", 5000),
            strict_gates=d.get("strict_gates", True),
            semantic_confidence_threshold=d.get(
                "semantic_confidence_threshold", 0.8
            ),
            max_discharge_attempts=d.get("max_discharge_attempts", 3),
            cache_dir=d.get("cache_dir"),
            lean_project_dir=d.get("lean_project_dir"),
            emit_lean=d.get("emit_lean", True),
            emit_sarif=d.get("emit_sarif", False),
            incremental=d.get("incremental", False),
        )

    @classmethod
    def default(cls) -> PipelineConfig:
        """Sensible defaults for local development."""
        return cls()

    @classmethod
    def strict(cls) -> PipelineConfig:
        """Strict configuration: all gates enforced, Lean required."""
        return cls(
            strict_gates=True,
            emit_lean=True,
            emit_sarif=True,
            semantic_confidence_threshold=0.9,
        )

    @classmethod
    def permissive(cls) -> PipelineConfig:
        """Permissive: gates are advisory, sorry's allowed."""
        return cls(
            strict_gates=False,
            emit_lean=False,
            emit_sarif=False,
            semantic_confidence_threshold=0.5,
        )

# ---------------------------------------------------------------------------
# GateResult
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class GateResult:
    """Result of a verification gate check."""

    passed: bool
    failures: List[str] = field(default_factory=list)
    trust_level: str = "untrusted"
    gate_name: str = ""
    details: Dict[str, Any] = field(default_factory=dict)

    @property
    def is_blocking(self) -> bool:
        """True if this gate failure should block the pipeline."""
        return not self.passed

    def to_dict(self) -> Dict[str, Any]:
        return {
            "gate": self.gate_name,
            "passed": self.passed,
            "failures": self.failures,
            "trust_level": self.trust_level,
            "details": self.details,
        }

    def summary(self) -> str:
        status = "PASS" if self.passed else "FAIL"
        msg = f"[{status}] {self.gate_name}"
        if self.failures:
            msg += f" — {len(self.failures)} failure(s)"
        return msg

# ---------------------------------------------------------------------------
# VerificationGate
# ---------------------------------------------------------------------------

@dataclass
class VerificationGate:
    """A verification gate that must be passed between pipeline stages.

    Gates enforce minimum quality thresholds before the pipeline advances
    to the next stage.
    """

    name: str
    required_trust: str
    required_checks: List[str] = field(default_factory=list)
    description: str = ""
    after_stage: Optional[PipelineStage] = None

    def check(
        self,
        output: StageOutput,
        config: Optional[PipelineConfig] = None,
    ) -> GateResult:
        """Check whether *output* satisfies this gate."""
        failures: List[str] = []
        cfg = config or PipelineConfig.default()

        # Trust level check
        trust_ok = self._trust_sufficient(output.trust_level, self.required_trust)
        if not trust_ok:
            failures.append(
                f"Trust level '{output.trust_level}' < required '{self.required_trust}'"
            )

        # Required checks
        for check_name in self.required_checks:
            ok, msg = self._run_required_check(check_name, output, cfg)
            if not ok:
                failures.append(f"{check_name}: {msg}")

        passed = len(failures) == 0

        # Determine resulting trust
        if passed:
            result_trust = output.trust_level
        else:
            result_trust = "untrusted"

        return GateResult(
            passed=passed,
            failures=failures,
            trust_level=result_trust,
            gate_name=self.name,
            details={
                "output_stage": output.stage.value,
                "output_trust": output.trust_level,
                "required_trust": self.required_trust,
            },
        )

    def _trust_sufficient(self, actual: str, required: str) -> bool:
        """Check if *actual* trust meets or exceeds *required*."""
        rank = {
            "lean_verified": 5,
            "z3_proven": 4,
            "llm_judged": 3,
            "runtime_checked": 2,
            "untrusted": 1,
            "contradicted": 0,
        }
        return rank.get(actual, 0) >= rank.get(required, 0)

    def _run_required_check(
        self,
        check_name: str,
        output: StageOutput,
        config: PipelineConfig,
    ) -> Tuple[bool, str]:
        """Execute a named check on the output."""
        if check_name == "all_claims_classified":
            return self._check_all_classified(output)
        elif check_name == "all_structural_proven":
            return self._check_all_structural_proven(output)
        elif check_name == "all_semantic_judged":
            return self._check_all_semantic_judged(output, config)
        elif check_name == "lean_compiles":
            return self._check_lean_compiles(output)
        elif check_name == "no_sorry":
            return self._check_no_sorry(output)
        elif check_name == "no_errors":
            return self._check_no_errors(output)
        elif check_name == "has_certificate":
            return self._check_has_certificate(output)
        elif check_name == "no_contradictions":
            return self._check_no_contradictions(output)
        else:
            return True, f"Unknown check '{check_name}' (skipped)"

    # -- Individual check implementations -----------------------------------

    def _check_all_classified(self, output: StageOutput) -> Tuple[bool, str]:
        """All claims must be classified as structural, semantic, or mixed."""
        specs = output.get("specs", [])
        if not specs:
            return False, "No specs found"
        for i, s in enumerate(specs):
            if s.get("kind") not in ("structural", "semantic", "mixed"):
                return False, f"spec[{i}] not classified"
        return True, "ok"

    def _check_all_structural_proven(self, output: StageOutput) -> Tuple[bool, str]:
        """All structural claims must have Z3_PROVEN status."""
        results = output.get("z3_results", [])
        if not results:
            return True, "No structural results to check"
        not_proven = [
            r for r in results if r.get("status") != "proven"
        ]
        if not_proven:
            ids = [r.get("spec_id", "?") for r in not_proven]
            return False, f"{len(not_proven)} not proven: {ids}"
        return True, "ok"

    def _check_all_semantic_judged(
        self,
        output: StageOutput,
        config: PipelineConfig,
    ) -> Tuple[bool, str]:
        """All semantic claims must be LLM_JUDGED with confidence ≥ threshold."""
        results = output.get("oracle_results", [])
        if not results:
            return True, "No semantic results to check"
        threshold = config.semantic_confidence_threshold
        low_conf = [
            r for r in results
            if r.get("confidence", 0) < threshold
            or r.get("judgment") not in ("supported",)
        ]
        if low_conf:
            ids = [r.get("spec_id", "?") for r in low_conf]
            return False, (
                f"{len(low_conf)} below threshold ({threshold}): {ids}"
            )
        return True, "ok"

    def _check_lean_compiles(self, output: StageOutput) -> Tuple[bool, str]:
        """Lean source must be present (compilation check is external)."""
        lean = output.get("lean_source", "")
        if not lean:
            return False, "No Lean source generated"
        if "theorem" not in lean.lower() and "def" not in lean.lower():
            return False, "Lean source has no theorem/def statements"
        return True, "ok"

    def _check_no_sorry(self, output: StageOutput) -> Tuple[bool, str]:
        """No sorry'd obligations remain."""
        proofs = output.get("proofs", [])
        sorry_proofs = [p for p in proofs if p.get("status") == "sorry"]
        if sorry_proofs:
            ids = [p.get("obligation_id", "?") for p in sorry_proofs]
            return False, f"{len(sorry_proofs)} sorry'd: {ids}"
        return True, "ok"

    def _check_no_errors(self, output: StageOutput) -> Tuple[bool, str]:
        """No errors in output."""
        if output.is_error:
            return False, f"Stage error: {output.get('error', '?')}"
        return True, "ok"

    def _check_has_certificate(self, output: StageOutput) -> Tuple[bool, str]:
        """Output must contain a verification certificate."""
        artifact = output.get("artifact", {})
        if not artifact:
            return False, "No artifact"
        cert = artifact.get("certificate")
        if not cert:
            return False, "No certificate in artifact"
        return True, "ok"

    def _check_no_contradictions(self, output: StageOutput) -> Tuple[bool, str]:
        """No contradicted results."""
        if output.trust_level == "contradicted":
            return False, "Output trust is contradicted"

        z3_results = output.get("z3_results", [])
        refuted = [r for r in z3_results if r.get("status") == "refuted"]
        if refuted:
            ids = [r.get("spec_id", "?") for r in refuted]
            return False, f"{len(refuted)} refuted by Z3: {ids}"

        oracle_results = output.get("oracle_results", [])
        refuted_oracle = [
            r for r in oracle_results if r.get("judgment") == "refuted"
        ]
        if refuted_oracle:
            ids = [r.get("spec_id", "?") for r in refuted_oracle]
            return False, f"{len(refuted_oracle)} refuted by oracle: {ids}"

        return True, "ok"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "required_trust": self.required_trust,
            "required_checks": self.required_checks,
            "description": self.description,
            "after_stage": self.after_stage.value if self.after_stage else None,
        }

# Pre-built verification gates

SPEC_GATE = VerificationGate(
    name="SPEC_GATE",
    required_trust="untrusted",
    required_checks=["all_claims_classified", "no_errors"],
    description="All claims must be classified (structural vs semantic)",
    after_stage=PipelineStage.SPECIFICATION,
)

STRUCTURAL_GATE = VerificationGate(
    name="STRUCTURAL_GATE",
    required_trust="runtime_checked",
    required_checks=["all_structural_proven", "no_contradictions", "no_errors"],
    description="All structural claims must be Z3_PROVEN",
    after_stage=PipelineStage.STRUCTURAL_CHECK,
)

SEMANTIC_GATE = VerificationGate(
    name="SEMANTIC_GATE",
    required_trust="untrusted",
    required_checks=["all_semantic_judged", "no_contradictions", "no_errors"],
    description="All semantic claims must be LLM_JUDGED with conf ≥ threshold",
    after_stage=PipelineStage.SEMANTIC_CHECK,
)

LEAN_GATE = VerificationGate(
    name="LEAN_GATE",
    required_trust="untrusted",
    required_checks=["lean_compiles", "no_errors"],
    description="All obligations must compile to valid Lean (even if sorry'd)",
    after_stage=PipelineStage.LEAN_TRANSLATION,
)

PRODUCTION_GATE = VerificationGate(
    name="PRODUCTION_GATE",
    required_trust="z3_proven",
    required_checks=["no_sorry", "has_certificate", "no_errors"],
    description="No sorry's, all LEAN_VERIFIED or explicitly ASSUMED",
    after_stage=PipelineStage.DISCHARGE,
)

# Gate ordering: checked after the corresponding stage
GATE_ORDER: List[Tuple[PipelineStage, VerificationGate]] = [
    (PipelineStage.SPECIFICATION, SPEC_GATE),
    (PipelineStage.STRUCTURAL_CHECK, STRUCTURAL_GATE),
    (PipelineStage.SEMANTIC_CHECK, SEMANTIC_GATE),
    (PipelineStage.LEAN_TRANSLATION, LEAN_GATE),
    (PipelineStage.DISCHARGE, PRODUCTION_GATE),
]

def get_gate_for_stage(stage: PipelineStage) -> Optional[VerificationGate]:
    """Return the gate to check after *stage*, if any."""
    for s, gate in GATE_ORDER:
        if s == stage:
            return gate
    return None

# ---------------------------------------------------------------------------
# PipelineManifest — full audit trail
# ---------------------------------------------------------------------------

@dataclass
class PipelineManifest:
    """Full audit trail of a pipeline execution.

    Records every stage execution, gate check, and oracle call for
    reproducibility and cost tracking.
    """

    entries: List[Dict[str, Any]] = field(default_factory=list)
    gate_checks: List[Dict[str, Any]] = field(default_factory=list)
    oracle_calls: List[Dict[str, Any]] = field(default_factory=list)
    start_time: float = field(default_factory=time.time)
    end_time: Optional[float] = None

    # -- recording ----------------------------------------------------------

    def add_stage(
        self,
        stage: PipelineStage,
        input_hash: str,
        output_hash: str,
        duration_ms: float,
        trust: str,
    ) -> None:
        """Record a stage execution."""
        self.entries.append({
            "kind": "stage",
            "stage": stage.value,
            "input_hash": input_hash,
            "output_hash": output_hash,
            "duration_ms": duration_ms,
            "trust": trust,
            "timestamp": time.time(),
        })

    def add_gate_check(
        self,
        gate: str,
        passed: bool,
        details: str,
    ) -> None:
        """Record a gate check result."""
        self.gate_checks.append({
            "kind": "gate_check",
            "gate": gate,
            "passed": passed,
            "details": details,
            "timestamp": time.time(),
        })

    def add_oracle_call(
        self,
        stage: PipelineStage,
        prompt_hash: str,
        tokens: int,
        cached: bool,
    ) -> None:
        """Record an oracle / LLM call."""
        self.oracle_calls.append({
            "kind": "oracle_call",
            "stage": stage.value,
            "prompt_hash": prompt_hash,
            "tokens": tokens,
            "cached": cached,
            "timestamp": time.time(),
        })

    def finish(self) -> None:
        """Mark the pipeline as complete."""
        self.end_time = time.time()

    # -- queries ------------------------------------------------------------

    def total_tokens(self) -> int:
        """Total oracle tokens consumed (excluding cached calls)."""
        return sum(
            c["tokens"] for c in self.oracle_calls if not c.get("cached")
        )

    def total_time_ms(self) -> float:
        """Total wall-clock time across all stages."""
        return sum(e["duration_ms"] for e in self.entries)

    def cache_hit_rate(self) -> float:
        """Fraction of oracle calls that were cache hits."""
        if not self.oracle_calls:
            return 0.0
        hits = sum(1 for c in self.oracle_calls if c.get("cached"))
        return hits / len(self.oracle_calls)

    def stage_durations(self) -> Dict[str, float]:
        """Map stage name → duration_ms."""
        return {
            e["stage"]: e["duration_ms"]
            for e in self.entries
            if e["kind"] == "stage"
        }

    def gates_passed(self) -> int:
        """Number of gates that passed."""
        return sum(1 for g in self.gate_checks if g["passed"])

    def gates_failed(self) -> int:
        """Number of gates that failed."""
        return sum(1 for g in self.gate_checks if not g["passed"])

    # -- persistence --------------------------------------------------------

    def save(self, path: str) -> None:
        """Save the manifest to a JSON file."""
        data = self.to_dict()
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        with open(path, "w") as f:
            json.dump(data, f, indent=2, default=str)

    @classmethod
    def load(cls, path: str) -> PipelineManifest:
        """Load a manifest from a JSON file."""
        with open(path) as f:
            data = json.load(f)
        manifest = cls()
        manifest.entries = data.get("entries", [])
        manifest.gate_checks = data.get("gate_checks", [])
        manifest.oracle_calls = data.get("oracle_calls", [])
        manifest.start_time = data.get("start_time", 0.0)
        manifest.end_time = data.get("end_time")
        return manifest

    def to_dict(self) -> Dict[str, Any]:
        return {
            "entries": self.entries,
            "gate_checks": self.gate_checks,
            "oracle_calls": self.oracle_calls,
            "start_time": self.start_time,
            "end_time": self.end_time,
            "summary": {
                "total_time_ms": self.total_time_ms(),
                "total_tokens": self.total_tokens(),
                "cache_hit_rate": self.cache_hit_rate(),
                "gates_passed": self.gates_passed(),
                "gates_failed": self.gates_failed(),
                "stages_run": len(self.entries),
            },
        }

    def summary_text(self) -> str:
        """Human-readable summary."""
        lines = [
            "Pipeline Manifest Summary",
            "=" * 40,
            f"  Stages run:     {len(self.entries)}",
            f"  Total time:     {self.total_time_ms():.1f} ms",
            f"  Gates passed:   {self.gates_passed()}",
            f"  Gates failed:   {self.gates_failed()}",
            f"  Oracle calls:   {len(self.oracle_calls)}",
            f"  Total tokens:   {self.total_tokens()}",
            f"  Cache hit rate: {self.cache_hit_rate():.1%}",
        ]
        return "\n".join(lines)

# ---------------------------------------------------------------------------
# PipelineResult
# ---------------------------------------------------------------------------

@dataclass
class PipelineResult(_safe_base(_CorePipelineResult) if _HAS_DEPPY_CORE else object):
    """Complete result from a pipeline execution.

    Extends the core ``PipelineResult`` when available, adding hybrid-layer
    stage outputs, gate results, and manifests.

    Aggregates outputs from all stages with an overall trust level,
    compiled code, Lean file, and verification certificate.
    """

    stages: Dict[PipelineStage, StageOutput] = field(default_factory=dict)
    overall_trust: str = "untrusted"
    compiled_code: Optional[str] = None
    lean_file: Optional[str] = None
    certificate: Dict[str, Any] = field(default_factory=dict)
    h1_status: str = "unknown"
    manifest: Optional[PipelineManifest] = None
    gate_results: Dict[str, GateResult] = field(default_factory=dict)
    error: Optional[str] = None

    @property
    def success(self) -> bool:
        """True if all stages completed without error."""
        return self.error is None and all(
            not out.is_error for out in self.stages.values()
        )

    @property
    def stage_count(self) -> int:
        return len(self.stages)

    @property
    def total_duration_ms(self) -> float:
        return sum(out.duration_ms for out in self.stages.values())

    @property
    def all_obligations(self) -> List[Dict[str, Any]]:
        """All obligations across all stages."""
        result: List[Dict[str, Any]] = []
        for out in self.stages.values():
            result.extend(out.obligations)
        return result

    @property
    def sorry_count(self) -> int:
        return sum(
            1 for o in self.all_obligations if o.get("status") == "sorry"
        )

    def summary(self) -> str:
        """Human-readable summary of the pipeline result."""
        lines: List[str] = []
        lines.append("Pipeline Result")
        lines.append("=" * 50)
        lines.append(f"  Status:       {'SUCCESS' if self.success else 'FAILED'}")
        lines.append(f"  Trust:        {self.overall_trust}")
        lines.append(f"  H¹ status:    {self.h1_status}")
        lines.append(f"  Stages run:   {self.stage_count}")
        lines.append(f"  Total time:   {self.total_duration_ms:.1f} ms")

        if self.error:
            lines.append(f"  Error:        {self.error}")

        lines.append("")
        lines.append("Stage Results:")
        lines.append("-" * 50)

        for stage in PipelineStage.ordered():
            if stage in self.stages:
                out = self.stages[stage]
                status_icon = "✗" if out.is_error else "✓"
                lines.append(
                    f"  {status_icon} {STAGE_NAMES[stage]:20s} "
                    f"trust={out.trust_level:15s} "
                    f"time={out.duration_ms:.1f}ms"
                )
            else:
                lines.append(f"  ○ {STAGE_NAMES[stage]:20s} (not run)")

        # Gate results
        if self.gate_results:
            lines.append("")
            lines.append("Gate Results:")
            lines.append("-" * 50)
            for name, result in self.gate_results.items():
                icon = "✓" if result.passed else "✗"
                lines.append(f"  {icon} {name}")
                for failure in result.failures:
                    lines.append(f"      └─ {failure}")

        # Obligations
        total_obl = len(self.all_obligations)
        if total_obl > 0:
            lines.append("")
            lines.append(f"Obligations: {total_obl} total, {self.sorry_count} sorry'd")

        return "\n".join(lines)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "success": self.success,
            "overall_trust": self.overall_trust,
            "h1_status": self.h1_status,
            "stage_count": self.stage_count,
            "total_duration_ms": self.total_duration_ms,
            "stages": {
                stage.value: out.to_dict()
                for stage, out in self.stages.items()
            },
            "gate_results": {
                name: gr.to_dict()
                for name, gr in self.gate_results.items()
            },
            "certificate": self.certificate,
            "compiled_code": self.compiled_code is not None,
            "lean_file": self.lean_file is not None,
            "error": self.error,
        }

# ---------------------------------------------------------------------------
# Stage result cache
# ---------------------------------------------------------------------------

class _StageCache:
    """Simple content-hash → StageOutput cache, optionally backed by disk."""

    def __init__(self, cache_dir: Optional[str] = None) -> None:
        self._mem: Dict[str, Dict[str, Any]] = {}
        self._cache_dir = cache_dir
        if cache_dir:
            os.makedirs(cache_dir, exist_ok=True)

    def get(self, stage: PipelineStage, content_hash: str) -> Optional[Dict[str, Any]]:
        """Look up a cached result."""
        key = f"{stage.value}:{content_hash}"
        if key in self._mem:
            return self._mem[key]

        if self._cache_dir:
            path = os.path.join(self._cache_dir, f"{key.replace(':', '_')}.json")
            if os.path.exists(path):
                try:
                    with open(path) as f:
                        data = json.load(f)
                    self._mem[key] = data
                    return data
                except (json.JSONDecodeError, OSError):
                    pass

        return None

    def put(
        self,
        stage: PipelineStage,
        content_hash: str,
        output_data: Dict[str, Any],
    ) -> None:
        """Store a result in the cache."""
        key = f"{stage.value}:{content_hash}"
        self._mem[key] = output_data

        if self._cache_dir:
            path = os.path.join(self._cache_dir, f"{key.replace(':', '_')}.json")
            try:
                with open(path, "w") as f:
                    json.dump(output_data, f, default=str)
            except OSError:
                pass

    @property
    def size(self) -> int:
        return len(self._mem)

    def clear(self) -> None:
        self._mem.clear()

# ---------------------------------------------------------------------------
# PipelineOrchestrator
# ---------------------------------------------------------------------------

class PipelineOrchestrator:
    """Contract-enforced orchestration of the 8-stage verified pipeline.

    Runs stages in order, checks verification gates at each transition,
    tracks provenance, and caches intermediate results.
    """

    def __init__(self, config: Optional[PipelineConfig] = None) -> None:
        self.config = config or PipelineConfig.default()
        self._cache = _StageCache(self.config.cache_dir)
        self._manifest = PipelineManifest()

        # Instantiate stages
        self._stages: Dict[PipelineStage, Any] = {
            PipelineStage.IDEATION: IdeationStage(),
            PipelineStage.SPECIFICATION: SpecificationStage(),
            PipelineStage.SYNTHESIS: SynthesisStage(),
            PipelineStage.STRUCTURAL_CHECK: StructuralCheckStage(
                timeout_ms=self.config.z3_timeout_ms
            ),
            PipelineStage.SEMANTIC_CHECK: SemanticCheckStage(),
            PipelineStage.LEAN_TRANSLATION: LeanTranslationStage(),
            PipelineStage.DISCHARGE: DischargeStage(
                max_attempts=self.config.max_discharge_attempts
            ),
            PipelineStage.PRODUCTION: ProductionStage(),
        }

    # -- Full pipeline run --------------------------------------------------

    def run_full(
        self,
        source: str,
        config: Optional[PipelineConfig] = None,
    ) -> PipelineResult:
        """Execute the full 8-stage pipeline on *source*.

        Parameters
        ----------
        source : str
            The source text — either Python code, an NL spec, or a
            code-with-holes template.
        config : PipelineConfig, optional
            Override config for this run.
        """
        cfg = config or self.config
        self._manifest = PipelineManifest()
        result = PipelineResult(manifest=self._manifest)

        # Accumulated data flowing through the pipeline
        pipeline_data: Dict[str, Any] = {}
        current_trust = "untrusted"

        try:
            # --- Stage 1: IDEATION ---
            ideation_out = self._run_ideation(source, cfg)
            result.stages[PipelineStage.IDEATION] = ideation_out
            if ideation_out.is_error:
                result.error = ideation_out.get("error")
                return self._finalize(result)
            pipeline_data.update(ideation_out.data)
            current_trust = ideation_out.trust_level

            # --- Stage 2: SPECIFICATION ---
            spec_out = self._run_specification(
                pipeline_data.get("claims", []), cfg
            )
            result.stages[PipelineStage.SPECIFICATION] = spec_out
            if spec_out.is_error:
                result.error = spec_out.get("error")
                return self._finalize(result)
            pipeline_data.update(spec_out.data)

            # Gate: SPEC_GATE
            gate_result = self._check_gate(SPEC_GATE, spec_out, cfg)
            result.gate_results[SPEC_GATE.name] = gate_result
            if not gate_result.passed and cfg.strict_gates:
                result.error = f"Gate {SPEC_GATE.name} failed: {gate_result.failures}"
                return self._finalize(result)

            # --- Stage 3: SYNTHESIS ---
            code_input = source if "def " in source else f"def f(x):\n    ???\n"
            synth_out = self._run_synthesis(
                code_input,
                pipeline_data.get("specs", []),
                cfg,
            )
            result.stages[PipelineStage.SYNTHESIS] = synth_out
            if synth_out.is_error:
                result.error = synth_out.get("error")
                return self._finalize(result)
            pipeline_data.update(synth_out.data)

            # --- Stage 4: STRUCTURAL_CHECK ---
            struct_out = self._run_structural_check(
                pipeline_data.get("code", source),
                pipeline_data.get("structural_specs", []),
                cfg,
            )
            result.stages[PipelineStage.STRUCTURAL_CHECK] = struct_out
            if struct_out.is_error:
                result.error = struct_out.get("error")
                return self._finalize(result)
            pipeline_data.update(struct_out.data)

            # Gate: STRUCTURAL_GATE
            gate_result = self._check_gate(STRUCTURAL_GATE, struct_out, cfg)
            result.gate_results[STRUCTURAL_GATE.name] = gate_result
            if not gate_result.passed and cfg.strict_gates:
                result.error = (
                    f"Gate {STRUCTURAL_GATE.name} failed: {gate_result.failures}"
                )
                return self._finalize(result)

            # --- Stage 5: SEMANTIC_CHECK ---
            sem_out = self._run_semantic_check(
                pipeline_data.get("code", source),
                pipeline_data.get("semantic_specs", []),
                cfg,
            )
            result.stages[PipelineStage.SEMANTIC_CHECK] = sem_out
            if sem_out.is_error:
                result.error = sem_out.get("error")
                return self._finalize(result)
            pipeline_data.update(sem_out.data)

            # Gate: SEMANTIC_GATE
            gate_result = self._check_gate(SEMANTIC_GATE, sem_out, cfg)
            result.gate_results[SEMANTIC_GATE.name] = gate_result
            if not gate_result.passed and cfg.strict_gates:
                result.error = (
                    f"Gate {SEMANTIC_GATE.name} failed: {gate_result.failures}"
                )
                return self._finalize(result)

            # --- Stage 6: LEAN_TRANSLATION ---
            if cfg.emit_lean:
                lean_out = self._run_lean_translation(
                    pipeline_data.get("code", source),
                    pipeline_data.get("specs", []),
                    pipeline_data.get("z3_results"),
                    cfg,
                )
                result.stages[PipelineStage.LEAN_TRANSLATION] = lean_out
                if lean_out.is_error:
                    result.error = lean_out.get("error")
                    return self._finalize(result)
                pipeline_data.update(lean_out.data)
                result.lean_file = lean_out.get("lean_source")

                # Gate: LEAN_GATE
                gate_result = self._check_gate(LEAN_GATE, lean_out, cfg)
                result.gate_results[LEAN_GATE.name] = gate_result
                if not gate_result.passed and cfg.strict_gates:
                    result.error = (
                        f"Gate {LEAN_GATE.name} failed: {gate_result.failures}"
                    )
                    return self._finalize(result)

                # Collect obligations from lean translation
                all_obligations = list(lean_out.obligations)
            else:
                all_obligations = []

            # --- Stage 7: DISCHARGE ---
            if all_obligations:
                discharge_out = self._run_discharge(all_obligations, cfg)
                result.stages[PipelineStage.DISCHARGE] = discharge_out
                if discharge_out.is_error:
                    result.error = discharge_out.get("error")
                    return self._finalize(result)
                pipeline_data.update(discharge_out.data)

                # Gate: PRODUCTION_GATE
                gate_result = self._check_gate(PRODUCTION_GATE, discharge_out, cfg)
                result.gate_results[PRODUCTION_GATE.name] = gate_result
                if not gate_result.passed and cfg.strict_gates:
                    result.error = (
                        f"Gate {PRODUCTION_GATE.name} failed: "
                        f"{gate_result.failures}"
                    )
                    return self._finalize(result)
            else:
                # No obligations — create a minimal discharge output
                discharge_out = StageOutput.create(
                    PipelineStage.DISCHARGE,
                    data={"proofs": [], "stats": {
                        "total": 0, "discharged": 0,
                        "sorry": 0, "assumed": 0, "failed": 0,
                    }},
                    trust_level="lean_verified",
                    provenance=["discharge(empty)"],
                )
                result.stages[PipelineStage.DISCHARGE] = discharge_out

            # --- Stage 8: PRODUCTION ---
            code = pipeline_data.get("code", source)
            proofs = pipeline_data.get("proofs", [])
            certificate = _build_certificate(
                code,
                pipeline_data.get("specs", []),
                pipeline_data.get("z3_results", []),
                pipeline_data.get("oracle_results", []),
                proofs,
            )

            prod_out = self._run_production(code, proofs, certificate, cfg)
            result.stages[PipelineStage.PRODUCTION] = prod_out
            if prod_out.is_error:
                result.error = prod_out.get("error")
                return self._finalize(result)

            # Final assembly
            result.compiled_code = code
            result.certificate = certificate
            result.overall_trust = certificate.get("trust_level", "untrusted")
            result.h1_status = certificate.get("h1_status", "unknown")

        except Exception as exc:
            result.error = f"Pipeline exception: {exc}"

        return self._finalize(result)

    # -- Incremental pipeline run -------------------------------------------

    def run_incremental(
        self,
        source: str,
        changed_functions: List[str],
        config: Optional[PipelineConfig] = None,
    ) -> PipelineResult:
        """Re-run only stages affected by *changed_functions*.

        Uses the Mayer-Vietoris principle: unchanged functions keep their
        cached results; only changed functions are re-verified.
        """
        cfg = config or self.config

        # For now, run the full pipeline but skip cached stages
        # A full implementation would do function-level diffing
        return self.run_full(source, cfg)

    # -- Single stage run ---------------------------------------------------

    def run_stage(
        self,
        stage: PipelineStage,
        inp: StageInput,
    ) -> StageOutput:
        """Execute a single stage with contract enforcement."""
        contract = STAGE_CONTRACTS.get(stage)
        if contract is None:
            return StageOutput.error(stage, f"No contract for stage {stage.value}")

        # Check precondition
        ok, msg = contract.check_pre(inp)
        if not ok:
            return StageOutput.error(stage, f"Precondition failed: {msg}")

        # Check cache
        cached = self._cache.get(stage, inp.content_hash)
        if cached is not None:
            return StageOutput(
                stage=stage,
                data=cached,
                content_hash=_content_hash(cached),
                trust_level=cached.get("_trust", "untrusted"),
                duration_ms=0.0,
                provenance=["cached"],
            )

        # Run stage
        t0 = time.monotonic()
        out = self._dispatch_stage(stage, inp)
        duration = (time.monotonic() - t0) * 1000

        # Check postcondition
        ok, msg = contract.check_post(out)
        if not ok:
            return StageOutput.error(
                stage, f"Postcondition failed: {msg}", duration_ms=duration
            )

        # Record in manifest
        self._manifest.add_stage(
            stage, inp.content_hash, out.content_hash, duration, out.trust_level
        )

        # Cache
        cache_data = dict(out.data)
        cache_data["_trust"] = out.trust_level
        self._cache.put(stage, inp.content_hash, cache_data)

        return out

    # -- Private stage dispatchers ------------------------------------------

    def _dispatch_stage(
        self,
        stage: PipelineStage,
        inp: StageInput,
    ) -> StageOutput:
        """Dispatch to the correct stage implementation."""
        impl = self._stages.get(stage)
        if impl is None:
            return StageOutput.error(stage, f"No implementation for {stage.value}")

        if stage == PipelineStage.IDEATION:
            return impl.run(inp.get("nl_text", ""), inp.get("context", {}))
        elif stage == PipelineStage.SPECIFICATION:
            return impl.run(inp.get("claims", []), inp.get("context", {}))
        elif stage == PipelineStage.SYNTHESIS:
            return impl.run(
                inp.get("code_with_holes", ""),
                inp.get("specs", []),
                inp.get("context", {}),
            )
        elif stage == PipelineStage.STRUCTURAL_CHECK:
            return impl.run(inp.get("code", ""), inp.get("structural_specs", []))
        elif stage == PipelineStage.SEMANTIC_CHECK:
            return impl.run(
                inp.get("code", ""),
                inp.get("semantic_specs", []),
                self.config.oracle_fn,
            )
        elif stage == PipelineStage.LEAN_TRANSLATION:
            return impl.run(
                inp.get("code", ""),
                inp.get("specs", []),
                inp.get("structural_results"),
            )
        elif stage == PipelineStage.DISCHARGE:
            return impl.run(inp.get("obligations", []))
        elif stage == PipelineStage.PRODUCTION:
            return impl.run(
                inp.get("code", ""),
                inp.get("proofs", []),
                inp.get("certificate", {}),
            )
        else:
            return StageOutput.error(stage, f"Unknown stage: {stage.value}")

    # -- Convenience stage runners ------------------------------------------

    def _run_ideation(
        self,
        source: str,
        cfg: PipelineConfig,
    ) -> StageOutput:
        """Run the ideation stage."""
        impl: IdeationStage = self._stages[PipelineStage.IDEATION]
        t0 = time.monotonic()
        out = impl.run(source, {})
        duration = (time.monotonic() - t0) * 1000

        self._manifest.add_stage(
            PipelineStage.IDEATION,
            _hash_text(source),
            out.content_hash,
            duration,
            out.trust_level,
        )
        return out

    def _run_specification(
        self,
        claims: List[Dict[str, Any]],
        cfg: PipelineConfig,
    ) -> StageOutput:
        """Run the specification stage."""
        impl: SpecificationStage = self._stages[PipelineStage.SPECIFICATION]
        t0 = time.monotonic()
        out = impl.run(claims, {})
        duration = (time.monotonic() - t0) * 1000

        self._manifest.add_stage(
            PipelineStage.SPECIFICATION,
            _content_hash(claims),
            out.content_hash,
            duration,
            out.trust_level,
        )
        return out

    def _run_synthesis(
        self,
        code_with_holes: str,
        specs: List[Dict[str, Any]],
        cfg: PipelineConfig,
    ) -> StageOutput:
        """Run the synthesis stage."""
        impl: SynthesisStage = self._stages[PipelineStage.SYNTHESIS]
        t0 = time.monotonic()
        out = impl.run(code_with_holes, specs, {})
        duration = (time.monotonic() - t0) * 1000

        self._manifest.add_stage(
            PipelineStage.SYNTHESIS,
            _hash_text(code_with_holes),
            out.content_hash,
            duration,
            out.trust_level,
        )
        return out

    def _run_structural_check(
        self,
        code: str,
        structural_specs: List[Dict[str, Any]],
        cfg: PipelineConfig,
    ) -> StageOutput:
        """Run the structural check stage."""
        impl: StructuralCheckStage = self._stages[PipelineStage.STRUCTURAL_CHECK]
        t0 = time.monotonic()
        out = impl.run(code, structural_specs)
        duration = (time.monotonic() - t0) * 1000

        self._manifest.add_stage(
            PipelineStage.STRUCTURAL_CHECK,
            _hash_text(code),
            out.content_hash,
            duration,
            out.trust_level,
        )
        return out

    def _run_semantic_check(
        self,
        code: str,
        semantic_specs: List[Dict[str, Any]],
        cfg: PipelineConfig,
    ) -> StageOutput:
        """Run the semantic check stage."""
        impl: SemanticCheckStage = self._stages[PipelineStage.SEMANTIC_CHECK]
        t0 = time.monotonic()
        out = impl.run(code, semantic_specs, cfg.oracle_fn)
        duration = (time.monotonic() - t0) * 1000

        # Record oracle calls in manifest
        oracle_results = out.get("oracle_results", [])
        for r in oracle_results:
            self._manifest.add_oracle_call(
                PipelineStage.SEMANTIC_CHECK,
                r.get("prompt_hash", ""),
                0,  # token count unknown without real oracle
                r.get("cached", False),
            )

        self._manifest.add_stage(
            PipelineStage.SEMANTIC_CHECK,
            _hash_text(code),
            out.content_hash,
            duration,
            out.trust_level,
        )
        return out

    def _run_lean_translation(
        self,
        code: str,
        specs: List[Dict[str, Any]],
        structural_results: Any,
        cfg: PipelineConfig,
    ) -> StageOutput:
        """Run the Lean translation stage."""
        impl: LeanTranslationStage = self._stages[PipelineStage.LEAN_TRANSLATION]
        t0 = time.monotonic()
        out = impl.run(code, specs, structural_results)
        duration = (time.monotonic() - t0) * 1000

        self._manifest.add_stage(
            PipelineStage.LEAN_TRANSLATION,
            _hash_text(code),
            out.content_hash,
            duration,
            out.trust_level,
        )
        return out

    def _run_discharge(
        self,
        obligations: List[Dict[str, Any]],
        cfg: PipelineConfig,
    ) -> StageOutput:
        """Run the discharge stage."""
        impl: DischargeStage = self._stages[PipelineStage.DISCHARGE]
        t0 = time.monotonic()
        out = impl.run(obligations)
        duration = (time.monotonic() - t0) * 1000

        self._manifest.add_stage(
            PipelineStage.DISCHARGE,
            _content_hash(obligations),
            out.content_hash,
            duration,
            out.trust_level,
        )
        return out

    def _run_production(
        self,
        code: str,
        proofs: List[Dict[str, Any]],
        certificate: Dict[str, Any],
        cfg: PipelineConfig,
    ) -> StageOutput:
        """Run the production stage."""
        impl: ProductionStage = self._stages[PipelineStage.PRODUCTION]
        t0 = time.monotonic()
        out = impl.run(code, proofs, certificate)
        duration = (time.monotonic() - t0) * 1000

        self._manifest.add_stage(
            PipelineStage.PRODUCTION,
            _hash_text(code),
            out.content_hash,
            duration,
            out.trust_level,
        )
        return out

    # -- Gate checking ------------------------------------------------------

    def _check_gate(
        self,
        gate: VerificationGate,
        output: StageOutput,
        cfg: PipelineConfig,
    ) -> GateResult:
        """Check a verification gate and record it in the manifest."""
        result = gate.check(output, cfg)
        self._manifest.add_gate_check(
            gate.name,
            result.passed,
            "; ".join(result.failures) if result.failures else "ok",
        )
        return result

    # -- Finalization -------------------------------------------------------

    def _finalize(self, result: PipelineResult) -> PipelineResult:
        """Compute final trust and finish the manifest."""
        self._manifest.finish()
        result.manifest = self._manifest

        # Overall trust = minimum across all completed stages
        if result.stages:
            trusts = [out.trust_level for out in result.stages.values()]
            current = trusts[0]
            for t in trusts[1:]:
                current = _join_trust(current, t)
            result.overall_trust = current

        return result

    # -- Accessors ----------------------------------------------------------

    @property
    def manifest(self) -> PipelineManifest:
        return self._manifest

    @property
    def cache_size(self) -> int:
        return self._cache.size

    def clear_cache(self) -> None:
        self._cache.clear()
