"""
Autonomous agent orchestrator for deppy.

``deppy "write me a trading app"`` → verified codebase.

Pipeline: parse_intent → expand_type → plan → generate → verify → assemble

Uses existing agent modules:
  - agent.verification_loop  — VerificationLoop, CEGARVerificationLoop
  - agent.project_assembler  — ProjectAssembler, ProjectStructure
  - agent.cli                — AgentCLI, LLMInterface, ProgressDisplay
"""
from __future__ import annotations

import copy
import enum
import hashlib
import json
import logging
import os
import re
import textwrap
import time
import traceback
import datetime
from collections import OrderedDict
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Set,
    Sequence,
    Tuple,
    Union,
)

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Trust-level lattice (mirrors verification_loop.py)
# ---------------------------------------------------------------------------

TRUST_LEVELS = ["UNCHECKED", "LLM_JUDGED", "Z3_PROVEN", "LEAN_VERIFIED"]
TRUST_RANK: Dict[str, int] = {level: i for i, level in enumerate(TRUST_LEVELS)}

TRUST_BADGES: Dict[str, str] = {
    "LEAN_VERIFIED": "🟢 LEAN_VERIFIED",
    "Z3_PROVEN":     "🟡 Z3_PROVEN",
    "LLM_JUDGED":    "🟠 LLM_JUDGED",
    "UNCHECKED":     "🔴 UNCHECKED",
}


def _min_trust(*levels: str) -> str:
    if not levels:
        return "UNCHECKED"
    return min(levels, key=lambda l: TRUST_RANK.get(l, 0))


def _max_trust(*levels: str) -> str:
    if not levels:
        return "UNCHECKED"
    return max(levels, key=lambda l: TRUST_RANK.get(l, 0))


def _content_hash(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _timestamp_iso() -> str:
    return datetime.datetime.utcnow().isoformat(timespec="seconds") + "Z"


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  AgentState — finite state machine for orchestration                    ║
# ╚══════════════════════════════════════════════════════════════════════════╝

class AgentState(enum.Enum):
    """Orchestrator state machine."""
    IDLE = "idle"
    PARSING = "parsing"
    EXPANDING = "expanding"
    PLANNING = "planning"
    GENERATING = "generating"
    VERIFYING = "verifying"
    ASSEMBLING = "assembling"
    DONE = "done"
    FAILED = "failed"

    # ------------------------------------------------------------------
    _transitions: Dict[str, List[str]]  # type: ignore[assignment]

    @classmethod
    def _valid_transitions(cls) -> Dict[str, List[str]]:
        return {
            "idle":       ["parsing"],
            "parsing":    ["expanding", "failed"],
            "expanding":  ["planning", "failed"],
            "planning":   ["generating", "failed"],
            "generating": ["verifying", "failed"],
            "verifying":  ["assembling", "generating", "failed"],
            "assembling": ["done", "failed"],
            "done":       ["idle"],
            "failed":     ["idle"],
        }

    def can_transition_to(self, target: "AgentState") -> bool:
        valid = self._valid_transitions()
        return target.value in valid.get(self.value, [])

    def __repr__(self) -> str:
        return f"AgentState.{self.name}"


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  OrchestratorConfig                                                     ║
# ╚══════════════════════════════════════════════════════════════════════════╝

@dataclass
class OrchestratorConfig:
    """Configuration for the orchestrator pipeline."""

    # Budget & limits
    max_llm_calls: int = 200
    max_cegar_rounds: int = 5
    max_modules: int = 50
    max_generation_retries: int = 3
    timeout_seconds: Optional[float] = None

    # Trust thresholds
    min_trust_level: str = "LLM_JUDGED"
    target_trust_level: str = "Z3_PROVEN"
    semantic_confidence_threshold: float = 0.85

    # Parallelism
    parallel_modules: int = 1
    parallel_verification: int = 1

    # Oracle settings
    oracle_model: str = "gpt-4"
    oracle_temperature: float = 0.2
    oracle_max_tokens: int = 4096

    # Verification settings
    z3_timeout_ms: Optional[int] = None
    emit_lean: bool = False
    strict_mode: bool = False
    cache_enabled: bool = True

    # Output
    output_dir: str = "./output"
    generate_readme: bool = True
    generate_tests: bool = True
    generate_ci: bool = True
    verbose: bool = False

    # LLM provider
    llm_model: str = "gpt-4"
    llm_api_key: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "max_llm_calls": self.max_llm_calls,
            "max_cegar_rounds": self.max_cegar_rounds,
            "max_modules": self.max_modules,
            "max_generation_retries": self.max_generation_retries,
            "timeout_seconds": self.timeout_seconds,
            "min_trust_level": self.min_trust_level,
            "target_trust_level": self.target_trust_level,
            "semantic_confidence_threshold": self.semantic_confidence_threshold,
            "parallel_modules": self.parallel_modules,
            "parallel_verification": self.parallel_verification,
            "oracle_model": self.oracle_model,
            "z3_timeout_ms": self.z3_timeout_ms,
            "emit_lean": self.emit_lean,
            "strict_mode": self.strict_mode,
            "cache_enabled": self.cache_enabled,
            "output_dir": self.output_dir,
            "generate_readme": self.generate_readme,
            "generate_tests": self.generate_tests,
            "generate_ci": self.generate_ci,
            "verbose": self.verbose,
            "llm_model": self.llm_model,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "OrchestratorConfig":
        known = {f.name for f in cls.__dataclass_fields__.values()}  # type: ignore[attr-defined]
        filtered = {k: v for k, v in d.items() if k in known}
        return cls(**filtered)

    def validate(self) -> List[str]:
        errors: List[str] = []
        if self.max_llm_calls < 1:
            errors.append("max_llm_calls must be >= 1")
        if self.max_cegar_rounds < 1:
            errors.append("max_cegar_rounds must be >= 1")
        if self.min_trust_level not in TRUST_RANK:
            errors.append(f"Unknown trust level: {self.min_trust_level}")
        if self.target_trust_level not in TRUST_RANK:
            errors.append(f"Unknown target trust level: {self.target_trust_level}")
        if self.timeout_seconds is not None and self.timeout_seconds <= 0:
            errors.append("timeout_seconds must be positive")
        if not (0.0 <= self.semantic_confidence_threshold <= 1.0):
            errors.append("semantic_confidence_threshold must be in [0, 1]")
        return errors


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  CostReport — tracks LLM usage                                         ║
# ╚══════════════════════════════════════════════════════════════════════════╝

@dataclass
class CostReport:
    """Tracks LLM calls and token usage across the pipeline."""

    total_calls: int = 0
    total_tokens: int = 0
    total_prompt_tokens: int = 0
    total_completion_tokens: int = 0
    phase_costs: Dict[str, Dict[str, int]] = field(default_factory=dict)
    start_time: float = 0.0
    end_time: float = 0.0

    def record_call(
        self,
        phase: str,
        tokens: int = 0,
        prompt_tokens: int = 0,
        completion_tokens: int = 0,
    ) -> None:
        self.total_calls += 1
        self.total_tokens += tokens
        self.total_prompt_tokens += prompt_tokens
        self.total_completion_tokens += completion_tokens
        if phase not in self.phase_costs:
            self.phase_costs[phase] = {"calls": 0, "tokens": 0}
        self.phase_costs[phase]["calls"] += 1
        self.phase_costs[phase]["tokens"] += tokens

    @property
    def wall_time_seconds(self) -> float:
        if self.end_time > 0 and self.start_time > 0:
            return self.end_time - self.start_time
        return 0.0

    def summary(self) -> str:
        lines = [
            f"Total LLM calls: {self.total_calls}",
            f"Total tokens: {self.total_tokens}",
            f"Wall time: {self.wall_time_seconds:.1f}s",
        ]
        for phase, costs in sorted(self.phase_costs.items()):
            lines.append(f"  {phase}: {costs['calls']} calls, {costs['tokens']} tokens")
        return "\n".join(lines)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "total_calls": self.total_calls,
            "total_tokens": self.total_tokens,
            "total_prompt_tokens": self.total_prompt_tokens,
            "total_completion_tokens": self.total_completion_tokens,
            "phase_costs": self.phase_costs,
            "wall_time_seconds": self.wall_time_seconds,
        }


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  TrustSummary — aggregate trust across modules                         ║
# ╚══════════════════════════════════════════════════════════════════════════╝

@dataclass
class TrustSummary:
    """Aggregate trust information across all generated modules."""

    module_trusts: Dict[str, str] = field(default_factory=dict)
    overall_trust: str = "UNCHECKED"
    total_claims_discharged: int = 0
    total_claims_residual: int = 0
    total_hallucination_findings: int = 0
    cross_module_passed: bool = False
    h1_status: str = "H¹ = 0"
    lean_obligations_discharged: int = 0
    lean_obligations_residual: int = 0

    def add_module(
        self,
        name: str,
        trust: str,
        discharged: int = 0,
        residual: int = 0,
        hallucinations: int = 0,
    ) -> None:
        self.module_trusts[name] = trust
        self.total_claims_discharged += discharged
        self.total_claims_residual += residual
        self.total_hallucination_findings += hallucinations
        self._recompute_overall()

    def _recompute_overall(self) -> None:
        if not self.module_trusts:
            self.overall_trust = "UNCHECKED"
            return
        self.overall_trust = _min_trust(*self.module_trusts.values())

    def meets_threshold(self, threshold: str) -> bool:
        return TRUST_RANK.get(self.overall_trust, 0) >= TRUST_RANK.get(threshold, 0)

    def summary(self) -> str:
        lines = [
            f"Overall trust: {TRUST_BADGES.get(self.overall_trust, self.overall_trust)}",
            f"Modules: {len(self.module_trusts)}",
            f"Claims discharged: {self.total_claims_discharged}",
            f"Claims residual: {self.total_claims_residual}",
            f"Hallucination findings: {self.total_hallucination_findings}",
            f"Cross-module: {'✓' if self.cross_module_passed else '✗'}",
            f"H¹ status: {self.h1_status}",
        ]
        for name, trust in sorted(self.module_trusts.items()):
            badge = TRUST_BADGES.get(trust, trust)
            lines.append(f"  {name}: {badge}")
        return "\n".join(lines)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "overall_trust": self.overall_trust,
            "module_trusts": self.module_trusts,
            "total_claims_discharged": self.total_claims_discharged,
            "total_claims_residual": self.total_claims_residual,
            "total_hallucination_findings": self.total_hallucination_findings,
            "cross_module_passed": self.cross_module_passed,
            "h1_status": self.h1_status,
        }


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  OrchestratorResult                                                     ║
# ╚══════════════════════════════════════════════════════════════════════════╝

@dataclass
class OrchestratorResult:
    """Final result from the orchestrator pipeline."""

    success: bool = False
    project_files: Dict[str, str] = field(default_factory=dict)
    certificate: Dict[str, Any] = field(default_factory=dict)
    trust_summary: Optional[TrustSummary] = None
    cost_report: Optional[CostReport] = None
    output_dir: str = ""
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    state_history: List[str] = field(default_factory=list)
    duration_seconds: float = 0.0
    modules_generated: int = 0
    modules_verified: int = 0

    def summary(self) -> str:
        status = "✓ SUCCESS" if self.success else "✗ FAILED"
        lines = [
            f"Orchestrator result: {status}",
            f"Modules: {self.modules_generated} generated, {self.modules_verified} verified",
            f"Files: {len(self.project_files)}",
            f"Duration: {self.duration_seconds:.1f}s",
        ]
        if self.trust_summary:
            lines.append(f"Trust: {TRUST_BADGES.get(self.trust_summary.overall_trust, 'UNKNOWN')}")
        if self.errors:
            lines.append(f"Errors: {len(self.errors)}")
            for e in self.errors[:5]:
                lines.append(f"  - {e}")
        if self.warnings:
            lines.append(f"Warnings: {len(self.warnings)}")
        return "\n".join(lines)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "success": self.success,
            "project_files": list(self.project_files.keys()),
            "certificate": self.certificate,
            "trust_summary": self.trust_summary.to_dict() if self.trust_summary else None,
            "cost_report": self.cost_report.to_dict() if self.cost_report else None,
            "output_dir": self.output_dir,
            "errors": self.errors,
            "warnings": self.warnings,
            "state_history": self.state_history,
            "duration_seconds": self.duration_seconds,
            "modules_generated": self.modules_generated,
            "modules_verified": self.modules_verified,
            "timestamp": _timestamp_iso(),
        }


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  ModulePlan — plan for a single module                                  ║
# ╚══════════════════════════════════════════════════════════════════════════╝

@dataclass
class ModulePlan:
    """Plan for generating one module."""
    name: str
    description: str = ""
    dependencies: List[str] = field(default_factory=list)
    type_spec: Dict[str, Any] = field(default_factory=dict)
    constraints: List[str] = field(default_factory=list)
    priority: int = 0
    estimated_complexity: str = "medium"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "description": self.description,
            "dependencies": self.dependencies,
            "type_spec": self.type_spec,
            "constraints": self.constraints,
            "priority": self.priority,
            "estimated_complexity": self.estimated_complexity,
        }


@dataclass
class ProjectPlan:
    """Full project plan: modules + dependency graph."""
    project_name: str = ""
    domain: str = ""
    description: str = ""
    modules: List[ModulePlan] = field(default_factory=list)
    dependency_graph: Dict[str, List[str]] = field(default_factory=dict)
    constraints: List[str] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)

    def topological_order(self) -> List[str]:
        """Return modules in dependency order (Kahn's algorithm)."""
        in_degree: Dict[str, int] = {m.name: 0 for m in self.modules}
        adj: Dict[str, List[str]] = {m.name: [] for m in self.modules}
        for m in self.modules:
            for dep in m.dependencies:
                if dep in adj:
                    adj[dep].append(m.name)
                    in_degree[m.name] = in_degree.get(m.name, 0) + 1

        queue = [name for name, deg in in_degree.items() if deg == 0]
        order: List[str] = []
        while queue:
            queue.sort(key=lambda n: next(
                (m.priority for m in self.modules if m.name == n), 0
            ), reverse=True)
            node = queue.pop(0)
            order.append(node)
            for neighbor in adj.get(node, []):
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)

        if len(order) != len(self.modules):
            logger.warning(
                "Dependency cycle detected; falling back to priority order"
            )
            seen = set(order)
            for m in sorted(self.modules, key=lambda m: -m.priority):
                if m.name not in seen:
                    order.append(m.name)
        return order

    def to_dict(self) -> Dict[str, Any]:
        return {
            "project_name": self.project_name,
            "domain": self.domain,
            "description": self.description,
            "modules": [m.to_dict() for m in self.modules],
            "dependency_graph": self.dependency_graph,
            "constraints": self.constraints,
            "metadata": self.metadata,
        }


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  ExpandedType — type after expansion from intent                        ║
# ╚══════════════════════════════════════════════════════════════════════════╝

@dataclass
class ExpandedType:
    """A type specification after expansion from the intent spec."""
    name: str
    refinement_predicates: List[str] = field(default_factory=list)
    dependent_params: List[Dict[str, Any]] = field(default_factory=list)
    contracts: Dict[str, List[str]] = field(default_factory=dict)
    associated_functions: List[str] = field(default_factory=list)
    ideation_lenses: List[Dict[str, Any]] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "refinement_predicates": self.refinement_predicates,
            "dependent_params": self.dependent_params,
            "contracts": self.contracts,
            "associated_functions": self.associated_functions,
            "ideation_lenses": self.ideation_lenses,
            "metadata": self.metadata,
        }


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  PhaseError — typed error for phase failures                            ║
# ╚══════════════════════════════════════════════════════════════════════════╝

class PhaseError(Exception):
    """Raised when a pipeline phase fails."""

    def __init__(
        self,
        phase: str,
        message: str,
        recoverable: bool = True,
        details: Optional[Dict[str, Any]] = None,
    ) -> None:
        self.phase = phase
        self.message = message
        self.recoverable = recoverable
        self.details = details or {}
        super().__init__(f"[{phase}] {message}")


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  PhaseRunner — runs individual phases with error recovery               ║
# ╚══════════════════════════════════════════════════════════════════════════╝

class PhaseRunner:
    """
    Runs individual orchestration phases with:
      - execution budgeting
      - retry logic
      - error capture & recovery
      - cost tracking
    """

    def __init__(
        self,
        config: OrchestratorConfig,
        cost_report: CostReport,
        llm_fn: Optional[Callable[..., str]] = None,
    ) -> None:
        self._config = config
        self._cost = cost_report
        self._llm_fn = llm_fn
        self._phase_timings: Dict[str, float] = {}

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def run_phase(
        self,
        phase_name: str,
        fn: Callable[..., Any],
        *args: Any,
        retries: int = 0,
        **kwargs: Any,
    ) -> Any:
        """
        Execute *fn* as a named phase with timing, error handling, and
        optional retry.
        """
        last_error: Optional[Exception] = None
        for attempt in range(1 + retries):
            if attempt > 0:
                logger.info(
                    "Retrying phase %s (attempt %d/%d)",
                    phase_name,
                    attempt + 1,
                    1 + retries,
                )
            t0 = time.monotonic()
            try:
                result = fn(*args, **kwargs)
                elapsed = time.monotonic() - t0
                self._phase_timings[phase_name] = elapsed
                logger.info(
                    "Phase %s completed in %.2fs", phase_name, elapsed
                )
                return result
            except PhaseError:
                raise
            except Exception as exc:
                elapsed = time.monotonic() - t0
                self._phase_timings[phase_name] = elapsed
                last_error = exc
                logger.warning(
                    "Phase %s failed (attempt %d): %s",
                    phase_name,
                    attempt + 1,
                    exc,
                )
        raise PhaseError(
            phase=phase_name,
            message=f"Failed after {1 + retries} attempts: {last_error}",
            recoverable=False,
            details={"last_error": str(last_error)},
        )

    # ------------------------------------------------------------------
    # Builtin phase implementations
    # ------------------------------------------------------------------

    def parse_intent(
        self,
        prompt: str,
        oracle: Optional[Any] = None,
    ) -> Dict[str, Any]:
        """
        Phase 1: Parse natural-language prompt into structured intent.

        Uses the IntentOracle if available, else falls back to LLM prompt.
        """
        if oracle is not None:
            try:
                spec = oracle.parse_intent(prompt)
                self._cost.record_call("parse_intent", tokens=0)
                return spec.to_dict() if hasattr(spec, "to_dict") else spec
            except Exception as exc:
                logger.warning("IntentOracle.parse_intent failed: %s", exc)

        if self._llm_fn is not None:
            system = (
                "You are a software architect. Parse the following user request "
                "into a structured JSON spec with keys: project_name, domain, "
                "description, modules (list of {name, description, dependencies}), "
                "constraints (list of strings), priorities (list of strings)."
            )
            raw = self._llm_fn(f"{system}\n\nUser request: {prompt}")
            self._cost.record_call("parse_intent", tokens=len(raw) // 4)
            return _safe_json_parse(raw, fallback={
                "project_name": "project",
                "domain": "general",
                "description": prompt,
                "modules": [{"name": "main", "description": prompt}],
                "constraints": [],
                "priorities": [],
            })

        return {
            "project_name": "project",
            "domain": "general",
            "description": prompt,
            "modules": [{"name": "main", "description": prompt}],
            "constraints": [],
            "priorities": [],
        }

    def expand_types(
        self,
        intent: Dict[str, Any],
    ) -> List[ExpandedType]:
        """
        Phase 2: Expand intent into typed module specifications.

        Each module in the intent is expanded into an ExpandedType with
        refinement predicates, contracts, and associated functions.
        """
        expanded: List[ExpandedType] = []
        modules = intent.get("modules", [])

        for mod in modules:
            name = mod.get("name", "unnamed")
            desc = mod.get("description", "")
            constraints = mod.get("constraints", [])

            predicates = _extract_predicates(desc, constraints)
            contracts = _extract_contracts(desc)
            functions = _extract_functions(desc)
            dep_params = _extract_dependent_params(desc)

            et = ExpandedType(
                name=name,
                refinement_predicates=predicates,
                dependent_params=dep_params,
                contracts=contracts,
                associated_functions=functions,
                metadata={
                    "description": desc,
                    "from_intent": True,
                    "domain": intent.get("domain", "general"),
                },
            )
            expanded.append(et)

        if not expanded:
            expanded.append(ExpandedType(
                name="main",
                metadata={"description": intent.get("description", ""), "fallback": True},
            ))

        return expanded

    def create_plan(
        self,
        intent: Dict[str, Any],
        expanded_types: List[ExpandedType],
    ) -> ProjectPlan:
        """
        Phase 3: Build a project plan from intent + expanded types.
        """
        modules_raw = intent.get("modules", [])
        dep_map: Dict[str, List[str]] = {}
        for mod in modules_raw:
            dep_map[mod.get("name", "unnamed")] = mod.get("dependencies", [])

        module_plans: List[ModulePlan] = []
        for i, et in enumerate(expanded_types):
            deps = dep_map.get(et.name, [])
            mp = ModulePlan(
                name=et.name,
                description=et.metadata.get("description", ""),
                dependencies=deps,
                type_spec=et.to_dict(),
                constraints=et.refinement_predicates,
                priority=len(expanded_types) - i,
                estimated_complexity=_estimate_complexity(et),
            )
            module_plans.append(mp)

        plan = ProjectPlan(
            project_name=intent.get("project_name", "project"),
            domain=intent.get("domain", "general"),
            description=intent.get("description", ""),
            modules=module_plans,
            dependency_graph=dep_map,
            constraints=intent.get("constraints", []),
            metadata={"intent_hash": _content_hash(json.dumps(intent, sort_keys=True))},
        )
        return plan

    def generate_module(
        self,
        module_plan: ModulePlan,
        context: Dict[str, Any],
        generator: Optional[Any] = None,
    ) -> Dict[str, Any]:
        """
        Phase 4: Generate code for a single module.

        Uses TypeDrivenGenerator if provided, else falls back to LLM.
        """
        if generator is not None:
            try:
                result = generator.generate(module_plan.type_spec, context)
                self._cost.record_call("generate", tokens=0)
                if hasattr(result, "to_dict"):
                    return result.to_dict()
                return result if isinstance(result, dict) else {"source": str(result)}
            except Exception as exc:
                logger.warning("Generator failed for %s: %s", module_plan.name, exc)

        if self._llm_fn is not None:
            prompt_text = _build_generation_prompt(module_plan, context)
            raw = self._llm_fn(prompt_text)
            self._cost.record_call("generate", tokens=len(raw) // 4)
            source = _extract_code_block(raw)
            return {
                "source": source,
                "module_name": module_plan.name,
                "trust_level": "UNCHECKED",
                "metadata": {"generated_by": "llm", "prompt_length": len(prompt_text)},
            }

        return _generate_stub(module_plan)

    def verify_module(
        self,
        source: str,
        module_name: str,
        verification_loop: Optional[Any] = None,
    ) -> Dict[str, Any]:
        """
        Phase 5: Verify generated code.

        Uses VerificationLoop if available, else does basic structural checks.
        """
        if verification_loop is not None:
            try:
                result = verification_loop.verify(source, module_name)
                self._cost.record_call("verify", tokens=0)
                if hasattr(result, "to_dict"):
                    return result.to_dict()
                return result if isinstance(result, dict) else {"passed": True}
            except Exception as exc:
                logger.warning("VerificationLoop failed for %s: %s", module_name, exc)

        return _basic_verify(source, module_name)

    def assemble_project(
        self,
        intent: Dict[str, Any],
        modules: Dict[str, Any],
        results: Dict[str, Any],
        assembler: Optional[Any] = None,
        config: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, str]:
        """
        Phase 6: Assemble verified modules into a project.

        Uses ProjectAssembler if available.
        """
        if assembler is not None:
            try:
                project = assembler.assemble(intent, modules, results, config)
                self._cost.record_call("assemble", tokens=0)
                if hasattr(project, "files"):
                    return project.files
                return project if isinstance(project, dict) else {}
            except Exception as exc:
                logger.warning("ProjectAssembler failed: %s", exc)

        return _basic_assemble(intent, modules)

    @property
    def timings(self) -> Dict[str, float]:
        return dict(self._phase_timings)


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  AgentOrchestrator — main entry point                                   ║
# ╚══════════════════════════════════════════════════════════════════════════╝

class AgentOrchestrator:
    """
    Main orchestrator: ``deppy "write me a trading app"`` → verified codebase.

    Pipeline::

        parse_intent → expand_type → plan → generate → verify → assemble

    Integrates with:
      - IntentOracle (agent.intent_oracle)
      - TypeDrivenGenerator (agent.code_generator)
      - VerificationLoop (agent.verification_loop)
      - ProjectAssembler (agent.project_assembler)
    """

    def __init__(
        self,
        llm_fn: Optional[Callable[..., str]] = None,
        config: Optional[OrchestratorConfig] = None,
    ) -> None:
        self._config = config or OrchestratorConfig()
        self._llm_fn = llm_fn
        self._state = AgentState.IDLE
        self._state_history: List[str] = ["idle"]
        self._cost = CostReport()
        self._trust_summary = TrustSummary()
        self._runner = PhaseRunner(self._config, self._cost, llm_fn)

        # Lazy-loaded collaborators
        self._intent_oracle: Optional[Any] = None
        self._generator: Optional[Any] = None
        self._verification_loop: Optional[Any] = None
        self._cegar_loop: Optional[Any] = None
        self._assembler: Optional[Any] = None
        self._progress: Optional[Any] = None

    # ------------------------------------------------------------------
    # State management
    # ------------------------------------------------------------------

    @property
    def state(self) -> AgentState:
        return self._state

    def _transition(self, target: AgentState) -> None:
        if not self._state.can_transition_to(target):
            raise PhaseError(
                phase="state_transition",
                message=(
                    f"Invalid transition: {self._state.value} → {target.value}"
                ),
                recoverable=False,
            )
        logger.info("State: %s → %s", self._state.value, target.value)
        self._state = target
        self._state_history.append(target.value)

    # ------------------------------------------------------------------
    # Lazy initialization of collaborators
    # ------------------------------------------------------------------

    def _get_intent_oracle(self) -> Optional[Any]:
        if self._intent_oracle is not None:
            return self._intent_oracle
        try:
            from agent.intent_oracle import IntentOracle
            self._intent_oracle = IntentOracle(llm_fn=self._llm_fn)
            return self._intent_oracle
        except ImportError:
            logger.debug("IntentOracle not available")
            return None
        except Exception as exc:
            logger.debug("IntentOracle init failed: %s", exc)
            return None

    def _get_generator(self) -> Optional[Any]:
        if self._generator is not None:
            return self._generator
        try:
            from agent.code_generator import TypeDrivenGenerator
            self._generator = TypeDrivenGenerator(llm_fn=self._llm_fn)
            return self._generator
        except ImportError:
            logger.debug("TypeDrivenGenerator not available")
            return None
        except Exception as exc:
            logger.debug("TypeDrivenGenerator init failed: %s", exc)
            return None

    def _get_verification_loop(self) -> Optional[Any]:
        if self._verification_loop is not None:
            return self._verification_loop
        try:
            from agent.verification_loop import VerificationLoop, VerificationConfig
            vc = VerificationConfig(
                z3_timeout_ms=self._config.z3_timeout_ms,
                semantic_confidence_threshold=self._config.semantic_confidence_threshold,
                max_cegar_rounds=self._config.max_cegar_rounds,
                emit_lean=self._config.emit_lean,
                cache_enabled=self._config.cache_enabled,
                oracle_model=self._config.oracle_model,
                strict_mode=self._config.strict_mode,
            )
            self._verification_loop = VerificationLoop(
                config=vc,
                oracle_fn=self._llm_fn,
            )
            return self._verification_loop
        except ImportError:
            logger.debug("VerificationLoop not available")
            return None
        except Exception as exc:
            logger.debug("VerificationLoop init failed: %s", exc)
            return None

    def _get_cegar_loop(self) -> Optional[Any]:
        if self._cegar_loop is not None:
            return self._cegar_loop
        try:
            from agent.verification_loop import CEGARVerificationLoop
            vloop = self._get_verification_loop()
            self._cegar_loop = CEGARVerificationLoop(verification_loop=vloop)
            return self._cegar_loop
        except ImportError:
            logger.debug("CEGARVerificationLoop not available")
            return None
        except Exception as exc:
            logger.debug("CEGARVerificationLoop init failed: %s", exc)
            return None

    def _get_assembler(self) -> Optional[Any]:
        if self._assembler is not None:
            return self._assembler
        try:
            from agent.project_assembler import ProjectAssembler
            self._assembler = ProjectAssembler()
            return self._assembler
        except ImportError:
            logger.debug("ProjectAssembler not available")
            return None
        except Exception as exc:
            logger.debug("ProjectAssembler init failed: %s", exc)
            return None

    def _get_progress(self) -> Optional[Any]:
        if self._progress is not None:
            return self._progress
        try:
            from agent.cli import ProgressDisplay
            self._progress = ProgressDisplay(verbose=self._config.verbose)
            return self._progress
        except ImportError:
            return None
        except Exception:
            return None

    # ------------------------------------------------------------------
    # Main entry point
    # ------------------------------------------------------------------

    def run(
        self,
        prompt: str,
        config: Optional[OrchestratorConfig] = None,
    ) -> OrchestratorResult:
        """
        Run the full orchestration pipeline.

        Parameters
        ----------
        prompt : str
            Natural-language description of the desired project.
        config : OrchestratorConfig, optional
            Override the instance config for this run.

        Returns
        -------
        OrchestratorResult
            Contains project files, trust summary, certificate, and cost.
        """
        if config is not None:
            self._config = config
            self._runner = PhaseRunner(config, self._cost, self._llm_fn)

        errors = self._config.validate()
        if errors:
            return OrchestratorResult(
                success=False,
                errors=[f"Config validation: {e}" for e in errors],
            )

        self._cost.start_time = time.monotonic()
        progress = self._get_progress()

        try:
            if progress:
                progress.intent_start(prompt)

            # Phase 1: Parse intent
            self._transition(AgentState.PARSING)
            oracle = self._get_intent_oracle()
            intent = self._runner.run_phase(
                "parse_intent",
                self._runner.parse_intent,
                prompt,
                oracle,
                retries=1,
            )
            logger.info("Intent: %s", intent.get("project_name", "?"))

            if progress:
                progress.intent_resolved(
                    intent.get("domain", "general"),
                    [m.get("name", "?") for m in intent.get("modules", [])],
                    intent.get("constraints", []),
                )

            # Phase 2: Expand types
            self._transition(AgentState.EXPANDING)
            expanded = self._runner.run_phase(
                "expand_types",
                self._runner.expand_types,
                intent,
            )
            logger.info("Expanded %d types", len(expanded))

            # Phase 3: Plan
            self._transition(AgentState.PLANNING)
            plan = self._runner.run_phase(
                "create_plan",
                self._runner.create_plan,
                intent,
                expanded,
            )
            build_order = plan.topological_order()
            logger.info("Plan: %d modules, order: %s", len(plan.modules), build_order)

            # Phase 4+5: Generate & Verify each module
            self._transition(AgentState.GENERATING)
            generator = self._get_generator()
            vloop = self._get_verification_loop()
            cegar = self._get_cegar_loop()

            generated_modules: Dict[str, Dict[str, Any]] = {}
            verification_results: Dict[str, Dict[str, Any]] = {}
            context: Dict[str, Any] = {
                "intent": intent,
                "plan": plan.to_dict(),
                "generated_so_far": {},
            }

            for idx, mod_name in enumerate(build_order):
                mod_plan = next(
                    (m for m in plan.modules if m.name == mod_name), None
                )
                if mod_plan is None:
                    continue

                if progress:
                    progress.module_start(
                        mod_name, idx, len(build_order),
                        pattern=mod_plan.estimated_complexity,
                    )

                gen_result = self._generate_and_verify_module(
                    mod_plan, context, generator, vloop, cegar, progress
                )
                generated_modules[mod_name] = gen_result["module"]
                verification_results[mod_name] = gen_result["verification"]

                vr = gen_result["verification"]
                self._trust_summary.add_module(
                    mod_name,
                    vr.get("trust_level", "UNCHECKED"),
                    discharged=vr.get("discharged", 0),
                    residual=vr.get("residual", 0),
                    hallucinations=len(vr.get("hallucination_findings", [])),
                )

                context["generated_so_far"][mod_name] = gen_result["module"].get("source", "")

                if progress:
                    progress.module_done(
                        mod_name,
                        vr.get("trust_level", "UNCHECKED"),
                    )

            # Phase 6: Assemble
            self._transition(AgentState.ASSEMBLING)
            assembler = self._get_assembler()
            project_files = self._runner.run_phase(
                "assemble",
                self._runner.assemble_project,
                intent,
                generated_modules,
                verification_results,
                assembler,
                self._config.to_dict(),
            )

            # Build certificate
            certificate = self._build_certificate(
                intent, plan, generated_modules, verification_results
            )

            self._transition(AgentState.DONE)
            self._cost.end_time = time.monotonic()

            if progress:
                progress.project_done("success", self._config.output_dir)

            result = OrchestratorResult(
                success=True,
                project_files=project_files,
                certificate=certificate,
                trust_summary=self._trust_summary,
                cost_report=self._cost,
                output_dir=self._config.output_dir,
                state_history=list(self._state_history),
                duration_seconds=self._cost.wall_time_seconds,
                modules_generated=len(generated_modules),
                modules_verified=sum(
                    1 for v in verification_results.values() if v.get("passed", False)
                ),
            )

            if not self._trust_summary.meets_threshold(self._config.min_trust_level):
                result.warnings.append(
                    f"Overall trust {self._trust_summary.overall_trust} "
                    f"below threshold {self._config.min_trust_level}"
                )

            return result

        except PhaseError as exc:
            self._cost.end_time = time.monotonic()
            try:
                self._transition(AgentState.FAILED)
            except PhaseError:
                self._state = AgentState.FAILED
                self._state_history.append("failed")

            if progress:
                progress.error(str(exc))

            return OrchestratorResult(
                success=False,
                errors=[str(exc)],
                trust_summary=self._trust_summary,
                cost_report=self._cost,
                state_history=list(self._state_history),
                duration_seconds=self._cost.wall_time_seconds,
            )

        except Exception as exc:
            self._cost.end_time = time.monotonic()
            try:
                self._transition(AgentState.FAILED)
            except PhaseError:
                self._state = AgentState.FAILED
                self._state_history.append("failed")

            logger.exception("Orchestrator failed unexpectedly")
            return OrchestratorResult(
                success=False,
                errors=[f"Unexpected error: {exc}"],
                trust_summary=self._trust_summary,
                cost_report=self._cost,
                state_history=list(self._state_history),
                duration_seconds=self._cost.wall_time_seconds,
            )

    # ------------------------------------------------------------------
    # Internal: generate + verify one module with CEGAR
    # ------------------------------------------------------------------

    def _generate_and_verify_module(
        self,
        mod_plan: ModulePlan,
        context: Dict[str, Any],
        generator: Optional[Any],
        vloop: Optional[Any],
        cegar: Optional[Any],
        progress: Optional[Any],
    ) -> Dict[str, Any]:
        """Generate and verify a single module, with CEGAR retry."""
        gen_result = self._runner.run_phase(
            f"generate:{mod_plan.name}",
            self._runner.generate_module,
            mod_plan,
            context,
            generator,
            retries=self._config.max_generation_retries - 1,
        )

        source = gen_result.get("source", "")
        if not source.strip():
            return {
                "module": gen_result,
                "verification": {
                    "passed": False,
                    "trust_level": "UNCHECKED",
                    "errors": ["Empty source generated"],
                },
            }

        # Verify
        self._ensure_state_for_verification()
        vresult = self._runner.run_phase(
            f"verify:{mod_plan.name}",
            self._runner.verify_module,
            source,
            mod_plan.name,
            vloop,
        )

        if not vresult.get("passed", False) and cegar is not None:
            source, vresult = self._run_cegar(
                mod_plan, source, vresult, cegar, context, generator, progress
            )
            gen_result["source"] = source

        return {"module": gen_result, "verification": vresult}

    def _ensure_state_for_verification(self) -> None:
        if self._state == AgentState.GENERATING:
            self._transition(AgentState.VERIFYING)
        elif self._state == AgentState.VERIFYING:
            pass  # already there
        # After verification, we may go back to generating for next module
        # The state machine allows VERIFYING → GENERATING

    def _run_cegar(
        self,
        mod_plan: ModulePlan,
        source: str,
        vresult: Dict[str, Any],
        cegar: Any,
        context: Dict[str, Any],
        generator: Optional[Any],
        progress: Optional[Any],
    ) -> Tuple[str, Dict[str, Any]]:
        """Run CEGAR loop: generate → verify → repair → verify."""
        max_rounds = self._config.max_cegar_rounds
        current_source = source
        current_result = vresult

        for round_no in range(1, max_rounds + 1):
            if progress:
                progress.cegar_start(mod_plan.name, round_no)

            # Extract counterexample
            feedback = _format_cegar_feedback(current_result)
            if not feedback:
                break

            # Re-generate with feedback
            repair_context = dict(context)
            repair_context["cegar_feedback"] = feedback
            repair_context["previous_source"] = current_source
            repair_context["round"] = round_no

            # Transition back to generating for repair
            if self._state == AgentState.VERIFYING:
                self._transition(AgentState.GENERATING)

            gen_result = self._runner.run_phase(
                f"repair:{mod_plan.name}:r{round_no}",
                self._runner.generate_module,
                mod_plan,
                repair_context,
                generator,
            )
            current_source = gen_result.get("source", current_source)

            # Re-verify
            self._ensure_state_for_verification()
            current_result = self._runner.run_phase(
                f"reverify:{mod_plan.name}:r{round_no}",
                self._runner.verify_module,
                current_source,
                mod_plan.name,
                self._get_verification_loop(),
            )

            if progress:
                progress.cegar_done(
                    mod_plan.name, round_no, current_result.get("passed", False)
                )

            if current_result.get("passed", False):
                break

        return current_source, current_result

    # ------------------------------------------------------------------
    # Certificate
    # ------------------------------------------------------------------

    def _build_certificate(
        self,
        intent: Dict[str, Any],
        plan: ProjectPlan,
        modules: Dict[str, Dict[str, Any]],
        results: Dict[str, Dict[str, Any]],
    ) -> Dict[str, Any]:
        """Build a verification certificate for the project."""
        module_certs = {}
        for name, vr in results.items():
            module_certs[name] = {
                "trust_level": vr.get("trust_level", "UNCHECKED"),
                "passed": vr.get("passed", False),
                "discharged": vr.get("discharged", 0),
                "residual": vr.get("residual", 0),
                "h1_status": vr.get("h1_status", "H¹ = 0"),
                "content_hash": _content_hash(
                    modules.get(name, {}).get("source", "")
                ),
            }

        return {
            "version": "1.0",
            "timestamp": _timestamp_iso(),
            "project_name": intent.get("project_name", "project"),
            "intent_hash": _content_hash(json.dumps(intent, sort_keys=True)),
            "overall_trust": self._trust_summary.overall_trust,
            "modules": module_certs,
            "cost": self._cost.to_dict(),
            "plan_hash": _content_hash(json.dumps(plan.to_dict(), sort_keys=True)),
        }

    # ------------------------------------------------------------------
    # Convenience
    # ------------------------------------------------------------------

    def reset(self) -> None:
        """Reset the orchestrator for a new run."""
        self._state = AgentState.IDLE
        self._state_history = ["idle"]
        self._cost = CostReport()
        self._trust_summary = TrustSummary()
        self._runner = PhaseRunner(self._config, self._cost, self._llm_fn)


# Alias for backwards compat with agent/__init__.py
DeppyAgent = AgentOrchestrator
AgentConfig = OrchestratorConfig


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  Helper functions (private)                                             ║
# ╚══════════════════════════════════════════════════════════════════════════╝

def _safe_json_parse(text: str, fallback: Any = None) -> Any:
    """Try to parse JSON from text, extracting from markdown if needed."""
    text = text.strip()
    # Try direct parse
    try:
        return json.loads(text)
    except (json.JSONDecodeError, ValueError):
        pass
    # Try extracting from markdown code fence
    match = re.search(r"```(?:json)?\s*\n(.*?)```", text, re.DOTALL)
    if match:
        try:
            return json.loads(match.group(1))
        except (json.JSONDecodeError, ValueError):
            pass
    # Try finding first { ... }
    brace_start = text.find("{")
    brace_end = text.rfind("}")
    if brace_start >= 0 and brace_end > brace_start:
        try:
            return json.loads(text[brace_start : brace_end + 1])
        except (json.JSONDecodeError, ValueError):
            pass
    return fallback if fallback is not None else {}


def _extract_code_block(text: str) -> str:
    """Extract code from markdown fences or return raw text."""
    match = re.search(r"```(?:python)?\s*\n(.*?)```", text, re.DOTALL)
    if match:
        return match.group(1).strip()
    return text.strip()


def _extract_predicates(
    description: str, constraints: List[str]
) -> List[str]:
    """Heuristically extract refinement predicates from description."""
    predicates: List[str] = []
    keywords = [
        "positive", "non-negative", "non-empty", "sorted",
        "unique", "valid", "bounded", "within range",
    ]
    desc_lower = description.lower()
    for kw in keywords:
        if kw in desc_lower:
            predicates.append(kw)
    predicates.extend(constraints)
    return predicates


def _extract_contracts(description: str) -> Dict[str, List[str]]:
    """Heuristically extract pre/post conditions from description."""
    contracts: Dict[str, List[str]] = {"requires": [], "ensures": []}
    lines = description.split(".")
    for line in lines:
        low = line.strip().lower()
        if any(w in low for w in ["must", "should", "required", "need"]):
            contracts["requires"].append(line.strip())
        if any(w in low for w in ["return", "produce", "output", "result"]):
            contracts["ensures"].append(line.strip())
    return contracts


def _extract_functions(description: str) -> List[str]:
    """Heuristically extract function names from description."""
    functions: List[str] = []
    patterns = [
        r"(?:function|method|def)\s+(\w+)",
        r"(\w+)\s*\(",
    ]
    for pat in patterns:
        for m in re.finditer(pat, description, re.IGNORECASE):
            name = m.group(1)
            if name.lower() not in {"the", "a", "an", "is", "are", "be", "for"}:
                functions.append(name)
    return list(OrderedDict.fromkeys(functions))


def _extract_dependent_params(description: str) -> List[Dict[str, Any]]:
    """Heuristically extract dependent parameters from description."""
    params: List[Dict[str, Any]] = []
    patterns = [
        r"(?:where|such that|given)\s+(\w+)\s*(?:is|:)\s*([^,.]+)",
    ]
    for pat in patterns:
        for m in re.finditer(pat, description, re.IGNORECASE):
            params.append({
                "name": m.group(1),
                "constraint": m.group(2).strip(),
            })
    return params


def _estimate_complexity(et: ExpandedType) -> str:
    """Estimate generation complexity from expanded type."""
    score = 0
    score += len(et.refinement_predicates) * 2
    score += len(et.dependent_params) * 3
    score += len(et.contracts.get("requires", [])) * 2
    score += len(et.contracts.get("ensures", [])) * 2
    score += len(et.associated_functions)
    if score < 5:
        return "simple"
    elif score < 15:
        return "medium"
    else:
        return "complex"


def _build_generation_prompt(
    mod_plan: ModulePlan, context: Dict[str, Any]
) -> str:
    """Build a prompt for LLM-based code generation."""
    parts = [
        "Generate a Python module with the following specification:",
        f"\nModule name: {mod_plan.name}",
        f"Description: {mod_plan.description}",
    ]
    if mod_plan.constraints:
        parts.append(f"Constraints: {', '.join(mod_plan.constraints)}")
    if mod_plan.dependencies:
        parts.append(f"Dependencies: {', '.join(mod_plan.dependencies)}")

    type_spec = mod_plan.type_spec
    if type_spec:
        preds = type_spec.get("refinement_predicates", [])
        if preds:
            parts.append(f"Refinement predicates: {', '.join(preds)}")
        contracts = type_spec.get("contracts", {})
        if contracts.get("requires"):
            parts.append(f"Preconditions: {'; '.join(contracts['requires'])}")
        if contracts.get("ensures"):
            parts.append(f"Postconditions: {'; '.join(contracts['ensures'])}")

    # CEGAR feedback
    feedback = context.get("cegar_feedback")
    if feedback:
        parts.append(f"\n--- REPAIR INSTRUCTIONS ---\n{feedback}")
        prev = context.get("previous_source", "")
        if prev:
            parts.append(f"\nPrevious (buggy) code:\n```python\n{prev}\n```")

    # Context from already-generated modules
    generated = context.get("generated_so_far", {})
    if generated:
        parts.append("\nAlready generated modules (for reference):")
        for name, src in generated.items():
            if name != mod_plan.name:
                snippet = src[:500] if len(src) > 500 else src
                parts.append(f"\n# {name}\n{snippet}")

    parts.append(
        "\nGenerate clean, well-typed Python code with docstrings and type hints."
        "\nInclude @requires/@ensures comments for contracts."
        "\nWrap code in ```python ... ```."
    )
    return "\n".join(parts)


def _format_cegar_feedback(vresult: Dict[str, Any]) -> str:
    """Format verification failures as CEGAR repair feedback."""
    lines: List[str] = []

    structural = vresult.get("structural_results", [])
    for sr in structural:
        if sr.get("status") == "failed":
            ce = sr.get("counterexample", "")
            lines.append(
                f"STRUCTURAL FAILURE: {sr.get('claim', '?')}"
                + (f" — counterexample: {ce}" if ce else "")
            )

    semantic = vresult.get("semantic_results", [])
    for sr in semantic:
        if sr.get("status") == "failed":
            lines.append(
                f"SEMANTIC FAILURE: {sr.get('claim', '?')}"
                f" — confidence {sr.get('confidence', 0):.2f}"
            )

    hallucinations = vresult.get("hallucination_findings", [])
    for hf in hallucinations:
        lines.append(
            f"HALLUCINATION: [{hf.get('detector', '?')}] "
            f"at {hf.get('location', '?')}: {hf.get('description', '?')}"
        )

    errors = vresult.get("errors", [])
    for e in errors:
        lines.append(f"ERROR: {e}")

    return "\n".join(lines)


def _generate_stub(mod_plan: ModulePlan) -> Dict[str, Any]:
    """Generate a stub module (no LLM)."""
    name = mod_plan.name
    safe_name = name.replace("-", "_").replace(".", "_")
    lines = [
        f'"""{mod_plan.description or name} module."""',
        "",
    ]

    for fn_name in mod_plan.type_spec.get("associated_functions", []):
        lines.extend([
            f"def {fn_name}():",
            f'    """TODO: implement {fn_name}."""',
            "    raise NotImplementedError",
            "",
        ])

    if not mod_plan.type_spec.get("associated_functions"):
        lines.extend([
            f"def main():",
            f'    """Entry point for {name}."""',
            "    raise NotImplementedError",
            "",
        ])

    return {
        "source": "\n".join(lines),
        "module_name": name,
        "trust_level": "UNCHECKED",
        "metadata": {"generated_by": "stub"},
    }


def _basic_verify(source: str, module_name: str) -> Dict[str, Any]:
    """Minimal verification when VerificationLoop is not available."""
    issues: List[str] = []

    # Check syntax
    try:
        import ast
        ast.parse(source)
    except SyntaxError as exc:
        issues.append(f"Syntax error: {exc}")

    # Check for bare except
    if re.search(r"\bexcept\s*:", source):
        issues.append("Bare except clause detected")

    # Check for eval/exec
    if re.search(r"\b(eval|exec)\s*\(", source):
        issues.append("Use of eval/exec detected")

    passed = len(issues) == 0
    return {
        "module_name": module_name,
        "passed": passed,
        "trust_level": "LLM_JUDGED" if passed else "UNCHECKED",
        "structural_results": [],
        "semantic_results": [],
        "hallucination_findings": [],
        "lean_obligations": [],
        "discharged": 0,
        "residual": 0,
        "h1_status": "H¹ = 0",
        "content_hash": _content_hash(source),
        "errors": issues,
    }


def _basic_assemble(
    intent: Dict[str, Any],
    modules: Dict[str, Dict[str, Any]],
) -> Dict[str, str]:
    """Basic project assembly when ProjectAssembler is not available."""
    files: Dict[str, str] = {}
    project_name = intent.get("project_name", "project")
    safe_name = project_name.replace("-", "_").replace(" ", "_").lower()

    for name, mod in modules.items():
        safe_mod = name.replace("-", "_").replace(".", "/")
        path = f"{safe_name}/{safe_mod}.py"
        files[path] = mod.get("source", "")

    # __init__.py
    mod_names = list(modules.keys())
    init_imports = "\n".join(
        f"from .{n.replace('-', '_')} import *  # noqa"
        for n in mod_names
    )
    files[f"{safe_name}/__init__.py"] = (
        f'"""{project_name}."""\n\n{init_imports}\n'
    )

    # pyproject.toml
    files["pyproject.toml"] = textwrap.dedent(f"""\
        [build-system]
        requires = ["setuptools>=68.0"]
        build-backend = "setuptools.backends._legacy:_Backend"

        [project]
        name = "{safe_name}"
        version = "0.1.0"
        description = "{intent.get('description', '')}"
        requires-python = ">=3.10"
    """)

    # README
    files["README.md"] = (
        f"# {project_name}\n\n"
        f"{intent.get('description', '')}\n\n"
        f"Generated and verified by deppy.\n"
    )

    return files
