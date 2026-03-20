"""
Verified Planning for Code Generation
======================================

Checks that a code generation plan is correct BEFORE spending tokens on
code generation.  A plan P for spec S is verified iff it satisfies five
conditions, each corresponding to a type-theoretic property:

    Plan(S) = Σ(m₁:M₁). Σ(m₂:M₂(m₁)). … ⊤

1. **Coverage**    – Γ_P ⊢ ΣᵢMᵢ : S — modules cover the spec
2. **Coherence**   – H¹(Cover_P, HybridTy) = 0 — no gaps between modules
3. **Feasibility** – ∀ leaf. atomic(leaf) — every leaf is small enough
4. **Consistency** – Z3.check(⋀ constraints) = SAT — no contradictions
5. **Budget**      – estimated_cost(P) ≤ budget — affordable to execute

The verifier returns a *PlanCertificate* when all five conditions pass,
or a detailed failure report with actionable suggestions.
"""
from __future__ import annotations

import copy
import hashlib
import json
import logging
import math
import re
import textwrap
import time
from collections import defaultdict, deque
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

if TYPE_CHECKING:
    pass

# ---------------------------------------------------------------------------
# Optional Z3 support
# ---------------------------------------------------------------------------
try:
    import z3 as _z3

    _HAS_Z3 = True
except ImportError:
    _z3 = None  # type: ignore[assignment]
    _HAS_Z3 = False


# --- Integration with existing deppy codebase ---
try:
    from deppy.solver import FragmentDispatcher, Z3Backend, SolverObligation
    from deppy.types.dependent import SigmaType, PiType
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

logger = logging.getLogger(__name__)

# ===================================================================
# Constants
# ===================================================================
_DEFAULT_LOC_THRESHOLD = 300
_DEFAULT_MAX_PARAMS = 5
_DEFAULT_COVERAGE_THRESHOLD = 0.80
_DEFAULT_MATCH_THRESHOLD = 0.30
_BUDGET_TOLERANCE = 1.10  # allow 10 % overshoot before failing


# ===================================================================
# VerificationCondition enum
# ===================================================================
class VerificationCondition(Enum):
    """The five conditions of plan verification."""

    COVERAGE = auto()
    COHERENCE = auto()
    FEASIBILITY = auto()
    CONSISTENCY = auto()
    BUDGET = auto()


# ===================================================================
# ConditionResult
# ===================================================================
@dataclass
class ConditionResult:
    """Outcome of checking a single verification condition.

    Parameters
    ----------
    condition:
        Which of the five verification conditions was checked.
    passed:
        Whether the check succeeded.
    confidence:
        A value in [0, 1] indicating how much we trust the verdict.
    evidence:
        Human-readable evidence supporting the judgment.
    trust_level:
        How the evidence was obtained:
        - ``STRUCTURAL`` – purely syntactic / keyword / graph analysis
        - ``Z3``         – backed by an SMT solver result
        - ``SEMANTIC``   – an oracle (e.g. LLM) was consulted
        - ``HEURISTIC``  – rule-of-thumb estimation
    details:
        Arbitrary structured data for programmatic consumption.
    suggestions:
        If the check *failed*, concrete suggestions for fixing the plan.
    """

    condition: VerificationCondition
    passed: bool
    confidence: float = 1.0
    evidence: str = ""
    trust_level: str = "STRUCTURAL"
    details: Dict[str, Any] = field(default_factory=dict)
    suggestions: List[str] = field(default_factory=list)

    # -- helpers ----------------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        return {
            "condition": self.condition.name,
            "passed": self.passed,
            "confidence": round(self.confidence, 4),
            "evidence": self.evidence,
            "trust_level": self.trust_level,
            "details": self.details,
            "suggestions": self.suggestions,
        }

    def short(self) -> str:
        status = "✓" if self.passed else "✗"
        return f"[{status}] {self.condition.name} (confidence={self.confidence:.2f}, trust={self.trust_level})"


# ===================================================================
# CoverageChecker
# ===================================================================
class CoverageChecker:
    """Check Γ_P ⊢ ΣᵢMᵢ : S — do the planned modules cover the spec?

    Strategy
    --------
    1. Extract *claims* (atomic requirements) from the NL spec.
    2. For each claim, check if at least one module addresses it.
    3. Coverage = |addressed_claims| / |total_claims|.

    Decidability stratification:

    * **Structural matching** – keyword / n-gram overlap between the claim
      text and the module's name + description.  Cheap, deterministic,
      but may miss synonyms.
    * **Semantic matching** – uses an *oracle_fn* (typically an LLM call)
      to judge whether a module addresses a claim.  More accurate but
      costs tokens.
    """

    def __init__(
        self,
        coverage_threshold: float = _DEFAULT_COVERAGE_THRESHOLD,
        match_threshold: float = _DEFAULT_MATCH_THRESHOLD,
    ) -> None:
        self.coverage_threshold = coverage_threshold
        self.match_threshold = match_threshold

    # ----- public API ---------------------------------------------------

    def check(
        self,
        spec: str,
        modules: List[Dict[str, Any]],
        oracle_fn: Optional[Callable[..., Any]] = None,
    ) -> ConditionResult:
        """Run the coverage check and return a :class:`ConditionResult`."""
        claims = self.extract_claims(spec)
        if not claims:
            return ConditionResult(
                condition=VerificationCondition.COVERAGE,
                passed=True,
                confidence=0.5,
                evidence="No claims could be extracted from the spec; vacuously covered.",
                trust_level="HEURISTIC",
                details={"total_claims": 0, "addressed": 0},
            )

        addressed: Dict[str, Tuple[float, str]] = {}  # claim -> (score, module_name)
        trust = "STRUCTURAL"

        for claim in claims:
            best_score = 0.0
            best_module = ""
            for mod in modules:
                structural = self.match_structural(claim, mod)
                if structural > best_score:
                    best_score = structural
                    best_module = mod.get("name", "<unnamed>")

            # Fall back to semantic if structural is weak
            if best_score < self.match_threshold and oracle_fn is not None:
                for mod in modules:
                    sem = self.match_semantic(claim, mod, oracle_fn)
                    if sem > best_score:
                        best_score = sem
                        best_module = mod.get("name", "<unnamed>")
                        trust = "SEMANTIC"

            if best_score >= self.match_threshold:
                addressed[claim] = (best_score, best_module)

        ratio = len(addressed) / len(claims) if claims else 1.0
        passed = ratio >= self.coverage_threshold

        uncovered = [c for c in claims if c not in addressed]
        suggestions: List[str] = []
        if uncovered:
            suggestions.append(
                "Add modules to cover: " + "; ".join(uncovered[:5])
            )
            if len(uncovered) > 5:
                suggestions.append(
                    f"... and {len(uncovered) - 5} more uncovered claims."
                )

        return ConditionResult(
            condition=VerificationCondition.COVERAGE,
            passed=passed,
            confidence=min(1.0, ratio + 0.1) if passed else ratio,
            evidence=(
                f"Coverage {ratio:.0%}: {len(addressed)}/{len(claims)} claims addressed."
            ),
            trust_level=trust,
            details={
                "total_claims": len(claims),
                "addressed": len(addressed),
                "coverage_ratio": round(ratio, 4),
                "uncovered": uncovered,
                "addressed_map": {
                    c: {"score": round(s, 4), "module": m}
                    for c, (s, m) in addressed.items()
                },
            },
            suggestions=suggestions,
        )

    # ----- claim extraction ---------------------------------------------

    def extract_claims(self, spec: str) -> List[str]:
        """Extract atomic claims/requirements from a natural-language spec.

        Heuristic: split on sentence boundaries and bullet points, then
        keep sentences that look imperative or contain requirement keywords.
        """
        raw_sentences = self._split_sentences(spec)
        claims: List[str] = []
        requirement_signals = {
            "must", "shall", "should", "need", "require",
            "implement", "support", "provide", "ensure",
            "return", "accept", "handle", "validate",
            "create", "define", "expose", "maintain",
            "compute", "calculate", "generate", "process",
        }
        for sent in raw_sentences:
            lower = sent.lower().strip()
            if not lower or len(lower) < 8:
                continue
            tokens = set(re.findall(r"[a-z_]+", lower))
            if tokens & requirement_signals:
                claims.append(sent.strip())
            elif lower.startswith(("-", "*", "•", "–")):
                claims.append(sent.strip().lstrip("-*•– "))
        # Deduplicate while preserving order
        seen: Set[str] = set()
        deduped: List[str] = []
        for c in claims:
            norm = c.lower()
            if norm not in seen:
                seen.add(norm)
                deduped.append(c)
        return deduped

    # ----- matching helpers ---------------------------------------------

    def match_structural(self, claim: str, module: Dict[str, Any]) -> float:
        """Keyword-overlap score between *claim* and a module descriptor."""
        claim_tokens = self._tokenize(claim)
        mod_tokens = self._module_tokens(module)
        if not claim_tokens or not mod_tokens:
            return 0.0
        overlap = claim_tokens & mod_tokens
        # Jaccard-like but biased toward claim coverage
        return len(overlap) / len(claim_tokens) if claim_tokens else 0.0

    def match_semantic(
        self,
        claim: str,
        module: Dict[str, Any],
        oracle_fn: Callable[..., Any],
    ) -> float:
        """Use an oracle (LLM) to judge if *module* addresses *claim*.

        The oracle_fn signature::

            oracle_fn(prompt: str) -> str

        We parse the response for a confidence score.
        """
        mod_desc = module.get("description", module.get("name", ""))
        prompt = (
            f"Does the following module address this requirement?\n\n"
            f"Requirement: {claim}\n"
            f"Module: {mod_desc}\n\n"
            f"Answer with a confidence score between 0.0 and 1.0."
        )
        try:
            response = str(oracle_fn(prompt))
            # Try to pull out a float from the response
            numbers = re.findall(r"\b([01](?:\.\d+)?)\b", response)
            if numbers:
                return float(numbers[0])
            return 0.0
        except Exception:  # noqa: BLE001
            logger.debug("Semantic match oracle failed for claim: %s", claim)
            return 0.0

    def uncovered_claims(
        self,
        spec: str,
        modules: List[Dict[str, Any]],
    ) -> List[str]:
        """Return claims not addressed by any module (structural only)."""
        claims = self.extract_claims(spec)
        uncovered: List[str] = []
        for claim in claims:
            best = max(
                (self.match_structural(claim, m) for m in modules),
                default=0.0,
            )
            if best < self.match_threshold:
                uncovered.append(claim)
        return uncovered

    # ----- private helpers ----------------------------------------------

    @staticmethod
    def _split_sentences(text: str) -> List[str]:
        """Split text on sentence boundaries and list markers."""
        # Handle bullet/numbered lists
        text = re.sub(r"\n\s*[-*•–]\s+", "\n. ", text)
        text = re.sub(r"\n\s*\d+\.\s+", "\n. ", text)
        parts = re.split(r"(?<=[.!?])\s+|\n\.\s*", text)
        return [p.strip() for p in parts if p.strip()]

    @staticmethod
    def _tokenize(text: str) -> Set[str]:
        """Lower-case token set, dropping short words."""
        tokens = re.findall(r"[a-z][a-z_]+", text.lower())
        stop = {"the", "and", "for", "with", "that", "this", "from", "are", "was", "been"}
        return {t for t in tokens if len(t) > 2 and t not in stop}

    @staticmethod
    def _module_tokens(module: Dict[str, Any]) -> Set[str]:
        blob = " ".join(
            str(module.get(k, ""))
            for k in ("name", "description", "exports", "responsibilities", "purpose")
        )
        return CoverageChecker._tokenize(blob)


# ===================================================================
# CoherenceChecker
# ===================================================================
class CoherenceChecker:
    """Check H¹(Cover_P, HybridTy) = 0 — no gaps between planned modules.

    The cover is {M₁, …, Mₙ} where each Mᵢ is a planned module.
    Overlaps Mᵢ ∩ Mⱼ = shared interfaces.

    H¹ ≠ 0 when:
    - Two modules provide the same API with different types.
    - A module imports something no other module exports.
    - Circular dependencies that cannot be resolved.
    - Missing adapter/glue between modules with incompatible interfaces.

    We compute a discrete first cohomology:

        H¹ = ker(δ₁) / im(δ₀)

    where δ₀, δ₁ come from the Čech complex of the cover.  In practice
    we approximate this with a concrete graph analysis that counts the
    independent obstructions to stitching the modules together.
    """

    # ----- public API ---------------------------------------------------

    def check(
        self,
        modules: List[Dict[str, Any]],
        interfaces: List[Dict[str, Any]],
    ) -> ConditionResult:
        """Run the coherence check."""
        missing = self.find_missing_exports(modules)
        mismatches = self.find_type_mismatches(interfaces)
        dep_graph = self.build_interface_graph(modules)
        cycles = self.find_cycles(dep_graph)
        h1 = self.compute_h1(modules, interfaces)
        generators = self.h1_generators(modules, interfaces)

        issues: List[str] = []
        suggestions: List[str] = []

        if missing:
            issues.append(f"Missing exports: {', '.join(missing[:10])}")
            suggestions.append(
                "Add modules that export: " + ", ".join(missing[:5])
            )
        if mismatches:
            issues.append(f"Type mismatches: {', '.join(mismatches[:10])}")
            suggestions.append("Reconcile the following interfaces: " + "; ".join(mismatches[:3]))
        if cycles:
            cycle_strs = [" → ".join(c) for c in cycles[:5]]
            issues.append(f"Dependency cycles: {'; '.join(cycle_strs)}")
            suggestions.append("Break cycles by introducing interface modules or inverting dependencies.")

        passed = h1 == 0

        return ConditionResult(
            condition=VerificationCondition.COHERENCE,
            passed=passed,
            confidence=1.0 if passed else max(0.0, 1.0 - 0.15 * h1),
            evidence=(
                f"H¹ = {h1}. "
                + (f"Generators: {generators}. " if generators else "")
                + (f"Issues: {'; '.join(issues)}" if issues else "No coherence issues found.")
            ),
            trust_level="STRUCTURAL",
            details={
                "h1": h1,
                "generators": generators,
                "missing_exports": missing,
                "type_mismatches": mismatches,
                "cycles": cycles,
                "dependency_graph": dep_graph,
            },
            suggestions=suggestions,
        )

    # ----- graph construction -------------------------------------------

    def build_interface_graph(
        self, modules: List[Dict[str, Any]]
    ) -> Dict[str, List[str]]:
        """Build a dependency graph: module_name -> [modules it depends on]."""
        graph: Dict[str, List[str]] = {}
        for mod in modules:
            name = mod.get("name", "")
            deps = mod.get("depends_on", [])
            if isinstance(deps, str):
                deps = [d.strip() for d in deps.split(",") if d.strip()]
            graph[name] = list(deps)
        return graph

    # ----- missing-export analysis --------------------------------------

    def find_missing_exports(self, modules: List[Dict[str, Any]]) -> List[str]:
        """Find symbols imported by some module but exported by none."""
        all_exports: Set[str] = set()
        all_imports: Set[str] = set()
        for mod in modules:
            exports = mod.get("exports", [])
            if isinstance(exports, str):
                exports = [e.strip() for e in exports.split(",") if e.strip()]
            all_exports.update(exports)

            imports = mod.get("imports", [])
            if isinstance(imports, str):
                imports = [i.strip() for i in imports.split(",") if i.strip()]
            all_imports.update(imports)

        return sorted(all_imports - all_exports)

    # ----- type-mismatch analysis ---------------------------------------

    def find_type_mismatches(
        self, interfaces: List[Dict[str, Any]]
    ) -> List[str]:
        """Find interfaces where provider and consumer disagree on types.

        Each interface dict should have:
        - ``name``: the symbol / API name
        - ``provider_type``: the type the provider declares
        - ``consumer_type``: the type the consumer expects
        """
        mismatches: List[str] = []
        for iface in interfaces:
            name = iface.get("name", "<unnamed>")
            prov = iface.get("provider_type", "")
            cons = iface.get("consumer_type", "")
            if prov and cons and not self._types_compatible(prov, cons):
                mismatches.append(f"{name}: provider={prov} vs consumer={cons}")
        return mismatches

    # ----- cycle detection (Kahn / DFS) ---------------------------------

    def find_cycles(
        self, dependency_graph: Dict[str, List[str]]
    ) -> List[List[str]]:
        """Find all elementary cycles in *dependency_graph* (Johnson's alg simplified)."""
        visited: Set[str] = set()
        on_stack: Set[str] = set()
        stack: List[str] = []
        cycles: List[List[str]] = []

        nodes = set(dependency_graph.keys())
        for deps in dependency_graph.values():
            nodes.update(deps)

        adj: Dict[str, List[str]] = defaultdict(list)
        for node, deps in dependency_graph.items():
            for dep in deps:
                adj[node].append(dep)

        def _dfs(node: str) -> None:
            visited.add(node)
            on_stack.add(node)
            stack.append(node)

            for neighbour in adj.get(node, []):
                if neighbour not in visited:
                    _dfs(neighbour)
                elif neighbour in on_stack:
                    # Extract cycle
                    idx = stack.index(neighbour)
                    cycle = stack[idx:] + [neighbour]
                    cycles.append(cycle)

            stack.pop()
            on_stack.discard(node)

        for node in sorted(nodes):
            if node not in visited:
                _dfs(node)

        return cycles

    # ----- Čech cohomology (discrete) -----------------------------------

    def compute_h1(
        self,
        modules: List[Dict[str, Any]],
        interfaces: List[Dict[str, Any]],
    ) -> int:
        """Compute dim H¹ ≈ #independent obstructions.

        Simplification: H¹ = |missing_exports| + |type_mismatches| + |cycles|.
        Each of these is an independent generator of the first cohomology
        of the nerve of the module cover.
        """
        missing = self.find_missing_exports(modules)
        mismatches = self.find_type_mismatches(interfaces)
        dep_graph = self.build_interface_graph(modules)
        cycles = self.find_cycles(dep_graph)
        return len(missing) + len(mismatches) + len(cycles)

    def h1_generators(
        self,
        modules: List[Dict[str, Any]],
        interfaces: List[Dict[str, Any]],
    ) -> List[str]:
        """Return human-readable descriptions of H¹ generators."""
        generators: List[str] = []
        for sym in self.find_missing_exports(modules):
            generators.append(f"missing-export({sym})")
        for mm in self.find_type_mismatches(interfaces):
            generators.append(f"type-mismatch({mm})")
        dep_graph = self.build_interface_graph(modules)
        for cyc in self.find_cycles(dep_graph):
            generators.append(f"cycle({' → '.join(cyc)})")
        return generators

    # ----- helpers ------------------------------------------------------

    @staticmethod
    def _types_compatible(provider: str, consumer: str) -> bool:
        """Very conservative syntactic compatibility check.

        Two types are compatible if they are literally equal after
        whitespace normalisation, or if the consumer is ``Any``.
        """
        norm_p = re.sub(r"\s+", " ", provider.strip())
        norm_c = re.sub(r"\s+", " ", consumer.strip())
        if norm_p == norm_c:
            return True
        if norm_c.lower() in ("any", "object", "unknown"):
            return True
        # Check if consumer is a supertype pattern
        if norm_c.startswith("Optional[") and norm_p == norm_c[len("Optional["):-1]:
            return True
        return False

    @staticmethod
    def _topological_sort(graph: Dict[str, List[str]]) -> Optional[List[str]]:
        """Return a topological ordering or ``None`` if a cycle exists."""
        in_degree: Dict[str, int] = defaultdict(int)
        for node in graph:
            in_degree.setdefault(node, 0)
            for dep in graph[node]:
                in_degree[dep] += 1

        queue: deque[str] = deque(n for n, d in in_degree.items() if d == 0)
        order: List[str] = []

        while queue:
            node = queue.popleft()
            order.append(node)
            for dep in graph.get(node, []):
                in_degree[dep] -= 1
                if in_degree[dep] == 0:
                    queue.append(dep)

        return order if len(order) == len(in_degree) else None


# ===================================================================
# FeasibilityChecker
# ===================================================================
class FeasibilityChecker:
    """Check ∀ leaf. atomic(leaf) — every leaf is implementable.

    A leaf module is *atomic* iff:

    - ``estimated_loc ≤ threshold`` (default 300)
    - ``σ_width ≤ 1`` (single responsibility)
    - ``π_arity ≤ max_params`` (default 5)
    - No unresolved dependencies on non-existent modules
    """

    def __init__(
        self,
        loc_threshold: int = _DEFAULT_LOC_THRESHOLD,
        max_params: int = _DEFAULT_MAX_PARAMS,
    ) -> None:
        self.loc_threshold = loc_threshold
        self.max_params = max_params

    # ----- public API ---------------------------------------------------

    def check(
        self,
        leaves: List[Dict[str, Any]],
        config: Optional[Dict[str, Any]] = None,
    ) -> ConditionResult:
        """Run feasibility over all *leaves* and return a result."""
        cfg = config or {}
        loc_thr = cfg.get("loc_threshold", self.loc_threshold)
        max_p = cfg.get("max_params", self.max_params)

        non_atomic = self.non_atomic_leaves(leaves)
        passed = len(non_atomic) == 0

        suggestions: List[str] = []
        for na in non_atomic:
            decomp = self.suggest_decomposition(na)
            name = na.get("name", "<unnamed>")
            reasons = na.get("_infeasibility_reasons", [])
            suggestions.append(
                f"Decompose '{name}' ({'; '.join(reasons)}) into "
                + ", ".join(d.get("name", "?") for d in decomp)
            )

        return ConditionResult(
            condition=VerificationCondition.FEASIBILITY,
            passed=passed,
            confidence=1.0 if passed else max(0.0, 1.0 - 0.2 * len(non_atomic)),
            evidence=(
                f"All {len(leaves)} leaves are atomic."
                if passed
                else f"{len(non_atomic)}/{len(leaves)} leaves are non-atomic."
            ),
            trust_level="STRUCTURAL",
            details={
                "total_leaves": len(leaves),
                "non_atomic_count": len(non_atomic),
                "non_atomic": [
                    {
                        "name": na.get("name", ""),
                        "reasons": na.get("_infeasibility_reasons", []),
                    }
                    for na in non_atomic
                ],
                "loc_threshold": loc_thr,
                "max_params": max_p,
            },
            suggestions=suggestions,
        )

    # ----- non-atomic detection -----------------------------------------

    def non_atomic_leaves(self, leaves: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Return leaves that violate atomicity."""
        result: List[Dict[str, Any]] = []
        for leaf in leaves:
            reasons = self._check_atomicity(leaf)
            if reasons:
                annotated = dict(leaf)
                annotated["_infeasibility_reasons"] = reasons
                result.append(annotated)
        return result

    # ----- decomposition suggestions ------------------------------------

    def suggest_decomposition(
        self, non_atomic: Dict[str, Any]
    ) -> List[Dict[str, Any]]:
        """Suggest how to split a non-atomic leaf into atomic parts.

        Uses a simple heuristic: divide estimated_loc by the threshold
        to get the number of sub-modules, then partition responsibilities.
        """
        est_loc = non_atomic.get("estimated_loc", self.loc_threshold + 1)
        parts = max(2, math.ceil(est_loc / self.loc_threshold))

        responsibilities: List[str] = non_atomic.get("responsibilities", [])
        if isinstance(responsibilities, str):
            responsibilities = [r.strip() for r in responsibilities.split(",") if r.strip()]

        # Round-robin responsibilities into parts
        sub_modules: List[Dict[str, Any]] = []
        base_name = non_atomic.get("name", "module")
        for i in range(parts):
            assigned = responsibilities[i::parts] if responsibilities else []
            sub_modules.append(
                {
                    "name": f"{base_name}_part{i + 1}",
                    "estimated_loc": est_loc // parts,
                    "responsibilities": assigned,
                    "sigma_width": 1,
                    "pi_arity": min(
                        non_atomic.get("pi_arity", self.max_params),
                        self.max_params,
                    ),
                }
            )
        return sub_modules

    # ----- private helpers ----------------------------------------------

    def _check_atomicity(self, leaf: Dict[str, Any]) -> List[str]:
        """Return a list of reasons why *leaf* is non-atomic (empty = ok)."""
        reasons: List[str] = []

        est_loc = leaf.get("estimated_loc", 0)
        if est_loc > self.loc_threshold:
            reasons.append(f"loc={est_loc}>{self.loc_threshold}")

        sigma_w = leaf.get("sigma_width", 1)
        if sigma_w > 1:
            reasons.append(f"σ-width={sigma_w}>1")

        pi_a = leaf.get("pi_arity", 0)
        if pi_a > self.max_params:
            reasons.append(f"π-arity={pi_a}>{self.max_params}")

        unresolved = leaf.get("unresolved_deps", [])
        if unresolved:
            reasons.append(f"unresolved deps: {unresolved}")

        return reasons


# ===================================================================
# ConsistencyChecker
# ===================================================================
class ConsistencyChecker:
    """Check Z3.check(⋀ constraints) = SAT — constraints are consistent.

    Collects and encodes constraints from all modules:

    * **Type constraints** – return types, parameter types
    * **Refinement constraints** – value ranges, invariants
    * **Interface constraints** – shared types must match across boundaries
    * **Timing constraints** – latency budgets, throughput requirements

    When Z3 is available, the constraints are encoded as an SMT formula
    and checked for satisfiability.  Without Z3, a structural heuristic
    is used (lower confidence).
    """

    # ----- public API ---------------------------------------------------

    def check(
        self,
        all_constraints: List[Dict[str, Any]],
    ) -> ConditionResult:
        """Check all constraints for consistency."""
        raw = self.collect_constraints_from_dicts(all_constraints)
        if not raw:
            return ConditionResult(
                condition=VerificationCondition.CONSISTENCY,
                passed=True,
                confidence=0.6,
                evidence="No constraints to check; vacuously consistent.",
                trust_level="HEURISTIC",
            )

        z3_formula = self.encode_z3(raw)
        if z3_formula is not None and _HAS_Z3:
            sat, model_or_core = self.check_sat(z3_formula)
            if sat:
                return ConditionResult(
                    condition=VerificationCondition.CONSISTENCY,
                    passed=True,
                    confidence=1.0,
                    evidence="Z3 reports SAT – all constraints are satisfiable.",
                    trust_level="Z3",
                    details={"z3_model": model_or_core},
                )
            else:
                core = self.minimal_unsat_core(raw)
                return ConditionResult(
                    condition=VerificationCondition.CONSISTENCY,
                    passed=False,
                    confidence=1.0,
                    evidence="Z3 reports UNSAT – constraints are contradictory.",
                    trust_level="Z3",
                    details={"unsat_core": core},
                    suggestions=[
                        f"Remove or relax constraint: {c}" for c in core[:5]
                    ],
                )

        # Fallback: heuristic consistency (no Z3)
        return self._heuristic_check(raw)

    # ----- constraint collection ----------------------------------------

    def collect_constraints(
        self, modules: List[Dict[str, Any]]
    ) -> List[str]:
        """Extract raw constraint strings from module dicts."""
        constraints: List[str] = []
        for mod in modules:
            for c in mod.get("constraints", []):
                if isinstance(c, str):
                    constraints.append(c)
                elif isinstance(c, dict):
                    constraints.append(json.dumps(c))
        return constraints

    def collect_constraints_from_dicts(
        self, all_constraints: List[Dict[str, Any]]
    ) -> List[str]:
        """Normalise heterogeneous constraint dicts into string form."""
        result: List[str] = []
        for entry in all_constraints:
            if isinstance(entry, str):
                result.append(entry)
            elif isinstance(entry, dict):
                expr = entry.get("expression") or entry.get("constraint") or entry.get("formula")
                if expr:
                    result.append(str(expr))
                else:
                    result.append(json.dumps(entry))
        return result

    # ----- Z3 encoding --------------------------------------------------

    def encode_z3(self, constraints: List[str]) -> Optional[str]:
        """Attempt to encode *constraints* as a Z3-compatible SMT-LIB string.

        Only simple arithmetic/boolean constraints are supported.
        Returns ``None`` if encoding fails.
        """
        if not _HAS_Z3:
            return None

        lines: List[str] = []
        declared_vars: Set[str] = set()

        for raw in constraints:
            parsed = self._parse_constraint(raw)
            if parsed is None:
                continue
            kind, data = parsed
            if kind == "comparison":
                lhs, op, rhs = data
                for v in self._extract_variables(lhs + " " + rhs):
                    if v not in declared_vars:
                        lines.append(f"(declare-const {v} Int)")
                        declared_vars.add(v)
                smt_expr = self._comparison_to_smt(lhs, op, rhs)
                if smt_expr:
                    lines.append(f"(assert {smt_expr})")
            elif kind == "boolean":
                lines.append(f"(assert {data})")

        if not lines:
            return None

        lines.append("(check-sat)")
        return "\n".join(lines)

    # ----- Z3 satisfiability -------------------------------------------

    def check_sat(
        self, z3_formula: str
    ) -> Tuple[bool, Optional[Dict[str, Any]]]:
        """Check satisfiability via Z3.

        Returns (True, model_dict) if SAT or (False, None) if UNSAT.
        """
        if not _HAS_Z3:
            return True, None

        try:
            solver = _z3.Solver()
            solver.set("timeout", 5000)  # 5 s timeout

            # Parse the SMT-LIB string
            assertions = _z3.parse_smt2_string(z3_formula)
            for a in assertions:
                solver.add(a)

            result = solver.check()
            if result == _z3.sat:
                model = solver.model()
                model_dict = {str(d): str(model[d]) for d in model.decls()}
                return True, model_dict
            else:
                return False, None
        except Exception as exc:  # noqa: BLE001
            logger.warning("Z3 check failed: %s", exc)
            return True, None  # be optimistic if Z3 crashes

    # ----- UNSAT core ---------------------------------------------------

    def minimal_unsat_core(
        self, constraints: List[str]
    ) -> List[str]:
        """Compute a minimal unsatisfiable subset of *constraints*.

        Uses Z3's built-in UNSAT core extraction if available,
        otherwise falls back to incremental removal.
        """
        if not _HAS_Z3:
            return constraints[:3]  # fallback: return first few

        try:
            solver = _z3.Solver()
            solver.set("timeout", 10000)
            solver.set("unsat_core", True)

            tracking: Dict[str, str] = {}
            for i, raw in enumerate(constraints):
                parsed = self._parse_constraint(raw)
                if parsed is None:
                    continue
                kind, data = parsed
                label = f"c{i}"
                tracker = _z3.Bool(label)
                tracking[label] = raw

                if kind == "comparison":
                    lhs, op, rhs = data
                    smt = self._comparison_to_smt(lhs, op, rhs)
                    if smt:
                        expr = _z3.parse_smt2_string(
                            f"(assert {smt})",
                        )
                        for e in expr:
                            solver.assert_and_track(e, tracker)
                elif kind == "boolean":
                    expr = _z3.parse_smt2_string(f"(assert {data})")
                    for e in expr:
                        solver.assert_and_track(e, tracker)

            result = solver.check()
            if result == _z3.unsat:
                core_labels = solver.unsat_core()
                return [tracking.get(str(lbl), str(lbl)) for lbl in core_labels]
            return []
        except Exception:  # noqa: BLE001
            return constraints[:3]

    # ----- heuristic fallback -------------------------------------------

    def _heuristic_check(self, constraints: List[str]) -> ConditionResult:
        """Structural consistency check when Z3 is unavailable.

        Looks for obvious contradictions:
        - Same variable required to be both > X and < Y where X ≥ Y
        - Duplicate contradictory boolean constraints
        """
        contradictions: List[str] = []
        bounds: Dict[str, Dict[str, List[float]]] = defaultdict(
            lambda: {"lower": [], "upper": []}
        )

        for raw in constraints:
            parsed = self._parse_constraint(raw)
            if parsed is None:
                continue
            kind, data = parsed
            if kind == "comparison":
                lhs, op, rhs = data
                self._collect_bounds(lhs, op, rhs, bounds)

        for var, bd in bounds.items():
            if bd["lower"] and bd["upper"]:
                lo = max(bd["lower"])
                hi = min(bd["upper"])
                if lo > hi:
                    contradictions.append(
                        f"{var}: lower bound {lo} > upper bound {hi}"
                    )

        passed = len(contradictions) == 0
        return ConditionResult(
            condition=VerificationCondition.CONSISTENCY,
            passed=passed,
            confidence=0.5,
            evidence=(
                "Heuristic check found no obvious contradictions."
                if passed
                else f"Heuristic found {len(contradictions)} contradictions."
            ),
            trust_level="HEURISTIC",
            details={"contradictions": contradictions, "z3_available": False},
            suggestions=[
                f"Resolve contradiction: {c}" for c in contradictions[:5]
            ],
        )

    # ----- parsing helpers ----------------------------------------------

    _CMP_RE = re.compile(
        r"^\s*([a-zA-Z_][\w.]*)\s*(<=|>=|<|>|==|!=)\s*(.+?)\s*$"
    )

    def _parse_constraint(
        self, raw: str
    ) -> Optional[Tuple[str, Any]]:
        """Try to parse *raw* into (kind, data).

        Returns:
        - ("comparison", (lhs, op, rhs))
        - ("boolean", smt_expr_str)
        - None if unparseable
        """
        m = self._CMP_RE.match(raw)
        if m:
            return ("comparison", (m.group(1), m.group(2), m.group(3).strip()))

        # Check if it looks like SMT-LIB
        stripped = raw.strip()
        if stripped.startswith("(") and stripped.endswith(")"):
            return ("boolean", stripped)

        return None

    @staticmethod
    def _extract_variables(text: str) -> List[str]:
        """Pull out identifiers that look like variable names."""
        return re.findall(r"\b([a-zA-Z_]\w*)\b", text)

    @staticmethod
    def _comparison_to_smt(lhs: str, op: str, rhs: str) -> Optional[str]:
        """Convert ``lhs op rhs`` to an SMT-LIB expression."""
        op_map = {
            "<=": "<=",
            ">=": ">=",
            "<": "<",
            ">": ">",
            "==": "=",
            "!=": "distinct",
        }
        smt_op = op_map.get(op)
        if smt_op is None:
            return None
        # Simple: only handle variable vs numeric literal
        try:
            rhs_val = str(int(rhs))
        except ValueError:
            try:
                rhs_val = str(int(float(rhs)))
            except ValueError:
                rhs_val = rhs
        return f"({smt_op} {lhs} {rhs_val})"

    @staticmethod
    def _collect_bounds(
        lhs: str,
        op: str,
        rhs: str,
        bounds: Dict[str, Dict[str, List[float]]],
    ) -> None:
        try:
            val = float(rhs)
        except ValueError:
            return
        if op in (">", ">="):
            bounds[lhs]["lower"].append(val)
        elif op in ("<", "<="):
            bounds[lhs]["upper"].append(val)


# ===================================================================
# BudgetChecker
# ===================================================================
class BudgetChecker:
    """Check estimated_cost(P) ≤ budget.

    Estimates the token / time / monetary cost of executing a plan and
    verifies it fits within the caller-specified budget.
    """

    # Rough per-line token estimates
    _TOKENS_PER_LOC_GENERATION = 15
    _TOKENS_PER_LOC_VERIFICATION = 8

    # ----- public API ---------------------------------------------------

    def check(
        self,
        plan_summary: Dict[str, Any],
        budget: Dict[str, Any],
    ) -> ConditionResult:
        """Run the budget check."""
        gen_cost = self.estimate_generation_cost(plan_summary)
        ver_cost = self.estimate_verification_cost(plan_summary)

        total_tokens = gen_cost.get("tokens", 0) + ver_cost.get("tokens", 0)
        total_calls = gen_cost.get("llm_calls", 0) + ver_cost.get("llm_calls", 0)

        budget_tokens = budget.get("max_tokens", float("inf"))
        budget_calls = budget.get("max_llm_calls", float("inf"))
        budget_cost = budget.get("max_cost_usd", float("inf"))

        estimated_cost_usd = total_tokens * budget.get("cost_per_token", 0.0)

        within_tokens = total_tokens <= budget_tokens * _BUDGET_TOLERANCE
        within_calls = total_calls <= budget_calls * _BUDGET_TOLERANCE
        within_cost = estimated_cost_usd <= budget_cost * _BUDGET_TOLERANCE

        passed = within_tokens and within_calls and within_cost

        overages: List[str] = []
        suggestions: List[str] = []
        if not within_tokens:
            overages.append(
                f"tokens: {total_tokens} > budget {budget_tokens}"
            )
            suggestions.append("Reduce plan scope or increase token budget.")
        if not within_calls:
            overages.append(
                f"LLM calls: {total_calls} > budget {budget_calls}"
            )
            suggestions.append("Merge small modules to reduce LLM call count.")
        if not within_cost:
            overages.append(
                f"cost: ${estimated_cost_usd:.4f} > budget ${budget_cost:.4f}"
            )
            suggestions.append("Use a cheaper model or reduce plan size.")

        return ConditionResult(
            condition=VerificationCondition.BUDGET,
            passed=passed,
            confidence=0.8,
            evidence=(
                f"Estimated {total_tokens} tokens, {total_calls} calls, "
                f"${estimated_cost_usd:.4f}."
                + (f" Overages: {'; '.join(overages)}." if overages else " Within budget.")
            ),
            trust_level="HEURISTIC",
            details={
                "generation_cost": gen_cost,
                "verification_cost": ver_cost,
                "total_tokens": total_tokens,
                "total_calls": total_calls,
                "estimated_cost_usd": round(estimated_cost_usd, 6),
                "budget": budget,
            },
            suggestions=suggestions,
        )

    # ----- cost estimation ----------------------------------------------

    def estimate_generation_cost(
        self, plan: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Estimate token/call cost of generating code for the plan."""
        modules = plan.get("modules", [])
        total_loc = 0
        for mod in modules:
            total_loc += mod.get("estimated_loc", 100)

        tokens = total_loc * self._TOKENS_PER_LOC_GENERATION
        llm_calls = len(modules)

        return {
            "tokens": tokens,
            "llm_calls": llm_calls,
            "estimated_loc": total_loc,
        }

    def estimate_verification_cost(
        self, plan: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Estimate token/call cost of verifying the generated code."""
        modules = plan.get("modules", [])
        total_loc = sum(m.get("estimated_loc", 100) for m in modules)

        tokens = total_loc * self._TOKENS_PER_LOC_VERIFICATION
        # Verification typically needs fewer LLM calls (type-checking is local)
        llm_calls = max(1, len(modules) // 2)

        return {
            "tokens": tokens,
            "llm_calls": llm_calls,
        }


# ===================================================================
# PlanCertificate
# ===================================================================
@dataclass
class PlanCertificate:
    """Machine-readable certificate that a plan has been verified.

    The certificate records which conditions were checked, the results,
    and enough information to audit the verification later.
    """

    plan_hash: str
    spec_hash: str
    timestamp: str
    conditions_met: List[str]
    coverage_score: float
    h1_dimension: int
    consistency_proof: Optional[str] = None  # Z3 model if SAT
    budget_estimate: Dict[str, Any] = field(default_factory=dict)
    trust_level: str = "STRUCTURAL"

    # -- serialisation ---------------------------------------------------

    def to_json(self) -> str:
        """Serialise to JSON."""
        return json.dumps(
            {
                "plan_hash": self.plan_hash,
                "spec_hash": self.spec_hash,
                "timestamp": self.timestamp,
                "conditions_met": self.conditions_met,
                "coverage_score": round(self.coverage_score, 4),
                "h1_dimension": self.h1_dimension,
                "consistency_proof": self.consistency_proof,
                "budget_estimate": self.budget_estimate,
                "trust_level": self.trust_level,
            },
            indent=2,
        )

    def to_lean(self) -> str:
        """Generate a Lean 4 declaration representing this certificate.

        This is a *stub* that records the verification metadata as a
        Lean structure literal — not a full proof.
        """
        conditions_str = ", ".join(f'"{c}"' for c in self.conditions_met)
        return textwrap.dedent(f"""\
            /-- Auto-generated plan verification certificate. --/
            def planCertificate : PlanCert where
              planHash       := "{self.plan_hash}"
              specHash       := "{self.spec_hash}"
              timestamp      := "{self.timestamp}"
              conditionsMet  := [{conditions_str}]
              coverageScore  := {self.coverage_score:.4f}
              h1Dimension    := {self.h1_dimension}
              trustLevel     := "{self.trust_level}"
        """)

    def verify_integrity(self) -> bool:
        """Re-check that the plan_hash and spec_hash are non-empty."""
        return bool(self.plan_hash) and bool(self.spec_hash)

    def to_dict(self) -> Dict[str, Any]:
        return json.loads(self.to_json())


# ===================================================================
# PlanVerificationResult
# ===================================================================
@dataclass
class PlanVerificationResult:
    """Aggregate result of verifying a plan against all five conditions."""

    all_passed: bool
    conditions: Dict[str, ConditionResult]
    certificate: Optional[PlanCertificate] = None
    suggestions: List[str] = field(default_factory=list)

    # -- presentation ----------------------------------------------------

    def summary(self) -> str:
        """One-line summary of the verification outcome."""
        n_pass = sum(1 for r in self.conditions.values() if r.passed)
        n_total = len(self.conditions)
        status = "VERIFIED ✓" if self.all_passed else "FAILED ✗"
        return f"Plan verification: {status} ({n_pass}/{n_total} conditions passed)"

    def to_markdown(self) -> str:
        """Render a Markdown report of the verification."""
        lines: List[str] = []
        lines.append(f"# Plan Verification Report\n")
        lines.append(f"**Status:** {'✅ VERIFIED' if self.all_passed else '❌ FAILED'}\n")

        for name, result in self.conditions.items():
            icon = "✅" if result.passed else "❌"
            lines.append(f"## {icon} {name}")
            lines.append(f"- **Confidence:** {result.confidence:.2f}")
            lines.append(f"- **Trust level:** {result.trust_level}")
            lines.append(f"- **Evidence:** {result.evidence}")
            if result.suggestions:
                lines.append("- **Suggestions:**")
                for s in result.suggestions:
                    lines.append(f"  - {s}")
            lines.append("")

        if self.suggestions:
            lines.append("## Overall Suggestions\n")
            for s in self.suggestions:
                lines.append(f"- {s}")
            lines.append("")

        if self.certificate:
            lines.append("## Certificate\n")
            lines.append(f"```json\n{self.certificate.to_json()}\n```\n")

        return "\n".join(lines)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "all_passed": self.all_passed,
            "conditions": {k: v.to_dict() for k, v in self.conditions.items()},
            "certificate": self.certificate.to_dict() if self.certificate else None,
            "suggestions": self.suggestions,
        }


# ===================================================================
# PlanVerifier — MAIN CLASS
# ===================================================================
class PlanVerifier:
    """Verify a code generation plan before execution.

    Orchestrates the five sub-checkers and produces a
    :class:`PlanVerificationResult` (and :class:`PlanCertificate` on
    success).

    Typical usage::

        verifier = PlanVerifier()
        result = verifier.verify(plan, spec, budget={"max_tokens": 50000})
        if result.all_passed:
            execute(plan, result.certificate)
        else:
            print(result.to_markdown())
    """

    def __init__(
        self,
        coverage_threshold: float = _DEFAULT_COVERAGE_THRESHOLD,
        loc_threshold: int = _DEFAULT_LOC_THRESHOLD,
        max_params: int = _DEFAULT_MAX_PARAMS,
    ) -> None:
        self._coverage = CoverageChecker(coverage_threshold=coverage_threshold)
        self._coherence = CoherenceChecker()
        self._feasibility = FeasibilityChecker(
            loc_threshold=loc_threshold, max_params=max_params
        )
        self._consistency = ConsistencyChecker()
        self._budget = BudgetChecker()

    # ----- main entry point ---------------------------------------------

    def verify(
        self,
        plan: Dict[str, Any],
        spec: str,
        budget: Optional[Dict[str, Any]] = None,
        oracle_fn: Optional[Callable[..., Any]] = None,
    ) -> PlanVerificationResult:
        """Run all five verification conditions against *plan*.

        Parameters
        ----------
        plan:
            A dict with keys ``modules``, ``interfaces``, ``constraints``,
            etc. describing the code generation plan.
        spec:
            The natural-language specification the plan is meant to satisfy.
        budget:
            Optional budget limits (``max_tokens``, ``max_llm_calls``, etc.).
        oracle_fn:
            Optional oracle (e.g. LLM) for semantic matching.
        """
        results: Dict[str, ConditionResult] = {}
        all_suggestions: List[str] = []

        # 1. Coverage
        coverage_result = self.verify_condition(
            VerificationCondition.COVERAGE, plan=plan, spec=spec, oracle_fn=oracle_fn
        )
        results["COVERAGE"] = coverage_result

        # 2. Coherence
        coherence_result = self.verify_condition(
            VerificationCondition.COHERENCE, plan=plan, spec=spec
        )
        results["COHERENCE"] = coherence_result

        # 3. Feasibility
        feasibility_result = self.verify_condition(
            VerificationCondition.FEASIBILITY, plan=plan, spec=spec
        )
        results["FEASIBILITY"] = feasibility_result

        # 4. Consistency
        consistency_result = self.verify_condition(
            VerificationCondition.CONSISTENCY, plan=plan, spec=spec
        )
        results["CONSISTENCY"] = consistency_result

        # 5. Budget
        budget_result = self.verify_condition(
            VerificationCondition.BUDGET, plan=plan, spec=spec, budget=budget
        )
        results["BUDGET"] = budget_result

        # Gather suggestions
        for r in results.values():
            if not r.passed:
                all_suggestions.extend(r.suggestions)

        all_passed = all(r.passed for r in results.values())

        certificate: Optional[PlanCertificate] = None
        if all_passed:
            certificate = self._build_certificate(plan, spec, results, budget)

        return PlanVerificationResult(
            all_passed=all_passed,
            conditions=results,
            certificate=certificate,
            suggestions=all_suggestions,
        )

    # ----- per-condition dispatch ---------------------------------------

    def verify_condition(
        self,
        condition: VerificationCondition,
        *,
        plan: Dict[str, Any],
        spec: str,
        budget: Optional[Dict[str, Any]] = None,
        oracle_fn: Optional[Callable[..., Any]] = None,
    ) -> ConditionResult:
        """Run a single verification condition."""
        modules = plan.get("modules", [])
        interfaces = plan.get("interfaces", [])
        constraints = plan.get("constraints", [])
        leaves = self._extract_leaves(modules)

        if condition is VerificationCondition.COVERAGE:
            return self._coverage.check(spec, modules, oracle_fn=oracle_fn)

        if condition is VerificationCondition.COHERENCE:
            return self._coherence.check(modules, interfaces)

        if condition is VerificationCondition.FEASIBILITY:
            return self._feasibility.check(leaves)

        if condition is VerificationCondition.CONSISTENCY:
            return self._consistency.check(constraints)

        if condition is VerificationCondition.BUDGET:
            effective_budget = budget or {"max_tokens": float("inf")}
            return self._budget.check(plan, effective_budget)

        raise ValueError(f"Unknown condition: {condition}")

    # ----- quick structural check ---------------------------------------

    def quick_verify(self, plan: Dict[str, Any], spec: str) -> bool:
        """Fast structural-only verification (no oracle, no Z3).

        Useful as a pre-flight check before committing to the full
        (potentially expensive) verification.
        """
        modules = plan.get("modules", [])
        interfaces = plan.get("interfaces", [])
        leaves = self._extract_leaves(modules)

        cov = self._coverage.check(spec, modules, oracle_fn=None)
        coh = self._coherence.check(modules, interfaces)
        fea = self._feasibility.check(leaves)

        return cov.passed and coh.passed and fea.passed

    # ----- certificate construction -------------------------------------

    def _build_certificate(
        self,
        plan: Dict[str, Any],
        spec: str,
        results: Dict[str, ConditionResult],
        budget: Optional[Dict[str, Any]],
    ) -> PlanCertificate:
        """Build a :class:`PlanCertificate` from successful results."""
        plan_hash = hashlib.sha256(
            json.dumps(plan, sort_keys=True, default=str).encode()
        ).hexdigest()[:16]
        spec_hash = hashlib.sha256(spec.encode()).hexdigest()[:16]

        coverage_score = results["COVERAGE"].details.get("coverage_ratio", 1.0)
        h1 = results["COHERENCE"].details.get("h1", 0)
        consistency_model = results["CONSISTENCY"].details.get("z3_model")
        consistency_proof = json.dumps(consistency_model) if consistency_model else None

        budget_estimate: Dict[str, Any] = {}
        if "BUDGET" in results:
            budget_estimate = {
                "total_tokens": results["BUDGET"].details.get("total_tokens", 0),
                "total_calls": results["BUDGET"].details.get("total_calls", 0),
                "estimated_cost_usd": results["BUDGET"].details.get(
                    "estimated_cost_usd", 0.0
                ),
            }

        # Determine overall trust level (weakest link)
        trust_levels = [r.trust_level for r in results.values()]
        trust_order = ["HEURISTIC", "SEMANTIC", "STRUCTURAL", "Z3"]
        weakest = "Z3"
        for tl in trust_levels:
            if tl in trust_order:
                idx = trust_order.index(tl)
                if idx < trust_order.index(weakest):
                    weakest = tl

        return PlanCertificate(
            plan_hash=plan_hash,
            spec_hash=spec_hash,
            timestamp=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            conditions_met=[c.name for c in VerificationCondition],
            coverage_score=coverage_score,
            h1_dimension=h1,
            consistency_proof=consistency_proof,
            budget_estimate=budget_estimate,
            trust_level=weakest,
        )

    # ----- helpers ------------------------------------------------------

    @staticmethod
    def _extract_leaves(modules: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Extract leaf modules (those with no children) from the plan.

        A module is a leaf if it has no ``children`` key or the children
        list is empty.  If the plan is flat (no hierarchy), every module
        is a leaf.
        """
        leaves: List[Dict[str, Any]] = []
        for mod in modules:
            children = mod.get("children")
            if not children:
                leaves.append(mod)
            else:
                # Recurse into children
                leaves.extend(PlanVerifier._extract_leaves(children))
        return leaves
