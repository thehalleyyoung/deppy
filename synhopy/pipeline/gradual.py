"""
SynHoPy Gradual Verification Engine

Unlike F*'s all-or-nothing approach, gradual verification lets you
verify *what you can*, track what remains unverified, and compute a
coverage metric.  Functions without specifications are inferred,
expensive obligations can be skipped, and trust boundaries are
propagated across call graphs.

Architecture:
    VerificationCoverage  — metrics (coverage %, trust score, badge)
    ObligationStatus      — per-obligation outcome
    GradualResult         — per-function result
    ModuleGradualResult   — per-module aggregation
    ProjectGradualResult  — project-wide aggregation
    GradualChecker        — the main engine
    SpecInferencer        — infer lightweight specs from code patterns
    TrustBoundary         — call-graph trust propagation
    GradualReport         — ASCII / JSON reporting & CI gates
"""
from __future__ import annotations

import ast
import json
import os
import re
import textwrap
import time
from dataclasses import dataclass, field
from typing import Any, Literal as LiteralType

from synhopy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Z3Proof, Structural, AxiomInvocation,
)
from synhopy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    Spec, SpecKind, FunctionSpec,
    Var, Literal, PyObjType, PyIntType, PyFloatType, PyStrType,
    PyBoolType, PyNoneType, PyListType, PyCallableType,
    RefinementType, PiType, arrow,
)
from synhopy.proofs.sugar import extract_spec

# Re-use pipeline components where possible
from synhopy.pipeline.verifier import (
    SpecExtractor, ObligationGenerator, CompositeStrategy,
    Z3Strategy, StructuralStrategy, AxiomStrategy,
)


# ═══════════════════════════════════════════════════════════════════
# §1  Coverage Metrics
# ═══════════════════════════════════════════════════════════════════

@dataclass
class VerificationCoverage:
    """Track verification coverage across a codebase."""

    total_functions: int = 0
    fully_verified: int = 0
    partially_verified: int = 0
    spec_only: int = 0
    unspecified: int = 0

    total_obligations: int = 0
    obligations_proved: int = 0
    obligations_assumed: int = 0
    obligations_failed: int = 0
    obligations_skipped: int = 0

    @property
    def coverage_pct(self) -> float:
        """Verification coverage: fraction of obligations proved."""
        if self.total_obligations == 0:
            return 0.0
        return (self.obligations_proved / self.total_obligations) * 100.0

    @property
    def trust_score(self) -> float:
        """Weighted trust score (proved > assumed > skipped > failed).

        Weights: proved=1.0, assumed=0.6, skipped=0.1, failed=0.0.
        Returns a percentage in [0, 100].
        """
        if self.total_obligations == 0:
            return 0.0
        score = (
            self.obligations_proved * 1.0
            + self.obligations_assumed * 0.6
            + self.obligations_skipped * 0.1
            + self.obligations_failed * 0.0
        )
        return (score / self.total_obligations) * 100.0

    def summary(self) -> str:
        """Pretty coverage report."""
        lines = [
            f"Coverage: {self.coverage_pct:.1f}%  Trust: {self.trust_score:.1f}%",
            f"Functions: {self.fully_verified} verified, "
            f"{self.partially_verified} partial, "
            f"{self.spec_only} spec-only, "
            f"{self.unspecified} unspecified "
            f"(total {self.total_functions})",
            f"Obligations: {self.obligations_proved} proved, "
            f"{self.obligations_assumed} assumed, "
            f"{self.obligations_skipped} skipped, "
            f"{self.obligations_failed} failed "
            f"(total {self.total_obligations})",
        ]
        return "\n".join(lines)

    def coverage_badge(self) -> str:
        """Generate a text badge: [■■■■■□□□□□ 50%]"""
        WIDTH = 10
        pct = self.coverage_pct
        filled = round(pct / 100.0 * WIDTH)
        filled = max(0, min(WIDTH, filled))
        bar = "■" * filled + "□" * (WIDTH - filled)
        return f"[{bar} {pct:.0f}%]"

    def merge(self, other: VerificationCoverage) -> VerificationCoverage:
        """Combine two coverage reports."""
        return VerificationCoverage(
            total_functions=self.total_functions + other.total_functions,
            fully_verified=self.fully_verified + other.fully_verified,
            partially_verified=self.partially_verified + other.partially_verified,
            spec_only=self.spec_only + other.spec_only,
            unspecified=self.unspecified + other.unspecified,
            total_obligations=self.total_obligations + other.total_obligations,
            obligations_proved=self.obligations_proved + other.obligations_proved,
            obligations_assumed=self.obligations_assumed + other.obligations_assumed,
            obligations_failed=self.obligations_failed + other.obligations_failed,
            obligations_skipped=self.obligations_skipped + other.obligations_skipped,
        )


# ═══════════════════════════════════════════════════════════════════
# §2  Result Data Structures
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ObligationStatus:
    """Outcome of a single proof obligation under gradual checking."""

    description: str
    status: LiteralType["proved", "assumed", "skipped", "failed", "timeout"]
    trust: TrustLevel
    proof_term: ProofTerm | None = None
    reason: str = ""

    def __repr__(self) -> str:
        icons = {
            "proved": "✓", "assumed": "≈", "skipped": "⊘",
            "failed": "✗", "timeout": "⏱",
        }
        return f"{icons.get(self.status, '?')} {self.description} [{self.status}]"


@dataclass
class GradualResult:
    """Gradual verification result for a single function."""

    function_name: str
    obligations: list[ObligationStatus] = field(default_factory=list)
    coverage: VerificationCoverage = field(default_factory=VerificationCoverage)
    trust_level: TrustLevel = TrustLevel.UNTRUSTED
    time_taken: float = 0.0
    has_spec: bool = True
    inferred_specs: list[InferredSpec] = field(default_factory=list)

    def __repr__(self) -> str:
        badge = self.coverage.coverage_badge()
        return f"{self.function_name}: {badge} [{self.trust_level.name}]"


@dataclass
class ModuleGradualResult:
    """Gradual verification result for a module."""

    module_name: str
    functions: list[GradualResult] = field(default_factory=list)
    coverage: VerificationCoverage = field(default_factory=VerificationCoverage)
    time_taken: float = 0.0

    def report(self) -> str:
        """Per-function report with coverage bars."""
        lines = [f"Module: {self.module_name}"]
        lines.append("─" * 50)
        for fr in self.functions:
            badge = fr.coverage.coverage_badge()
            lines.append(
                f"  {fr.function_name:<25s} {badge} {fr.trust_level.name}"
            )
        lines.append("─" * 50)
        lines.append(f"  {self.coverage.summary()}")
        return "\n".join(lines)


@dataclass
class ProjectGradualResult:
    """Gradual verification result for an entire project."""

    project_name: str
    modules: list[ModuleGradualResult] = field(default_factory=list)
    coverage: VerificationCoverage = field(default_factory=VerificationCoverage)
    time_taken: float = 0.0

    def report(self) -> str:
        """Human-readable project report."""
        lines = [
            f"Project: {self.project_name}",
            self.coverage.coverage_badge(),
            "",
        ]
        for mod in self.modules:
            lines.append(mod.report())
            lines.append("")
        lines.append(self.coverage.summary())
        return "\n".join(lines)

    def to_json(self) -> dict:
        """Machine-readable coverage for CI integration."""
        return {
            "project": self.project_name,
            "coverage_pct": round(self.coverage.coverage_pct, 2),
            "trust_score": round(self.coverage.trust_score, 2),
            "total_functions": self.coverage.total_functions,
            "fully_verified": self.coverage.fully_verified,
            "partially_verified": self.coverage.partially_verified,
            "spec_only": self.coverage.spec_only,
            "unspecified": self.coverage.unspecified,
            "obligations": {
                "total": self.coverage.total_obligations,
                "proved": self.coverage.obligations_proved,
                "assumed": self.coverage.obligations_assumed,
                "failed": self.coverage.obligations_failed,
                "skipped": self.coverage.obligations_skipped,
            },
            "time_taken_s": round(self.time_taken, 3),
            "modules": [
                {
                    "name": mod.module_name,
                    "coverage_pct": round(mod.coverage.coverage_pct, 2),
                    "functions": [
                        {
                            "name": f.function_name,
                            "trust": f.trust_level.name,
                            "coverage_pct": round(f.coverage.coverage_pct, 2),
                            "obligations": [
                                {
                                    "description": o.description,
                                    "status": o.status,
                                    "trust": o.trust.name,
                                    "reason": o.reason,
                                }
                                for o in f.obligations
                            ],
                        }
                        for f in mod.functions
                    ],
                }
                for mod in self.modules
            ],
        }

    def heatmap(self) -> str:
        """ASCII heatmap of verification coverage by file."""
        if not self.modules:
            return "(no modules)"

        max_name = max(len(m.module_name) for m in self.modules)
        max_name = min(max_name, 40)
        lines: list[str] = []
        lines.append(f"{'File':<{max_name}}  Coverage  Trust")
        lines.append("─" * (max_name + 24))
        for mod in self.modules:
            name = mod.module_name
            if len(name) > max_name:
                name = "…" + name[-(max_name - 1):]
            pct = mod.coverage.coverage_pct
            trust = mod.coverage.trust_score
            # Heat colours via block characters
            bar_w = 10
            filled = round(pct / 100.0 * bar_w)
            filled = max(0, min(bar_w, filled))
            bar = "█" * filled + "░" * (bar_w - filled)
            lines.append(f"{name:<{max_name}}  {bar} {pct:5.1f}%  {trust:5.1f}%")
        lines.append("─" * (max_name + 24))
        lines.append(
            f"{'Total':<{max_name}}  "
            f"{self.coverage.coverage_badge()}  "
            f"{self.coverage.trust_score:.1f}%"
        )
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# §3  Spec Inferencer
# ═══════════════════════════════════════════════════════════════════

@dataclass
class InferredSpec:
    """A lightweight specification inferred from code patterns."""

    kind: str  # "requires", "ensures", "pure", "exception", "type_check"
    description: str
    formal: str | None = None
    confidence: float = 1.0
    source: str = ""  # "return_type", "guard", "assert", "docstring", etc.

    def __repr__(self) -> str:
        conf = f" ({self.confidence:.0%})" if self.confidence < 1.0 else ""
        return f"InferredSpec({self.kind}: {self.description!r}{conf})"


class SpecInferencer:
    """Infer lightweight specs for functions that lack explicit annotations.

    Analyses:
        1. Return type → ensures isinstance(result, T)
        2. Guard clauses → requires
        3. assert statements → check
        4. Docstring "raises" → exception spec
        5. Pure analysis → @pure
        6. Loop with accumulator → guarantees result type
    """

    def infer(self, source: str, func_name: str) -> list[InferredSpec]:
        """Infer specs from code patterns, types, and docstrings."""
        try:
            tree = ast.parse(textwrap.dedent(source))
        except SyntaxError:
            return []

        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef) and node.name == func_name:
                return self._infer_from_node(node)
        return []

    def infer_all(self, source: str) -> dict[str, list[InferredSpec]]:
        """Infer specs for all functions in source."""
        try:
            tree = ast.parse(textwrap.dedent(source))
        except SyntaxError:
            return {}
        result: dict[str, list[InferredSpec]] = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                result[node.name] = self._infer_from_node(node)
        return result

    def _infer_from_node(self, node: ast.FunctionDef) -> list[InferredSpec]:
        specs: list[InferredSpec] = []
        specs.extend(self._infer_return_type(node))
        specs.extend(self._infer_guard_clauses(node))
        specs.extend(self._infer_asserts(node))
        specs.extend(self._infer_docstring(node))
        specs.extend(self._infer_purity(node))
        specs.extend(self._infer_loop_accumulator(node))
        return specs

    # --- individual inference strategies ---------------------------------

    def _infer_return_type(self, node: ast.FunctionDef) -> list[InferredSpec]:
        """Return type annotation → ensures isinstance(result, T)."""
        if node.returns is None:
            return []
        ann = ast.dump(node.returns) if not isinstance(node.returns, ast.Constant) else ""
        type_str = _annotation_to_str(node.returns)
        if type_str and type_str != "Any":
            return [InferredSpec(
                kind="ensures",
                description=f"result is {type_str}",
                formal=f"isinstance(result, {type_str})",
                confidence=0.95,
                source="return_type",
            )]
        return []

    def _infer_guard_clauses(self, node: ast.FunctionDef) -> list[InferredSpec]:
        """Guard clauses at the start of function → requires."""
        specs: list[InferredSpec] = []
        for stmt in _function_body(node):
            if isinstance(stmt, ast.If):
                test_src = _unparse_safe(stmt.test)
                if test_src and _body_is_raise(stmt):
                    negated = _negate_simple(test_src)
                    specs.append(InferredSpec(
                        kind="requires",
                        description=negated,
                        formal=negated,
                        confidence=0.8,
                        source="guard",
                    ))
                else:
                    break
            elif isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant):
                continue  # skip docstrings
            else:
                break
        return specs

    def _infer_asserts(self, node: ast.FunctionDef) -> list[InferredSpec]:
        """assert statements → check."""
        specs: list[InferredSpec] = []
        for stmt in ast.walk(node):
            if isinstance(stmt, ast.Assert):
                test_src = _unparse_safe(stmt.test)
                if test_src:
                    specs.append(InferredSpec(
                        kind="ensures",
                        description=f"assertion holds: {test_src}",
                        formal=test_src,
                        confidence=0.7,
                        source="assert",
                    ))
        return specs

    def _infer_docstring(self, node: ast.FunctionDef) -> list[InferredSpec]:
        """Docstring 'Raises' section → exception spec."""
        docstring = ast.get_docstring(node)
        if not docstring:
            return []
        specs: list[InferredSpec] = []
        # Look for 'Raises:' or ':raises ...:' patterns
        for m in re.finditer(
            r"(?:Raises|:raises)\s*[:\-]?\s*(\w+)", docstring, re.IGNORECASE
        ):
            exc = m.group(1)
            specs.append(InferredSpec(
                kind="exception",
                description=f"may raise {exc}",
                confidence=0.75,
                source="docstring",
            ))
        return specs

    def _infer_purity(self, node: ast.FunctionDef) -> list[InferredSpec]:
        """Detect pure functions (no global/nonlocal, no attribute sets)."""
        for stmt in ast.walk(node):
            if isinstance(stmt, (ast.Global, ast.Nonlocal)):
                return []
            if isinstance(stmt, ast.Assign):
                for target in stmt.targets:
                    if isinstance(target, ast.Attribute):
                        return []
            if isinstance(stmt, ast.AugAssign):
                if isinstance(stmt.target, ast.Attribute):
                    return []
        return [InferredSpec(
            kind="pure",
            description="function appears pure",
            confidence=0.6,
            source="purity_analysis",
        )]

    def _infer_loop_accumulator(self, node: ast.FunctionDef) -> list[InferredSpec]:
        """Loop with accumulator pattern → guarantees result type."""
        specs: list[InferredSpec] = []
        body = _function_body(node)
        for stmt in body:
            if isinstance(stmt, ast.For):
                # Check for append / += pattern
                for child in ast.walk(stmt):
                    if isinstance(child, ast.Expr) and isinstance(child.value, ast.Call):
                        func = child.value.func
                        if (isinstance(func, ast.Attribute) and func.attr == "append"):
                            specs.append(InferredSpec(
                                kind="ensures",
                                description="result is a list (loop-accumulator pattern)",
                                formal="isinstance(result, list)",
                                confidence=0.65,
                                source="loop_pattern",
                            ))
                            return specs
                    if isinstance(child, ast.AugAssign):
                        specs.append(InferredSpec(
                            kind="ensures",
                            description="result is accumulated value",
                            confidence=0.5,
                            source="loop_pattern",
                        ))
                        return specs
        return specs

    def confidence(self, spec: InferredSpec) -> float:
        """How confident are we in this inferred spec?"""
        return spec.confidence


# ═══════════════════════════════════════════════════════════════════
# §4  Trust Boundary
# ═══════════════════════════════════════════════════════════════════

class TrustBoundary:
    """Track trust boundaries in a call graph.

    A function's effective trust is min(own trust, callees' trust).
    Boundary crossings occur when a verified function calls an
    unverified one (or vice-versa).
    """

    def __init__(self) -> None:
        self._trust: dict[str, TrustLevel] = {}
        self._calls: dict[str, set[str]] = {}

    def set_trust(self, func: str, level: TrustLevel) -> None:
        """Set the trust level for a function."""
        self._trust[func] = level

    def add_call(self, caller: str, callee: str) -> None:
        """Record that *caller* calls *callee*."""
        self._calls.setdefault(caller, set()).add(callee)

    def propagate(self) -> dict[str, TrustLevel]:
        """Propagate trust: a function's trust is min(its own, its callees')."""
        effective: dict[str, TrustLevel] = dict(self._trust)
        # Fixed-point iteration (call graph is typically small)
        changed = True
        max_iters = len(self._trust) + 1
        for _ in range(max_iters):
            if not changed:
                break
            changed = False
            for func, callees in self._calls.items():
                own = effective.get(func, TrustLevel.UNTRUSTED)
                for callee in callees:
                    callee_trust = effective.get(callee, TrustLevel.UNTRUSTED)
                    if callee_trust.value < own.value:
                        effective[func] = TrustLevel(callee_trust.value)
                        changed = True
        return effective

    def boundary_crossings(self) -> list[tuple[str, str, TrustLevel, TrustLevel]]:
        """Find calls that cross trust boundaries.

        Uses the *declared* (not propagated) trust levels so that a verified
        function calling an unverified one is always flagged.
        """
        crossings: list[tuple[str, str, TrustLevel, TrustLevel]] = []
        for caller, callees in self._calls.items():
            caller_trust = self._trust.get(caller, TrustLevel.UNTRUSTED)
            for callee in sorted(callees):
                callee_trust = self._trust.get(callee, TrustLevel.UNTRUSTED)
                if caller_trust != callee_trust:
                    crossings.append((caller, callee, caller_trust, callee_trust))
        return crossings

    def visualize(self) -> str:
        """ASCII visualization of trust boundaries."""
        effective = self.propagate()
        if not effective:
            return "(empty call graph)"

        trust_icon = {
            TrustLevel.KERNEL: "🟢",
            TrustLevel.Z3_VERIFIED: "🟡",
            TrustLevel.STRUCTURAL_CHAIN: "🟠",
            TrustLevel.LLM_CHECKED: "🟠",
            TrustLevel.AXIOM_TRUSTED: "🔵",
            TrustLevel.EFFECT_ASSUMED: "⚪",
            TrustLevel.UNTRUSTED: "🔴",
        }

        lines: list[str] = ["Trust Boundary Map", "─" * 40]
        for func in sorted(effective):
            level = effective[func]
            icon = trust_icon.get(level, "?")
            callees = self._calls.get(func, set())
            if callees:
                targets = ", ".join(sorted(callees))
                lines.append(f"  {icon} {func} [{level.name}] → {targets}")
            else:
                lines.append(f"  {icon} {func} [{level.name}]")

        crossings = self.boundary_crossings()
        if crossings:
            lines.append("")
            lines.append("⚠ Boundary crossings:")
            for caller, callee, ct, et in crossings:
                lines.append(f"  {caller} [{ct.name}] → {callee} [{et.name}]")

        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# §5  Gradual Checker
# ═══════════════════════════════════════════════════════════════════

class GradualChecker:
    """Gradual verification: verify what you can, track the rest.

    Unlike all-or-nothing systems, the gradual checker:
    - Infers specs for un-annotated functions
    - Tracks unverifiable obligations as "skipped" rather than "failed"
    - Computes coverage metrics and trust scores
    - Builds a trust boundary across the call graph
    """

    def __init__(
        self,
        kernel: ProofKernel | None = None,
        *,
        min_trust: TrustLevel = TrustLevel.UNTRUSTED,
        timeout_per_obligation: float = 5.0,
        skip_expensive: bool = False,
    ) -> None:
        self._kernel = kernel or ProofKernel()
        self._min_trust = min_trust
        self._timeout = timeout_per_obligation
        self._skip_expensive = skip_expensive
        self._spec_extractor = SpecExtractor()
        self._obligation_gen = ObligationGenerator()
        self._spec_inferencer = SpecInferencer()
        self._strategy = CompositeStrategy([
            Z3Strategy(),
            StructuralStrategy(),
            AxiomStrategy(self._kernel),
        ])
        self._boundary = TrustBoundary()

    @property
    def trust_boundary(self) -> TrustBoundary:
        return self._boundary

    # -- single function ---------------------------------------------------

    def check_function(self, source: str, func_name: str) -> GradualResult:
        """Check a single function, tracking unverifiable obligations."""
        t0 = time.monotonic()

        # Extract explicit specs
        specs = self._spec_extractor.extract_from_source(source)
        func_spec: FunctionSpec | None = None
        for s in specs:
            if s.name == func_name:
                func_spec = s
                break

        has_spec = func_spec is not None and bool(
            func_spec.guarantees or func_spec.assumptions or func_spec.checks
        )

        # Infer specs if none provided
        inferred: list[InferredSpec] = []
        if func_spec is None:
            # Build a minimal spec from return type annotation
            func_spec = FunctionSpec(
                name=func_name,
                params=[],
                return_type=PyObjType(),
            )
            has_spec = False
        if not has_spec:
            inferred = self._spec_inferencer.infer(source, func_name)

        # Generate proof obligations
        obligations_raw = self._obligation_gen.generate(func_spec)
        # Also add inferred specs as obligations
        for ispec in inferred:
            if ispec.formal:
                obligations_raw.append((
                    f"Inferred: {ispec.description}",
                    Judgment(
                        kind=JudgmentKind.TYPE_CHECK,
                        context=Context(),
                        term=Var(func_name),
                        type_=RefinementType(
                            base_type=PyObjType(),
                            predicate=ispec.formal,
                        ),
                    ),
                ))

        # Attempt to prove each obligation
        obligation_statuses: list[ObligationStatus] = []
        for desc, judgment in obligations_raw:
            status = self._check_obligation(desc, judgment)
            obligation_statuses.append(status)

        # Compute coverage
        proved = sum(1 for o in obligation_statuses if o.status == "proved")
        assumed = sum(1 for o in obligation_statuses if o.status == "assumed")
        failed = sum(1 for o in obligation_statuses if o.status == "failed")
        skipped = sum(
            1 for o in obligation_statuses
            if o.status in ("skipped", "timeout")
        )
        total = len(obligation_statuses)

        # Determine function category
        if has_spec and proved == total and total > 0:
            cat = "fully_verified"
        elif has_spec and proved > 0:
            cat = "partially_verified"
        elif has_spec:
            cat = "spec_only"
        else:
            cat = "unspecified"

        coverage = VerificationCoverage(
            total_functions=1,
            fully_verified=1 if cat == "fully_verified" else 0,
            partially_verified=1 if cat == "partially_verified" else 0,
            spec_only=1 if cat == "spec_only" else 0,
            unspecified=1 if cat == "unspecified" else 0,
            total_obligations=total,
            obligations_proved=proved,
            obligations_assumed=assumed,
            obligations_failed=failed,
            obligations_skipped=skipped,
        )

        # Trust level = min of successful proof trusts, or UNTRUSTED
        trust_levels = [o.trust for o in obligation_statuses if o.status == "proved"]
        if trust_levels:
            trust = TrustLevel(min(t.value for t in trust_levels))
        elif assumed > 0:
            trust = TrustLevel.AXIOM_TRUSTED
        else:
            trust = TrustLevel.UNTRUSTED

        self._boundary.set_trust(func_name, trust)

        elapsed = time.monotonic() - t0
        return GradualResult(
            function_name=func_name,
            obligations=obligation_statuses,
            coverage=coverage,
            trust_level=trust,
            time_taken=elapsed,
            has_spec=has_spec,
            inferred_specs=inferred,
        )

    def _check_obligation(
        self, description: str, judgment: Judgment,
    ) -> ObligationStatus:
        """Attempt to prove a single obligation; gracefully degrade."""
        if self._skip_expensive and self._looks_expensive(judgment):
            return ObligationStatus(
                description=description,
                status="skipped",
                trust=TrustLevel.UNTRUSTED,
                reason="skipped (expensive)",
            )

        t0 = time.monotonic()
        try:
            # Try composite strategy
            if isinstance(self._strategy, CompositeStrategy):
                proof, strategy_name = self._strategy.try_prove_with_info(
                    judgment, judgment.context,
                )
            else:
                proof = self._strategy.try_prove(judgment, judgment.context)
                strategy_name = self._strategy.name if proof else "none"

            elapsed = time.monotonic() - t0
            if elapsed > self._timeout:
                return ObligationStatus(
                    description=description,
                    status="timeout",
                    trust=TrustLevel.UNTRUSTED,
                    proof_term=proof,
                    reason=f"exceeded {self._timeout}s timeout",
                )

            if proof is not None:
                vr = self._kernel.verify(judgment.context, judgment, proof)
                if vr.success:
                    return ObligationStatus(
                        description=description,
                        status="proved",
                        trust=vr.trust_level,
                        proof_term=proof,
                        reason=strategy_name,
                    )
                else:
                    return ObligationStatus(
                        description=description,
                        status="failed",
                        trust=TrustLevel.UNTRUSTED,
                        proof_term=proof,
                        reason=f"kernel rejected: {vr.message}",
                    )

            # No strategy could prove it — mark as skipped (gradual)
            return ObligationStatus(
                description=description,
                status="skipped",
                trust=TrustLevel.UNTRUSTED,
                reason="no strategy could handle this obligation",
            )
        except Exception as exc:
            return ObligationStatus(
                description=description,
                status="failed",
                trust=TrustLevel.UNTRUSTED,
                reason=f"exception: {exc}",
            )

    @staticmethod
    def _looks_expensive(judgment: Judgment) -> bool:
        """Heuristic: is this obligation likely to be expensive?"""
        if judgment.type_ is not None and isinstance(judgment.type_, RefinementType):
            pred = judgment.type_.predicate
            if any(kw in pred for kw in ("forall", "exists", "∀", "∃", "sum(", "all(")):
                return True
        return False

    # -- module-level checking ---------------------------------------------

    def check_module(self, source: str, *, module_name: str = "<module>") -> ModuleGradualResult:
        """Check all functions in a module."""
        t0 = time.monotonic()
        try:
            tree = ast.parse(textwrap.dedent(source))
        except SyntaxError:
            return ModuleGradualResult(
                module_name=module_name,
                coverage=VerificationCoverage(total_functions=0),
                time_taken=time.monotonic() - t0,
            )

        func_names = [
            node.name for node in ast.walk(tree)
            if isinstance(node, ast.FunctionDef)
        ]

        # Collect call graph from AST
        self._extract_call_graph(tree)

        results: list[GradualResult] = []
        for fn in func_names:
            r = self.check_function(source, fn)
            results.append(r)

        # Aggregate coverage
        agg = VerificationCoverage()
        for r in results:
            agg = agg.merge(r.coverage)

        elapsed = time.monotonic() - t0
        return ModuleGradualResult(
            module_name=module_name,
            functions=results,
            coverage=agg,
            time_taken=elapsed,
        )

    def _extract_call_graph(self, tree: ast.AST) -> None:
        """Extract caller→callee edges from AST."""
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                caller = node.name
                for child in ast.walk(node):
                    if isinstance(child, ast.Call):
                        callee_name = _call_name(child)
                        if callee_name and callee_name != caller:
                            self._boundary.add_call(caller, callee_name)

    # -- directory-level checking ------------------------------------------

    def check_directory(
        self,
        path: str,
        *,
        pattern: str = "**/*.py",
        project_name: str | None = None,
    ) -> ProjectGradualResult:
        """Check an entire project directory."""
        import glob as glob_mod

        t0 = time.monotonic()
        if project_name is None:
            project_name = os.path.basename(os.path.abspath(path))

        py_files = sorted(glob_mod.glob(os.path.join(path, pattern), recursive=True))
        modules: list[ModuleGradualResult] = []
        for fpath in py_files:
            try:
                with open(fpath, encoding="utf-8", errors="replace") as f:
                    source = f.read()
            except OSError:
                continue

            rel = os.path.relpath(fpath, path)
            mod_result = self.check_module(source, module_name=rel)
            if mod_result.coverage.total_functions > 0:
                modules.append(mod_result)

        agg = VerificationCoverage()
        for m in modules:
            agg = agg.merge(m.coverage)

        elapsed = time.monotonic() - t0
        return ProjectGradualResult(
            project_name=project_name,
            modules=modules,
            coverage=agg,
            time_taken=elapsed,
        )


# ═══════════════════════════════════════════════════════════════════
# §6  Gradual Report
# ═══════════════════════════════════════════════════════════════════

class GradualReport:
    """Generate comprehensive verification reports."""

    @staticmethod
    def ascii_coverage(result: ProjectGradualResult) -> str:
        """Full ASCII coverage report with box-drawing characters."""
        c = result.coverage
        W = 48

        lines: list[str] = []
        lines.append("╔" + "═" * W + "╗")
        lines.append("║" + "  SynHoPy Gradual Verification Report".ljust(W) + "║")
        lines.append("╠" + "═" * W + "╣")

        header = f" {'File':<20s} {'Coverage':>10s}  {'Trust':>6s}  {'Status':<8s} "
        lines.append("║" + header.ljust(W) + "║")
        lines.append("║" + " " + "─" * (W - 2) + " " + "║")

        for mod in result.modules:
            name = mod.module_name
            if len(name) > 20:
                name = "…" + name[-19:]
            pct = mod.coverage.coverage_pct
            trust_pct = mod.coverage.trust_score
            bar_w = 10
            filled = round(pct / 100.0 * bar_w)
            filled = max(0, min(bar_w, filled))
            bar = "■" * filled + "□" * (bar_w - filled)

            # Status label
            if pct >= 100:
                status = "FULL"
            elif pct > 0:
                status = "PARTIAL"
            elif mod.coverage.spec_only > 0:
                status = "SPEC"
            else:
                status = "UNSPEC"

            row = f" {name:<20s} {bar} {pct:3.0f}%  {trust_pct:5.1f}%  {status:<8s} "
            lines.append("║" + row.ljust(W) + "║")

        lines.append("╠" + "═" * W + "╣")
        total_line = (
            f" Total: {c.coverage_pct:.0f}% verified "
            f"({c.obligations_proved}/{c.total_obligations} obligations)"
        )
        lines.append("║" + total_line.ljust(W) + "║")
        trust_line = (
            f" Trust: {c.trust_score:.0f}% "
            f"({c.obligations_proved + c.obligations_assumed}"
            f"/{c.total_obligations} proved or assumed)"
        )
        lines.append("║" + trust_line.ljust(W) + "║")
        lines.append("╚" + "═" * W + "╝")
        return "\n".join(lines)

    @staticmethod
    def json_coverage(result: ProjectGradualResult) -> dict:
        """Machine-readable coverage for CI integration."""
        return result.to_json()

    @staticmethod
    def ci_gate(
        result: ProjectGradualResult,
        *,
        min_coverage: float = 0.0,
        min_trust: float = 0.0,
        no_regressions: ProjectGradualResult | None = None,
    ) -> bool:
        """CI gate: pass/fail based on coverage thresholds.

        Parameters
        ----------
        min_coverage : float
            Minimum coverage percentage (0-100) to pass.
        min_trust : float
            Minimum trust score (0-100) to pass.
        no_regressions : ProjectGradualResult | None
            If provided, coverage must not decrease compared to this baseline.
        """
        if result.coverage.coverage_pct < min_coverage:
            return False
        if result.coverage.trust_score < min_trust:
            return False
        if no_regressions is not None:
            if result.coverage.coverage_pct < no_regressions.coverage.coverage_pct:
                return False
            if result.coverage.trust_score < no_regressions.coverage.trust_score:
                return False
        return True


# ═══════════════════════════════════════════════════════════════════
# §7  AST helpers (private)
# ═══════════════════════════════════════════════════════════════════

def _annotation_to_str(node: ast.expr | None) -> str:
    """Convert an annotation AST node to a readable string."""
    if node is None:
        return ""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Constant):
        return str(node.value)
    if isinstance(node, ast.Attribute):
        val = _annotation_to_str(node.value)
        return f"{val}.{node.attr}" if val else node.attr
    if isinstance(node, ast.Subscript):
        base = _annotation_to_str(node.value)
        sl = _annotation_to_str(node.slice)
        return f"{base}[{sl}]"
    return _unparse_safe(node)


def _unparse_safe(node: ast.AST) -> str:
    """Safely unparse an AST node (Python 3.9+)."""
    try:
        return ast.unparse(node)
    except Exception:
        return ""


def _body_is_raise(node: ast.If) -> bool:
    """Check if the if-body is a single raise statement."""
    body = node.body
    if len(body) == 1 and isinstance(body[0], ast.Raise):
        return True
    if (len(body) == 1 and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Call)):
        return False
    return False


def _negate_simple(expr: str) -> str:
    """Simple negation of a comparison expression."""
    negations = {
        " is None": " is not None",
        " is not None": " is None",
        " == ": " != ",
        " != ": " == ",
        " < ": " >= ",
        " > ": " <= ",
        " <= ": " > ",
        " >= ": " < ",
    }
    for old, new in negations.items():
        if old in expr:
            return expr.replace(old, new, 1)
    return f"not ({expr})"


def _function_body(node: ast.FunctionDef) -> list[ast.stmt]:
    """Get the function body, skipping docstring."""
    body = node.body
    if (body and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        return body[1:]
    return body


def _call_name(node: ast.Call) -> str | None:
    """Extract the callee name from a Call node, or None."""
    func = node.func
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        return func.attr
    return None


# ═══════════════════════════════════════════════════════════════════
# §8  Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:  # noqa: C901 — intentionally dense test battery
    """Run comprehensive self-tests for the gradual verification engine."""
    passed = 0

    # --- VerificationCoverage ---
    # 1. empty coverage
    vc = VerificationCoverage()
    assert vc.coverage_pct == 0.0, f"empty coverage_pct: {vc.coverage_pct}"
    passed += 1

    # 2. zero-function, zero-obligation coverage → 0 %
    vc0 = VerificationCoverage(total_functions=0, total_obligations=0)
    assert vc0.coverage_pct == 0.0
    assert vc0.trust_score == 0.0
    passed += 1

    # 3. all proved
    vc1 = VerificationCoverage(
        total_functions=2, fully_verified=2,
        total_obligations=4, obligations_proved=4,
    )
    assert vc1.coverage_pct == 100.0
    assert vc1.trust_score == 100.0
    passed += 1

    # 4. half proved, half failed
    vc2 = VerificationCoverage(
        total_functions=2, fully_verified=1, partially_verified=1,
        total_obligations=4, obligations_proved=2, obligations_failed=2,
    )
    assert vc2.coverage_pct == 50.0
    assert vc2.trust_score == 50.0
    passed += 1

    # 5. coverage badge
    badge = vc2.coverage_badge()
    assert "■" in badge and "□" in badge and "50%" in badge, badge
    passed += 1

    # 6. coverage summary
    summary = vc2.summary()
    assert "50.0%" in summary
    passed += 1

    # 7. merge
    merged = vc1.merge(vc2)
    assert merged.total_functions == 4
    assert merged.obligations_proved == 6
    assert merged.total_obligations == 8
    passed += 1

    # 8. trust score with assumed
    vc3 = VerificationCoverage(
        total_functions=1, total_obligations=10,
        obligations_proved=5, obligations_assumed=5,
    )
    expected_trust = (5 * 1.0 + 5 * 0.6) / 10 * 100
    assert abs(vc3.trust_score - expected_trust) < 0.01, vc3.trust_score
    passed += 1

    # 9. badge at 0%
    vc_zero = VerificationCoverage(
        total_functions=1, total_obligations=5, obligations_failed=5,
    )
    assert "0%" in vc_zero.coverage_badge()
    passed += 1

    # 10. badge at 100%
    vc_full = VerificationCoverage(
        total_functions=1, fully_verified=1,
        total_obligations=3, obligations_proved=3,
    )
    assert "100%" in vc_full.coverage_badge()
    passed += 1

    # --- ObligationStatus ---
    # 11. repr
    os1 = ObligationStatus("test", "proved", TrustLevel.KERNEL)
    assert "✓" in repr(os1)
    passed += 1

    # 12. failed repr
    os2 = ObligationStatus("test", "failed", TrustLevel.UNTRUSTED, reason="bad")
    assert "✗" in repr(os2)
    passed += 1

    # 13. skipped repr
    os3 = ObligationStatus("test", "skipped", TrustLevel.UNTRUSTED)
    assert "⊘" in repr(os3)
    passed += 1

    # --- SpecInferencer ---
    inferencer = SpecInferencer()

    # 14. return type inference
    src14 = "def add(x: int, y: int) -> int:\n    return x + y\n"
    specs14 = inferencer.infer(src14, "add")
    assert any(s.kind == "ensures" and "int" in s.description for s in specs14), specs14
    passed += 1

    # 15. guard clause inference
    src15 = textwrap.dedent("""\
        def divide(x: int, y: int) -> float:
            if y == 0:
                raise ValueError("division by zero")
            return x / y
    """)
    specs15 = inferencer.infer(src15, "divide")
    assert any(s.kind == "requires" for s in specs15), specs15
    passed += 1

    # 16. assert inference
    src16 = "def foo(x: int) -> int:\n    assert x > 0\n    return x\n"
    specs16 = inferencer.infer(src16, "foo")
    assert any(s.kind == "ensures" and "assert" in s.source for s in specs16), specs16
    passed += 1

    # 17. docstring raises
    src17 = textwrap.dedent('''\
        def bar(x: int) -> int:
            """Do something.

            Raises:
                ValueError: if x is negative
            """
            return x
    ''')
    specs17 = inferencer.infer(src17, "bar")
    assert any(s.kind == "exception" for s in specs17), specs17
    passed += 1

    # 18. purity inference
    src18 = "def pure_fn(x: int) -> int:\n    return x * 2\n"
    specs18 = inferencer.infer(src18, "pure_fn")
    assert any(s.kind == "pure" for s in specs18), specs18
    passed += 1

    # 19. infer_all
    src19 = textwrap.dedent("""\
        def f1(x: int) -> int:
            return x
        def f2(x: str) -> str:
            return x
    """)
    all19 = inferencer.infer_all(src19)
    assert "f1" in all19 and "f2" in all19
    passed += 1

    # 20. confidence accessor
    ispec = InferredSpec("ensures", "test", confidence=0.8)
    assert inferencer.confidence(ispec) == 0.8
    passed += 1

    # --- TrustBoundary ---
    tb = TrustBoundary()

    # 21. set and propagate
    tb.set_trust("a", TrustLevel.Z3_VERIFIED)
    tb.set_trust("b", TrustLevel.UNTRUSTED)
    tb.add_call("a", "b")
    eff = tb.propagate()
    assert eff["a"] == TrustLevel.UNTRUSTED, eff["a"]
    passed += 1

    # 22. boundary crossings
    tb2 = TrustBoundary()
    tb2.set_trust("verified_fn", TrustLevel.KERNEL)
    tb2.set_trust("unverified_fn", TrustLevel.UNTRUSTED)
    tb2.add_call("verified_fn", "unverified_fn")
    crossings = tb2.boundary_crossings()
    assert len(crossings) >= 1
    passed += 1

    # 23. visualize
    viz = tb2.visualize()
    assert "verified_fn" in viz
    assert "Boundary" in viz
    passed += 1

    # 24. empty boundary
    tb_empty = TrustBoundary()
    assert "empty" in tb_empty.visualize()
    passed += 1

    # 25. no crossing when same trust
    tb3 = TrustBoundary()
    tb3.set_trust("x", TrustLevel.KERNEL)
    tb3.set_trust("y", TrustLevel.KERNEL)
    tb3.add_call("x", "y")
    assert len(tb3.boundary_crossings()) == 0
    passed += 1

    # --- GradualChecker ---
    checker = GradualChecker()

    # 26. check a simple annotated function
    src26 = textwrap.dedent("""\
        def add(x: int, y: int) -> int:
            return x + y
    """)
    r26 = checker.check_function(src26, "add")
    assert r26.function_name == "add"
    assert r26.coverage.total_obligations >= 1
    passed += 1

    # 27. check function with guarantee
    src27 = textwrap.dedent("""\
        @guarantee("result >= 0")
        def abs_val(x: int) -> int:
            if x >= 0:
                return x
            return -x
    """)
    r27 = checker.check_function(src27, "abs_val")
    assert r27.function_name == "abs_val"
    assert r27.has_spec is True
    passed += 1

    # 28. check function with no specs
    src28 = "def noop():\n    pass\n"
    r28 = checker.check_function(src28, "noop")
    assert r28.has_spec is False
    passed += 1

    # 29. time_taken is positive
    assert r26.time_taken >= 0
    passed += 1

    # 30. check_module
    src30 = textwrap.dedent("""\
        def f(x: int) -> int:
            return x
        def g(y: str) -> str:
            return y
    """)
    mod30 = checker.check_module(src30, module_name="test_mod")
    assert mod30.module_name == "test_mod"
    assert len(mod30.functions) == 2
    assert mod30.coverage.total_functions == 2
    passed += 1

    # 31. module report
    report30 = mod30.report()
    assert "test_mod" in report30
    passed += 1

    # 32. check_module with syntax error
    mod32 = checker.check_module("def broken(", module_name="bad")
    assert mod32.coverage.total_functions == 0
    passed += 1

    # 33. ProjectGradualResult.to_json round-trip
    proj = ProjectGradualResult(
        project_name="test_proj",
        modules=[mod30],
        coverage=mod30.coverage,
        time_taken=0.01,
    )
    j = proj.to_json()
    assert j["project"] == "test_proj"
    assert "obligations" in j
    assert "modules" in j
    assert isinstance(j["modules"], list)
    passed += 1

    # 34. ProjectGradualResult.report
    pr = proj.report()
    assert "test_proj" in pr
    passed += 1

    # 35. ProjectGradualResult.heatmap
    hm = proj.heatmap()
    assert "test_mod" in hm
    passed += 1

    # 36. heatmap empty
    empty_proj = ProjectGradualResult(project_name="empty")
    assert "no modules" in empty_proj.heatmap()
    passed += 1

    # --- GradualReport ---
    # 37. ascii_coverage
    ascii_rep = GradualReport.ascii_coverage(proj)
    assert "SynHoPy" in ascii_rep
    assert "╔" in ascii_rep
    passed += 1

    # 38. json_coverage
    jc = GradualReport.json_coverage(proj)
    assert "coverage_pct" in jc
    passed += 1

    # 39. ci_gate passes when thresholds are 0
    assert GradualReport.ci_gate(proj, min_coverage=0.0, min_trust=0.0) is True
    passed += 1

    # 40. ci_gate fails when threshold is too high
    assert GradualReport.ci_gate(proj, min_coverage=99999.0) is False
    passed += 1

    # 41. ci_gate no-regression check
    worse = ProjectGradualResult(
        project_name="worse",
        coverage=VerificationCoverage(
            total_functions=1, total_obligations=10,
            obligations_proved=1, obligations_failed=9,
        ),
    )
    # worse has lower coverage than proj — should fail regression gate
    assert GradualReport.ci_gate(worse, no_regressions=proj) is False
    passed += 1

    # 42. skip_expensive flag
    checker_skip = GradualChecker(skip_expensive=True)
    src42 = textwrap.dedent("""\
        @guarantee("forall x in xs: x > 0")
        def check_pos(xs: list) -> bool:
            return all(x > 0 for x in xs)
    """)
    r42 = checker_skip.check_function(src42, "check_pos")
    # Should have at least one skipped obligation
    has_skipped = any(o.status == "skipped" for o in r42.obligations)
    assert has_skipped, [o.status for o in r42.obligations]
    passed += 1

    # 43. InferredSpec repr
    ispec43 = InferredSpec("ensures", "test thing", confidence=0.5)
    r43 = repr(ispec43)
    assert "50%" in r43, r43
    passed += 1

    # 44. GradualResult repr
    r44_repr = repr(r26)
    assert "add" in r44_repr
    passed += 1

    # 45. loop accumulator inference
    src45 = textwrap.dedent("""\
        def collect(items):
            result = []
            for item in items:
                result.append(item * 2)
            return result
    """)
    specs45 = inferencer.infer(src45, "collect")
    assert any("list" in s.description.lower() or "accumul" in s.description.lower()
               for s in specs45), specs45
    passed += 1

    # 46. trust boundary propagation chain
    tb4 = TrustBoundary()
    tb4.set_trust("top", TrustLevel.KERNEL)
    tb4.set_trust("mid", TrustLevel.Z3_VERIFIED)
    tb4.set_trust("bot", TrustLevel.UNTRUSTED)
    tb4.add_call("top", "mid")
    tb4.add_call("mid", "bot")
    eff4 = tb4.propagate()
    assert eff4["top"] == TrustLevel.UNTRUSTED
    assert eff4["mid"] == TrustLevel.UNTRUSTED
    passed += 1

    # 47. checker.trust_boundary accessible
    assert isinstance(checker.trust_boundary, TrustBoundary)
    passed += 1

    # 48. ObligationStatus timeout
    os_timeout = ObligationStatus("slow", "timeout", TrustLevel.UNTRUSTED)
    assert "⏱" in repr(os_timeout)
    passed += 1

    print(f"\n✓ All {passed} gradual verification self-tests passed.")


if __name__ == "__main__":
    _self_test()
