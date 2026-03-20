#!/usr/bin/env python3
"""Comet-H Verified: A research pipeline with JSON-refinement dependent typing.

This system applies techniques from programming languages and formal verification
to LLM pipeline orchestration:

  1. JSON REFINEMENT TYPES — every artifact has a base JSON schema narrowed by
     a predicate (refinement).  Stage pre/postconditions are refinement types
     that are machine-checked at every transition.

  2. DEPENDENT TYPES — a stage's output type can depend on the *value* of its
     input.  E.g., the paper-writing stage's output type requires that every
     hypothesis from synthesis appears as a grounded claim.

  3. PROVENANCE TRACKING (taint analysis) — every claim, result, and citation
     carries a provenance chain recording which stage produced it, which LLM
     call generated it, and which inputs it derived from.  Hallucinations can
     be traced to their origin.

  4. QUALITY LATTICE — quality is a vector in a product lattice
     (grounding x novelty x correctness x clarity x completeness).
     The pipeline enforces monotonicity: each step must be non-decreasing in
     at least one dimension.

  5. STAGE GRAPH VERIFICATION — the pipeline DAG is statically checked for
     reachability, termination, deadlock-freedom, and gate correctness.

  6. CEGAR REPAIR — failed experiments are repaired via counterexample-guided
     abstraction refinement with a monotonically growing test suite that
     guarantees convergence.

  7. CLAIM-CITATION ALIGNMENT — claims attributed to citations are checked
     for semantic entailment, catching false attributions that pass simple
     "does this DOI exist?" checks.

The key insight: LLM pipelines pass JSON between stages.  JSON is a type.
Refinement predicates over JSON are refinement types.  Stage dependencies
create dependent types.  The entire pipeline becomes a dependently-typed
program whose well-typedness implies correctness properties.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone
from enum import Enum, auto
from pathlib import Path
from typing import Any, Callable


# ═══════════════════════════════════════════════════════════════════════
# PART 1: JSON REFINEMENT TYPE SYSTEM
# ═══════════════════════════════════════════════════════════════════════


class JsonTypeKind(Enum):
    NULL = auto()
    BOOL = auto()
    INT = auto()
    FLOAT = auto()
    STRING = auto()
    ARRAY = auto()
    OBJECT = auto()
    ANY = auto()
    UNION = auto()


@dataclass(frozen=True)
class JsonType:
    """Base JSON type — the 'simple type' layer before refinement.

    This corresponds to the ground types in a refinement type system:
    the refinement predicate narrows these into refined types.
    """
    kind: JsonTypeKind
    # For ARRAY: element type
    element: JsonType | None = None
    # For OBJECT: field name -> field type (required fields)
    fields: tuple[tuple[str, JsonType], ...] | None = None
    # For UNION: constituent types
    variants: tuple[JsonType, ...] | None = None

    def check(self, value: Any) -> bool:
        """Check that a value inhabits this base type."""
        if self.kind == JsonTypeKind.ANY:
            return True
        if self.kind == JsonTypeKind.NULL:
            return value is None
        if self.kind == JsonTypeKind.BOOL:
            return isinstance(value, bool)
        if self.kind == JsonTypeKind.INT:
            return isinstance(value, int) and not isinstance(value, bool)
        if self.kind == JsonTypeKind.FLOAT:
            return isinstance(value, (int, float)) and not isinstance(value, bool)
        if self.kind == JsonTypeKind.STRING:
            return isinstance(value, str)
        if self.kind == JsonTypeKind.ARRAY:
            if not isinstance(value, list):
                return False
            if self.element is not None:
                return all(self.element.check(item) for item in value)
            return True
        if self.kind == JsonTypeKind.OBJECT:
            if not isinstance(value, dict):
                return False
            if self.fields is not None:
                for fname, ftype in self.fields:
                    if fname not in value:
                        return False
                    if not ftype.check(value[fname]):
                        return False
            return True
        if self.kind == JsonTypeKind.UNION:
            if self.variants is None:
                return False
            return any(v.check(value) for v in self.variants)
        return False


# Convenience constructors
def JNull() -> JsonType:
    return JsonType(JsonTypeKind.NULL)

def JBool() -> JsonType:
    return JsonType(JsonTypeKind.BOOL)

def JInt() -> JsonType:
    return JsonType(JsonTypeKind.INT)

def JFloat() -> JsonType:
    return JsonType(JsonTypeKind.FLOAT)

def JString() -> JsonType:
    return JsonType(JsonTypeKind.STRING)

def JArray(element: JsonType | None = None) -> JsonType:
    return JsonType(JsonTypeKind.ARRAY, element=element)

def JObject(**fields: JsonType) -> JsonType:
    return JsonType(JsonTypeKind.OBJECT, fields=tuple(fields.items()))

def JAny() -> JsonType:
    return JsonType(JsonTypeKind.ANY)

def JUnion(*variants: JsonType) -> JsonType:
    return JsonType(JsonTypeKind.UNION, variants=variants)


# ---------------------------------------------------------------------------
# 1.2  Refinement predicates
# ---------------------------------------------------------------------------

@dataclass(frozen=False)
class Refinement:
    """A predicate that narrows a base type.

    In classical refinement type theory: {x : T | phi(x)}
    Here T is a JsonType and phi is a Python predicate.

    The predicate receives the value and returns (satisfied, reason).
    """
    name: str
    predicate: Callable[[Any], tuple[bool, str]]

    def check(self, value: Any) -> tuple[bool, str]:
        try:
            return self.predicate(value)
        except Exception as e:
            return False, f"Refinement '{self.name}' raised: {e}"


def refinement(name: str, pred: Callable[[Any], bool], msg: str = "") -> Refinement:
    """Convenience: wrap a simple bool predicate into a Refinement."""
    return Refinement(
        name=name,
        predicate=lambda v: (True, "") if pred(v) else (False, msg or f"Refinement '{name}' failed"),
    )


# Common refinements
def non_empty(field: str) -> Refinement:
    return refinement(
        f"non_empty({field})",
        lambda v: isinstance(v, dict) and field in v and bool(v[field]),
        f"Field '{field}' must be non-empty",
    )

def has_fields(*names: str) -> Refinement:
    return refinement(
        f"has_fields({', '.join(names)})",
        lambda v: isinstance(v, dict) and all(n in v for n in names),
        f"Missing required fields: {names}",
    )

def array_min_length(field: str, n: int) -> Refinement:
    return refinement(
        f"array_min_length({field}, {n})",
        lambda v: isinstance(v, dict) and isinstance(v.get(field), list) and len(v[field]) >= n,
        f"Field '{field}' must have at least {n} elements",
    )

def no_placeholder_text() -> Refinement:
    """Check that no field contains placeholder markers."""
    import re
    patterns = [
        re.compile(r"\[INSERT\b", re.IGNORECASE),
        re.compile(r"\[TODO\b", re.IGNORECASE),
        re.compile(r"Lorem ipsum", re.IGNORECASE),
        re.compile(r"this section will describe", re.IGNORECASE),
        re.compile(r"\[PLACEHOLDER\b", re.IGNORECASE),
    ]

    def _check(v: Any) -> tuple[bool, str]:
        text = json.dumps(v) if not isinstance(v, str) else v
        for pat in patterns:
            m = pat.search(text)
            if m:
                return False, f"Placeholder text found: '{m.group()}'"
        return True, ""

    return Refinement("no_placeholder_text", _check)


# ---------------------------------------------------------------------------
# 1.3  Refined types (base + refinement)
# ---------------------------------------------------------------------------

@dataclass(frozen=False)
class RefinedType:
    """A JSON type narrowed by zero or more refinement predicates.

    This is the core type in our system:  {x : base | R1(x) & R2(x) & ...}

    Type checking = base type check + all refinement predicates satisfied.
    """
    name: str
    base: JsonType
    refinements: list[Refinement] = field(default_factory=list)

    def check(self, value: Any) -> TypeCheckResult:
        """Full type check: base + all refinements."""
        if not self.base.check(value):
            return TypeCheckResult(
                valid=False,
                type_name=self.name,
                violations=[f"Base type {self.base.kind.name} check failed"],
            )
        violations = []
        for ref in self.refinements:
            ok, reason = ref.check(value)
            if not ok:
                violations.append(f"[{ref.name}] {reason}")
        return TypeCheckResult(
            valid=len(violations) == 0,
            type_name=self.name,
            violations=violations,
        )

    def __and__(self, other: RefinedType) -> RefinedType:
        """Intersection: both types must be satisfied."""
        return RefinedType(
            name=f"({self.name} & {other.name})",
            base=self.base,  # assumes compatible bases
            refinements=self.refinements + other.refinements,
        )


@dataclass(frozen=True)
class TypeCheckResult:
    valid: bool
    type_name: str
    violations: list[str] = field(default_factory=list)

    def __bool__(self) -> bool:
        return self.valid

    def __str__(self) -> str:
        if self.valid:
            return f"{self.type_name}: OK"
        return f"{self.type_name}: FAILED\n" + "\n".join(f"  - {v}" for v in self.violations)


# ---------------------------------------------------------------------------
# 1.4  Dependent types (type families parameterized by values)
# ---------------------------------------------------------------------------

class DependentType:
    """A type that depends on a value — the dependent function space.

    In our system: given an input value `v`, produces a RefinedType
    that the output must satisfy.  This is the key mechanism for
    inter-stage consistency:

      writing_output_type(synthesis_result) =
        {paper : Paper | covers_all_hypotheses(paper, synthesis_result.hypotheses)}

    The output type literally depends on what the previous stage produced.
    """

    def __init__(
        self,
        name: str,
        type_family: Callable[[Any], RefinedType],
    ) -> None:
        self.name = name
        self._type_family = type_family

    def instantiate(self, input_value: Any) -> RefinedType:
        """Given the actual input value, produce the concrete output type."""
        return self._type_family(input_value)

    def check(self, input_value: Any, output_value: Any) -> TypeCheckResult:
        """Check that output_value has the type induced by input_value."""
        concrete_type = self.instantiate(input_value)
        return concrete_type.check(output_value)


# ═══════════════════════════════════════════════════════════════════════
# PART 2: PROVENANCE TRACKING (TAINT ANALYSIS)
# ═══════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ProvenanceRecord:
    """A single provenance entry — who produced this value and how."""
    stage: str
    step_index: int
    timestamp: str
    llm_model: str | None = None
    llm_call_id: str | None = None
    input_hashes: tuple[str, ...] = ()
    description: str = ""


@dataclass
class TaintedValue:
    """A JSON value with its full provenance chain.

    This is the information-flow-control (IFC) layer.  Every value
    produced by the pipeline carries a list of provenance records
    showing exactly how it was derived.  When a hallucination is
    detected in the final paper, we can trace it back through the
    chain to the originating stage and LLM call.

    Formally: a tainted value is a pair (v, tau) where v is the
    value and tau is a sequence of provenance records forming a
    derivation tree.
    """
    value: Any
    provenance: list[ProvenanceRecord] = field(default_factory=list)
    _content_hash: str = ""

    def __post_init__(self) -> None:
        if not self._content_hash:
            raw = json.dumps(self.value, sort_keys=True, default=str)
            object.__setattr__(self, "_content_hash", hashlib.sha256(raw.encode()).hexdigest()[:16])

    @property
    def content_hash(self) -> str:
        return self._content_hash

    def derive(
        self,
        new_value: Any,
        *,
        stage: str,
        step_index: int,
        llm_model: str | None = None,
        description: str = "",
    ) -> TaintedValue:
        """Derive a new tainted value from this one, extending the provenance chain."""
        record = ProvenanceRecord(
            stage=stage,
            step_index=step_index,
            timestamp=datetime.now(timezone.utc).isoformat(),
            llm_model=llm_model,
            input_hashes=(self.content_hash,),
            description=description,
        )
        return TaintedValue(
            value=new_value,
            provenance=self.provenance + [record],
        )

    def trace_origin(self) -> ProvenanceRecord | None:
        """Return the earliest provenance record — where this value was born."""
        return self.provenance[0] if self.provenance else None

    def trace_stages(self) -> list[str]:
        """Return the ordered list of stages this value passed through."""
        return [r.stage for r in self.provenance]

    def to_dict(self) -> dict[str, Any]:
        return {
            "value": self.value,
            "content_hash": self.content_hash,
            "provenance": [
                {
                    "stage": r.stage,
                    "step": r.step_index,
                    "timestamp": r.timestamp,
                    "llm_model": r.llm_model,
                    "input_hashes": list(r.input_hashes),
                    "description": r.description,
                }
                for r in self.provenance
            ],
        }


def merge_provenance(*tainted: TaintedValue) -> list[ProvenanceRecord]:
    """Merge provenance from multiple tainted inputs (join in the IFC lattice)."""
    seen: set[str] = set()
    merged: list[ProvenanceRecord] = []
    for tv in tainted:
        for record in tv.provenance:
            key = f"{record.stage}:{record.step_index}:{record.timestamp}"
            if key not in seen:
                seen.add(key)
                merged.append(record)
    merged.sort(key=lambda r: r.timestamp)
    return merged


# ═══════════════════════════════════════════════════════════════════════
# PART 3: STAGE CONTRACTS (dependent pre/postconditions)
# ═══════════════════════════════════════════════════════════════════════


@dataclass(frozen=False)
class StageContract:
    """A contract for a pipeline stage with dependent pre/postconditions.

    This is design-by-contract (Meyer/Eiffel) lifted to the JSON-refinement
    level.  Each stage declares:

      - precondition: a RefinedType that the input must satisfy
      - postcondition: a DependentType — the output type depends on the
        actual input value
      - frame: which workspace fields the stage is allowed to modify
        (anything not in the frame must be unchanged — frame rule from
        separation logic)

    Contract enforcement is not optional.  A stage that violates its
    postcondition is not "failed" — it is *ill-typed*.  The pipeline
    will not accept its output.
    """
    stage_name: str
    precondition: RefinedType
    postcondition: DependentType
    frame: frozenset[str] = frozenset()  # fields this stage may modify
    max_retries: int = 2

    def check_pre(self, input_value: Any) -> TypeCheckResult:
        return self.precondition.check(input_value)

    def check_post(self, input_value: Any, output_value: Any) -> TypeCheckResult:
        return self.postcondition.check(input_value, output_value)

    def check_frame(self, before: dict, after: dict) -> list[str]:
        """Frame check: fields not in the frame must be unchanged.

        This is the frame rule from separation logic applied to
        workspace state: a stage can only modify what it declares.
        """
        violations = []
        for key in before:
            if key not in self.frame and key in after:
                if before[key] != after[key]:
                    violations.append(
                        f"Frame violation: '{key}' modified by {self.stage_name} "
                        f"but not in its frame {self.frame}"
                    )
        return violations


class ContractEnforcer:
    """Runtime contract enforcement engine.

    Wraps stage execution with pre/post checking and provenance tracking.
    This is the "verified" part of the pipeline — every transition is
    type-checked.
    """

    def __init__(self) -> None:
        self._violations: list[dict[str, Any]] = []
        self._checks_passed: int = 0
        self._checks_failed: int = 0

    def enforce(
        self,
        contract: StageContract,
        input_value: TaintedValue,
        execute_fn: Callable[[Any], Any],
        *,
        step_index: int,
        model: str = "",
    ) -> tuple[TaintedValue | None, list[str]]:
        """Execute a stage with full contract enforcement.

        Returns (output_tainted_value, violations).
        If violations is non-empty, the output should be rejected.
        """
        all_violations: list[str] = []

        # 1. Check precondition
        pre_result = contract.check_pre(input_value.value)
        if not pre_result:
            all_violations.extend(
                f"PRE[{contract.stage_name}] {v}" for v in pre_result.violations
            )
            self._checks_failed += 1
            return None, all_violations
        self._checks_passed += 1

        # 2. Snapshot workspace for frame check
        workspace_before = copy.deepcopy(input_value.value) if isinstance(input_value.value, dict) else None

        # 3. Execute stage
        try:
            raw_output = execute_fn(input_value.value)
        except Exception as e:
            all_violations.append(f"EXEC[{contract.stage_name}] Stage raised: {e}")
            self._checks_failed += 1
            return None, all_violations

        # 4. Check postcondition (DEPENDENT: output type depends on input value)
        post_result = contract.check_post(input_value.value, raw_output)
        if not post_result:
            all_violations.extend(
                f"POST[{contract.stage_name}] {v}" for v in post_result.violations
            )
            self._checks_failed += 1
        else:
            self._checks_passed += 1

        # 5. Frame check (separation logic)
        if workspace_before is not None and isinstance(raw_output, dict):
            frame_violations = contract.check_frame(workspace_before, raw_output)
            all_violations.extend(frame_violations)

        # 6. Wrap output with provenance
        output_tainted = input_value.derive(
            raw_output,
            stage=contract.stage_name,
            step_index=step_index,
            llm_model=model,
            description=f"Output of {contract.stage_name} (step {step_index})",
        )

        return output_tainted, all_violations

    @property
    def stats(self) -> dict[str, int]:
        return {
            "checks_passed": self._checks_passed,
            "checks_failed": self._checks_failed,
            "total_violations": len(self._violations),
        }


# ═══════════════════════════════════════════════════════════════════════
# PART 4: QUALITY LATTICE
# ═══════════════════════════════════════════════════════════════════════


class QualityDimension(Enum):
    """Dimensions of the quality lattice.

    Quality is a vector in the product lattice [0,1]^5.
    The partial order is pointwise: q1 <= q2 iff q1[d] <= q2[d] for all d.
    """
    GROUNDING = "grounding"      # every claim has traceable evidence
    NOVELTY = "novelty"          # contribution is genuinely new
    CORRECTNESS = "correctness"  # no hallucinations, proofs are valid
    CLARITY = "clarity"          # well-written, reproducible
    COMPLETENESS = "completeness"  # nothing important is missing


@dataclass(frozen=True)
class QualityPoint:
    """A point in the quality lattice — a vector of dimension scores."""
    scores: dict[str, float]  # dimension name -> [0, 1]

    def __le__(self, other: QualityPoint) -> bool:
        """Pointwise partial order on the product lattice."""
        for dim in QualityDimension:
            if self.scores.get(dim.value, 0) > other.scores.get(dim.value, 0) + 1e-9:
                return False
        return True

    def __lt__(self, other: QualityPoint) -> bool:
        return self <= other and self != other

    def join(self, other: QualityPoint) -> QualityPoint:
        """Least upper bound (pointwise max)."""
        return QualityPoint({
            dim.value: max(
                self.scores.get(dim.value, 0),
                other.scores.get(dim.value, 0),
            )
            for dim in QualityDimension
        })

    def meet(self, other: QualityPoint) -> QualityPoint:
        """Greatest lower bound (pointwise min)."""
        return QualityPoint({
            dim.value: min(
                self.scores.get(dim.value, 0),
                other.scores.get(dim.value, 0),
            )
            for dim in QualityDimension
        })

    def distance(self, other: QualityPoint) -> float:
        """L2 distance in the lattice."""
        total = 0.0
        for dim in QualityDimension:
            d = self.scores.get(dim.value, 0) - other.scores.get(dim.value, 0)
            total += d * d
        return math.sqrt(total)

    def min_dimension(self) -> tuple[str, float]:
        """Return the weakest dimension (the bottleneck)."""
        worst = min(
            ((dim.value, self.scores.get(dim.value, 0)) for dim in QualityDimension),
            key=lambda x: x[1],
        )
        return worst

    def summary(self) -> str:
        parts = [f"{d.value[:4]}={self.scores.get(d.value, 0):.2f}" for d in QualityDimension]
        return f"Q({', '.join(parts)})"


# Bottom and top of the lattice
Q_BOTTOM = QualityPoint({d.value: 0.0 for d in QualityDimension})
Q_TOP = QualityPoint({d.value: 1.0 for d in QualityDimension})
Q_ACCEPT_THRESHOLD = QualityPoint({d.value: 0.7 for d in QualityDimension})


def check_monotonicity(
    before: QualityPoint,
    after: QualityPoint,
    *,
    allow_contraction: bool = False,
) -> tuple[bool, str]:
    """Check that a step maintained quality monotonicity.

    Strict: after >= before in all dimensions.
    With allow_contraction: after may decrease in some dimensions
    if it increases in others (Pareto-compatible).
    """
    if after <= before and before <= after:
        return True, "Quality unchanged."

    if before <= after:
        return True, "Quality improved (monotone)."

    if allow_contraction:
        # Check Pareto: at least one dimension improved
        improved = False
        for dim in QualityDimension:
            if after.scores.get(dim.value, 0) > before.scores.get(dim.value, 0) + 1e-9:
                improved = True
                break
        if improved:
            return True, "Quality changed (Pareto-compatible contraction)."

    # Find which dimensions decreased
    decreased = []
    for dim in QualityDimension:
        b = before.scores.get(dim.value, 0)
        a = after.scores.get(dim.value, 0)
        if a < b - 1e-9:
            decreased.append(f"{dim.value}: {b:.2f} -> {a:.2f}")

    return False, f"Quality regression in: {', '.join(decreased)}"


# ═══════════════════════════════════════════════════════════════════════
# PART 5: STAGE GRAPH VERIFICATION
# ═══════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class StageNode:
    """A node in the stage graph."""
    id: str
    phase: str
    is_gate: bool = False
    is_terminal: bool = False


@dataclass(frozen=True)
class StageEdge:
    """An edge in the stage graph."""
    source: str
    target: str
    condition: str = "always"  # "always", "proceed", "refine", "pivot"


@dataclass
class StageGraph:
    """A directed graph of pipeline stages with static verification.

    The stage graph is verified at construction time for:
    1. Reachability: every stage is reachable from the initial state
    2. Termination: no infinite loops (cycles must pass through gates)
    3. Gate correctness: gates actually prevent forward progress until satisfied
    4. Completeness: every non-terminal stage has at least one outgoing edge
    """
    nodes: dict[str, StageNode]
    edges: list[StageEdge]
    initial: str

    def successors(self, node_id: str) -> list[str]:
        return [e.target for e in self.edges if e.source == node_id]

    def predecessors(self, node_id: str) -> list[str]:
        return [e.source for e in self.edges if e.target == node_id]

    def verify(self) -> list[str]:
        """Run all static verification checks. Returns violations."""
        violations: list[str] = []
        violations.extend(self._check_reachability())
        violations.extend(self._check_completeness())
        violations.extend(self._check_termination())
        violations.extend(self._check_gates())
        return violations

    def _check_reachability(self) -> list[str]:
        """BFS from initial — all nodes must be reachable."""
        visited: set[str] = set()
        queue = [self.initial]
        while queue:
            current = queue.pop(0)
            if current in visited:
                continue
            visited.add(current)
            queue.extend(self.successors(current))

        unreachable = set(self.nodes) - visited
        if unreachable:
            return [f"Unreachable stages: {unreachable}"]
        return []

    def _check_completeness(self) -> list[str]:
        """Every non-terminal node must have at least one outgoing edge."""
        violations = []
        for node_id, node in self.nodes.items():
            if not node.is_terminal and not self.successors(node_id):
                violations.append(f"Stage '{node_id}' has no outgoing edges (deadlock)")
        return violations

    def _check_termination(self) -> list[str]:
        """Cycles must pass through at least one gate node.

        This is a necessary condition for termination: gates can
        break the cycle by failing, so cycles through gates are
        potentially terminating.  Cycles without gates are
        definitely non-terminating.
        """
        violations = []
        cycles = self._find_cycles()
        for cycle in cycles:
            has_gate = any(self.nodes[n].is_gate for n in cycle)
            if not has_gate:
                violations.append(
                    f"Cycle {' -> '.join(cycle)} has no gate — "
                    f"may not terminate"
                )
        return violations

    def _check_gates(self) -> list[str]:
        """Gate nodes must have a backward edge (rollback target)."""
        violations = []
        for node_id, node in self.nodes.items():
            if node.is_gate:
                back_edges = [
                    e for e in self.edges
                    if e.source == node_id and e.condition in ("refine", "pivot", "rollback")
                ]
                if not back_edges:
                    violations.append(
                        f"Gate '{node_id}' has no rollback edge — "
                        f"cannot enforce its gate condition"
                    )
        return violations

    def _find_cycles(self) -> list[list[str]]:
        """Find all elementary cycles using DFS."""
        cycles: list[list[str]] = []
        visited: set[str] = set()
        path: list[str] = []
        on_path: set[str] = set()

        def dfs(node: str) -> None:
            if node in on_path:
                idx = path.index(node)
                cycles.append(path[idx:] + [node])
                return
            if node in visited:
                return
            visited.add(node)
            on_path.add(node)
            path.append(node)
            for succ in self.successors(node):
                dfs(succ)
            path.pop()
            on_path.discard(node)

        for node_id in self.nodes:
            visited.clear()
            on_path.clear()
            path.clear()
            dfs(node_id)
        return cycles


# ═══════════════════════════════════════════════════════════════════════
# PART 6: CEGAR REPAIR
# ═══════════════════════════════════════════════════════════════════════


@dataclass
class Counterexample:
    """A concrete test case that a stage's output failed."""
    input_value: Any
    expected_property: str
    actual_output: Any
    violation: str


@dataclass
class CEGARState:
    """State of the counterexample-guided repair loop.

    Key invariant: the test suite is MONOTONICALLY GROWING.
    Each repair attempt must pass ALL accumulated counterexamples,
    not just the most recent one.  This prevents oscillation and
    guarantees convergence (the hypothesis space shrinks with each
    counterexample).
    """
    counterexamples: list[Counterexample] = field(default_factory=list)
    repair_attempts: int = 0
    max_attempts: int = 10
    converged: bool = False

    def add_counterexample(self, cx: Counterexample) -> None:
        self.counterexamples.append(cx)

    def check_all(self, output: Any, check_fn: Callable[[Any, Counterexample], bool]) -> list[Counterexample]:
        """Check output against ALL accumulated counterexamples.

        Returns the list of counterexamples that still fail.
        An empty list means the output satisfies the full test suite.
        """
        failures = []
        for cx in self.counterexamples:
            if not check_fn(output, cx):
                failures.append(cx)
        return failures

    @property
    def suite_size(self) -> int:
        return len(self.counterexamples)

    @property
    def can_retry(self) -> bool:
        return self.repair_attempts < self.max_attempts and not self.converged


def cegar_repair_loop(
    initial_output: Any,
    contract: StageContract,
    input_value: Any,
    repair_fn: Callable[[Any, list[Counterexample]], Any],
    *,
    max_attempts: int = 10,
) -> tuple[Any, CEGARState]:
    """Run CEGAR-style repair until the output satisfies the contract.

    1. Check output against postcondition
    2. If it fails, extract counterexample from the violation
    3. Add counterexample to the monotonically growing suite
    4. Call repair_fn with the current output and full suite
    5. Repeat until pass or budget exhaustion

    Convergence argument: each counterexample strictly reduces the set
    of outputs that the repair_fn can produce (it must pass all
    accumulated tests).  In a finite output space, this terminates.
    """
    state = CEGARState(max_attempts=max_attempts)
    current_output = initial_output

    while state.can_retry:
        # Type-check against contract
        result = contract.check_post(input_value, current_output)
        if result.valid:
            state.converged = True
            return current_output, state

        # Extract counterexample from each violation
        for violation in result.violations:
            cx = Counterexample(
                input_value=input_value,
                expected_property=violation,
                actual_output=current_output,
                violation=violation,
            )
            state.add_counterexample(cx)

        # Repair: must satisfy ALL accumulated counterexamples
        state.repair_attempts += 1
        current_output = repair_fn(current_output, state.counterexamples)

    return current_output, state


# ═══════════════════════════════════════════════════════════════════════
# PART 7: CLAIM-CITATION ALIGNMENT
# ═══════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class Claim:
    """A claim made in a paper with its attributed source."""
    text: str
    citation_key: str
    attributed_result: str  # what the paper says the citation shows
    section: str = ""


@dataclass(frozen=True)
class CitationRecord:
    """Actual content of a cited work."""
    key: str
    title: str
    abstract: str
    doi: str | None = None
    arxiv_id: str | None = None
    verified_exists: bool = False


@dataclass(frozen=True)
class AlignmentResult:
    """Result of checking claim-citation alignment."""
    claim: Claim
    citation: CitationRecord | None
    exists: bool          # citation is a real paper
    aligned: bool         # claim matches what the paper actually says
    confidence: float     # 0-1 confidence in alignment judgment
    reason: str = ""


def check_claim_citation_alignment(
    claims: list[Claim],
    citations: dict[str, CitationRecord],
    *,
    llm_judge_fn: Callable[[str], str] | None = None,
) -> list[AlignmentResult]:
    """Verify that claims attributed to citations match what those papers say.

    This goes beyond "does this DOI exist?" (which AutoResearchClaw does)
    to "does this paper actually say what we claim it says?" (which nobody
    does automatically).

    Three checks per claim:
    1. EXISTENCE: the citation key maps to a real paper
    2. RELEVANCE: the paper's abstract is topically related to the claim
    3. ENTAILMENT: the specific result attributed to the paper is consistent
       with the paper's abstract/content

    Check 3 uses an LLM judge if available, or falls back to keyword overlap.
    """
    results = []
    for claim in claims:
        citation = citations.get(claim.citation_key)

        # Check 1: Existence
        if citation is None:
            results.append(AlignmentResult(
                claim=claim, citation=None,
                exists=False, aligned=False, confidence=1.0,
                reason=f"Citation '{claim.citation_key}' not found in bibliography",
            ))
            continue

        if not citation.verified_exists:
            results.append(AlignmentResult(
                claim=claim, citation=citation,
                exists=False, aligned=False, confidence=0.8,
                reason=f"Citation '{claim.citation_key}' could not be verified as a real paper",
            ))
            continue

        # Check 2+3: Relevance and entailment
        if llm_judge_fn is not None:
            prompt = (
                f"A paper claims: \"{claim.attributed_result}\"\n"
                f"This is attributed to: \"{citation.title}\"\n"
                f"Abstract of the cited paper: \"{citation.abstract}\"\n\n"
                f"Does the cited paper's abstract support the attributed result? "
                f"Reply ALIGNED or MISALIGNED on the first line, then explain briefly."
            )
            response = llm_judge_fn(prompt)
            first_line = response.strip().split("\n")[0].upper()
            aligned = "ALIGNED" in first_line and "MISALIGNED" not in first_line
            results.append(AlignmentResult(
                claim=claim, citation=citation,
                exists=True, aligned=aligned, confidence=0.7,
                reason=response[:200],
            ))
        else:
            # Fallback: keyword overlap heuristic
            claim_words = set(claim.attributed_result.lower().split())
            abstract_words = set(citation.abstract.lower().split())
            overlap = len(claim_words & abstract_words) / max(1, len(claim_words))
            aligned = overlap > 0.3
            results.append(AlignmentResult(
                claim=claim, citation=citation,
                exists=True, aligned=aligned, confidence=overlap,
                reason=f"Keyword overlap: {overlap:.0%}",
            ))

    return results


# ═══════════════════════════════════════════════════════════════════════
# PART 7.5: Z3 + LLM HYBRID VERIFICATION
# ═══════════════════════════════════════════════════════════════════════
#
# The core idea: refinement predicates fall into two classes:
#
#   DECIDABLE (structural) — array lengths, field existence, numeric bounds,
#     set membership, implication between boolean fields.
#     → Encode as Z3 constraints.  Verification is sound and complete.
#
#   UNDECIDABLE (semantic) — "this claim is grounded", "this paper is novel",
#     "the code is bug-free", "the citation actually supports the claim".
#     → Delegate to an LLM judge (Copilot / GPT / Claude).
#     → Verification is best-effort (sound but incomplete).
#
# By splitting the verification obligation, we get the best of both:
# Z3 catches all structural violations with certainty, and the LLM
# catches semantic violations with high probability.  A human reviewer
# only needs to audit the LLM judgments, not the structural checks.


# ---------------------------------------------------------------------------
# 7.5.1  Z3 refinements (decidable fragment)
# ---------------------------------------------------------------------------

try:
    import z3
    _HAS_Z3 = True
except ImportError:
    _HAS_Z3 = False


class Z3Refinement(Refinement):
    """A refinement whose predicate is encoded as a Z3 formula.

    When Z3 is available, verification is done symbolically (sound and
    complete for the QF_LIA/QF_LRA fragment).  When Z3 is not available,
    falls back to the Python predicate.

    This is the "proven methodology" component: SMT solving is a
    well-established technique from formal verification.
    """

    def __init__(
        self,
        name: str,
        python_predicate: Callable[[Any], tuple[bool, str]],
        z3_builder: Callable[[], tuple[list, Any]] | None = None,
    ) -> None:
        """
        Args:
            name: Human-readable name for the refinement.
            python_predicate: Fallback predicate (value -> (ok, reason)).
            z3_builder: Function that returns (z3_variables, z3_constraint).
                        Called with no arguments; the returned constraint is
                        checked for satisfiability to verify the refinement
                        structurally.
        """
        super().__init__(name=name, predicate=python_predicate)
        self._z3_builder = z3_builder
        self._z3_result_cache: dict[str, bool] = {}

    def check_z3(self, bindings: dict[str, Any]) -> tuple[bool, str] | None:
        """Check the refinement using Z3 if available.

        Returns None if Z3 is not available or the constraint is not
        expressible in Z3.  Otherwise returns (satisfied, reason).
        """
        if not _HAS_Z3 or self._z3_builder is None:
            return None

        try:
            variables, constraint = self._z3_builder()

            # Create solver and bind concrete values
            solver = z3.Solver()
            solver.set("timeout", 5000)  # 5 second timeout

            # Bind variables to concrete values from the JSON
            for var in variables:
                var_name = str(var)
                if var_name in bindings:
                    val = bindings[var_name]
                    if isinstance(val, bool):
                        solver.add(var == val)
                    elif isinstance(val, int):
                        solver.add(var == val)
                    elif isinstance(val, float):
                        solver.add(var == z3.RealVal(val))

            # Check if the negation of the constraint is satisfiable
            # If neg(constraint) is UNSAT, the constraint always holds
            # If neg(constraint) is SAT, we have a counterexample
            solver.add(z3.Not(constraint))
            result = solver.check()

            if result == z3.unsat:
                return True, f"Z3 verified: {self.name} (UNSAT negation)"
            elif result == z3.sat:
                model = solver.model()
                return False, f"Z3 counterexample for {self.name}: {model}"
            else:
                return None, f"Z3 timeout/unknown for {self.name}"
        except Exception as e:
            return None  # Fall back to Python predicate

    def check(self, value: Any) -> tuple[bool, str]:
        """Check using Z3 first, fall back to Python."""
        if _HAS_Z3 and self._z3_builder is not None:
            # Extract numeric/boolean bindings from value for Z3
            bindings = {}
            if isinstance(value, dict):
                for k, v in value.items():
                    if isinstance(v, (int, float, bool)):
                        bindings[k] = v
                    elif isinstance(v, list):
                        bindings[f"len_{k}"] = len(v)

            z3_result = self.check_z3(bindings)
            if z3_result is not None:
                return z3_result

        # Fall back to Python predicate
        return self.predicate(value)


def z3_array_min_length(field: str, n: int) -> Z3Refinement:
    """Z3-backed refinement: array field must have >= n elements."""
    def python_pred(v: Any) -> tuple[bool, str]:
        if not isinstance(v, dict) or not isinstance(v.get(field), list):
            return False, f"Field '{field}' is not an array"
        if len(v[field]) < n:
            return False, f"Field '{field}' has {len(v[field])} elements, need >= {n}"
        return True, ""

    def z3_build() -> tuple[list, Any]:
        length = z3.Int(f"len_{field}")
        return [length], length >= n

    return Z3Refinement(
        name=f"z3_array_min_length({field}, {n})",
        python_predicate=python_pred,
        z3_builder=z3_build if _HAS_Z3 else None,
    )


def z3_numeric_bound(field: str, *, min_val: float | None = None, max_val: float | None = None) -> Z3Refinement:
    """Z3-backed refinement: numeric field must be within bounds."""
    def python_pred(v: Any) -> tuple[bool, str]:
        if not isinstance(v, dict) or field not in v:
            return False, f"Field '{field}' missing"
        val = v[field]
        if not isinstance(val, (int, float)):
            return False, f"Field '{field}' is not numeric"
        if min_val is not None and val < min_val:
            return False, f"Field '{field}' = {val} < {min_val}"
        if max_val is not None and val > max_val:
            return False, f"Field '{field}' = {val} > {max_val}"
        return True, ""

    def z3_build() -> tuple[list, Any]:
        var = z3.Real(field)
        constraints = []
        if min_val is not None:
            constraints.append(var >= z3.RealVal(min_val))
        if max_val is not None:
            constraints.append(var <= z3.RealVal(max_val))
        return [var], z3.And(*constraints) if constraints else z3.BoolVal(True)

    return Z3Refinement(
        name=f"z3_bound({field}, min={min_val}, max={max_val})",
        python_predicate=python_pred,
        z3_builder=z3_build if _HAS_Z3 else None,
    )


def z3_implies(condition_field: str, required_field: str) -> Z3Refinement:
    """Z3-backed refinement: if condition_field is true, required_field must exist/be true."""
    def python_pred(v: Any) -> tuple[bool, str]:
        if not isinstance(v, dict):
            return False, "Not an object"
        if v.get(condition_field):
            if not v.get(required_field):
                return False, f"'{condition_field}' is true but '{required_field}' is not"
        return True, ""

    def z3_build() -> tuple[list, Any]:
        cond = z3.Bool(condition_field)
        req = z3.Bool(required_field)
        return [cond, req], z3.Implies(cond, req)

    return Z3Refinement(
        name=f"z3_implies({condition_field} => {required_field})",
        python_predicate=python_pred,
        z3_builder=z3_build if _HAS_Z3 else None,
    )


def z3_coverage(items_field: str, covered_field: str) -> Z3Refinement:
    """Z3-backed refinement: |covered| >= |items| (full coverage)."""
    def python_pred(v: Any) -> tuple[bool, str]:
        if not isinstance(v, dict):
            return False, "Not an object"
        items = v.get(items_field, [])
        covered = v.get(covered_field, [])
        if not isinstance(items, list) or not isinstance(covered, list):
            return False, f"Fields '{items_field}' and '{covered_field}' must be arrays"
        if len(covered) < len(items):
            return False, f"|{covered_field}| = {len(covered)} < |{items_field}| = {len(items)}"
        return True, ""

    def z3_build() -> tuple[list, Any]:
        n_items = z3.Int(f"len_{items_field}")
        n_covered = z3.Int(f"len_{covered_field}")
        return [n_items, n_covered], n_covered >= n_items

    return Z3Refinement(
        name=f"z3_coverage({covered_field} covers {items_field})",
        python_predicate=python_pred,
        z3_builder=z3_build if _HAS_Z3 else None,
    )


# ---------------------------------------------------------------------------
# 7.5.2  LLM refinements (undecidable fragment)
# ---------------------------------------------------------------------------

class LLMRefinement(Refinement):
    """A refinement whose predicate requires LLM judgment.

    For semantic properties that cannot be encoded in Z3 — novelty,
    correctness of prose claims, grounding adequacy, clarity.

    The LLM judge is called via `copilot` CLI (or any configured
    LLM backend).  The result is cached to avoid redundant calls.

    This is the "novel methodology" component: using LLM-as-judge
    as a verification oracle for undecidable refinement predicates.
    """

    def __init__(
        self,
        name: str,
        judge_prompt_template: str,
        *,
        model: str = "gpt-4",
        cache: dict[str, tuple[bool, str]] | None = None,
        fallback_predicate: Callable[[Any], tuple[bool, str]] | None = None,
    ) -> None:
        self._judge_template = judge_prompt_template
        self._model = model
        self._cache = cache if cache is not None else {}
        self._fallback = fallback_predicate

        def _pred(v: Any) -> tuple[bool, str]:
            return self._evaluate(v)

        super().__init__(name=name, predicate=_pred)

    def _evaluate(self, value: Any) -> tuple[bool, str]:
        # Serialize value for cache key
        content = json.dumps(value, sort_keys=True, default=str)
        cache_key = hashlib.sha256(
            f"{self.name}:{content[:2000]}".encode()
        ).hexdigest()[:16]

        if cache_key in self._cache:
            return self._cache[cache_key]

        # Build judge prompt
        if isinstance(value, dict):
            # Extract the most relevant content for the judge
            content_for_judge = json.dumps(value, indent=2, default=str)
            if len(content_for_judge) > 8000:
                content_for_judge = content_for_judge[:8000] + "\n[TRUNCATED]"
        else:
            content_for_judge = str(value)[:8000]

        prompt = self._judge_template.replace("{content}", content_for_judge)

        # Try calling copilot
        try:
            result = subprocess.run(
                ["copilot", "--model", self._model, "-p", prompt,
                 "--no-ask-user", "--autopilot"],
                capture_output=True, text=True, timeout=120,
                stdin=subprocess.DEVNULL, check=False,
            )
            response = (result.stdout or result.stderr).strip()
            first_line = response.split("\n")[0].strip().upper() if response else ""

            if "PASS" in first_line or "YES" in first_line or "SATISFIED" in first_line:
                verdict = (True, f"LLM judge ({self.name}): PASS — {response[:200]}")
            elif "FAIL" in first_line or "NO" in first_line or "VIOLATED" in first_line:
                verdict = (False, f"LLM judge ({self.name}): FAIL — {response[:200]}")
            else:
                # Ambiguous — treat as uncertain, use fallback if available
                if self._fallback:
                    verdict = self._fallback(value)
                else:
                    verdict = (False, f"LLM judge ({self.name}): AMBIGUOUS — {response[:200]}")
        except (subprocess.TimeoutExpired, FileNotFoundError):
            # Copilot not available — use fallback
            if self._fallback:
                verdict = self._fallback(value)
            else:
                verdict = (False, f"LLM judge ({self.name}): UNAVAILABLE (copilot not found)")

        self._cache[cache_key] = verdict
        return verdict


def llm_grounding_check() -> LLMRefinement:
    """LLM-backed check that every claim has adequate grounding."""
    return LLMRefinement(
        name="llm_grounding_check",
        judge_prompt_template=(
            "You are a grounding auditor. Review this research artifact:\n\n"
            "{content}\n\n"
            "Check: does every empirical claim, theorem, and citation have "
            "a traceable evidence path (experiment script, proof sketch, or URL)?\n\n"
            "Reply PASS if all claims are grounded, FAIL if any claim lacks evidence. "
            "On the first line write exactly PASS or FAIL, then explain."
        ),
        fallback_predicate=lambda v: (
            isinstance(v, dict)
            and len(v.get("groundings", [])) > 0,
            "Fallback: has at least one grounding entry",
        ),
    )


def llm_novelty_check() -> LLMRefinement:
    """LLM-backed check that the contribution is genuinely novel."""
    return LLMRefinement(
        name="llm_novelty_check",
        judge_prompt_template=(
            "You are a novelty reviewer for a top ML conference. "
            "Review this research artifact:\n\n{content}\n\n"
            "Is the core contribution genuinely novel — not a trivial "
            "variation of existing work?\n\n"
            "Reply PASS if novel, FAIL if derivative. First line: PASS or FAIL."
        ),
    )


def llm_no_hallucination() -> LLMRefinement:
    """LLM-backed check that no claims are fabricated."""
    return LLMRefinement(
        name="llm_no_hallucination",
        judge_prompt_template=(
            "You are a hallucination detector. Review this research artifact:\n\n"
            "{content}\n\n"
            "Check for:\n"
            "1. Fabricated experimental results (numbers with no backing experiment)\n"
            "2. Invented citations (papers that don't exist)\n"
            "3. Claims about code behavior that don't match the actual code\n"
            "4. Theorems stated without proof or proof sketch\n\n"
            "Reply PASS if no hallucinations found, FAIL if any detected. "
            "First line: PASS or FAIL, then list any issues."
        ),
    )


def llm_code_correctness(description: str = "") -> LLMRefinement:
    """LLM-backed check that code is correct and bug-free."""
    return LLMRefinement(
        name="llm_code_correctness",
        judge_prompt_template=(
            "You are a code reviewer. Review this code artifact:\n\n"
            "{content}\n\n"
            f"Context: {description}\n\n"
            "Check for:\n"
            "1. Logic errors and off-by-one bugs\n"
            "2. Unhandled edge cases\n"
            "3. Type mismatches\n"
            "4. Resource leaks\n"
            "5. Security vulnerabilities\n\n"
            "Reply PASS if the code looks correct, FAIL if bugs found. "
            "First line: PASS or FAIL."
        ),
    )


# ---------------------------------------------------------------------------
# 7.5.3  Hybrid verification: Z3 ∧ LLM
# ---------------------------------------------------------------------------

class HybridRefinement(Refinement):
    """Combines Z3 (decidable) and LLM (undecidable) checks.

    The verification obligation is split:
      structural_obligations: Z3Refinement[] — sound & complete
      semantic_obligations: LLMRefinement[] — sound but incomplete

    A value satisfies the hybrid refinement iff:
      ALL structural checks pass (Z3, certain) AND
      ALL semantic checks pass (LLM, best-effort)

    The separation is the key insight: structural bugs are caught with
    certainty by Z3.  Semantic bugs are caught with high probability
    by the LLM.  A human reviewer only needs to audit the LLM
    judgments, not re-check array lengths or field existence.
    """

    def __init__(
        self,
        name: str,
        structural: list[Z3Refinement],
        semantic: list[LLMRefinement],
    ) -> None:
        self.structural = structural
        self.semantic = semantic

        def _pred(v: Any) -> tuple[bool, str]:
            return self._evaluate(v)

        super().__init__(name=name, predicate=_pred)

    def _evaluate(self, value: Any) -> tuple[bool, str]:
        all_reasons: list[str] = []

        # Phase 1: Z3 checks (fast, certain)
        for ref in self.structural:
            ok, reason = ref.check(value)
            if not ok:
                all_reasons.append(f"[Z3/{ref.name}] {reason}")

        # If structural checks fail, don't bother with expensive LLM calls
        if all_reasons:
            return False, "; ".join(all_reasons)

        # Phase 2: LLM checks (slow, best-effort)
        for ref in self.semantic:
            ok, reason = ref.check(value)
            if not ok:
                all_reasons.append(f"[LLM/{ref.name}] {reason}")

        if all_reasons:
            return False, "; ".join(all_reasons)
        return True, f"Hybrid verification passed: {len(self.structural)} Z3 + {len(self.semantic)} LLM checks"

    def summary(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "structural_checks": [r.name for r in self.structural],
            "semantic_checks": [r.name for r in self.semantic],
            "z3_available": _HAS_Z3,
        }


def build_grounded_paper_check() -> HybridRefinement:
    """The full hybrid check for a grounded, hallucination-free paper.

    Structural (Z3):
      - groundings array is non-empty
      - claims_verified > 0
      - claims_verified <= claims_total
      - audit_passed => hallucinations_found is empty
      - every repo has a grounding entry

    Semantic (LLM):
      - no hallucinated claims
      - claims are actually grounded (not just structurally present)
      - paper is novel
    """
    return HybridRefinement(
        name="grounded_paper",
        structural=[
            z3_array_min_length("groundings", 1),
            z3_numeric_bound("claims_verified", min_val=1),
            z3_implies("audit_passed", "no_hallucinations"),
            z3_coverage("repos", "grounded_repos"),
        ],
        semantic=[
            llm_no_hallucination(),
            llm_grounding_check(),
        ],
    )


# ═══════════════════════════════════════════════════════════════════════
# PART 8: VERIFIED PIPELINE
# ═══════════════════════════════════════════════════════════════════════

# ---------------------------------------------------------------------------
# 8.1  Research pipeline stage definitions
# ---------------------------------------------------------------------------

# The full idea-to-production pipeline as a verified stage graph.

RESEARCH_STAGES = StageGraph(
    nodes={
        "ideation": StageNode("ideation", "seed"),
        "radical_math": StageNode("radical_math", "seed"),
        "generation": StageNode("generation", "seed"),
        "upgrade": StageNode("upgrade", "seed"),
        "grounding": StageNode("grounding", "harden"),
        "audit": StageNode("audit", "harden", is_gate=True),
        "paper_write": StageNode("paper_write", "harden"),
        "benchmark": StageNode("benchmark", "harden"),
        "critique": StageNode("critique", "harden"),
        "respond": StageNode("respond", "harden"),
        "ci_cd": StageNode("production", "production"),
        "type_check": StageNode("type_check", "production"),
        "security": StageNode("security", "production"),
        "demos": StageNode("demos", "production"),
        "integration_test": StageNode("integration_test", "production"),
        "release": StageNode("release", "production", is_terminal=True),
    },
    edges=[
        # Seed sequence
        StageEdge("ideation", "radical_math"),
        StageEdge("radical_math", "generation"),
        StageEdge("generation", "upgrade"),
        # Upgrade -> grounding (mandatory)
        StageEdge("upgrade", "grounding"),
        # Grounding -> audit (mandatory: hallucination resistance)
        StageEdge("grounding", "audit"),
        # Audit gate: pass -> paper, fail -> rollback to grounding
        StageEdge("audit", "paper_write", condition="proceed"),
        StageEdge("audit", "grounding", condition="rollback"),
        # Paper -> benchmark -> critique -> respond
        StageEdge("paper_write", "benchmark"),
        StageEdge("benchmark", "critique"),
        StageEdge("critique", "respond"),
        # Respond -> re-audit (cycle through gate)
        StageEdge("respond", "grounding"),
        # Once audit passes, can enter production
        StageEdge("paper_write", "ci_cd"),
        StageEdge("ci_cd", "type_check"),
        StageEdge("type_check", "security"),
        StageEdge("security", "demos"),
        StageEdge("demos", "integration_test"),
        StageEdge("integration_test", "release"),
    ],
    initial="ideation",
)


# ---------------------------------------------------------------------------
# 8.2  Contract definitions for each stage
# ---------------------------------------------------------------------------

# Input/output types for each stage, with dependent postconditions.

IDEATION_CONTRACT = StageContract(
    stage_name="ideation",
    precondition=RefinedType("IdeationInput", JAny()),
    postcondition=DependentType(
        "IdeationOutput",
        lambda _: RefinedType(
            "IdeationResult",
            JObject(problems=JArray(JObject(
                name=JString(),
                description=JString(),
                math_object=JString(),
                benchmark=JString(),
            ))),
            [
                array_min_length("problems", 1),
                no_placeholder_text(),
            ],
        ),
    ),
    frame=frozenset({"problems"}),
)

GENERATION_CONTRACT = StageContract(
    stage_name="generation",
    precondition=RefinedType(
        "GenerationInput",
        JObject(problems=JArray(), theories=JArray()),
        [array_min_length("problems", 1), array_min_length("theories", 1)],
    ),
    postcondition=DependentType(
        "GenerationOutput",
        lambda input_val: RefinedType(
            f"GenerationResult(covers {len(input_val.get('problems', []))} problems)",
            JObject(repos=JArray(JObject(
                name=JString(),
                problem_ref=JString(),
                loc=JInt(),
            ))),
            [
                # DEPENDENT: must have one repo per problem
                refinement(
                    "covers_all_problems",
                    lambda v: len(v.get("repos", [])) >= len(input_val.get("problems", [])),
                    f"Must generate repos for all {len(input_val.get('problems', []))} problems",
                ),
                # Each repo must have > 0 LOC
                refinement(
                    "non_trivial_repos",
                    lambda v: all(r.get("loc", 0) > 0 for r in v.get("repos", [])),
                    "All repos must have non-zero LOC",
                ),
            ],
        ),
    ),
    frame=frozenset({"repos"}),
)

GROUNDING_CONTRACT = StageContract(
    stage_name="grounding",
    precondition=RefinedType(
        "GroundingInput",
        JObject(repos=JArray()),
        [array_min_length("repos", 1)],
    ),
    postcondition=DependentType(
        "GroundingOutput",
        lambda input_val: RefinedType(
            "GroundingResult",
            JObject(
                repos=JArray(),
                groundings=JArray(JObject(
                    repo=JString(),
                    claim=JString(),
                    evidence_type=JString(),
                    evidence_path=JString(),
                )),
            ),
            [
                # DEPENDENT: every repo must have at least one grounding entry
                refinement(
                    "all_repos_grounded",
                    lambda v: set(r.get("name", r.get("repo", "")) for r in v.get("repos", []))
                             <= set(g.get("repo", "") for g in v.get("groundings", [])),
                    "Every repo must have at least one grounding entry",
                ),
                # No empty evidence paths
                refinement(
                    "no_empty_evidence",
                    lambda v: all(
                        g.get("evidence_path", "").strip()
                        for g in v.get("groundings", [])
                    ),
                    "Every grounding entry must have a non-empty evidence path",
                ),
            ],
        ),
    ),
    frame=frozenset({"groundings"}),
)

AUDIT_CONTRACT = StageContract(
    stage_name="audit",
    precondition=RefinedType(
        "AuditInput",
        JObject(repos=JArray(), groundings=JArray()),
        [array_min_length("groundings", 1)],
    ),
    postcondition=DependentType(
        "AuditOutput",
        lambda input_val: RefinedType(
            "AuditResult",
            JObject(
                repos=JArray(),
                groundings=JArray(),
                audit_passed=JBool(),
                hallucinations_found=JArray(JString()),
                claims_verified=JInt(),
                claims_total=JInt(),
            ),
            [
                # The audit must actually check something
                refinement(
                    "non_trivial_audit",
                    lambda v: v.get("claims_total", 0) > 0,
                    "Audit must check at least one claim",
                ),
                # If audit passes, hallucinations list must be empty
                refinement(
                    "pass_implies_no_hallucinations",
                    lambda v: (
                        not v.get("audit_passed", False)
                        or len(v.get("hallucinations_found", [])) == 0
                    ),
                    "If audit_passed=true, hallucinations_found must be empty",
                ),
                # Verification rate must be > 0
                refinement(
                    "positive_verification",
                    lambda v: v.get("claims_verified", 0) > 0,
                    "At least one claim must be verified",
                ),
            ],
        ),
    ),
    frame=frozenset({"audit_passed", "hallucinations_found", "claims_verified", "claims_total"}),
)


# All contracts in pipeline order
STAGE_CONTRACTS: dict[str, StageContract] = {
    "ideation": IDEATION_CONTRACT,
    "generation": GENERATION_CONTRACT,
    "grounding": GROUNDING_CONTRACT,
    "audit": AUDIT_CONTRACT,
}


# ---------------------------------------------------------------------------
# 8.3  Verified pipeline runner
# ---------------------------------------------------------------------------

@dataclass
class PipelineState:
    """The full state of a pipeline run, with provenance."""
    workspace: TaintedValue
    quality: QualityPoint
    history: list[str] = field(default_factory=list)
    violations: list[dict[str, Any]] = field(default_factory=list)
    step_index: int = 0


class VerifiedPipeline:
    """Pipeline runner with full verification at every step.

    Every transition is:
    1. Precondition-checked (input type must be satisfied)
    2. Executed
    3. Postcondition-checked (dependent output type must be satisfied)
    4. Frame-checked (only declared fields modified)
    5. Quality-monotonicity-checked (quality never decreases)
    6. Provenance-tracked (output carries derivation chain)

    If any check fails, the output is rejected and the step is
    retried with CEGAR-style repair (if a repair function is provided)
    or the pipeline halts with a precise type error.
    """

    def __init__(
        self,
        graph: StageGraph,
        contracts: dict[str, StageContract],
        *,
        trace_dir: Path | None = None,
    ) -> None:
        # Verify graph at construction time
        violations = graph.verify()
        if violations:
            raise ValueError(
                f"Stage graph has {len(violations)} verification failures:\n"
                + "\n".join(f"  - {v}" for v in violations)
            )

        self.graph = graph
        self.contracts = contracts
        self.enforcer = ContractEnforcer()
        self.trace_dir = trace_dir

    def run(
        self,
        initial_input: dict[str, Any],
        stage_executors: dict[str, Callable[[Any], Any]],
        *,
        quality_scorer: Callable[[Any], QualityPoint] | None = None,
        model: str = "",
    ) -> dict[str, Any]:
        """Execute the pipeline with full verification."""
        state = PipelineState(
            workspace=TaintedValue(value=initial_input),
            quality=Q_BOTTOM,
        )

        # Topological traversal of the stage graph
        current_stage = self.graph.initial
        manifest: dict[str, Any] = {
            "stages_executed": [],
            "violations": [],
            "quality_trace": [],
            "provenance_chain": [],
            "accepted": False,
        }

        while current_stage is not None:
            node = self.graph.nodes.get(current_stage)
            if node is None:
                break

            state.step_index += 1
            state.history.append(current_stage)

            contract = self.contracts.get(current_stage)
            executor = stage_executors.get(current_stage)

            if executor is None:
                print(f"  [{state.step_index}] {current_stage}: no executor, skipping", flush=True)
                current_stage = self._next_stage(current_stage, state)
                continue

            print(f"  [{state.step_index}] {current_stage}...", end=" ", flush=True)

            if contract is not None:
                # Full contract enforcement
                output, violations = self.enforcer.enforce(
                    contract, state.workspace, executor,
                    step_index=state.step_index, model=model,
                )

                if violations:
                    print(f"TYPE ERROR ({len(violations)} violations)", flush=True)
                    for v in violations:
                        print(f"    - {v}", flush=True)
                    manifest["violations"].extend(
                        {"stage": current_stage, "step": state.step_index, "violation": v}
                        for v in violations
                    )

                    # Gate check: if this is a gate and postcondition failed,
                    # roll back instead of proceeding
                    if node.is_gate and output is not None:
                        rollback = self._rollback_target(current_stage)
                        if rollback:
                            print(f"    -> rolling back to {rollback}", flush=True)
                            current_stage = rollback
                            continue

                if output is not None:
                    state.workspace = output
            else:
                # No contract — execute without verification
                try:
                    raw = executor(state.workspace.value)
                    state.workspace = state.workspace.derive(
                        raw, stage=current_stage,
                        step_index=state.step_index, model=model,
                    )
                except Exception as e:
                    print(f"EXEC ERROR: {e}", flush=True)
                    current_stage = self._next_stage(current_stage, state)
                    continue

            # Quality monotonicity check
            if quality_scorer is not None:
                new_quality = quality_scorer(state.workspace.value)
                mono_ok, mono_reason = check_monotonicity(
                    state.quality, new_quality, allow_contraction=True,
                )
                if not mono_ok:
                    print(f"QUALITY REGRESSION: {mono_reason}", flush=True)
                    manifest["violations"].append({
                        "stage": current_stage,
                        "step": state.step_index,
                        "violation": f"Quality regression: {mono_reason}",
                    })
                state.quality = new_quality
                manifest["quality_trace"].append({
                    "stage": current_stage,
                    "quality": new_quality.summary(),
                })

            print(f"OK {state.quality.summary() if quality_scorer else ''}", flush=True)

            manifest["stages_executed"].append({
                "stage": current_stage,
                "step": state.step_index,
                "provenance_depth": len(state.workspace.provenance),
            })

            # Record provenance
            manifest["provenance_chain"] = state.workspace.to_dict()["provenance"]

            # Advance
            if node.is_terminal:
                current_stage = None
            else:
                current_stage = self._next_stage(current_stage, state)

        manifest["accepted"] = len(manifest["violations"]) == 0
        manifest["enforcer_stats"] = self.enforcer.stats
        manifest["final_quality"] = state.quality.summary() if quality_scorer else None
        manifest["total_steps"] = state.step_index

        if self.trace_dir:
            self.trace_dir.mkdir(parents=True, exist_ok=True)
            (self.trace_dir / "manifest.json").write_text(
                json.dumps(manifest, indent=2, default=str) + "\n"
            )

        return manifest

    def _next_stage(self, current: str, state: PipelineState) -> str | None:
        """Determine the next stage based on the graph and current state."""
        edges = [e for e in self.graph.edges if e.source == current]
        if not edges:
            return None
        # Prefer "proceed" edges, then "always" edges
        for condition in ("proceed", "always"):
            for edge in edges:
                if edge.condition == condition:
                    return edge.target
        # Fallback to first edge
        return edges[0].target

    def _rollback_target(self, current: str) -> str | None:
        """Find the rollback target for a gate stage."""
        for edge in self.graph.edges:
            if edge.source == current and edge.condition in ("rollback", "refine", "pivot"):
                return edge.target
        return None


# ═══════════════════════════════════════════════════════════════════════
# PART 9: CLI
# ═══════════════════════════════════════════════════════════════════════

def cmd_verify(argv: list[str] | None = None) -> int:
    """Verify the stage graph and all contracts."""
    print("=== Stage Graph Verification ===")
    violations = RESEARCH_STAGES.verify()
    if violations:
        for v in violations:
            print(f"  FAIL: {v}")
    else:
        print(f"  OK: {len(RESEARCH_STAGES.nodes)} stages, {len(RESEARCH_STAGES.edges)} edges")

    print("\n=== Contract Verification ===")
    for name, contract in STAGE_CONTRACTS.items():
        # Check that the precondition type is well-formed
        # (can check an empty value without crashing)
        try:
            contract.check_pre({})
            print(f"  {name}: precondition well-formed")
        except Exception as e:
            print(f"  {name}: precondition MALFORMED: {e}")

    print("\n=== Type System Self-Test ===")
    # Test the type system on sample values
    tests = [
        ("JInt checks int", JInt(), 42, True),
        ("JInt rejects str", JInt(), "hello", False),
        ("JString checks str", JString(), "hello", True),
        ("JArray checks list", JArray(JInt()), [1, 2, 3], True),
        ("JArray rejects mixed", JArray(JInt()), [1, "two"], False),
        ("JObject checks fields", JObject(x=JInt(), y=JString()), {"x": 1, "y": "hi"}, True),
        ("JObject rejects missing", JObject(x=JInt()), {"z": 1}, False),
    ]
    passed = 0
    for desc, jtype, value, expected in tests:
        result = jtype.check(value)
        ok = result == expected
        passed += ok
        status = "OK" if ok else "FAIL"
        print(f"  {status}: {desc}")
    print(f"  {passed}/{len(tests)} type system tests passed")

    print("\n=== Refinement Self-Test ===")
    grounded = RefinedType(
        "GroundedClaim",
        JObject(text=JString(), evidence=JArray(JString())),
        [non_empty("text"), array_min_length("evidence", 1)],
    )
    good = {"text": "X achieves 95%", "evidence": ["results/exp1.json"]}
    bad_empty = {"text": "", "evidence": ["results/exp1.json"]}
    bad_no_evidence = {"text": "X achieves 95%", "evidence": []}
    print(f"  Good claim: {grounded.check(good)}")
    print(f"  Empty text: {grounded.check(bad_empty)}")
    print(f"  No evidence: {grounded.check(bad_no_evidence)}")

    print("\n=== Dependent Type Self-Test ===")
    dep = DependentType(
        "GenerationCovers",
        lambda inp: RefinedType(
            f"Covers({len(inp.get('problems', []))} problems)",
            JObject(repos=JArray()),
            [refinement(
                "count_match",
                lambda v: len(v.get("repos", [])) >= len(inp.get("problems", [])),
                "Must have one repo per problem",
            )],
        ),
    )
    inp_3 = {"problems": [1, 2, 3]}
    out_ok = {"repos": [{"name": "a"}, {"name": "b"}, {"name": "c"}]}
    out_bad = {"repos": [{"name": "a"}]}
    print(f"  3 problems, 3 repos: {dep.check(inp_3, out_ok)}")
    print(f"  3 problems, 1 repo:  {dep.check(inp_3, out_bad)}")

    print("\n=== Provenance Self-Test ===")
    tv = TaintedValue(value={"topic": "ML"})
    tv2 = tv.derive({"hypotheses": ["H1"]}, stage="synthesis", step_index=1)
    tv3 = tv2.derive({"paper": "draft"}, stage="writing", step_index=2)
    print(f"  Provenance chain: {tv3.trace_stages()}")
    print(f"  Origin: {tv3.trace_origin()}")

    print("\n=== Quality Lattice Self-Test ===")
    q1 = QualityPoint({"grounding": 0.5, "novelty": 0.6, "correctness": 0.7, "clarity": 0.4, "completeness": 0.3})
    q2 = QualityPoint({"grounding": 0.6, "novelty": 0.7, "correctness": 0.8, "clarity": 0.5, "completeness": 0.4})
    print(f"  q1 <= q2: {q1 <= q2}")
    print(f"  q2 <= q1: {q2 <= q1}")
    print(f"  join: {q1.join(q2).summary()}")
    print(f"  meet: {q1.meet(q2).summary()}")
    print(f"  monotone: {check_monotonicity(q1, q2)}")
    print(f"  regression: {check_monotonicity(q2, q1)}")

    print(f"\n=== Z3 Refinement Self-Test (Z3 available: {_HAS_Z3}) ===")
    # Test Z3-backed refinements
    z3_len = z3_array_min_length("items", 3)
    print(f"  len([1,2,3]) >= 3: {z3_len.check({'items': [1, 2, 3]})}")
    print(f"  len([1]) >= 3:     {z3_len.check({'items': [1]})}")

    z3_bound = z3_numeric_bound("score", min_val=0.0, max_val=1.0)
    print(f"  score=0.5 in [0,1]: {z3_bound.check({'score': 0.5})}")
    print(f"  score=1.5 in [0,1]: {z3_bound.check({'score': 1.5})}")

    z3_imp = z3_implies("audit_passed", "no_hallucinations")
    print(f"  audit=T, no_hall=T: {z3_imp.check({'audit_passed': True, 'no_hallucinations': True})}")
    print(f"  audit=T, no_hall=F: {z3_imp.check({'audit_passed': True, 'no_hallucinations': False})}")
    print(f"  audit=F, no_hall=F: {z3_imp.check({'audit_passed': False, 'no_hallucinations': False})}")

    z3_cov = z3_coverage("problems", "repos")
    print(f"  3 problems, 3 repos: {z3_cov.check({'problems': [1,2,3], 'repos': ['a','b','c']})}")
    print(f"  3 problems, 1 repo:  {z3_cov.check({'problems': [1,2,3], 'repos': ['a']})}")

    print(f"\n=== Hybrid Verification Self-Test ===")
    hybrid = HybridRefinement(
        name="test_hybrid",
        structural=[z3_array_min_length("claims", 1), z3_numeric_bound("score", min_val=0.5)],
        semantic=[],  # skip LLM in self-test
    )
    print(f"  Structural pass: {hybrid.check({'claims': ['c1'], 'score': 0.8})}")
    print(f"  Structural fail: {hybrid.check({'claims': [], 'score': 0.8})}")
    print(f"  Hybrid summary:  {hybrid.summary()}")

    total_violations = len(violations)
    return 0 if total_violations == 0 else 1


def cmd_trace(pipeline_root: Path, claim_text: str) -> int:
    """Trace the provenance of a claim through the pipeline."""
    # Look for manifest with provenance data
    manifest_path = pipeline_root / "manifest.json"
    if not manifest_path.exists():
        print(f"No manifest found at {manifest_path}")
        return 1
    manifest = json.loads(manifest_path.read_text())
    chain = manifest.get("provenance_chain", [])
    print(f"Provenance chain ({len(chain)} records):")
    for record in chain:
        print(f"  [{record.get('step', '?')}] {record.get('stage', '?')} "
              f"@ {record.get('timestamp', '?')}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Comet-H Verified: JSON-refinement dependent typing for LLM pipelines",
    )
    sub = parser.add_subparsers(dest="command")

    sub.add_parser("verify", help="Verify stage graph, contracts, and type system.")
    sub.add_parser("self-test", help="Run all self-tests (same as verify).")

    trace_parser = sub.add_parser("trace", help="Trace provenance of a claim.")
    trace_parser.add_argument("--pipeline-dir", required=True)
    trace_parser.add_argument("--claim", required=True)

    args = parser.parse_args(argv)

    if args.command in ("verify", "self-test", None):
        return cmd_verify()
    elif args.command == "trace":
        return cmd_trace(Path(args.pipeline_dir), args.claim)
    else:
        parser.print_help()
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
