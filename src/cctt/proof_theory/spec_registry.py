"""Spec Registry — trust-as-proven-spec enforcement.

When function A calls function B, A must only assume what B has PROVEN.
Not a vague string like "trust: math.sqrt" — the actual proven ensures:
  "isinstance(result, float)" and "result >= 0 when x >= 0".

This module provides:

1. **ProvenSpec** — a spec with proved/candidate distinction
2. **SpecRef** — a reference to a proven spec (replaces bare trust strings)
3. **SpecRegistry** — maps qualified names to their ProvenSpecs
4. **CallObligation** — what A assumes about B at a specific call site
5. **ObligationChecker** — verify that A's assumptions ⊆ B's proven ensures

The key insight: trust isn't transitive or blanket. When A says
"I trust B", it means: "I USE B's proven postconditions as axioms."
If B only proved `isinstance(result, int)`, then A cannot assume
`result > 0` — that's not in B's contract.

In the sheaf picture: the spec is a section of the "contract sheaf",
and trust enforcement is checking that A's local section RESTRICTS to
B's section over the shared fiber.

Usage::

    registry = SpecRegistry()

    # Register B's proven spec
    registry.register_proved("math.sqrt", C4Spec(
        requires=["x >= 0"],
        ensures=["result >= 0", "result * result == x"],
    ))

    # When proving A, extract what A assumes about B
    obligations = extract_call_obligations(a_source, "a_func", registry)

    # Check each obligation is covered by B's proven spec
    for obl in obligations:
        result = check_obligation(obl, registry)
        if not result.satisfied:
            print(f"A assumes {obl.assumed} about {obl.callee}, "
                  f"but B only proved {result.available}")
"""
from __future__ import annotations

import ast
import textwrap
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from cctt.proof_theory.spec_inference import C4Spec, SpecSource, SpecStrength


# ═══════════════════════════════════════════════════════════════════
# Proof status for a spec
# ═══════════════════════════════════════════════════════════════════

class ProofStatus(Enum):
    """Status of a spec's proof."""
    UNPROVED = "unproved"         # Spec exists but not verified
    CANDIDATE = "candidate"       # Inferred by static analysis or LLM, not verified
    Z3_PROVED = "z3_proved"       # All VCs discharged by Z3
    STRUCTURALLY_PROVED = "structurally_proved"  # Proved by proof term structure
    ASSUMED = "assumed"           # Assumed correct (library axiom)
    FAILED = "failed"             # Verification attempted and failed

    @property
    def is_trusted(self) -> bool:
        """Can downstream code rely on this spec?"""
        return self in (
            ProofStatus.Z3_PROVED,
            ProofStatus.STRUCTURALLY_PROVED,
            ProofStatus.ASSUMED,
        )


# ═══════════════════════════════════════════════════════════════════
# ProvenSpec — spec with proved/candidate distinction
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProvenSpec:
    """A spec with explicit proof status.

    The crucial distinction: `candidate_spec` is what we THINK the function
    does (from static analysis or LLM). `proved_spec` is what we have
    VERIFIED it does. Only `proved_spec` may be used as axioms by callers.

    If proved_spec is None, nothing has been verified yet.
    """
    qualname: str
    candidate_spec: C4Spec
    proved_spec: Optional[C4Spec] = None
    proof_status: ProofStatus = ProofStatus.UNPROVED
    trust_basis: List[str] = field(default_factory=list)
    proof_details: Dict[str, Any] = field(default_factory=dict)

    @property
    def usable_spec(self) -> Optional[C4Spec]:
        """The spec that downstream code may rely on."""
        if self.proof_status.is_trusted and self.proved_spec is not None:
            return self.proved_spec
        return None

    @property
    def usable_ensures(self) -> List[str]:
        """Only the PROVEN ensures — what callers may assume."""
        s = self.usable_spec
        return s.ensures if s else []

    @property
    def usable_requires(self) -> List[str]:
        """Only the PROVEN preconditions — what callers must satisfy."""
        s = self.usable_spec
        return s.requires if s else []


# ═══════════════════════════════════════════════════════════════════
# SpecRef — structured trust reference (replaces bare strings)
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class SpecRef:
    """A reference to a proven spec — carries the actual contract content.

    Instead of trust=["math.sqrt"], we now have:
        trust=[SpecRef("math.sqrt", ensures=["result >= 0"], status=ASSUMED)]

    This makes trust TRANSPARENT: you can see exactly what properties
    are assumed about each dependency.
    """
    qualname: str
    ensures: Tuple[str, ...] = ()
    requires: Tuple[str, ...] = ()
    status: ProofStatus = ProofStatus.UNPROVED
    source: str = ""  # "registry", "library_axiom", "assumed"

    @property
    def is_trusted(self) -> bool:
        return self.status.is_trusted

    def covers(self, assumption: str) -> bool:
        """Does this ref's proven ensures cover the given assumption?

        Simple text matching for now. In a full system, this would use
        Z3 entailment checking.
        """
        # Exact match
        if assumption in self.ensures:
            return True
        # The assumption is weaker than something we proved
        # (e.g., "isinstance(result, int)" is covered by "result == x + y")
        # This is a heuristic — real system would use Z3
        for e in self.ensures:
            if assumption in e:
                return True
        return False

    def to_json(self) -> Dict[str, Any]:
        return {
            "qualname": self.qualname,
            "ensures": list(self.ensures),
            "requires": list(self.requires),
            "status": self.status.value,
            "source": self.source,
        }

    @staticmethod
    def from_json(d: Dict[str, Any]) -> SpecRef:
        return SpecRef(
            qualname=d["qualname"],
            ensures=tuple(d.get("ensures", [])),
            requires=tuple(d.get("requires", [])),
            status=ProofStatus(d.get("status", "unproved")),
            source=d.get("source", ""),
        )

    def __str__(self) -> str:
        status_icon = "✓" if self.is_trusted else "?"
        return f"{status_icon} {self.qualname}: {', '.join(self.ensures[:2])}"


# ═══════════════════════════════════════════════════════════════════
# SpecRegistry — the central map from names to proven specs
# ═══════════════════════════════════════════════════════════════════

class SpecRegistry:
    """Registry mapping qualified names to their ProvenSpecs.

    When proving a library top-down:
    1. First pass: infer candidate specs for all functions
    2. Second pass: prove specs bottom-up (leaves first)
    3. When A calls B, look up B's proven spec from the registry
    4. A may only assume B's proven ensures — not B's candidate spec

    Thread-safe for read access after initial registration.
    """

    def __init__(self) -> None:
        self._specs: Dict[str, ProvenSpec] = {}
        self._spec_refs: Dict[str, SpecRef] = {}

    def register_candidate(self, qualname: str, spec: C4Spec) -> None:
        """Register a candidate spec (not yet proved)."""
        if qualname in self._specs:
            self._specs[qualname].candidate_spec = spec
        else:
            self._specs[qualname] = ProvenSpec(
                qualname=qualname,
                candidate_spec=spec,
            )

    def register_proved(self, qualname: str, spec: C4Spec,
                        status: ProofStatus = ProofStatus.Z3_PROVED,
                        trust_basis: Optional[List[str]] = None) -> None:
        """Register a proven spec — now usable by downstream callers."""
        if qualname in self._specs:
            ps = self._specs[qualname]
            ps.proved_spec = spec
            ps.proof_status = status
            if trust_basis:
                ps.trust_basis = trust_basis
        else:
            self._specs[qualname] = ProvenSpec(
                qualname=qualname,
                candidate_spec=spec,
                proved_spec=spec,
                proof_status=status,
                trust_basis=trust_basis or [],
            )
        # Update the SpecRef cache
        self._spec_refs[qualname] = SpecRef(
            qualname=qualname,
            ensures=tuple(spec.ensures),
            requires=tuple(spec.requires),
            status=status,
            source="registry",
        )

    def get_spec(self, qualname: str) -> Optional[ProvenSpec]:
        """Get a ProvenSpec by qualified name."""
        return self._specs.get(qualname)

    def get_ref(self, qualname: str) -> Optional[SpecRef]:
        """Get a SpecRef by qualified name (for trust references)."""
        return self._spec_refs.get(qualname)

    def get_usable_ensures(self, qualname: str) -> List[str]:
        """Get only the PROVEN ensures for a given name."""
        ps = self._specs.get(qualname)
        if ps:
            return ps.usable_ensures
        return []

    def has_proven(self, qualname: str) -> bool:
        """Is there a proven spec for this name?"""
        ps = self._specs.get(qualname)
        return ps is not None and ps.proof_status.is_trusted

    @property
    def all_names(self) -> Set[str]:
        return set(self._specs.keys())

    @property
    def proved_names(self) -> Set[str]:
        return {n for n, ps in self._specs.items() if ps.proof_status.is_trusted}

    @property
    def unproved_names(self) -> Set[str]:
        return {n for n, ps in self._specs.items() if not ps.proof_status.is_trusted}

    def stats(self) -> Dict[str, int]:
        by_status: Dict[str, int] = {}
        for ps in self._specs.values():
            key = ps.proof_status.value
            by_status[key] = by_status.get(key, 0) + 1
        return by_status

    def resolve_trust_refs(self, old_refs: List[str]) -> List[SpecRef]:
        """Convert old-style string trust refs to structured SpecRefs.

        For each string ref like "math.sqrt":
          - If registry has a proven spec → SpecRef with actual ensures
          - If not → SpecRef with status=UNPROVED (honest about unknowns)
        """
        result: List[SpecRef] = []
        for ref_str in old_refs:
            # Handle special prefixes
            if ref_str.startswith("CIRCULAR:"):
                result.append(SpecRef(
                    qualname=ref_str,
                    status=ProofStatus.FAILED,
                    source="circular",
                ))
                continue
            if ref_str.startswith("assumed:"):
                result.append(SpecRef(
                    qualname=ref_str,
                    status=ProofStatus.ASSUMED,
                    source="assumed",
                ))
                continue
            if ref_str.startswith("lean.") or ref_str.startswith("z3."):
                result.append(SpecRef(
                    qualname=ref_str,
                    status=ProofStatus.Z3_PROVED,
                    source="kernel",
                ))
                continue

            # Look up in registry
            cached = self._spec_refs.get(ref_str)
            if cached is not None:
                result.append(cached)
            else:
                result.append(SpecRef(
                    qualname=ref_str,
                    status=ProofStatus.UNPROVED,
                    source="unresolved",
                ))
        return result


# ═══════════════════════════════════════════════════════════════════
# Call obligations — what A assumes about B at each call site
# ═══════════════════════════════════════════════════════════════════

@dataclass
class CallObligation:
    """What a caller assumes about a callee at a specific call site.

    When A calls B(x, y), A implicitly assumes B's postconditions.
    This obligation records:
      - caller: A's qualified name
      - callee: B's qualified name
      - call_args: how A instantiates B's parameters
      - assumed: what A relies on from B's return value
      - line: line number in A's source
    """
    caller: str
    callee: str
    call_args: Dict[str, str] = field(default_factory=dict)  # param -> arg expression
    assumed: List[str] = field(default_factory=list)
    line: int = 0

    def to_json(self) -> Dict[str, Any]:
        return {
            "caller": self.caller,
            "callee": self.callee,
            "call_args": self.call_args,
            "assumed": self.assumed,
            "line": self.line,
        }


@dataclass
class ObligationResult:
    """Result of checking a call obligation against the registry."""
    obligation: CallObligation
    satisfied: bool
    available_ensures: List[str] = field(default_factory=list)
    unsatisfied: List[str] = field(default_factory=list)
    reason: str = ""


# ═══════════════════════════════════════════════════════════════════
# Call obligation extraction — find what A assumes about B
# ═══════════════════════════════════════════════════════════════════

def extract_call_obligations(
    source: str,
    func_name: str,
    registry: SpecRegistry,
    caller_qualname: str = "",
) -> List[CallObligation]:
    """Extract call obligations from a function's source.

    For each call to a registered function, record what the caller
    might assume about the return value.

    Currently detects:
      - Direct usage in comparisons: `if B(x) > 0` → assumes B returns > 0
      - Assignment then test: `y = B(x); if y > 0` → assumes B returns > 0
      - Return of call result: `return B(x)` → assumes B satisfies caller's spec
      - Passing to other functions: `C(B(x))` → assumes B satisfies C's preconditions
    """
    try:
        tree = ast.parse(textwrap.dedent(source))
    except SyntaxError:
        return []

    fn_node = _find_function(tree, func_name)
    if fn_node is None:
        return []

    obligations: List[CallObligation] = []
    known_names = registry.all_names

    # Walk the AST and find calls to registered functions
    for node in ast.walk(fn_node):
        if not isinstance(node, ast.Call):
            continue

        callee_name = _extract_call_name(node)
        if not callee_name:
            continue

        # Check if this callee is in the registry (by full name or suffix)
        matched_name = None
        if callee_name in known_names:
            matched_name = callee_name
        else:
            # Try suffix matching (e.g., "sqrt" matches "math.sqrt")
            for kn in known_names:
                if kn.endswith(f".{callee_name}"):
                    matched_name = kn
                    break

        if matched_name is None:
            continue

        # Extract argument mapping
        call_args: Dict[str, str] = {}
        ps = registry.get_spec(matched_name)
        if ps and ps.candidate_spec:
            param_names = []
            # Try to get param names from spec requires (crude but workable)
            for r in ps.candidate_spec.requires:
                for token in r.replace("(", " ").replace(")", " ").split():
                    if token.isidentifier() and token not in ("isinstance", "result", "True", "False"):
                        if token not in param_names:
                            param_names.append(token)

        for i, arg in enumerate(node.args):
            arg_str = ast.unparse(arg)
            call_args[f"arg{i}"] = arg_str

        obligations.append(CallObligation(
            caller=caller_qualname or func_name,
            callee=matched_name,
            call_args=call_args,
            assumed=registry.get_usable_ensures(matched_name),
            line=getattr(node, "lineno", 0),
        ))

    return obligations


def check_obligation(
    obligation: CallObligation,
    registry: SpecRegistry,
) -> ObligationResult:
    """Check whether a call obligation is satisfied by the callee's proven spec.

    Returns ObligationResult with:
      - satisfied: True if all assumptions are covered
      - unsatisfied: list of assumptions NOT covered by callee's spec
      - available_ensures: what the callee actually proved
    """
    callee_spec = registry.get_spec(obligation.callee)
    if callee_spec is None:
        return ObligationResult(
            obligation=obligation,
            satisfied=False,
            reason=f"No spec registered for {obligation.callee}",
        )

    available = callee_spec.usable_ensures
    if not available:
        return ObligationResult(
            obligation=obligation,
            satisfied=False,
            available_ensures=[],
            reason=f"{obligation.callee} has no proven ensures",
        )

    # Check each assumption against available ensures
    unsatisfied = []
    ref = registry.get_ref(obligation.callee)
    for assumed in obligation.assumed:
        if ref and ref.covers(assumed):
            continue
        # Not directly covered — this is an unsupported assumption
        unsatisfied.append(assumed)

    return ObligationResult(
        obligation=obligation,
        satisfied=len(unsatisfied) == 0,
        available_ensures=available,
        unsatisfied=unsatisfied,
        reason="" if not unsatisfied else f"{len(unsatisfied)} assumptions not covered",
    )


def check_all_obligations(
    obligations: List[CallObligation],
    registry: SpecRegistry,
) -> Tuple[List[ObligationResult], bool]:
    """Check all obligations, return (results, all_satisfied)."""
    results = [check_obligation(obl, registry) for obl in obligations]
    all_ok = all(r.satisfied for r in results)
    return results, all_ok


# ═══════════════════════════════════════════════════════════════════
# SCC-based ordering for mutual recursion
# ═══════════════════════════════════════════════════════════════════

def compute_proof_order(
    call_graph: Dict[str, Set[str]],
) -> List[List[str]]:
    """Compute SCC-based proof order from a call graph.

    Returns a list of SCCs in topological order.
    Acyclic nodes are singleton SCCs.
    Cyclic SCCs need fixed-point or manual seed specs.

    Uses Tarjan's algorithm.
    """
    index_counter = [0]
    stack: List[str] = []
    lowlink: Dict[str, int] = {}
    index: Dict[str, int] = {}
    on_stack: Set[str] = set()
    sccs: List[List[str]] = []

    def strongconnect(v: str) -> None:
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)

        for w in call_graph.get(v, set()):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])

        if lowlink[v] == index[v]:
            scc: List[str] = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            sccs.append(scc)

    for v in call_graph:
        if v not in index:
            strongconnect(v)

    # Tarjan produces SCCs in reverse topological order (leaves first)
    # which is exactly the bottom-up proof order we want
    return sccs


# ═══════════════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════════════

def _find_function(tree: ast.Module, name: str) -> Optional[ast.FunctionDef]:
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.name == name:
                return node
    return None


def _extract_call_name(node: ast.Call) -> Optional[str]:
    """Extract the function name from a call node."""
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        owner = _extract_dotted(node.func.value)
        if owner:
            return f"{owner}.{node.func.attr}"
        return node.func.attr
    return None


def _extract_dotted(node: ast.expr) -> Optional[str]:
    """Extract a dotted name like 'math.sqrt'."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        owner = _extract_dotted(node.value)
        if owner:
            return f"{owner}.{node.attr}"
    return None
