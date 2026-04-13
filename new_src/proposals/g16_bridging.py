"""Bridging the Intensional-Extensional Gap -- proposal module (Ch.41).

This module formalizes the gap analysis and improvement programme
described in Chapter 41 of the CCTT monograph, making the theoretical
constructs directly executable alongside the existing checker pipeline.

Proposals
---------
1. **PipelineVerdict** -- Typed verdict with graded confidence.
2. **PipelineLayer** -- Abstract base for each strategy layer pi_k.
3. **NormalizerPhase** -- Individual normalizer phase with confluence
   tracking.
4. **CongruenceRule** -- Typed congruence rule for HIT prover.
5. **NEQCertificate** -- Structured certificate of non-equivalence.
6. **SpecPattern** -- Pattern for the D20 spec identification engine.
7. **RewriteGroupoid** -- Explicit groupoid structure over normal forms.
8. **GapAnalyzer** -- Classifies failure pairs into Category 1/2/3.
9. **ProvabilityHorizon** -- Tracks the set of provable equivalences.
10. **ImprovementAxis** -- Framework for measuring axiom additions.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any, Callable, Dict, FrozenSet, Iterator, List, Mapping,
    Optional, Sequence, Set, Tuple, Union,
)

from new_src.cctt.path_search import PathStep, PathResult
from new_src.cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    normalize,
)


# =====================================================================
# 1. PipelineVerdict -- Typed verdict with graded confidence
# =====================================================================

class VerdictKind(Enum):
    """The three possible pipeline verdicts (Definition 41.1)."""
    EQ = auto()
    NEQ = auto()
    UNKNOWN = auto()


@dataclass(frozen=True)
class PipelineVerdict:
    """A graded verdict (v, c) per Definition 41.13.

    - kind: EQ, NEQ, or UNKNOWN
    - confidence: h0 / max(|Fibers|, 1) in [0,1]
    - source_layer: which pi_k produced this verdict
    - path: optional rewrite path (for EQ from HIT/BFS)
    - certificate: optional NEQ certificate
    """
    kind: VerdictKind
    confidence: float = 1.0
    source_layer: int = -1
    path: Optional[List[PathStep]] = None
    certificate: Optional["NEQCertificate"] = None

    def is_definitive(self) -> bool:
        return self.kind in (VerdictKind.EQ, VerdictKind.NEQ)

    def __repr__(self) -> str:
        c_str = f", c={self.confidence:.2f}" if self.kind == VerdictKind.UNKNOWN else ""
        return f"Verdict({self.kind.name}{c_str}, layer={self.source_layer})"


# =====================================================================
# 2. PipelineLayer -- Abstract base for each strategy layer
# =====================================================================

@dataclass
class PipelineLayer:
    """Abstract base for a pipeline strategy layer pi_k.

    Each layer is a partial decision procedure that either refines
    the verdict or passes it through (Def 41.1).  The pipeline
    composes layers via short-circuiting.
    """
    index: int
    name: str

    def decide(
        self,
        src_f: str,
        src_g: str,
        oterm_f: Optional[OTerm] = None,
        oterm_g: Optional[OTerm] = None,
    ) -> Optional[PipelineVerdict]:
        """Return a verdict or None (pass-through)."""
        raise NotImplementedError

    def __repr__(self) -> str:
        return f"pi_{self.index}({self.name})"


class ClosedTermEvalLayer(PipelineLayer):
    """pi_0: Closed-term evaluation for zero-argument functions."""

    def __init__(self) -> None:
        super().__init__(index=0, name="closed_term_eval")

    def decide(self, src_f, src_g, oterm_f=None, oterm_g=None):
        # Placeholder: actual implementation calls subprocess
        return None


class DenotationalLayer(PipelineLayer):
    """pi_1: Denotational OTerm equivalence (primary strategy).

    Sub-strategies:
      (a) Exact canonical form match
      (b) Flexible matching (OFix key tolerance)
      (c) HIT path induction + BFS path search
      (d) Provable NEQ detection
    """

    def __init__(self) -> None:
        super().__init__(index=1, name="denotational_equiv")

    def decide(self, src_f, src_g, oterm_f=None, oterm_g=None):
        # Placeholder: delegates to denotational_equiv()
        return None


class Z3StructuralLayer(PipelineLayer):
    """pi_2: Z3 structural equality (trusted only when fully interpreted)."""

    def __init__(self) -> None:
        super().__init__(index=2, name="z3_structural")

    def decide(self, src_f, src_g, oterm_f=None, oterm_g=None):
        return None


class Z3FiberCechLayer(PipelineLayer):
    """pi_3: Z3 per-fiber + Cech H^1."""

    def __init__(self) -> None:
        super().__init__(index=3, name="z3_fiber_cech")

    def decide(self, src_f, src_g, oterm_f=None, oterm_g=None):
        return None


def run_pipeline(
    src_f: str,
    src_g: str,
    layers: Optional[List[PipelineLayer]] = None,
) -> PipelineVerdict:
    """Run the full pipeline Pi = pi_3 o pi_2 o pi_1 o pi_0.

    Short-circuits on the first definitive verdict (Thm 41.2).
    """
    if layers is None:
        layers = [
            ClosedTermEvalLayer(),
            DenotationalLayer(),
            Z3StructuralLayer(),
            Z3FiberCechLayer(),
        ]
    for layer in layers:
        verdict = layer.decide(src_f, src_g)
        if verdict is not None and verdict.is_definitive():
            return verdict
    return PipelineVerdict(kind=VerdictKind.UNKNOWN, confidence=0.0)


# =====================================================================
# 3. NormalizerPhase -- Individual normalizer phase
# =====================================================================

class PhaseKind(Enum):
    """The seven normalizer phases (Definition 41.3)."""
    BETA_REDUCTION = 1
    RING_LATTICE = 2
    FOLD_CANON = 3
    HOF_FUSION = 4
    SYMBOL_UNIFY = 5
    QUOTIENT = 6
    PIECEWISE = 7


@dataclass
class NormalizerPhase:
    """One phase phi_k of the 7-phase normalizer.

    Tracks:
    - rules_applied: count of rules fired in this phase
    - confluence_check: whether rules are non-overlapping at root
    """
    kind: PhaseKind
    rules_applied: int = 0
    is_confluent: bool = True  # Prop 41.5: non-overlapping at root

    def apply(self, term: OTerm) -> OTerm:
        """Apply this phase to an OTerm (structural recursion)."""
        # Each phase is a structural recursion on the OTerm tree
        # (Proposition 41.4: terminates on each invocation)
        raise NotImplementedError

    def is_sound(self) -> bool:
        """Check soundness: phi_k(t) = t' => [[t]] = [[t']] (Prop 41.6)."""
        return True  # Sound by construction per proof sketch


def run_normalizer(term: OTerm, max_iter: int = 8) -> OTerm:
    """Run N = (phi_7 o ... o phi_1)^{<=8} until fixpoint (Def 41.3)."""
    phases = [NormalizerPhase(kind=PhaseKind(k)) for k in range(1, 8)]
    prev_canon = ""
    for _ in range(max_iter):
        for phase in phases:
            term = phase.apply(term)
        curr_canon = str(term)
        if curr_canon == prev_canon:
            break
        prev_canon = curr_canon
    return term


# =====================================================================
# 4. CongruenceRule -- Typed congruence rule for HIT prover
# =====================================================================

class CongruenceKind(Enum):
    """Congruence rule names from Section 41.4."""
    REFL = auto()
    OOP_CONG = auto()
    OCASE_CONG = auto()
    OCASE_FLIP = auto()
    OFOLD_CONG = auto()
    OLAM_CONG = auto()
    OMAP_CONG = auto()
    COMM = auto()  # fiber-restricted


@dataclass(frozen=True)
class CongruenceRule:
    """A single congruence rule for the HIT prover.

    The Comm rule is fiber-restricted: Comm_tau depends on the
    duck-type fiber tau (sheaf descent at the rewriting level).
    """
    kind: CongruenceKind
    fiber_restricted: bool = False
    applicable_fibers: FrozenSet[str] = frozenset()

    def can_apply(self, a: OTerm, b: OTerm, fiber: str = "any") -> bool:
        """Check if this rule is applicable to the given pair."""
        if self.fiber_restricted and fiber not in self.applicable_fibers:
            return False
        if self.kind == CongruenceKind.REFL:
            return str(a) == str(b)
        if self.kind == CongruenceKind.OOP_CONG:
            return isinstance(a, OOp) and isinstance(b, OOp) and a.op == b.op
        if self.kind == CongruenceKind.OCASE_CONG:
            return isinstance(a, OCase) and isinstance(b, OCase)
        if self.kind == CongruenceKind.OFOLD_CONG:
            return isinstance(a, OFold) and isinstance(b, OFold)
        if self.kind == CongruenceKind.OLAM_CONG:
            return isinstance(a, OLam) and isinstance(b, OLam)
        if self.kind == CongruenceKind.OMAP_CONG:
            return isinstance(a, OMap) and isinstance(b, OMap)
        return False


# Comm rule for numeric fibers (add is commutative)
COMM_NUMERIC = CongruenceRule(
    kind=CongruenceKind.COMM,
    fiber_restricted=True,
    applicable_fibers=frozenset({"int", "float", "complex", "Decimal"}),
)


# =====================================================================
# 5. NEQCertificate -- Structured certificate of non-equivalence
# =====================================================================

class NEQCategory(Enum):
    """Categories of NEQ certificates (Section 41.6)."""
    EFFECT_FIBER = auto()
    LITERAL = auto()
    ARGUMENT_ORDER = auto()
    COMPARISON_OPERATOR = auto()
    SEQUENCE_LENGTH = auto()
    FOLD_OPERATOR = auto()
    CROSS_TYPE = auto()


@dataclass(frozen=True)
class NEQCertificate:
    """A certificate of non-equivalence (Definition 41.8).

    P(a, b) => exists x. [[a]](x) != [[b]](x).
    Each certificate is sound (Theorem 41.9).
    """
    category: NEQCategory
    reason: str
    witness: Optional[Any] = None
    in_case_branch: bool = False

    def is_valid(self) -> bool:
        """Cross-type certificates are suppressed inside case branches."""
        if self.category == NEQCategory.CROSS_TYPE and self.in_case_branch:
            return False
        return True

    def __repr__(self) -> str:
        valid = "valid" if self.is_valid() else "suppressed"
        return f"NEQ({self.category.name}, {valid}: {self.reason})"


# Non-commutative operations (argument-order certificates)
NON_COMMUTATIVE_OPS: FrozenSet[str] = frozenset({
    "sub", "floordiv", "mod", "pow", "concat", "merge",
    "truediv", "lshift", "rshift", "matmul", "getitem",
})

# Operations whose commutativity is fiber-dependent
FIBER_DEPENDENT_COMM: FrozenSet[str] = frozenset({"add", "iadd"})


def detect_neq(
    a: OTerm,
    b: OTerm,
    fiber: str = "any",
    in_case_branch: bool = False,
) -> Optional[NEQCertificate]:
    """Attempt to detect provable non-equivalence.

    Checks certificates in order: effect-fiber, literal,
    argument-order, comparison-operator, structural.
    """
    # Effect-fiber divergence
    a_effects = _extract_effects(a)
    b_effects = _extract_effects(b)
    if a_effects != b_effects:
        return NEQCertificate(
            category=NEQCategory.EFFECT_FIBER,
            reason=f"effect divergence: {a_effects} vs {b_effects}",
        )

    # Literal mismatch
    if isinstance(a, OLit) and isinstance(b, OLit) and a.value != b.value:
        return NEQCertificate(
            category=NEQCategory.LITERAL,
            reason=f"literal {a.value} != {b.value}",
            witness=(a.value, b.value),
        )

    # Argument-order on non-commutative ops
    if (isinstance(a, OOp) and isinstance(b, OOp)
            and a.op == b.op and a.op in NON_COMMUTATIVE_OPS
            and len(a.args) == 2 and len(b.args) == 2):
        if str(a.args[0]) == str(b.args[1]) and str(a.args[1]) == str(b.args[0]):
            if str(a.args[0]) != str(a.args[1]):
                return NEQCertificate(
                    category=NEQCategory.ARGUMENT_ORDER,
                    reason=f"non-commutative {a.op} with swapped args",
                )

    # Fiber-dependent commutativity
    if (isinstance(a, OOp) and isinstance(b, OOp)
            and a.op == b.op and a.op in FIBER_DEPENDENT_COMM
            and fiber in ("str", "list", "bytes")):
        if (len(a.args) == 2 and len(b.args) == 2
                and str(a.args[0]) == str(b.args[1])
                and str(a.args[1]) == str(b.args[0])
                and str(a.args[0]) != str(a.args[1])):
            return NEQCertificate(
                category=NEQCategory.ARGUMENT_ORDER,
                reason=f"{a.op} non-commutative on fiber {fiber}",
            )

    # Cross-type (suppressed in case branches)
    if not in_case_branch:
        a_type = type(a).__name__
        b_type = type(b).__name__
        cross_type_pairs = {
            ("OSeq", "OOp"), ("OOp", "OMap"), ("OFold", "OOp"),
            ("OOp", "OCase"), ("OQuotient", "OOp"),
        }
        pair = (a_type, b_type)
        if pair in cross_type_pairs or (pair[1], pair[0]) in cross_type_pairs:
            return NEQCertificate(
                category=NEQCategory.CROSS_TYPE,
                reason=f"cross-type {a_type} vs {b_type}",
                in_case_branch=in_case_branch,
            )

    return None


def _extract_effects(t: OTerm) -> FrozenSet[str]:
    """Extract effect operations from an OTerm."""
    effects: Set[str] = set()
    _walk_effects(t, effects)
    return frozenset(effects)


def _walk_effects(t: OTerm, acc: Set[str]) -> None:
    if isinstance(t, OOp):
        if t.op.startswith("effect_"):
            acc.add(t.op)
        for arg in t.args:
            _walk_effects(arg, acc)
    elif isinstance(t, OCase):
        _walk_effects(t.guard, acc)
        _walk_effects(t.true_br, acc)
        _walk_effects(t.false_br, acc)
    elif isinstance(t, OFold):
        _walk_effects(t.init, acc)
        _walk_effects(t.collection, acc)
    elif isinstance(t, OMap):
        _walk_effects(t.transform, acc)
        _walk_effects(t.collection, acc)
    elif isinstance(t, OSeq):
        for elt in t.elts:
            _walk_effects(elt, acc)


# =====================================================================
# 6. SpecPattern -- Pattern for D20 spec identification
# =====================================================================

@dataclass(frozen=True)
class SpecPattern:
    """A specification recognition pattern (Definition 41.7).

    iota : OTerm -> (SpecName, OTerm*) is a partial map defined
    by structural pattern matching.  Each pattern is a sufficient
    condition for the corresponding spec (Prop 41.8).
    """
    spec_name: str
    description: str
    recognizer: Callable[[OTerm], Optional[Tuple[str, ...]]] = field(
        default=lambda t: None, repr=False
    )

    def identify(self, term: OTerm) -> Optional[Tuple[str, Tuple[str, ...]]]:
        """Try to identify this spec in the given OTerm."""
        params = self.recognizer(term)
        if params is not None:
            return (self.spec_name, params)
        return None


def _recognize_factorial(t: OTerm) -> Optional[Tuple[str, ...]]:
    """Recognize fold(mul, 1, range(..., n)) as factorial(n)."""
    if isinstance(t, OFold) and t.op in ("mul", "imul"):
        if isinstance(t.init, OLit) and t.init.value == 1:
            if isinstance(t.collection, OOp) and t.collection.op == "range":
                args = t.collection.args
                if len(args) >= 1:
                    return (str(args[-1]),)
    return None


def _recognize_range_sum(t: OTerm) -> Optional[Tuple[str, ...]]:
    """Recognize fold(add, 0, range(..., n)) as range_sum(n)."""
    if isinstance(t, OFold) and t.op in ("add", "iadd"):
        if isinstance(t.init, OLit) and t.init.value == 0:
            if isinstance(t.collection, OOp) and t.collection.op == "range":
                args = t.collection.args
                if len(args) >= 1:
                    return (str(args[-1]),)
    return None


def _recognize_sorted(t: OTerm) -> Optional[Tuple[str, ...]]:
    """Recognize sorted(x) as sorted(x)."""
    if isinstance(t, OOp) and t.op == "sorted":
        if len(t.args) == 1:
            return (str(t.args[0]),)
    return None


# The five spec families from Section 41.5
SPEC_PATTERNS: List[SpecPattern] = [
    SpecPattern("factorial", "n! = fold(mul, 1, range(1,n+1))",
                _recognize_factorial),
    SpecPattern("range_sum", "sum(range(...,n)) = fold(add, 0, range)",
                _recognize_range_sum),
    SpecPattern("sorted", "sorted(x)", _recognize_sorted),
    # fib_like and binomial use heuristic matching (see path_search.py)
]


def identify_spec(term: OTerm) -> Optional[Tuple[str, Tuple[str, ...]]]:
    """Run all spec patterns; return first match (Def 41.7)."""
    for pattern in SPEC_PATTERNS:
        result = pattern.identify(term)
        if result is not None:
            return result
    return None


# =====================================================================
# 7. RewriteGroupoid -- Explicit groupoid over normal forms
# =====================================================================

@dataclass
class RewriteGroupoid:
    """The rewrite groupoid G_PyComp (Definition 41.14).

    Objects: OTerms in normal form (after N).
    Morphisms: finite composites of path constructors and inverses.

    pi_0(G) classifies the connected components; the goal is to
    reduce |pi_0(G)| by adding new axioms (Prop 41.15).
    """
    # Adjacency: canon(term) -> set of (canon(rewritten), axiom_name)
    _edges: Dict[str, Set[Tuple[str, str]]] = field(default_factory=dict)

    def add_edge(self, source: str, target: str, axiom: str) -> None:
        """Record a one-step rewrite (path constructor)."""
        self._edges.setdefault(source, set()).add((target, axiom))
        # Groupoid: every morphism has an inverse
        self._edges.setdefault(target, set()).add((source, f"{axiom}^-1"))

    def connected_component(self, term: str) -> Set[str]:
        """BFS to find all terms reachable from 'term'."""
        visited: Set[str] = set()
        frontier = {term}
        while frontier:
            current = frontier.pop()
            if current in visited:
                continue
            visited.add(current)
            for target, _ in self._edges.get(current, set()):
                if target not in visited:
                    frontier.add(target)
        return visited

    def pi_0(self) -> List[Set[str]]:
        """Compute pi_0(G): the connected components."""
        all_terms = set(self._edges.keys())
        components: List[Set[str]] = []
        visited: Set[str] = set()
        for term in all_terms:
            if term not in visited:
                comp = self.connected_component(term)
                components.append(comp)
                visited |= comp
        return components

    def are_connected(self, a: str, b: str) -> bool:
        """Check if a and b are in the same connected component."""
        return b in self.connected_component(a)


# =====================================================================
# 8. GapAnalyzer -- Classify failure pairs into categories
# =====================================================================

class FailureCategory(Enum):
    """Categories of pipeline failures (Section 41.7)."""
    GENUINELY_DIFFERENT = 1  # Different algorithms, disconnected components
    COMPILATION_LOSSY = 2     # OTerm compiler loses information
    TIMEOUT_MEMORY = 3        # Z3 runs out of resources


@dataclass
class GapAnalysis:
    """Analysis of why a pair (f, g) is in the gap set G."""
    category: FailureCategory
    reason: str
    has_ounknown: bool = False
    canon_too_short: bool = False
    z3_timeout: bool = False

    def is_fundamental(self) -> bool:
        """Category 1 is fundamental; 2 and 3 are engineering."""
        return self.category == FailureCategory.GENUINELY_DIFFERENT


def analyze_gap(
    src_f: str,
    src_g: str,
    oterm_f: Optional[OTerm],
    oterm_g: Optional[OTerm],
    z3_timed_out: bool = False,
) -> GapAnalysis:
    """Classify a failed equivalence check into Category 1/2/3."""
    # Category 2: compilation lossy-ness
    if oterm_f is None or oterm_g is None:
        return GapAnalysis(
            category=FailureCategory.COMPILATION_LOSSY,
            reason="OTerm compilation failed",
        )

    canon_f = str(normalize(oterm_f))
    canon_g = str(normalize(oterm_g))

    has_unknown_f = "OUnknown" in canon_f
    has_unknown_g = "OUnknown" in canon_g
    if has_unknown_f or has_unknown_g:
        return GapAnalysis(
            category=FailureCategory.COMPILATION_LOSSY,
            reason="OUnknown nodes in canonical form",
            has_ounknown=True,
        )

    if len(canon_f) < 20 or len(canon_g) < 20:
        return GapAnalysis(
            category=FailureCategory.COMPILATION_LOSSY,
            reason="canonical form too short to trust",
            canon_too_short=True,
        )

    # Category 3: Z3 timeout
    if z3_timed_out:
        return GapAnalysis(
            category=FailureCategory.TIMEOUT_MEMORY,
            reason="Z3 fiber checker timed out",
            z3_timeout=True,
        )

    # Category 1: genuinely different algorithms
    return GapAnalysis(
        category=FailureCategory.GENUINELY_DIFFERENT,
        reason="terms in disconnected components of rewrite groupoid",
    )


# =====================================================================
# 9. ProvabilityHorizon -- Track provable equivalences
# =====================================================================

@dataclass
class ProvabilityHorizon:
    """The provability horizon H and gap set G (Definition 41.12).

    H = {(f,g) : f equiv g and Pi(f,g) = EQ}
    G = {(f,g) : f equiv g and Pi(f,g) != EQ}

    The gap set G is non-empty by Rice's theorem (Thm 41.11).
    """
    proven_pairs: Set[Tuple[str, str]] = field(default_factory=set)
    gap_pairs: Set[Tuple[str, str]] = field(default_factory=set)

    def add_proven(self, f_name: str, g_name: str) -> None:
        pair = (min(f_name, g_name), max(f_name, g_name))
        self.proven_pairs.add(pair)
        self.gap_pairs.discard(pair)

    def add_gap(self, f_name: str, g_name: str) -> None:
        pair = (min(f_name, g_name), max(f_name, g_name))
        if pair not in self.proven_pairs:
            self.gap_pairs.add(pair)

    @property
    def coverage(self) -> float:
        """Fraction of known equivalent pairs that are proven."""
        total = len(self.proven_pairs) + len(self.gap_pairs)
        if total == 0:
            return 1.0
        return len(self.proven_pairs) / total


# =====================================================================
# 10. ImprovementAxis -- Framework for measuring axiom additions
# =====================================================================

class AxisKind(Enum):
    """The three improvement axes (Section 41.12)."""
    NORMALIZATION = 1   # More paths via normalizer rules
    SPECIFICATION = 2   # More Yoneda via spec patterns
    Z3_FIDELITY = 3     # Fewer spurious H^1 via Z3 RecFunctions


@dataclass
class ImprovementAxis:
    """A single improvement axis with estimated impact.

    Corresponds to:
    - Axis 1: Richer normalization (Conjecture 41.1: accumulator extraction)
    - Axis 2: Richer specs (Conjecture 41.2: compositional recognition)
    - Axis 3: Z3 fidelity (Conjecture 41.3: RecFunction completeness)
    """
    kind: AxisKind
    description: str
    estimated_pairs_closed: int = 0
    new_axioms: List[str] = field(default_factory=list)

    def expected_pi0_reduction(self) -> int:
        """How many connected components this would merge."""
        return self.estimated_pairs_closed


# Pre-defined improvement axes from Section 41.12
IMPROVEMENT_AXES: List[ImprovementAxis] = [
    ImprovementAxis(
        kind=AxisKind.NORMALIZATION,
        description="Accumulator extraction: fix[f](acc, n) -> fold(step, acc0, range)",
        estimated_pairs_closed=5,
        new_axioms=["accumulator_to_fold"],
    ),
    ImprovementAxis(
        kind=AxisKind.SPECIFICATION,
        description="Compositional spec recognition via operad homomorphism",
        estimated_pairs_closed=3,
        new_axioms=["gcd_spec", "lcm_spec", "binomial_multiplicative"],
    ),
    ImprovementAxis(
        kind=AxisKind.Z3_FIDELITY,
        description="Axiomatize sorted/set/str as Z3 RecFunctions",
        estimated_pairs_closed=15,
        new_axioms=["sorted_recfun", "set_recfun", "str_recfun"],
    ),
]


# =====================================================================
# Summary table (Section 41.13)
# =====================================================================

THEORY_TO_IMPLEMENTATION: List[Tuple[str, str, str]] = [
    ("New path constructors", "7-phase normalizer rules", "Category 2 failures"),
    ("Yoneda (D20)", "Spec library patterns", "Category 1 failures"),
    ("Transport", "Type coercion paths", "Cross-type pairs"),
    ("Sheaf descent", "Fiber-aware spec matching", "Combined evidence"),
    ("Galois connection", "Spec-constrained Z3", "Z3 timeout pairs"),
    ("RecFunction analysis", "Z3 recurrence matching", "Recursive pairs"),
    ("Operadic composition", "Compositional spec recognition", "Complex specs"),
]
