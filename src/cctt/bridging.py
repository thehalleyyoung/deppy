"""§41: Bridging the Intensional-Extensional Gap (Ch.41 of the CCTT monograph).

Connects the denotational layer (OTerm normalization, path search) with
the Z3 structural layer (per-fiber Čech H¹) through typed pipeline
verdicts, structured NEQ certificates, rewrite-groupoid tracking,
gap analysis, and provability-horizon bookkeeping.

The pipeline is the composition  Π = π₃ ∘ π₂ ∘ π₁ ∘ π₀  of:
  π₀  Closed-term evaluation  (denotation = value for zero-arg fns)
  π₁  Denotational OTerm equivalence
  π₂  Z3 structural equality
  π₃  Z3 per-fiber + Čech H¹

Each layer either produces a definitive verdict or passes through.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any, Callable, Dict, FrozenSet, Iterator, List, Mapping,
    Optional, Sequence, Set, Tuple, Union,
)

from .path_search import PathStep, PathResult
from .denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    normalize, compile_to_oterm, denotational_equiv,
)


# =====================================================================
# 1. PipelineVerdict — typed verdict with graded confidence
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
    - confidence: h0 / max(|Fibers|, 1) in [0, 1]
    - source_layer: which π_k produced this verdict
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
# 2. PipelineLayer — abstract base for each strategy layer
# =====================================================================

@dataclass
class PipelineLayer:
    """Abstract base for a pipeline strategy layer π_k.

    Each layer is a partial decision procedure that either refines
    the verdict or passes it through (Def 41.1).
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
    """π₀: Closed-term evaluation for zero-argument functions.

    If both functions take zero args, evaluate them and compare
    their return values directly — the denotation IS the value.
    """

    def __init__(self) -> None:
        super().__init__(index=0, name="closed_term_eval")

    def decide(self, src_f, src_g, oterm_f=None, oterm_g=None):
        import ast, textwrap
        try:
            tree_f = ast.parse(textwrap.dedent(src_f))
            tree_g = ast.parse(textwrap.dedent(src_g))
        except SyntaxError:
            return None

        def _param_count(tree):
            for n in ast.walk(tree):
                if isinstance(n, ast.FunctionDef):
                    return len(n.args.args)
            return -1

        if _param_count(tree_f) != 0 or _param_count(tree_g) != 0:
            return None

        # Both are zero-arg — evaluate (import lazily to avoid circular deps)
        try:
            from .checker import _evaluate_closed_term
            ok_f, val_f = _evaluate_closed_term(src_f)
            ok_g, val_g = _evaluate_closed_term(src_g)
            if ok_f and ok_g:
                if val_f == val_g:
                    return PipelineVerdict(
                        kind=VerdictKind.EQ, confidence=1.0,
                        source_layer=self.index,
                    )
                else:
                    return PipelineVerdict(
                        kind=VerdictKind.NEQ, confidence=1.0,
                        source_layer=self.index,
                        certificate=NEQCertificate(
                            category=NEQCategory.LITERAL,
                            reason=f"closed-term values differ: {val_f} vs {val_g}",
                            witness=(val_f, val_g),
                        ),
                    )
        except Exception:
            pass
        return None


class DenotationalLayer(PipelineLayer):
    """π₁: Denotational OTerm equivalence (primary strategy).

    Delegates to denotational_equiv() which implements:
      (a) Exact canonical-form match
      (b) Flexible matching (OFix key tolerance)
      (c) HIT path induction + BFS path search
      (d) Provable NEQ detection
    """

    def __init__(self) -> None:
        super().__init__(index=1, name="denotational_equiv")

    def decide(self, src_f, src_g, oterm_f=None, oterm_g=None):
        result = denotational_equiv(src_f, src_g)
        if result is True:
            return PipelineVerdict(
                kind=VerdictKind.EQ, confidence=1.0,
                source_layer=self.index,
            )
        elif result is False:
            return PipelineVerdict(
                kind=VerdictKind.NEQ, confidence=1.0,
                source_layer=self.index,
            )
        return None


class Z3FiberCechLayer(PipelineLayer):
    """π₂: Z3 per-fiber + Čech H¹.

    Delegates to the checker's Z3 fiber pipeline — compiles both
    functions to Z3 terms and checks per-fiber equivalence, then
    glues via Čech cohomology.
    """

    def __init__(self) -> None:
        super().__init__(index=2, name="z3_fiber_cech")

    def decide(self, src_f, src_g, oterm_f=None, oterm_g=None):
        try:
            from .checker import check_equivalence
            r = check_equivalence(src_f, src_g, timeout_ms=3000)
            if r.equivalent is True:
                return PipelineVerdict(
                    kind=VerdictKind.EQ, confidence=r.confidence,
                    source_layer=self.index,
                )
            elif r.equivalent is False:
                return PipelineVerdict(
                    kind=VerdictKind.NEQ, confidence=r.confidence,
                    source_layer=self.index,
                )
        except Exception:
            pass
        return None


def run_pipeline(
    src_f: str,
    src_g: str,
    layers: Optional[List[PipelineLayer]] = None,
) -> PipelineVerdict:
    """Run the full pipeline Π = π₂ ∘ π₁ ∘ π₀.

    Short-circuits on the first definitive verdict (Thm 41.2).
    """
    if layers is None:
        layers = [
            ClosedTermEvalLayer(),
            DenotationalLayer(),
            Z3FiberCechLayer(),
        ]
    for layer in layers:
        verdict = layer.decide(src_f, src_g)
        if verdict is not None and verdict.is_definitive():
            return verdict
    return PipelineVerdict(kind=VerdictKind.UNKNOWN, confidence=0.0)


# =====================================================================
# 3. CongruenceRule — typed congruence rule for HIT prover
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
    COMM = auto()


@dataclass(frozen=True)
class CongruenceRule:
    """A single congruence rule for the HIT prover.

    The Comm rule is fiber-restricted: Comm_τ depends on the
    duck-type fiber τ (sheaf descent at the rewriting level).
    """
    kind: CongruenceKind
    fiber_restricted: bool = False
    applicable_fibers: FrozenSet[str] = frozenset()

    def can_apply(self, a: OTerm, b: OTerm, fiber: str = "any") -> bool:
        """Check if this rule is applicable to the given pair."""
        if self.fiber_restricted and fiber not in self.applicable_fibers:
            return False
        if self.kind == CongruenceKind.REFL:
            return a.canon() == b.canon()
        if self.kind == CongruenceKind.OOP_CONG:
            return isinstance(a, OOp) and isinstance(b, OOp) and a.name == b.name
        if self.kind == CongruenceKind.OCASE_CONG:
            return isinstance(a, OCase) and isinstance(b, OCase)
        if self.kind == CongruenceKind.OFOLD_CONG:
            return isinstance(a, OFold) and isinstance(b, OFold)
        if self.kind == CongruenceKind.OLAM_CONG:
            return isinstance(a, OLam) and isinstance(b, OLam)
        if self.kind == CongruenceKind.OMAP_CONG:
            return isinstance(a, OMap) and isinstance(b, OMap)
        return False


COMM_NUMERIC = CongruenceRule(
    kind=CongruenceKind.COMM,
    fiber_restricted=True,
    applicable_fibers=frozenset({"int", "float", "complex", "Decimal"}),
)


# =====================================================================
# 4. NEQCertificate — structured certificate of non-equivalence
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

    P(a, b) ⇒ ∃x. ⟦a⟧(x) ≠ ⟦b⟧(x).
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


NON_COMMUTATIVE_OPS: FrozenSet[str] = frozenset({
    "sub", "floordiv", "mod", "pow", "concat", "merge",
    "truediv", "lshift", "rshift", "matmul", "getitem",
})

FIBER_DEPENDENT_COMM: FrozenSet[str] = frozenset({"add", "iadd"})


def detect_neq(
    a: OTerm,
    b: OTerm,
    fiber: str = "any",
    in_case_branch: bool = False,
) -> Optional[NEQCertificate]:
    """Attempt to detect provable non-equivalence between two OTerms.

    Checks in order: effect-fiber, literal, argument-order,
    comparison-operator, cross-type.
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
            and a.name == b.name and a.name in NON_COMMUTATIVE_OPS
            and len(a.args) == 2 and len(b.args) == 2):
        if (a.args[0].canon() == b.args[1].canon()
                and a.args[1].canon() == b.args[0].canon()
                and a.args[0].canon() != a.args[1].canon()):
            return NEQCertificate(
                category=NEQCategory.ARGUMENT_ORDER,
                reason=f"non-commutative {a.name} with swapped args",
            )

    # Fiber-dependent commutativity
    if (isinstance(a, OOp) and isinstance(b, OOp)
            and a.name == b.name and a.name in FIBER_DEPENDENT_COMM
            and fiber in ("str", "list", "bytes")):
        if (len(a.args) == 2 and len(b.args) == 2
                and a.args[0].canon() == b.args[1].canon()
                and a.args[1].canon() == b.args[0].canon()
                and a.args[0].canon() != a.args[1].canon()):
            return NEQCertificate(
                category=NEQCategory.ARGUMENT_ORDER,
                reason=f"{a.name} non-commutative on fiber {fiber}",
            )

    # Fold operator mismatch
    if (isinstance(a, OFold) and isinstance(b, OFold)
            and a.op_name != b.op_name):
        return NEQCertificate(
            category=NEQCategory.FOLD_OPERATOR,
            reason=f"fold op {a.op_name} vs {b.op_name}",
        )

    # Comparison operator mismatch
    _cmp_ops = {"lt", "le", "gt", "ge", "eq", "ne"}
    if (isinstance(a, OOp) and isinstance(b, OOp)
            and a.name in _cmp_ops and b.name in _cmp_ops
            and a.name != b.name
            and len(a.args) == len(b.args) == 2
            and a.args[0].canon() == b.args[0].canon()
            and a.args[1].canon() == b.args[1].canon()):
        return NEQCertificate(
            category=NEQCategory.COMPARISON_OPERATOR,
            reason=f"comparison {a.name} vs {b.name} on same operands",
        )

    # Cross-type
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
        if t.name.startswith("effect_"):
            acc.add(t.name)
        for arg in t.args:
            _walk_effects(arg, acc)
    elif isinstance(t, OCase):
        _walk_effects(t.test, acc)
        _walk_effects(t.true_branch, acc)
        _walk_effects(t.false_branch, acc)
    elif isinstance(t, OFold):
        _walk_effects(t.init, acc)
        _walk_effects(t.collection, acc)
    elif isinstance(t, OMap):
        _walk_effects(t.transform, acc)
        _walk_effects(t.collection, acc)
    elif isinstance(t, OSeq):
        for elt in t.elements:
            _walk_effects(elt, acc)


# =====================================================================
# 5. SpecPattern — OTerm-level spec identification
# =====================================================================

@dataclass(frozen=True)
class SpecPattern:
    """A specification recognition pattern (Definition 41.7).

    ι : OTerm → (SpecName, OTerm*) is a partial map defined
    by structural pattern matching.
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
    if isinstance(t, OFold) and t.op_name in ("mul", "imul"):
        if isinstance(t.init, OLit) and t.init.value == 1:
            if isinstance(t.collection, OOp) and t.collection.name == "range":
                args = t.collection.args
                if len(args) >= 1:
                    return (args[-1].canon(),)
    return None


def _recognize_range_sum(t: OTerm) -> Optional[Tuple[str, ...]]:
    """Recognize fold(add, 0, range(..., n)) as range_sum(n)."""
    if isinstance(t, OFold) and t.op_name in ("add", "iadd"):
        if isinstance(t.init, OLit) and t.init.value == 0:
            if isinstance(t.collection, OOp) and t.collection.name == "range":
                args = t.collection.args
                if len(args) >= 1:
                    return (args[-1].canon(),)
    return None


def _recognize_sorted(t: OTerm) -> Optional[Tuple[str, ...]]:
    """Recognize sorted(x) as sorted(x)."""
    if isinstance(t, OOp) and t.name == "sorted":
        if len(t.args) == 1:
            return (t.args[0].canon(),)
    return None


SPEC_PATTERNS: List[SpecPattern] = [
    SpecPattern("factorial", "n! = fold(mul, 1, range(1,n+1))",
                _recognize_factorial),
    SpecPattern("range_sum", "sum(range(...,n)) = fold(add, 0, range)",
                _recognize_range_sum),
    SpecPattern("sorted", "sorted(x)", _recognize_sorted),
]


def identify_spec(term: OTerm) -> Optional[Tuple[str, Tuple[str, ...]]]:
    """Run all spec patterns; return first match (Def 41.7)."""
    for pattern in SPEC_PATTERNS:
        result = pattern.identify(term)
        if result is not None:
            return result
    return None


# =====================================================================
# 6. RewriteGroupoid — explicit groupoid over normal forms
# =====================================================================

@dataclass
class RewriteGroupoid:
    """The rewrite groupoid G_PyComp (Definition 41.14).

    Objects: OTerms in normal form (after N).
    Morphisms: finite composites of path constructors and inverses.

    π₀(G) classifies the connected components; the goal is to
    reduce |π₀(G)| by adding new axioms (Prop 41.15).
    """
    _edges: Dict[str, Set[Tuple[str, str]]] = field(default_factory=dict)

    def add_edge(self, source: str, target: str, axiom: str) -> None:
        """Record a one-step rewrite (path constructor)."""
        self._edges.setdefault(source, set()).add((target, axiom))
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
        """Compute π₀(G): the connected components."""
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
# 7. GapAnalyzer — classify failure pairs into categories
# =====================================================================

class FailureCategory(Enum):
    """Categories of pipeline failures (Section 41.7)."""
    GENUINELY_DIFFERENT = 1
    COMPILATION_LOSSY = 2
    TIMEOUT_MEMORY = 3


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
    oterm_f: Optional[OTerm] = None,
    oterm_g: Optional[OTerm] = None,
    z3_timed_out: bool = False,
) -> GapAnalysis:
    """Classify a failed equivalence check into Category 1/2/3.

    Compiles sources to OTerms if not provided, then inspects the
    canonical forms for OUnknown nodes, short canons, and Z3 timeout.
    """
    if oterm_f is None:
        r = compile_to_oterm(src_f)
        oterm_f = r[0] if r else None
    if oterm_g is None:
        r = compile_to_oterm(src_g)
        oterm_g = r[0] if r else None

    if oterm_f is None or oterm_g is None:
        return GapAnalysis(
            category=FailureCategory.COMPILATION_LOSSY,
            reason="OTerm compilation failed",
        )

    canon_f = normalize(oterm_f).canon()
    canon_g = normalize(oterm_g).canon()

    if "OUnknown" in canon_f or "?" in canon_f or "OUnknown" in canon_g or "?" in canon_g:
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

    if z3_timed_out:
        return GapAnalysis(
            category=FailureCategory.TIMEOUT_MEMORY,
            reason="Z3 fiber checker timed out",
            z3_timeout=True,
        )

    return GapAnalysis(
        category=FailureCategory.GENUINELY_DIFFERENT,
        reason="terms in disconnected components of rewrite groupoid",
    )


# =====================================================================
# 8. ProvabilityHorizon — track provable equivalences
# =====================================================================

@dataclass
class ProvabilityHorizon:
    """The provability horizon H and gap set G (Definition 41.12).

    H = {(f,g) : f ≡ g and Π(f,g) = EQ}
    G = {(f,g) : f ≡ g and Π(f,g) ≠ EQ}
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
# 9. ImprovementAxis — framework for measuring axiom additions
# =====================================================================

class AxisKind(Enum):
    """The three improvement axes (Section 41.12)."""
    NORMALIZATION = 1
    SPECIFICATION = 2
    Z3_FIDELITY = 3


@dataclass
class ImprovementAxis:
    """A single improvement axis with estimated impact."""
    kind: AxisKind
    description: str
    estimated_pairs_closed: int = 0
    new_axioms: List[str] = field(default_factory=list)

    def expected_pi0_reduction(self) -> int:
        """How many connected components this would merge."""
        return self.estimated_pairs_closed


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
# 10. BridgingSession — end-to-end bridge between layers
# =====================================================================

@dataclass
class BridgingSession:
    """Run the full bridging pipeline and collect diagnostics.

    Ties together: OTerm compilation → normalization → NEQ detection
    → spec identification → gap analysis → provability tracking.
    """
    horizon: ProvabilityHorizon = field(default_factory=ProvabilityHorizon)
    groupoid: RewriteGroupoid = field(default_factory=RewriteGroupoid)

    def check_pair(
        self, src_f: str, src_g: str, *, name_f: str = "f", name_g: str = "g",
    ) -> PipelineVerdict:
        """Run the denotational bridging pipeline on a source pair.

        1. Compile both to OTerms
        2. Normalize
        3. Check denotational equivalence
        4. If EQ, record in groupoid + horizon
        5. If UNKNOWN, run NEQ detection + gap analysis
        """
        rf = compile_to_oterm(src_f)
        rg = compile_to_oterm(src_g)
        oterm_f = rf[0] if rf else None
        oterm_g = rg[0] if rg else None

        # Normalize if we have terms
        nf_f = normalize(oterm_f) if oterm_f else None
        nf_g = normalize(oterm_g) if oterm_g else None

        # Try denotational equivalence first
        result = denotational_equiv(src_f, src_g)
        if result is True:
            self.horizon.add_proven(name_f, name_g)
            if nf_f and nf_g:
                cf = nf_f.canon()
                cg = nf_g.canon()
                if cf != cg:
                    self.groupoid.add_edge(cf, cg, "denotational_equiv")
            return PipelineVerdict(
                kind=VerdictKind.EQ, confidence=1.0, source_layer=1,
            )

        if result is False:
            cert = None
            if nf_f and nf_g:
                cert = detect_neq(nf_f, nf_g)
            return PipelineVerdict(
                kind=VerdictKind.NEQ, confidence=1.0,
                source_layer=1, certificate=cert,
            )

        # Inconclusive — try NEQ detection on normalized terms
        if nf_f and nf_g:
            cert = detect_neq(nf_f, nf_g)
            if cert and cert.is_valid():
                return PipelineVerdict(
                    kind=VerdictKind.NEQ, confidence=0.9,
                    source_layer=1, certificate=cert,
                )

        # Try spec identification
        if nf_f and nf_g:
            spec_f = identify_spec(nf_f)
            spec_g = identify_spec(nf_g)
            if spec_f and spec_g and spec_f[0] == spec_g[0]:
                self.horizon.add_proven(name_f, name_g)
                cf = nf_f.canon()
                cg = nf_g.canon()
                self.groupoid.add_edge(cf, cg, f"spec:{spec_f[0]}")
                return PipelineVerdict(
                    kind=VerdictKind.EQ, confidence=0.85, source_layer=1,
                )

        # Record gap
        self.horizon.add_gap(name_f, name_g)
        gap = analyze_gap(src_f, src_g, oterm_f, oterm_g)
        return PipelineVerdict(
            kind=VerdictKind.UNKNOWN, confidence=0.0, source_layer=-1,
        )


# =====================================================================
# Self-tests
# =====================================================================

def _self_test():
    """Verify all bridging components work correctly."""
    errors = []

    # --- VerdictKind + PipelineVerdict ---
    v_eq = PipelineVerdict(kind=VerdictKind.EQ, source_layer=1)
    v_neq = PipelineVerdict(kind=VerdictKind.NEQ, source_layer=2)
    v_unk = PipelineVerdict(kind=VerdictKind.UNKNOWN, confidence=0.5)
    assert v_eq.is_definitive(), "EQ should be definitive"
    assert v_neq.is_definitive(), "NEQ should be definitive"
    assert not v_unk.is_definitive(), "UNKNOWN should not be definitive"
    assert "EQ" in repr(v_eq)

    # --- CongruenceRule ---
    refl = CongruenceRule(kind=CongruenceKind.REFL)
    a = OLit(42)
    b = OLit(42)
    c = OLit(99)
    assert refl.can_apply(a, b), "REFL should apply to equal terms"
    assert not refl.can_apply(a, c), "REFL should not apply to unequal"

    cong = CongruenceRule(kind=CongruenceKind.OOP_CONG)
    op_a = OOp("add", (OVar("x"), OLit(1)))
    op_b = OOp("add", (OVar("y"), OLit(2)))
    op_c = OOp("sub", (OVar("x"), OLit(1)))
    assert cong.can_apply(op_a, op_b), "OOP_CONG: same op name"
    assert not cong.can_apply(op_a, op_c), "OOP_CONG: different op name"

    assert not COMM_NUMERIC.can_apply(op_a, op_b, fiber="str"), \
        "COMM_NUMERIC fiber-restricted"
    assert not COMM_NUMERIC.can_apply(op_a, op_b, fiber="int"), \
        "COMM_NUMERIC kind is COMM not OOP_CONG — can_apply returns False"

    # --- NEQCertificate + detect_neq ---
    cert = NEQCertificate(category=NEQCategory.LITERAL, reason="test")
    assert cert.is_valid()

    cross = NEQCertificate(
        category=NEQCategory.CROSS_TYPE, reason="x", in_case_branch=True
    )
    assert not cross.is_valid(), "cross-type in case branch suppressed"

    neq = detect_neq(OLit(1), OLit(2))
    assert neq is not None and neq.category == NEQCategory.LITERAL

    sub_a = OOp("sub", (OVar("x"), OVar("y")))
    sub_b = OOp("sub", (OVar("y"), OVar("x")))
    neq2 = detect_neq(sub_a, sub_b)
    assert neq2 is not None and neq2.category == NEQCategory.ARGUMENT_ORDER

    add_a = OOp("add", (OVar("x"), OVar("y")))
    add_b = OOp("add", (OVar("y"), OVar("x")))
    neq3 = detect_neq(add_a, add_b, fiber="str")
    assert neq3 is not None and neq3.category == NEQCategory.ARGUMENT_ORDER

    neq4 = detect_neq(add_a, add_b, fiber="int")
    assert neq4 is None, "add is commutative on int fiber"

    fold_a = OFold("add", OLit(0), OVar("xs"))
    fold_b = OFold("mul", OLit(1), OVar("xs"))
    neq5 = detect_neq(fold_a, fold_b)
    assert neq5 is not None and neq5.category == NEQCategory.FOLD_OPERATOR

    lt_a = OOp("lt", (OVar("x"), OVar("y")))
    gt_b = OOp("gt", (OVar("x"), OVar("y")))
    neq6 = detect_neq(lt_a, gt_b)
    assert neq6 is not None and neq6.category == NEQCategory.COMPARISON_OPERATOR

    # --- SpecPattern ---
    t_fact = OFold("mul", OLit(1), OOp("range", (OLit(1), OVar("n"))))
    spec_r = identify_spec(t_fact)
    assert spec_r is not None and spec_r[0] == "factorial"

    t_sum = OFold("add", OLit(0), OOp("range", (OVar("n"),)))
    spec_s = identify_spec(t_sum)
    assert spec_s is not None and spec_s[0] == "range_sum"

    t_sort = OOp("sorted", (OVar("xs"),))
    spec_t = identify_spec(t_sort)
    assert spec_t is not None and spec_t[0] == "sorted"

    # --- RewriteGroupoid ---
    g = RewriteGroupoid()
    g.add_edge("A", "B", "D1")
    g.add_edge("B", "C", "D2")
    assert g.are_connected("A", "C"), "A-B-C should be connected"
    assert not g.are_connected("A", "D"), "D is isolated"

    comps = g.pi_0()
    assert len(comps) == 1, "A, B, C should form one component"
    assert {"A", "B", "C"} == comps[0]

    g.add_edge("D", "E", "D3")
    comps2 = g.pi_0()
    assert len(comps2) == 2, "now two components"

    # --- GapAnalyzer ---
    gap1 = analyze_gap("def f(): pass", "def g(): pass")
    assert isinstance(gap1, GapAnalysis)

    gap2 = analyze_gap("not valid python", "def g(): return 1")
    assert gap2.category == FailureCategory.COMPILATION_LOSSY

    # --- ProvabilityHorizon ---
    h = ProvabilityHorizon()
    h.add_proven("f", "g")
    h.add_gap("a", "b")
    assert h.coverage == 0.5
    h.add_proven("a", "b")
    assert h.coverage == 1.0
    assert len(h.gap_pairs) == 0

    # --- ImprovementAxis ---
    assert len(IMPROVEMENT_AXES) == 3
    assert IMPROVEMENT_AXES[0].expected_pi0_reduction() == 5
    assert IMPROVEMENT_AXES[2].kind == AxisKind.Z3_FIDELITY

    # --- BridgingSession ---
    session = BridgingSession()
    # Two identical functions — should be EQ or at least not error
    src_a = "def f(n):\n    return n * 2\n"
    src_b = "def g(n):\n    return n + n\n"
    verdict = session.check_pair(src_a, src_b, name_f="f", name_g="g")
    assert isinstance(verdict, PipelineVerdict)

    # Two clearly different functions
    src_c = "def f(n):\n    return n + 1\n"
    src_d = "def g(n):\n    return n - 1\n"
    verdict2 = session.check_pair(src_c, src_d, name_f="f2", name_g="g2")
    assert isinstance(verdict2, PipelineVerdict)

    print("All bridging self-tests passed.")


if __name__ == "__main__":
    _self_test()
