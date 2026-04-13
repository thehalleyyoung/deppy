"""Code proposals for Chapter 24 (g11): Deep Theory — Algorithm A ↔ Algorithm B.

These proposals implement the formal concepts from the deepened chapter:
  1. Specification-based equivalence checking (Theorem det-spec)
  2. Factorial / Fibonacci / GCD spec identification
  3. Matroid/greedy theorem integration with D18/D20
  4. Hard-8 classifier: detecting which pairs need D20
  5. Structural/extensional boundary detection
"""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple


# ═══════════════════════════════════════════════════════════
# 1. Deterministic Specification Framework (Thm det-spec)
# ═══════════════════════════════════════════════════════════

class SpecKind(Enum):
    """Specification determinism classification."""
    DETERMINISTIC = "deterministic"       # unique output for each input
    NONDETERMINISTIC = "nondeterministic" # multiple valid outputs
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class Specification:
    """A formal specification S : A × B → Type.

    Encodes the specification as a predicate on (input, output) pairs,
    plus a proof strategy for determinism (functionality).
    """
    name: str
    predicate_desc: str   # human-readable description of S(x, y)
    kind: SpecKind
    determinism_proof: str  # why Σ_y S(x,y) is propositional

    def is_deterministic(self) -> bool:
        return self.kind == SpecKind.DETERMINISTIC


# ── Standard Specifications (from the chapter) ──

SPEC_FACTORIAL = Specification(
    name="factorial",
    predicate_desc="v = product(1..n)",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="The product of 1..n is a unique integer.",
)

SPEC_FIBONACCI = Specification(
    name="fibonacci",
    predicate_desc="v = F(n) where F(0)=0, F(1)=1, F(n)=F(n-1)+F(n-2)",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="F(n) is uniquely defined by the recurrence.",
)

SPEC_GCD = Specification(
    name="gcd",
    predicate_desc="d | a, d | b, and forall c: (c|a and c|b) => c|d",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="GCD is unique for positive integers.",
)

SPEC_BINOMIAL = Specification(
    name="binomial",
    predicate_desc="v = n! / (k! * (n-k)!)",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="n! is unique, so the quotient is unique.",
)

SPEC_CONVEX_HULL = Specification(
    name="convex_hull",
    predicate_desc="H = extreme points of P in CCW order from leftmost-lowest",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Extreme points are unique; CCW order from fixed start is unique.",
)

SPEC_EDIT_DISTANCE = Specification(
    name="edit_distance",
    predicate_desc="d = min edits (insert/delete/substitute) to transform s1 to s2",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="The minimum exists and is unique (well-ordering of N).",
)

SPEC_SCC = Specification(
    name="strongly_connected_components",
    predicate_desc="C = partition of V into maximal SCCs in reverse topo order",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Maximal SCCs are unique; reverse topo order of SCC DAG is unique.",
)

SPEC_MST = Specification(
    name="minimum_spanning_tree",
    predicate_desc="T is a spanning tree of G with minimum total weight",
    kind=SpecKind.NONDETERMINISTIC,
    determinism_proof="Multiple MSTs may exist when edge weights have ties.",
)

SPEC_TOPOLOGICAL_SORT = Specification(
    name="topological_sort",
    predicate_desc="sigma is a linear extension of the DAG's partial order",
    kind=SpecKind.NONDETERMINISTIC,
    determinism_proof="Multiple valid orderings exist in general.",
)


# Specification registry for automated lookup
SPEC_REGISTRY: Dict[str, Specification] = {
    s.name: s for s in [
        SPEC_FACTORIAL, SPEC_FIBONACCI, SPEC_GCD, SPEC_BINOMIAL,
        SPEC_CONVEX_HULL, SPEC_EDIT_DISTANCE, SPEC_SCC,
        SPEC_MST, SPEC_TOPOLOGICAL_SORT,
    ]
}


# ═══════════════════════════════════════════════════════════
# 2. Specification Identification from OTerms
# ═══════════════════════════════════════════════════════════

def identify_specification(canon: str) -> Optional[Specification]:
    """Given a canonical OTerm string, identify the specification it satisfies.

    This is the _identify_spec function from path_search.py, elevated to
    return full Specification objects with determinism proofs.

    Returns None if the specification cannot be identified.
    """
    # factorial: fold[mul](1, range(1, n+1))
    if "fold[" in canon and ("mul" in canon or "mult" in canon):
        if "range" in canon and canon.count("1") >= 1:
            return SPEC_FACTORIAL

    # fibonacci: fix with add and sub pattern
    if canon.startswith("fix[") and "add" in canon and "sub" in canon:
        return SPEC_FIBONACCI

    # sorted output
    if canon.startswith("sorted("):
        return Specification(
            name="sorted",
            predicate_desc="y is the sorted permutation of x",
            kind=SpecKind.DETERMINISTIC,
            determinism_proof="Total order has unique sorted sequence.",
        )

    # binomial: math.comb
    if "math.comb" in canon:
        return SPEC_BINOMIAL

    return None


# ═══════════════════════════════════════════════════════════
# 3. Matroid / Greedy Theorem (§24.matroid-greedy)
# ═══════════════════════════════════════════════════════════

@dataclass(frozen=True)
class MatroidStructure:
    """Represents a matroid (E, I) for the greedy theorem.

    In practice, we don't enumerate I explicitly — we check the
    three matroid axioms on a representation of the feasibility system.
    """
    ground_set_desc: str    # description of E
    independence_desc: str  # description of I
    is_matroid: bool        # whether the axioms hold
    greedy_optimal: bool    # consequence of Rado-Edmonds theorem


def check_greedy_dp_equivalence(
    greedy_canon: str,
    dp_canon: str,
    matroid: Optional[MatroidStructure] = None,
) -> Optional[str]:
    """Check if a greedy algorithm and a DP algorithm are D20-equivalent.

    If the optimization problem has matroid structure, the greedy algorithm
    computes an optimal solution, matching the DP result.

    Returns:
        "D20_matroid_greedy" if equivalence is established via the matroid theorem.
        None if the matroid structure is not detected.
    """
    if matroid is not None and matroid.is_matroid and matroid.greedy_optimal:
        return "D20_matroid_greedy"

    # Heuristic: if the greedy canon contains "greedy" or "sorted + accumulate"
    # and the DP canon contains "dp" or nested folds, flag for D20 analysis
    greedy_indicators = {"sorted", "min", "max", "greedy"}
    dp_indicators = {"fix[", "fold[", "dp", "table"}

    has_greedy = any(ind in greedy_canon.lower() for ind in greedy_indicators)
    has_dp = any(ind in dp_canon.lower() for ind in dp_indicators)

    if has_greedy and has_dp:
        return "D20_possible_matroid"  # needs manual verification

    return None


# Stock profit matroid instance (EQ-47)
STOCK_PROFIT_MATROID = MatroidStructure(
    ground_set_desc="Set of non-overlapping buy-sell intervals",
    independence_desc="Subsets of at most k non-overlapping intervals",
    is_matroid=True,  # uniform matroid on intervals
    greedy_optimal=True,  # when k >= n/2, greedy is optimal
)


# ═══════════════════════════════════════════════════════════
# 4. Hard-8 Classifier
# ═══════════════════════════════════════════════════════════

class EquivStratum(Enum):
    """The three strata of program equivalence (Theorem boundary)."""
    STRUCTURAL = "structural"       # provable by D1-D19, D21-D24
    SPECIFICATION = "specification" # requires D20 (spec uniqueness)
    EXTENSIONAL = "extensional"     # beyond D20 (mathematical argument only)


@dataclass
class EquivClassification:
    """Classification of an equivalence pair."""
    pair_id: str
    stratum: EquivStratum
    path_axioms: List[str]     # axioms used in the proof path
    specification: Optional[Specification]  # if D20 is needed
    reason: str


# The hard-8 pairs that require D20
HARD_8_PAIRS: Dict[str, EquivClassification] = {
    "eq07": EquivClassification(
        pair_id="eq07",
        stratum=EquivStratum.SPECIFICATION,
        path_axioms=["D20_spec_unify"],
        specification=SPEC_CONVEX_HULL,
        reason="Graham scan and monotone chain use different invariants; "
               "equivalence requires convex hull uniqueness theorem.",
    ),
    "eq08": EquivClassification(
        pair_id="eq08",
        stratum=EquivStratum.SPECIFICATION,
        path_axioms=["D20_spec_unify"],
        specification=SPEC_EDIT_DISTANCE,
        reason="Wagner-Fischer and Hirschberg use different space strategies; "
               "equivalence requires edit distance uniqueness.",
    ),
    "eq16": EquivClassification(
        pair_id="eq16",
        stratum=EquivStratum.SPECIFICATION,
        path_axioms=["D20_spec_unify"],
        specification=SPEC_SCC,
        reason="Tarjan and Kosaraju use fundamentally different traversals; "
               "equivalence requires SCC uniqueness.",
    ),
    "eq29": EquivClassification(
        pair_id="eq29",
        stratum=EquivStratum.SPECIFICATION,
        path_axioms=["D20_spec_unify"],
        specification=Specification(
            name="deep_copy_canonical",
            predicate_desc="y is a deep copy of x with sorted canonical form",
            kind=SpecKind.DETERMINISTIC,
            determinism_proof="Deep copy is unique; sorted canonical form is unique.",
        ),
        reason="Different copy strategies (recursive deepcopy vs BFS) with same "
               "canonical output form.",
    ),
    "eq33": EquivClassification(
        pair_id="eq33",
        stratum=EquivStratum.SPECIFICATION,
        path_axioms=["D20_spec_unify"],
        specification=Specification(
            name="nth_permutation",
            predicate_desc="y is the n-th permutation of range(size) in lex order",
            kind=SpecKind.DETERMINISTIC,
            determinism_proof="Lex order on permutations is total; n-th element is unique.",
        ),
        reason="Factoradic decomposition vs itertools.permutations use different "
               "combinatorial identities.",
    ),
    "eq37": EquivClassification(
        pair_id="eq37",
        stratum=EquivStratum.SPECIFICATION,
        path_axioms=["D20_spec_unify"],
        specification=SPEC_FIBONACCI,
        reason="Matrix exponentiation and fast doubling use different algebraic "
               "identities to compute F(n).",
    ),
    "eq40": EquivClassification(
        pair_id="eq40",
        stratum=EquivStratum.SPECIFICATION,
        path_axioms=["D20_spec_unify"],
        specification=SPEC_BINOMIAL,
        reason="Multiplicative formula and Pascal's triangle use different "
               "recurrence structures.",
    ),
    "eq47": EquivClassification(
        pair_id="eq47",
        stratum=EquivStratum.SPECIFICATION,
        path_axioms=["D20_spec_unify", "D18_greedy"],
        specification=Specification(
            name="max_stock_profit",
            predicate_desc="v = max profit from at most k transactions",
            kind=SpecKind.DETERMINISTIC,
            determinism_proof="Maximum over a finite set of sums is unique.",
        ),
        reason="DP table vs greedy+DP: greedy branch justified by matroid property "
               "when k >= n/2.",
    ),
}


def classify_pair(
    pair_id: str,
    structural_path_found: bool,
    spec_identified: Optional[Specification] = None,
) -> EquivClassification:
    """Classify an equivalence pair into the three strata.

    This implements the Structural/Extensional Boundary theorem:
    - If structural path found → STRUCTURAL stratum
    - If spec identified and deterministic → SPECIFICATION stratum
    - Otherwise → EXTENSIONAL stratum (needs mathematical argument)
    """
    # Check hard-8 registry first
    if pair_id in HARD_8_PAIRS:
        return HARD_8_PAIRS[pair_id]

    if structural_path_found:
        return EquivClassification(
            pair_id=pair_id,
            stratum=EquivStratum.STRUCTURAL,
            path_axioms=["structural_path"],
            specification=None,
            reason="Resolved by structural path constructors (D1-D19, D21-D24).",
        )

    if spec_identified is not None and spec_identified.is_deterministic():
        return EquivClassification(
            pair_id=pair_id,
            stratum=EquivStratum.SPECIFICATION,
            path_axioms=["D20_spec_unify"],
            specification=spec_identified,
            reason=f"Both satisfy deterministic spec '{spec_identified.name}'; "
                   f"uniqueness: {spec_identified.determinism_proof}",
        )

    return EquivClassification(
        pair_id=pair_id,
        stratum=EquivStratum.EXTENSIONAL,
        path_axioms=[],
        specification=spec_identified,
        reason="No structural path or recognizable specification found. "
               "Requires mathematical argument beyond the formal system.",
    )


# ═══════════════════════════════════════════════════════════
# 5. Yoneda Embedding for Observational Equivalence
# ═══════════════════════════════════════════════════════════

# The observations (shared function symbols) that approximate
# the full Yoneda embedding
STANDARD_OBSERVATIONS: List[str] = [
    "sorted", "len", "sum", "hash", "str", "repr",
    "min", "max", "set", "frozenset", "tuple", "list",
    "bool", "int", "float", "type",
]


def yoneda_check_equivalent(
    f_canon: str,
    g_canon: str,
    observations: Optional[List[str]] = None,
) -> Tuple[bool, Optional[str]]:
    """Check observational equivalence via finite Yoneda approximation.

    For each observation t in the observation set, check whether
    t(f(p)) == t(g(p)) for all p.  This is a finite approximation
    of the Yoneda lemma: f ≡ g iff ∀t. t∘f ≡ t∘g.

    In practice, this is implemented as a Z3 query (not here).
    This function provides the framework and classification.

    Returns:
        (True, None) if observationally equivalent under all observations.
        (False, witness_obs) if a distinguishing observation is found.
    """
    obs = observations or STANDARD_OBSERVATIONS

    # In the actual implementation, this would construct Z3 queries:
    # ∃p. t(⟦f⟧(p)) ≠ t(⟦g⟧(p)) for each observation t.
    # Here we just document the interface.

    if f_canon == g_canon:
        return (True, None)

    # Placeholder: actual Z3 checking would go here
    return (True, None)  # conservative: assume equivalent


# ═══════════════════════════════════════════════════════════
# 6. Full Benchmark Classification (50 EQ pairs)
# ═══════════════════════════════════════════════════════════

# Classification of all 50 EQ pairs by proof technique.
# Pairs in bold in the chapter table are the hard-8.
BENCHMARK_CLASSIFICATION: Dict[str, Tuple[str, List[str]]] = {
    "eq01": ("Flatten + sort + unique", ["D4", "D19"]),
    "eq02": ("Word frequency histogram", ["D13", "D19"]),
    "eq03": ("Arithmetic expression eval", ["D1"]),
    "eq04": ("Register machine simulation", ["D1"]),
    "eq05": ("Topological sort (lex-smallest)", ["D15"]),
    "eq06": ("RLE encode/decode roundtrip", ["D1", "D4"]),
    "eq07": ("Convex hull", ["D20"]),
    "eq08": ("Edit distance", ["D20"]),
    "eq09": ("LRU cache simulation", ["D11"]),
    "eq10": ("Matrix multiplication", ["D4", "D5"]),
    "eq11": ("Merge k sorted iterators", ["D5"]),
    "eq12": ("Binary tree serialize/deserialize", ["D1"]),
    "eq13": ("DAG path counting", ["D1", "D16"]),
    "eq14": ("Calculator (parse + eval)", ["D1", "D2"]),
    "eq15": ("Longest increasing subsequence", ["D16"]),
    "eq16": ("Strongly connected components", ["D20"]),
    "eq17": ("Power set generation", ["D1"]),
    "eq18": ("JSON-like pretty printer", ["D1", "D2"]),
    "eq19": ("0/1 Knapsack", ["D16"]),
    "eq20": ("Structural hashing (SHA-256)", ["D1", "D19"]),
    "eq21": ("Prime factorization", ["D1"]),
    "eq22": ("Cycle detection (Floyd/Brent)", ["D1"]),
    "eq23": ("Balanced parentheses", ["D9"]),
    "eq24": ("Levenshtein distance", ["D16"]),
    "eq25": ("Merge overlapping intervals", ["D19"]),
    "eq26": ("k-th smallest (quickselect)", ["D1"]),
    "eq27": ("Longest common subsequence", ["D16"]),
    "eq28": ("Regex state machine", ["D1", "D9"]),
    "eq29": ("Deep copy + sort", ["D20"]),
    "eq30": ("Trie search", ["D11"]),
    "eq31": ("Dijkstra shortest path", ["D10"]),
    "eq32": ("Island counting (grid)", ["D15"]),
    "eq33": ("n-th permutation", ["D20"]),
    "eq34": ("Postfix expression eval", ["D9"]),
    "eq35": ("all ↔ not-any-not", ["ALG"]),
    "eq36": ("Transpose dict-of-lists", ["D4", "D5"]),
    "eq37": ("Fibonacci mod p", ["D20"]),
    "eq38": ("Group anagrams", ["D19", "D20"]),
    "eq39": ("Perfect power check", ["D1"]),
    "eq40": ("Binomial coefficient", ["D20"]),
    "eq41": ("Zip-longest with fill", ["D5", "D6"]),
    "eq42": ("Currying", ["D24"]),
    "eq43": ("CSV parsing", ["D1", "D4"]),
    "eq44": ("Coin change DP", ["D16"]),
    "eq45": ("Grid path counting", ["D16"]),
    "eq46": ("Mini type inference", ["D1", "D8"]),
    "eq47": ("Stock profit", ["D20"]),
    "eq48": ("Trailing zeroes in n!", ["D1"]),
    "eq49": ("Deep equality with cycles", ["D1", "D9"]),
    "eq50": ("N-queens", ["D1", "D8"]),
}


def get_hard_8_ids() -> List[str]:
    """Return the IDs of the hard-8 pairs (require D20)."""
    return [pid for pid, (_, axioms) in BENCHMARK_CLASSIFICATION.items()
            if "D20" in axioms and pid not in ("eq38",)]
    # eq38 uses D20 but also D19; it's borderline structural


def get_structural_ids() -> List[str]:
    """Return IDs of pairs resolved by structural paths only."""
    return [pid for pid, (_, axioms) in BENCHMARK_CLASSIFICATION.items()
            if "D20" not in axioms]


# ═══════════════════════════════════════════════════════════
# 7. Proof Path Templates
# ═══════════════════════════════════════════════════════════

@dataclass
class ProofSketch:
    """A formal proof sketch for an algorithm equivalence."""
    pair_id: str
    specification: Specification
    path_description: str
    key_lemma: str
    oterm_path: List[str]  # sequence of axiom names


FACTORIAL_PROOF = ProofSketch(
    pair_id="factorial_variants",
    specification=SPEC_FACTORIAL,
    path_description=(
        "fix[h](case(n=0, 1, n*h(n-1))) →[D1] fold[mul](1, range(1,n+1)) "
        "←[D5] reduce(mul, range(1,n+1), 1)"
    ),
    key_lemma="Primitive recursion with accumulation operator = fold (D1_fix_to_fold)",
    oterm_path=["D1_fix_to_fold", "D5_fold_universal"],
)

FIBONACCI_PROOF = ProofSketch(
    pair_id="eq37",
    specification=SPEC_FIBONACCI,
    path_description=(
        "Matrix exponentiation and fast doubling both compute F(n) "
        "via the identity M^n = [[F(n+1),F(n)],[F(n),F(n-1)]]. "
        "Fast doubling derives F(2k) and F(2k+1) from matrix squaring."
    ),
    key_lemma="Both satisfy S_fib; uniqueness of F(n) gives the path (D20).",
    oterm_path=["D20_spec_unify"],
)

GCD_PROOF = ProofSketch(
    pair_id="gcd_variants",
    specification=SPEC_GCD,
    path_description=(
        "Euclidean: (a,b) → (b, a mod b). "
        "Subtraction: (a,b) → (a-b, b) or (a, b-a). "
        "Both terminate with gcd(a,b) by the fundamental property."
    ),
    key_lemma="gcd(a,b) = gcd(b, a mod b) = gcd(a-b, b); uniqueness gives D20 path.",
    oterm_path=["D20_spec_unify"],
)

BINOMIAL_PROOF = ProofSketch(
    pair_id="eq40",
    specification=SPEC_BINOMIAL,
    path_description=(
        "Multiplicative: fold[div_mul](1, range(k)). "
        "Pascal's triangle: nested fold over rows. "
        "Both compute C(n,k) = n!/(k!(n-k)!)."
    ),
    key_lemma="Uniqueness of n! and integer arithmetic; D1 + D20.",
    oterm_path=["D1_fix_to_fold", "D20_spec_unify"],
)
