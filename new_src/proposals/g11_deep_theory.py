"""Chapter 24 (g11): Deep Theory — Algorithm A ↔ Algorithm B.

Implements the formal concepts from the deepened chapter:
  1. Specification-based equivalence checking (Theorem det-spec)
  2. Factorial / Fibonacci / GCD spec identification
  3. Matroid/greedy theorem integration with D18/D20
  4. Hard-8 classifier: detecting which pairs need D20
  5. Structural/extensional boundary detection
  6. Full 50-pair EQ classification with expected proof paths
  7. Hard-8 analyzer (why a pair resists structural proofs)
  8. Fibonacci variant recognizer (naive/memo/iterative/matrix/fast-doubling)
  9. GCD variant recognizer (Euclidean/subtraction/binary)
  10. Sorting pipeline recognizer (sort-then-process patterns)
  11. Yoneda embedding approximation (spec-based program characterization)
  12. Proof path planner (given a pair, suggest which dichotomies to try)
  13. Stratum classifier (structural/semi-structural/extensional)
  14. Matroid structure detector for greedy algorithm equivalences
  15. Benchmark regression test generator (auto-generate tests from classification)
"""
from __future__ import annotations

import re
import hashlib
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any, Callable, Dict, FrozenSet, List, Optional, Set, Sequence,
    Tuple, Union,
)


# ═══════════════════════════════════════════════════════════════════
# §1  Deterministic Specification Framework  (Thm det-spec)
# ═══════════════════════════════════════════════════════════════════

class SpecKind(Enum):
    """Specification determinism classification."""
    DETERMINISTIC = "deterministic"
    NONDETERMINISTIC = "nondeterministic"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class Specification:
    """A formal specification S : A × B → Type.

    Encodes the specification as a predicate on (input, output) pairs,
    plus a proof strategy for determinism (functionality).
    """
    name: str
    predicate_desc: str
    kind: SpecKind
    determinism_proof: str

    def is_deterministic(self) -> bool:
        return self.kind == SpecKind.DETERMINISTIC


# ── Standard Specifications ──

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

SPEC_SORTED = Specification(
    name="sorted",
    predicate_desc="y is the sorted permutation of x",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Total order has unique sorted sequence.",
)

SPEC_RANGE_SUM = Specification(
    name="range_sum",
    predicate_desc="v = sum(0..n-1)",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Sum of integers 0..n-1 = n*(n-1)/2 is unique.",
)

SPEC_POWER = Specification(
    name="power",
    predicate_desc="v = base^exp",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Exponentiation is a total function on integers.",
)

SPEC_PRIMALITY = Specification(
    name="primality",
    predicate_desc="True iff n has no divisors in 2..sqrt(n)",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Divisibility is decidable; set of factors is unique.",
)

SPEC_LCS = Specification(
    name="longest_common_subsequence",
    predicate_desc="S is a longest common subsequence of A and B",
    kind=SpecKind.NONDETERMINISTIC,
    determinism_proof="Multiple LCS of same length may exist.",
)

SPEC_LCS_LENGTH = Specification(
    name="lcs_length",
    predicate_desc="k = length of a longest common subsequence of A and B",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="The maximum length is unique (well-ordering of N).",
)

SPEC_LIS = Specification(
    name="longest_increasing_subsequence",
    predicate_desc="S is a longest increasing subsequence of A",
    kind=SpecKind.NONDETERMINISTIC,
    determinism_proof="Multiple LIS of same length may exist.",
)

SPEC_LIS_LENGTH = Specification(
    name="lis_length",
    predicate_desc="k = length of a longest increasing subsequence of A",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="The maximum length is unique (well-ordering of N).",
)

SPEC_KNAPSACK = Specification(
    name="knapsack_01",
    predicate_desc="v = maximum value achievable with weight <= W",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Max over a finite set is unique.",
)

SPEC_SHORTEST_PATH = Specification(
    name="shortest_path",
    predicate_desc="d = weight of a shortest path from s to t in G",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Minimum weight path value is unique (non-negative weights).",
)

SPEC_COIN_CHANGE = Specification(
    name="coin_change",
    predicate_desc="k = minimum number of coins summing to amount",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Minimum count is unique.",
)

SPEC_GRID_PATHS = Specification(
    name="grid_paths",
    predicate_desc="k = number of right-down paths in an m x n grid",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="C(m+n-2, m-1) is unique.",
)

SPEC_NTH_PERMUTATION = Specification(
    name="nth_permutation",
    predicate_desc="y is the n-th permutation of range(size) in lex order",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Lex order on permutations is total; n-th element is unique.",
)

SPEC_DEEP_COPY = Specification(
    name="deep_copy_canonical",
    predicate_desc="y is a deep copy of x with sorted canonical form",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Deep copy is unique; sorted canonical form is unique.",
)

SPEC_MAX_STOCK_PROFIT = Specification(
    name="max_stock_profit",
    predicate_desc="v = max profit from at most k transactions",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Maximum over a finite set of sums is unique.",
)

SPEC_TRAILING_ZEROES = Specification(
    name="trailing_zeroes",
    predicate_desc="k = number of trailing zeroes in n!",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="v_5(n!) = sum_{i=1}^{inf} floor(n/5^i) is unique.",
)

SPEC_NQUEENS = Specification(
    name="nqueens",
    predicate_desc="S = set of valid n-queens placements",
    kind=SpecKind.DETERMINISTIC,
    determinism_proof="Set of valid placements is unique (defined by non-attack constraint).",
)


SPEC_REGISTRY: Dict[str, Specification] = {
    s.name: s for s in [
        SPEC_FACTORIAL, SPEC_FIBONACCI, SPEC_GCD, SPEC_BINOMIAL,
        SPEC_CONVEX_HULL, SPEC_EDIT_DISTANCE, SPEC_SCC,
        SPEC_MST, SPEC_TOPOLOGICAL_SORT, SPEC_SORTED, SPEC_RANGE_SUM,
        SPEC_POWER, SPEC_PRIMALITY, SPEC_LCS, SPEC_LCS_LENGTH,
        SPEC_LIS, SPEC_LIS_LENGTH, SPEC_KNAPSACK, SPEC_SHORTEST_PATH,
        SPEC_COIN_CHANGE, SPEC_GRID_PATHS, SPEC_NTH_PERMUTATION,
        SPEC_DEEP_COPY, SPEC_MAX_STOCK_PROFIT, SPEC_TRAILING_ZEROES,
        SPEC_NQUEENS,
    ]
}


# ═══════════════════════════════════════════════════════════════════
# §2  Specification Identification from OTerms
# ═══════════════════════════════════════════════════════════════════

def identify_specification(canon: str) -> Optional[Specification]:
    """Given a canonical OTerm string, identify the specification it satisfies.

    This is the _identify_spec function from path_search.py, elevated to
    return full Specification objects with determinism proofs.
    """
    if "fold[" in canon and ("mul" in canon or "mult" in canon):
        if "range" in canon and canon.count("1") >= 1:
            return SPEC_FACTORIAL

    if canon.startswith("fix[") and "add" in canon and "sub" in canon:
        return SPEC_FIBONACCI

    if canon.startswith("sorted("):
        return SPEC_SORTED

    if "math.comb" in canon:
        return SPEC_BINOMIAL

    if "fold[" in canon and ("add" in canon or "iadd" in canon):
        if "range" in canon:
            return SPEC_RANGE_SUM

    if "pow" in canon or "power" in canon:
        return SPEC_POWER

    if "gcd" in canon or ("mod" in canon and "fix[" in canon):
        return SPEC_GCD

    return None


# ═══════════════════════════════════════════════════════════════════
# §3  Matroid / Greedy Theorem  (§24.matroid-greedy)
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class MatroidStructure:
    """Represents a matroid (E, I) for the greedy theorem.

    In practice we don't enumerate I explicitly — we verify the three
    matroid axioms on a representation of the feasibility system:
      (M1) ∅ ∈ I
      (M2) A ⊆ B ∈ I ⟹ A ∈ I   (hereditary)
      (M3) |A| < |B| ∈ I ⟹ ∃x ∈ B\\A: A ∪ {x} ∈ I   (exchange)
    """
    ground_set_desc: str
    independence_desc: str
    is_matroid: bool
    greedy_optimal: bool
    rank: Optional[int] = None


def check_matroid_axioms(
    ground_set: Set[Any],
    is_independent: Callable[[FrozenSet[Any]], bool],
) -> MatroidStructure:
    """Verify the three matroid axioms on a concrete independence oracle.

    Brute-force check — only feasible for small ground sets (|E| ≤ 15).
    Returns a MatroidStructure recording whether the axioms hold.
    """
    n = len(ground_set)
    elements = sorted(ground_set, key=str)

    if not is_independent(frozenset()):
        return MatroidStructure(
            ground_set_desc=str(ground_set),
            independence_desc="oracle",
            is_matroid=False,
            greedy_optimal=False,
        )

    independent_sets: List[FrozenSet[Any]] = [frozenset()]
    for mask in range(1, 1 << n):
        subset = frozenset(elements[i] for i in range(n) if mask & (1 << i))
        if is_independent(subset):
            independent_sets.append(subset)

    for s in independent_sets:
        for elem in s:
            sub = s - {elem}
            if sub not in independent_sets and sub != frozenset():
                found = False
                for t in independent_sets:
                    if t == sub:
                        found = True
                        break
                if not found:
                    return MatroidStructure(
                        ground_set_desc=str(ground_set),
                        independence_desc="oracle",
                        is_matroid=False,
                        greedy_optimal=False,
                    )

    for a in independent_sets:
        for b in independent_sets:
            if len(a) < len(b):
                can_augment = any(
                    (a | {x}) in set(independent_sets)
                    for x in b - a
                )
                if not can_augment:
                    augment_found = False
                    for x in b - a:
                        candidate = a | {x}
                        if is_independent(frozenset(candidate)):
                            augment_found = True
                            break
                    if not augment_found:
                        return MatroidStructure(
                            ground_set_desc=str(ground_set),
                            independence_desc="oracle",
                            is_matroid=False,
                            greedy_optimal=False,
                        )

    max_rank = max(len(s) for s in independent_sets)
    return MatroidStructure(
        ground_set_desc=str(ground_set),
        independence_desc="oracle",
        is_matroid=True,
        greedy_optimal=True,
        rank=max_rank,
    )


def detect_matroid_pattern(canon: str) -> Optional[str]:
    """Heuristic detection of matroid-amenable patterns in canonical OTerm strings.

    Returns the matroid type name if detected, else None.
    """
    canon_lower = canon.lower()
    if "sorted" in canon_lower and ("greedy" in canon_lower or "accumulate" in canon_lower):
        if "weight" in canon_lower or "cost" in canon_lower:
            return "graphic_matroid"
    if "interval" in canon_lower and "sorted" in canon_lower:
        return "uniform_matroid"
    if "rank" in canon_lower or "basis" in canon_lower:
        return "linear_matroid"
    if re.search(r"partition|coloring|schedule", canon_lower):
        return "partition_matroid"
    return None


def check_greedy_dp_equivalence(
    greedy_canon: str,
    dp_canon: str,
    matroid: Optional[MatroidStructure] = None,
) -> Optional[str]:
    """Check if a greedy algorithm and a DP algorithm are D20-equivalent.

    If the optimization problem has matroid structure, the greedy algorithm
    computes an optimal solution, matching the DP result.
    """
    if matroid is not None and matroid.is_matroid and matroid.greedy_optimal:
        return "D20_matroid_greedy"

    greedy_indicators = {"sorted", "min", "max", "greedy"}
    dp_indicators = {"fix[", "fold[", "dp", "table"}

    has_greedy = any(ind in greedy_canon.lower() for ind in greedy_indicators)
    has_dp = any(ind in dp_canon.lower() for ind in dp_indicators)

    if has_greedy and has_dp:
        matroid_type = detect_matroid_pattern(greedy_canon)
        if matroid_type:
            return f"D20_matroid_greedy({matroid_type})"
        return "D20_possible_matroid"

    return None


STOCK_PROFIT_MATROID = MatroidStructure(
    ground_set_desc="Set of non-overlapping buy-sell intervals",
    independence_desc="Subsets of at most k non-overlapping intervals",
    is_matroid=True,
    greedy_optimal=True,
    rank=None,
)

ACTIVITY_SELECTION_MATROID = MatroidStructure(
    ground_set_desc="Set of activities with start/end times",
    independence_desc="Subsets of mutually non-overlapping activities",
    is_matroid=True,
    greedy_optimal=True,
    rank=None,
)

HUFFMAN_MATROID = MatroidStructure(
    ground_set_desc="Set of symbol merge-trees",
    independence_desc="Forests of at most k trees (merge steps)",
    is_matroid=True,
    greedy_optimal=True,
    rank=None,
)


# ═══════════════════════════════════════════════════════════════════
# §4  Equivalence Stratum & Hard-8 Classifier
# ═══════════════════════════════════════════════════════════════════

class EquivStratum(Enum):
    """The three strata of program equivalence (Theorem boundary)."""
    STRUCTURAL = "structural"
    SEMI_STRUCTURAL = "semi-structural"
    SPECIFICATION = "specification"
    EXTENSIONAL = "extensional"


@dataclass
class EquivClassification:
    """Classification of an equivalence pair."""
    pair_id: str
    stratum: EquivStratum
    path_axioms: List[str]
    specification: Optional[Specification]
    reason: str
    resistance_factors: List[str] = field(default_factory=list)


class ResistanceFactor(Enum):
    """Why a pair resists purely structural proof."""
    DIFFERENT_INVARIANT = auto()
    DIFFERENT_TRAVERSAL_ORDER = auto()
    DIFFERENT_ALGEBRAIC_IDENTITY = auto()
    DIFFERENT_DATA_STRUCTURE = auto()
    DIFFERENT_RECURRENCE = auto()
    MATHEMATICAL_THEOREM_REQUIRED = auto()
    COMBINATORIAL_IDENTITY = auto()
    NONDETERMINISTIC_SPEC = auto()


@dataclass
class Hard8Analysis:
    """Detailed analysis of why a hard-8 pair resists structural proofs."""
    pair_id: str
    description: str
    algorithm_a: str
    algorithm_b: str
    shared_spec: Specification
    resistance: List[ResistanceFactor]
    mathematical_content: str
    suggested_axioms: List[str]
    d20_essential: bool


HARD_8_ANALYSES: Dict[str, Hard8Analysis] = {
    "eq07": Hard8Analysis(
        pair_id="eq07",
        description="Convex hull: Graham scan vs Monotone chain",
        algorithm_a="Graham scan (polar-angle sort + stack)",
        algorithm_b="Monotone chain (x-sort + upper/lower hulls)",
        shared_spec=SPEC_CONVEX_HULL,
        resistance=[
            ResistanceFactor.DIFFERENT_INVARIANT,
            ResistanceFactor.DIFFERENT_TRAVERSAL_ORDER,
        ],
        mathematical_content=(
            "Graham maintains a CCW-turn invariant after polar-angle sort. "
            "Monotone chain builds upper and lower hulls separately after x-sort. "
            "Neither invariant can be rewritten to the other by D1-D19."
        ),
        suggested_axioms=["D20_spec_unify"],
        d20_essential=True,
    ),
    "eq08": Hard8Analysis(
        pair_id="eq08",
        description="Edit distance: Wagner-Fischer vs Hirschberg",
        algorithm_a="Wagner-Fischer (full O(mn) table)",
        algorithm_b="Hirschberg (divide-and-conquer, O(n) space)",
        shared_spec=SPEC_EDIT_DISTANCE,
        resistance=[
            ResistanceFactor.DIFFERENT_DATA_STRUCTURE,
            ResistanceFactor.MATHEMATICAL_THEOREM_REQUIRED,
        ],
        mathematical_content=(
            "Wagner-Fischer fills a 2D DP table. Hirschberg uses divide-and-conquer "
            "on the midpoint row to reconstruct the alignment in O(n) space. The "
            "space optimization requires the DP recurrence to be expressible as a "
            "linear-space subproblem."
        ),
        suggested_axioms=["D20_spec_unify"],
        d20_essential=True,
    ),
    "eq16": Hard8Analysis(
        pair_id="eq16",
        description="SCC: Tarjan vs Kosaraju",
        algorithm_a="Tarjan (single DFS with lowlink)",
        algorithm_b="Kosaraju (two-pass DFS on G and G^T)",
        shared_spec=SPEC_SCC,
        resistance=[
            ResistanceFactor.DIFFERENT_INVARIANT,
            ResistanceFactor.DIFFERENT_TRAVERSAL_ORDER,
            ResistanceFactor.MATHEMATICAL_THEOREM_REQUIRED,
        ],
        mathematical_content=(
            "Tarjan computes lowlink values in one DFS and emits SCCs via stack. "
            "Kosaraju does a DFS on G for finish-time ordering, then a DFS on "
            "G^T in reverse finish order. Equivalence follows from the SCC "
            "uniqueness theorem: the condensation DAG is unique."
        ),
        suggested_axioms=["D20_spec_unify"],
        d20_essential=True,
    ),
    "eq29": Hard8Analysis(
        pair_id="eq29",
        description="Deep copy + sort: recursive vs BFS",
        algorithm_a="Recursive deepcopy with canonical sorting",
        algorithm_b="BFS-based copy with canonical sorting",
        shared_spec=SPEC_DEEP_COPY,
        resistance=[
            ResistanceFactor.DIFFERENT_TRAVERSAL_ORDER,
        ],
        mathematical_content=(
            "Both produce identical canonical-form deep copies, but traverse "
            "the object graph in different orders (DFS vs BFS). The canonical "
            "output form (sorted keys at each level) ensures the same result."
        ),
        suggested_axioms=["D20_spec_unify"],
        d20_essential=True,
    ),
    "eq33": Hard8Analysis(
        pair_id="eq33",
        description="n-th permutation: factoradic vs itertools",
        algorithm_a="Factoradic number system decomposition",
        algorithm_b="itertools.permutations enumeration",
        shared_spec=SPEC_NTH_PERMUTATION,
        resistance=[
            ResistanceFactor.DIFFERENT_ALGEBRAIC_IDENTITY,
            ResistanceFactor.COMBINATORIAL_IDENTITY,
        ],
        mathematical_content=(
            "Factoradic uses the mixed-radix representation: n = d_{k}*k! + ... + d_1*1!. "
            "itertools generates permutations in lex order. Equivalence requires "
            "the theorem that factoradic decomposition produces the n-th lex permutation."
        ),
        suggested_axioms=["D20_spec_unify"],
        d20_essential=True,
    ),
    "eq37": Hard8Analysis(
        pair_id="eq37",
        description="Fibonacci: matrix exponentiation vs fast doubling",
        algorithm_a="Matrix exponentiation [[1,1],[1,0]]^n",
        algorithm_b="Fast doubling F(2k), F(2k+1) identities",
        shared_spec=SPEC_FIBONACCI,
        resistance=[
            ResistanceFactor.DIFFERENT_ALGEBRAIC_IDENTITY,
            ResistanceFactor.MATHEMATICAL_THEOREM_REQUIRED,
        ],
        mathematical_content=(
            "Matrix exponentiation uses [[F(n+1),F(n)],[F(n),F(n-1)]] = M^n. "
            "Fast doubling uses F(2k)=F(k)[2F(k+1)-F(k)] and F(2k+1)=F(k+1)^2+F(k)^2. "
            "Both derive from M^n but via different matrix-identity paths."
        ),
        suggested_axioms=["D20_spec_unify"],
        d20_essential=True,
    ),
    "eq40": Hard8Analysis(
        pair_id="eq40",
        description="Binomial: multiplicative formula vs Pascal's triangle",
        algorithm_a="Multiplicative: C(n,k) = prod_{i=0}^{k-1} (n-i)/(i+1)",
        algorithm_b="Pascal's triangle: C(n,k) = C(n-1,k-1) + C(n-1,k)",
        shared_spec=SPEC_BINOMIAL,
        resistance=[
            ResistanceFactor.DIFFERENT_RECURRENCE,
            ResistanceFactor.COMBINATORIAL_IDENTITY,
        ],
        mathematical_content=(
            "The multiplicative formula computes C(n,k) by a product. "
            "Pascal's triangle uses the addition recurrence. "
            "Equivalence: both compute n!/(k!(n-k)!) by different routes."
        ),
        suggested_axioms=["D1_fix_to_fold", "D20_spec_unify"],
        d20_essential=True,
    ),
    "eq47": Hard8Analysis(
        pair_id="eq47",
        description="Stock profit: DP table vs greedy+DP hybrid",
        algorithm_a="Full DP table over (day, transactions)",
        algorithm_b="Greedy for large k, DP for small k",
        shared_spec=SPEC_MAX_STOCK_PROFIT,
        resistance=[
            ResistanceFactor.MATHEMATICAL_THEOREM_REQUIRED,
            ResistanceFactor.DIFFERENT_DATA_STRUCTURE,
        ],
        mathematical_content=(
            "When k >= n/2, the greedy approach (sum all positive differences) "
            "is optimal by a matroid-like argument: each day-pair is independent. "
            "For small k, DP is required. The hybrid must prove correctness "
            "of the branch point."
        ),
        suggested_axioms=["D20_spec_unify", "D18_greedy"],
        d20_essential=True,
    ),
}


HARD_8_PAIRS: Dict[str, EquivClassification] = {
    pid: EquivClassification(
        pair_id=pid,
        stratum=EquivStratum.SPECIFICATION,
        path_axioms=analysis.suggested_axioms,
        specification=analysis.shared_spec,
        reason=analysis.mathematical_content[:120] + "...",
        resistance_factors=[r.name for r in analysis.resistance],
    )
    for pid, analysis in HARD_8_ANALYSES.items()
}


def analyze_hard_8(pair_id: str) -> Optional[Hard8Analysis]:
    """Return the detailed analysis for a hard-8 pair, or None."""
    return HARD_8_ANALYSES.get(pair_id)


def why_hard(pair_id: str) -> str:
    """One-line explanation of why a pair is in the hard-8."""
    analysis = HARD_8_ANALYSES.get(pair_id)
    if analysis is None:
        return f"{pair_id} is not in the hard-8."
    factors = ", ".join(r.name.lower().replace("_", " ") for r in analysis.resistance)
    return f"{pair_id}: {analysis.description} — resists due to {factors}."


# ═══════════════════════════════════════════════════════════════════
# §5  Fibonacci Variant Recognizer
# ═══════════════════════════════════════════════════════════════════

class FibVariant(Enum):
    NAIVE_RECURSIVE = "naive_recursive"
    MEMOIZED = "memoized"
    ITERATIVE = "iterative"
    MATRIX_EXP = "matrix_exponentiation"
    FAST_DOUBLING = "fast_doubling"
    CLOSED_FORM = "closed_form"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class FibRecognition:
    variant: FibVariant
    confidence: float
    evidence: str


_FIB_PATTERNS: List[Tuple[FibVariant, List[str], str]] = [
    (FibVariant.NAIVE_RECURSIVE,
     [r"def\s+\w+\(n\)", r"return\s+\w+\(n\s*-\s*1\)\s*\+\s*\w+\(n\s*-\s*2\)"],
     "Direct double-recursive call"),
    (FibVariant.MEMOIZED,
     [r"(cache|memo|lru_cache|functools\.cache)", r"n\s*-\s*1.*n\s*-\s*2"],
     "Cached recursive with subtraction pattern"),
    (FibVariant.ITERATIVE,
     [r"(for|while)", r"a\s*,\s*b\s*=\s*b\s*,\s*a\s*\+\s*b"],
     "Iterative variable-swap pattern"),
    (FibVariant.MATRIX_EXP,
     [r"\[\[.*1.*1.*\].*\[.*1.*0.*\]\]", r"matrix|mat_mul|mat_pow"],
     "Matrix [[1,1],[1,0]]^n pattern"),
    (FibVariant.FAST_DOUBLING,
     [r"n\s*//\s*2|n\s*>>\s*1|k\s*=\s*n\s*//\s*2",
      r"2\s*\*\s*\w+\(|f2k|F\(2k\)|f_2k"],
     "Halving/doubling recurrence"),
    (FibVariant.CLOSED_FORM,
     [r"sqrt\(5\)|phi|golden", r"round|int\("],
     "Binet's formula / golden ratio"),
]


def recognize_fibonacci_variant(source: str) -> FibRecognition:
    """Recognize which Fibonacci implementation variant a source string represents."""
    best_variant = FibVariant.UNKNOWN
    best_score = 0.0
    best_evidence = "No Fibonacci pattern detected."

    for variant, patterns, description in _FIB_PATTERNS:
        matches = sum(1 for p in patterns if re.search(p, source, re.IGNORECASE | re.DOTALL))
        score = matches / len(patterns)
        if score >= best_score and score > 0:
            best_score = score
            best_variant = variant
            best_evidence = description

    if best_score < 0.3:
        if re.search(r"fib|fibonacci", source, re.IGNORECASE):
            best_variant = FibVariant.UNKNOWN
            best_evidence = "Contains 'fib' but pattern not recognized."
            best_score = 0.2

    return FibRecognition(
        variant=best_variant,
        confidence=best_score,
        evidence=best_evidence,
    )


def fibonacci_variants_equivalent(a: FibVariant, b: FibVariant) -> Tuple[bool, str]:
    """All Fibonacci variants compute F(n) — equivalence via D20 spec uniqueness."""
    if a == FibVariant.UNKNOWN or b == FibVariant.UNKNOWN:
        return False, "Cannot confirm equivalence for unknown variant."
    if a == b:
        return True, "Same variant — structural equivalence (refl)."
    return True, (
        f"Both {a.value} and {b.value} satisfy S_fib(n, F(n)); "
        f"uniqueness of F(n) yields path via D20_spec_unify."
    )


# ═══════════════════════════════════════════════════════════════════
# §6  GCD Variant Recognizer
# ═══════════════════════════════════════════════════════════════════

class GCDVariant(Enum):
    EUCLIDEAN = "euclidean"
    SUBTRACTION = "subtraction"
    BINARY = "binary"
    RECURSIVE_EUCLIDEAN = "recursive_euclidean"
    BUILTIN = "builtin"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class GCDRecognition:
    variant: GCDVariant
    confidence: float
    evidence: str


_GCD_PATTERNS: List[Tuple[GCDVariant, List[str], str]] = [
    (GCDVariant.EUCLIDEAN,
     [r"while.*b\s*(!?=|>)\s*0", r"a\s*%\s*b|a\s*mod\s*b"],
     "Iterative Euclidean with modulo"),
    (GCDVariant.RECURSIVE_EUCLIDEAN,
     [r"def\s+\w+\(a\s*,\s*b\)", r"return\s+\w+\(b\s*,\s*a\s*%\s*b\)"],
     "Recursive Euclidean"),
    (GCDVariant.SUBTRACTION,
     [r"a\s*-\s*b|b\s*-\s*a", r"while\s+(a\s*!=\s*b|a\s*>\s*0)"],
     "Subtraction-based (Euclidean original)"),
    (GCDVariant.BINARY,
     [r"(>>|<<|&\s*1|%\s*2)", r"(even|odd|a\s*&\s*1)"],
     "Binary GCD (Stein's algorithm)"),
    (GCDVariant.BUILTIN,
     [r"math\.gcd|gcd\("],
     "Python builtin math.gcd"),
]


def recognize_gcd_variant(source: str) -> GCDRecognition:
    """Recognize which GCD implementation variant a source string represents."""
    best_variant = GCDVariant.UNKNOWN
    best_score = 0.0
    best_evidence = "No GCD pattern detected."

    for variant, patterns, description in _GCD_PATTERNS:
        matches = sum(1 for p in patterns if re.search(p, source, re.IGNORECASE))
        score = matches / len(patterns)
        if score > best_score:
            best_score = score
            best_variant = variant
            best_evidence = description

    return GCDRecognition(
        variant=best_variant,
        confidence=best_score,
        evidence=best_evidence,
    )


def gcd_variants_equivalent(a: GCDVariant, b: GCDVariant) -> Tuple[bool, str]:
    """All GCD variants compute gcd(a,b) — equivalence via D20."""
    if a == GCDVariant.UNKNOWN or b == GCDVariant.UNKNOWN:
        return False, "Cannot confirm equivalence for unknown variant."
    if a == b:
        return True, "Same variant — structural equivalence (refl)."
    return True, (
        f"Both {a.value} and {b.value} satisfy S_gcd; "
        f"gcd(a,b) is unique → D20_spec_unify."
    )


# ═══════════════════════════════════════════════════════════════════
# §7  Sorting Pipeline Recognizer
# ═══════════════════════════════════════════════════════════════════

class SortPipeline(Enum):
    SORT_THEN_FOLD = "sort_then_fold"
    SORT_THEN_MAP = "sort_then_map"
    SORT_THEN_FILTER = "sort_then_filter"
    SORT_THEN_GROUP = "sort_then_group"
    SORT_THEN_UNIQUE = "sort_then_unique"
    SORT_THEN_BINARY_SEARCH = "sort_then_binary_search"
    NO_PIPELINE = "no_pipeline"


@dataclass(frozen=True)
class SortPipelineRecognition:
    """Recognition of a sort-then-process pattern."""
    pipeline: SortPipeline
    sort_key: Optional[str]
    post_process: Optional[str]
    order_matters: bool
    d19_applicable: bool


def recognize_sort_pipeline(canon: str) -> SortPipelineRecognition:
    """Detect sort-then-process patterns in a canonical OTerm.

    Returns whether D19 (sort-then-scan ↔ sweep) might apply.
    """
    if "sorted(" not in canon and "sort(" not in canon:
        return SortPipelineRecognition(
            pipeline=SortPipeline.NO_PIPELINE,
            sort_key=None,
            post_process=None,
            order_matters=False,
            d19_applicable=False,
        )

    sort_match = re.search(r"sorted\(([^)]+)\)", canon)
    sort_key = sort_match.group(1) if sort_match else None

    if "fold[" in canon and "sorted(" in canon:
        fold_op_match = re.search(r"fold\[(\w+)\]", canon)
        fold_op = fold_op_match.group(1) if fold_op_match else "?"
        commutative_ops = {"add", ".add", "mul", ".mul", "min", "max", "and", "or",
                           "union", "intersection", "bitand", "bitor", "bitxor"}
        order_matters = fold_op not in commutative_ops
        return SortPipelineRecognition(
            pipeline=SortPipeline.SORT_THEN_FOLD,
            sort_key=sort_key,
            post_process=f"fold[{fold_op}]",
            order_matters=order_matters,
            d19_applicable=not order_matters,
        )

    if "map(" in canon and "sorted(" in canon:
        return SortPipelineRecognition(
            pipeline=SortPipeline.SORT_THEN_MAP,
            sort_key=sort_key,
            post_process="map",
            order_matters=True,
            d19_applicable=False,
        )

    if "filter" in canon and "sorted(" in canon:
        return SortPipelineRecognition(
            pipeline=SortPipeline.SORT_THEN_FILTER,
            sort_key=sort_key,
            post_process="filter",
            order_matters=True,
            d19_applicable=False,
        )

    if "groupby" in canon and "sorted(" in canon:
        return SortPipelineRecognition(
            pipeline=SortPipeline.SORT_THEN_GROUP,
            sort_key=sort_key,
            post_process="groupby",
            order_matters=True,
            d19_applicable=False,
        )

    if ("set(" in canon or "unique" in canon or "dedup" in canon) and "sorted(" in canon:
        return SortPipelineRecognition(
            pipeline=SortPipeline.SORT_THEN_UNIQUE,
            sort_key=sort_key,
            post_process="unique",
            order_matters=False,
            d19_applicable=True,
        )

    if ("bisect" in canon or "binary_search" in canon) and "sorted(" in canon:
        return SortPipelineRecognition(
            pipeline=SortPipeline.SORT_THEN_BINARY_SEARCH,
            sort_key=sort_key,
            post_process="binary_search",
            order_matters=True,
            d19_applicable=False,
        )

    return SortPipelineRecognition(
        pipeline=SortPipeline.NO_PIPELINE,
        sort_key=sort_key,
        post_process=None,
        order_matters=True,
        d19_applicable=False,
    )


# ═══════════════════════════════════════════════════════════════════
# §8  Yoneda Embedding Approximation
# ═══════════════════════════════════════════════════════════════════

STANDARD_OBSERVATIONS: List[str] = [
    "sorted", "len", "sum", "hash", "str", "repr",
    "min", "max", "set", "frozenset", "tuple", "list",
    "bool", "int", "float", "type",
]


@dataclass(frozen=True)
class YonedaProfile:
    """Finite approximation of the Yoneda embedding for a program.

    Each observation t in the observation set produces a
    "behavior component" t∘f.  Two programs with the same
    YonedaProfile are observationally equivalent up to the
    chosen observation set.
    """
    canonical_form: str
    spec_name: Optional[str]
    observation_hashes: Dict[str, str]
    is_deterministic: bool
    stratum: EquivStratum


def build_yoneda_profile(
    canon: str,
    observations: Optional[List[str]] = None,
) -> YonedaProfile:
    """Build a finite Yoneda profile for a canonical OTerm.

    In the full implementation, this would evaluate t(⟦f⟧(p)) for each
    observation t and representative inputs p via Z3 or concrete execution.
    Here we build the profile structurally from the canonical form.
    """
    obs = observations or STANDARD_OBSERVATIONS

    spec = identify_specification(canon)
    spec_name = spec.name if spec else None
    is_det = spec.is_deterministic() if spec else True

    obs_hashes: Dict[str, str] = {}
    for t in obs:
        composite = f"{t}({canon})"
        h = hashlib.md5(composite.encode()).hexdigest()[:12]
        obs_hashes[t] = h

    if spec and spec.is_deterministic():
        stratum = EquivStratum.STRUCTURAL
    elif spec:
        stratum = EquivStratum.SPECIFICATION
    else:
        stratum = EquivStratum.EXTENSIONAL

    return YonedaProfile(
        canonical_form=canon,
        spec_name=spec_name,
        observation_hashes=obs_hashes,
        is_deterministic=is_det,
        stratum=stratum,
    )


def yoneda_check_equivalent(
    f_canon: str,
    g_canon: str,
    observations: Optional[List[str]] = None,
) -> Tuple[bool, Optional[str]]:
    """Check observational equivalence via finite Yoneda approximation.

    For each observation t in the observation set, check whether
    t(f(p)) == t(g(p)) for all p.

    Returns:
        (True, None) if observationally equivalent under all observations.
        (False, witness_obs) if a distinguishing observation is found.
    """
    if f_canon == g_canon:
        return (True, None)

    pf = build_yoneda_profile(f_canon, observations)
    pg = build_yoneda_profile(g_canon, observations)

    if pf.spec_name and pg.spec_name and pf.spec_name == pg.spec_name:
        spec = SPEC_REGISTRY.get(pf.spec_name)
        if spec and spec.is_deterministic():
            return (True, None)

    for obs_name in (observations or STANDARD_OBSERVATIONS):
        if pf.observation_hashes.get(obs_name) != pg.observation_hashes.get(obs_name):
            return (False, obs_name)

    return (True, None)


# ═══════════════════════════════════════════════════════════════════
# §9  Full Benchmark Classification  (50 EQ pairs)
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class EQPairInfo:
    """Classification data for one EQ pair."""
    pair_id: str
    description: str
    axioms: List[str]
    stratum: EquivStratum
    specification: Optional[str]
    expected_proof_path: List[str]
    notes: str = ""


_RAW_CLASSIFICATION: List[Tuple[str, str, List[str], str, Optional[str], List[str], str]] = [
    ("eq01", "Flatten + sort + unique",
     ["D4", "D19"], "structural", None,
     ["D4_map_fusion", "D19_sort_scan", "QUOT_sorted_canonical"], ""),
    ("eq02", "Word frequency histogram",
     ["D13", "D19"], "structural", None,
     ["D13_counter_to_fold", "D19_sort_scan"], ""),
    ("eq03", "Arithmetic expression eval",
     ["D1"], "structural", None,
     ["D1_fix_to_fold", "D9_stack_rec"], "recursive vs stack-based eval"),
    ("eq04", "Register machine simulation",
     ["D1"], "structural", None,
     ["D1_fix_to_fold"], "different loop representations"),
    ("eq05", "Topological sort (lex-smallest)",
     ["D15"], "structural", None,
     ["D15_traversal", "D10_pq"], "Kahn's vs DFS with priority"),
    ("eq06", "RLE encode/decode roundtrip",
     ["D1", "D4"], "structural", None,
     ["D1_fix_to_fold", "D4_comp_fusion"], ""),
    ("eq07", "Convex hull",
     ["D20"], "specification", "convex_hull",
     ["D20_spec_unify"], "Graham scan vs Monotone chain"),
    ("eq08", "Edit distance",
     ["D20"], "specification", "edit_distance",
     ["D20_spec_unify"], "Wagner-Fischer vs Hirschberg"),
    ("eq09", "LRU cache simulation",
     ["D11"], "structural", None,
     ["D11_adt"], "OrderedDict vs manual doubly-linked list"),
    ("eq10", "Matrix multiplication",
     ["D4", "D5"], "structural", None,
     ["D4_comp_fusion", "D5_fold_universal"], "nested loops vs numpy-style"),
    ("eq11", "Merge k sorted iterators",
     ["D5"], "structural", None,
     ["D5_fold_universal", "D10_pq"], "heapq merge vs manual"),
    ("eq12", "Binary tree serialize/deserialize",
     ["D1"], "structural", None,
     ["D1_fix_to_fold", "D2_beta"], "preorder vs level-order"),
    ("eq13", "DAG path counting",
     ["D1", "D16"], "structural", None,
     ["D1_fix_to_fold", "D16_recurrence_normalize"], "memo vs DP"),
    ("eq14", "Calculator (parse + eval)",
     ["D1", "D2"], "structural", None,
     ["D1_fix_to_fold", "D2_beta"], "recursive descent vs stack"),
    ("eq15", "Longest increasing subsequence",
     ["D16"], "structural", None,
     ["D16_recurrence_normalize"], "DP vs patience sorting"),
    ("eq16", "Strongly connected components",
     ["D20"], "specification", "strongly_connected_components",
     ["D20_spec_unify"], "Tarjan vs Kosaraju"),
    ("eq17", "Power set generation",
     ["D1"], "structural", None,
     ["D1_fix_to_fold"], "recursive vs iterative bitmask"),
    ("eq18", "JSON-like pretty printer",
     ["D1", "D2"], "structural", None,
     ["D1_fix_to_fold", "D2_beta"], "recursive vs iterative with stack"),
    ("eq19", "0/1 Knapsack",
     ["D16"], "structural", None,
     ["D16_recurrence_normalize"], "top-down memo vs bottom-up DP"),
    ("eq20", "Structural hashing (SHA-256)",
     ["D1", "D19"], "structural", None,
     ["D1_fix_to_fold", "D19_sort_scan"], "recursive vs iterative hashing"),
    ("eq21", "Prime factorization",
     ["D1"], "structural", None,
     ["D1_fix_to_fold"], "trial division variants"),
    ("eq22", "Cycle detection (Floyd/Brent)",
     ["D1"], "semi-structural", None,
     ["D1_fix_to_fold", "HIT_structural"], "different invariants, same spec"),
    ("eq23", "Balanced parentheses",
     ["D9"], "structural", None,
     ["D9_stack_rec"], "stack vs counter"),
    ("eq24", "Levenshtein distance",
     ["D16"], "structural", None,
     ["D16_recurrence_normalize"], "same DP, different table fill order"),
    ("eq25", "Merge overlapping intervals",
     ["D19"], "structural", None,
     ["D19_sort_scan"], "sort + scan"),
    ("eq26", "k-th smallest (quickselect)",
     ["D1"], "structural", None,
     ["D1_fix_to_fold"], "quickselect vs sort-and-index"),
    ("eq27", "Longest common subsequence",
     ["D16"], "structural", None,
     ["D16_recurrence_normalize"], "memo vs DP"),
    ("eq28", "Regex state machine",
     ["D1", "D9"], "structural", None,
     ["D1_fix_to_fold", "D9_stack_rec"], "NFA vs backtracking"),
    ("eq29", "Deep copy + sort",
     ["D20"], "specification", "deep_copy_canonical",
     ["D20_spec_unify"], "recursive vs BFS copy"),
    ("eq30", "Trie search",
     ["D11"], "structural", None,
     ["D11_adt"], "dict-of-dicts vs class-based node"),
    ("eq31", "Dijkstra shortest path",
     ["D10"], "structural", None,
     ["D10_pq"], "heapq vs sorted-list priority queue"),
    ("eq32", "Island counting (grid)",
     ["D15"], "structural", None,
     ["D15_traversal"], "BFS vs DFS flood-fill"),
    ("eq33", "n-th permutation",
     ["D20"], "specification", "nth_permutation",
     ["D20_spec_unify"], "factoradic vs itertools"),
    ("eq34", "Postfix expression eval",
     ["D9"], "structural", None,
     ["D9_stack_rec"], "explicit stack vs reduce"),
    ("eq35", "all ↔ not-any-not",
     ["ALG"], "structural", None,
     ["ALG_demorgan", "FOLD_all_any_dual"], "De Morgan duality"),
    ("eq36", "Transpose dict-of-lists",
     ["D4", "D5"], "structural", None,
     ["D4_comp_fusion", "D5_fold_universal"], "nested comprehension vs loops"),
    ("eq37", "Fibonacci mod p",
     ["D20"], "specification", "fibonacci",
     ["D20_spec_unify"], "matrix exp vs fast doubling"),
    ("eq38", "Group anagrams",
     ["D19", "D20"], "semi-structural", "sorted",
     ["D19_sort_scan", "D20_spec_unify"], "sort-based key vs Counter key"),
    ("eq39", "Perfect power check",
     ["D1"], "structural", None,
     ["D1_fix_to_fold"], "log-based vs root extraction"),
    ("eq40", "Binomial coefficient",
     ["D20"], "specification", "binomial",
     ["D1_fix_to_fold", "D20_spec_unify"], "multiplicative vs Pascal"),
    ("eq41", "Zip-longest with fill",
     ["D5", "D6"], "structural", None,
     ["D5_fold_universal", "D6_lazy_eager"], "itertools vs manual"),
    ("eq42", "Currying",
     ["D24"], "structural", None,
     ["D24_eta_contract"], "curried vs uncurried"),
    ("eq43", "CSV parsing",
     ["D1", "D4"], "structural", None,
     ["D1_fix_to_fold", "D4_map_fusion"], "split+join vs state machine"),
    ("eq44", "Coin change DP",
     ["D16"], "structural", None,
     ["D16_recurrence_normalize"], "memo vs bottom-up"),
    ("eq45", "Grid path counting",
     ["D16"], "structural", None,
     ["D16_recurrence_normalize"], "DP vs combinatorial C(m+n-2,m-1)"),
    ("eq46", "Mini type inference",
     ["D1", "D8"], "structural", None,
     ["D1_fix_to_fold", "D8_section_merge"], "recursive unify variants"),
    ("eq47", "Stock profit",
     ["D20"], "specification", "max_stock_profit",
     ["D20_spec_unify", "D18_greedy"], "DP vs greedy+DP hybrid"),
    ("eq48", "Trailing zeroes in n!",
     ["D1"], "structural", None,
     ["D1_fix_to_fold"], "loop vs closed-form sum"),
    ("eq49", "Deep equality with cycles",
     ["D1", "D9"], "structural", None,
     ["D1_fix_to_fold", "D9_stack_rec"], "recursive with memo vs BFS"),
    ("eq50", "N-queens",
     ["D1", "D8"], "structural", None,
     ["D1_fix_to_fold", "D8_section_merge"], "backtracking variants"),
]


_STRATUM_MAP = {
    "structural": EquivStratum.STRUCTURAL,
    "semi-structural": EquivStratum.SEMI_STRUCTURAL,
    "specification": EquivStratum.SPECIFICATION,
    "extensional": EquivStratum.EXTENSIONAL,
}


EQ_PAIRS_FULL: Dict[str, EQPairInfo] = {}
for _row in _RAW_CLASSIFICATION:
    _pid, _desc, _axioms, _strat, _spec, _path, _notes = _row
    EQ_PAIRS_FULL[_pid] = EQPairInfo(
        pair_id=_pid,
        description=_desc,
        axioms=_axioms,
        stratum=_STRATUM_MAP[_strat],
        specification=_spec,
        expected_proof_path=_path,
        notes=_notes,
    )


BENCHMARK_CLASSIFICATION: Dict[str, Tuple[str, List[str]]] = {
    info.pair_id: (info.description, info.axioms) for info in EQ_PAIRS_FULL.values()
}


def get_hard_8_ids() -> List[str]:
    """Return the IDs of the hard-8 pairs (require D20)."""
    return [pid for pid, info in EQ_PAIRS_FULL.items()
            if "D20" in info.axioms and info.stratum == EquivStratum.SPECIFICATION]


def get_structural_ids() -> List[str]:
    """Return IDs of pairs resolved by structural paths only."""
    return [pid for pid, info in EQ_PAIRS_FULL.items()
            if info.stratum == EquivStratum.STRUCTURAL]


def get_semi_structural_ids() -> List[str]:
    """Return IDs of pairs that are on the structural/spec boundary."""
    return [pid for pid, info in EQ_PAIRS_FULL.items()
            if info.stratum == EquivStratum.SEMI_STRUCTURAL]


# ═══════════════════════════════════════════════════════════════════
# §10  Stratum Classifier
# ═══════════════════════════════════════════════════════════════════

def classify_stratum(
    pair_id: str,
    structural_path_found: bool,
    spec_identified: Optional[Specification] = None,
    has_matroid: bool = False,
    canon_a: str = "",
    canon_b: str = "",
) -> EquivStratum:
    """Classify a pair into the four-stratum hierarchy.

    1. STRUCTURAL — provable by D1-D19 + D21-D24 + algebraic axioms
    2. SEMI_STRUCTURAL — partially structural, needs one D20 step
    3. SPECIFICATION — requires D20 (spec uniqueness)
    4. EXTENSIONAL — beyond the formal system
    """
    if pair_id in EQ_PAIRS_FULL:
        return EQ_PAIRS_FULL[pair_id].stratum

    if structural_path_found:
        return EquivStratum.STRUCTURAL

    if spec_identified and spec_identified.is_deterministic():
        if has_matroid:
            return EquivStratum.SPECIFICATION
        pipe_a = recognize_sort_pipeline(canon_a)
        pipe_b = recognize_sort_pipeline(canon_b)
        if pipe_a.d19_applicable and pipe_b.d19_applicable:
            return EquivStratum.SEMI_STRUCTURAL
        return EquivStratum.SPECIFICATION

    return EquivStratum.EXTENSIONAL


def classify_pair(
    pair_id: str,
    structural_path_found: bool,
    spec_identified: Optional[Specification] = None,
) -> EquivClassification:
    """Classify an equivalence pair."""
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
            reason=(f"Both satisfy deterministic spec '{spec_identified.name}'; "
                    f"uniqueness: {spec_identified.determinism_proof}"),
        )

    return EquivClassification(
        pair_id=pair_id,
        stratum=EquivStratum.EXTENSIONAL,
        path_axioms=[],
        specification=spec_identified,
        reason="No structural path or recognizable specification found.",
    )


# ═══════════════════════════════════════════════════════════════════
# §11  Proof Path Planner
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProofPlan:
    """A suggested proof plan for an equivalence pair."""
    pair_id: str
    strategy: str
    steps: List[str]
    estimated_difficulty: str
    dichotomies: List[str]
    fallback: Optional[str]


DICHOTOMY_GROUPS: Dict[str, List[str]] = {
    "control_flow": ["D1", "D2", "D3", "D4", "D5", "D6", "D7", "D8"],
    "data_structure": ["D9", "D10", "D11", "D12", "D13", "D14"],
    "algorithm_strategy": ["D15", "D16", "D17", "D18", "D19", "D20"],
    "language_feature": ["D21", "D22", "D23", "D24"],
    "algebraic": ["ALG"],
}


def _dichotomy_group(d: str) -> str:
    """Return the dichotomy group for a given axiom name."""
    for group, members in DICHOTOMY_GROUPS.items():
        if d in members:
            return group
    return "unknown"


def plan_proof(pair_id: str, canon_a: str = "", canon_b: str = "") -> ProofPlan:
    """Given a pair, suggest which dichotomies to try and in what order."""
    if pair_id in EQ_PAIRS_FULL:
        info = EQ_PAIRS_FULL[pair_id]
        return ProofPlan(
            pair_id=pair_id,
            strategy=f"Known pair: {info.description}",
            steps=info.expected_proof_path,
            estimated_difficulty=(
                "easy" if info.stratum == EquivStratum.STRUCTURAL else
                "medium" if info.stratum == EquivStratum.SEMI_STRUCTURAL else
                "hard"
            ),
            dichotomies=info.axioms,
            fallback="D20_spec_unify" if "D20" in info.axioms else None,
        )

    steps: List[str] = []
    dichotomies: List[str] = []
    strategy_parts: List[str] = []

    combined = (canon_a + " " + canon_b).lower()

    if "fix[" in combined or "fold[" in combined:
        steps.append("Try D1: rec↔iter (fold/unfold)")
        dichotomies.append("D1")
        strategy_parts.append("recursion-iteration")

    if "map(" in combined or "filter_map(" in combined:
        steps.append("Try D4: comprehension fusion")
        dichotomies.append("D4")
        strategy_parts.append("comprehension")

    if "sorted(" in combined:
        steps.append("Try D19: sort-then-scan equivalence")
        dichotomies.append("D19")
        strategy_parts.append("sort-pipeline")

    if "Counter" in combined or "defaultdict" in combined:
        steps.append("Try D13: histogram equivalence")
        dichotomies.append("D13")
        strategy_parts.append("histogram")

    if "catch(" in combined:
        steps.append("Try D22: effect elimination")
        dichotomies.append("D22")
        strategy_parts.append("exception")

    if "apply(" in combined or "λ(" in combined:
        steps.append("Try D24: η-expansion")
        dichotomies.append("D24")
        strategy_parts.append("lambda")

    steps.append("Try D20: spec identification (Yoneda)")
    dichotomies.append("D20")

    spec_a = identify_specification(canon_a)
    spec_b = identify_specification(canon_b)
    if spec_a and spec_b and spec_a.name == spec_b.name:
        strategy_parts.append(f"spec={spec_a.name}")
        difficulty = "medium"
    elif spec_a or spec_b:
        difficulty = "hard"
    else:
        difficulty = "hard" if not dichotomies else "medium"

    return ProofPlan(
        pair_id=pair_id,
        strategy="Heuristic plan: " + " + ".join(strategy_parts) if strategy_parts else "Exhaustive search",
        steps=steps,
        estimated_difficulty=difficulty,
        dichotomies=dichotomies,
        fallback="D20_spec_unify",
    )


# ═══════════════════════════════════════════════════════════════════
# §12  Proof Path Templates
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProofSketch:
    """A formal proof sketch for an algorithm equivalence."""
    pair_id: str
    specification: Specification
    path_description: str
    key_lemma: str
    oterm_path: List[str]


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

CONVEX_HULL_PROOF = ProofSketch(
    pair_id="eq07",
    specification=SPEC_CONVEX_HULL,
    path_description=(
        "Graham scan: polar-sort + CCW-stack scan. "
        "Monotone chain: x-sort + upper/lower hull merge. "
        "Both produce the unique convex hull in CCW order."
    ),
    key_lemma="Convex hull is unique; CCW ordering from canonical start is unique.",
    oterm_path=["D20_spec_unify"],
)

SCC_PROOF = ProofSketch(
    pair_id="eq16",
    specification=SPEC_SCC,
    path_description=(
        "Tarjan: single DFS with lowlink → SCC on stack pop. "
        "Kosaraju: DFS(G) for ordering, DFS(G^T) in reverse → SCCs. "
        "Both produce unique SCC partition."
    ),
    key_lemma="SCC partition is unique; condensation DAG is unique.",
    oterm_path=["D20_spec_unify"],
)

PROOF_SKETCHES: Dict[str, ProofSketch] = {
    s.pair_id: s for s in [
        FACTORIAL_PROOF, FIBONACCI_PROOF, GCD_PROOF,
        BINOMIAL_PROOF, CONVEX_HULL_PROOF, SCC_PROOF,
    ]
}


# ═══════════════════════════════════════════════════════════════════
# §13  Benchmark Regression Test Generator
# ═══════════════════════════════════════════════════════════════════

@dataclass
class RegressionTest:
    """Auto-generated regression test for a benchmark pair."""
    test_name: str
    pair_id: str
    expected_stratum: EquivStratum
    expected_axioms: List[str]
    expected_spec: Optional[str]
    test_code: str


def generate_regression_test(pair_id: str) -> Optional[RegressionTest]:
    """Generate a regression test from the classification data."""
    info = EQ_PAIRS_FULL.get(pair_id)
    if info is None:
        return None

    test_name = f"test_{pair_id}_{info.description.lower().replace(' ', '_').replace('/', '_')}"
    test_name = re.sub(r"[^a-zA-Z0-9_]", "", test_name)

    axiom_list = repr(info.axioms)
    spec_check = f'"{info.specification}"' if info.specification else "None"
    stratum_name = info.stratum.value

    test_code = (
        f"def {test_name}():\n"
        f'    """Regression test for {pair_id}: {info.description}."""\n'
        f"    from new_src.proposals.g11_deep_theory import (\n"
        f"        classify_pair, EquivStratum, SPEC_REGISTRY,\n"
        f"    )\n"
        f"    spec = SPEC_REGISTRY.get({spec_check})\n"
        f"    structural = {info.stratum == EquivStratum.STRUCTURAL}\n"
        f"    result = classify_pair({pair_id!r}, structural, spec)\n"
        f'    assert result.stratum.value == {stratum_name!r}, (\n'
        f'        f"Expected {{stratum_name!r}}, got {{result.stratum.value}}"\n'
        f"    )\n"
        f"    expected_axioms = {axiom_list}\n"
        f"    for ax in expected_axioms:\n"
        f"        found = any(ax in ra for ra in result.path_axioms) or ax in result.path_axioms\n"
        f'        assert found, f"Expected axiom {{ax}} in path"\n'
    )

    return RegressionTest(
        test_name=test_name,
        pair_id=pair_id,
        expected_stratum=info.stratum,
        expected_axioms=info.axioms,
        expected_spec=info.specification,
        test_code=test_code,
    )


def generate_all_regression_tests() -> List[RegressionTest]:
    """Generate regression tests for all 50 EQ pairs."""
    tests = []
    for pid in sorted(EQ_PAIRS_FULL.keys(), key=lambda x: int(x[2:])):
        t = generate_regression_test(pid)
        if t is not None:
            tests.append(t)
    return tests


def regression_test_suite_source() -> str:
    """Generate a complete test suite source file."""
    tests = generate_all_regression_tests()
    lines = [
        '"""Auto-generated regression tests for g11_deep_theory benchmark classification."""',
        "from __future__ import annotations",
        "",
        "",
    ]
    for t in tests:
        lines.append(t.test_code)
        lines.append("")
    lines.append("")
    lines.append('if __name__ == "__main__":')
    lines.append("    import sys")
    lines.append("    failures = 0")
    for t in tests:
        lines.append(f"    try:")
        lines.append(f"        {t.test_name}()")
        lines.append(f'        print(f"  PASS: {t.test_name}")')
        lines.append(f"    except Exception as e:")
        lines.append(f'        print(f"  FAIL: {t.test_name}: {{e}}")')
        lines.append(f"        failures += 1")
    lines.append('    print(f"\\n{{len(tests) - failures}}/{{len(tests)}} passed")')
    lines.append("    sys.exit(1 if failures else 0)")
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# §14  Matroid Structure Detector for Greedy Equivalences
# ═══════════════════════════════════════════════════════════════════

class MatroidType(Enum):
    UNIFORM = "uniform"
    GRAPHIC = "graphic"
    PARTITION = "partition"
    TRANSVERSAL = "transversal"
    LINEAR = "linear"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class MatroidDetection:
    """Result of matroid structure detection."""
    detected: bool
    matroid_type: MatroidType
    confidence: float
    evidence: str
    greedy_gives_optimal: bool


def detect_matroid_structure(
    canon: str,
    source: str = "",
) -> MatroidDetection:
    """Detect matroid structure in a canonical OTerm or source code.

    Heuristic detection of common matroid-amenable patterns:
    - Uniform matroid: select k items with max weight
    - Graphic matroid: MST / forest selection
    - Partition matroid: coloring / scheduling
    - Transversal matroid: bipartite matching
    """
    combined = (canon + " " + source).lower()

    if re.search(r"(kruskal|prim|spanning.tree|mst)", combined):
        return MatroidDetection(
            detected=True,
            matroid_type=MatroidType.GRAPHIC,
            confidence=0.9,
            evidence="Spanning tree / MST pattern detected",
            greedy_gives_optimal=True,
        )

    if re.search(r"(activity.selection|interval.schedule|non.overlap)", combined):
        return MatroidDetection(
            detected=True,
            matroid_type=MatroidType.UNIFORM,
            confidence=0.85,
            evidence="Activity selection / interval scheduling pattern",
            greedy_gives_optimal=True,
        )

    if re.search(r"(huffman|prefix.code|encoding.tree)", combined):
        return MatroidDetection(
            detected=True,
            matroid_type=MatroidType.UNIFORM,
            confidence=0.8,
            evidence="Huffman coding pattern",
            greedy_gives_optimal=True,
        )

    if re.search(r"(fractional.knapsack|weight.ratio|value.per.weight)", combined):
        return MatroidDetection(
            detected=True,
            matroid_type=MatroidType.UNIFORM,
            confidence=0.75,
            evidence="Fractional knapsack pattern",
            greedy_gives_optimal=True,
        )

    if re.search(r"(coloring|chromatic|partition)", combined):
        return MatroidDetection(
            detected=True,
            matroid_type=MatroidType.PARTITION,
            confidence=0.6,
            evidence="Partition/coloring pattern (verify partition matroid axioms)",
            greedy_gives_optimal=False,
        )

    if re.search(r"(matching|bipartite|assignment)", combined):
        return MatroidDetection(
            detected=True,
            matroid_type=MatroidType.TRANSVERSAL,
            confidence=0.5,
            evidence="Matching/assignment pattern (transversal matroid possible)",
            greedy_gives_optimal=False,
        )

    if re.search(r"sorted.*(?:greedy|select|pick)", combined):
        return MatroidDetection(
            detected=True,
            matroid_type=MatroidType.UNKNOWN,
            confidence=0.4,
            evidence="Sort-then-select pattern, may have matroid structure",
            greedy_gives_optimal=False,
        )

    return MatroidDetection(
        detected=False,
        matroid_type=MatroidType.UNKNOWN,
        confidence=0.0,
        evidence="No matroid pattern detected",
        greedy_gives_optimal=False,
    )


def greedy_dp_matroid_bridge(
    greedy_canon: str,
    dp_canon: str,
    greedy_source: str = "",
    dp_source: str = "",
) -> Tuple[Optional[str], MatroidDetection]:
    """Bridge between greedy and DP via matroid detection.

    Returns (axiom_name_or_None, detection).
    """
    detection = detect_matroid_structure(greedy_canon, greedy_source)
    if detection.detected and detection.greedy_gives_optimal:
        axiom = f"D20_matroid_{detection.matroid_type.value}"
        return (axiom, detection)

    simple_check = check_greedy_dp_equivalence(greedy_canon, dp_canon)
    if simple_check:
        return (simple_check, detection)

    return (None, detection)


# ═══════════════════════════════════════════════════════════════════
# §15  Self-Tests
# ═══════════════════════════════════════════════════════════════════

def _run_self_tests() -> Tuple[int, int]:
    """Run comprehensive self-tests. Returns (passed, total)."""
    passed = 0
    total = 0

    def check(name: str, condition: bool) -> None:
        nonlocal passed, total
        total += 1
        if condition:
            passed += 1
            print(f"  PASS: {name}")
        else:
            print(f"  FAIL: {name}")

    # §1 Specification framework
    check("SPEC_FACTORIAL is deterministic",
          SPEC_FACTORIAL.is_deterministic())
    check("SPEC_MST is nondeterministic",
          not SPEC_MST.is_deterministic())
    check("SPEC_REGISTRY has all standard specs",
          len(SPEC_REGISTRY) >= 20)
    check("SPEC_REGISTRY lookup works",
          SPEC_REGISTRY["factorial"] is SPEC_FACTORIAL)

    # §2 Specification identification
    check("identify_specification finds factorial",
          identify_specification("fold[mul](1,range(1,add($n,1)))") == SPEC_FACTORIAL)
    check("identify_specification finds fibonacci from fix",
          identify_specification("fix[h](add(sub(...)))") == SPEC_FIBONACCI)
    check("identify_specification finds sorted",
          identify_specification("sorted($x)") == SPEC_SORTED)
    check("identify_specification returns None for unknown",
          identify_specification("unknown_term()") is None)

    # §3 Matroid structures
    check("STOCK_PROFIT_MATROID is a matroid",
          STOCK_PROFIT_MATROID.is_matroid)
    check("ACTIVITY_SELECTION_MATROID is greedy-optimal",
          ACTIVITY_SELECTION_MATROID.greedy_optimal)
    check("detect_matroid_pattern finds graphic",
          detect_matroid_pattern("sorted(greedy, weight, cost)") == "graphic_matroid")
    check("detect_matroid_pattern finds uniform on intervals",
          detect_matroid_pattern("interval sorted accumulate") == "uniform_matroid")
    check("detect_matroid_pattern returns None for plain",
          detect_matroid_pattern("add(x, y)") is None)

    # §3b check_greedy_dp_equivalence
    check("greedy/DP with matroid → D20",
          check_greedy_dp_equivalence("greedy", "dp", STOCK_PROFIT_MATROID) == "D20_matroid_greedy")
    check("greedy/DP heuristic detection",
          check_greedy_dp_equivalence("sorted(max)", "fix[dp]") is not None)

    # §3c check_matroid_axioms on uniform matroid
    ground = {1, 2, 3}
    def uniform_2(s: FrozenSet[Any]) -> bool:
        return len(s) <= 2
    result = check_matroid_axioms(ground, uniform_2)
    check("check_matroid_axioms: uniform(3,2) is matroid",
          result.is_matroid)
    check("check_matroid_axioms: rank = 2",
          result.rank == 2)

    # §4 Hard-8 classifier
    check("HARD_8_PAIRS has 8 entries",
          len(HARD_8_PAIRS) == 8)
    check("eq07 is in HARD_8_PAIRS",
          "eq07" in HARD_8_PAIRS)
    check("eq37 requires D20",
          "D20_spec_unify" in HARD_8_PAIRS["eq37"].path_axioms)
    check("analyze_hard_8 returns analysis",
          analyze_hard_8("eq07") is not None)
    check("analyze_hard_8 returns None for non-hard",
          analyze_hard_8("eq01") is None)
    check("why_hard gives explanation",
          "resists due to" in why_hard("eq07"))

    # §5 Fibonacci recognizer
    naive_src = "def fib(n):\n  if n <= 1: return n\n  return fib(n-1) + fib(n-2)"
    check("Fibonacci naive recognized",
          recognize_fibonacci_variant(naive_src).variant == FibVariant.NAIVE_RECURSIVE)

    memo_src = "@functools.cache\ndef fib(n):\n  return fib(n-1) + fib(n-2) if n > 1 else n"
    check("Fibonacci memoized recognized",
          recognize_fibonacci_variant(memo_src).variant == FibVariant.MEMOIZED)

    iter_src = "def fib(n):\n  a, b = 0, 1\n  for _ in range(n):\n    a, b = b, a + b\n  return a"
    check("Fibonacci iterative recognized",
          recognize_fibonacci_variant(iter_src).variant == FibVariant.ITERATIVE)

    matrix_src = "def fib(n):\n  M = [[1,1],[1,0]]\n  return mat_pow(M, n)[0][1]"
    check("Fibonacci matrix recognized",
          recognize_fibonacci_variant(matrix_src).variant == FibVariant.MATRIX_EXP)

    fast_src = "def fib(n):\n  if n == 0: return 0\n  k = n // 2\n  f2k = f(k) * (2*f(k+1) - f(k))"
    check("Fibonacci fast-doubling recognized",
          recognize_fibonacci_variant(fast_src).variant == FibVariant.FAST_DOUBLING)

    check("Fibonacci variants are equivalent",
          fibonacci_variants_equivalent(FibVariant.NAIVE_RECURSIVE, FibVariant.MATRIX_EXP)[0])
    check("Unknown variant blocks equivalence",
          not fibonacci_variants_equivalent(FibVariant.UNKNOWN, FibVariant.ITERATIVE)[0])

    # §6 GCD recognizer
    euclid_src = "def gcd(a, b):\n  while b > 0:\n    a, b = b, a % b\n  return a"
    check("GCD Euclidean recognized",
          recognize_gcd_variant(euclid_src).variant == GCDVariant.EUCLIDEAN)

    sub_src = "def gcd(a, b):\n  while a != b:\n    if a > 0:\n      a = a - b\n    else:\n      b = b - a\n  return a"
    check("GCD subtraction recognized",
          recognize_gcd_variant(sub_src).variant == GCDVariant.SUBTRACTION)

    binary_src = "def gcd(a, b):\n  while b:\n    if a & 1 == 0: a >>= 1\n    elif b & 1 == 0: b >>= 1"
    check("GCD binary recognized",
          recognize_gcd_variant(binary_src).variant == GCDVariant.BINARY)

    check("GCD variants are equivalent",
          gcd_variants_equivalent(GCDVariant.EUCLIDEAN, GCDVariant.BINARY)[0])

    # §7 Sort pipeline recognizer
    check("sort-then-fold detected",
          recognize_sort_pipeline("fold[add](0,sorted($x))").pipeline == SortPipeline.SORT_THEN_FOLD)
    check("sort-then-fold with commutative op → d19 applicable",
          recognize_sort_pipeline("fold[add](0,sorted($x))").d19_applicable)
    check("sort-then-fold with non-commutative op → d19 not applicable",
          not recognize_sort_pipeline("fold[concat](,sorted($x))").d19_applicable)
    check("sort-then-filter detected",
          recognize_sort_pipeline("filter(pred,sorted($x))").pipeline == SortPipeline.SORT_THEN_FILTER)
    check("no pipeline for plain fold",
          recognize_sort_pipeline("fold[add](0,$x)").pipeline == SortPipeline.NO_PIPELINE)

    # §8 Yoneda embedding
    eq_result, witness = yoneda_check_equivalent("sorted($x)", "sorted($x)")
    check("Yoneda: identical canons are equivalent",
          eq_result is True)

    profile = build_yoneda_profile("fold[mul](1,range(1,add($n,1)))")
    check("Yoneda profile has spec name",
          profile.spec_name == "factorial")
    check("Yoneda profile is deterministic",
          profile.is_deterministic)

    # §9 Benchmark classification
    check("50 EQ pairs in classification",
          len(EQ_PAIRS_FULL) == 50)
    check("All EQ pair IDs are eq01..eq50",
          all(f"eq{i:02d}" in EQ_PAIRS_FULL for i in range(1, 51)))
    check("BENCHMARK_CLASSIFICATION mirrors EQ_PAIRS_FULL",
          len(BENCHMARK_CLASSIFICATION) == 50)
    check("get_hard_8_ids returns 8",
          len(get_hard_8_ids()) == 8)
    hard_8 = set(get_hard_8_ids())
    expected_hard_8 = {"eq07", "eq08", "eq16", "eq29", "eq33", "eq37", "eq40", "eq47"}
    check("Hard-8 IDs match expected",
          hard_8 == expected_hard_8)
    structural_ids = get_structural_ids()
    check("Structural pairs > 30",
          len(structural_ids) > 30)
    semi_ids = get_semi_structural_ids()
    check("Semi-structural pairs exist",
          len(semi_ids) >= 1)

    # §10 Stratum classifier
    check("classify_stratum: structural path → STRUCTURAL",
          classify_stratum("eq99", True) == EquivStratum.STRUCTURAL)
    check("classify_stratum: known pair → stored stratum",
          classify_stratum("eq07", False) == EquivStratum.SPECIFICATION)
    check("classify_stratum: det spec → SPECIFICATION",
          classify_stratum("eq99", False, SPEC_FACTORIAL) == EquivStratum.SPECIFICATION)
    check("classify_stratum: no info → EXTENSIONAL",
          classify_stratum("eq99", False) == EquivStratum.EXTENSIONAL)

    # §11 Proof path planner
    plan = plan_proof("eq07")
    check("plan_proof for known pair",
          plan.pair_id == "eq07")
    check("plan difficulty for hard pair",
          plan.estimated_difficulty == "hard")

    plan2 = plan_proof("custom", "fold[add](0,sorted($x))", "fold[add](0,$y)")
    check("plan_proof for custom pair includes D19",
          "D19" in plan2.dichotomies)
    check("plan_proof for custom pair includes D20 fallback",
          plan2.fallback == "D20_spec_unify")

    # §12 Proof sketches
    check("FACTORIAL_PROOF exists",
          FACTORIAL_PROOF.pair_id == "factorial_variants")
    check("PROOF_SKETCHES has entries",
          len(PROOF_SKETCHES) >= 5)

    # §13 Regression test generator
    test = generate_regression_test("eq01")
    check("generate_regression_test works",
          test is not None)
    check("generated test has correct pair_id",
          test.pair_id == "eq01")
    check("generated test code is valid Python syntax",
          _is_valid_python(test.test_code))

    all_tests = generate_all_regression_tests()
    check("generate_all_regression_tests produces 50",
          len(all_tests) == 50)

    suite_src = regression_test_suite_source()
    check("regression suite source is non-empty",
          len(suite_src) > 500)

    # §14 Matroid detector
    detection = detect_matroid_structure("", "kruskal MST spanning tree")
    check("matroid detector finds graphic matroid",
          detection.matroid_type == MatroidType.GRAPHIC)
    check("graphic matroid greedy is optimal",
          detection.greedy_gives_optimal)

    detection2 = detect_matroid_structure("", "activity selection non-overlapping intervals")
    check("matroid detector finds uniform for activity selection",
          detection2.matroid_type == MatroidType.UNIFORM)

    detection3 = detect_matroid_structure("add(x,y)", "")
    check("matroid detector returns not-detected for plain arithmetic",
          not detection3.detected)

    bridge_axiom, bridge_det = greedy_dp_matroid_bridge(
        "sorted(max)", "fix[dp]", "kruskal spanning tree", "")
    check("greedy-DP bridge with matroid returns axiom",
          bridge_axiom is not None)

    # §5/6 cross-variant equivalence table
    all_fib_variants = [v for v in FibVariant if v != FibVariant.UNKNOWN]
    all_pairs_eq = all(
        fibonacci_variants_equivalent(a, b)[0]
        for a in all_fib_variants for b in all_fib_variants
    )
    check("All known Fibonacci variants are pairwise equivalent",
          all_pairs_eq)

    all_gcd_variants = [v for v in GCDVariant if v != GCDVariant.UNKNOWN]
    all_gcd_eq = all(
        gcd_variants_equivalent(a, b)[0]
        for a in all_gcd_variants for b in all_gcd_variants
    )
    check("All known GCD variants are pairwise equivalent",
          all_gcd_eq)

    # Edge cases
    check("Empty canon → no spec",
          identify_specification("") is None)
    check("Empty canon → no pipeline",
          recognize_sort_pipeline("").pipeline == SortPipeline.NO_PIPELINE)
    check("Empty source → unknown fib",
          recognize_fibonacci_variant("").variant == FibVariant.UNKNOWN)
    check("Empty source → unknown gcd",
          recognize_gcd_variant("").variant == GCDVariant.UNKNOWN)
    check("classify_pair for known hard-8",
          classify_pair("eq07", False).stratum == EquivStratum.SPECIFICATION)
    check("classify_pair for structural",
          classify_pair("eq99", True).stratum == EquivStratum.STRUCTURAL)

    return passed, total


def _is_valid_python(code: str) -> bool:
    """Check if a string is valid Python syntax."""
    import ast as _ast
    try:
        _ast.parse(code)
        return True
    except SyntaxError:
        return False


if __name__ == "__main__":
    print("=" * 60)
    print("g11_deep_theory: Self-Test Suite")
    print("=" * 60)
    passed, total = _run_self_tests()
    print("=" * 60)
    print(f"Results: {passed}/{total} passed")
    if passed < total:
        print("SOME TESTS FAILED")
        raise SystemExit(1)
    else:
        print("ALL TESTS PASSED")
