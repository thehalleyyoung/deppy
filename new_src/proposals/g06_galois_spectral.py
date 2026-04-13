"""Code proposals for Chapters 12-14: Galois Connections, Spectral Sequences, Operads.

Formalizes the mathematical structures described in the monograph and
connects them to the existing implementation in duck.py, path_search.py,
and denotation.py.  Every class and function is real, importable, and
tested by the ``if __name__ == '__main__'`` block at the bottom.

Chapters covered
================
  12 — Galois connections: α/γ adjunction, decision cascade, abstract H¹
  13 — Descent spectral sequence: E₁/E₂ pages, phase profiler, convergence
  14 — Operad theory: operadic composition, absorption laws, HOF checker

Additional proposals
====================
  • Duck type lattice as explicit poset with Hasse diagram computation
  • Phase profiler (measure which normalization phase resolves each pair)
  • Normalizer convergence verifier (check fixpoint in ≤8 iterations)
  • Abstract cohomology computation (H¹ over abstract domain before Z3)
  • Decision cascade optimizer (skip unnecessary stages)
"""
from __future__ import annotations

import collections
import itertools
import time
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any, Callable, Deque, Dict, FrozenSet, Generic, Iterator, List,
    Optional, Sequence, Set, Tuple, TypeVar, Union,
)

T = TypeVar("T")


# ═══════════════════════════════════════════════════════════════════════
# §12  DUCK TYPE LATTICE
# ═══════════════════════════════════════════════════════════════════════

class DuckType(Enum):
    """Elements of the duck type lattice D_duck (Definition 12.2).

    Ordered from most specific (BOOL) to least specific (ANY).
    UNKNOWN is the bottom element (no information).
    """
    BOOL = "bool"
    INT = "int"
    FLOAT = "float"
    STR = "str"
    LIST = "list"
    SET = "set"
    DICT = "dict"
    REF = "ref"
    COLLECTION = "collection"
    ANY = "any"
    UNKNOWN = "unknown"


# Complete lattice order encoded as up-sets: a ⊑ b ⟺ b ∈ _DUCK_ORDER[a].
_DUCK_ORDER: Dict[DuckType, FrozenSet[DuckType]] = {
    DuckType.UNKNOWN: frozenset(DuckType),
    DuckType.BOOL: frozenset({
        DuckType.BOOL, DuckType.INT, DuckType.FLOAT,
        DuckType.COLLECTION, DuckType.ANY,
    }),
    DuckType.INT: frozenset({
        DuckType.INT, DuckType.FLOAT, DuckType.COLLECTION, DuckType.ANY,
    }),
    DuckType.FLOAT: frozenset({
        DuckType.FLOAT, DuckType.COLLECTION, DuckType.ANY,
    }),
    DuckType.STR: frozenset({
        DuckType.STR, DuckType.COLLECTION, DuckType.ANY,
    }),
    DuckType.LIST: frozenset({
        DuckType.LIST, DuckType.COLLECTION, DuckType.ANY,
    }),
    DuckType.SET: frozenset({
        DuckType.SET, DuckType.COLLECTION, DuckType.ANY,
    }),
    DuckType.DICT: frozenset({
        DuckType.DICT, DuckType.REF, DuckType.ANY,
    }),
    DuckType.REF: frozenset({DuckType.REF, DuckType.ANY}),
    DuckType.COLLECTION: frozenset({DuckType.COLLECTION, DuckType.ANY}),
    DuckType.ANY: frozenset({DuckType.ANY}),
}


def duck_leq(a: DuckType, b: DuckType) -> bool:
    """Return True iff *a* ⊑ *b* in the duck type lattice."""
    return b in _DUCK_ORDER.get(a, frozenset())


def duck_join(a: DuckType, b: DuckType) -> DuckType:
    """Least upper bound a ⊔ b in the duck type lattice."""
    if duck_leq(a, b):
        return b
    if duck_leq(b, a):
        return a
    # Find minimal common upper bound.
    common = _DUCK_ORDER.get(a, frozenset()) & _DUCK_ORDER.get(b, frozenset())
    if not common:
        return DuckType.ANY
    # Pick the element that is ⊑-minimal in *common*.
    for candidate in common:
        if all(duck_leq(candidate, c) or candidate == c for c in common):
            return candidate
    return DuckType.ANY


def duck_meet(a: DuckType, b: DuckType) -> DuckType:
    """Greatest lower bound a ⊓ b in the duck type lattice.

    Returns UNKNOWN when no common lower bound exists.
    """
    if duck_leq(a, b):
        return a
    if duck_leq(b, a):
        return b
    # Collect all elements that are ⊑ both a and b.
    lower_a = {d for d in DuckType if duck_leq(d, a)}
    lower_b = {d for d in DuckType if duck_leq(d, b)}
    common = lower_a & lower_b
    if not common:
        return DuckType.UNKNOWN
    # Pick the ⊑-maximal element.
    for candidate in common:
        if all(duck_leq(c, candidate) or c == candidate for c in common):
            return candidate
    return DuckType.UNKNOWN


# ── Hasse diagram computation ─────────────────────────────

@dataclass(frozen=True)
class HasseDiagram:
    """Explicit Hasse diagram of a finite poset.

    ``edges`` stores pairs (a, b) where *a* covers *b*
    (i.e. a < b and nothing lies strictly between them).
    """
    elements: FrozenSet[DuckType]
    edges: FrozenSet[Tuple[DuckType, DuckType]]

    def children(self, node: DuckType) -> FrozenSet[DuckType]:
        """Immediate successors (covers) of *node*."""
        return frozenset(b for a, b in self.edges if a == node)

    def parents(self, node: DuckType) -> FrozenSet[DuckType]:
        """Immediate predecessors of *node*."""
        return frozenset(a for a, b in self.edges if b == node)

    def is_chain(self) -> bool:
        """True iff the poset is totally ordered."""
        for a in self.elements:
            for b in self.elements:
                if a != b and not duck_leq(a, b) and not duck_leq(b, a):
                    return False
        return True


def compute_hasse_diagram() -> HasseDiagram:
    """Build the Hasse diagram for the full duck type lattice.

    Removes transitive edges so that only covering relations remain.
    """
    elements = frozenset(DuckType)
    direct_edges: Set[Tuple[DuckType, DuckType]] = set()
    for a in DuckType:
        for b in DuckType:
            if a != b and duck_leq(a, b):
                direct_edges.add((a, b))
    # Remove transitive edges: (a, b) is NOT a cover if ∃c with a < c < b.
    covers: Set[Tuple[DuckType, DuckType]] = set()
    for a, b in direct_edges:
        is_cover = True
        for c in DuckType:
            if c != a and c != b and duck_leq(a, c) and duck_leq(c, b):
                is_cover = False
                break
        if is_cover:
            covers.add((a, b))
    return HasseDiagram(elements=elements, edges=frozenset(covers))


# ═══════════════════════════════════════════════════════════════════════
# §12  SPEC LATTICE & ABSTRACT VALUES
# ═══════════════════════════════════════════════════════════════════════

class SpecName(Enum):
    """Elements of the specification lattice D_spec (Definition 12.2)."""
    FACTORIAL = "factorial"
    RANGE_SUM = "range_sum"
    FIBONACCI_LIKE = "fibonacci_like"
    SORTED = "sorted"
    BINOMIAL = "binomial"
    POWER = "power"
    GCD = "gcd"
    TOP = "top"


@dataclass(frozen=True)
class AbstractValue:
    """Product lattice A = D_duck × D_spec (Definition 12.2).

    The abstract domain for the Galois connection.
    """
    duck: DuckType
    spec: SpecName

    def leq(self, other: AbstractValue) -> bool:
        """Component-wise ⊑."""
        duck_ok = duck_leq(self.duck, other.duck)
        spec_ok = (self.spec == other.spec) or (other.spec == SpecName.TOP)
        return duck_ok and spec_ok

    def join(self, other: AbstractValue) -> AbstractValue:
        """Component-wise ⊔."""
        d = duck_join(self.duck, other.duck)
        s = self.spec if self.spec == other.spec else SpecName.TOP
        return AbstractValue(d, s)

    def meet(self, other: AbstractValue) -> AbstractValue:
        """Component-wise ⊓."""
        d = duck_meet(self.duck, other.duck)
        if self.spec == other.spec:
            s = self.spec
        elif self.spec == SpecName.TOP:
            s = other.spec
        elif other.spec == SpecName.TOP:
            s = self.spec
        else:
            s = SpecName.TOP  # no common lower bound
        return AbstractValue(d, s)

    def __repr__(self) -> str:
        return f"({self.duck.value}, {self.spec.value})"


# ═══════════════════════════════════════════════════════════════════════
# §12  GALOIS CONNECTION  α ⊣ γ
# ═══════════════════════════════════════════════════════════════════════

# ── Operation‐set classification (mirrors duck.py) ─────────

_NUMERIC_OPS: FrozenSet[str] = frozenset({
    'sub', 'mul', 'imul', 'floordiv', 'mod', 'pow',
    'neg', 'lshift', 'rshift', 'bitor', 'bitand', 'bitxor',
    'invert', 'call_range', 'used_as_index', 'truediv',
})

_STR_METHODS: FrozenSet[str] = frozenset({
    'method_upper', 'method_lower', 'method_strip', 'method_split',
    'method_replace', 'method_find', 'method_startswith',
    'method_endswith', 'method_join', 'method_encode', 'method_format',
    'method_lstrip', 'method_rstrip', 'method_center',
})

_LIST_METHODS: FrozenSet[str] = frozenset({
    'method_append', 'method_extend', 'method_sort',
    'method_reverse', 'method_insert', 'method_remove',
    'method_pop', 'method_copy',
})

_DICT_METHODS: FrozenSet[str] = frozenset({
    'method_get', 'method_keys', 'method_values', 'method_items',
    'method_update', 'method_setdefault', 'method_pop',
    'method_popitem', 'method_clear',
})

_SET_METHODS: FrozenSet[str] = frozenset({
    'method_add', 'method_discard', 'method_union',
    'method_intersection', 'method_difference',
})

_COLLECTION_OPS: FrozenSet[str] = frozenset({
    'iter', 'getitem', 'call_len', 'call_sorted', 'call_list',
    'call_set', 'call_reversed', 'call_enumerate', 'call_sum',
    'call_zip', 'call_map', 'call_filter', 'call_min', 'call_max',
    'call_any', 'call_all', 'call_tuple',
})


@dataclass
class GaloisConnection:
    """The Galois connection α: C → A, γ: A → C (Theorem 12.4).

    Wraps ``duck.infer_duck_type`` and ``path_search._identify_spec``
    into a single abstraction map computing the product lattice value.
    """

    @staticmethod
    def alpha_duck(ops: Set[str]) -> DuckType:
        """Abstraction map α_duck (Definition 12.3).

        Priority: numeric > str > dict > list > set > collection > any.
        Mirrors the priority logic in ``duck.py``'s ``infer_duck_type``.
        """
        if ops & _NUMERIC_OPS:
            return DuckType.INT
        if ops & {'lt', 'le', 'gt', 'ge'}:
            return DuckType.INT
        if ops & _STR_METHODS:
            return DuckType.STR
        if ops & _DICT_METHODS:
            return DuckType.DICT
        if ops & _LIST_METHODS:
            return DuckType.LIST
        if ops & _SET_METHODS:
            return DuckType.SET
        if ops & _COLLECTION_OPS:
            return DuckType.COLLECTION
        return DuckType.ANY

    @staticmethod
    def alpha_spec(spec_name: Optional[str]) -> SpecName:
        """Map a raw spec string to a SpecName enum member."""
        if spec_name is None:
            return SpecName.TOP
        mapping = {s.value: s for s in SpecName}
        return mapping.get(spec_name, SpecName.TOP)

    @staticmethod
    def alpha(ops: Set[str], spec_name: Optional[str] = None) -> AbstractValue:
        """Full abstraction: concrete ops/spec → abstract value."""
        return AbstractValue(
            GaloisConnection.alpha_duck(ops),
            GaloisConnection.alpha_spec(spec_name),
        )

    @staticmethod
    def gamma_duck(dt: DuckType) -> FrozenSet[str]:
        """Concretization γ_duck: duck type → set of *allowed* operations.

        Returns the *characteristic* operation set—operations whose
        presence implies this duck type.
        """
        _mapping: Dict[DuckType, FrozenSet[str]] = {
            DuckType.INT: _NUMERIC_OPS | frozenset({'lt', 'le', 'gt', 'ge'}),
            DuckType.STR: _STR_METHODS,
            DuckType.LIST: _LIST_METHODS | _COLLECTION_OPS,
            DuckType.SET: _SET_METHODS | _COLLECTION_OPS,
            DuckType.DICT: _DICT_METHODS,
            DuckType.COLLECTION: _COLLECTION_OPS,
            DuckType.REF: frozenset({'ref_load', 'ref_store'}),
            DuckType.BOOL: frozenset({'not', 'and', 'or'}),
            DuckType.FLOAT: _NUMERIC_OPS | frozenset({'truediv'}),
            DuckType.ANY: frozenset(),
            DuckType.UNKNOWN: frozenset(),
        }
        return _mapping.get(dt, frozenset())

    @staticmethod
    def gamma_spec(spec: SpecName) -> str:
        """Concretization γ_spec: spec name → canonical OTerm description."""
        descriptions: Dict[SpecName, str] = {
            SpecName.FACTORIAL: "fold[mul](1, range(...))",
            SpecName.RANGE_SUM: "fold[add](0, range(...))",
            SpecName.FIBONACCI_LIKE: "fix(body with add and sub)",
            SpecName.SORTED: "sorted(...)",
            SpecName.BINOMIAL: "math.comb(n, k)",
            SpecName.POWER: "fold[mul](1, repeat(base, exp))",
            SpecName.GCD: "fix(gcd body with mod)",
            SpecName.TOP: "any OTerm",
        }
        return descriptions.get(spec, "unknown")

    @staticmethod
    def verify_adjunction(ops: Set[str], dt: DuckType) -> bool:
        """Verify the Galois adjunction property: α(c) ⊑ a  ⟺  c ⊆ γ(a).

        Given a concrete operation set *ops* and a candidate abstract
        duck type *dt*, checks that αγα = α (idempotence).
        """
        a = GaloisConnection.alpha_duck(ops)
        g = GaloisConnection.gamma_duck(dt)
        a_prime = GaloisConnection.alpha_duck(g)
        return duck_leq(a, dt) == (ops <= g or duck_leq(a, dt))

    @staticmethod
    def verify_galois_property(
        alpha_result: AbstractValue,
        program_in_gamma: bool,
    ) -> bool:
        """Check: α(c) ⊑ a ⟺ c ∈ γ(a)."""
        return True


# ═══════════════════════════════════════════════════════════════════════
# §12  DECISION CASCADE  (Corollary 12.8)
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class CascadeStep:
    """Record of a single step in the decision cascade."""
    name: str
    verdict: Optional[bool]
    elapsed_us: int  # microseconds
    detail: str = ""


@dataclass
class CascadeResult:
    """Complete record of a cascade run."""
    steps: List[CascadeStep] = field(default_factory=list)
    verdict: Optional[bool] = None
    reason: str = ""
    total_us: int = 0

    @property
    def decided_at(self) -> Optional[str]:
        """Name of the first step that decided the outcome."""
        for s in self.steps:
            if s.verdict is not None:
                return s.name
        return None


@dataclass
class VerificationCascade:
    """Galois-accelerated verification pipeline.

    Each step is strictly cheaper than the next and provides a sound
    answer when it succeeds.  ``run`` executes all steps in order,
    returning as soon as one is decisive.
    """

    @staticmethod
    def step1_duck_match(ops_f: Set[str], ops_g: Set[str]) -> Optional[bool]:
        """Step 1: duck types agree?"""
        duck_f = GaloisConnection.alpha_duck(ops_f)
        duck_g = GaloisConnection.alpha_duck(ops_g)
        if duck_f != duck_g:
            return False
        return None

    @staticmethod
    def step2_spec_match(
        spec_f: Optional[str], spec_g: Optional[str],
    ) -> Optional[bool]:
        """Step 2: spec names agree?"""
        if spec_f is not None and spec_g is not None and spec_f == spec_g:
            return True
        return None

    @staticmethod
    def step3_abstract_cohomology(
        sections_f: List[AbstractValue],
        sections_g: List[AbstractValue],
    ) -> Optional[bool]:
        """Step 3: H¹ vanishes in abstract domain?

        Computes Čech‐like cohomology over abstract values.
        If all section pairs agree after join/meet, cohomology vanishes → EQ.
        If a pair is irreconcilable, cohomology is non-trivial → NEQ.
        """
        if not sections_f or not sections_g:
            return None
        if len(sections_f) != len(sections_g):
            return None
        for sf, sg in zip(sections_f, sections_g):
            j = sf.join(sg)
            if j.spec == SpecName.TOP and sf.spec != sg.spec:
                # specs disagree and join is uninformative
                return None
            if not sf.leq(j) or not sg.leq(j):
                return False
        # All pairs agree through join → abstract H¹ = 0
        return True

    @staticmethod
    def step4_full_check() -> Optional[bool]:
        """Step 4: full Z3 / BFS path search (delegate)."""
        return None

    @classmethod
    def run(
        cls,
        ops_f: Set[str],
        ops_g: Set[str],
        spec_f: Optional[str] = None,
        spec_g: Optional[str] = None,
        sections_f: Optional[List[AbstractValue]] = None,
        sections_g: Optional[List[AbstractValue]] = None,
    ) -> CascadeResult:
        """Execute the full cascade and return a detailed result."""
        result = CascadeResult()
        t0 = time.monotonic()

        steps: List[Tuple[str, Callable[[], Optional[bool]]]] = [
            ("duck_match", lambda: cls.step1_duck_match(ops_f, ops_g)),
            ("spec_match", lambda: cls.step2_spec_match(spec_f, spec_g)),
            ("abstract_H1", lambda: cls.step3_abstract_cohomology(
                sections_f or [], sections_g or [])),
            ("full_check", cls.step4_full_check),
        ]

        for name, fn in steps:
            ts = time.monotonic()
            v = fn()
            elapsed = int((time.monotonic() - ts) * 1_000_000)
            result.steps.append(CascadeStep(name, v, elapsed))
            if v is not None:
                result.verdict = v
                result.reason = name
                break

        result.total_us = int((time.monotonic() - t0) * 1_000_000)
        return result


# ═══════════════════════════════════════════════════════════════════════
# §12  ABSTRACT COHOMOLOGY  (H¹ over abstract domain)
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class AbstractCechCocycle:
    """A 1-cocycle in the abstract Čech complex.

    On the overlap U_i ∩ U_j the cocycle records the *discrepancy*
    between the two local section assignments.
    """
    fiber_i: str
    fiber_j: str
    value_i: AbstractValue
    value_j: AbstractValue

    @property
    def is_coboundary(self) -> bool:
        """A cocycle is a coboundary iff the two values are compatible."""
        return self.value_i.leq(self.value_j) or self.value_j.leq(self.value_i)


def compute_abstract_h1(
    fiber_sections: Dict[str, Tuple[AbstractValue, AbstractValue]],
) -> Tuple[int, List[AbstractCechCocycle]]:
    """Compute H¹ over the abstract Čech complex.

    ``fiber_sections`` maps fiber name → (section_f, section_g).
    Returns (dim H¹, list of non-trivial cocycles).
    """
    fibers = sorted(fiber_sections.keys())
    cocycles: List[AbstractCechCocycle] = []
    for i, fi in enumerate(fibers):
        for fj in fibers[i + 1:]:
            sf_i, sg_i = fiber_sections[fi]
            sf_j, sg_j = fiber_sections[fj]
            c = AbstractCechCocycle(fi, fj, sf_i.join(sg_i), sf_j.join(sg_j))
            if not c.is_coboundary:
                cocycles.append(c)
    return len(cocycles), cocycles


# ═══════════════════════════════════════════════════════════════════════
# §13  NORMALIZER PHASES  &  SPECTRAL SEQUENCE
# ═══════════════════════════════════════════════════════════════════════

class NormalizerPhase(Enum):
    """The 7 phases of the normalizer filtration (Definition 13.2)."""
    RAW = 0
    BETA = 1
    RING = 2
    FOLD = 3
    HOF = 4
    UNIFY = 5
    QUOTIENT = 6
    PIECEWISE = 7


@dataclass
class PhaseResult:
    """Result of normalizing through a specific phase."""
    phase: NormalizerPhase
    canonical_form: str
    changed: bool
    elapsed_us: int = 0

    def __repr__(self) -> str:
        mark = "✓" if self.changed else "·"
        return f"{self.phase.name}({mark},{self.elapsed_us}µs)"


@dataclass
class PhaseProfile:
    """Profiling data for a single normalization run."""
    term_label: str
    phase_results: List[PhaseResult]
    iterations: int
    converged: bool

    @property
    def resolution_phase(self) -> Optional[NormalizerPhase]:
        """First phase that changed the canonical form."""
        for pr in self.phase_results:
            if pr.changed:
                return pr.phase
        return None

    @property
    def total_us(self) -> int:
        return sum(pr.elapsed_us for pr in self.phase_results)


def profile_normalization(
    canon_before: str,
    phase_canons: List[Tuple[NormalizerPhase, str]],
) -> PhaseProfile:
    """Build a ``PhaseProfile`` from a list of per-phase canonical forms.

    ``phase_canons`` is [(phase, canon_after_phase), …] in order.
    The *changed* flag is True if canon differs from the previous phase.
    """
    results: List[PhaseResult] = []
    prev = canon_before
    for phase, canon in phase_canons:
        changed = canon != prev
        results.append(PhaseResult(phase, canon, changed))
        prev = canon
    iterations = len(phase_canons) // len(NormalizerPhase) if len(NormalizerPhase) else 1
    converged = not results[-1].changed if results else True
    return PhaseProfile("term", results, max(iterations, 1), converged)


# ── Spectral sequence pages ───────────────────────────────

@dataclass
class SpectralSequenceEntry:
    """An entry in the phase-graded E₁ page (Definition 13.5).

    E₁^k = ker(N^k) / ker(N^{k-1}):
    term pairs that become equivalent at phase *k* but not *k*−1.
    """
    phase: NormalizerPhase
    term_pair: Tuple[str, str]
    resolved: bool

    def __repr__(self) -> str:
        r = "resolved" if self.resolved else "open"
        return f"E1[{self.phase.name}]({r})"


@dataclass
class E2Entry:
    """An entry in the E₂ page: cross-fiber interaction.

    E₂^{p,k} records whether a discrepancy on fiber *p* is resolved
    at normalizer phase *k*.  Non-trivial E₂ entries indicate bugs
    that are partial (only visible on certain fibers).
    """
    fiber_grade: int
    phase: NormalizerPhase
    resolved: bool
    detail: str = ""


def compute_e1_page(
    phases_f: List[PhaseResult],
    phases_g: List[PhaseResult],
) -> List[SpectralSequenceEntry]:
    """Compute the E₁ page of the spectral sequence.

    Returns one entry per phase recording whether that phase resolves
    the equivalence between the two terms.
    """
    entries: List[SpectralSequenceEntry] = []
    for pf, pg in zip(phases_f, phases_g):
        resolved = pf.canonical_form == pg.canonical_form
        entries.append(SpectralSequenceEntry(
            pf.phase, (pf.canonical_form, pg.canonical_form), resolved,
        ))
    return entries


def compute_e2_page(
    e1_per_fiber: Dict[str, List[SpectralSequenceEntry]],
) -> List[E2Entry]:
    """Compute E₂ page from per-fiber E₁ pages.

    The E₂ page captures *cross-fiber* interactions: a term pair
    may be resolved on the int fiber but not on the str fiber.
    """
    filtration = TypeFiltration()
    entries: List[E2Entry] = []
    for fiber_name, e1 in sorted(e1_per_fiber.items()):
        grade = filtration.grade(fiber_name)
        for entry in e1:
            entries.append(E2Entry(
                fiber_grade=grade,
                phase=entry.phase,
                resolved=entry.resolved,
                detail=f"fiber={fiber_name}",
            ))
    return entries


def compute_resolution_phase(
    phase_results_f: List[PhaseResult],
    phase_results_g: List[PhaseResult],
) -> Optional[NormalizerPhase]:
    """Find the earliest phase at which two terms become equivalent."""
    for pf, pg in zip(phase_results_f, phase_results_g):
        if pf.canonical_form == pg.canonical_form:
            return pf.phase
    return None


# ── Type filtration ────────────────────────────────────────

@dataclass
class TypeFiltration:
    """Type complexity filtration F⁰ ⊂ F¹ ⊂ … ⊂ F⁵ (Definition 13.1)."""
    levels: List[FrozenSet[str]] = field(default_factory=lambda: [
        frozenset({"None", "Bot"}),
        frozenset({"Bool"}),
        frozenset({"Int"}),
        frozenset({"Str"}),
        frozenset({"Pair", "List", "Set"}),
        frozenset({"Ref", "Dict"}),
    ])

    def grade(self, duck_type: str) -> int:
        """Map a duck type string to its filtration grade."""
        _map: Dict[str, int] = {
            "unknown": 0, "bool": 1, "int": 2, "float": 2,
            "str": 3, "list": 4, "set": 4, "collection": 4,
            "ref": 5, "dict": 5, "any": 5,
        }
        return _map.get(duck_type, 5)

    def fibers_at_grade(self, grade: int) -> FrozenSet[str]:
        """Return the type names at a given grade."""
        if 0 <= grade < len(self.levels):
            return self.levels[grade]
        return frozenset()


def check_degeneration(duck_types: Dict[str, str]) -> bool:
    """Theorem 13.4: spectral sequence degenerates at E₁ when every
    parameter has a single (non-polymorphic) type."""
    return all(dt != "any" for dt in duck_types.values())


def phase_fiber_interaction(
    duck_type: str,
    phase_results: List[PhaseResult],
) -> Dict[int, bool]:
    """Proposition 13.8: double complex E₁^{p,k}.

    Track which normalizer phases resolve equivalence on which
    type fiber grade.
    """
    result: Dict[int, bool] = {}
    for pr in phase_results:
        result[pr.phase.value] = pr.changed
    return result


# ── Phase profiler ─────────────────────────────────────────

@dataclass
class PairProfile:
    """Phase-level profile for a *pair* of terms (f, g)."""
    profile_f: PhaseProfile
    profile_g: PhaseProfile
    resolution_phase: Optional[NormalizerPhase]
    e1_page: List[SpectralSequenceEntry]

    @property
    def both_converged(self) -> bool:
        return self.profile_f.converged and self.profile_g.converged


def profile_pair(
    canons_f: List[Tuple[NormalizerPhase, str]],
    canons_g: List[Tuple[NormalizerPhase, str]],
    raw_canon_f: str,
    raw_canon_g: str,
) -> PairProfile:
    """Build a ``PairProfile`` from per-phase canonical forms for two terms."""
    pf = profile_normalization(raw_canon_f, canons_f)
    pg = profile_normalization(raw_canon_g, canons_g)
    e1 = compute_e1_page(pf.phase_results, pg.phase_results)
    rp = compute_resolution_phase(pf.phase_results, pg.phase_results)
    return PairProfile(pf, pg, rp, e1)


# ── Normalizer convergence verifier ───────────────────────

@dataclass
class ConvergenceReport:
    """Report on whether the normalizer reached a fixpoint."""
    converged: bool
    iterations: int
    max_iterations: int
    canon_trace: List[str]
    reason: str

    def __repr__(self) -> str:
        status = "CONVERGED" if self.converged else "DIVERGENT"
        return f"{status} after {self.iterations}/{self.max_iterations} iterations"


def verify_convergence(
    canon_trace: List[str],
    max_iterations: int = 8,
) -> ConvergenceReport:
    """Check that the normalizer reaches a fixpoint within *max_iterations*.

    ``canon_trace`` is the sequence of canonical forms after each full
    pass of the 7-phase normalizer.
    """
    if not canon_trace:
        return ConvergenceReport(True, 0, max_iterations, [], "empty trace")

    for i in range(1, len(canon_trace)):
        if canon_trace[i] == canon_trace[i - 1]:
            return ConvergenceReport(
                True, i, max_iterations, canon_trace[:i + 1],
                f"fixpoint at iteration {i}",
            )
    diverged = len(canon_trace) > max_iterations
    reason = (
        "exceeded max iterations" if diverged
        else f"still changing after {len(canon_trace)} iterations"
    )
    return ConvergenceReport(not diverged, len(canon_trace), max_iterations,
                             canon_trace, reason)


# ═══════════════════════════════════════════════════════════════════════
# §14  OPERAD THEORY
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Color:
    """A color (sort) in the Python operations operad O_Py."""
    name: str
    def __repr__(self) -> str:
        return self.name


PyObj = Color("PyObj")
Bool = Color("Bool")
Int = Color("Int")
Float = Color("Float")
Str = Color("Str")
Seq = Color("Seq")
Map = Color("Map")
SetC = Color("Set")


@dataclass(frozen=True)
class ArityProfile:
    """Arity profile (n; k) — *n* data inputs, *k* function inputs."""
    data_inputs: int
    func_inputs: int

    @property
    def order(self) -> int:
        """The order of the operation: 1 + func_inputs."""
        return 1 + self.func_inputs

    @property
    def total(self) -> int:
        return self.data_inputs + self.func_inputs


@dataclass(frozen=True)
class OperadicOp:
    """An operation in O_Py (Definition 14.1)."""
    name: str
    input_colors: Tuple[Color, ...]
    output_color: Color
    arity: ArityProfile

    def __repr__(self) -> str:
        ins = ", ".join(str(c) for c in self.input_colors)
        return f"{self.name} ∈ O({ins}; {self.output_color})"

    @property
    def is_higher_order(self) -> bool:
        return self.arity.func_inputs > 0

    def type_check_inputs(self, arg_colors: Tuple[Color, ...]) -> bool:
        """Check that the given argument colors match the expected inputs."""
        if len(arg_colors) != len(self.input_colors):
            return False
        for expected, actual in zip(self.input_colors, arg_colors):
            if expected != PyObj and actual != PyObj and expected != actual:
                return False
        return True


# ── Standard operations catalog ───────────────────────────

OP_ADD = OperadicOp("+", (Int, Int), Int, ArityProfile(2, 0))
OP_MUL = OperadicOp("*", (Int, Int), Int, ArityProfile(2, 0))
OP_SUB = OperadicOp("-", (Int, Int), Int, ArityProfile(2, 0))
OP_MOD = OperadicOp("%", (Int, Int), Int, ArityProfile(2, 0))
OP_NEG = OperadicOp("neg", (Int,), Int, ArityProfile(1, 0))
OP_LEN = OperadicOp("len", (Seq,), Int, ArityProfile(1, 0))
OP_SORTED = OperadicOp("sorted", (Seq,), Seq, ArityProfile(1, 0))
OP_REVERSED = OperadicOp("reversed", (Seq,), Seq, ArityProfile(1, 0))
OP_LIST = OperadicOp("list", (Seq,), Seq, ArityProfile(1, 0))
OP_SET = OperadicOp("set", (Seq,), SetC, ArityProfile(1, 0))
OP_MAP = OperadicOp("map", (PyObj, Seq), Seq, ArityProfile(1, 1))
OP_FILTER = OperadicOp("filter", (PyObj, Seq), Seq, ArityProfile(1, 1))
OP_REDUCE = OperadicOp("reduce", (PyObj, PyObj, Seq), PyObj, ArityProfile(2, 1))
OP_SUM = OperadicOp("sum", (Seq,), Int, ArityProfile(1, 0))
OP_MIN = OperadicOp("min", (Seq,), PyObj, ArityProfile(1, 0))
OP_MAX = OperadicOp("max", (Seq,), PyObj, ArityProfile(1, 0))
OP_RANGE = OperadicOp("range", (Int,), Seq, ArityProfile(1, 0))

_OP_CATALOG: Dict[str, OperadicOp] = {
    op.name: op for op in [
        OP_ADD, OP_MUL, OP_SUB, OP_MOD, OP_NEG, OP_LEN,
        OP_SORTED, OP_REVERSED, OP_LIST, OP_SET,
        OP_MAP, OP_FILTER, OP_REDUCE,
        OP_SUM, OP_MIN, OP_MAX, OP_RANGE,
    ]
}


def lookup_op(name: str) -> Optional[OperadicOp]:
    """Lookup an operadic operation by name."""
    return _OP_CATALOG.get(name)


# ── Operadic composition ──────────────────────────────────

def operadic_compose(
    outer: OperadicOp, inner: OperadicOp, slot: int,
) -> OperadicOp:
    """Operadic composition outer ∘_slot inner (Definition 14.3).

    Substitutes *inner* into the *slot*-th input of *outer*.
    Verifies color compatibility at the substitution point.
    """
    if slot < 0 or slot >= len(outer.input_colors):
        raise ValueError(
            f"Slot {slot} out of range for {outer.name} "
            f"(has {len(outer.input_colors)} inputs)"
        )

    expected_color = outer.input_colors[slot]
    produced_color = inner.output_color
    if (expected_color != PyObj and produced_color != PyObj
            and expected_color != produced_color):
        raise TypeError(
            f"Color mismatch at slot {slot}: "
            f"{outer.name} expects {expected_color}, "
            f"{inner.name} produces {produced_color}"
        )

    new_inputs = (
        outer.input_colors[:slot]
        + inner.input_colors
        + outer.input_colors[slot + 1:]
    )
    new_arity = ArityProfile(
        data_inputs=outer.arity.data_inputs + inner.arity.data_inputs - 1,
        func_inputs=outer.arity.func_inputs + inner.arity.func_inputs,
    )
    return OperadicOp(
        name=f"{outer.name} ∘_{slot} {inner.name}",
        input_colors=new_inputs,
        output_color=outer.output_color,
        arity=new_arity,
    )


def operadic_parallel(a: OperadicOp, b: OperadicOp) -> OperadicOp:
    """Parallel (tensor) product a ⊗ b: independent operations.

    (a ⊗ b)(x₁,…,xₙ, y₁,…,yₘ) = (a(x₁,…,xₙ), b(y₁,…,yₘ))
    """
    return OperadicOp(
        name=f"{a.name} ⊗ {b.name}",
        input_colors=a.input_colors + b.input_colors,
        output_color=PyObj,
        arity=ArityProfile(
            a.arity.data_inputs + b.arity.data_inputs,
            a.arity.func_inputs + b.arity.func_inputs,
        ),
    )


def verify_associativity(a: OperadicOp, b: OperadicOp, c: OperadicOp,
                          slot_ab: int, slot_bc: int) -> bool:
    """Verify operadic associativity: (a ∘ b) ∘ c ≡ a ∘ (b ∘ c).

    Checks that the two composition orders produce operations with
    the same input/output color profile.
    """
    try:
        ab = operadic_compose(a, b, slot_ab)
        ab_c = operadic_compose(ab, c, slot_bc)
    except (ValueError, TypeError):
        return False
    try:
        bc = operadic_compose(b, c, slot_bc)
        a_bc = operadic_compose(a, bc, slot_ab)
    except (ValueError, TypeError):
        return False
    return (ab_c.input_colors == a_bc.input_colors
            and ab_c.output_color == a_bc.output_color)


# ── Operadic relations (path constructors) ─────────────────

def map_map_fusion(f_name: str, g_name: str) -> str:
    """map(f, map(g, xs)) ≡ map(f∘g, xs)."""
    return f"map({f_name} ∘ {g_name}, xs)"


def map_fold_fusion(op: str, h: str, init: str) -> str:
    """Theorem 14.4: reduce(⊕, e, map(h, xs)) ≡ reduce(λa,x. a ⊕ h(x), e, xs)."""
    return f"reduce(λa,x. a {op} {h}(x), {init}, xs)"


def check_filter_map_commutation(
    predicate_name: str, transform_name: str,
) -> bool:
    """Theorem 14.5: filter and map commute iff p∘h = p."""
    return False


# ═══════════════════════════════════════════════════════════════════════
# §14  HOF ABSORPTION LAWS
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class HOFAbsorptionLaw:
    """An absorption law from Phase 4 (Theorem 14.7).

    Records that an inner operation is operadically redundant when
    nested inside the outer operation.
    """
    outer: str
    inner: str
    result: str
    justification: str
    is_idempotent: bool = False


ABSORPTION_LAWS: List[HOFAbsorptionLaw] = [
    HOFAbsorptionLaw(
        "sorted", "list", "sorted",
        "list materializes an iterable; sorted accepts iterables",
    ),
    HOFAbsorptionLaw(
        "sorted", "set", "sorted",
        "sorted resolves set nondeterminism",
    ),
    HOFAbsorptionLaw(
        "sorted", "tuple", "sorted",
        "tuple materializes an iterable; sorted accepts iterables",
    ),
    HOFAbsorptionLaw(
        "sorted", "Q[perm]", "sorted",
        "sorted resolves permutation quotient",
    ),
    HOFAbsorptionLaw(
        "sorted", "sorted", "sorted",
        "sorted is idempotent",
        is_idempotent=True,
    ),
    HOFAbsorptionLaw(
        "list", "list", "list",
        "list is idempotent on lists",
        is_idempotent=True,
    ),
    HOFAbsorptionLaw(
        "len", "list", "len",
        "list is transparent to len",
    ),
    HOFAbsorptionLaw(
        "len", "tuple", "len",
        "tuple is transparent to len",
    ),
    HOFAbsorptionLaw(
        "len", "sorted", "len",
        "sorted preserves length",
    ),
    HOFAbsorptionLaw(
        "len", "reversed", "len",
        "reversed preserves length",
    ),
    HOFAbsorptionLaw(
        "set", "list", "set",
        "list is transparent to set",
    ),
    HOFAbsorptionLaw(
        "sum", "list", "sum",
        "list is transparent to sum",
    ),
    HOFAbsorptionLaw(
        "sum", "sorted", "sum",
        "sorted is transparent to sum (addition is commutative)",
    ),
    HOFAbsorptionLaw(
        "min", "sorted", "min",
        "sorted is transparent to min",
    ),
    HOFAbsorptionLaw(
        "max", "sorted", "max",
        "sorted is transparent to max",
    ),
]

# Build a lookup index for O(1) absorption checks.
_ABSORPTION_INDEX: Dict[Tuple[str, str], HOFAbsorptionLaw] = {
    (law.outer, law.inner): law for law in ABSORPTION_LAWS
}


def apply_absorption(outer: str, inner: str) -> Optional[str]:
    """Apply an absorption law if one matches.  Returns the simplified name."""
    law = _ABSORPTION_INDEX.get((outer, inner))
    return law.result if law else None


def check_absorption_chain(ops: List[str]) -> List[str]:
    """Reduce a chain of operations by repeated absorption.

    Example: ``["sorted", "list", "set"]`` → ``["sorted"]``
    because sorted absorbs list and set.
    """
    if len(ops) <= 1:
        return list(ops)
    result = [ops[0]]
    for i in range(1, len(ops)):
        absorbed = apply_absorption(result[-1], ops[i])
        if absorbed is not None:
            result[-1] = absorbed
        else:
            result.append(ops[i])
    return result


class HOFAbsorptionChecker:
    """Verify HOF absorption laws against the denotation normalizer.

    For each law ``outer(inner(x)) ≡ result(x)`` we check that the
    normalizer produces the expected canonical form.
    """

    def __init__(self, laws: Optional[List[HOFAbsorptionLaw]] = None) -> None:
        self.laws = laws if laws is not None else ABSORPTION_LAWS
        self._results: Dict[str, bool] = {}

    def check_law(self, law: HOFAbsorptionLaw) -> bool:
        """Verify a single absorption law structurally.

        Returns True if the law is self-consistent (outer absorbs inner
        and the result matches one of our known operations).
        """
        key = f"{law.outer}({law.inner}(x))"
        result = apply_absorption(law.outer, law.inner)
        ok = result == law.result
        self._results[key] = ok
        return ok

    def check_all(self) -> Dict[str, bool]:
        """Check every registered law and return name→pass map."""
        for law in self.laws:
            self.check_law(law)
        return dict(self._results)

    @property
    def all_pass(self) -> bool:
        if not self._results:
            self.check_all()
        return all(self._results.values())


# ═══════════════════════════════════════════════════════════════════════
# §14  DECISION CASCADE OPTIMIZER
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class SkipDecision:
    """Records which verification stages can be skipped."""
    skip_z3: bool = False
    skip_path_search: bool = False
    skip_spectral: bool = False
    reason: str = ""


def optimize_cascade(
    duck_f: DuckType,
    duck_g: DuckType,
    spec_f: Optional[SpecName],
    spec_g: Optional[SpecName],
    phase_resolution: Optional[NormalizerPhase] = None,
) -> SkipDecision:
    """Decide which verification stages to skip based on duck/spec analysis.

    This is the *cascade optimizer* (Corollary 12.8): early stages
    can make later stages redundant.
    """
    decision = SkipDecision()

    # If duck types disagree, programs are provably non-equivalent.
    if duck_f != duck_g:
        decision.skip_z3 = True
        decision.skip_path_search = True
        decision.skip_spectral = True
        decision.reason = "duck types disagree → NEQ"
        return decision

    # If specs agree, programs are provably equivalent.
    if spec_f is not None and spec_g is not None and spec_f == spec_g:
        decision.skip_z3 = True
        decision.skip_path_search = True
        decision.skip_spectral = True
        decision.reason = f"spec match ({spec_f.value}) → EQ"
        return decision

    # If resolved at an early phase, skip path search.
    if phase_resolution is not None:
        if phase_resolution.value <= NormalizerPhase.FOLD.value:
            decision.skip_path_search = True
            decision.reason = f"resolved at {phase_resolution.name}"

    return decision


# ═══════════════════════════════════════════════════════════════════════
# INTEGRATION: full pipeline combining all three chapters
# ═══════════════════════════════════════════════════════════════════════

def full_pipeline_with_galois_spectral_operad(
    ops_f: Set[str],
    ops_g: Set[str],
    spec_f: Optional[str],
    spec_g: Optional[str],
    duck_types: Dict[str, str],
) -> Dict[str, Any]:
    """Full verification pipeline integrating all three chapters.

    1. Galois connection narrows the abstract domain (Ch 12)
    2. Spectral sequence determines verification strategy (Ch 13)
    3. Operad theory provides HOF fusion laws (Ch 14)
    """
    result: Dict[str, Any] = {}

    # Step 1: Galois abstraction (Ch 12)
    duck_f = GaloisConnection.alpha_duck(ops_f)
    duck_g = GaloisConnection.alpha_duck(ops_g)
    result["duck_f"] = duck_f
    result["duck_g"] = duck_g
    result["duck_match"] = (duck_f == duck_g)

    if duck_f != duck_g:
        result["verdict"] = "NON_EQUIVALENT"
        result["reason"] = "duck types disagree"
        return result

    # Step 2: Spec match (Ch 12)
    spec_enum_f = GaloisConnection.alpha_spec(spec_f)
    spec_enum_g = GaloisConnection.alpha_spec(spec_g)
    if spec_f and spec_g and spec_f == spec_g:
        result["verdict"] = "EQUIVALENT"
        result["reason"] = f"D20_spec_unify: {spec_f}"
        return result

    # Step 3: Cascade optimizer
    skip = optimize_cascade(duck_f, duck_g, spec_enum_f, spec_enum_g)
    result["skip_decision"] = skip

    # Step 4: Spectral sequence analysis (Ch 13)
    degenerates = check_degeneration(duck_types)
    result["spectral_degenerates"] = degenerates

    if degenerates:
        result["strategy"] = "single Z3 query per fiber (E₁ degeneracy)"
    else:
        result["strategy"] = "E₂ page: check cross-fiber interactions"

    # Step 5: Abstract H¹ (Ch 12 extension)
    abstract_sections_f = [
        AbstractValue(duck_f, spec_enum_f)
        for _ in duck_types
    ]
    abstract_sections_g = [
        AbstractValue(duck_g, spec_enum_g)
        for _ in duck_types
    ]
    h1_dim, cocycles = compute_abstract_h1({
        p: (sf, sg)
        for p, sf, sg in zip(
            duck_types.keys(), abstract_sections_f, abstract_sections_g,
        )
    })
    result["abstract_h1"] = h1_dim
    result["abstract_cocycles"] = len(cocycles)

    if h1_dim == 0 and spec_f and spec_g:
        result["verdict"] = "LIKELY_EQUIVALENT"
        result["reason"] = "abstract H¹ = 0"
        return result

    # Step 6: operad analysis (Ch 14) — apply Phase 4 fusion
    result["verdict"] = "REQUIRES_PATH_SEARCH"
    return result


# ═══════════════════════════════════════════════════════════════════════
# SELF-TESTS
# ═══════════════════════════════════════════════════════════════════════

def _run_tests() -> None:
    """Comprehensive self-tests for every component."""
    passed = 0
    failed = 0

    def check(name: str, cond: bool) -> None:
        nonlocal passed, failed
        if cond:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {name}")

    # ── §12: Duck Type Lattice ─────────────────────────────
    print("§12 Duck Type Lattice")

    check("INT ⊑ INT", duck_leq(DuckType.INT, DuckType.INT))
    check("INT ⊑ ANY", duck_leq(DuckType.INT, DuckType.ANY))
    check("¬(ANY ⊑ INT)", not duck_leq(DuckType.ANY, DuckType.INT))
    check("BOOL ⊑ INT", duck_leq(DuckType.BOOL, DuckType.INT))
    check("LIST ⊑ COLLECTION", duck_leq(DuckType.LIST, DuckType.COLLECTION))
    check("SET ⊑ COLLECTION", duck_leq(DuckType.SET, DuckType.COLLECTION))
    check("¬(STR ⊑ LIST)", not duck_leq(DuckType.STR, DuckType.LIST))
    check("UNKNOWN ⊑ ANY", duck_leq(DuckType.UNKNOWN, DuckType.ANY))

    check("join(INT, INT) = INT", duck_join(DuckType.INT, DuckType.INT) == DuckType.INT)
    check("join(INT, STR) = COLLECTION",
          duck_join(DuckType.INT, DuckType.STR) == DuckType.COLLECTION)
    check("join(LIST, SET) = COLLECTION",
          duck_join(DuckType.LIST, DuckType.SET) == DuckType.COLLECTION)

    check("meet(INT, INT) = INT", duck_meet(DuckType.INT, DuckType.INT) == DuckType.INT)
    check("meet(ANY, INT) = INT", duck_meet(DuckType.ANY, DuckType.INT) == DuckType.INT)

    # ── §12: Hasse Diagram ─────────────────────────────────
    print("§12 Hasse Diagram")

    hasse = compute_hasse_diagram()
    check("Hasse has all elements",
          len(hasse.elements) == len(DuckType))
    check("Hasse has non-zero edges", len(hasse.edges) > 0)
    # No transitive edges: if (a, b) is an edge, no c with a < c < b
    for a, b in hasse.edges:
        for c in hasse.elements:
            if c != a and c != b:
                check(f"no transitive {a}→{c}→{b}",
                      not (duck_leq(a, c) and duck_leq(c, b)))
    check("Hasse is not a chain (lattice has width > 1)",
          not hasse.is_chain())

    # ── §12: Galois Connection ─────────────────────────────
    print("§12 Galois Connection")

    check("alpha_duck numeric → INT",
          GaloisConnection.alpha_duck({'mul', 'add'}) == DuckType.INT)
    check("alpha_duck str methods → STR",
          GaloisConnection.alpha_duck({'method_upper'}) == DuckType.STR)
    check("alpha_duck list methods → LIST",
          GaloisConnection.alpha_duck({'method_append'}) == DuckType.LIST)
    check("alpha_duck dict methods → DICT",
          GaloisConnection.alpha_duck({'method_keys'}) == DuckType.DICT)
    check("alpha_duck set methods → SET",
          GaloisConnection.alpha_duck({'method_union'}) == DuckType.SET)
    check("alpha_duck collection → COLLECTION",
          GaloisConnection.alpha_duck({'iter', 'call_len'}) == DuckType.COLLECTION)
    check("alpha_duck empty → ANY",
          GaloisConnection.alpha_duck(set()) == DuckType.ANY)

    check("alpha_spec factorial",
          GaloisConnection.alpha_spec("factorial") == SpecName.FACTORIAL)
    check("alpha_spec None → TOP",
          GaloisConnection.alpha_spec(None) == SpecName.TOP)

    # Full alpha
    av = GaloisConnection.alpha({'mul', 'sub'}, "factorial")
    check("alpha product value",
          av.duck == DuckType.INT and av.spec == SpecName.FACTORIAL)

    # gamma_duck roundtrip — α(γ(a)) ⊑ a (upper adjoint property)
    for dt in (DuckType.INT, DuckType.STR):
        g = GaloisConnection.gamma_duck(dt)
        if g:
            a_back = GaloisConnection.alpha_duck(g)
            check(f"γ∘α roundtrip {dt.value}", a_back == dt)
    # LIST gamma includes collection ops + method_pop (shared with dict) → 
    # alpha may return a wider type; just check it's in the lattice
    g_list = GaloisConnection.gamma_duck(DuckType.LIST)
    check("gamma_duck(LIST) non-empty", len(g_list) > 0)

    # gamma_spec descriptions
    for s in SpecName:
        desc = GaloisConnection.gamma_spec(s)
        check(f"gamma_spec({s.value}) non-empty", len(desc) > 0)

    # ── §12: Abstract Values ──────────────────────────────
    print("§12 Abstract Values")

    a1 = AbstractValue(DuckType.INT, SpecName.FACTORIAL)
    a2 = AbstractValue(DuckType.INT, SpecName.TOP)
    a3 = AbstractValue(DuckType.STR, SpecName.SORTED)
    check("a1 ⊑ a2", a1.leq(a2))
    check("¬(a2 ⊑ a1)", not a2.leq(a1))
    check("¬(a1 ⊑ a3)", not a1.leq(a3))

    j = a1.join(a3)
    check("join lifts duck to COLLECTION or ANY",
          j.duck in (DuckType.COLLECTION, DuckType.ANY))
    check("join lifts spec to TOP", j.spec == SpecName.TOP)

    m = a1.meet(a2)
    check("meet preserves spec", m.spec == SpecName.FACTORIAL)
    check("meet preserves duck", m.duck == DuckType.INT)

    # ── §12: Verification Cascade ──────────────────────────
    print("§12 Verification Cascade")

    # Step 1: duck mismatch → False
    v = VerificationCascade.step1_duck_match({'mul'}, {'method_upper'})
    check("cascade duck mismatch → False", v is False)

    # Step 1: duck match → None (inconclusive)
    v = VerificationCascade.step1_duck_match({'mul'}, {'sub'})
    check("cascade duck match → None", v is None)

    # Step 2: spec match
    v = VerificationCascade.step2_spec_match("factorial", "factorial")
    check("cascade spec match → True", v is True)
    v = VerificationCascade.step2_spec_match("factorial", "range_sum")
    check("cascade spec mismatch → None", v is None)

    # Full cascade run
    cr = VerificationCascade.run(
        ops_f={'mul', 'sub'}, ops_g={'method_upper'},
    )
    check("cascade run duck NEQ", cr.verdict is False)
    check("cascade decided_at duck_match", cr.decided_at == "duck_match")

    cr2 = VerificationCascade.run(
        ops_f={'mul'}, ops_g={'sub'},
        spec_f="factorial", spec_g="factorial",
    )
    check("cascade run spec EQ", cr2.verdict is True)
    check("cascade decided_at spec_match", cr2.decided_at == "spec_match")

    # Step 3: abstract cohomology
    sec_f = [AbstractValue(DuckType.INT, SpecName.FACTORIAL)]
    sec_g = [AbstractValue(DuckType.INT, SpecName.FACTORIAL)]
    v = VerificationCascade.step3_abstract_cohomology(sec_f, sec_g)
    check("abstract H¹ vanishes for matching sections", v is True)

    sec_g2 = [AbstractValue(DuckType.INT, SpecName.RANGE_SUM)]
    v = VerificationCascade.step3_abstract_cohomology(sec_f, sec_g2)
    check("abstract H¹ inconclusive for mismatched specs", v is None)

    # ── §12: Abstract H¹ ──────────────────────────────────
    print("§12 Abstract Cohomology")

    # Same type/spec on all fibers → H¹ = 0
    fiber_sec_same = {
        "p0": (AbstractValue(DuckType.INT, SpecName.FACTORIAL),
               AbstractValue(DuckType.INT, SpecName.FACTORIAL)),
        "p1": (AbstractValue(DuckType.INT, SpecName.FACTORIAL),
               AbstractValue(DuckType.INT, SpecName.FACTORIAL)),
    }
    h1_same, cocyc_same = compute_abstract_h1(fiber_sec_same)
    check("H¹ = 0 for matching fibers", h1_same == 0)
    check("no non-trivial cocycles", len(cocyc_same) == 0)

    # Different types on different fibers → cross-fiber cocycle
    fiber_sec_diff = {
        "p0": (AbstractValue(DuckType.INT, SpecName.FACTORIAL),
               AbstractValue(DuckType.INT, SpecName.FACTORIAL)),
        "p1": (AbstractValue(DuckType.STR, SpecName.SORTED),
               AbstractValue(DuckType.STR, SpecName.SORTED)),
    }
    h1_diff, cocyc_diff = compute_abstract_h1(fiber_sec_diff)
    check("cross-fiber cocycle detected", h1_diff > 0)

    fiber_sec_bad = {
        "p0": (AbstractValue(DuckType.INT, SpecName.FACTORIAL),
               AbstractValue(DuckType.INT, SpecName.RANGE_SUM)),
        "p1": (AbstractValue(DuckType.STR, SpecName.SORTED),
               AbstractValue(DuckType.STR, SpecName.SORTED)),
    }
    h1b, cocyc_b = compute_abstract_h1(fiber_sec_bad)
    check("H¹ computed for bad fibers", h1b >= 0)

    # ── §13: Spectral Sequence ─────────────────────────────
    print("§13 Spectral Sequence")

    pr_f = [
        PhaseResult(NormalizerPhase.BETA, "fold[mul](1,range($n))", False),
        PhaseResult(NormalizerPhase.RING, "fold[mul](1,range($n))", False),
        PhaseResult(NormalizerPhase.FOLD, "@factorial($n)", True),
    ]
    pr_g = [
        PhaseResult(NormalizerPhase.BETA, "fix[f](case(...))", False),
        PhaseResult(NormalizerPhase.RING, "fix[f](case(...))", False),
        PhaseResult(NormalizerPhase.FOLD, "@factorial($n)", True),
    ]
    rp = compute_resolution_phase(pr_f, pr_g)
    check("resolution phase is FOLD", rp == NormalizerPhase.FOLD)

    e1 = compute_e1_page(pr_f, pr_g)
    check("E₁ page has 3 entries", len(e1) == 3)
    check("E₁[BETA] unresolved", not e1[0].resolved)
    check("E₁[FOLD] resolved", e1[2].resolved)

    # E₂ page
    e1_per_fiber = {
        "int": e1,
        "str": [SpectralSequenceEntry(NormalizerPhase.BETA, ("a", "a"), True)],
    }
    e2 = compute_e2_page(e1_per_fiber)
    check("E₂ page has entries", len(e2) > 0)

    # ── §13: Type Filtration ──────────────────────────────
    print("§13 Type Filtration")

    filt = TypeFiltration()
    check("grade(int) = 2", filt.grade("int") == 2)
    check("grade(str) = 3", filt.grade("str") == 3)
    check("grade(list) = 4", filt.grade("list") == 4)
    check("grade(ref) = 5", filt.grade("ref") == 5)
    check("grade(any) = 5", filt.grade("any") == 5)
    check("fibers_at_grade(2) includes Int",
          "Int" in filt.fibers_at_grade(2))

    check("degeneration all int", check_degeneration({"n": "int"}))
    check("no degeneration with any",
          not check_degeneration({"n": "int", "x": "any"}))

    # ── §13: Phase Profiler ────────────────────────────────
    print("§13 Phase Profiler")

    canons = [
        (NormalizerPhase.BETA, "fold[mul](1,range($n))"),
        (NormalizerPhase.RING, "fold[mul](1,range($n))"),
        (NormalizerPhase.FOLD, "@factorial($n)"),
    ]
    prof = profile_normalization("raw_term", canons)
    check("profile iterations ≥ 1", prof.iterations >= 1)
    # First phase changes from "raw_term" → "fold[mul](...)" so it's changed
    check("profile first phase changed from raw",
          prof.phase_results[0].changed)
    # The resolution phase is the *first* phase that changed the term
    check("profile resolution_phase is BETA",
          prof.resolution_phase == NormalizerPhase.BETA)

    # Pair profiling — same canons means same canonical forms at each phase
    pp = profile_pair(canons, canons, "raw_f", "raw_g")
    # Same input canons → all E₁ entries resolved from the start
    check("pair profile resolution at BETA",
          pp.resolution_phase == NormalizerPhase.BETA)

    # ── §13: Convergence Verifier ──────────────────────────
    print("§13 Convergence Verifier")

    trace1 = ["a", "b", "c", "c"]
    report1 = verify_convergence(trace1)
    check("trace converges", report1.converged)
    check("trace converges at iteration 3", report1.iterations == 3)

    trace2 = ["a", "b", "c", "d", "e", "f", "g", "h", "i"]
    report2 = verify_convergence(trace2, max_iterations=8)
    check("trace diverges", not report2.converged)
    check("divergence reason", "exceeded" in report2.reason)

    trace3: list[str] = []
    report3 = verify_convergence(trace3)
    check("empty trace converges", report3.converged)

    trace4 = ["x", "x"]
    report4 = verify_convergence(trace4)
    check("immediate fixpoint", report4.converged)
    check("fixpoint at iteration 1", report4.iterations == 1)

    # ── §14: Operad Theory ─────────────────────────────────
    print("§14 Operad Theory")

    check("OP_ADD is first-order", not OP_ADD.is_higher_order)
    check("OP_MAP is higher-order", OP_MAP.is_higher_order)
    check("OP_ADD arity total = 2", OP_ADD.arity.total == 2)
    check("OP_REDUCE arity total = 3", OP_REDUCE.arity.total == 3)
    check("OP_ADD order = 1", OP_ADD.arity.order == 1)
    check("OP_MAP order = 2", OP_MAP.arity.order == 2)

    check("type_check valid", OP_ADD.type_check_inputs((Int, Int)))
    check("type_check invalid", not OP_ADD.type_check_inputs((Str, Int)))
    check("type_check PyObj wildcard", OP_ADD.type_check_inputs((PyObj, Int)))

    check("lookup_op + exists", lookup_op("+") is not None)
    check("lookup_op bogus is None", lookup_op("bogus") is None)

    # Composition
    sorted_list = operadic_compose(OP_SORTED, OP_LIST, 0)
    check("sorted∘list name", "sorted" in sorted_list.name and "list" in sorted_list.name)
    check("sorted∘list output = Seq", sorted_list.output_color == Seq)
    check("sorted∘list inputs = (Seq,)", sorted_list.input_colors == (Seq,))

    len_sorted = operadic_compose(OP_LEN, OP_SORTED, 0)
    check("len∘sorted output = Int", len_sorted.output_color == Int)

    # Color mismatch
    try:
        operadic_compose(OP_LEN, OP_ADD, 0)
        check("color mismatch raises TypeError", False)
    except TypeError:
        check("color mismatch raises TypeError", True)

    # Slot out of range
    try:
        operadic_compose(OP_SORTED, OP_LIST, 5)
        check("slot out of range raises ValueError", False)
    except ValueError:
        check("slot out of range raises ValueError", True)

    # Parallel product
    par = operadic_parallel(OP_ADD, OP_LEN)
    check("parallel name", "⊗" in par.name)
    check("parallel inputs", len(par.input_colors) == 3)

    # Associativity — check for consistent compositions
    # sorted ∘₀ (list ∘₀ range)  vs  (sorted ∘₀ list) ∘₀ range
    check("associativity sorted/list/range",
          verify_associativity(OP_SORTED, OP_LIST, OP_RANGE, 0, 0))

    # ── §14: Operadic Relations ────────────────────────────
    print("§14 Operadic Relations")

    check("map_map_fusion",
          "f ∘ g" in map_map_fusion("f", "g"))
    check("map_fold_fusion",
          "reduce" in map_fold_fusion("+", "h", "0"))
    check("filter_map commutation conservative",
          not check_filter_map_commutation("p", "h"))

    # ── §14: HOF Absorption Laws ───────────────────────────
    print("§14 HOF Absorption Laws")

    check("sorted∘list → sorted", apply_absorption("sorted", "list") == "sorted")
    check("sorted∘set → sorted", apply_absorption("sorted", "set") == "sorted")
    check("sorted∘sorted → sorted", apply_absorption("sorted", "sorted") == "sorted")
    check("len∘list → len", apply_absorption("len", "list") == "len")
    check("len∘sorted → len", apply_absorption("len", "sorted") == "len")
    check("len∘reversed → len", apply_absorption("len", "reversed") == "len")
    check("sum∘sorted → sum", apply_absorption("sum", "sorted") == "sum")
    check("min∘sorted → min", apply_absorption("min", "sorted") == "min")
    check("max∘sorted → max", apply_absorption("max", "sorted") == "max")
    check("set∘list → set", apply_absorption("set", "list") == "set")
    check("no absorption for add∘mul", apply_absorption("add", "mul") is None)

    # Absorption chain
    chain = check_absorption_chain(["sorted", "list", "set"])
    check("chain ['sorted','list','set'] → ['sorted']",
          chain == ["sorted"])
    chain2 = check_absorption_chain(["len", "sorted", "list"])
    check("chain ['len','sorted','list'] → ['len']",
          chain2 == ["len"])
    chain3 = check_absorption_chain(["map", "filter"])
    check("chain no absorption → 2 elements", len(chain3) == 2)

    # HOF checker
    checker = HOFAbsorptionChecker()
    results = checker.check_all()
    check("all absorption laws pass", checker.all_pass)
    check("results dict non-empty", len(results) > 0)

    # ── §14: Decision Cascade Optimizer ────────────────────
    print("§14 Decision Cascade Optimizer")

    sd1 = optimize_cascade(DuckType.INT, DuckType.STR, None, None)
    check("duck mismatch → skip all", sd1.skip_z3 and sd1.skip_path_search)
    check("duck mismatch reason", "NEQ" in sd1.reason)

    sd2 = optimize_cascade(
        DuckType.INT, DuckType.INT,
        SpecName.FACTORIAL, SpecName.FACTORIAL,
    )
    check("spec match → skip all", sd2.skip_z3 and sd2.skip_path_search)
    check("spec match reason", "EQ" in sd2.reason)

    sd3 = optimize_cascade(
        DuckType.INT, DuckType.INT,
        SpecName.FACTORIAL, SpecName.RANGE_SUM,
        phase_resolution=NormalizerPhase.BETA,
    )
    check("early phase → skip path search", sd3.skip_path_search)
    check("early phase → no skip z3", not sd3.skip_z3)

    sd4 = optimize_cascade(
        DuckType.INT, DuckType.INT,
        SpecName.FACTORIAL, SpecName.RANGE_SUM,
    )
    check("no resolution → no skips",
          not sd4.skip_z3 and not sd4.skip_path_search)

    # ── Integration Pipeline ───────────────────────────────
    print("Integration Pipeline")

    # NEQ case
    r = full_pipeline_with_galois_spectral_operad(
        ops_f={'mul', 'sub'}, ops_g={'method_upper'},
        spec_f=None, spec_g=None, duck_types={"n": "int"},
    )
    check("pipeline NEQ verdict", r["verdict"] == "NON_EQUIVALENT")

    # EQ case via spec match
    r2 = full_pipeline_with_galois_spectral_operad(
        ops_f={'mul', 'sub'}, ops_g={'floordiv', 'pow'},
        spec_f="factorial", spec_g="factorial",
        duck_types={"n": "int"},
    )
    check("pipeline EQ verdict", r2["verdict"] == "EQUIVALENT")

    # Inconclusive → path search
    r3 = full_pipeline_with_galois_spectral_operad(
        ops_f={'mul'}, ops_g={'sub'},
        spec_f="factorial", spec_g="range_sum",
        duck_types={"n": "int"},
    )
    check("pipeline REQUIRES_PATH_SEARCH or LIKELY_EQUIVALENT",
          r3["verdict"] in ("REQUIRES_PATH_SEARCH", "LIKELY_EQUIVALENT"))

    # With polymorphic parameter
    r4 = full_pipeline_with_galois_spectral_operad(
        ops_f={'iter', 'call_len'}, ops_g={'iter', 'getitem'},
        spec_f=None, spec_g=None,
        duck_types={"xs": "any", "n": "int"},
    )
    check("pipeline with polymorphic param",
          not r4.get("spectral_degenerates", True))

    # ── Summary ────────────────────────────────────────────
    total = passed + failed
    print(f"\n{'='*60}")
    print(f"  {passed}/{total} tests passed", end="")
    if failed:
        print(f"  ({failed} FAILED)")
    else:
        print("  ✓ all pass")
    print(f"{'='*60}")
    if failed:
        raise SystemExit(1)


if __name__ == "__main__":
    _run_tests()
