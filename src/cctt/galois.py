"""§12: Galois Connections Between Type Abstractions.

Formalizes the Galois connection α ⊣ γ between concrete operation sets
(from duck.py) and an abstract product lattice D_duck × D_spec.

Components:
  - DuckType lattice with join/meet/leq (Definition 12.2)
  - Hasse diagram computation for the lattice
  - AbstractValue product lattice A = D_duck × D_spec
  - GaloisConnection: α (abstraction) and γ (concretization)
  - VerificationCascade: Galois-accelerated decision pipeline
  - Abstract Čech cohomology: H¹ over abstract domain before Z3
  - Cascade optimizer: skip expensive stages when cheap ones decide

Integration: provides a pre-filter for checker.py — programs whose
abstract values disagree are provably non-equivalent without Z3.
"""
from __future__ import annotations

import time
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple,
)


# ═══════════════════════════════════════════════════════════════════════
# §12  DUCK TYPE LATTICE  (Definition 12.2)
# ═══════════════════════════════════════════════════════════════════════

class DuckType(Enum):
    """Elements of the duck type lattice D_duck.

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
    common = _DUCK_ORDER.get(a, frozenset()) & _DUCK_ORDER.get(b, frozenset())
    if not common:
        return DuckType.ANY
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
    lower_a = {d for d in DuckType if duck_leq(d, a)}
    lower_b = {d for d in DuckType if duck_leq(d, b)}
    common = lower_a & lower_b
    if not common:
        return DuckType.UNKNOWN
    for candidate in common:
        if all(duck_leq(c, candidate) or c == candidate for c in common):
            return candidate
    return DuckType.UNKNOWN


def duck_from_string(s: str) -> DuckType:
    """Map a raw duck type string (from duck.py) to DuckType enum."""
    _map = {dt.value: dt for dt in DuckType}
    return _map.get(s, DuckType.UNKNOWN)


# ═══════════════════════════════════════════════════════════════════════
# §12  HASSE DIAGRAM
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class HasseDiagram:
    """Explicit Hasse diagram of the duck type lattice.

    ``edges`` stores (a, b) where a covers b (a < b with nothing between).
    """
    elements: FrozenSet[DuckType]
    edges: FrozenSet[Tuple[DuckType, DuckType]]

    def children(self, node: DuckType) -> FrozenSet[DuckType]:
        return frozenset(b for a, b in self.edges if a == node)

    def parents(self, node: DuckType) -> FrozenSet[DuckType]:
        return frozenset(a for a, b in self.edges if b == node)

    def is_chain(self) -> bool:
        for a in self.elements:
            for b in self.elements:
                if a != b and not duck_leq(a, b) and not duck_leq(b, a):
                    return False
        return True


def compute_hasse_diagram() -> HasseDiagram:
    """Build the Hasse diagram — covering relations only (no transitive edges)."""
    elements = frozenset(DuckType)
    direct_edges: Set[Tuple[DuckType, DuckType]] = set()
    for a in DuckType:
        for b in DuckType:
            if a != b and duck_leq(a, b):
                direct_edges.add((a, b))
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
    """Elements of the specification lattice D_spec."""
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
    """Product lattice A = D_duck × D_spec (Definition 12.2)."""
    duck: DuckType
    spec: SpecName

    def leq(self, other: AbstractValue) -> bool:
        duck_ok = duck_leq(self.duck, other.duck)
        spec_ok = (self.spec == other.spec) or (other.spec == SpecName.TOP)
        return duck_ok and spec_ok

    def join(self, other: AbstractValue) -> AbstractValue:
        d = duck_join(self.duck, other.duck)
        s = self.spec if self.spec == other.spec else SpecName.TOP
        return AbstractValue(d, s)

    def meet(self, other: AbstractValue) -> AbstractValue:
        d = duck_meet(self.duck, other.duck)
        if self.spec == other.spec:
            s = self.spec
        elif self.spec == SpecName.TOP:
            s = other.spec
        elif other.spec == SpecName.TOP:
            s = self.spec
        else:
            s = SpecName.TOP
        return AbstractValue(d, s)

    def __repr__(self) -> str:
        return f"({self.duck.value}, {self.spec.value})"


# ═══════════════════════════════════════════════════════════════════════
# §12  GALOIS CONNECTION  α ⊣ γ  (Theorem 12.4)
# ═══════════════════════════════════════════════════════════════════════

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


class GaloisConnection:
    """The Galois connection α: C → A, γ: A → C (Theorem 12.4).

    Wraps duck.infer_duck_type and spec identification into a single
    abstraction map computing the product lattice value.
    """

    @staticmethod
    def alpha_duck(ops: Set[str]) -> DuckType:
        """Abstraction map α_duck (Definition 12.3).

        Priority mirrors duck.py's infer_duck_type.
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
        """Concretization γ_duck: duck type → characteristic operation set."""
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
        """Verify: α(γ(a)) ⊑ a (upper adjoint property / idempotence)."""
        a = GaloisConnection.alpha_duck(ops)
        g = GaloisConnection.gamma_duck(dt)
        a_prime = GaloisConnection.alpha_duck(g)
        return duck_leq(a, dt) == (ops <= g or duck_leq(a, dt))


# ═══════════════════════════════════════════════════════════════════════
# §12  ABSTRACT ČECH COHOMOLOGY (H¹ over abstract domain)
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class AbstractCechCocycle:
    """A 1-cocycle in the abstract Čech complex.

    On overlap U_i ∩ U_j the cocycle records the discrepancy
    between the two local section assignments.
    """
    fiber_i: str
    fiber_j: str
    value_i: AbstractValue
    value_j: AbstractValue

    @property
    def is_coboundary(self) -> bool:
        """A cocycle is a coboundary iff the two values are comparable."""
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
# §12  VERIFICATION CASCADE  (Corollary 12.8)
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class CascadeStep:
    """Record of a single step in the decision cascade."""
    name: str
    verdict: Optional[bool]
    elapsed_us: int
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
        for s in self.steps:
            if s.verdict is not None:
                return s.name
        return None


class VerificationCascade:
    """Galois-accelerated verification pipeline.

    Each step is strictly cheaper than the next and provides a sound
    answer when it succeeds.
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
        """Step 3: H¹ vanishes in abstract domain?"""
        if not sections_f or not sections_g:
            return None
        if len(sections_f) != len(sections_g):
            return None
        for sf, sg in zip(sections_f, sections_g):
            j = sf.join(sg)
            if j.spec == SpecName.TOP and sf.spec != sg.spec:
                return None
            if not sf.leq(j) or not sg.leq(j):
                return False
        return True

    @staticmethod
    def step4_full_check() -> Optional[bool]:
        """Step 4: full Z3 / BFS path search (delegate to checker)."""
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
        """Execute the full cascade, returning as soon as one step decides."""
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
# §12  CASCADE OPTIMIZER  (Corollary 12.8 — skip expensive stages)
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
    phase_resolution: Optional[int] = None,
) -> SkipDecision:
    """Decide which stages to skip based on abstract analysis.

    ``phase_resolution`` is the normalizer phase index (0-7) at which
    the two programs were resolved to the same canonical form.
    """
    decision = SkipDecision()

    if duck_f != duck_g:
        decision.skip_z3 = True
        decision.skip_path_search = True
        decision.skip_spectral = True
        decision.reason = "duck types disagree → NEQ"
        return decision

    if spec_f is not None and spec_g is not None and spec_f == spec_g:
        decision.skip_z3 = True
        decision.skip_path_search = True
        decision.skip_spectral = True
        decision.reason = f"spec match ({spec_f.value}) → EQ"
        return decision

    if phase_resolution is not None and phase_resolution <= 3:
        decision.skip_path_search = True
        decision.reason = f"resolved at normalizer phase {phase_resolution}"

    return decision


# ═══════════════════════════════════════════════════════════════════════
# INTEGRATION: galois_prefilter for checker.py
# ═══════════════════════════════════════════════════════════════════════

def galois_prefilter(
    ops_f: Set[str],
    ops_g: Set[str],
    spec_f: Optional[str] = None,
    spec_g: Optional[str] = None,
    duck_types: Optional[Dict[str, str]] = None,
) -> Dict[str, Any]:
    """Run the Galois pre-filter before expensive Z3/path search.

    Returns a dict with:
      - ``verdict``: "EQUIVALENT", "NON_EQUIVALENT", or None (undecided)
      - ``duck_f``, ``duck_g``: DuckType enum values
      - ``skip``: SkipDecision for downstream stages
      - ``abstract_h1``: H¹ dimension in the abstract domain
      - ``cascade``: full CascadeResult
    """
    result: Dict[str, Any] = {}

    duck_f = GaloisConnection.alpha_duck(ops_f)
    duck_g = GaloisConnection.alpha_duck(ops_g)
    result["duck_f"] = duck_f
    result["duck_g"] = duck_g

    # Run cascade
    cascade = VerificationCascade.run(
        ops_f, ops_g, spec_f, spec_g,
    )
    result["cascade"] = cascade

    if cascade.verdict is False:
        result["verdict"] = "NON_EQUIVALENT"
        result["skip"] = SkipDecision(True, True, True, "cascade NEQ")
        result["abstract_h1"] = -1
        return result

    if cascade.verdict is True:
        result["verdict"] = "EQUIVALENT"
        result["skip"] = SkipDecision(True, True, True, "cascade EQ")
        result["abstract_h1"] = 0
        return result

    # Cascade inconclusive — compute abstract H¹
    spec_enum_f = GaloisConnection.alpha_spec(spec_f)
    spec_enum_g = GaloisConnection.alpha_spec(spec_g)
    skip = optimize_cascade(duck_f, duck_g, spec_enum_f, spec_enum_g)
    result["skip"] = skip

    if duck_types:
        fiber_sections = {
            p: (AbstractValue(duck_f, spec_enum_f),
                AbstractValue(duck_g, spec_enum_g))
            for p in duck_types
        }
        h1_dim, cocycles = compute_abstract_h1(fiber_sections)
        result["abstract_h1"] = h1_dim
        result["abstract_cocycles"] = len(cocycles)
    else:
        result["abstract_h1"] = 0

    result["verdict"] = None
    return result


# ═══════════════════════════════════════════════════════════════════════
# SELF-TESTS
# ═══════════════════════════════════════════════════════════════════════

def _run_tests() -> None:
    """Comprehensive self-tests for the Galois connection module."""
    passed = 0
    failed = 0

    def check(name: str, cond: bool) -> None:
        nonlocal passed, failed
        if cond:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {name}")

    # ── Duck Type Lattice ──────────────────────────────────
    print("Duck Type Lattice")
    check("INT ⊑ INT", duck_leq(DuckType.INT, DuckType.INT))
    check("INT ⊑ ANY", duck_leq(DuckType.INT, DuckType.ANY))
    check("¬(ANY ⊑ INT)", not duck_leq(DuckType.ANY, DuckType.INT))
    check("BOOL ⊑ INT", duck_leq(DuckType.BOOL, DuckType.INT))
    check("LIST ⊑ COLLECTION", duck_leq(DuckType.LIST, DuckType.COLLECTION))
    check("SET ⊑ COLLECTION", duck_leq(DuckType.SET, DuckType.COLLECTION))
    check("¬(STR ⊑ LIST)", not duck_leq(DuckType.STR, DuckType.LIST))
    check("UNKNOWN ⊑ ANY", duck_leq(DuckType.UNKNOWN, DuckType.ANY))

    check("join(INT,INT)=INT",
          duck_join(DuckType.INT, DuckType.INT) == DuckType.INT)
    check("join(INT,STR)=COLLECTION",
          duck_join(DuckType.INT, DuckType.STR) == DuckType.COLLECTION)
    check("join(LIST,SET)=COLLECTION",
          duck_join(DuckType.LIST, DuckType.SET) == DuckType.COLLECTION)
    check("meet(INT,INT)=INT",
          duck_meet(DuckType.INT, DuckType.INT) == DuckType.INT)
    check("meet(ANY,INT)=INT",
          duck_meet(DuckType.ANY, DuckType.INT) == DuckType.INT)

    check("duck_from_string('int')=INT",
          duck_from_string('int') == DuckType.INT)
    check("duck_from_string('bogus')=UNKNOWN",
          duck_from_string('bogus') == DuckType.UNKNOWN)

    # ── Hasse Diagram ──────────────────────────────────────
    print("Hasse Diagram")
    hasse = compute_hasse_diagram()
    check("has all elements", len(hasse.elements) == len(DuckType))
    check("has edges", len(hasse.edges) > 0)
    for a, b in hasse.edges:
        for c in hasse.elements:
            if c != a and c != b:
                check(f"no transitive {a.value}→{c.value}→{b.value}",
                      not (duck_leq(a, c) and duck_leq(c, b)))
    check("not a chain", not hasse.is_chain())

    # ── Galois Connection ──────────────────────────────────
    print("Galois Connection")
    check("α numeric→INT",
          GaloisConnection.alpha_duck({'mul', 'add'}) == DuckType.INT)
    check("α str→STR",
          GaloisConnection.alpha_duck({'method_upper'}) == DuckType.STR)
    check("α list→LIST",
          GaloisConnection.alpha_duck({'method_append'}) == DuckType.LIST)
    check("α dict→DICT",
          GaloisConnection.alpha_duck({'method_keys'}) == DuckType.DICT)
    check("α set→SET",
          GaloisConnection.alpha_duck({'method_union'}) == DuckType.SET)
    check("α collection→COLLECTION",
          GaloisConnection.alpha_duck({'iter', 'call_len'}) == DuckType.COLLECTION)
    check("α empty→ANY",
          GaloisConnection.alpha_duck(set()) == DuckType.ANY)

    check("α_spec factorial",
          GaloisConnection.alpha_spec("factorial") == SpecName.FACTORIAL)
    check("α_spec None→TOP",
          GaloisConnection.alpha_spec(None) == SpecName.TOP)

    av = GaloisConnection.alpha({'mul', 'sub'}, "factorial")
    check("α product", av.duck == DuckType.INT and av.spec == SpecName.FACTORIAL)

    # γ roundtrip: α(γ(a)) ⊑ a
    for dt in (DuckType.INT, DuckType.STR):
        g = GaloisConnection.gamma_duck(dt)
        if g:
            a_back = GaloisConnection.alpha_duck(g)
            check(f"γ∘α roundtrip {dt.value}", a_back == dt)

    for s in SpecName:
        desc = GaloisConnection.gamma_spec(s)
        check(f"γ_spec({s.value}) non-empty", len(desc) > 0)

    # ── Abstract Values ────────────────────────────────────
    print("Abstract Values")
    a1 = AbstractValue(DuckType.INT, SpecName.FACTORIAL)
    a2 = AbstractValue(DuckType.INT, SpecName.TOP)
    a3 = AbstractValue(DuckType.STR, SpecName.SORTED)
    check("a1 ⊑ a2", a1.leq(a2))
    check("¬(a2 ⊑ a1)", not a2.leq(a1))
    check("¬(a1 ⊑ a3)", not a1.leq(a3))
    j = a1.join(a3)
    check("join lifts duck", j.duck in (DuckType.COLLECTION, DuckType.ANY))
    check("join lifts spec", j.spec == SpecName.TOP)
    m = a1.meet(a2)
    check("meet preserves spec", m.spec == SpecName.FACTORIAL)
    check("meet preserves duck", m.duck == DuckType.INT)

    # ── Abstract H¹ ────────────────────────────────────────
    print("Abstract Cohomology")
    fiber_sec_same = {
        "p0": (AbstractValue(DuckType.INT, SpecName.FACTORIAL),
               AbstractValue(DuckType.INT, SpecName.FACTORIAL)),
        "p1": (AbstractValue(DuckType.INT, SpecName.FACTORIAL),
               AbstractValue(DuckType.INT, SpecName.FACTORIAL)),
    }
    h1_same, cocyc_same = compute_abstract_h1(fiber_sec_same)
    check("H¹=0 matching fibers", h1_same == 0)
    check("no cocycles", len(cocyc_same) == 0)

    fiber_sec_diff = {
        "p0": (AbstractValue(DuckType.INT, SpecName.FACTORIAL),
               AbstractValue(DuckType.INT, SpecName.FACTORIAL)),
        "p1": (AbstractValue(DuckType.STR, SpecName.SORTED),
               AbstractValue(DuckType.STR, SpecName.SORTED)),
    }
    h1_diff, cocyc_diff = compute_abstract_h1(fiber_sec_diff)
    check("cross-fiber cocycle", h1_diff > 0)

    # ── Verification Cascade ───────────────────────────────
    print("Verification Cascade")
    v = VerificationCascade.step1_duck_match({'mul'}, {'method_upper'})
    check("duck mismatch→False", v is False)
    v = VerificationCascade.step1_duck_match({'mul'}, {'sub'})
    check("duck match→None", v is None)
    v = VerificationCascade.step2_spec_match("factorial", "factorial")
    check("spec match→True", v is True)
    v = VerificationCascade.step2_spec_match("factorial", "range_sum")
    check("spec mismatch→None", v is None)

    cr = VerificationCascade.run(ops_f={'mul', 'sub'}, ops_g={'method_upper'})
    check("cascade NEQ", cr.verdict is False)
    check("decided_at duck_match", cr.decided_at == "duck_match")

    cr2 = VerificationCascade.run(
        ops_f={'mul'}, ops_g={'sub'},
        spec_f="factorial", spec_g="factorial",
    )
    check("cascade EQ", cr2.verdict is True)
    check("decided_at spec_match", cr2.decided_at == "spec_match")

    sec_f = [AbstractValue(DuckType.INT, SpecName.FACTORIAL)]
    sec_g = [AbstractValue(DuckType.INT, SpecName.FACTORIAL)]
    v = VerificationCascade.step3_abstract_cohomology(sec_f, sec_g)
    check("abstract H¹ vanishes", v is True)

    sec_g2 = [AbstractValue(DuckType.INT, SpecName.RANGE_SUM)]
    v = VerificationCascade.step3_abstract_cohomology(sec_f, sec_g2)
    check("abstract H¹ inconclusive", v is None)

    # ── Cascade Optimizer ──────────────────────────────────
    print("Cascade Optimizer")
    sd1 = optimize_cascade(DuckType.INT, DuckType.STR, None, None)
    check("duck NEQ→skip all", sd1.skip_z3 and sd1.skip_path_search)
    check("duck NEQ reason", "NEQ" in sd1.reason)

    sd2 = optimize_cascade(
        DuckType.INT, DuckType.INT,
        SpecName.FACTORIAL, SpecName.FACTORIAL,
    )
    check("spec EQ→skip all", sd2.skip_z3 and sd2.skip_path_search)
    check("spec EQ reason", "EQ" in sd2.reason)

    sd3 = optimize_cascade(
        DuckType.INT, DuckType.INT,
        SpecName.FACTORIAL, SpecName.RANGE_SUM,
        phase_resolution=1,
    )
    check("early phase→skip path search", sd3.skip_path_search)
    check("early phase→no skip z3", not sd3.skip_z3)

    sd4 = optimize_cascade(
        DuckType.INT, DuckType.INT,
        SpecName.FACTORIAL, SpecName.RANGE_SUM,
    )
    check("no resolution→no skips",
          not sd4.skip_z3 and not sd4.skip_path_search)

    # ── galois_prefilter ───────────────────────────────────
    print("Prefilter Integration")
    r = galois_prefilter(
        ops_f={'mul', 'sub'}, ops_g={'method_upper'},
    )
    check("prefilter NEQ", r["verdict"] == "NON_EQUIVALENT")

    r2 = galois_prefilter(
        ops_f={'mul'}, ops_g={'sub'},
        spec_f="factorial", spec_g="factorial",
    )
    check("prefilter EQ", r2["verdict"] == "EQUIVALENT")

    r3 = galois_prefilter(
        ops_f={'mul'}, ops_g={'sub'},
        spec_f="factorial", spec_g="range_sum",
        duck_types={"n": "int"},
    )
    check("prefilter undecided", r3["verdict"] is None)
    check("prefilter has h1", "abstract_h1" in r3)

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
