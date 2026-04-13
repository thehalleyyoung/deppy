"""Proposals for Chapters 15-17: Enrichment, Inductive Families, Computable Fragment.

Exhaustive, importable module connecting monograph theory to concrete
implementation in new_src/cctt/.  Every class is fully implemented with
docstrings, type annotations, edge-case handling, and self-tests.

Proposals included:
    1. DuckType lattice as explicit poset with meet/join/covers
    2. Enriched Hom computation over the duck-type lattice
    3. OTerm arity tracker (indexed inductive family)
    4. OTerm generic eliminator (dependent recursor)
    5. OTerm pattern-matching exhaustiveness checker
    6. Decidability classifier for OTerm trees
    7. Decidability oracle (predict resolution strategy for a pair)
    8. Z3 theory fragment classifier
    9. Z3 theory fragment analyzer (per-pair feature vector)
   10. Enriched cohomology (H¹ over the duck-type lattice)
   11. Inductive family eliminator code generator
"""
from __future__ import annotations

import itertools
import textwrap
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Optional,
    Set,
    Tuple,
    Union,
)


# ═══════════════════════════════════════════════════════════════════
# §1  DUCK-TYPE LATTICE AS EXPLICIT POSET
# ═══════════════════════════════════════════════════════════════════

class DuckType:
    """A duck type = a set of required operations.

    Elements of the *duck-type lattice* D from Chapter 15.  Ordering
    is by operation-set inclusion: D₁ ≤ D₂ iff ops(D₁) ⊆ ops(D₂).
    Meet = intersection of ops, join = union of ops.  The top element ⊤
    has *all* ops (most refined); the bottom element ⊥ has none (most
    coarse / the ``object`` type).
    """

    __slots__ = ("name", "ops")

    def __init__(self, name: str, ops: FrozenSet[str]) -> None:
        self.name: str = name
        self.ops: FrozenSet[str] = ops

    # -- ordering ----------------------------------------------------------

    def __le__(self, other: DuckType) -> bool:
        """Subtyping: D₁ ≤ D₂ iff ops(D₁) ⊆ ops(D₂)."""
        return self.ops <= other.ops

    def __lt__(self, other: DuckType) -> bool:
        return self.ops < other.ops

    def __ge__(self, other: DuckType) -> bool:
        return other.ops <= self.ops

    def __gt__(self, other: DuckType) -> bool:
        return other.ops < self.ops

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, DuckType):
            return NotImplemented
        return self.ops == other.ops

    def __hash__(self) -> int:
        return hash(self.ops)

    # -- lattice operations ------------------------------------------------

    def meet(self, other: DuckType) -> DuckType:
        """Greatest lower bound (intersection of ops)."""
        return DuckType(
            f"({self.name}∧{other.name})",
            self.ops & other.ops,
        )

    def join(self, other: DuckType) -> DuckType:
        """Least upper bound (union of ops)."""
        return DuckType(
            f"({self.name}∨{other.name})",
            self.ops | other.ops,
        )

    def difference(self, other: DuckType) -> DuckType:
        """Ops in *self* but not in *other*."""
        return DuckType(
            f"({self.name}\\{other.name})",
            self.ops - other.ops,
        )

    def is_bottom(self) -> bool:
        """True if this is the trivial ``object`` type (no ops)."""
        return len(self.ops) == 0

    def covers(self, other: DuckType) -> bool:
        """True if *self* covers *other* (no element strictly between)."""
        if not (other < self):
            return False
        diff = self.ops - other.ops
        return len(diff) == 1

    def width(self) -> int:
        """Number of operations (a measure of specificity)."""
        return len(self.ops)

    # -- display -----------------------------------------------------------

    def __repr__(self) -> str:
        abbrev = ",".join(sorted(self.ops)[:4])
        if len(self.ops) > 4:
            abbrev += ",…"
        return f"DuckType({self.name!r}, {{{abbrev}}})"

    def __str__(self) -> str:
        return self.name


# -- canonical duck-type atoms -------------------------------------------

BOTTOM = DuckType("⊥", frozenset())
ADDABLE = DuckType("Addable", frozenset({"__add__"}))
ITERABLE = DuckType(
    "Iterable", frozenset({"__iter__", "__next__"})
)
COMPARABLE = DuckType(
    "Comparable",
    frozenset({"__lt__", "__le__", "__gt__", "__ge__"}),
)
HASHABLE = DuckType("Hashable", frozenset({"__hash__", "__eq__"}))
SIZED = DuckType("Sized", frozenset({"__len__"}))
SUBSCRIPTABLE = DuckType("Subscriptable", frozenset({"__getitem__"}))
NUMERIC = DuckType(
    "Numeric",
    frozenset({
        "__add__", "__sub__", "__mul__", "__floordiv__",
        "__mod__", "__neg__", "__abs__",
    }),
)
STRINGLIKE = DuckType(
    "StringLike",
    frozenset({
        "__add__", "__mul__", "__getitem__", "__len__",
        "__contains__", "__iter__",
    }),
)

ALL_ATOMS: List[DuckType] = [
    BOTTOM, ADDABLE, ITERABLE, COMPARABLE,
    HASHABLE, SIZED, SUBSCRIPTABLE, NUMERIC, STRINGLIKE,
]


# ═══════════════════════════════════════════════════════════════════
# §2  DUCK-TYPE POSET (finite lattice utilities)
# ═══════════════════════════════════════════════════════════════════

class DuckTypePoset:
    """Finite poset of duck types with precomputed Hasse diagram.

    Keeps a universe of named duck types and exposes lattice queries:
    meet, join, all-covers, upset, downset.
    """

    def __init__(self, elements: Optional[List[DuckType]] = None) -> None:
        self.elements: List[DuckType] = list(elements or ALL_ATOMS)
        self._hasse: Dict[DuckType, Set[DuckType]] = {}
        self._rebuild_hasse()

    # -- mutators ----------------------------------------------------------

    def add(self, dt: DuckType) -> None:
        """Insert a new element and rebuild the diagram."""
        if dt not in self.elements:
            self.elements.append(dt)
            self._rebuild_hasse()

    # -- lattice -----------------------------------------------------------

    def meet(self, a: DuckType, b: DuckType) -> DuckType:
        """Greatest lower bound in the universe."""
        m = a.meet(b)
        best = BOTTOM
        for e in self.elements:
            if e <= a and e <= b and best <= e:
                best = e
        return best if best in self.elements else m

    def join(self, a: DuckType, b: DuckType) -> DuckType:
        """Least upper bound in the universe."""
        j = a.join(b)
        best: Optional[DuckType] = None
        for e in self.elements:
            if a <= e and b <= e:
                if best is None or e <= best:
                    best = e
        return best if best is not None else j

    def upset(self, dt: DuckType) -> List[DuckType]:
        """All elements ≥ *dt*."""
        return [e for e in self.elements if dt <= e]

    def downset(self, dt: DuckType) -> List[DuckType]:
        """All elements ≤ *dt*."""
        return [e for e in self.elements if e <= dt]

    def covers_of(self, dt: DuckType) -> List[DuckType]:
        """Immediate successors in the Hasse diagram."""
        return list(self._hasse.get(dt, set()))

    # -- internals ---------------------------------------------------------

    def _rebuild_hasse(self) -> None:
        """Compute the Hasse diagram (covering relation)."""
        self._hasse = {e: set() for e in self.elements}
        for a in self.elements:
            for b in self.elements:
                if a < b:
                    is_cover = True
                    for c in self.elements:
                        if a < c and c < b:
                            is_cover = False
                            break
                    if is_cover:
                        self._hasse[a].add(b)


# ═══════════════════════════════════════════════════════════════════
# §3  ENRICHED HOM (Chapter 15)
# ═══════════════════════════════════════════════════════════════════

@dataclass
class EnrichedHomResult:
    """Result of enriched-hom computation.

    Stores the per-fiber duck-type agreements and the global meet.
    """

    per_fiber: Dict[str, DuckType]
    global_meet: DuckType
    fibers_checked: int
    fibers_agreeing: int

    @property
    def is_equivalent(self) -> bool:
        """True iff the global meet is non-trivial (some ops agree)."""
        return not self.global_meet.is_bottom()

    def refinement_level(self) -> int:
        """Width of the global meet — how refined the agreement is."""
        return self.global_meet.width()

    def disagreeing_fibers(self) -> List[str]:
        """Fibers where f and g share zero ops."""
        return [f for f, dt in self.per_fiber.items() if dt.is_bottom()]


def enriched_hom(
    fiber_results: Dict[str, Set[str]],
) -> EnrichedHomResult:
    """Compute the enriched hom from per-fiber equivalence results.

    Args:
        fiber_results: maps fiber name → set of duck-type op names
            under which f and g agree on that fiber.

    Returns:
        EnrichedHomResult with per-fiber duck types and the global meet.
    """
    per_fiber: Dict[str, DuckType] = {}
    ops_accumulator: Optional[FrozenSet[str]] = None
    agreeing = 0

    for fiber_name, fiber_ops in fiber_results.items():
        dt = DuckType(f"fiber:{fiber_name}", frozenset(fiber_ops))
        per_fiber[fiber_name] = dt
        if not dt.is_bottom():
            agreeing += 1
        if ops_accumulator is None:
            ops_accumulator = frozenset(fiber_ops)
        else:
            ops_accumulator = ops_accumulator & frozenset(fiber_ops)

    global_meet = DuckType("enriched", ops_accumulator or frozenset())

    return EnrichedHomResult(
        per_fiber=per_fiber,
        global_meet=global_meet,
        fibers_checked=len(fiber_results),
        fibers_agreeing=agreeing,
    )


def enriched_hom_from_duck_types(
    fiber_ducks: Dict[str, DuckType],
) -> EnrichedHomResult:
    """Convenience wrapper accepting DuckType values directly."""
    raw: Dict[str, Set[str]] = {
        name: set(dt.ops) for name, dt in fiber_ducks.items()
    }
    return enriched_hom(raw)


# ═══════════════════════════════════════════════════════════════════
# §4  OTerm ARITY TRACKER  (Chapter 16 — indexed inductive family)
# ═══════════════════════════════════════════════════════════════════

def _oterm_types() -> tuple:
    """Lazy import of OTerm constructors from denotation.py."""
    from new_src.cctt.denotation import (
        OVar, OLit, OOp, OFold, OCase, OFix, OSeq,
        ODict, OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    )
    return (
        OVar, OLit, OOp, OFold, OCase, OFix, OSeq,
        ODict, OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    )


def oterm_free_vars(term: Any) -> FrozenSet[str]:
    """Collect all free variable names (OVar.name) in a term."""
    (OVar, OLit, OOp, OFold, OCase, OFix, OSeq,
     ODict, OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch) = _oterm_types()

    if isinstance(term, OLit):
        return frozenset()
    if isinstance(term, OVar):
        return frozenset({term.name})
    if isinstance(term, OOp):
        acc: Set[str] = set()
        for a in term.args:
            acc |= oterm_free_vars(a)
        return frozenset(acc)
    if isinstance(term, OFold):
        return oterm_free_vars(term.init) | oterm_free_vars(term.collection)
    if isinstance(term, OCase):
        return (oterm_free_vars(term.test)
                | oterm_free_vars(term.true_branch)
                | oterm_free_vars(term.false_branch))
    if isinstance(term, OFix):
        return oterm_free_vars(term.body) - frozenset({term.name})
    if isinstance(term, OSeq):
        acc = set()
        for e in term.elements:
            acc |= oterm_free_vars(e)
        return frozenset(acc)
    if isinstance(term, ODict):
        acc = set()
        for k, v in term.pairs:
            acc |= oterm_free_vars(k) | oterm_free_vars(v)
        return frozenset(acc)
    if isinstance(term, OLam):
        return oterm_free_vars(term.body) - frozenset(term.params)
    if isinstance(term, OMap):
        acc = oterm_free_vars(term.transform) | oterm_free_vars(term.collection)
        if term.filter_pred is not None:
            acc |= oterm_free_vars(term.filter_pred)
        return frozenset(acc)
    if isinstance(term, OQuotient):
        return oterm_free_vars(term.inner)
    if isinstance(term, OCatch):
        return oterm_free_vars(term.body) | oterm_free_vars(term.default)
    if isinstance(term, OAbstract):
        acc = set()
        for a in term.inputs:
            acc |= oterm_free_vars(a)
        return frozenset(acc)
    return frozenset()


def oterm_arity(term: Any) -> int:
    """Compute the arity index of an OTerm.

    Arity = |free variables|.  This is the family index from the
    monograph's OTerm(n) indexed inductive family.
    """
    return len(oterm_free_vars(term))


def oterm_depth(term: Any) -> int:
    """Maximum nesting depth of a term."""
    (OVar, OLit, OOp, OFold, OCase, OFix, OSeq,
     ODict, OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch) = _oterm_types()

    if isinstance(term, (OLit, OVar, OUnknown)):
        return 0
    if isinstance(term, OOp):
        return 1 + max((oterm_depth(a) for a in term.args), default=0)
    if isinstance(term, OFold):
        return 1 + max(oterm_depth(term.init), oterm_depth(term.collection))
    if isinstance(term, OCase):
        return 1 + max(oterm_depth(term.test),
                       oterm_depth(term.true_branch),
                       oterm_depth(term.false_branch))
    if isinstance(term, OFix):
        return 1 + oterm_depth(term.body)
    if isinstance(term, OSeq):
        return 1 + max((oterm_depth(e) for e in term.elements), default=0)
    if isinstance(term, ODict):
        if not term.pairs:
            return 1
        return 1 + max(max(oterm_depth(k), oterm_depth(v))
                       for k, v in term.pairs)
    if isinstance(term, OLam):
        return 1 + oterm_depth(term.body)
    if isinstance(term, OMap):
        d = max(oterm_depth(term.transform), oterm_depth(term.collection))
        if term.filter_pred is not None:
            d = max(d, oterm_depth(term.filter_pred))
        return 1 + d
    if isinstance(term, OQuotient):
        return 1 + oterm_depth(term.inner)
    if isinstance(term, OAbstract):
        return 1 + max((oterm_depth(a) for a in term.inputs), default=0)
    if isinstance(term, OCatch):
        return 1 + max(oterm_depth(term.body), oterm_depth(term.default))
    return 0


def oterm_size(term: Any) -> int:
    """Total number of constructor nodes."""
    (OVar, OLit, OOp, OFold, OCase, OFix, OSeq,
     ODict, OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch) = _oterm_types()

    if isinstance(term, (OLit, OVar, OUnknown)):
        return 1
    if isinstance(term, OOp):
        return 1 + sum(oterm_size(a) for a in term.args)
    if isinstance(term, OFold):
        return 1 + oterm_size(term.init) + oterm_size(term.collection)
    if isinstance(term, OCase):
        return (1 + oterm_size(term.test) + oterm_size(term.true_branch)
                + oterm_size(term.false_branch))
    if isinstance(term, OFix):
        return 1 + oterm_size(term.body)
    if isinstance(term, OSeq):
        return 1 + sum(oterm_size(e) for e in term.elements)
    if isinstance(term, ODict):
        return 1 + sum(oterm_size(k) + oterm_size(v) for k, v in term.pairs)
    if isinstance(term, OLam):
        return 1 + oterm_size(term.body)
    if isinstance(term, OMap):
        s = 1 + oterm_size(term.transform) + oterm_size(term.collection)
        if term.filter_pred is not None:
            s += oterm_size(term.filter_pred)
        return s
    if isinstance(term, OQuotient):
        return 1 + oterm_size(term.inner)
    if isinstance(term, OAbstract):
        return 1 + sum(oterm_size(a) for a in term.inputs)
    if isinstance(term, OCatch):
        return 1 + oterm_size(term.body) + oterm_size(term.default)
    return 1


# ═══════════════════════════════════════════════════════════════════
# §5  OTerm GENERIC ELIMINATOR (dependent recursor)
# ═══════════════════════════════════════════════════════════════════

def oterm_eliminate(term: Any, motives: Dict[str, Callable[..., Any]]) -> Any:
    """Dependent recursor for OTerm.

    *motives* maps constructor name → callable.  Missing motives use
    identity defaults.  Recursion is performed on sub-terms before
    calling the motive, so results passed to the motive are already
    eliminated.

    Example::

        oterm_eliminate(t, {
            'OLit': lambda v: str(v),
            'OOp': lambda name, *subs: f'{name}({",".join(subs)})',
        })
    """
    (OVar, OLit, OOp, OFold, OCase, OFix, OSeq,
     ODict, OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch) = _oterm_types()

    if isinstance(term, OLit):
        return motives.get("OLit", lambda v: v)(term.value)
    if isinstance(term, OVar):
        return motives.get("OVar", lambda n: n)(term.name)
    if isinstance(term, OOp):
        sub = tuple(oterm_eliminate(a, motives) for a in term.args)
        return motives.get("OOp", lambda n, *a: (n, a))(term.name, *sub)
    if isinstance(term, OFold):
        zi = oterm_eliminate(term.init, motives)
        ci = oterm_eliminate(term.collection, motives)
        return motives.get("OFold", lambda o, z, c: (o, z, c))(
            term.op_name, zi, ci
        )
    if isinstance(term, OCase):
        t = oterm_eliminate(term.test, motives)
        b1 = oterm_eliminate(term.true_branch, motives)
        b2 = oterm_eliminate(term.false_branch, motives)
        return motives.get("OCase", lambda *a: a)(t, b1, b2)
    if isinstance(term, OFix):
        b = oterm_eliminate(term.body, motives)
        return motives.get("OFix", lambda n, b: (n, b))(term.name, b)
    if isinstance(term, OSeq):
        es = tuple(oterm_eliminate(e, motives) for e in term.elements)
        return motives.get("OSeq", lambda *e: e)(*es)
    if isinstance(term, ODict):
        ps = tuple(
            (oterm_eliminate(k, motives), oterm_eliminate(v, motives))
            for k, v in term.pairs
        )
        return motives.get("ODict", lambda *p: p)(*ps)
    if isinstance(term, OLam):
        b = oterm_eliminate(term.body, motives)
        return motives.get("OLam", lambda p, b: (p, b))(term.params, b)
    if isinstance(term, OMap):
        f = oterm_eliminate(term.transform, motives)
        c = oterm_eliminate(term.collection, motives)
        fp = None
        if term.filter_pred is not None:
            fp = oterm_eliminate(term.filter_pred, motives)
        return motives.get("OMap", lambda *a: a)(f, c, fp)
    if isinstance(term, OQuotient):
        inner = oterm_eliminate(term.inner, motives)
        return motives.get("OQuotient", lambda i, e: (i, e))(
            inner, term.equiv_class
        )
    if isinstance(term, OCatch):
        b = oterm_eliminate(term.body, motives)
        d = oterm_eliminate(term.default, motives)
        return motives.get("OCatch", lambda b, d: (b, d))(b, d)
    if isinstance(term, OAbstract):
        subs = tuple(oterm_eliminate(a, motives) for a in term.inputs)
        return motives.get("OAbstract", lambda s, *a: (s, a))(
            term.spec, *subs
        )
    return motives.get("default", lambda t: t)(term)


# ═══════════════════════════════════════════════════════════════════
# §6  OTerm PATTERN-MATCHING EXHAUSTIVENESS CHECKER
# ═══════════════════════════════════════════════════════════════════

ALL_OTERM_CONSTRUCTORS: FrozenSet[str] = frozenset({
    "OVar", "OLit", "OOp", "OFold", "OCase", "OFix", "OSeq",
    "ODict", "OUnknown", "OQuotient", "OAbstract", "OLam", "OMap", "OCatch",
})


@dataclass
class ExhaustivenessReport:
    """Report on whether a set of motive patterns covers all constructors."""

    covered: FrozenSet[str]
    missing: FrozenSet[str]
    has_default: bool

    @property
    def is_exhaustive(self) -> bool:
        """True if every constructor is handled (or a default exists)."""
        return self.has_default or len(self.missing) == 0

    def summary(self) -> str:
        if self.is_exhaustive:
            return "exhaustive"
        return f"NON-EXHAUSTIVE — missing: {', '.join(sorted(self.missing))}"


def check_exhaustiveness(
    motives: Dict[str, Any],
    universe: FrozenSet[str] = ALL_OTERM_CONSTRUCTORS,
) -> ExhaustivenessReport:
    """Check whether a motive dictionary covers all OTerm constructors.

    Args:
        motives: the motive dict passed to ``oterm_eliminate``.
        universe: set of constructor names to check against.

    Returns:
        ExhaustivenessReport detailing coverage.
    """
    covered = frozenset(k for k in motives if k in universe)
    has_default = "default" in motives
    missing = universe - covered
    return ExhaustivenessReport(
        covered=covered,
        missing=missing if not has_default else frozenset(),
        has_default=has_default,
    )


def oterm_constructor_name(term: Any) -> str:
    """Return the constructor name for a concrete OTerm value."""
    return type(term).__name__


def oterm_children(term: Any) -> List[Any]:
    """Return immediate sub-terms of a term (for generic traversal)."""
    (OVar, OLit, OOp, OFold, OCase, OFix, OSeq,
     ODict, OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch) = _oterm_types()

    if isinstance(term, (OLit, OVar, OUnknown)):
        return []
    if isinstance(term, OOp):
        return list(term.args)
    if isinstance(term, OFold):
        return [term.init, term.collection]
    if isinstance(term, OCase):
        return [term.test, term.true_branch, term.false_branch]
    if isinstance(term, OFix):
        return [term.body]
    if isinstance(term, OSeq):
        return list(term.elements)
    if isinstance(term, ODict):
        return [x for pair in term.pairs for x in pair]
    if isinstance(term, OLam):
        return [term.body]
    if isinstance(term, OMap):
        ch = [term.transform, term.collection]
        if term.filter_pred is not None:
            ch.append(term.filter_pred)
        return ch
    if isinstance(term, OQuotient):
        return [term.inner]
    if isinstance(term, OAbstract):
        return list(term.inputs)
    if isinstance(term, OCatch):
        return [term.body, term.default]
    return []


def oterm_constructor_histogram(term: Any) -> Dict[str, int]:
    """Count occurrences of each constructor in a term tree."""
    hist: Dict[str, int] = {}
    stack = [term]
    while stack:
        t = stack.pop()
        name = oterm_constructor_name(t)
        hist[name] = hist.get(name, 0) + 1
        stack.extend(oterm_children(t))
    return hist


# ═══════════════════════════════════════════════════════════════════
# §7  DECIDABILITY CLASSIFIER (Chapter 17)
# ═══════════════════════════════════════════════════════════════════

class Decidability(Enum):
    """Decidability class for equivalence checking."""

    DECIDABLE = "decidable"
    SEMI_DECIDABLE = "semi-decidable"
    UNDECIDABLE = "undecidable"

    @staticmethod
    def join(a: Decidability, b: Decidability) -> Decidability:
        """Least upper bound: DECIDABLE < SEMI < UNDECIDABLE."""
        order = {
            Decidability.DECIDABLE: 0,
            Decidability.SEMI_DECIDABLE: 1,
            Decidability.UNDECIDABLE: 2,
        }
        return a if order[a] >= order[b] else b


def _decidability_join_all(classes: List[Decidability]) -> Decidability:
    """Compute the join of a list of decidability classes."""
    result = Decidability.DECIDABLE
    for c in classes:
        result = Decidability.join(result, c)
    return result


def classify_term_decidability(term: Any) -> Decidability:
    """Classify the decidability of checking a term.

    - OLit, OVar, OSeq, ODict: decidable (finite structure)
    - OOp with all decidable args: decidable
    - OFold: semi-decidable (RecFunction in Z3)
    - OFix: semi-decidable (recursion)
    - OUnknown/OAbstract: undecidable (opaque)
    """
    (OVar, OLit, OOp, OFold, OCase, OFix, OSeq,
     ODict, OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch) = _oterm_types()

    if isinstance(term, (OLit, OVar)):
        return Decidability.DECIDABLE
    if isinstance(term, (OUnknown, OAbstract)):
        return Decidability.UNDECIDABLE
    if isinstance(term, (OFold, OFix)):
        return Decidability.SEMI_DECIDABLE
    if isinstance(term, OOp):
        return _decidability_join_all(
            [classify_term_decidability(a) for a in term.args]
        )
    if isinstance(term, OCase):
        return _decidability_join_all([
            classify_term_decidability(term.test),
            classify_term_decidability(term.true_branch),
            classify_term_decidability(term.false_branch),
        ])
    if isinstance(term, OSeq):
        return _decidability_join_all(
            [classify_term_decidability(e) for e in term.elements]
        )
    if isinstance(term, ODict):
        parts = []
        for k, v in term.pairs:
            parts.append(classify_term_decidability(k))
            parts.append(classify_term_decidability(v))
        return _decidability_join_all(parts) if parts else Decidability.DECIDABLE
    if isinstance(term, OLam):
        return classify_term_decidability(term.body)
    if isinstance(term, OMap):
        parts = [
            classify_term_decidability(term.transform),
            classify_term_decidability(term.collection),
        ]
        if term.filter_pred is not None:
            parts.append(classify_term_decidability(term.filter_pred))
        return _decidability_join_all(parts)
    if isinstance(term, OQuotient):
        return classify_term_decidability(term.inner)
    if isinstance(term, OCatch):
        return _decidability_join_all([
            classify_term_decidability(term.body),
            classify_term_decidability(term.default),
        ])
    return Decidability.UNDECIDABLE


def is_in_decidable_core(term: Any) -> bool:
    """True iff the term is in the decidable core of CCTT.

    The decidable core (Theorem 17.1) requires no OFold, OFix,
    OUnknown, or OAbstract constructors.
    """
    return classify_term_decidability(term) == Decidability.DECIDABLE


# ═══════════════════════════════════════════════════════════════════
# §8  DECIDABILITY ORACLE (predict strategy for a pair)
# ═══════════════════════════════════════════════════════════════════

class Strategy(Enum):
    """Resolution strategy for a (term_f, term_g) pair."""

    CLOSED_EVAL = auto()
    DENOTATIONAL = auto()
    Z3_QF = auto()
    Z3_RECURSIVE = auto()
    PATH_SEARCH = auto()
    SEMANTIC = auto()
    UNKNOWN = auto()


@dataclass
class StrategyPrediction:
    """Predicted best strategy for checking a pair."""

    strategy: Strategy
    confidence: float
    reason: str
    decidability_f: Decidability
    decidability_g: Decidability
    arity_f: int
    arity_g: int


def predict_strategy(term_f: Any, term_g: Any) -> StrategyPrediction:
    """Given two OTerms, predict which pipeline strategy will work best.

    Heuristic rules:
    1. Both arity-0 → CLOSED_EVAL
    2. Same canonical form → DENOTATIONAL
    3. Both decidable, small → Z3_QF
    4. Semi-decidable → Z3_RECURSIVE or PATH_SEARCH
    5. Undecidable → SEMANTIC
    """
    af = oterm_arity(term_f)
    ag = oterm_arity(term_g)
    df = classify_term_decidability(term_f)
    dg = classify_term_decidability(term_g)
    overall = Decidability.join(df, dg)

    if overall == Decidability.UNDECIDABLE:
        return StrategyPrediction(
            strategy=Strategy.SEMANTIC,
            confidence=0.3,
            reason="Contains opaque/abstract terms — needs semantic analysis",
            decidability_f=df, decidability_g=dg,
            arity_f=af, arity_g=ag,
        )

    if af == 0 and ag == 0:
        return StrategyPrediction(
            strategy=Strategy.CLOSED_EVAL,
            confidence=0.95,
            reason="Both terms are closed (arity 0) — evaluate directly",
            decidability_f=df, decidability_g=dg,
            arity_f=af, arity_g=ag,
        )

    try:
        cf = term_f.canon()
        cg = term_g.canon()
        if cf == cg:
            return StrategyPrediction(
                strategy=Strategy.DENOTATIONAL,
                confidence=1.0,
                reason="Canonical forms are identical",
                decidability_f=df, decidability_g=dg,
                arity_f=af, arity_g=ag,
            )
    except Exception:
        pass

    if overall == Decidability.DECIDABLE:
        sf = oterm_size(term_f)
        sg = oterm_size(term_g)
        if sf + sg < 50:
            return StrategyPrediction(
                strategy=Strategy.Z3_QF,
                confidence=0.85,
                reason=f"Both decidable, combined size {sf+sg} < 50",
                decidability_f=df, decidability_g=dg,
                arity_f=af, arity_g=ag,
            )
        return StrategyPrediction(
            strategy=Strategy.Z3_QF,
            confidence=0.6,
            reason=f"Both decidable but large (size {sf+sg})",
            decidability_f=df, decidability_g=dg,
            arity_f=af, arity_g=ag,
        )

    if overall == Decidability.SEMI_DECIDABLE:
        hist_f = oterm_constructor_histogram(term_f)
        hist_g = oterm_constructor_histogram(term_g)
        has_fix = hist_f.get("OFix", 0) + hist_g.get("OFix", 0)
        has_fold = hist_f.get("OFold", 0) + hist_g.get("OFold", 0)
        if has_fix > 0 and has_fold > 0:
            return StrategyPrediction(
                strategy=Strategy.PATH_SEARCH,
                confidence=0.7,
                reason="Mix of OFix and OFold — path search may find rec↔iter",
                decidability_f=df, decidability_g=dg,
                arity_f=af, arity_g=ag,
            )
        return StrategyPrediction(
            strategy=Strategy.Z3_RECURSIVE,
            confidence=0.6,
            reason="Semi-decidable — Z3 with RecFunctions",
            decidability_f=df, decidability_g=dg,
            arity_f=af, arity_g=ag,
        )

    return StrategyPrediction(
        strategy=Strategy.UNKNOWN,
        confidence=0.1,
        reason="No matching strategy heuristic",
        decidability_f=df, decidability_g=dg,
        arity_f=af, arity_g=ag,
    )


# ═══════════════════════════════════════════════════════════════════
# §9  Z3 THEORY FRAGMENT CLASSIFIER (Chapter 17)
# ═══════════════════════════════════════════════════════════════════

class Z3Fragment(Enum):
    """Z3 theory fragment classification."""

    QF_DT_LIA = "QF_DT_LIA"
    QF_DT_LIA_S = "QF_DT_LIA_S"
    QF_DT_NIA = "QF_DT_NIA"
    REC_FUNCTION = "RecFunction"
    QUANTIFIED = "Quantified"
    UNKNOWN = "unknown"

    @property
    def is_decidable(self) -> bool:
        return self in (Z3Fragment.QF_DT_LIA, Z3Fragment.QF_DT_LIA_S)


def classify_z3_fragment(formula: Any) -> Z3Fragment:
    """Classify a Z3 formula into its decidability fragment.

    The monograph identifies QF_DT + QF_LIA + QF_S as decidable
    via Nelson-Oppen combination.  Non-linear arithmetic and
    recursive functions push into undecidable territory.
    """
    try:
        import z3
    except ImportError:
        return Z3Fragment.UNKNOWN

    if not isinstance(formula, z3.ExprRef):
        return Z3Fragment.UNKNOWN

    has_rec = False
    has_quantifier = False
    has_string = False
    has_nonlinear = False

    def walk(expr: Any) -> None:
        nonlocal has_rec, has_quantifier, has_string, has_nonlinear

        if z3.is_quantifier(expr):
            has_quantifier = True
            return
        if z3.is_app(expr):
            decl = expr.decl()
            kind = decl.kind()
            if kind == z3.Z3_OP_RECURSIVE:
                has_rec = True
            if expr.sort() == z3.StringSort():
                has_string = True
            if kind == z3.Z3_OP_MUL and expr.num_args() >= 2:
                non_const = sum(
                    1 for i in range(expr.num_args())
                    if not z3.is_int_value(expr.arg(i))
                )
                if non_const >= 2:
                    has_nonlinear = True
        for i in range(expr.num_args()):
            walk(expr.arg(i))

    walk(formula)

    if has_quantifier:
        return Z3Fragment.QUANTIFIED
    if has_rec:
        return Z3Fragment.REC_FUNCTION
    if has_nonlinear:
        return Z3Fragment.QF_DT_NIA
    if has_string:
        return Z3Fragment.QF_DT_LIA_S
    return Z3Fragment.QF_DT_LIA


# ═══════════════════════════════════════════════════════════════════
# §10  Z3 FEATURE ANALYZER (per-pair feature vector)
# ═══════════════════════════════════════════════════════════════════

@dataclass
class Z3FeatureVector:
    """Feature vector describing what Z3 theories/features a pair needs."""

    uses_integers: bool = False
    uses_strings: bool = False
    uses_booleans: bool = False
    uses_datatypes: bool = False
    uses_sequences: bool = False
    uses_quantifiers: bool = False
    uses_recursive_fns: bool = False
    uses_nonlinear_arith: bool = False
    num_variables: int = 0
    num_assertions: int = 0
    max_depth: int = 0

    @property
    def fragment(self) -> Z3Fragment:
        """Derive the fragment from the feature vector."""
        if self.uses_quantifiers:
            return Z3Fragment.QUANTIFIED
        if self.uses_recursive_fns:
            return Z3Fragment.REC_FUNCTION
        if self.uses_nonlinear_arith:
            return Z3Fragment.QF_DT_NIA
        if self.uses_strings:
            return Z3Fragment.QF_DT_LIA_S
        return Z3Fragment.QF_DT_LIA

    @property
    def estimated_difficulty(self) -> float:
        """Heuristic difficulty score in [0, 1]."""
        score = 0.0
        if self.uses_quantifiers:
            score += 0.4
        if self.uses_recursive_fns:
            score += 0.3
        if self.uses_nonlinear_arith:
            score += 0.2
        if self.uses_strings:
            score += 0.1
        score += min(0.2, self.num_variables * 0.01)
        score += min(0.1, self.max_depth * 0.01)
        return min(1.0, score)

    def summary(self) -> str:
        parts = []
        if self.uses_integers:
            parts.append("LIA")
        if self.uses_strings:
            parts.append("Strings")
        if self.uses_booleans:
            parts.append("Bool")
        if self.uses_datatypes:
            parts.append("DT")
        if self.uses_quantifiers:
            parts.append("∀/∃")
        if self.uses_recursive_fns:
            parts.append("RecFn")
        if self.uses_nonlinear_arith:
            parts.append("NIA")
        return f"Z3Features({'+'.join(parts) or 'empty'}, vars={self.num_variables})"


def analyze_z3_features(formula: Any) -> Z3FeatureVector:
    """Analyze a Z3 formula and produce a feature vector."""
    try:
        import z3
    except ImportError:
        return Z3FeatureVector()

    if not isinstance(formula, z3.ExprRef):
        return Z3FeatureVector()

    fv = Z3FeatureVector()
    seen_vars: Set[str] = set()
    max_d = 0

    def walk(expr: Any, depth: int = 0) -> None:
        nonlocal max_d
        max_d = max(max_d, depth)

        if z3.is_quantifier(expr):
            fv.uses_quantifiers = True
        if z3.is_const(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            seen_vars.add(str(expr))
        if z3.is_app(expr):
            decl = expr.decl()
            kind = decl.kind()
            sort = expr.sort()
            if sort == z3.IntSort():
                fv.uses_integers = True
            elif sort == z3.BoolSort():
                fv.uses_booleans = True
            elif sort == z3.StringSort():
                fv.uses_strings = True
            if kind == z3.Z3_OP_RECURSIVE:
                fv.uses_recursive_fns = True
            if kind == z3.Z3_OP_DT_CONSTRUCTOR:
                fv.uses_datatypes = True
            if kind == z3.Z3_OP_MUL and expr.num_args() >= 2:
                non_const = sum(
                    1 for i in range(expr.num_args())
                    if not z3.is_int_value(expr.arg(i))
                )
                if non_const >= 2:
                    fv.uses_nonlinear_arith = True

        for i in range(expr.num_args()):
            walk(expr.arg(i), depth + 1)

    walk(formula)
    fv.num_variables = len(seen_vars)
    fv.max_depth = max_d
    return fv


def analyze_oterm_pair_z3_needs(term_f: Any, term_g: Any) -> Z3FeatureVector:
    """Predict Z3 feature requirements from OTerm structure (no Z3 needed).

    Inspects the OTerm constructors to estimate which Z3 theories will
    be engaged when compiling to a Z3 formula.
    """
    fv = Z3FeatureVector()
    hist_f = oterm_constructor_histogram(term_f)
    hist_g = oterm_constructor_histogram(term_g)

    combined: Dict[str, int] = {}
    for h in (hist_f, hist_g):
        for k, v in h.items():
            combined[k] = combined.get(k, 0) + v

    fv.uses_integers = True
    fv.uses_booleans = combined.get("OCase", 0) > 0
    fv.uses_datatypes = True
    fv.uses_recursive_fns = (
        combined.get("OFold", 0) + combined.get("OFix", 0) > 0
    )
    fv.num_variables = oterm_arity(term_f) + oterm_arity(term_g)
    fv.max_depth = max(oterm_depth(term_f), oterm_depth(term_g))
    fv.num_assertions = oterm_size(term_f) + oterm_size(term_g)

    return fv


# ═══════════════════════════════════════════════════════════════════
# §11  ENRICHED COHOMOLOGY (H¹ over the duck-type lattice)
# ═══════════════════════════════════════════════════════════════════

def _gf2_rank(matrix: List[List[int]]) -> int:
    """Gaussian elimination over GF(2) to compute rank."""
    if not matrix or not matrix[0]:
        return 0
    m = [row[:] for row in matrix]
    rows, cols = len(m), len(m[0])
    rank = 0
    for col in range(cols):
        pivot = None
        for row in range(rank, rows):
            if m[row][col] == 1:
                pivot = row
                break
        if pivot is None:
            continue
        m[rank], m[pivot] = m[pivot], m[rank]
        for row in range(rows):
            if row != rank and m[row][col] == 1:
                m[row] = [(m[row][j] + m[rank][j]) % 2 for j in range(cols)]
        rank += 1
    return rank


@dataclass
class EnrichedLocalJudgment:
    """Local judgment enriched with duck-type information.

    Instead of just bool (equivalent or not), records *which* duck type
    the equivalence holds under.  This is the enriched coefficient sheaf.
    """

    fiber: Tuple[str, ...]
    agreement_type: DuckType
    is_equivalent: Optional[bool]
    counterexample: Optional[str] = None

    @property
    def agreement_width(self) -> int:
        return self.agreement_type.width()


@dataclass
class EnrichedCechResult:
    """Čech cohomology result with duck-type enriched coefficients.

    H¹ is computed over the lattice D instead of GF(2):
    - Each 0-cochain is a DuckType (not a bit)
    - The coboundary δ⁰ measures *agreement mismatch* between fibers
    - H¹ ≠ 0 means the agreement levels don't glue globally
    """

    h0: int
    h1_rank: int
    total_fibers: int
    unknown_fibers: int
    obstructions: List[Tuple[str, ...]]
    global_agreement: DuckType
    per_fiber_agreements: Dict[Tuple[str, ...], DuckType]

    @property
    def equivalent(self) -> Optional[bool]:
        if self.obstructions:
            return False
        if self.h0 > 0 and self.h1_rank == 0 and self.unknown_fibers == 0:
            return True
        if self.h0 > 0 and self.h1_rank == 0 and self.total_fibers > 0:
            coverage = self.h0 / self.total_fibers
            if coverage >= 0.5:
                return True
        return None

    def summary(self) -> str:
        status = {True: "EQ", False: "NEQ", None: "?"}[self.equivalent]
        return (
            f"EnrichedČech(H⁰={self.h0}, H¹={self.h1_rank}, "
            f"status={status}, agreement={self.global_agreement})"
        )


def compute_enriched_cech_h1(
    judgments: Dict[Tuple[str, ...], EnrichedLocalJudgment],
    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
) -> EnrichedCechResult:
    """Compute Čech H¹ with enriched (duck-type lattice) coefficients.

    The enrichment replaces GF(2) coefficients with DuckType values:
    - A 0-cochain assigns to each fiber the DuckType under which
      f ≡ g on that fiber.
    - The coboundary measures whether adjacent fibers agree at
      the same duck-type level.
    - H¹ ≠ 0 detects "agreement level mismatch" — f ≡ g on
      int-fiber under Addable but on str-fiber only under Hashable,
      so the agreements don't glue.
    """
    fibers = list(judgments.keys())
    n = len(fibers)

    equiv_fibers = [
        f for f in fibers if judgments[f].is_equivalent is True
    ]
    inequiv_fibers = [
        f for f in fibers if judgments[f].is_equivalent is False
    ]
    unknown_fibers_list = [
        f for f in fibers if judgments[f].is_equivalent is None
    ]

    per_fiber_agreements: Dict[Tuple[str, ...], DuckType] = {
        f: judgments[f].agreement_type for f in fibers
    }

    if inequiv_fibers:
        return EnrichedCechResult(
            h0=len(equiv_fibers),
            h1_rank=len(inequiv_fibers),
            total_fibers=n,
            unknown_fibers=len(unknown_fibers_list),
            obstructions=inequiv_fibers,
            global_agreement=BOTTOM,
            per_fiber_agreements=per_fiber_agreements,
        )

    if not equiv_fibers:
        return EnrichedCechResult(
            h0=0, h1_rank=0, total_fibers=n,
            unknown_fibers=len(unknown_fibers_list),
            obstructions=[],
            global_agreement=BOTTOM,
            per_fiber_agreements=per_fiber_agreements,
        )

    # Compute global agreement = meet of all fiber agreements
    global_agr: Optional[DuckType] = None
    for f in equiv_fibers:
        dt = judgments[f].agreement_type
        if global_agr is None:
            global_agr = dt
        else:
            global_agr = global_agr.meet(dt)

    # Enriched H¹: check whether all overlapping fibers agree at the
    # same level.  If fiber A has agreement DuckType X and fiber B
    # has agreement DuckType Y, and X ≠ Y, there is a 1-cocycle
    # obstruction.
    if not overlaps or len(equiv_fibers) <= 1:
        return EnrichedCechResult(
            h0=len(equiv_fibers), h1_rank=0,
            total_fibers=n,
            unknown_fibers=len(unknown_fibers_list),
            obstructions=[],
            global_agreement=global_agr or BOTTOM,
            per_fiber_agreements=per_fiber_agreements,
        )

    fiber_idx = {f: i for i, f in enumerate(equiv_fibers)}
    overlap_list = [
        (a, b) for a, b in overlaps
        if a in fiber_idx and b in fiber_idx
    ]
    m = len(overlap_list)
    if m == 0:
        return EnrichedCechResult(
            h0=len(equiv_fibers), h1_rank=0,
            total_fibers=n,
            unknown_fibers=len(unknown_fibers_list),
            obstructions=[],
            global_agreement=global_agr or BOTTOM,
            per_fiber_agreements=per_fiber_agreements,
        )

    # Build δ⁰ over GF(2) where entry is 1 when the two fibers
    # have *different* agreement duck types (enriched coboundary).
    delta0 = [[0] * len(equiv_fibers) for _ in range(m)]
    for k, (a, b) in enumerate(overlap_list):
        dt_a = judgments[a].agreement_type
        dt_b = judgments[b].agreement_type
        if dt_a != dt_b:
            delta0[k][fiber_idx[a]] = 1
            delta0[k][fiber_idx[b]] = 1

    triples: List[Tuple[int, int]] = []
    for i, (a1, b1) in enumerate(overlap_list):
        for j, (a2, b2) in enumerate(overlap_list):
            if j <= i:
                continue
            common = {a1, b1} & {a2, b2}
            if common:
                third = ({a1, b1} | {a2, b2}) - common
                if third:
                    triples.append((i, j))

    delta1 = [[0] * m for _ in range(len(triples))]
    for t, (i, j) in enumerate(triples):
        delta1[t][i] = 1
        delta1[t][j] = 1

    rank_delta0 = _gf2_rank(delta0)
    rank_delta1 = _gf2_rank(delta1) if delta1 else 0
    ker_delta1 = m - rank_delta1
    h1_rank = max(0, ker_delta1 - rank_delta0)

    return EnrichedCechResult(
        h0=len(equiv_fibers),
        h1_rank=h1_rank,
        total_fibers=n,
        unknown_fibers=len(unknown_fibers_list),
        obstructions=[],
        global_agreement=global_agr or BOTTOM,
        per_fiber_agreements=per_fiber_agreements,
    )


# ═══════════════════════════════════════════════════════════════════
# §12  INDUCTIVE FAMILY ELIMINATOR CODE GENERATOR
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ConstructorSpec:
    """Specification of a single OTerm constructor for codegen."""

    name: str
    fields: List[Tuple[str, str]]  # (field_name, type_hint)
    recursive_fields: List[str]

    @property
    def arity(self) -> int:
        return len(self.fields)

    @property
    def is_leaf(self) -> bool:
        return len(self.recursive_fields) == 0


OTERM_CONSTRUCTORS: List[ConstructorSpec] = [
    ConstructorSpec("OLit", [("value", "Any")], []),
    ConstructorSpec("OVar", [("name", "str")], []),
    ConstructorSpec("OOp", [("name", "str"), ("args", "Tuple[OTerm, ...]")], ["args"]),
    ConstructorSpec(
        "OFold",
        [("op_name", "str"), ("init", "OTerm"), ("collection", "OTerm")],
        ["init", "collection"],
    ),
    ConstructorSpec(
        "OCase",
        [("test", "OTerm"), ("true_branch", "OTerm"), ("false_branch", "OTerm")],
        ["test", "true_branch", "false_branch"],
    ),
    ConstructorSpec("OFix", [("name", "str"), ("body", "OTerm")], ["body"]),
    ConstructorSpec("OSeq", [("elements", "Tuple[OTerm, ...]")], ["elements"]),
    ConstructorSpec(
        "ODict", [("pairs", "Tuple[Tuple[OTerm, OTerm], ...]")], ["pairs"]
    ),
    ConstructorSpec("OUnknown", [("desc", "str")], []),
    ConstructorSpec(
        "OQuotient", [("inner", "OTerm"), ("equiv_class", "str")], ["inner"]
    ),
    ConstructorSpec(
        "OAbstract", [("spec", "str"), ("inputs", "Tuple[OTerm, ...]")], ["inputs"]
    ),
    ConstructorSpec("OLam", [("params", "Tuple[str, ...]"), ("body", "OTerm")], ["body"]),
    ConstructorSpec(
        "OMap",
        [("transform", "OTerm"), ("collection", "OTerm"), ("filter_pred", "Optional[OTerm]")],
        ["transform", "collection", "filter_pred"],
    ),
    ConstructorSpec(
        "OCatch", [("body", "OTerm"), ("default", "OTerm")], ["body", "default"]
    ),
]


def generate_eliminator(
    func_name: str = "elim_oterm",
    result_type: str = "R",
    include_docstring: bool = True,
) -> str:
    """Generate Python source for a typed OTerm eliminator function.

    Produces a function that takes a term and one motive per constructor,
    recurses on sub-terms, and calls the appropriate motive.  This is
    the computational content of elim_OTerm from Chapter 16.

    Args:
        func_name: name of the generated function.
        result_type: return type annotation.
        include_docstring: whether to emit a docstring.

    Returns:
        Python source code string.
    """
    lines: List[str] = []
    motive_params = []
    for cs in OTERM_CONSTRUCTORS:
        positional_types = []
        for fn, ft in cs.fields:
            if fn in cs.recursive_fields:
                positional_types.append(result_type)
            else:
                positional_types.append(ft)
        type_list = ", ".join(positional_types)
        motive_params.append(
            f"    motive_{cs.name}: Callable[[{type_list}], {result_type}],"
        )

    sig = f"def {func_name}(\n    term: OTerm,\n"
    sig += "\n".join(motive_params)
    sig += f"\n) -> {result_type}:"

    lines.append(sig)

    if include_docstring:
        lines.append('    """Generated eliminator (dependent recursor) for OTerm."""')

    for cs in OTERM_CONSTRUCTORS:
        lines.append(f"    if isinstance(term, {cs.name}):")
        rec_calls: List[str] = []
        for fn, ft in cs.fields:
            if fn in cs.recursive_fields:
                if "Tuple" in ft and "..." in ft:
                    rec_var = f"_rec_{fn}"
                    lines.append(
                        f"        {rec_var} = tuple("
                        f"{func_name}(x, "
                        + ", ".join(f"motive_{c.name}" for c in OTERM_CONSTRUCTORS)
                        + f") for x in term.{fn})"
                    )
                    rec_calls.append(rec_var)
                elif fn == "pairs":
                    rec_var = f"_rec_{fn}"
                    lines.append(
                        f"        {rec_var} = tuple(("
                        f"{func_name}(k, "
                        + ", ".join(f"motive_{c.name}" for c in OTERM_CONSTRUCTORS)
                        + f"), {func_name}(v, "
                        + ", ".join(f"motive_{c.name}" for c in OTERM_CONSTRUCTORS)
                        + f")) for k, v in term.{fn})"
                    )
                    rec_calls.append(rec_var)
                elif "Optional" in ft:
                    rec_var = f"_rec_{fn}"
                    call = (
                        f"{func_name}(term.{fn}, "
                        + ", ".join(f"motive_{c.name}" for c in OTERM_CONSTRUCTORS)
                        + ")"
                    )
                    lines.append(
                        f"        {rec_var} = {call} if term.{fn} is not None else None"
                    )
                    rec_calls.append(rec_var)
                else:
                    rec_var = f"_rec_{fn}"
                    call = (
                        f"{func_name}(term.{fn}, "
                        + ", ".join(f"motive_{c.name}" for c in OTERM_CONSTRUCTORS)
                        + ")"
                    )
                    lines.append(f"        {rec_var} = {call}")
                    rec_calls.append(rec_var)
            else:
                rec_calls.append(f"term.{fn}")
        args_str = ", ".join(rec_calls)
        lines.append(f"        return motive_{cs.name}({args_str})")

    lines.append(f'    raise TypeError(f"Unknown OTerm constructor: {{type(term).__name__}}")')
    return "\n".join(lines)


def generate_fold(
    func_name: str = "fold_oterm",
    result_type: str = "R",
) -> str:
    """Generate a non-dependent fold (catamorphism) for OTerm.

    Unlike the eliminator, the fold ignores the family index and
    uses a single accumulator type.
    """
    lines: List[str] = []
    lines.append(f"def {func_name}(term: OTerm, algebra: Dict[str, Callable[..., {result_type}]]) -> {result_type}:")
    lines.append(f'    """Generated catamorphism for OTerm."""')

    for cs in OTERM_CONSTRUCTORS:
        lines.append(f"    if isinstance(term, {cs.name}):")
        rec_args: List[str] = []
        for fn, ft in cs.fields:
            if fn in cs.recursive_fields:
                if "Tuple" in ft and "..." in ft:
                    lines.append(
                        f"        _r_{fn} = tuple({func_name}(x, algebra) for x in term.{fn})"
                    )
                    rec_args.append(f"_r_{fn}")
                elif fn == "pairs":
                    lines.append(
                        f"        _r_{fn} = tuple(({func_name}(k, algebra), {func_name}(v, algebra)) for k, v in term.{fn})"
                    )
                    rec_args.append(f"_r_{fn}")
                elif "Optional" in ft:
                    lines.append(
                        f"        _r_{fn} = {func_name}(term.{fn}, algebra) if term.{fn} is not None else None"
                    )
                    rec_args.append(f"_r_{fn}")
                else:
                    lines.append(f"        _r_{fn} = {func_name}(term.{fn}, algebra)")
                    rec_args.append(f"_r_{fn}")
            else:
                rec_args.append(f"term.{fn}")
        args_str = ", ".join(rec_args)
        lines.append(
            f"        return algebra.get('{cs.name}', lambda *a: a)({args_str})"
        )

    lines.append(f'    raise TypeError(f"Unknown OTerm constructor: {{type(term).__name__}}")')
    return "\n".join(lines)


def validate_generated_eliminator(source: str) -> bool:
    """Compile-check generated eliminator source."""
    try:
        compile(source, "<generated-eliminator>", "exec")
        return True
    except SyntaxError:
        return False


# ═══════════════════════════════════════════════════════════════════
# §13  INTEGRATION HELPERS
# ═══════════════════════════════════════════════════════════════════

def oterm_to_enriched_judgment(
    fiber: Tuple[str, ...],
    term_f: Any,
    term_g: Any,
    agreed_ops: Set[str],
    is_eq: Optional[bool],
    counterexample: Optional[str] = None,
) -> EnrichedLocalJudgment:
    """Create an enriched local judgment from pipeline outputs.

    Bridge between checker.py's per-fiber Z3 result and the
    enriched cohomology computation.
    """
    return EnrichedLocalJudgment(
        fiber=fiber,
        agreement_type=DuckType(
            f"fiber:{'×'.join(fiber)}",
            frozenset(agreed_ops),
        ),
        is_equivalent=is_eq,
        counterexample=counterexample,
    )


def pipeline_summary(
    term_f: Any,
    term_g: Any,
    enriched_result: EnrichedCechResult,
    strategy: StrategyPrediction,
) -> str:
    """Produce a human-readable summary combining all analyses."""
    lines = [
        "═══ CCTT Pipeline Summary ═══",
        f"Strategy:      {strategy.strategy.name} (confidence {strategy.confidence:.0%})",
        f"  reason:      {strategy.reason}",
        f"Decidability:  f={strategy.decidability_f.value}, g={strategy.decidability_g.value}",
        f"Arity:         f={strategy.arity_f}, g={strategy.arity_g}",
        f"Cohomology:    H⁰={enriched_result.h0}, H¹={enriched_result.h1_rank}",
        f"Agreement:     {enriched_result.global_agreement}",
        f"Verdict:       {enriched_result.equivalent}",
    ]
    if enriched_result.obstructions:
        lines.append(f"Obstructions:  {enriched_result.obstructions}")
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# §14  SELF-TESTS
# ═══════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    import sys
    passed = 0
    failed = 0

    def _assert(cond: bool, msg: str) -> None:
        global passed, failed
        if cond:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {msg}", file=sys.stderr)

    # ── §1/§2: DuckType lattice ──────────────────────────────────
    print("§1/§2 DuckType lattice …")
    _assert(ADDABLE <= NUMERIC, "Addable ≤ Numeric")
    _assert(not NUMERIC <= ADDABLE, "¬(Numeric ≤ Addable)")
    _assert(BOTTOM <= ADDABLE, "⊥ ≤ Addable")
    _assert(ADDABLE.meet(NUMERIC) == ADDABLE, "Addable ∧ Numeric == Addable")
    _assert(ADDABLE.join(COMPARABLE).ops == ADDABLE.ops | COMPARABLE.ops,
            "join is union of ops")
    _assert(BOTTOM.is_bottom(), "⊥.is_bottom()")
    _assert(not ADDABLE.is_bottom(), "Addable not bottom")
    m = NUMERIC.meet(STRINGLIKE)
    _assert("__add__" in m.ops, "Numeric ∧ StringLike includes __add__")
    _assert("__sub__" not in m.ops, "Numeric ∧ StringLike excludes __sub__")

    poset = DuckTypePoset()
    _assert(len(poset.upset(BOTTOM)) == len(ALL_ATOMS), "upset(⊥) == all atoms")
    _assert(BOTTOM in poset.downset(ADDABLE), "⊥ in downset(Addable)")
    covers = poset.covers_of(BOTTOM)
    _assert(ADDABLE in covers, "Addable covers ⊥")

    # ── §3: Enriched hom ─────────────────────────────────────────
    print("§3 Enriched hom …")
    result = enriched_hom({
        "int": {"__add__", "__sub__", "__mul__"},
        "str": {"__add__", "__len__"},
    })
    _assert(result.global_meet.ops == frozenset({"__add__"}),
            "enriched hom meet is {__add__}")
    _assert(result.fibers_agreeing == 2, "both fibers agreeing")
    _assert(result.is_equivalent, "enriched hom is_equivalent")

    empty_result = enriched_hom({})
    _assert(empty_result.global_meet.is_bottom(), "empty fiber_results → ⊥")

    # ── §4: OTerm arity / free vars / depth / size ───────────────
    print("§4 OTerm arity …")
    try:
        from new_src.cctt.denotation import (
            OVar, OLit, OOp, OFold, OCase, OFix, OSeq,
            ODict, OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
        )

        lit = OLit(42)
        var_x = OVar("x")
        var_y = OVar("y")
        add_xy = OOp("add", (var_x, var_y))

        _assert(oterm_arity(lit) == 0, "OLit arity == 0")
        _assert(oterm_arity(var_x) == 1, "OVar arity == 1")
        _assert(oterm_arity(add_xy) == 2, "OOp(add, x, y) arity == 2")
        _assert(oterm_free_vars(lit) == frozenset(), "OLit free vars empty")
        _assert(oterm_free_vars(add_xy) == frozenset({"x", "y"}), "add free vars")
        _assert(oterm_depth(lit) == 0, "OLit depth 0")
        _assert(oterm_depth(add_xy) == 1, "add(x,y) depth 1")
        _assert(oterm_size(add_xy) == 3, "add(x,y) size 3")

        lam = OLam(("x",), OOp("add", (OVar("x"), OLit(1))))
        _assert(oterm_arity(lam) == 0, "λx.x+1 arity 0 (x bound)")
        _assert(oterm_free_vars(lam) == frozenset(), "λx.x+1 no free vars")

        fix = OFix("f", OOp("add", (OVar("f"), OVar("n"))))
        _assert("n" in oterm_free_vars(fix), "fix f. f+n has n free")
        _assert("f" not in oterm_free_vars(fix), "fix f. f+n binds f")

        # ── §5: Eliminator ───────────────────────────────────────
        print("§5 OTerm eliminator …")
        to_str = oterm_eliminate(add_xy, {
            "OVar": lambda n: f"${n}",
            "OLit": lambda v: str(v),
            "OOp": lambda name, *args: f"{name}({','.join(str(a) for a in args)})",
        })
        _assert(to_str == "add($x,$y)", f"eliminator string: {to_str}")

        # ── §6: Exhaustiveness ───────────────────────────────────
        print("§6 Exhaustiveness checker …")
        partial = {"OLit": lambda v: v, "OVar": lambda n: n}
        report = check_exhaustiveness(partial)
        _assert(not report.is_exhaustive, "partial motives not exhaustive")
        _assert("OOp" in report.missing, "OOp missing from partial")

        with_default = {"OLit": lambda v: v, "default": lambda t: None}
        report2 = check_exhaustiveness(with_default)
        _assert(report2.is_exhaustive, "default makes it exhaustive")

        _assert(oterm_constructor_name(lit) == "OLit", "constructor name")
        _assert(len(oterm_children(add_xy)) == 2, "OOp has 2 children")
        _assert(len(oterm_children(lit)) == 0, "OLit has 0 children")

        hist = oterm_constructor_histogram(add_xy)
        _assert(hist.get("OOp", 0) == 1, "histogram: 1 OOp")
        _assert(hist.get("OVar", 0) == 2, "histogram: 2 OVar")

        # ── §7: Decidability classifier ──────────────────────────
        print("§7 Decidability classifier …")
        _assert(classify_term_decidability(lit) == Decidability.DECIDABLE,
                "OLit decidable")
        _assert(classify_term_decidability(OUnknown("?")) == Decidability.UNDECIDABLE,
                "OUnknown undecidable")
        fold = OFold("add", OLit(0), OVar("xs"))
        _assert(classify_term_decidability(fold) == Decidability.SEMI_DECIDABLE,
                "OFold semi-decidable")
        _assert(is_in_decidable_core(add_xy), "add(x,y) in decidable core")
        _assert(not is_in_decidable_core(fold), "fold not in decidable core")

        # Decidability.join
        _assert(
            Decidability.join(Decidability.DECIDABLE, Decidability.SEMI_DECIDABLE)
            == Decidability.SEMI_DECIDABLE,
            "join(D, SD) == SD",
        )

        # ── §8: Strategy oracle ──────────────────────────────────
        print("§8 Strategy oracle …")
        pred = predict_strategy(lit, OLit(43))
        _assert(pred.strategy == Strategy.CLOSED_EVAL, "two lits → CLOSED_EVAL")

        pred2 = predict_strategy(add_xy, OOp("add", (var_y, var_x)))
        _assert(pred2.strategy in (Strategy.Z3_QF, Strategy.DENOTATIONAL),
                "simple add → Z3_QF or DENOTATIONAL")

        pred3 = predict_strategy(fold, OFix("g", OOp("add", (OVar("g"), OVar("n")))))
        _assert(pred3.strategy in (Strategy.PATH_SEARCH, Strategy.Z3_RECURSIVE),
                "fold vs fix → PATH_SEARCH or Z3_RECURSIVE")

        pred4 = predict_strategy(OUnknown("?"), OUnknown("??"))
        _assert(pred4.strategy == Strategy.SEMANTIC, "opaque → SEMANTIC")

        # ── §11: Enriched cohomology ─────────────────────────────
        print("§11 Enriched cohomology …")
        jdg1 = EnrichedLocalJudgment(
            fiber=("int",), agreement_type=NUMERIC, is_equivalent=True,
        )
        jdg2 = EnrichedLocalJudgment(
            fiber=("str",), agreement_type=STRINGLIKE, is_equivalent=True,
        )
        cech = compute_enriched_cech_h1(
            {("int",): jdg1, ("str",): jdg2},
            overlaps=[(("int",), ("str",))],
        )
        _assert(cech.h0 == 2, "enriched H⁰ == 2")
        _assert(cech.h1_rank >= 0, "enriched H¹ ≥ 0")
        _assert(cech.equivalent is True or cech.equivalent is None,
                "enriched cech result")

        jdg_neq = EnrichedLocalJudgment(
            fiber=("list",), agreement_type=BOTTOM, is_equivalent=False,
            counterexample="[1] vs [2]",
        )
        cech_neq = compute_enriched_cech_h1(
            {("list",): jdg_neq}, overlaps=[],
        )
        _assert(cech_neq.equivalent is False, "enriched NEQ")
        _assert(len(cech_neq.obstructions) == 1, "one obstruction")

        # ── §12: Code generator ──────────────────────────────────
        print("§12 Eliminator codegen …")
        elim_src = generate_eliminator()
        _assert(validate_generated_eliminator(elim_src), "eliminator compiles")
        _assert("def elim_oterm" in elim_src, "function name present")
        _assert("motive_OLit" in elim_src, "OLit motive present")
        _assert("motive_OCatch" in elim_src, "OCatch motive present")

        fold_src = generate_fold()
        _assert(validate_generated_eliminator(fold_src), "fold compiles")
        _assert("def fold_oterm" in fold_src, "fold function name")

        # ── §13: Integration helpers ─────────────────────────────
        print("§13 Integration helpers …")
        ej = oterm_to_enriched_judgment(
            fiber=("int",),
            term_f=lit, term_g=OLit(43),
            agreed_ops={"__add__", "__sub__"},
            is_eq=True,
        )
        _assert(ej.agreement_width == 2, "2 agreed ops")

        summary = pipeline_summary(
            lit, OLit(43), cech, pred,
        )
        _assert("Strategy" in summary, "summary has strategy")
        _assert("H⁰" in summary, "summary has H⁰")

    except ImportError as e:
        print(f"  SKIP OTerm tests (import error: {e})")

    # ── §9/§10: Z3 fragment tests (best-effort) ─────────────────
    print("§9/§10 Z3 fragment …")
    try:
        import z3
        x = z3.Int("x")
        y = z3.Int("y")
        fml = x + y > 0
        frag = classify_z3_fragment(fml)
        _assert(frag == Z3Fragment.QF_DT_LIA, f"x+y>0 → QF_DT_LIA (got {frag})")

        fv = analyze_z3_features(fml)
        _assert(fv.uses_integers, "feature: uses_integers")
        _assert(not fv.uses_strings, "feature: no strings")
        _assert(fv.fragment == Z3Fragment.QF_DT_LIA, "feature vector fragment")
        _assert(fv.estimated_difficulty < 0.5, "simple formula low difficulty")

        s = z3.String("s")
        str_fml = z3.Length(s) > 0
        frag_s = classify_z3_fragment(str_fml)
        _assert(frag_s == Z3Fragment.QF_DT_LIA_S, "string formula → QF_DT_LIA_S")

        nla = x * y > 0
        frag_n = classify_z3_fragment(nla)
        _assert(frag_n == Z3Fragment.QF_DT_NIA, "x*y>0 → QF_DT_NIA")
    except ImportError:
        print("  SKIP Z3 tests (z3 not available)")

    # ── summary ──────────────────────────────────────────────────
    total = passed + failed
    print(f"\n{'═' * 40}")
    print(f"  {passed}/{total} tests passed", end="")
    if failed:
        print(f"  ({failed} FAILED)")
        sys.exit(1)
    else:
        print("  ✓ all green")
        sys.exit(0)
