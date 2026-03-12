"""Generate loop invariant candidates.

InvariantCandidateGenerator uses templates and section data to propose
loop invariants.  These candidates can then be checked by the verification
backend (SMT solver or abstract interpreter).

The generator combines:
1. Template-based invariants (common patterns like monotonicity, bounds).
2. Section-based invariants (derived from the type information at loop sites).
3. Relational invariants (relationships between loop variables).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.types.base import (
    ANY_TYPE,
    AnyType,
    ListType,
    NeverType,
    PrimitiveKind,
    PrimitiveType,
    TypeBase,
)
from deppy.types.refinement import (
    ComparisonOp,
    ComparisonPred,
    ConjunctionPred,
    LengthPred,
    Predicate,
    RefinementType,
    TruePred,
)


# ---------------------------------------------------------------------------
# Invariant candidate data
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class InvariantCandidate:
    """A candidate loop invariant.

    Attributes:
        expression: The invariant as a predicate expression string.
        predicate: The structured predicate object.
        variables: Variables referenced by this invariant.
        source: How this candidate was generated ('template', 'section', 'relational').
        confidence: Confidence that this invariant holds (0..1).
        loop_site: The loop site this invariant applies to.
        is_inductive: Whether this has been verified to be inductive.
    """

    _expression: str
    _predicate: Optional[Predicate] = None
    _variables: FrozenSet[str] = field(default_factory=frozenset)
    _source: str = "template"
    _confidence: float = 0.5
    _loop_site: Optional[SiteId] = None
    _is_inductive: bool = False

    @property
    def expression(self) -> str:
        return self._expression

    @property
    def predicate(self) -> Optional[Predicate]:
        return self._predicate

    @property
    def variables(self) -> FrozenSet[str]:
        return self._variables

    @property
    def source(self) -> str:
        return self._source

    @property
    def confidence(self) -> float:
        return self._confidence

    @property
    def loop_site(self) -> Optional[SiteId]:
        return self._loop_site

    @property
    def is_inductive(self) -> bool:
        return self._is_inductive


# ---------------------------------------------------------------------------
# Loop information extraction
# ---------------------------------------------------------------------------

@dataclass
class _LoopInfo:
    """Extracted information about a loop for invariant generation."""

    site_id: SiteId
    variables: Set[str]
    carrier_type: Any
    refinements: Dict[str, Any]
    has_counter: bool
    counter_name: Optional[str]
    has_accumulator: bool
    accumulator_name: Optional[str]
    collection_name: Optional[str]
    bound_vars: Dict[str, Tuple[Optional[Any], Optional[Any]]]  # name -> (lo, hi)


def _extract_loop_info(
    loop_site: SiteId,
    sections: Dict[SiteId, LocalSection],
) -> _LoopInfo:
    """Extract loop-relevant information from sections."""
    sec = sections.get(loop_site)
    refs = sec.refinements if sec else {}
    carrier = sec.carrier_type if sec else None

    variables: Set[str] = set()
    has_counter = False
    counter_name: Optional[str] = None
    has_accumulator = False
    accumulator_name: Optional[str] = None
    collection_name: Optional[str] = None
    bound_vars: Dict[str, Tuple[Optional[Any], Optional[Any]]] = {}

    for key, value in refs.items():
        if key.startswith("_"):
            continue
        variables.add(key)

        if key in ("i", "j", "k", "idx", "index", "counter", "n"):
            has_counter = True
            counter_name = key
        elif key in ("acc", "total", "sum", "result", "accumulator"):
            has_accumulator = True
            accumulator_name = key
        elif key in ("items", "elements", "data", "collection", "lst"):
            collection_name = key

        if isinstance(value, dict):
            lo = value.get("lower", value.get("min", None))
            hi = value.get("upper", value.get("max", None))
            if lo is not None or hi is not None:
                bound_vars[key] = (lo, hi)
        elif isinstance(value, (list, tuple)) and len(value) == 2:
            bound_vars[key] = (value[0], value[1])

    name = loop_site.name
    for part in name.split("."):
        if part and part[0].islower() and len(part) <= 3:
            variables.add(part)

    return _LoopInfo(
        site_id=loop_site,
        variables=variables,
        carrier_type=carrier,
        refinements=refs,
        has_counter=has_counter,
        counter_name=counter_name,
        has_accumulator=has_accumulator,
        accumulator_name=accumulator_name,
        collection_name=collection_name,
        bound_vars=bound_vars,
    )


# ---------------------------------------------------------------------------
# Template-based invariant generation
# ---------------------------------------------------------------------------

def _template_counter_bounds(info: _LoopInfo) -> List[InvariantCandidate]:
    """Generate counter-related invariant candidates."""
    candidates: List[InvariantCandidate] = []
    cname = info.counter_name
    if cname is None:
        return candidates

    candidates.append(InvariantCandidate(
        _expression=f"{cname} >= 0",
        _predicate=ComparisonPred(cname, ComparisonOp.GE, 0),
        _variables=frozenset({cname}),
        _source="template",
        _confidence=0.85,
        _loop_site=info.site_id,
    ))

    if cname in info.bound_vars:
        lo, hi = info.bound_vars[cname]
        if lo is not None:
            candidates.append(InvariantCandidate(
                _expression=f"{cname} >= {lo}",
                _predicate=ComparisonPred(cname, ComparisonOp.GE, lo),
                _variables=frozenset({cname}),
                _source="template",
                _confidence=0.80,
                _loop_site=info.site_id,
            ))
        if hi is not None:
            candidates.append(InvariantCandidate(
                _expression=f"{cname} <= {hi}",
                _predicate=ComparisonPred(cname, ComparisonOp.LE, hi),
                _variables=frozenset({cname}),
                _source="template",
                _confidence=0.80,
                _loop_site=info.site_id,
            ))

    if info.collection_name:
        coll = info.collection_name
        candidates.append(InvariantCandidate(
            _expression=f"{cname} <= len({coll})",
            _predicate=None,
            _variables=frozenset({cname, coll}),
            _source="template",
            _confidence=0.75,
            _loop_site=info.site_id,
        ))

    return candidates


def _template_accumulator(info: _LoopInfo) -> List[InvariantCandidate]:
    """Generate accumulator-related invariant candidates."""
    candidates: List[InvariantCandidate] = []
    aname = info.accumulator_name
    if aname is None:
        return candidates

    candidates.append(InvariantCandidate(
        _expression=f"{aname} >= 0",
        _predicate=ComparisonPred(aname, ComparisonOp.GE, 0),
        _variables=frozenset({aname}),
        _source="template",
        _confidence=0.60,
        _loop_site=info.site_id,
    ))

    if aname in info.bound_vars:
        lo, hi = info.bound_vars[aname]
        if lo is not None:
            candidates.append(InvariantCandidate(
                _expression=f"{aname} >= {lo}",
                _predicate=ComparisonPred(aname, ComparisonOp.GE, lo),
                _variables=frozenset({aname}),
                _source="template",
                _confidence=0.70,
                _loop_site=info.site_id,
            ))

    return candidates


def _template_monotonicity(info: _LoopInfo) -> List[InvariantCandidate]:
    """Generate monotonicity invariant candidates."""
    candidates: List[InvariantCandidate] = []

    if info.has_counter and info.counter_name:
        cname = info.counter_name
        candidates.append(InvariantCandidate(
            _expression=f"{cname}' >= {cname}  (monotonically increasing)",
            _variables=frozenset({cname}),
            _source="template",
            _confidence=0.70,
            _loop_site=info.site_id,
        ))

    if info.has_accumulator and info.accumulator_name:
        aname = info.accumulator_name
        candidates.append(InvariantCandidate(
            _expression=f"{aname}' >= {aname}  (monotonically non-decreasing)",
            _variables=frozenset({aname}),
            _source="template",
            _confidence=0.55,
            _loop_site=info.site_id,
        ))

    return candidates


def _template_collection_invariants(info: _LoopInfo) -> List[InvariantCandidate]:
    """Generate collection-related invariant candidates."""
    candidates: List[InvariantCandidate] = []

    if info.collection_name:
        coll = info.collection_name
        candidates.append(InvariantCandidate(
            _expression=f"len({coll}) >= 0",
            _predicate=LengthPred(coll, ComparisonOp.GE, 0),
            _variables=frozenset({coll}),
            _source="template",
            _confidence=0.95,
            _loop_site=info.site_id,
        ))

    return candidates


def _template_type_preservation(info: _LoopInfo) -> List[InvariantCandidate]:
    """Generate type preservation invariant candidates."""
    candidates: List[InvariantCandidate] = []
    carrier = info.carrier_type

    if carrier is not None and not isinstance(carrier, (AnyType, NeverType)):
        for var in sorted(info.variables):
            if isinstance(carrier, PrimitiveType):
                candidates.append(InvariantCandidate(
                    _expression=f"isinstance({var}, {carrier.kind.value})",
                    _variables=frozenset({var}),
                    _source="template",
                    _confidence=0.65,
                    _loop_site=info.site_id,
                ))
                break

    return candidates


# ---------------------------------------------------------------------------
# Section-based invariant generation
# ---------------------------------------------------------------------------

def _section_based_invariants(
    loop_site: SiteId,
    sections: Dict[SiteId, LocalSection],
) -> List[InvariantCandidate]:
    """Generate invariants from section refinement data."""
    candidates: List[InvariantCandidate] = []
    sec = sections.get(loop_site)
    if sec is None:
        return candidates

    carrier = sec.carrier_type
    if isinstance(carrier, RefinementType):
        pred_str = repr(carrier.predicate)
        candidates.append(InvariantCandidate(
            _expression=pred_str,
            _predicate=carrier.predicate,
            _variables=frozenset(carrier.predicate.free_vars()),
            _source="section",
            _confidence=0.80,
            _loop_site=loop_site,
        ))

    for key, value in sec.refinements.items():
        if key.startswith("_"):
            continue

        if isinstance(value, Predicate):
            pred_str = repr(value)
            candidates.append(InvariantCandidate(
                _expression=pred_str,
                _predicate=value,
                _variables=frozenset(value.free_vars()),
                _source="section",
                _confidence=0.75,
                _loop_site=loop_site,
            ))
        elif key == "non_null" and value:
            candidates.append(InvariantCandidate(
                _expression=f"{key} is not None",
                _variables=frozenset({key}),
                _source="section",
                _confidence=0.85,
                _loop_site=loop_site,
            ))
        elif key == "non_negative" and value:
            candidates.append(InvariantCandidate(
                _expression=f"{key} >= 0",
                _predicate=ComparisonPred(key, ComparisonOp.GE, 0),
                _variables=frozenset({key}),
                _source="section",
                _confidence=0.80,
                _loop_site=loop_site,
            ))
        elif key == "positive" and value:
            candidates.append(InvariantCandidate(
                _expression=f"{key} > 0",
                _predicate=ComparisonPred(key, ComparisonOp.GT, 0),
                _variables=frozenset({key}),
                _source="section",
                _confidence=0.80,
                _loop_site=loop_site,
            ))

    return candidates


# ---------------------------------------------------------------------------
# Relational invariant generation
# ---------------------------------------------------------------------------

def _relational_invariants(
    info: _LoopInfo,
    sections: Dict[SiteId, LocalSection],
) -> List[InvariantCandidate]:
    """Generate relational invariants between loop variables."""
    candidates: List[InvariantCandidate] = []
    vars_list = sorted(info.variables)

    if len(vars_list) < 2:
        return candidates

    for i in range(len(vars_list)):
        for j in range(i + 1, len(vars_list)):
            va, vb = vars_list[i], vars_list[j]

            if va in info.bound_vars and vb in info.bound_vars:
                lo_a, hi_a = info.bound_vars[va]
                lo_b, hi_b = info.bound_vars[vb]
                if hi_a is not None and lo_b is not None and hi_a == lo_b:
                    candidates.append(InvariantCandidate(
                        _expression=f"{va} <= {vb}",
                        _predicate=ComparisonPred(va, ComparisonOp.LE, vb),
                        _variables=frozenset({va, vb}),
                        _source="relational",
                        _confidence=0.60,
                        _loop_site=info.site_id,
                    ))

    if info.counter_name and info.accumulator_name:
        c = info.counter_name
        a = info.accumulator_name
        candidates.append(InvariantCandidate(
            _expression=f"{a} is a function of {c} iterations",
            _variables=frozenset({c, a}),
            _source="relational",
            _confidence=0.45,
            _loop_site=info.site_id,
        ))

    return candidates


# ---------------------------------------------------------------------------
# InvariantCandidateGenerator
# ---------------------------------------------------------------------------

class InvariantCandidateGenerator:
    """Generate loop invariant candidates from templates and section data.

    Usage::

        gen = InvariantCandidateGenerator()
        candidates = gen.generate(loop_site, sections)
        for c in candidates:
            print(f"[{c.source}, {c.confidence:.0%}] {c.expression}")
    """

    def __init__(
        self,
        *,
        min_confidence: float = 0.0,
        max_candidates: int = 20,
        include_relational: bool = True,
    ) -> None:
        self._min_confidence = min_confidence
        self._max_candidates = max_candidates
        self._include_relational = include_relational

    def generate(
        self,
        loop_site: SiteId,
        sections: Dict[SiteId, LocalSection],
    ) -> List[InvariantCandidate]:
        """Generate invariant candidates for a loop site.

        Combines template-based, section-based, and relational invariants.
        Returns a list sorted by confidence (highest first).
        """
        info = _extract_loop_info(loop_site, sections)

        candidates: List[InvariantCandidate] = []
        candidates.extend(self._template_based(info))
        candidates.extend(self._section_based(loop_site, sections))

        if self._include_relational:
            candidates.extend(_relational_invariants(info, sections))

        candidates = [
            c for c in candidates if c.confidence >= self._min_confidence
        ]
        candidates = _deduplicate_candidates(candidates)
        candidates.sort(key=lambda c: c.confidence, reverse=True)
        return candidates[: self._max_candidates]

    def _template_based(
        self,
        loop_info: _LoopInfo,
    ) -> List[InvariantCandidate]:
        """Generate template-based invariant candidates."""
        candidates: List[InvariantCandidate] = []
        candidates.extend(_template_counter_bounds(loop_info))
        candidates.extend(_template_accumulator(loop_info))
        candidates.extend(_template_monotonicity(loop_info))
        candidates.extend(_template_collection_invariants(loop_info))
        candidates.extend(_template_type_preservation(loop_info))
        return candidates

    def _section_based(
        self,
        loop_site: SiteId,
        sections: Dict[SiteId, LocalSection],
    ) -> List[InvariantCandidate]:
        """Generate section-based invariant candidates."""
        return _section_based_invariants(loop_site, sections)

    def generate_for_all_loops(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Dict[SiteId, List[InvariantCandidate]]:
        """Generate invariant candidates for all loop sites in a cover."""
        results: Dict[SiteId, List[InvariantCandidate]] = {}
        for sid in cover.sites:
            if sid.kind == SiteKind.LOOP_HEADER_INVARIANT:
                results[sid] = self.generate(sid, sections)
        return results

    def summarize(
        self,
        candidates: List[InvariantCandidate],
    ) -> str:
        """Produce a human-readable summary of invariant candidates."""
        if not candidates:
            return "No invariant candidates generated."

        lines: List[str] = []
        lines.append(f"Invariant Candidates ({len(candidates)} total):")

        by_source: Dict[str, List[InvariantCandidate]] = {}
        for c in candidates:
            by_source.setdefault(c.source, []).append(c)

        for source, source_cands in sorted(by_source.items()):
            lines.append(f"\n  [{source}] ({len(source_cands)} candidates)")
            for i, c in enumerate(source_cands, 1):
                vars_str = ", ".join(sorted(c.variables))
                lines.append(
                    f"    {i}. [{c.confidence:.0%}] {c.expression}"
                )
                if vars_str:
                    lines.append(f"       vars: {vars_str}")

        return "\n".join(lines)


def _deduplicate_candidates(
    candidates: List[InvariantCandidate],
) -> List[InvariantCandidate]:
    """Remove duplicate candidates by expression text."""
    seen: Set[str] = set()
    deduped: List[InvariantCandidate] = []
    for c in candidates:
        key = c.expression.strip()
        if key not in seen:
            seen.add(key)
            deduped.append(c)
    return deduped
