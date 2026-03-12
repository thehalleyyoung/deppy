"""Theory Family 9: Sequence & Collection Theory.

Handles list/tuple/dict/set length, membership, emptiness tracking.
Forward: propagate length through operations.
Backward: require non-empty/sufficient length.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism

from .theory_pack_base import (
    BoundaryClassification,
    SolverResult,
    SolverStatus,
    TheoryPackBase,
    merge_refinements,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Collection kind
# ═══════════════════════════════════════════════════════════════════════════════


class CollectionKind(Enum):
    LIST = "list"
    TUPLE = "tuple"
    DICT = "dict"
    SET = "set"
    FROZENSET = "frozenset"
    STRING = "str"
    BYTES = "bytes"
    DEQUE = "deque"
    RANGE = "range"
    GENERATOR = "generator"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class LengthInfo:
    """Length information for a collection."""
    exact: Optional[int] = None
    min_length: Optional[int] = None
    max_length: Optional[int] = None

    @property
    def is_known_empty(self) -> bool:
        return self.exact == 0

    @property
    def is_known_non_empty(self) -> bool:
        if self.exact is not None:
            return self.exact > 0
        if self.min_length is not None:
            return self.min_length > 0
        return False

    @property
    def is_exact(self) -> bool:
        return self.exact is not None

    def intersect(self, other: LengthInfo) -> LengthInfo:
        exact = self.exact
        if other.exact is not None:
            if exact is not None and exact != other.exact:
                return LengthInfo(exact=-1)  # contradiction
            exact = other.exact
        lo = max(self.min_length or 0, other.min_length or 0)
        hi_a = self.max_length
        hi_b = other.max_length
        if hi_a is not None and hi_b is not None:
            hi = min(hi_a, hi_b)
        else:
            hi = hi_a if hi_a is not None else hi_b
        if exact is not None:
            return LengthInfo(exact=exact)
        return LengthInfo(min_length=lo if lo > 0 else None, max_length=hi)

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {}
        if self.exact is not None:
            refs["length"] = self.exact
            refs["non_empty"] = self.exact > 0
        else:
            if self.min_length is not None:
                refs["min_length"] = self.min_length
                refs["non_empty"] = self.min_length > 0
            if self.max_length is not None:
                refs["max_length"] = self.max_length
        return refs

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> LengthInfo:
        exact = refs.get("length")
        if isinstance(exact, int):
            return LengthInfo(exact=exact)
        lo = refs.get("min_length")
        hi = refs.get("max_length")
        if refs.get("non_empty") and (lo is None or lo < 1):
            lo = 1
        return LengthInfo(
            min_length=lo if isinstance(lo, int) else None,
            max_length=hi if isinstance(hi, int) else None,
        )


@dataclass
class CollectionInfo:
    """Complete information about a collection."""
    kind: CollectionKind = CollectionKind.UNKNOWN
    length: LengthInfo = field(default_factory=LengthInfo)
    element_type: Any = None
    key_type: Any = None
    value_type: Any = None
    known_contents: Optional[Tuple[Any, ...]] = None
    is_homogeneous: bool = True
    is_mutable: bool = True

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {"collection_kind": self.kind.value}
        refs.update(self.length.to_refinements())
        if self.element_type is not None:
            refs["element_type"] = self.element_type
        if self.key_type is not None:
            refs["key_type"] = self.key_type
        if self.value_type is not None:
            refs["value_type"] = self.value_type
        if self.known_contents is not None:
            refs["known_contents"] = self.known_contents
        refs["is_homogeneous"] = self.is_homogeneous
        refs["is_mutable"] = self.is_mutable
        return refs

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> CollectionInfo:
        kind_str = refs.get("collection_kind", "unknown")
        try:
            kind = CollectionKind(kind_str)
        except ValueError:
            kind = CollectionKind.UNKNOWN
        return CollectionInfo(
            kind=kind,
            length=LengthInfo.from_refinements(refs),
            element_type=refs.get("element_type"),
            key_type=refs.get("key_type"),
            value_type=refs.get("value_type"),
            known_contents=refs.get("known_contents"),
            is_homogeneous=refs.get("is_homogeneous", True),
            is_mutable=refs.get("is_mutable", True),
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Collection operation rules
# ═══════════════════════════════════════════════════════════════════════════════


def append_length(info: LengthInfo) -> LengthInfo:
    if info.exact is not None:
        return LengthInfo(exact=info.exact + 1)
    lo = (info.min_length or 0) + 1
    hi = info.max_length + 1 if info.max_length is not None else None
    return LengthInfo(min_length=lo, max_length=hi)


def extend_length(info: LengthInfo, extension: LengthInfo) -> LengthInfo:
    if info.exact is not None and extension.exact is not None:
        return LengthInfo(exact=info.exact + extension.exact)
    lo = (info.min_length or 0) + (extension.min_length or 0)
    hi_a = info.max_length
    hi_b = extension.max_length
    hi = hi_a + hi_b if hi_a is not None and hi_b is not None else None
    return LengthInfo(min_length=lo if lo > 0 else None, max_length=hi)


def pop_length(info: LengthInfo) -> LengthInfo:
    if info.exact is not None:
        return LengthInfo(exact=max(0, info.exact - 1))
    lo = max(0, (info.min_length or 0) - 1)
    hi = max(0, info.max_length - 1) if info.max_length is not None else None
    return LengthInfo(min_length=lo if lo > 0 else None, max_length=hi)


def slice_length(info: LengthInfo, start: Optional[int], stop: Optional[int], step: Optional[int]) -> LengthInfo:
    if info.exact is not None:
        s = start if start is not None else 0
        e = stop if stop is not None else info.exact
        st = step if step is not None else 1
        if s < 0:
            s += info.exact
        if e < 0:
            e += info.exact
        s = max(0, min(s, info.exact))
        e = max(0, min(e, info.exact))
        if st > 0:
            result = max(0, (e - s + st - 1) // st)
        elif st < 0:
            result = max(0, (s - e - st - 1) // (-st))
        else:
            result = 0
        return LengthInfo(exact=result)
    return LengthInfo()


def concat_length(a: LengthInfo, b: LengthInfo) -> LengthInfo:
    return extend_length(a, b)


def filter_length(info: LengthInfo) -> LengthInfo:
    hi = info.exact if info.exact is not None else info.max_length
    return LengthInfo(min_length=0, max_length=hi)


def dict_update_length(base: LengthInfo, update: LengthInfo) -> LengthInfo:
    if base.exact is not None and update.exact is not None:
        max_len = base.exact + update.exact
        min_len = max(base.exact, update.exact)
        return LengthInfo(min_length=min_len, max_length=max_len)
    return LengthInfo(min_length=base.min_length)


# ═══════════════════════════════════════════════════════════════════════════════
# SequenceCollectionTheoryPack
# ═══════════════════════════════════════════════════════════════════════════════


class SequenceCollectionTheoryPack(TheoryPackBase):
    """Theory Family 9: Sequence & Collection Theory."""

    pack_name = "sequence_collection"
    pack_priority = 22

    _APPLICABLE = frozenset({
        SiteKind.SSA_VALUE,
        SiteKind.ARGUMENT_BOUNDARY,
        SiteKind.RETURN_OUTPUT_BOUNDARY,
        SiteKind.CALL_RESULT,
        SiteKind.ERROR,
    })

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._APPLICABLE

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        refs = section.refinements
        info = CollectionInfo.from_refinements(refs)

        if info.kind == CollectionKind.UNKNOWN and not self._is_collection_section(refs):
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation="not a collection section",
            )

        op_name = refs.get("collection_op")
        if op_name is not None:
            return self._solve_collection_op(site, section, info, str(op_name))

        new_refs = dict(refs)
        new_refs.update(info.to_refinements())
        return SolverResult(
            status=SolverStatus.REFINED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=section.trust,
                provenance=f"collection info: {info.kind.value}",
                witnesses=dict(section.witnesses),
            ),
            explanation=f"collection {info.kind.value}: length={info.length}",
        )

    def _solve_collection_op(
        self, site: SiteId, section: LocalSection,
        info: CollectionInfo, op_name: str,
    ) -> SolverResult:
        refs = section.refinements
        result_length = info.length

        if op_name == "append":
            result_length = append_length(info.length)
        elif op_name == "extend":
            ext = LengthInfo.from_refinements(refs.get("_extension_info", {}))
            result_length = extend_length(info.length, ext)
        elif op_name == "pop":
            if info.length.is_known_empty:
                return SolverResult(
                    status=SolverStatus.UNSATISFIABLE,
                    section=section,
                    explanation="pop from empty collection",
                )
            result_length = pop_length(info.length)
        elif op_name == "insert":
            result_length = append_length(info.length)
        elif op_name == "remove":
            result_length = pop_length(info.length)
        elif op_name in ("clear", "reset"):
            result_length = LengthInfo(exact=0)
        elif op_name == "slice":
            start = refs.get("slice_start")
            stop = refs.get("slice_stop")
            step = refs.get("slice_step")
            result_length = slice_length(info.length, start, stop, step)
        elif op_name in ("concat", "__add__", "+"):
            other = LengthInfo.from_refinements(refs.get("_other_info", {}))
            result_length = concat_length(info.length, other)
        elif op_name == "filter":
            result_length = filter_length(info.length)
        elif op_name in ("copy", "list", "tuple", "sorted"):
            result_length = info.length
        elif op_name in ("keys", "values", "items"):
            result_length = info.length
        elif op_name == "update":
            other = LengthInfo.from_refinements(refs.get("_other_info", {}))
            result_length = dict_update_length(info.length, other)
        elif op_name == "reverse":
            result_length = info.length
        elif op_name == "sort":
            result_length = info.length
        elif op_name == "index":
            if info.length.is_known_empty:
                return SolverResult(
                    status=SolverStatus.UNSATISFIABLE,
                    section=section,
                    explanation="index on empty collection",
                )

        result_info = CollectionInfo(
            kind=info.kind, length=result_length,
            element_type=info.element_type,
            key_type=info.key_type, value_type=info.value_type,
        )
        new_refs = dict(refs)
        new_refs.update(result_info.to_refinements())
        new_refs["_collection_op_resolved"] = True

        return SolverResult(
            status=SolverStatus.SOLVED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=TrustLevel.BOUNDED_AUTO,
                provenance=f"collection: {op_name} -> length={result_length}",
                witnesses=dict(section.witnesses),
            ),
            explanation=f"{op_name}: length {info.length} -> {result_length}",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        restricted = morphism.restrict(section)
        info = CollectionInfo.from_refinements(section.refinements)

        if info.kind == CollectionKind.UNKNOWN:
            return restricted

        new_refs = merge_refinements(restricted.refinements, info.to_refinements(), "meet")
        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance="collection forward",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        refs = section.refinements
        required_refs: Dict[str, Any] = {}

        op_name = refs.get("collection_op") or refs.get("operation")
        if op_name in ("pop", "index", "__getitem__", "remove"):
            required_refs["non_empty"] = True
            required_refs["min_length"] = 1

        idx = refs.get("access_index")
        if idx is not None and isinstance(idx, int):
            required_refs["min_length"] = abs(idx) + 1 if idx >= 0 else abs(idx)

        if refs.get("requires_non_empty"):
            required_refs["non_empty"] = True

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required_refs,
            trust=TrustLevel.RESIDUAL,
            provenance="collection pullback",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        name = error_site.name
        if "pop" in name.lower() or "index" in name.lower():
            return "collection is non-empty"
        if "key" in name.lower():
            return "key exists in dictionary"
        return f"collection precondition for {name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        refs = section.refinements
        if refs.get("_collection_op_resolved"):
            return BoundaryClassification.FULLY_PROVEN
        info = CollectionInfo.from_refinements(refs)
        if info.length.is_exact:
            return BoundaryClassification.FULLY_PROVEN
        if info.length.is_known_non_empty:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        return BoundaryClassification.REQUIRES_PROOF

    def _is_collection_section(self, refs: Dict[str, Any]) -> bool:
        keys = {"collection_kind", "length", "min_length", "max_length",
                "non_empty", "element_type", "collection_op", "known_contents"}
        return bool(keys & set(refs.keys()))
