"""Built-in Python sequence operations theory pack.

Provides refined type analysis for list, tuple, and str operations
including indexing, slicing, iteration, comprehensions, and mutation.
Integrates with the SequenceCollectionTheoryPack for length tracking
and adds Python-specific operation semantics.
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
    Sequence,
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

from ..theory_pack_base import (
    BoundaryClassification,
    SolverResult,
    SolverStatus,
    TheoryPackBase,
    merge_refinements,
    make_section,
)
from ..sequence_collection_theory import (
    CollectionKind,
    LengthInfo,
    CollectionInfo,
    append_length,
    extend_length,
    pop_length,
    slice_length,
    concat_length,
    filter_length,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Sequence element type tracking
# ═══════════════════════════════════════════════════════════════════════════════


class ElementTypeStatus(Enum):
    """Status of element type knowledge."""
    KNOWN_UNIFORM = "known_uniform"
    KNOWN_HETEROGENEOUS = "known_heterogeneous"
    PARTIALLY_KNOWN = "partially_known"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class ElementTypeInfo:
    """Element type information for a sequence."""
    status: ElementTypeStatus = ElementTypeStatus.UNKNOWN
    uniform_type: Optional[str] = None
    position_types: Tuple[Optional[str], ...] = ()
    contains_none: bool = False
    element_supertypes: Tuple[str, ...] = ()

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {
            "_element_type_status": self.status.value,
        }
        if self.uniform_type is not None:
            refs["element_type"] = self.uniform_type
        if self.position_types:
            refs["_position_types"] = self.position_types
        if self.contains_none:
            refs["_contains_none"] = True
        if self.element_supertypes:
            refs["_element_supertypes"] = self.element_supertypes
        return refs

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> ElementTypeInfo:
        status_str = refs.get("_element_type_status", "unknown")
        try:
            status = ElementTypeStatus(status_str)
        except ValueError:
            status = ElementTypeStatus.UNKNOWN
        pos_types = refs.get("_position_types", ())
        if isinstance(pos_types, list):
            pos_types = tuple(pos_types)
        supers = refs.get("_element_supertypes", ())
        if isinstance(supers, list):
            supers = tuple(supers)
        return ElementTypeInfo(
            status=status,
            uniform_type=refs.get("element_type"),
            position_types=pos_types,
            contains_none=refs.get("_contains_none", False),
            element_supertypes=supers,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# List-specific operation semantics
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ListOpResult:
    """Result of analyzing a list operation."""
    length: LengthInfo
    element_info: ElementTypeInfo
    is_in_place: bool = False
    returns_value: bool = False
    return_type: Optional[str] = None
    may_raise: Tuple[str, ...] = ()
    preserves_order: bool = True

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {}
        refs.update(self.length.to_refinements())
        refs.update(self.element_info.to_refinements())
        refs["_list_op_in_place"] = self.is_in_place
        refs["_list_op_returns_value"] = self.returns_value
        if self.return_type is not None:
            refs["_list_op_return_type"] = self.return_type
        if self.may_raise:
            refs["_list_op_may_raise"] = self.may_raise
        refs["_list_op_preserves_order"] = self.preserves_order
        return refs


def analyze_list_append(info: CollectionInfo, elem_type: Optional[str]) -> ListOpResult:
    """Analyze list.append(x) operation."""
    new_length = append_length(info.length)
    if info.element_type is not None and elem_type is not None:
        if info.element_type == elem_type:
            elem_info = ElementTypeInfo(
                status=ElementTypeStatus.KNOWN_UNIFORM,
                uniform_type=elem_type,
            )
        else:
            elem_info = ElementTypeInfo(
                status=ElementTypeStatus.KNOWN_HETEROGENEOUS,
                element_supertypes=(str(info.element_type), elem_type),
            )
    else:
        elem_info = ElementTypeInfo(status=ElementTypeStatus.UNKNOWN)
    return ListOpResult(
        length=new_length, element_info=elem_info,
        is_in_place=True, returns_value=False, return_type="None",
    )


def analyze_list_insert(
    info: CollectionInfo, index: Optional[int], elem_type: Optional[str]
) -> ListOpResult:
    """Analyze list.insert(i, x) operation."""
    new_length = append_length(info.length)
    may_raise: Tuple[str, ...] = ()
    elem_info = ElementTypeInfo(status=ElementTypeStatus.UNKNOWN)
    if elem_type is not None and info.element_type is not None:
        if elem_type == info.element_type:
            elem_info = ElementTypeInfo(
                status=ElementTypeStatus.KNOWN_UNIFORM,
                uniform_type=elem_type,
            )
    return ListOpResult(
        length=new_length, element_info=elem_info,
        is_in_place=True, returns_value=False, return_type="None",
        may_raise=may_raise,
    )


def analyze_list_pop(
    info: CollectionInfo, index: Optional[int] = None
) -> ListOpResult:
    """Analyze list.pop([i]) operation."""
    may_raise: Tuple[str, ...] = ()
    if info.length.is_known_empty:
        may_raise = ("IndexError",)
    elif index is not None:
        if info.length.exact is not None:
            if index >= info.length.exact or index < -info.length.exact:
                may_raise = ("IndexError",)
    new_length = pop_length(info.length)
    elem_info = ElementTypeInfo(
        status=ElementTypeStatus.UNKNOWN,
        uniform_type=info.element_type if isinstance(info.element_type, str) else None,
    )
    return ListOpResult(
        length=new_length, element_info=elem_info,
        is_in_place=True, returns_value=True,
        return_type=info.element_type if isinstance(info.element_type, str) else None,
        may_raise=may_raise,
    )


def analyze_list_remove(info: CollectionInfo) -> ListOpResult:
    """Analyze list.remove(x) operation."""
    may_raise: Tuple[str, ...] = ()
    if info.length.is_known_empty:
        may_raise = ("ValueError",)
    new_length = pop_length(info.length)
    return ListOpResult(
        length=new_length,
        element_info=ElementTypeInfo(status=ElementTypeStatus.UNKNOWN),
        is_in_place=True, returns_value=False, return_type="None",
        may_raise=may_raise,
    )


def analyze_list_extend(info: CollectionInfo, other: CollectionInfo) -> ListOpResult:
    """Analyze list.extend(iterable) operation."""
    new_length = extend_length(info.length, other.length)
    if info.element_type is not None and other.element_type is not None:
        if info.element_type == other.element_type:
            elem_info = ElementTypeInfo(
                status=ElementTypeStatus.KNOWN_UNIFORM,
                uniform_type=str(info.element_type),
            )
        else:
            elem_info = ElementTypeInfo(
                status=ElementTypeStatus.KNOWN_HETEROGENEOUS,
                element_supertypes=(str(info.element_type), str(other.element_type)),
            )
    else:
        elem_info = ElementTypeInfo(status=ElementTypeStatus.UNKNOWN)
    return ListOpResult(
        length=new_length, element_info=elem_info,
        is_in_place=True, returns_value=False, return_type="None",
    )


def analyze_list_sort(info: CollectionInfo) -> ListOpResult:
    """Analyze list.sort() operation."""
    return ListOpResult(
        length=info.length,
        element_info=ElementTypeInfo(
            status=ElementTypeStatus.KNOWN_UNIFORM if info.element_type else ElementTypeStatus.UNKNOWN,
            uniform_type=info.element_type if isinstance(info.element_type, str) else None,
        ),
        is_in_place=True, returns_value=False, return_type="None",
        preserves_order=False,
    )


def analyze_list_reverse(info: CollectionInfo) -> ListOpResult:
    """Analyze list.reverse() operation."""
    return ListOpResult(
        length=info.length,
        element_info=ElementTypeInfo(
            status=ElementTypeStatus.KNOWN_UNIFORM if info.element_type else ElementTypeStatus.UNKNOWN,
            uniform_type=info.element_type if isinstance(info.element_type, str) else None,
        ),
        is_in_place=True, returns_value=False, return_type="None",
        preserves_order=False,
    )


def analyze_list_copy(info: CollectionInfo) -> ListOpResult:
    """Analyze list.copy() operation."""
    return ListOpResult(
        length=info.length,
        element_info=ElementTypeInfo(
            status=ElementTypeStatus.KNOWN_UNIFORM if info.element_type else ElementTypeStatus.UNKNOWN,
            uniform_type=info.element_type if isinstance(info.element_type, str) else None,
        ),
        is_in_place=False, returns_value=True, return_type="list",
    )


def analyze_list_clear(info: CollectionInfo) -> ListOpResult:
    """Analyze list.clear() operation."""
    return ListOpResult(
        length=LengthInfo(exact=0),
        element_info=ElementTypeInfo(status=ElementTypeStatus.UNKNOWN),
        is_in_place=True, returns_value=False, return_type="None",
    )


def analyze_list_index(info: CollectionInfo) -> ListOpResult:
    """Analyze list.index(x) operation."""
    may_raise: Tuple[str, ...] = ()
    if info.length.is_known_empty:
        may_raise = ("ValueError",)
    return ListOpResult(
        length=info.length,
        element_info=ElementTypeInfo(status=ElementTypeStatus.UNKNOWN),
        is_in_place=False, returns_value=True, return_type="int",
        may_raise=may_raise,
    )


def analyze_list_count(info: CollectionInfo) -> ListOpResult:
    """Analyze list.count(x) operation."""
    return ListOpResult(
        length=info.length,
        element_info=ElementTypeInfo(status=ElementTypeStatus.UNKNOWN),
        is_in_place=False, returns_value=True, return_type="int",
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Tuple-specific operation semantics
# ═══════════════════════════════════════════════════════════════════════════════


def analyze_tuple_index_access(
    info: CollectionInfo, index: int
) -> Dict[str, Any]:
    """Analyze tuple[i] access with position-type tracking."""
    result: Dict[str, Any] = {}
    may_raise: List[str] = []

    if info.length.exact is not None:
        if 0 <= index < info.length.exact or -info.length.exact <= index < 0:
            result["_access_safe"] = True
        else:
            may_raise.append("IndexError")
            result["_access_safe"] = False
    elif info.length.min_length is not None:
        if 0 <= index < info.length.min_length:
            result["_access_safe"] = True
        else:
            result["_access_safe"] = None  # unknown
    else:
        result["_access_safe"] = None

    elem_refs = ElementTypeInfo.from_refinements(info.to_refinements())
    if elem_refs.position_types:
        actual_idx = index if index >= 0 else (
            len(elem_refs.position_types) + index
            if info.length.exact is not None else None
        )
        if actual_idx is not None and 0 <= actual_idx < len(elem_refs.position_types):
            pos_type = elem_refs.position_types[actual_idx]
            if pos_type is not None:
                result["_result_type"] = pos_type
    elif elem_refs.uniform_type is not None:
        result["_result_type"] = elem_refs.uniform_type

    result["_may_raise"] = tuple(may_raise)
    return result


def analyze_tuple_concat(a: CollectionInfo, b: CollectionInfo) -> CollectionInfo:
    """Analyze tuple + tuple concatenation."""
    new_length = concat_length(a.length, b.length)
    a_elem = ElementTypeInfo.from_refinements(a.to_refinements())
    b_elem = ElementTypeInfo.from_refinements(b.to_refinements())

    combined_pos = a_elem.position_types + b_elem.position_types
    if a_elem.uniform_type is not None and b_elem.uniform_type is not None:
        if a_elem.uniform_type == b_elem.uniform_type:
            elem_type = a_elem.uniform_type
        else:
            elem_type = f"Union[{a_elem.uniform_type}, {b_elem.uniform_type}]"
    else:
        elem_type = None

    return CollectionInfo(
        kind=CollectionKind.TUPLE,
        length=new_length,
        element_type=elem_type,
        is_homogeneous=a.is_homogeneous and b.is_homogeneous and elem_type is not None,
        is_mutable=False,
    )


def analyze_tuple_multiply(info: CollectionInfo, n: int) -> CollectionInfo:
    """Analyze tuple * n operation."""
    if info.length.exact is not None:
        new_length = LengthInfo(exact=info.length.exact * n if n > 0 else 0)
    elif n <= 0:
        new_length = LengthInfo(exact=0)
    else:
        lo = (info.length.min_length or 0) * n
        hi = info.length.max_length * n if info.length.max_length is not None else None
        new_length = LengthInfo(min_length=lo if lo > 0 else None, max_length=hi)
    return CollectionInfo(
        kind=info.kind,
        length=new_length,
        element_type=info.element_type,
        is_homogeneous=info.is_homogeneous,
        is_mutable=info.is_mutable,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# String-specific operation semantics
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class StringOpResult:
    """Result of analyzing a string operation."""
    length: LengthInfo
    return_type: str = "str"
    may_raise: Tuple[str, ...] = ()
    preserves_case: bool = True

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {}
        refs.update(self.length.to_refinements())
        refs["collection_kind"] = "str"
        refs["_str_return_type"] = self.return_type
        if self.may_raise:
            refs["_str_may_raise"] = self.may_raise
        refs["_str_preserves_case"] = self.preserves_case
        return refs


def analyze_str_join(sep: CollectionInfo, iterable: CollectionInfo) -> StringOpResult:
    """Analyze str.join(iterable) operation."""
    if iterable.length.exact is not None and sep.length.exact is not None:
        if iterable.length.exact == 0:
            result_len = LengthInfo(exact=0)
        else:
            min_total = sep.length.exact * (iterable.length.exact - 1)
            result_len = LengthInfo(min_length=min_total)
    else:
        result_len = LengthInfo()
    return StringOpResult(length=result_len)


def analyze_str_split(info: CollectionInfo, maxsplit: Optional[int] = None) -> StringOpResult:
    """Analyze str.split() which returns a list of strings."""
    if info.length.is_known_empty:
        result_len = LengthInfo(exact=1)
    elif maxsplit is not None:
        result_len = LengthInfo(min_length=1, max_length=maxsplit + 1)
    elif info.length.exact is not None:
        result_len = LengthInfo(min_length=1, max_length=info.length.exact)
    else:
        result_len = LengthInfo(min_length=1)
    return StringOpResult(length=result_len, return_type="list[str]")


def analyze_str_replace(
    info: CollectionInfo, old_len: int, new_len: int, count: Optional[int] = None
) -> StringOpResult:
    """Analyze str.replace(old, new, count) operation."""
    if info.length.exact is not None and old_len > 0:
        max_replacements = info.length.exact // old_len if old_len > 0 else 0
        if count is not None:
            max_replacements = min(max_replacements, count)
        length_change = (new_len - old_len) * max_replacements
        lo = max(0, info.length.exact - abs(length_change)) if length_change < 0 else info.length.exact
        hi = info.length.exact + abs(length_change) if length_change > 0 else info.length.exact
        result_len = LengthInfo(min_length=lo, max_length=hi)
    else:
        result_len = LengthInfo()
    return StringOpResult(length=result_len)


def analyze_str_strip(info: CollectionInfo) -> StringOpResult:
    """Analyze str.strip/lstrip/rstrip operation."""
    if info.length.exact is not None:
        result_len = LengthInfo(min_length=0, max_length=info.length.exact)
    elif info.length.max_length is not None:
        result_len = LengthInfo(min_length=0, max_length=info.length.max_length)
    else:
        result_len = LengthInfo(min_length=0)
    return StringOpResult(length=result_len)


def analyze_str_upper_lower(info: CollectionInfo) -> StringOpResult:
    """Analyze str.upper/lower/title/capitalize/swapcase operation."""
    return StringOpResult(length=info.length, preserves_case=False)


def analyze_str_format(info: CollectionInfo, arg_count: int) -> StringOpResult:
    """Analyze str.format(*args) or f-string operation."""
    return StringOpResult(length=LengthInfo())


def analyze_str_encode(info: CollectionInfo, encoding: str = "utf-8") -> StringOpResult:
    """Analyze str.encode(encoding) operation."""
    if encoding in ("ascii", "latin-1", "iso-8859-1") and info.length.exact is not None:
        result_len = LengthInfo(exact=info.length.exact)
    elif info.length.exact is not None:
        if encoding == "utf-8":
            result_len = LengthInfo(
                min_length=info.length.exact,
                max_length=info.length.exact * 4,
            )
        else:
            result_len = LengthInfo(min_length=1)
    else:
        result_len = LengthInfo()
    return StringOpResult(length=result_len, return_type="bytes")


def analyze_str_startswith_endswith(info: CollectionInfo) -> StringOpResult:
    """Analyze str.startswith/endswith which returns bool."""
    return StringOpResult(length=info.length, return_type="bool")


def analyze_str_find(info: CollectionInfo) -> StringOpResult:
    """Analyze str.find/rfind which returns int (-1 or index)."""
    return StringOpResult(length=info.length, return_type="int")


def analyze_str_index_method(info: CollectionInfo) -> StringOpResult:
    """Analyze str.index/rindex which returns int or raises ValueError."""
    may_raise: Tuple[str, ...] = ()
    if info.length.is_known_empty:
        may_raise = ("ValueError",)
    return StringOpResult(length=info.length, return_type="int", may_raise=may_raise)


# ═══════════════════════════════════════════════════════════════════════════════
# Dispatch table
# ═══════════════════════════════════════════════════════════════════════════════


_LIST_OPS = frozenset({
    "append", "insert", "pop", "remove", "extend", "sort", "reverse",
    "copy", "clear", "index", "count",
})

_TUPLE_OPS = frozenset({
    "index", "count", "__add__", "__mul__",
})

_STR_OPS = frozenset({
    "join", "split", "rsplit", "replace", "strip", "lstrip", "rstrip",
    "upper", "lower", "title", "capitalize", "swapcase",
    "format", "encode", "startswith", "endswith",
    "find", "rfind", "index", "rindex",
    "center", "ljust", "rjust", "zfill",
    "isdigit", "isalpha", "isalnum", "isspace", "isupper", "islower",
})


def dispatch_sequence_op(
    kind: CollectionKind,
    op_name: str,
    info: CollectionInfo,
    refs: Dict[str, Any],
) -> Dict[str, Any]:
    """Dispatch a sequence operation and return result refinements."""
    result: Dict[str, Any] = {}

    if kind == CollectionKind.LIST:
        elem_type = refs.get("_new_element_type")
        if op_name == "append":
            r = analyze_list_append(info, elem_type)
            result.update(r.to_refinements())
        elif op_name == "insert":
            idx = refs.get("_insert_index")
            r = analyze_list_insert(info, idx, elem_type)
            result.update(r.to_refinements())
        elif op_name == "pop":
            idx = refs.get("_pop_index")
            r = analyze_list_pop(info, idx)
            result.update(r.to_refinements())
        elif op_name == "remove":
            r = analyze_list_remove(info)
            result.update(r.to_refinements())
        elif op_name == "extend":
            other = CollectionInfo.from_refinements(refs.get("_other_info", {}))
            r = analyze_list_extend(info, other)
            result.update(r.to_refinements())
        elif op_name == "sort":
            r = analyze_list_sort(info)
            result.update(r.to_refinements())
        elif op_name == "reverse":
            r = analyze_list_reverse(info)
            result.update(r.to_refinements())
        elif op_name == "copy":
            r = analyze_list_copy(info)
            result.update(r.to_refinements())
        elif op_name == "clear":
            r = analyze_list_clear(info)
            result.update(r.to_refinements())
        elif op_name == "index":
            r = analyze_list_index(info)
            result.update(r.to_refinements())
        elif op_name == "count":
            r = analyze_list_count(info)
            result.update(r.to_refinements())

    elif kind == CollectionKind.TUPLE:
        if op_name == "__getitem__":
            idx = refs.get("_access_index", 0)
            if isinstance(idx, int):
                r = analyze_tuple_index_access(info, idx)
                result.update(r)
        elif op_name == "__add__":
            other = CollectionInfo.from_refinements(refs.get("_other_info", {}))
            new_info = analyze_tuple_concat(info, other)
            result.update(new_info.to_refinements())
        elif op_name == "__mul__":
            n = refs.get("_multiply_count", 1)
            if isinstance(n, int):
                new_info = analyze_tuple_multiply(info, n)
                result.update(new_info.to_refinements())

    elif kind == CollectionKind.STRING:
        if op_name == "join":
            iterable = CollectionInfo.from_refinements(refs.get("_iterable_info", {}))
            r = analyze_str_join(info, iterable)
            result.update(r.to_refinements())
        elif op_name in ("split", "rsplit"):
            maxsplit = refs.get("_maxsplit")
            r = analyze_str_split(info, maxsplit)
            result.update(r.to_refinements())
        elif op_name == "replace":
            old_len = refs.get("_old_len", 1)
            new_len = refs.get("_new_len", 1)
            count = refs.get("_replace_count")
            r = analyze_str_replace(info, old_len, new_len, count)
            result.update(r.to_refinements())
        elif op_name in ("strip", "lstrip", "rstrip"):
            r = analyze_str_strip(info)
            result.update(r.to_refinements())
        elif op_name in ("upper", "lower", "title", "capitalize", "swapcase"):
            r = analyze_str_upper_lower(info)
            result.update(r.to_refinements())
        elif op_name == "format":
            arg_count = refs.get("_format_arg_count", 0)
            r = analyze_str_format(info, arg_count)
            result.update(r.to_refinements())
        elif op_name == "encode":
            encoding = refs.get("_encoding", "utf-8")
            r = analyze_str_encode(info, encoding)
            result.update(r.to_refinements())
        elif op_name in ("startswith", "endswith"):
            r = analyze_str_startswith_endswith(info)
            result.update(r.to_refinements())
        elif op_name in ("find", "rfind"):
            r = analyze_str_find(info)
            result.update(r.to_refinements())
        elif op_name in ("index", "rindex"):
            r = analyze_str_index_method(info)
            result.update(r.to_refinements())
        elif op_name in ("isdigit", "isalpha", "isalnum", "isspace", "isupper", "islower"):
            result["_str_return_type"] = "bool"
            result.update(info.length.to_refinements())
        elif op_name in ("center", "ljust", "rjust"):
            width = refs.get("_width", 0)
            if isinstance(width, int) and info.length.exact is not None:
                result_len = LengthInfo(exact=max(info.length.exact, width))
            else:
                result_len = LengthInfo()
            result.update(result_len.to_refinements())
        elif op_name == "zfill":
            width = refs.get("_width", 0)
            if isinstance(width, int) and info.length.exact is not None:
                result_len = LengthInfo(exact=max(info.length.exact, width))
            else:
                result_len = LengthInfo()
            result.update(result_len.to_refinements())

    return result


# ═══════════════════════════════════════════════════════════════════════════════
# Comprehension analysis
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ComprehensionInfo:
    """Information about a list/set/dict/generator comprehension."""
    kind: CollectionKind
    source_length: LengthInfo
    has_filter: bool = False
    filter_selectivity: Optional[float] = None
    element_type: Optional[str] = None
    nested_depth: int = 1

    def output_length(self) -> LengthInfo:
        """Compute the output length of this comprehension."""
        if self.nested_depth > 1:
            if self.source_length.exact is not None:
                return LengthInfo(min_length=0)
            return LengthInfo()

        if not self.has_filter:
            return self.source_length

        if self.filter_selectivity is not None:
            if self.source_length.exact is not None:
                approx = int(self.source_length.exact * self.filter_selectivity)
                return LengthInfo(min_length=0, max_length=self.source_length.exact)
            if self.source_length.max_length is not None:
                return LengthInfo(min_length=0, max_length=self.source_length.max_length)
        return filter_length(self.source_length)

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {
            "collection_kind": self.kind.value,
            "_comprehension": True,
            "_has_filter": self.has_filter,
            "_nested_depth": self.nested_depth,
        }
        refs.update(self.output_length().to_refinements())
        if self.element_type is not None:
            refs["element_type"] = self.element_type
        if self.filter_selectivity is not None:
            refs["_filter_selectivity"] = self.filter_selectivity
        return refs


# ═══════════════════════════════════════════════════════════════════════════════
# BuiltinSequencePack
# ═══════════════════════════════════════════════════════════════════════════════


class BuiltinSequencePack(TheoryPackBase):
    """Theory pack for built-in Python sequence operations (list, tuple, str).

    Extends SequenceCollectionTheoryPack with Python-specific semantics
    including element type tracking, comprehension analysis, and
    method-level operation analysis.
    """

    pack_name = "builtin_sequence"
    pack_priority = 24

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

        if not self._is_sequence_section(refs, info):
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation="not a sequence section",
            )

        # Handle comprehension sites
        if refs.get("_comprehension"):
            return self._solve_comprehension(site, section, refs)

        # Handle operation dispatch
        op_name = refs.get("sequence_op") or refs.get("collection_op")
        if op_name is not None:
            return self._solve_sequence_op(site, section, info, str(op_name))

        # Handle indexing
        if refs.get("_access_index") is not None:
            return self._solve_index_access(site, section, info)

        # Handle slicing
        if refs.get("_slice"):
            return self._solve_slice(site, section, info)

        # Default: propagate element type info
        new_refs = dict(refs)
        elem_info = ElementTypeInfo.from_refinements(refs)
        new_refs.update(elem_info.to_refinements())
        new_refs.update(info.to_refinements())

        return SolverResult(
            status=SolverStatus.REFINED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=section.trust,
                provenance=f"builtin_sequence: {info.kind.value}",
                witnesses=dict(section.witnesses),
            ),
            explanation=f"sequence {info.kind.value} analyzed",
        )

    def _solve_sequence_op(
        self, site: SiteId, section: LocalSection,
        info: CollectionInfo, op_name: str,
    ) -> SolverResult:
        refs = section.refinements
        result_refs = dispatch_sequence_op(info.kind, op_name, info, refs)

        if not result_refs:
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation=f"no handler for {info.kind.value}.{op_name}",
            )

        # Check for errors
        may_raise = result_refs.get("_may_raise") or result_refs.get("_list_op_may_raise") or ()
        if may_raise and site.kind == SiteKind.ERROR:
            return SolverResult(
                status=SolverStatus.UNSATISFIABLE,
                section=section,
                constraints_remaining=[f"may raise {e}" for e in may_raise],
                explanation=f"{op_name} may raise: {', '.join(may_raise)}",
            )

        new_refs = dict(refs)
        new_refs.update(result_refs)
        new_refs["_sequence_op_resolved"] = True

        return SolverResult(
            status=SolverStatus.SOLVED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=TrustLevel.BOUNDED_AUTO,
                provenance=f"builtin_sequence: {info.kind.value}.{op_name}",
                witnesses=dict(section.witnesses),
            ),
            explanation=f"{info.kind.value}.{op_name} analyzed",
        )

    def _solve_index_access(
        self, site: SiteId, section: LocalSection, info: CollectionInfo,
    ) -> SolverResult:
        refs = section.refinements
        idx = refs["_access_index"]

        if not isinstance(idx, int):
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation="non-integer index",
            )

        new_refs = dict(refs)
        may_raise: List[str] = []

        if info.length.exact is not None:
            if 0 <= idx < info.length.exact or -info.length.exact <= idx < 0:
                new_refs["_access_safe"] = True
            else:
                may_raise.append("IndexError")
                new_refs["_access_safe"] = False
        elif info.length.min_length is not None:
            if 0 <= idx < info.length.min_length:
                new_refs["_access_safe"] = True

        # Track element type for the result
        elem_info = ElementTypeInfo.from_refinements(refs)
        if elem_info.uniform_type is not None:
            new_refs["_result_type"] = elem_info.uniform_type
        elif elem_info.position_types:
            actual_idx = idx if idx >= 0 else (
                len(elem_info.position_types) + idx
                if info.length.exact else None
            )
            if actual_idx is not None and 0 <= actual_idx < len(elem_info.position_types):
                pos_type = elem_info.position_types[actual_idx]
                if pos_type is not None:
                    new_refs["_result_type"] = pos_type

        if may_raise:
            new_refs["_may_raise"] = tuple(may_raise)

        status = SolverStatus.SOLVED if new_refs.get("_access_safe") is True else SolverStatus.REFINED
        return SolverResult(
            status=status,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=section.trust,
                provenance=f"builtin_sequence: index[{idx}]",
                witnesses=dict(section.witnesses),
            ),
            constraints_remaining=[f"may raise {e}" for e in may_raise],
            explanation=f"index access [{idx}] on {info.kind.value}",
        )

    def _solve_slice(
        self, site: SiteId, section: LocalSection, info: CollectionInfo,
    ) -> SolverResult:
        refs = section.refinements
        start = refs.get("slice_start")
        stop = refs.get("slice_stop")
        step = refs.get("slice_step")
        result_length = slice_length(info.length, start, stop, step)

        new_refs = dict(refs)
        new_refs.update(result_length.to_refinements())
        new_refs["collection_kind"] = info.kind.value
        new_refs["_slice_resolved"] = True

        # Preserve element type
        if info.element_type is not None:
            new_refs["element_type"] = info.element_type

        return SolverResult(
            status=SolverStatus.SOLVED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=TrustLevel.BOUNDED_AUTO,
                provenance="builtin_sequence: slice",
                witnesses=dict(section.witnesses),
            ),
            explanation=f"slice [{start}:{stop}:{step}]",
        )

    def _solve_comprehension(
        self, site: SiteId, section: LocalSection, refs: Dict[str, Any],
    ) -> SolverResult:
        kind_str = refs.get("collection_kind", "list")
        try:
            kind = CollectionKind(kind_str)
        except ValueError:
            kind = CollectionKind.LIST

        source_length = LengthInfo.from_refinements(refs.get("_source_info", {}))
        comp_info = ComprehensionInfo(
            kind=kind,
            source_length=source_length,
            has_filter=refs.get("_has_filter", False),
            filter_selectivity=refs.get("_filter_selectivity"),
            element_type=refs.get("element_type"),
            nested_depth=refs.get("_nested_depth", 1),
        )

        new_refs = dict(refs)
        new_refs.update(comp_info.to_refinements())
        new_refs["_comprehension_resolved"] = True

        return SolverResult(
            status=SolverStatus.SOLVED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=TrustLevel.BOUNDED_AUTO,
                provenance=f"builtin_sequence: {kind.value} comprehension",
                witnesses=dict(section.witnesses),
            ),
            explanation=f"{kind.value} comprehension analyzed",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        restricted = morphism.restrict(section)
        info = CollectionInfo.from_refinements(section.refinements)
        elem_info = ElementTypeInfo.from_refinements(section.refinements)

        if info.kind == CollectionKind.UNKNOWN:
            return restricted

        forward_refs: Dict[str, Any] = {}
        forward_refs.update(info.to_refinements())
        forward_refs.update(elem_info.to_refinements())

        new_refs = merge_refinements(restricted.refinements, forward_refs, "meet")
        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance="builtin_sequence forward",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        refs = section.refinements
        required_refs: Dict[str, Any] = {}

        op_name = refs.get("sequence_op") or refs.get("collection_op")
        if op_name in ("pop", "index", "__getitem__", "remove"):
            required_refs["non_empty"] = True
            required_refs["min_length"] = 1

        idx = refs.get("_access_index")
        if idx is not None and isinstance(idx, int):
            if idx >= 0:
                required_refs["min_length"] = idx + 1
            else:
                required_refs["min_length"] = abs(idx)

        if refs.get("requires_non_empty"):
            required_refs["non_empty"] = True

        # For str operations that require non-empty
        if op_name in ("index", "rindex") and refs.get("collection_kind") == "str":
            required_refs["non_empty"] = True

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required_refs,
            trust=TrustLevel.RESIDUAL,
            provenance="builtin_sequence pullback",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        name = error_site.name.lower()
        if "index" in name or "getitem" in name:
            return "index is within bounds"
        if "pop" in name:
            return "sequence is non-empty"
        if "remove" in name:
            return "element exists in sequence"
        if "valueerror" in name:
            return "value is valid for operation"
        return f"sequence precondition for {error_site.name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        refs = section.refinements
        if refs.get("_sequence_op_resolved") or refs.get("_comprehension_resolved"):
            return BoundaryClassification.FULLY_PROVEN
        if refs.get("_access_safe") is True:
            return BoundaryClassification.FULLY_PROVEN
        if refs.get("_access_safe") is False:
            return BoundaryClassification.INCONSISTENT
        info = CollectionInfo.from_refinements(refs)
        if info.length.is_exact:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        return BoundaryClassification.REQUIRES_PROOF

    def _is_sequence_section(self, refs: Dict[str, Any], info: CollectionInfo) -> bool:
        """Check if this section is relevant to the builtin sequence pack."""
        if info.kind in (CollectionKind.LIST, CollectionKind.TUPLE, CollectionKind.STRING):
            return True
        seq_keys = {
            "sequence_op", "_comprehension", "_access_index", "_slice",
            "_element_type_status", "_position_types", "element_type",
        }
        return bool(seq_keys & set(refs.keys()))
