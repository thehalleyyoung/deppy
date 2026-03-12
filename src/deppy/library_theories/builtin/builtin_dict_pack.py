"""Built-in Python dictionary operations theory pack.

Provides refined type analysis for dict operations including key
lookup, mutation, iteration, merging, and comprehension. Tracks
key sets, value types, default factories, and missing-key safety.
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
)
from ..sequence_collection_theory import (
    CollectionKind,
    LengthInfo,
    CollectionInfo,
    dict_update_length,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Key tracking
# ═══════════════════════════════════════════════════════════════════════════════


class KeyPresence(Enum):
    """Whether a key is known to be present in a dictionary."""
    PRESENT = "present"
    ABSENT = "absent"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class KeyInfo:
    """Information about a specific key in a dictionary."""
    key: str
    presence: KeyPresence = KeyPresence.UNKNOWN
    value_type: Optional[str] = None
    is_default: bool = False


@dataclass
class DictTypeInfo:
    """Complete type information for a dictionary."""
    key_type: Optional[str] = None
    value_type: Optional[str] = None
    length: LengthInfo = field(default_factory=LengthInfo)
    known_keys: Dict[str, KeyInfo] = field(default_factory=dict)
    has_default_factory: bool = False
    default_factory_type: Optional[str] = None
    is_ordered: bool = True  # Python 3.7+ dicts maintain insertion order
    is_typed_dict: bool = False
    required_keys: FrozenSet[str] = frozenset()
    optional_keys: FrozenSet[str] = frozenset()

    def add_key(self, key: str, value_type: Optional[str] = None) -> None:
        """Record that a key is known to be present."""
        self.known_keys[key] = KeyInfo(
            key=key, presence=KeyPresence.PRESENT, value_type=value_type,
        )

    def remove_key(self, key: str) -> None:
        """Record that a key has been removed."""
        self.known_keys[key] = KeyInfo(
            key=key, presence=KeyPresence.ABSENT,
        )

    def key_presence(self, key: str) -> KeyPresence:
        """Check if a key is known to be present, absent, or unknown."""
        info = self.known_keys.get(key)
        if info is not None:
            return info.presence
        return KeyPresence.UNKNOWN

    def key_value_type(self, key: str) -> Optional[str]:
        """Get the value type for a specific known key."""
        info = self.known_keys.get(key)
        if info is not None and info.value_type is not None:
            return info.value_type
        return self.value_type

    @property
    def present_keys(self) -> Set[str]:
        """Set of keys known to be present."""
        return {k for k, info in self.known_keys.items()
                if info.presence == KeyPresence.PRESENT}

    @property
    def absent_keys(self) -> Set[str]:
        """Set of keys known to be absent."""
        return {k for k, info in self.known_keys.items()
                if info.presence == KeyPresence.ABSENT}

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {"collection_kind": "dict"}
        refs.update(self.length.to_refinements())
        if self.key_type is not None:
            refs["key_type"] = self.key_type
        if self.value_type is not None:
            refs["value_type"] = self.value_type
        if self.known_keys:
            refs["_known_keys"] = {
                k: {"presence": info.presence.value, "value_type": info.value_type}
                for k, info in self.known_keys.items()
            }
        if self.has_default_factory:
            refs["_has_default_factory"] = True
            if self.default_factory_type is not None:
                refs["_default_factory_type"] = self.default_factory_type
        refs["_is_ordered"] = self.is_ordered
        if self.is_typed_dict:
            refs["_is_typed_dict"] = True
            refs["_required_keys"] = sorted(self.required_keys)
            refs["_optional_keys"] = sorted(self.optional_keys)
        return refs

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> DictTypeInfo:
        known_keys: Dict[str, KeyInfo] = {}
        raw_keys = refs.get("_known_keys", {})
        if isinstance(raw_keys, dict):
            for k, info_data in raw_keys.items():
                if isinstance(info_data, dict):
                    try:
                        presence = KeyPresence(info_data.get("presence", "unknown"))
                    except ValueError:
                        presence = KeyPresence.UNKNOWN
                    known_keys[k] = KeyInfo(
                        key=k,
                        presence=presence,
                        value_type=info_data.get("value_type"),
                    )
        req_keys = refs.get("_required_keys", [])
        opt_keys = refs.get("_optional_keys", [])
        return DictTypeInfo(
            key_type=refs.get("key_type"),
            value_type=refs.get("value_type"),
            length=LengthInfo.from_refinements(refs),
            known_keys=known_keys,
            has_default_factory=refs.get("_has_default_factory", False),
            default_factory_type=refs.get("_default_factory_type"),
            is_ordered=refs.get("_is_ordered", True),
            is_typed_dict=refs.get("_is_typed_dict", False),
            required_keys=frozenset(req_keys) if isinstance(req_keys, (list, set)) else frozenset(),
            optional_keys=frozenset(opt_keys) if isinstance(opt_keys, (list, set)) else frozenset(),
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Dict operation analysis
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class DictOpResult:
    """Result of analyzing a dict operation."""
    dict_info: DictTypeInfo
    return_type: Optional[str] = None
    returns_value: bool = False
    is_in_place: bool = False
    may_raise: Tuple[str, ...] = ()

    def to_refinements(self) -> Dict[str, Any]:
        refs = self.dict_info.to_refinements()
        if self.return_type is not None:
            refs["_dict_op_return_type"] = self.return_type
        refs["_dict_op_returns_value"] = self.returns_value
        refs["_dict_op_in_place"] = self.is_in_place
        if self.may_raise:
            refs["_dict_op_may_raise"] = self.may_raise
        return refs


def analyze_dict_getitem(info: DictTypeInfo, key: Optional[str]) -> DictOpResult:
    """Analyze dict[key] access."""
    may_raise: Tuple[str, ...] = ()
    return_type = info.value_type

    if key is not None:
        presence = info.key_presence(key)
        if presence == KeyPresence.ABSENT and not info.has_default_factory:
            may_raise = ("KeyError",)
        elif presence == KeyPresence.UNKNOWN and not info.has_default_factory:
            may_raise = ("KeyError",)
        vtype = info.key_value_type(key)
        if vtype is not None:
            return_type = vtype

    if info.has_default_factory:
        may_raise = ()
        if return_type is None and info.default_factory_type is not None:
            return_type = info.default_factory_type

    return DictOpResult(
        dict_info=info, return_type=return_type,
        returns_value=True, may_raise=may_raise,
    )


def analyze_dict_setitem(
    info: DictTypeInfo, key: Optional[str], value_type: Optional[str]
) -> DictOpResult:
    """Analyze dict[key] = value assignment."""
    new_info = DictTypeInfo(
        key_type=info.key_type,
        value_type=info.value_type,
        length=info.length,
        known_keys=dict(info.known_keys),
        has_default_factory=info.has_default_factory,
        default_factory_type=info.default_factory_type,
        is_ordered=info.is_ordered,
        is_typed_dict=info.is_typed_dict,
        required_keys=info.required_keys,
        optional_keys=info.optional_keys,
    )
    if key is not None:
        was_present = info.key_presence(key) == KeyPresence.PRESENT
        new_info.add_key(key, value_type)
        if not was_present:
            if info.length.exact is not None:
                new_info.length = LengthInfo(exact=info.length.exact + 1)
            else:
                lo = (info.length.min_length or 0) + 1
                hi = info.length.max_length + 1 if info.length.max_length is not None else None
                new_info.length = LengthInfo(
                    min_length=lo if lo > 0 else None, max_length=hi,
                )
    return DictOpResult(
        dict_info=new_info, is_in_place=True,
    )


def analyze_dict_delitem(info: DictTypeInfo, key: Optional[str]) -> DictOpResult:
    """Analyze del dict[key]."""
    may_raise: Tuple[str, ...] = ()
    new_info = DictTypeInfo(
        key_type=info.key_type,
        value_type=info.value_type,
        length=info.length,
        known_keys=dict(info.known_keys),
        has_default_factory=info.has_default_factory,
        default_factory_type=info.default_factory_type,
        is_ordered=info.is_ordered,
        is_typed_dict=info.is_typed_dict,
        required_keys=info.required_keys,
        optional_keys=info.optional_keys,
    )
    if key is not None:
        presence = info.key_presence(key)
        if presence == KeyPresence.ABSENT:
            may_raise = ("KeyError",)
        elif presence == KeyPresence.UNKNOWN:
            may_raise = ("KeyError",)
        new_info.remove_key(key)
        if info.length.exact is not None:
            new_info.length = LengthInfo(exact=max(0, info.length.exact - 1))
        else:
            lo = max(0, (info.length.min_length or 0) - 1)
            hi = max(0, info.length.max_length - 1) if info.length.max_length is not None else None
            new_info.length = LengthInfo(
                min_length=lo if lo > 0 else None, max_length=hi,
            )
    else:
        may_raise = ("KeyError",)

    return DictOpResult(
        dict_info=new_info, is_in_place=True, may_raise=may_raise,
    )


def analyze_dict_get(
    info: DictTypeInfo, key: Optional[str], has_default: bool = False
) -> DictOpResult:
    """Analyze dict.get(key, default) -- never raises KeyError."""
    return_type = info.value_type
    if key is not None:
        vtype = info.key_value_type(key)
        if vtype is not None:
            return_type = vtype
    if has_default:
        if return_type is not None:
            return_type = f"Optional[{return_type}]"
    else:
        return_type = f"Optional[{return_type}]" if return_type else "Optional[Any]"
    return DictOpResult(
        dict_info=info, return_type=return_type, returns_value=True,
    )


def analyze_dict_setdefault(
    info: DictTypeInfo, key: Optional[str], default_type: Optional[str] = None
) -> DictOpResult:
    """Analyze dict.setdefault(key, default)."""
    new_info = DictTypeInfo(
        key_type=info.key_type,
        value_type=info.value_type,
        length=info.length,
        known_keys=dict(info.known_keys),
        has_default_factory=info.has_default_factory,
        default_factory_type=info.default_factory_type,
        is_ordered=info.is_ordered,
        is_typed_dict=info.is_typed_dict,
        required_keys=info.required_keys,
        optional_keys=info.optional_keys,
    )
    return_type = info.value_type
    if key is not None:
        presence = info.key_presence(key)
        if presence == KeyPresence.PRESENT:
            vtype = info.key_value_type(key)
            if vtype is not None:
                return_type = vtype
        else:
            new_info.add_key(key, default_type or info.value_type)
            return_type = default_type or info.value_type
            if presence != KeyPresence.PRESENT:
                if info.length.exact is not None:
                    new_info.length = LengthInfo(exact=info.length.exact + 1)
    return DictOpResult(
        dict_info=new_info, return_type=return_type, returns_value=True, is_in_place=True,
    )


def analyze_dict_pop(
    info: DictTypeInfo, key: Optional[str], has_default: bool = False
) -> DictOpResult:
    """Analyze dict.pop(key, [default])."""
    may_raise: Tuple[str, ...] = ()
    new_info = DictTypeInfo(
        key_type=info.key_type,
        value_type=info.value_type,
        length=info.length,
        known_keys=dict(info.known_keys),
        has_default_factory=info.has_default_factory,
        default_factory_type=info.default_factory_type,
        is_ordered=info.is_ordered,
        is_typed_dict=info.is_typed_dict,
        required_keys=info.required_keys,
        optional_keys=info.optional_keys,
    )
    return_type = info.value_type

    if key is not None:
        presence = info.key_presence(key)
        if presence == KeyPresence.ABSENT and not has_default:
            may_raise = ("KeyError",)
        elif presence == KeyPresence.UNKNOWN and not has_default:
            may_raise = ("KeyError",)
        vtype = info.key_value_type(key)
        if vtype is not None:
            return_type = vtype
        new_info.remove_key(key)
        if info.length.exact is not None:
            new_info.length = LengthInfo(exact=max(0, info.length.exact - 1))
    elif not has_default:
        may_raise = ("KeyError",)

    return DictOpResult(
        dict_info=new_info, return_type=return_type,
        returns_value=True, is_in_place=True, may_raise=may_raise,
    )


def analyze_dict_popitem(info: DictTypeInfo) -> DictOpResult:
    """Analyze dict.popitem() -- raises KeyError if empty."""
    may_raise: Tuple[str, ...] = ()
    if info.length.is_known_empty:
        may_raise = ("KeyError",)
    new_length = LengthInfo(
        exact=max(0, info.length.exact - 1) if info.length.exact is not None else None,
        min_length=max(0, (info.length.min_length or 0) - 1) or None,
        max_length=max(0, info.length.max_length - 1) if info.length.max_length is not None else None,
    )
    new_info = DictTypeInfo(
        key_type=info.key_type,
        value_type=info.value_type,
        length=new_length,
        known_keys=dict(info.known_keys),
        has_default_factory=info.has_default_factory,
        default_factory_type=info.default_factory_type,
        is_ordered=info.is_ordered,
    )
    kt = info.key_type or "Any"
    vt = info.value_type or "Any"
    return DictOpResult(
        dict_info=new_info, return_type=f"Tuple[{kt}, {vt}]",
        returns_value=True, is_in_place=True, may_raise=may_raise,
    )


def analyze_dict_update(info: DictTypeInfo, other: DictTypeInfo) -> DictOpResult:
    """Analyze dict.update(other)."""
    new_info = DictTypeInfo(
        key_type=info.key_type,
        value_type=info.value_type,
        length=dict_update_length(info.length, other.length) if info.length and other.length else info.length,
        known_keys=dict(info.known_keys),
        has_default_factory=info.has_default_factory,
        default_factory_type=info.default_factory_type,
        is_ordered=info.is_ordered,
        is_typed_dict=info.is_typed_dict,
        required_keys=info.required_keys,
        optional_keys=info.optional_keys,
    )
    # Merge known keys from other
    for k, ki in other.known_keys.items():
        if ki.presence == KeyPresence.PRESENT:
            new_info.add_key(k, ki.value_type)

    return DictOpResult(
        dict_info=new_info, is_in_place=True, return_type="None",
    )


def analyze_dict_clear(info: DictTypeInfo) -> DictOpResult:
    """Analyze dict.clear()."""
    new_info = DictTypeInfo(
        key_type=info.key_type,
        value_type=info.value_type,
        length=LengthInfo(exact=0),
        has_default_factory=info.has_default_factory,
        default_factory_type=info.default_factory_type,
        is_ordered=info.is_ordered,
    )
    return DictOpResult(
        dict_info=new_info, is_in_place=True, return_type="None",
    )


def analyze_dict_copy(info: DictTypeInfo) -> DictOpResult:
    """Analyze dict.copy()."""
    return DictOpResult(
        dict_info=info, return_type="dict", returns_value=True,
    )


def analyze_dict_keys(info: DictTypeInfo) -> DictOpResult:
    """Analyze dict.keys()."""
    return DictOpResult(
        dict_info=info,
        return_type=f"dict_keys[{info.key_type or 'Any'}]",
        returns_value=True,
    )


def analyze_dict_values(info: DictTypeInfo) -> DictOpResult:
    """Analyze dict.values()."""
    return DictOpResult(
        dict_info=info,
        return_type=f"dict_values[{info.value_type or 'Any'}]",
        returns_value=True,
    )


def analyze_dict_items(info: DictTypeInfo) -> DictOpResult:
    """Analyze dict.items()."""
    kt = info.key_type or "Any"
    vt = info.value_type or "Any"
    return DictOpResult(
        dict_info=info,
        return_type=f"dict_items[{kt}, {vt}]",
        returns_value=True,
    )


def analyze_dict_merge(a: DictTypeInfo, b: DictTypeInfo) -> DictOpResult:
    """Analyze a | b (dict merge, Python 3.9+)."""
    new_info = DictTypeInfo(
        key_type=a.key_type or b.key_type,
        value_type=a.value_type or b.value_type,
        length=dict_update_length(a.length, b.length),
        known_keys=dict(a.known_keys),
        is_ordered=True,
    )
    for k, ki in b.known_keys.items():
        if ki.presence == KeyPresence.PRESENT:
            new_info.add_key(k, ki.value_type)

    return DictOpResult(
        dict_info=new_info, return_type="dict", returns_value=True,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# TypedDict validation
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class TypedDictValidation:
    """Result of validating a dict against a TypedDict specification."""
    is_valid: bool
    missing_required: Tuple[str, ...] = ()
    extra_keys: Tuple[str, ...] = ()
    type_mismatches: Tuple[Tuple[str, str, str], ...] = ()  # (key, expected, actual)
    explanation: str = ""

    def to_refinements(self) -> Dict[str, Any]:
        return {
            "_typed_dict_valid": self.is_valid,
            "_missing_required": self.missing_required,
            "_extra_keys": self.extra_keys,
            "_type_mismatches": self.type_mismatches,
            "_typed_dict_explanation": self.explanation,
        }


def validate_typed_dict(info: DictTypeInfo) -> TypedDictValidation:
    """Validate a dictionary against its TypedDict specification."""
    if not info.is_typed_dict:
        return TypedDictValidation(is_valid=True, explanation="not a TypedDict")

    present = info.present_keys
    missing = []
    for rk in sorted(info.required_keys):
        if rk not in present and info.key_presence(rk) != KeyPresence.PRESENT:
            missing.append(rk)

    all_valid_keys = info.required_keys | info.optional_keys
    extra = []
    for pk in sorted(present):
        if pk not in all_valid_keys:
            extra.append(pk)

    type_mismatches: List[Tuple[str, str, str]] = []
    for k, ki in info.known_keys.items():
        if ki.presence == KeyPresence.PRESENT and ki.value_type is not None:
            expected = info.key_value_type(k)
            if expected is not None and expected != ki.value_type:
                type_mismatches.append((k, expected, ki.value_type))

    is_valid = not missing and not extra and not type_mismatches
    parts = []
    if missing:
        parts.append(f"missing required keys: {', '.join(missing)}")
    if extra:
        parts.append(f"extra keys: {', '.join(extra)}")
    if type_mismatches:
        parts.append(f"type mismatches: {len(type_mismatches)}")

    return TypedDictValidation(
        is_valid=is_valid,
        missing_required=tuple(missing),
        extra_keys=tuple(extra),
        type_mismatches=tuple(type_mismatches),
        explanation="; ".join(parts) if parts else "valid TypedDict",
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Dict operation dispatch
# ═══════════════════════════════════════════════════════════════════════════════


def dispatch_dict_op(
    op_name: str, info: DictTypeInfo, refs: Dict[str, Any]
) -> DictOpResult:
    """Dispatch a dict operation and return the analysis result."""
    key = refs.get("_key")
    if isinstance(key, str):
        key_str: Optional[str] = key
    else:
        key_str = str(key) if key is not None else None

    if op_name == "__getitem__":
        return analyze_dict_getitem(info, key_str)
    elif op_name == "__setitem__":
        vtype = refs.get("_value_type")
        return analyze_dict_setitem(info, key_str, vtype if isinstance(vtype, str) else None)
    elif op_name == "__delitem__":
        return analyze_dict_delitem(info, key_str)
    elif op_name == "get":
        has_default = refs.get("_has_default", False)
        return analyze_dict_get(info, key_str, has_default)
    elif op_name == "setdefault":
        dtype = refs.get("_default_type")
        return analyze_dict_setdefault(info, key_str, dtype if isinstance(dtype, str) else None)
    elif op_name == "pop":
        has_default = refs.get("_has_default", False)
        return analyze_dict_pop(info, key_str, has_default)
    elif op_name == "popitem":
        return analyze_dict_popitem(info)
    elif op_name == "update":
        other = DictTypeInfo.from_refinements(refs.get("_other_info", {}))
        return analyze_dict_update(info, other)
    elif op_name == "clear":
        return analyze_dict_clear(info)
    elif op_name == "copy":
        return analyze_dict_copy(info)
    elif op_name == "keys":
        return analyze_dict_keys(info)
    elif op_name == "values":
        return analyze_dict_values(info)
    elif op_name == "items":
        return analyze_dict_items(info)
    elif op_name in ("__or__", "merge", "|"):
        other = DictTypeInfo.from_refinements(refs.get("_other_info", {}))
        return analyze_dict_merge(info, other)
    elif op_name == "__contains__":
        return DictOpResult(dict_info=info, return_type="bool", returns_value=True)
    elif op_name == "__len__":
        return DictOpResult(dict_info=info, return_type="int", returns_value=True)
    elif op_name == "__iter__":
        return DictOpResult(
            dict_info=info,
            return_type=f"Iterator[{info.key_type or 'Any'}]",
            returns_value=True,
        )

    # Unknown operation - return unchanged
    return DictOpResult(dict_info=info)


# ═══════════════════════════════════════════════════════════════════════════════
# BuiltinDictPack
# ═══════════════════════════════════════════════════════════════════════════════


class BuiltinDictPack(TheoryPackBase):
    """Theory pack for built-in Python dictionary operations.

    Tracks key presence, value types, TypedDict validation, and
    method-level operation analysis for dict, defaultdict, OrderedDict,
    and Counter types.
    """

    pack_name = "builtin_dict"
    pack_priority = 25

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
        if not self._is_dict_section(refs):
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation="not a dict section",
            )

        info = DictTypeInfo.from_refinements(refs)

        # Handle TypedDict validation
        if info.is_typed_dict and refs.get("_validate_typed_dict"):
            return self._solve_typed_dict_validation(site, section, info)

        # Handle operation dispatch
        op_name = refs.get("dict_op") or refs.get("collection_op")
        if op_name is not None:
            return self._solve_dict_op(site, section, info, str(op_name))

        # Handle key containment check
        if refs.get("_check_key") is not None:
            return self._solve_key_check(site, section, info)

        # Default: propagate dict type info
        new_refs = dict(refs)
        new_refs.update(info.to_refinements())

        return SolverResult(
            status=SolverStatus.REFINED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=section.trust,
                provenance="builtin_dict: analyzed",
                witnesses=dict(section.witnesses),
            ),
            explanation=f"dict analyzed: {len(info.present_keys)} known keys",
        )

    def _solve_dict_op(
        self, site: SiteId, section: LocalSection,
        info: DictTypeInfo, op_name: str,
    ) -> SolverResult:
        refs = section.refinements
        result = dispatch_dict_op(op_name, info, refs)

        # Check for errors
        if result.may_raise and site.kind == SiteKind.ERROR:
            return SolverResult(
                status=SolverStatus.UNSATISFIABLE,
                section=section,
                constraints_remaining=[f"may raise {e}" for e in result.may_raise],
                explanation=f"dict.{op_name} may raise: {', '.join(result.may_raise)}",
            )

        new_refs = dict(refs)
        new_refs.update(result.to_refinements())
        new_refs["_dict_op_resolved"] = True

        trust = TrustLevel.BOUNDED_AUTO
        if result.may_raise:
            trust = section.trust

        return SolverResult(
            status=SolverStatus.SOLVED if not result.may_raise else SolverStatus.REFINED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=trust,
                provenance=f"builtin_dict: {op_name}",
                witnesses=dict(section.witnesses),
            ),
            constraints_remaining=[f"may raise {e}" for e in result.may_raise],
            explanation=f"dict.{op_name} analyzed",
        )

    def _solve_key_check(
        self, site: SiteId, section: LocalSection, info: DictTypeInfo,
    ) -> SolverResult:
        refs = section.refinements
        key = refs["_check_key"]
        key_str = str(key) if key is not None else None

        new_refs = dict(refs)

        if key_str is not None:
            presence = info.key_presence(key_str)
            if presence == KeyPresence.PRESENT:
                new_refs["_key_present"] = True
                new_refs["_key_check_result"] = "present"
            elif presence == KeyPresence.ABSENT:
                new_refs["_key_present"] = False
                new_refs["_key_check_result"] = "absent"
            else:
                new_refs["_key_check_result"] = "unknown"

        return SolverResult(
            status=SolverStatus.SOLVED if new_refs.get("_key_check_result") != "unknown" else SolverStatus.REFINED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=section.trust,
                provenance="builtin_dict: key check",
                witnesses=dict(section.witnesses),
            ),
            explanation=f"key check: {key_str} is {new_refs.get('_key_check_result', 'unknown')}",
        )

    def _solve_typed_dict_validation(
        self, site: SiteId, section: LocalSection, info: DictTypeInfo,
    ) -> SolverResult:
        validation = validate_typed_dict(info)
        new_refs = dict(section.refinements)
        new_refs.update(validation.to_refinements())
        new_refs.update(info.to_refinements())

        if not validation.is_valid:
            return SolverResult(
                status=SolverStatus.UNSATISFIABLE,
                section=LocalSection(
                    site_id=section.site_id,
                    carrier_type=section.carrier_type,
                    refinements=new_refs,
                    trust=section.trust,
                    provenance=f"builtin_dict: TypedDict invalid - {validation.explanation}",
                    witnesses=dict(section.witnesses),
                ),
                constraints_remaining=[validation.explanation],
                explanation=f"TypedDict validation failed: {validation.explanation}",
            )

        return SolverResult(
            status=SolverStatus.SOLVED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=TrustLevel.BOUNDED_AUTO,
                provenance="builtin_dict: TypedDict valid",
                witnesses=dict(section.witnesses),
            ),
            explanation="TypedDict validation passed",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        restricted = morphism.restrict(section)
        info = DictTypeInfo.from_refinements(section.refinements)

        forward_refs = info.to_refinements()
        new_refs = merge_refinements(restricted.refinements, forward_refs, "meet")

        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance="builtin_dict forward",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        refs = section.refinements
        required_refs: Dict[str, Any] = {}

        op_name = refs.get("dict_op") or refs.get("collection_op")
        if op_name in ("__getitem__", "__delitem__", "pop"):
            key = refs.get("_key")
            has_default = refs.get("_has_default", False)
            if key is not None and not has_default:
                required_refs[f"_requires_key_{key}"] = True
            if not refs.get("_has_default_factory"):
                required_refs["non_empty"] = True

        if op_name == "popitem":
            required_refs["non_empty"] = True
            required_refs["min_length"] = 1

        # TypedDict requirements
        if refs.get("_is_typed_dict"):
            req_keys = refs.get("_required_keys", [])
            if isinstance(req_keys, (list, set)):
                for rk in req_keys:
                    required_refs[f"_requires_key_{rk}"] = True

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required_refs,
            trust=TrustLevel.RESIDUAL,
            provenance="builtin_dict pullback",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        name = error_site.name.lower()
        if "key" in name or "getitem" in name:
            return "key exists in dictionary"
        if "popitem" in name:
            return "dictionary is non-empty"
        if "typeddict" in name:
            return "all required keys present with correct types"
        return f"dict precondition for {error_site.name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        refs = section.refinements
        if refs.get("_dict_op_resolved"):
            may_raise = refs.get("_dict_op_may_raise", ())
            if not may_raise:
                return BoundaryClassification.FULLY_PROVEN
            return BoundaryClassification.REQUIRES_PROOF

        if refs.get("_typed_dict_valid") is True:
            return BoundaryClassification.FULLY_PROVEN
        if refs.get("_typed_dict_valid") is False:
            return BoundaryClassification.INCONSISTENT

        info = DictTypeInfo.from_refinements(refs)
        if info.length.is_exact and info.present_keys:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        return BoundaryClassification.REQUIRES_PROOF

    def _is_dict_section(self, refs: Dict[str, Any]) -> bool:
        """Check if this section is relevant to the dict pack."""
        if refs.get("collection_kind") == "dict":
            return True
        dict_keys = {
            "dict_op", "_known_keys", "key_type", "value_type",
            "_is_typed_dict", "_has_default_factory", "_check_key",
            "_validate_typed_dict",
        }
        return bool(dict_keys & set(refs.keys()))
