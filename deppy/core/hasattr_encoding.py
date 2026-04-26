"""Per-type ``hasattr`` Z3 encoding.

Audit fix #10
=============

Before this module the Z3 encoder collapsed *every* ``hasattr(x, name)``
call to ``z3.BoolVal(True)``::

    if fn.id == "hasattr" and len(node.args) == 2:
        return z3.BoolVal(True)

This was unsound — the encoder claimed that ``hasattr(x: int, 'append')``
held, even though ``int`` has no ``append`` attribute.  Anywhere downstream
checked ``hasattr`` to decide whether an attribute access was safe, the
SMT layer would say "yes, safe" regardless of the actual class.

The fix: a per-type attribute table built from Python's built-in
classes plus protocol families (Mapping, Sequence, Set, Iterable, …).
Given the receiver's type and the attribute name we return a precise
Z3 truth value:

* known type, attribute is present  → ``BoolVal(True)``
* known type, attribute is absent   → ``BoolVal(False)``
* opaque type / unknown class       → an *uninterpreted* Bool
  predicate ``hasattr_<sort>__<name>``, so Z3 can reason
  symbolically (``hasattr(x, 'foo') ∧ ¬ hasattr(x, 'foo')`` is still
  contradictory; the predicate is *deterministic* per (type, name)).

For Union types (``Optional[T]``, ``T | U``) the result is the
disjunction over arms — ``hasattr(x: int | str, 'upper')`` is True
only on the ``str`` arm but the disjunction is True overall (Z3
considers the predicate over both arms).  For the pessimistic
direction (``hasattr(x: int | str, 'upper') ⟹ ...``) Z3 still
needs an arm-specific narrowing — that's handled in the higher-
level isinstance / type() lowering.

Public API
----------

::

    table = HasattrTable.default()
    has = table.has_attribute(type_name, attr_name)
    # has ∈ {Tristate.YES, Tristate.NO, Tristate.UNKNOWN}

    encode_hasattr(receiver_type, attr_name, *,
                   sort_name: str, z3_module) -> z3.Bool
"""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Iterable, Optional


class Tristate(str, Enum):
    """Three-valued result of an attribute-presence query."""
    YES = "yes"
    NO = "no"
    UNKNOWN = "unknown"


# ─────────────────────────────────────────────────────────────────────
#  Built-in type → attribute table
# ─────────────────────────────────────────────────────────────────────


# Universal attributes — present on every Python object via
# ``object.__init__`` / type machinery.  Conservative inclusion: any
# attribute named in a dunder pattern that *every* object has.
_OBJECT_ATTRS = frozenset({
    "__class__", "__dict__", "__doc__", "__init__",
    "__init_subclass__", "__subclasshook__",
    "__getattribute__", "__setattr__", "__delattr__",
    "__hash__", "__eq__", "__ne__", "__str__", "__repr__",
    "__sizeof__", "__reduce__", "__reduce_ex__", "__format__",
    "__dir__", "__new__", "__module__",
})


_INT_ATTRS = _OBJECT_ATTRS | frozenset({
    "__abs__", "__add__", "__sub__", "__mul__", "__floordiv__",
    "__mod__", "__divmod__", "__pow__", "__lshift__", "__rshift__",
    "__and__", "__or__", "__xor__", "__neg__", "__pos__",
    "__invert__", "__bool__", "__index__", "__int__", "__float__",
    "__complex__", "__trunc__", "__round__", "__floor__", "__ceil__",
    "__lt__", "__le__", "__gt__", "__ge__",
    "bit_length", "bit_count", "to_bytes", "from_bytes",
    "real", "imag", "numerator", "denominator", "conjugate",
    "as_integer_ratio",
})


_FLOAT_ATTRS = _OBJECT_ATTRS | frozenset({
    "__abs__", "__add__", "__sub__", "__mul__", "__truediv__",
    "__floordiv__", "__mod__", "__divmod__", "__pow__",
    "__neg__", "__pos__", "__bool__", "__int__", "__float__",
    "__complex__", "__round__", "__lt__", "__le__", "__gt__", "__ge__",
    "real", "imag", "conjugate", "is_integer", "as_integer_ratio",
    "fromhex", "hex",
})


_BOOL_ATTRS = _INT_ATTRS  # bool is a subclass of int


_STR_ATTRS = _OBJECT_ATTRS | frozenset({
    "__add__", "__mul__", "__contains__", "__iter__", "__len__",
    "__getitem__", "__lt__", "__le__", "__gt__", "__ge__",
    "capitalize", "casefold", "center", "count", "encode",
    "endswith", "expandtabs", "find", "format", "format_map",
    "index", "isalnum", "isalpha", "isascii", "isdecimal",
    "isdigit", "isidentifier", "islower", "isnumeric",
    "isprintable", "isspace", "istitle", "isupper", "join",
    "ljust", "lower", "lstrip", "maketrans", "partition",
    "removeprefix", "removesuffix", "replace", "rfind", "rindex",
    "rjust", "rpartition", "rsplit", "rstrip", "split",
    "splitlines", "startswith", "strip", "swapcase", "title",
    "translate", "upper", "zfill",
})


_BYTES_ATTRS = _OBJECT_ATTRS | frozenset({
    "__add__", "__mul__", "__contains__", "__iter__", "__len__",
    "__getitem__", "decode", "endswith", "find", "fromhex",
    "hex", "index", "isalnum", "isalpha", "isascii", "isdigit",
    "islower", "isspace", "istitle", "isupper", "join",
    "lower", "lstrip", "maketrans", "partition", "removeprefix",
    "removesuffix", "replace", "rfind", "rindex", "rpartition",
    "rsplit", "rstrip", "split", "splitlines", "startswith",
    "strip", "swapcase", "title", "translate", "upper", "zfill",
    "capitalize", "center", "count", "expandtabs", "ljust", "rjust",
})


_BYTEARRAY_ATTRS = _BYTES_ATTRS | frozenset({
    "__setitem__", "__delitem__", "__iadd__", "__imul__",
    "append", "clear", "copy", "extend", "insert", "pop",
    "remove", "reverse",
})


_LIST_ATTRS = _OBJECT_ATTRS | frozenset({
    "__add__", "__mul__", "__contains__", "__iter__", "__len__",
    "__getitem__", "__setitem__", "__delitem__", "__iadd__",
    "__imul__", "__lt__", "__le__", "__gt__", "__ge__",
    "append", "clear", "copy", "count", "extend", "index",
    "insert", "pop", "remove", "reverse", "sort",
})


_TUPLE_ATTRS = _OBJECT_ATTRS | frozenset({
    "__add__", "__mul__", "__contains__", "__iter__", "__len__",
    "__getitem__", "__lt__", "__le__", "__gt__", "__ge__",
    "count", "index",
})


_DICT_ATTRS = _OBJECT_ATTRS | frozenset({
    "__contains__", "__iter__", "__len__", "__getitem__",
    "__setitem__", "__delitem__", "__or__", "__ior__", "__ror__",
    "clear", "copy", "fromkeys", "get", "items", "keys",
    "pop", "popitem", "setdefault", "update", "values",
})


_SET_ATTRS = _OBJECT_ATTRS | frozenset({
    "__contains__", "__iter__", "__len__", "__and__", "__or__",
    "__xor__", "__sub__", "__iand__", "__ior__", "__ixor__",
    "__isub__", "__lt__", "__le__", "__gt__", "__ge__",
    "add", "clear", "copy", "difference", "difference_update",
    "discard", "intersection", "intersection_update", "isdisjoint",
    "issubset", "issuperset", "pop", "remove", "symmetric_difference",
    "symmetric_difference_update", "union", "update",
})


_FROZENSET_ATTRS = _OBJECT_ATTRS | frozenset({
    "__contains__", "__iter__", "__len__", "__and__", "__or__",
    "__xor__", "__sub__", "__lt__", "__le__", "__gt__", "__ge__",
    "copy", "difference", "intersection", "isdisjoint",
    "issubset", "issuperset", "symmetric_difference", "union",
})


_NONE_ATTRS = _OBJECT_ATTRS | frozenset({
    "__bool__",
})


_RANGE_ATTRS = _OBJECT_ATTRS | frozenset({
    "__contains__", "__iter__", "__len__", "__getitem__",
    "__reversed__", "count", "index", "start", "stop", "step",
})


_FUNCTION_ATTRS = _OBJECT_ATTRS | frozenset({
    "__call__", "__name__", "__qualname__", "__defaults__",
    "__code__", "__globals__", "__closure__", "__annotations__",
    "__kwdefaults__", "__wrapped__", "__get__",
})


# Public attribute table.
@dataclass(frozen=True)
class HasattrTable:
    """A mapping from Python type names to their attribute sets."""

    by_type: dict[str, frozenset[str]]
    type_aliases: dict[str, str]

    @classmethod
    def default(cls) -> "HasattrTable":
        """Default table seeded with built-in Python types."""
        return cls(
            by_type=dict(_DEFAULT_TYPE_TO_ATTRS),
            type_aliases=dict(_DEFAULT_TYPE_ALIASES),
        )

    def with_class(
        self, name: str, attrs: Iterable[str],
    ) -> "HasattrTable":
        """Return a new table with ``name`` mapped to ``attrs``.

        Used by the analyser when it discovers a user-defined class
        and parses its body for declared attributes.
        """
        new_by_type = dict(self.by_type)
        new_by_type[name] = frozenset(attrs) | _OBJECT_ATTRS
        return HasattrTable(
            by_type=new_by_type,
            type_aliases=dict(self.type_aliases),
        )

    def known_types(self) -> set[str]:
        return set(self.by_type)

    def resolve(self, name: str) -> Optional[str]:
        """Resolve a possibly-aliased type name to its canonical form."""
        if name in self.by_type:
            return name
        canonical = self.type_aliases.get(name)
        if canonical is not None:
            return canonical
        return None

    def has_attribute(
        self, type_name: str, attr_name: str,
    ) -> Tristate:
        """Decide whether instances of ``type_name`` have ``attr_name``.

        Returns:
          * ``Tristate.YES``   — known type, attribute is in the set.
          * ``Tristate.NO``    — known type, attribute is absent.
          * ``Tristate.UNKNOWN`` — unrecognised type.
        """
        canonical = self.resolve(type_name)
        if canonical is None:
            return Tristate.UNKNOWN
        attrs = self.by_type.get(canonical, frozenset())
        return Tristate.YES if attr_name in attrs else Tristate.NO

    def disjunction(
        self, type_names: Iterable[str], attr_name: str,
    ) -> Tristate:
        """For Union types, return ``YES`` if *any* arm has the
        attribute, ``NO`` if every arm is known to lack it, and
        ``UNKNOWN`` otherwise."""
        results = [self.has_attribute(t, attr_name) for t in type_names]
        if any(r is Tristate.YES for r in results):
            return Tristate.YES
        if all(r is Tristate.NO for r in results):
            return Tristate.NO
        return Tristate.UNKNOWN

    def conjunction(
        self, type_names: Iterable[str], attr_name: str,
    ) -> Tristate:
        """For ``isinstance(x, T1) and isinstance(x, T2)`` (i.e. x's
        type is the *intersection* of T1 and T2), return YES if both
        have the attribute, NO if either lacks it, UNKNOWN otherwise."""
        results = [self.has_attribute(t, attr_name) for t in type_names]
        if any(r is Tristate.NO for r in results):
            return Tristate.NO
        if all(r is Tristate.YES for r in results):
            return Tristate.YES
        return Tristate.UNKNOWN


_DEFAULT_TYPE_TO_ATTRS: dict[str, frozenset[str]] = {
    "object": _OBJECT_ATTRS,
    "int": _INT_ATTRS,
    "float": _FLOAT_ATTRS,
    "bool": _BOOL_ATTRS,
    "complex": _OBJECT_ATTRS | frozenset({
        "__abs__", "__add__", "__sub__", "__mul__", "__truediv__",
        "__pow__", "__neg__", "__pos__", "__bool__",
        "real", "imag", "conjugate",
    }),
    "str": _STR_ATTRS,
    "bytes": _BYTES_ATTRS,
    "bytearray": _BYTEARRAY_ATTRS,
    "list": _LIST_ATTRS,
    "tuple": _TUPLE_ATTRS,
    "dict": _DICT_ATTRS,
    "set": _SET_ATTRS,
    "frozenset": _FROZENSET_ATTRS,
    "NoneType": _NONE_ATTRS,
    "None": _NONE_ATTRS,
    "range": _RANGE_ATTRS,
    "function": _FUNCTION_ATTRS,
    "callable": _FUNCTION_ATTRS,
}


# Type aliases: Lean / Python typing names → canonical type name.
_DEFAULT_TYPE_ALIASES: dict[str, str] = {
    # typing module
    "List": "list",
    "Dict": "dict",
    "Set": "set",
    "FrozenSet": "frozenset",
    "Tuple": "tuple",
    "Optional": "object",     # T | None — see Union handling
    "Mapping": "dict",
    "MutableMapping": "dict",
    "Sequence": "list",       # generic sequence — list is a superset
    "MutableSequence": "list",
    "Iterable": "object",     # only __iter__ guaranteed
    "Iterator": "object",
    "Callable": "function",
    "Bool": "bool",
    "Int": "int",
    "Float": "float",
    "Str": "str",
    "Bytes": "bytes",
    "ByteArray": "bytearray",
    "Counter": "dict",
    "OrderedDict": "dict",
    "defaultdict": "dict",
    "ChainMap": "dict",
    "deque": "list",
    "Self": "object",
}


# ─────────────────────────────────────────────────────────────────────
#  Z3 encoding driver
# ─────────────────────────────────────────────────────────────────────


def encode_hasattr(
    type_name: Optional[str], attr_name: str, *,
    sort_name: str = "object", z3_module=None,
    table: Optional[HasattrTable] = None,
    uninterp_cache: Optional[dict[tuple[str, str], "object"]] = None,
):
    """Return a Z3 expression for ``hasattr(x, attr_name)`` where ``x``
    has Python type ``type_name``.

    Parameters
    ----------
    type_name :
        The Python type name (e.g. ``"int"``, ``"list"``, ``"MyClass"``).
        ``None`` is treated as ``UNKNOWN`` and produces an
        uninterpreted predicate.
    attr_name :
        The attribute name (e.g. ``"upper"``, ``"append"``, ``"__len__"``).
    sort_name :
        Used to name the uninterpreted predicate when ``type_name``
        resolves to UNKNOWN.  Different sort names produce distinct
        predicates so Z3 can keep them apart.
    z3_module :
        The ``z3`` module (passed in to keep this module free of an
        import-time dependency).  Required.
    table :
        The :class:`HasattrTable` to consult; defaults to the built-in
        table.
    uninterp_cache :
        Optional shared cache mapping ``(sort_name, attr_name)`` to a
        previously-created uninterpreted Bool.  When supplied we
        reuse the same predicate across calls — this matters because
        ``hasattr(x, 'foo')`` should resolve to the same Z3 atom
        regardless of where the call appears, so the SMT layer can
        propagate equalities.
    """
    if z3_module is None:
        raise ValueError("z3_module is required")
    table = table or HasattrTable.default()

    if type_name is None:
        return _uninterpreted(
            sort_name, attr_name, z3_module, uninterp_cache,
        )
    result = table.has_attribute(type_name, attr_name)
    if result is Tristate.YES:
        return z3_module.BoolVal(True)
    if result is Tristate.NO:
        return z3_module.BoolVal(False)
    return _uninterpreted(
        sort_name, attr_name, z3_module, uninterp_cache,
    )


def encode_hasattr_union(
    type_names: list[str], attr_name: str, *,
    sort_name: str = "object", z3_module=None,
    table: Optional[HasattrTable] = None,
    uninterp_cache: Optional[dict[tuple[str, str], "object"]] = None,
):
    """Encode ``hasattr(x, attr_name)`` where ``x``'s type is a union
    of ``type_names`` (e.g. ``Optional[int]`` → ``["int", "None"]``).

    Returns:
      * ``BoolVal(True)`` if some arm definitely has the attribute.
      * ``BoolVal(False)`` if every arm definitely lacks it.
      * Uninterpreted Bool otherwise.
    """
    if z3_module is None:
        raise ValueError("z3_module is required")
    table = table or HasattrTable.default()
    result = table.disjunction(type_names, attr_name)
    if result is Tristate.YES:
        return z3_module.BoolVal(True)
    if result is Tristate.NO:
        return z3_module.BoolVal(False)
    return _uninterpreted(
        sort_name, attr_name, z3_module, uninterp_cache,
    )


def _uninterpreted(
    sort_name: str, attr_name: str, z3_module,
    cache: Optional[dict[tuple[str, str], "object"]],
):
    """Create (or look up) an uninterpreted Bool ``hasattr_<sort>__<name>``.

    Two calls with the same ``(sort_name, attr_name)`` resolve to the
    same Z3 atom — this matters for soundness: ``hasattr(x, 'foo') ∧
    ¬ hasattr(x, 'foo')`` must be a contradiction at the SMT level.
    """
    safe_attr = _safe_ident(attr_name)
    safe_sort = _safe_ident(sort_name)
    name = f"hasattr_{safe_sort}__{safe_attr}"
    if cache is not None:
        cached = cache.get((sort_name, attr_name))
        if cached is not None:
            return cached
    atom = z3_module.Bool(name)
    if cache is not None:
        cache[(sort_name, attr_name)] = atom
    return atom


def _safe_ident(text: str) -> str:
    """Sanitize a string into a Z3-safe identifier (alphanumeric + _)."""
    out = []
    for ch in text:
        if ch.isalnum() or ch == "_":
            out.append(ch)
        else:
            out.append(f"x{ord(ch):x}")
    if out and out[0].isdigit():
        out.insert(0, "x")
    return "".join(out) or "anon"


# ─────────────────────────────────────────────────────────────────────
#  Helpers for callers
# ─────────────────────────────────────────────────────────────────────


def parse_union_type(annotation_text: str) -> list[str]:
    """Parse a Python annotation string into the list of arm type
    names of its union.  Handles:

    * bare names: ``int`` → ``["int"]``
    * PEP 604: ``int | str`` → ``["int", "str"]``
    * Optional[T]: ``["T", "None"]``
    * Union[T1, T2]: ``["T1", "T2"]``
    * generic-parameterised: ``list[int]`` → ``["list"]`` (we strip
      the parameter for hasattr decisions)
    * unknown / unparseable → ``[]``
    """
    if not annotation_text:
        return []
    text = annotation_text.strip()
    # Strip outer parentheses.
    while text.startswith("(") and text.endswith(")"):
        text = text[1:-1].strip()
    # Optional[T] → T | None
    if text.startswith("Optional[") and text.endswith("]"):
        inner = text[len("Optional["):-1]
        return parse_union_type(inner) + ["None"]
    # Union[T1, T2, ...]
    if text.startswith("Union[") and text.endswith("]"):
        inner = text[len("Union["):-1]
        return _split_top_level(inner, ",")
    # PEP 604 union: split at depth-0 ``|``.  ``_split_top_level``
    # already respects bracket depth, so a ``list[int] | dict[str, int]``
    # is split into two arms while ``list[int | str]`` (an inner
    # union as a generic parameter) splits to one arm at the top.
    parts = _split_top_level(text, "|")
    if len(parts) > 1:
        return [_strip_generic(t.strip()) for t in parts]
    return [_strip_generic(text)]


def _strip_generic(name: str) -> str:
    """``list[int]`` → ``list``."""
    bracket = name.find("[")
    if bracket >= 0:
        return name[:bracket].strip()
    return name.strip()


def _split_top_level(text: str, sep: str) -> list[str]:
    """Split ``text`` on ``sep`` at the top level (depth 0)."""
    parts: list[str] = []
    depth = 0
    current = ""
    for ch in text:
        if ch == "[":
            depth += 1
            current += ch
        elif ch == "]":
            depth -= 1
            current += ch
        elif ch == sep and depth == 0:
            parts.append(current.strip())
            current = ""
        else:
            current += ch
    if current.strip():
        parts.append(current.strip())
    return parts


__all__ = [
    "Tristate",
    "HasattrTable",
    "encode_hasattr",
    "encode_hasattr_union",
    "parse_union_type",
]
