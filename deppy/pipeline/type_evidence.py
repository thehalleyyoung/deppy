"""Source-specific type evidence lookup for the safety pipeline.

Audit fix #9
============

The safety pipeline previously made type-narrowing decisions by
walking *every* refinement fact in the function — an
``isinstance(d, dict)`` guard recorded at line 5 was visible to a
subscript at line 50, even though the guard had long since fallen
out of scope.

This module provides a *source-specific* type-evidence query so
each subscript / attribute / call gets type evidence from only the
guards that hold at its specific source location.

Public API
----------

::

    table = build_evidence_table(refinement_map)
    evidence_set = table.evidence_at(lineno, col, kinds)
    receiver_type = table.evidence_for_subscript(receiver_text, lineno, col, kinds)

Representation
--------------

The :class:`TypeEvidenceTable` indexes the refinement map's per-source
facts by ``(lineno, col, kind)`` and supports fast lookups.  Each
:class:`TypeEvidence` records a single piece of static evidence — the
matching expression, the inferred class family, and the source
guard text that supports it.

Pattern coverage
----------------

The analyser recognises:

* ``isinstance(x, T)`` / ``isinstance(x, (T1, T2, ...))``
* ``type(x) is T`` / ``type(x) == T`` / ``type(x) in (T1, T2, ...)``
* ``hasattr(x, 'name')`` (narrows to "object with attribute name")
* ``x is None`` / ``x is not None`` (narrows Optional[T] → T or None)
* ``x in C`` / ``x not in C`` (narrows membership; for dict-typed C
  this confirms that subsequent ``C[x]`` is safe)
* ``len(x) > 0`` / ``len(x) >= 1`` / ``len(x) > k`` for k constant
  (narrows non-empty container)

Each pattern produces a :class:`TypeEvidence` of the appropriate
:class:`EvidenceKind`.  Callers (e.g. the subscript-promotion logic
in safety_pipeline) inspect the kind and decide whether to act.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from enum import Enum
from typing import Iterable, Optional


# ─────────────────────────────────────────────────────────────────────
#  Evidence kinds and structured records
# ─────────────────────────────────────────────────────────────────────


class EvidenceKind(str, Enum):
    """The semantic category of a piece of type evidence."""

    DICT = "dict"               # x is dict-like (Mapping)
    SEQUENCE = "sequence"        # x is sequence-like (list/tuple/str/bytes)
    SET = "set"                  # x is set-like
    INT = "int"                  # x is an integer
    FLOAT = "float"
    STR = "str"
    BOOL = "bool"
    NONE = "none"                # x is None
    NOT_NONE = "not_none"        # x is not None
    NON_EMPTY = "non_empty"      # x is a non-empty container
    HAS_ATTR = "has_attr"        # x has the named attribute
    KEY_PRESENT = "key_present"  # k is in d (subsequent d[k] safe)
    ZERO_OK = "zero_ok"          # x != 0 (so 1/x is safe)
    POSITIVE = "positive"        # x > 0
    NON_NEGATIVE = "non_negative"  # x >= 0
    OBJECT = "object"            # x is an instance of a custom class


@dataclass(frozen=True)
class TypeEvidence:
    """One piece of static type evidence at a source location.

    ``expression`` is the receiver expression (Python source text)
    the evidence applies to — e.g. ``"d"`` for ``isinstance(d, dict)``
    or ``"x"`` for ``x is not None``.

    ``kind`` is the :class:`EvidenceKind`.

    ``payload`` carries kind-specific data (e.g. for ``HAS_ATTR``
    it's the attribute name; for ``KEY_PRESENT`` it's the key text;
    for ``OBJECT`` it's the class name).

    ``source_guard`` is the original guard text the evidence came from
    (useful for debugging / display).
    """

    expression: str
    kind: EvidenceKind
    source_guard: str
    payload: tuple[str, ...] = ()

    def matches_expression(self, expr_text: str) -> bool:
        return self.expression.strip() == expr_text.strip()

    def with_payload(self, *args: str) -> "TypeEvidence":
        return TypeEvidence(
            expression=self.expression, kind=self.kind,
            source_guard=self.source_guard, payload=tuple(args),
        )


# ─────────────────────────────────────────────────────────────────────
#  TypeEvidenceTable — per-source indexed lookup
# ─────────────────────────────────────────────────────────────────────


@dataclass
class TypeEvidenceTable:
    """Indexed view of type evidence for a function.

    Built once per function (see :func:`build_evidence_table`) and
    queried per-source-location.  The internal index is a dict from
    ``(lineno, col, kind)`` to a list of :class:`TypeEvidence`.
    """

    _index: dict[tuple[int, int, str], list[TypeEvidence]] = field(
        default_factory=dict,
    )

    def add(
        self, lineno: int, col: int, kind: str,
        evidence: TypeEvidence,
    ) -> None:
        key = (lineno, col, kind)
        self._index.setdefault(key, []).append(evidence)

    def evidence_at(
        self, lineno: int, col: int,
        kinds: Optional[Iterable[str]] = None,
    ) -> list[TypeEvidence]:
        """Return all evidence at ``(lineno, col)`` whose source kind
        is in ``kinds`` (when provided).  When ``kinds`` is ``None``
        we return evidence across all source kinds at this location.
        """
        out: list[TypeEvidence] = []
        if kinds is None:
            # Walk the whole index for the location.
            for (l, c, _k), evs in self._index.items():
                if l == lineno and c == col:
                    out.extend(evs)
        else:
            for k in kinds:
                out.extend(self._index.get((lineno, col, k), []))
        return out

    def evidence_for_expression(
        self, expr_text: str, lineno: int, col: int,
        kinds: Optional[Iterable[str]] = None,
    ) -> list[TypeEvidence]:
        return [
            e for e in self.evidence_at(lineno, col, kinds)
            if e.matches_expression(expr_text)
        ]

    def kind_for_subscript(
        self, receiver_text: str, lineno: int, col: int,
        kinds: Optional[Iterable[str]] = None,
    ) -> Optional[str]:
        """Return ``"dict"`` / ``"sequence"`` / ``None`` based on
        evidence at the receiver's source location.

        This mirrors the legacy
        :func:`safety_pipeline._subscript_type_evidence` API but
        consults *only* the source-specific evidence — guards from
        other locations are ignored.
        """
        evs = self.evidence_for_expression(
            receiver_text, lineno, col, kinds,
        )
        for e in evs:
            if e.kind is EvidenceKind.DICT:
                return "dict"
            if e.kind is EvidenceKind.SEQUENCE:
                return "sequence"
        return None

    def all_evidence(self) -> Iterable[TypeEvidence]:
        for evs in self._index.values():
            yield from evs

    def __len__(self) -> int:
        return sum(len(evs) for evs in self._index.values())


# ─────────────────────────────────────────────────────────────────────
#  Pattern recognisers
# ─────────────────────────────────────────────────────────────────────


_DICT_NAMES = frozenset({
    "dict", "Dict", "Mapping", "MutableMapping", "OrderedDict",
    "defaultdict", "Counter", "ChainMap",
})
_SEQUENCE_NAMES = frozenset({
    "list", "List", "tuple", "Tuple", "Sequence", "MutableSequence",
    "str", "Str", "bytes", "Bytes", "bytearray", "ByteArray",
    "Iterable", "Iterator", "frozenset", "set",  # set is iterable
})
_SET_NAMES = frozenset({
    "set", "Set", "frozenset", "FrozenSet", "MutableSet",
})


def _classify_typename(name: str) -> Optional[EvidenceKind]:
    """Map a Python type-class name to its :class:`EvidenceKind`."""
    if name in _DICT_NAMES:
        return EvidenceKind.DICT
    if name in _SEQUENCE_NAMES:
        return EvidenceKind.SEQUENCE
    if name in _SET_NAMES:
        return EvidenceKind.SET
    if name == "int":
        return EvidenceKind.INT
    if name == "float":
        return EvidenceKind.FLOAT
    if name == "str":
        return EvidenceKind.STR
    if name == "bool":
        return EvidenceKind.BOOL
    return None


def _classify_typename_strict(name: str) -> EvidenceKind:
    """Map a type-class name; default to ``OBJECT`` for unknowns."""
    k = _classify_typename(name)
    return k if k is not None else EvidenceKind.OBJECT


def _safe_unparse(node: ast.AST) -> str:
    try:
        return ast.unparse(node).strip()
    except Exception:
        return ""


def evidence_from_guard(
    guard_text: str,
) -> list[TypeEvidence]:
    """Parse a single guard string and extract every piece of type
    evidence it conveys.

    A guard like ``"isinstance(d, dict) and len(d) > 0"`` produces
    two evidence records: one ``DICT`` and one ``NON_EMPTY``.
    """
    out: list[TypeEvidence] = []
    try:
        tree = ast.parse(guard_text or "True", mode="eval")
    except SyntaxError:
        return out
    _walk_predicate(tree.body, guard_text, out)
    return out


def _walk_predicate(
    node: ast.expr, source: str, out: list[TypeEvidence],
) -> None:
    """Walk a Boolean predicate and emit evidence for every clause."""
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And):
        for v in node.values:
            _walk_predicate(v, source, out)
        return
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        # ``not (x is None)`` → x is not None.  Recurse with negated
        # interpretation only when the inner is a single-clause
        # negatable form.
        inner = node.operand
        _emit_negated(inner, source, out)
        return
    _emit(node, source, out)


def _emit(node: ast.expr, source: str, out: list[TypeEvidence]) -> None:
    """Emit evidence for a single (un-negated) clause."""
    # isinstance(x, T) / isinstance(x, (T1, T2, ...))
    if isinstance(node, ast.Call) and _name_is(node.func, "isinstance"):
        if len(node.args) >= 2:
            target_text = _safe_unparse(node.args[0])
            classes = _classes_from_isinstance_arg(node.args[1])
            for cname in classes:
                kind = _classify_typename_strict(cname)
                out.append(TypeEvidence(
                    expression=target_text, kind=kind, source_guard=source,
                    payload=(cname,),
                ))
        return
    # type(x) is T / type(x) == T
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        op = node.ops[0]
        left = node.left
        right = node.comparators[0]
        # type(x) is T
        if (isinstance(op, (ast.Is, ast.Eq))
                and isinstance(left, ast.Call)
                and _name_is(left.func, "type")
                and len(left.args) == 1):
            target_text = _safe_unparse(left.args[0])
            cname = _name_of(right)
            if cname:
                kind = _classify_typename_strict(cname)
                out.append(TypeEvidence(
                    expression=target_text, kind=kind, source_guard=source,
                    payload=(cname,),
                ))
            return
        # type(x) in (T1, T2, ...)
        if (isinstance(op, ast.In)
                and isinstance(left, ast.Call)
                and _name_is(left.func, "type")
                and len(left.args) == 1
                and isinstance(right, (ast.Tuple, ast.List, ast.Set))):
            target_text = _safe_unparse(left.args[0])
            for elt in right.elts:
                cname = _name_of(elt)
                if cname:
                    kind = _classify_typename_strict(cname)
                    out.append(TypeEvidence(
                        expression=target_text, kind=kind,
                        source_guard=source, payload=(cname,),
                    ))
            return
        # x is None / x is not None
        if isinstance(op, ast.Is) and _is_none(right):
            out.append(TypeEvidence(
                expression=_safe_unparse(left),
                kind=EvidenceKind.NONE, source_guard=source,
            ))
            return
        if isinstance(op, ast.IsNot) and _is_none(right):
            out.append(TypeEvidence(
                expression=_safe_unparse(left),
                kind=EvidenceKind.NOT_NONE, source_guard=source,
            ))
            return
        # k in d
        if isinstance(op, ast.In):
            out.append(TypeEvidence(
                expression=_safe_unparse(right),
                kind=EvidenceKind.KEY_PRESENT, source_guard=source,
                payload=(_safe_unparse(left),),
            ))
            return
        # k not in d
        if isinstance(op, ast.NotIn):
            # No positive evidence; skip.
            return
        # x != 0 (zero-OK)
        if (isinstance(op, ast.NotEq) and _is_zero(right)):
            out.append(TypeEvidence(
                expression=_safe_unparse(left),
                kind=EvidenceKind.ZERO_OK, source_guard=source,
            ))
            return
        if (isinstance(op, ast.NotEq) and _is_zero(left)):
            out.append(TypeEvidence(
                expression=_safe_unparse(right),
                kind=EvidenceKind.ZERO_OK, source_guard=source,
            ))
            return
        # len(x) > 0  / len(x) >= 1 — must come BEFORE the generic
        # positive check (a ``len(x) > 0`` would match POSITIVE on
        # the ``len(x)`` expression but the more useful evidence is
        # NON_EMPTY on x itself).
        if (isinstance(op, (ast.Gt, ast.GtE))
                and isinstance(left, ast.Call)
                and _name_is(left.func, "len")
                and len(left.args) == 1
                and _is_positive_constant(right, op)):
            out.append(TypeEvidence(
                expression=_safe_unparse(left.args[0]),
                kind=EvidenceKind.NON_EMPTY, source_guard=source,
            ))
            return
        # x > 0 / x >= 0
        if isinstance(op, ast.Gt) and _is_zero(right):
            out.append(TypeEvidence(
                expression=_safe_unparse(left),
                kind=EvidenceKind.POSITIVE, source_guard=source,
            ))
            return
        if isinstance(op, ast.GtE) and _is_zero(right):
            out.append(TypeEvidence(
                expression=_safe_unparse(left),
                kind=EvidenceKind.NON_NEGATIVE, source_guard=source,
            ))
            return
        # 0 < x / 0 <= x (mirror)
        if isinstance(op, ast.Lt) and _is_zero(left):
            out.append(TypeEvidence(
                expression=_safe_unparse(right),
                kind=EvidenceKind.POSITIVE, source_guard=source,
            ))
            return
        if isinstance(op, ast.LtE) and _is_zero(left):
            out.append(TypeEvidence(
                expression=_safe_unparse(right),
                kind=EvidenceKind.NON_NEGATIVE, source_guard=source,
            ))
            return
    # hasattr(x, 'name')
    if isinstance(node, ast.Call) and _name_is(node.func, "hasattr"):
        if len(node.args) >= 2:
            target_text = _safe_unparse(node.args[0])
            attr_node = node.args[1]
            attr_name = ""
            if isinstance(attr_node, ast.Constant) and isinstance(
                attr_node.value, str,
            ):
                attr_name = attr_node.value
            out.append(TypeEvidence(
                expression=target_text, kind=EvidenceKind.HAS_ATTR,
                source_guard=source, payload=(attr_name,),
            ))
        return
    # ``x`` (truthy) — narrows to NOT_NONE for Optional types.
    if isinstance(node, ast.Name):
        out.append(TypeEvidence(
            expression=node.id, kind=EvidenceKind.NOT_NONE,
            source_guard=source,
        ))
        return


def _emit_negated(
    node: ast.expr, source: str, out: list[TypeEvidence],
) -> None:
    """Emit evidence for a *negated* clause.  Only a few shapes are
    informative under negation:

    * ``not isinstance(x, T)``  → no positive evidence (we don't track
      "x is NOT T") in this iteration.
    * ``not (x is None)``       → x is not None.
    * ``not (x in C)``          → no positive evidence.
    """
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        op = node.ops[0]
        if isinstance(op, ast.Is) and _is_none(node.comparators[0]):
            out.append(TypeEvidence(
                expression=_safe_unparse(node.left),
                kind=EvidenceKind.NOT_NONE, source_guard=source,
            ))


def _name_is(node: ast.expr, name: str) -> bool:
    return isinstance(node, ast.Name) and node.id == name


def _is_none(node: ast.expr) -> bool:
    return isinstance(node, ast.Constant) and node.value is None


def _is_zero(node: ast.expr) -> bool:
    if isinstance(node, ast.Constant):
        return node.value == 0
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return _is_zero(node.operand)
    return False


def _is_positive_constant(node: ast.expr, op: ast.cmpop) -> bool:
    """``len(x) > 0`` — right side must be 0; ``len(x) >= 1`` — right
    side must be 1."""
    if isinstance(op, ast.Gt) and _is_zero(node):
        return True
    if isinstance(op, ast.GtE):
        if isinstance(node, ast.Constant) and isinstance(
            node.value, int,
        ) and node.value >= 1:
            return True
    return False


def _name_of(node: ast.expr) -> Optional[str]:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return _name_of(node.value)  # rough — first segment
    return None


def _classes_from_isinstance_arg(node: ast.expr) -> list[str]:
    """Return the list of class names mentioned in ``isinstance(x, T)``'s
    second argument.  ``T`` may be a single class, a tuple, or a list."""
    if isinstance(node, ast.Name):
        return [node.id]
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        out: list[str] = []
        for elt in node.elts:
            if isinstance(elt, ast.Name):
                out.append(elt.id)
            elif isinstance(elt, ast.Attribute):
                # ``typing.Mapping`` etc.
                name = _safe_unparse(elt)
                short = name.rsplit(".", 1)[-1]
                out.append(short)
        return out
    if isinstance(node, ast.Attribute):
        name = _safe_unparse(node)
        return [name.rsplit(".", 1)[-1]]
    return []


# ─────────────────────────────────────────────────────────────────────
#  Builder — refinement_map → TypeEvidenceTable
# ─────────────────────────────────────────────────────────────────────


def build_evidence_table(refinement_map) -> TypeEvidenceTable:
    """Walk a :class:`RefinementMap` and produce a per-source
    :class:`TypeEvidenceTable`.

    Each fact in the refinement map's ``per_source`` list contributes
    its evidence at its specific ``(lineno, col, kind)`` key.  The
    same evidence may appear at multiple locations if the same
    isinstance guard is in scope at several sources — that's
    correct and intended.
    """
    table = TypeEvidenceTable()
    if refinement_map is None:
        return table
    for fact in getattr(refinement_map, "per_source", []) or []:
        for guard_text in fact.guards:
            for ev in evidence_from_guard(guard_text):
                table.add(
                    fact.source_lineno, fact.source_col,
                    fact.source_kind, ev,
                )
    return table


# ─────────────────────────────────────────────────────────────────────
#  Convenience helpers for the safety pipeline
# ─────────────────────────────────────────────────────────────────────


def has_dict_evidence_at(
    table: TypeEvidenceTable, expr_text: str,
    lineno: int, col: int,
    kinds: Optional[Iterable[str]] = None,
) -> bool:
    return any(
        e.kind is EvidenceKind.DICT
        for e in table.evidence_for_expression(
            expr_text, lineno, col, kinds,
        )
    )


def has_sequence_evidence_at(
    table: TypeEvidenceTable, expr_text: str,
    lineno: int, col: int,
    kinds: Optional[Iterable[str]] = None,
) -> bool:
    return any(
        e.kind is EvidenceKind.SEQUENCE
        for e in table.evidence_for_expression(
            expr_text, lineno, col, kinds,
        )
    )


def has_not_none_evidence_at(
    table: TypeEvidenceTable, expr_text: str,
    lineno: int, col: int,
    kinds: Optional[Iterable[str]] = None,
) -> bool:
    return any(
        e.kind is EvidenceKind.NOT_NONE
        for e in table.evidence_for_expression(
            expr_text, lineno, col, kinds,
        )
    )


def has_zero_ok_evidence_at(
    table: TypeEvidenceTable, expr_text: str,
    lineno: int, col: int,
    kinds: Optional[Iterable[str]] = None,
) -> bool:
    return any(
        e.kind is EvidenceKind.ZERO_OK
        for e in table.evidence_for_expression(
            expr_text, lineno, col, kinds,
        )
    )


def has_key_present_evidence_at(
    table: TypeEvidenceTable, container_text: str, key_text: str,
    lineno: int, col: int,
    kinds: Optional[Iterable[str]] = None,
) -> bool:
    """Return True iff a guard at (lineno, col) records ``key_text in
    container_text``."""
    for e in table.evidence_for_expression(
        container_text, lineno, col, kinds,
    ):
        if e.kind is EvidenceKind.KEY_PRESENT and e.payload[:1] == (key_text,):
            return True
    return False


def has_non_empty_evidence_at(
    table: TypeEvidenceTable, expr_text: str,
    lineno: int, col: int,
    kinds: Optional[Iterable[str]] = None,
) -> bool:
    return any(
        e.kind is EvidenceKind.NON_EMPTY
        for e in table.evidence_for_expression(
            expr_text, lineno, col, kinds,
        )
    )


__all__ = [
    "EvidenceKind",
    "TypeEvidence",
    "TypeEvidenceTable",
    "evidence_from_guard",
    "build_evidence_table",
    "has_dict_evidence_at",
    "has_sequence_evidence_at",
    "has_not_none_evidence_at",
    "has_zero_ok_evidence_at",
    "has_key_present_evidence_at",
    "has_non_empty_evidence_at",
]
