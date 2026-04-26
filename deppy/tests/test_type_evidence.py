"""Audit fix #9 — source-specific type evidence lookup.

Tests :class:`deppy.pipeline.type_evidence.TypeEvidenceTable` and the
guard-parsing primitives.

The tests are organised by what's being checked:

* ``TestEvidenceFromGuard`` — pattern-recognition for individual
  guard strings (isinstance, type(), is None, hasattr, len, in, …).
* ``TestEvidenceTable`` — building, indexing, source-specific
  lookup, kind-filter.
* ``TestBuildFromRefinementMap`` — end-to-end on synthetic
  RefinementMap inputs.
* ``TestSafetyPipelineIntegration`` — the integration into
  ``_subscript_type_evidence`` so a guard at one location does not
  leak into another location's decision.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from deppy.pipeline.type_evidence import (
    EvidenceKind,
    TypeEvidence,
    TypeEvidenceTable,
    build_evidence_table,
    evidence_from_guard,
    has_dict_evidence_at,
    has_key_present_evidence_at,
    has_non_empty_evidence_at,
    has_not_none_evidence_at,
    has_sequence_evidence_at,
    has_zero_ok_evidence_at,
)


# Lightweight stand-in for the real RefinementFact / RefinementMap.
@dataclass
class _Fact:
    source_lineno: int
    source_col: int
    source_kind: str
    guards: tuple[str, ...] = ()
    safety_predicate: str = ""


@dataclass
class _Map:
    per_source: list[_Fact] = field(default_factory=list)


# ─────────────────────────────────────────────────────────────────────
#  Pattern recognition
# ─────────────────────────────────────────────────────────────────────


class TestEvidenceFromGuard:
    def test_isinstance_dict(self):
        evs = evidence_from_guard("isinstance(d, dict)")
        kinds = [e.kind for e in evs]
        assert EvidenceKind.DICT in kinds
        assert all(e.expression == "d" for e in evs if e.kind == EvidenceKind.DICT)

    def test_isinstance_list(self):
        evs = evidence_from_guard("isinstance(xs, list)")
        assert any(e.kind is EvidenceKind.SEQUENCE for e in evs)

    def test_isinstance_tuple_of_classes(self):
        evs = evidence_from_guard("isinstance(x, (list, tuple))")
        # Should produce evidence for both list AND tuple (both
        # SEQUENCE).
        assert sum(1 for e in evs if e.kind is EvidenceKind.SEQUENCE) >= 2

    def test_isinstance_user_class_is_object(self):
        evs = evidence_from_guard("isinstance(x, MyClass)")
        assert any(e.kind is EvidenceKind.OBJECT for e in evs)

    def test_type_is(self):
        evs = evidence_from_guard("type(x) is dict")
        assert any(e.kind is EvidenceKind.DICT for e in evs)

    def test_type_eq(self):
        evs = evidence_from_guard("type(x) == list")
        assert any(e.kind is EvidenceKind.SEQUENCE for e in evs)

    def test_type_in_tuple(self):
        evs = evidence_from_guard("type(x) in (list, tuple)")
        assert any(e.kind is EvidenceKind.SEQUENCE for e in evs)

    def test_x_is_none(self):
        evs = evidence_from_guard("x is None")
        assert any(e.kind is EvidenceKind.NONE for e in evs)

    def test_x_is_not_none(self):
        evs = evidence_from_guard("x is not None")
        assert any(e.kind is EvidenceKind.NOT_NONE for e in evs)

    def test_negated_x_is_none(self):
        evs = evidence_from_guard("not (x is None)")
        assert any(e.kind is EvidenceKind.NOT_NONE for e in evs)

    def test_hasattr(self):
        evs = evidence_from_guard("hasattr(x, 'foo')")
        attrs = [e for e in evs if e.kind is EvidenceKind.HAS_ATTR]
        assert attrs
        assert attrs[0].payload[0] == "foo"

    def test_key_in_dict(self):
        evs = evidence_from_guard("k in d")
        # ``k in d`` records: container=d, kind=KEY_PRESENT, key=k.
        kp = [e for e in evs if e.kind is EvidenceKind.KEY_PRESENT]
        assert kp
        assert kp[0].expression == "d"
        assert kp[0].payload[0] == "k"

    def test_b_neq_zero(self):
        evs = evidence_from_guard("b != 0")
        assert any(e.kind is EvidenceKind.ZERO_OK for e in evs)

    def test_zero_neq_b(self):
        evs = evidence_from_guard("0 != b")
        assert any(e.kind is EvidenceKind.ZERO_OK for e in evs)

    def test_x_gt_zero(self):
        evs = evidence_from_guard("x > 0")
        assert any(e.kind is EvidenceKind.POSITIVE for e in evs)

    def test_x_gte_zero(self):
        evs = evidence_from_guard("x >= 0")
        assert any(e.kind is EvidenceKind.NON_NEGATIVE for e in evs)

    def test_zero_lt_x(self):
        evs = evidence_from_guard("0 < x")
        assert any(e.kind is EvidenceKind.POSITIVE for e in evs)

    def test_len_x_gt_zero(self):
        evs = evidence_from_guard("len(xs) > 0")
        assert any(e.kind is EvidenceKind.NON_EMPTY for e in evs)

    def test_len_x_gte_one(self):
        evs = evidence_from_guard("len(xs) >= 1")
        assert any(e.kind is EvidenceKind.NON_EMPTY for e in evs)

    def test_compound_and(self):
        evs = evidence_from_guard("isinstance(d, dict) and len(d) > 0")
        kinds = {e.kind for e in evs}
        assert EvidenceKind.DICT in kinds
        assert EvidenceKind.NON_EMPTY in kinds

    def test_unparseable_guard_returns_empty(self):
        evs = evidence_from_guard("a >>> b")
        assert evs == []

    def test_truthy_name_implies_not_none(self):
        evs = evidence_from_guard("x")
        assert any(e.kind is EvidenceKind.NOT_NONE for e in evs)


# ─────────────────────────────────────────────────────────────────────
#  TypeEvidenceTable
# ─────────────────────────────────────────────────────────────────────


class TestEvidenceTable:
    def test_empty_table_returns_empty(self):
        t = TypeEvidenceTable()
        assert list(t.all_evidence()) == []
        assert t.evidence_at(1, 0) == []

    def test_add_and_lookup(self):
        t = TypeEvidenceTable()
        ev = TypeEvidence(
            expression="d", kind=EvidenceKind.DICT,
            source_guard="isinstance(d, dict)",
        )
        t.add(5, 10, "KEY_ERROR", ev)
        # Match.
        evs = t.evidence_at(5, 10, ["KEY_ERROR"])
        assert evs == [ev]
        # No match — wrong location.
        assert t.evidence_at(6, 10, ["KEY_ERROR"]) == []
        # No match — wrong kind.
        assert t.evidence_at(5, 10, ["INDEX_ERROR"]) == []
        # Match — kind filter omitted.
        assert t.evidence_at(5, 10) == [ev]

    def test_lookup_by_expression(self):
        t = TypeEvidenceTable()
        t.add(5, 0, "KEY_ERROR", TypeEvidence(
            expression="d", kind=EvidenceKind.DICT, source_guard="g",
        ))
        t.add(5, 0, "KEY_ERROR", TypeEvidence(
            expression="other", kind=EvidenceKind.SEQUENCE, source_guard="g2",
        ))
        evs = t.evidence_for_expression("d", 5, 0)
        assert len(evs) == 1
        assert evs[0].kind is EvidenceKind.DICT

    def test_kind_for_subscript(self):
        t = TypeEvidenceTable()
        t.add(5, 0, "KEY_ERROR", TypeEvidence(
            expression="d", kind=EvidenceKind.DICT, source_guard="g",
        ))
        assert t.kind_for_subscript("d", 5, 0) == "dict"
        assert t.kind_for_subscript("d", 6, 0) is None  # different location
        assert t.kind_for_subscript("other", 5, 0) is None

    def test_kind_for_subscript_with_sequence(self):
        t = TypeEvidenceTable()
        t.add(5, 0, "INDEX_ERROR", TypeEvidence(
            expression="xs", kind=EvidenceKind.SEQUENCE, source_guard="g",
        ))
        assert t.kind_for_subscript("xs", 5, 0) == "sequence"


# ─────────────────────────────────────────────────────────────────────
#  build_evidence_table
# ─────────────────────────────────────────────────────────────────────


class TestBuildFromRefinementMap:
    def test_empty_map(self):
        t = build_evidence_table(_Map())
        assert len(t) == 0

    def test_one_fact_one_guard(self):
        m = _Map(per_source=[
            _Fact(
                source_lineno=10, source_col=4, source_kind="KEY_ERROR",
                guards=("isinstance(d, dict)",),
            ),
        ])
        t = build_evidence_table(m)
        evs = t.evidence_at(10, 4, ["KEY_ERROR"])
        assert any(e.kind is EvidenceKind.DICT for e in evs)

    def test_multiple_facts_indexed_separately(self):
        m = _Map(per_source=[
            _Fact(
                source_lineno=5, source_col=0, source_kind="KEY_ERROR",
                guards=("isinstance(d, dict)",),
            ),
            _Fact(
                source_lineno=20, source_col=0, source_kind="INDEX_ERROR",
                guards=("isinstance(xs, list)",),
            ),
        ])
        t = build_evidence_table(m)
        # Each fact is at its own (lineno, col, kind).
        assert t.kind_for_subscript("d", 5, 0, ["KEY_ERROR"]) == "dict"
        assert t.kind_for_subscript("xs", 20, 0, ["INDEX_ERROR"]) == "sequence"
        # Critically: a guard at line 5 must NOT show up at line 20.
        assert t.kind_for_subscript("d", 20, 0, ["INDEX_ERROR"]) is None

    def test_none_map_is_safe(self):
        t = build_evidence_table(None)
        assert len(t) == 0


# ─────────────────────────────────────────────────────────────────────
#  Convenience helpers
# ─────────────────────────────────────────────────────────────────────


class TestConvenienceHelpers:
    def _table_with(self, lineno, col, kind, guard) -> TypeEvidenceTable:
        m = _Map(per_source=[
            _Fact(
                source_lineno=lineno, source_col=col,
                source_kind=kind, guards=(guard,),
            ),
        ])
        return build_evidence_table(m)

    def test_has_dict_evidence_at(self):
        t = self._table_with(5, 0, "KEY_ERROR", "isinstance(d, dict)")
        assert has_dict_evidence_at(t, "d", 5, 0)
        assert not has_dict_evidence_at(t, "d", 6, 0)

    def test_has_sequence_evidence_at(self):
        t = self._table_with(5, 0, "INDEX_ERROR", "isinstance(xs, list)")
        assert has_sequence_evidence_at(t, "xs", 5, 0)
        assert not has_sequence_evidence_at(t, "xs", 99, 0)

    def test_has_not_none_evidence_at(self):
        t = self._table_with(5, 0, "ATTRIBUTE_ERROR", "x is not None")
        assert has_not_none_evidence_at(t, "x", 5, 0)

    def test_has_zero_ok_evidence_at(self):
        t = self._table_with(5, 0, "ZERO_DIVISION", "b != 0")
        assert has_zero_ok_evidence_at(t, "b", 5, 0)

    def test_has_key_present_evidence_at(self):
        t = self._table_with(5, 0, "KEY_ERROR", "k in d")
        assert has_key_present_evidence_at(t, "d", "k", 5, 0)
        # Wrong key — not present.
        assert not has_key_present_evidence_at(t, "d", "j", 5, 0)

    def test_has_non_empty_evidence_at(self):
        t = self._table_with(5, 0, "INDEX_ERROR", "len(xs) > 0")
        assert has_non_empty_evidence_at(t, "xs", 5, 0)


# ─────────────────────────────────────────────────────────────────────
#  Integration regression — guard at line A doesn't leak to line B
# ─────────────────────────────────────────────────────────────────────


class TestSourceLeakageRegression:
    """Audit fix #9 — a guard at one source location must NOT
    influence type-evidence decisions at a different source.

    Synthetic scenario: a refinement map records ``isinstance(d, dict)``
    only at line 5 (KEY_ERROR), but at line 50 there's a different
    subscript with no guard.  The query for line 50 must return None
    (no evidence) — not "dict" leaked from line 5.
    """

    def test_dict_guard_does_not_leak(self):
        m = _Map(per_source=[
            _Fact(
                source_lineno=5, source_col=10, source_kind="KEY_ERROR",
                guards=("isinstance(d, dict)",),
            ),
            _Fact(
                source_lineno=50, source_col=10, source_kind="INDEX_ERROR",
                guards=(),  # no guards at this location
            ),
        ])
        t = build_evidence_table(m)
        # Line 5 has dict evidence.
        assert t.kind_for_subscript("d", 5, 10, ["KEY_ERROR"]) == "dict"
        # Line 50 has NO evidence — the dict guard from line 5 must
        # not leak through.
        assert t.kind_for_subscript("d", 50, 10, ["INDEX_ERROR"]) is None

    def test_sequence_guard_does_not_leak(self):
        m = _Map(per_source=[
            _Fact(
                source_lineno=10, source_col=0, source_kind="INDEX_ERROR",
                guards=("isinstance(xs, list)",),
            ),
            _Fact(
                source_lineno=20, source_col=0, source_kind="INDEX_ERROR",
                guards=(),
            ),
        ])
        t = build_evidence_table(m)
        assert t.kind_for_subscript("xs", 10, 0, ["INDEX_ERROR"]) == "sequence"
        assert t.kind_for_subscript("xs", 20, 0, ["INDEX_ERROR"]) is None

    def test_kind_filter_excludes_unmatched_kinds(self):
        m = _Map(per_source=[
            _Fact(
                source_lineno=5, source_col=0, source_kind="KEY_ERROR",
                guards=("isinstance(d, dict)",),
            ),
        ])
        t = build_evidence_table(m)
        # Looking for INDEX_ERROR evidence at the same location → None.
        assert t.kind_for_subscript("d", 5, 0, ["INDEX_ERROR"]) is None
        # KEY_ERROR matches.
        assert t.kind_for_subscript("d", 5, 0, ["KEY_ERROR"]) == "dict"
