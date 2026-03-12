"""Tests for ErrorSiteRegistry -- error pattern registration and viability lookup.

Tests verify pattern registration, error site registration, viability
queries, and aggregate statistics.
"""

import pytest

from deppy.core._protocols import SiteId, SiteKind
from deppy.core.error_site_registry import (
    ErrorKind,
    ErrorPattern,
    ErrorSiteEntry,
    ErrorSiteRegistry,
    OperationKind,
    ViabilityPredicate,
)


# ============================================================================
# Helpers
# ============================================================================


def _make_error_site_id(name: str) -> SiteId:
    return SiteId(kind=SiteKind.ERROR, name=name)


def _make_viability(
    desc: str,
    error_kind: ErrorKind = ErrorKind.TYPE_ERROR,
    op: OperationKind = OperationKind.CALL,
    **kwargs,
) -> ViabilityPredicate:
    return ViabilityPredicate(
        _description=desc,
        _error_kind=error_kind,
        _operation=op,
        **kwargs,
    )


# ============================================================================
# Default patterns
# ============================================================================


class TestDefaultPatterns:
    """Test the built-in error pattern catalog."""

    def test_defaults_loaded(self):
        reg = ErrorSiteRegistry(load_defaults=True)
        assert reg.pattern_count > 0

    def test_no_defaults(self):
        reg = ErrorSiteRegistry(load_defaults=False)
        assert reg.pattern_count == 0

    def test_index_error_pattern_exists(self):
        reg = ErrorSiteRegistry()
        patterns = reg.get_patterns_for_error(ErrorKind.INDEX_ERROR)
        assert len(patterns) >= 1

    def test_key_error_pattern_exists(self):
        reg = ErrorSiteRegistry()
        patterns = reg.get_patterns_for_error(ErrorKind.KEY_ERROR)
        assert len(patterns) >= 1

    def test_type_error_pattern_exists(self):
        reg = ErrorSiteRegistry()
        patterns = reg.get_patterns_for_error(ErrorKind.TYPE_ERROR)
        assert len(patterns) >= 1

    def test_zero_division_error_pattern_exists(self):
        reg = ErrorSiteRegistry()
        patterns = reg.get_patterns_for_error(ErrorKind.ZERO_DIVISION_ERROR)
        assert len(patterns) >= 1

    def test_attribute_error_pattern_exists(self):
        reg = ErrorSiteRegistry()
        patterns = reg.get_patterns_for_error(ErrorKind.ATTRIBUTE_ERROR)
        assert len(patterns) >= 1

    def test_patterns_for_division_operation(self):
        reg = ErrorSiteRegistry()
        patterns = reg.get_patterns_for_operation(OperationKind.DIVISION)
        assert len(patterns) >= 1
        assert all(p.operation == OperationKind.DIVISION for p in patterns)

    def test_patterns_for_subscript_operation(self):
        reg = ErrorSiteRegistry()
        patterns = reg.get_patterns_for_operation(OperationKind.SUBSCRIPT)
        assert len(patterns) >= 1


# ============================================================================
# Pattern registration
# ============================================================================


class TestPatternRegistration:

    def test_register_custom_pattern(self):
        reg = ErrorSiteRegistry(load_defaults=False)
        viab = _make_viability("custom condition", ErrorKind.CUSTOM, OperationKind.CALL)
        pattern = ErrorPattern(
            _error_kind=ErrorKind.CUSTOM,
            _operation=OperationKind.CALL,
            _description="custom error",
            _viability=viab,
        )
        reg.register_pattern(pattern)
        assert reg.pattern_count == 1
        pats = reg.get_patterns_for_error(ErrorKind.CUSTOM)
        assert len(pats) == 1

    def test_register_error_pattern_by_components(self):
        reg = ErrorSiteRegistry(load_defaults=False)
        viab = _make_viability("domain error", ErrorKind.VALUE_ERROR, OperationKind.CALL)
        pattern = reg.register_error_pattern(ErrorKind.VALUE_ERROR, viab)
        assert isinstance(pattern, ErrorPattern)
        assert reg.pattern_count == 1


# ============================================================================
# Error site registration
# ============================================================================


class TestSiteRegistration:

    def test_register_error_site(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("div_0")
        entry = reg.register_error_site(
            sid, ErrorKind.ZERO_DIVISION_ERROR, OperationKind.DIVISION,
            source_operation="a / b", source_line=10,
        )
        assert isinstance(entry, ErrorSiteEntry)
        assert entry.site_id == sid
        assert entry.error_kind == ErrorKind.ZERO_DIVISION_ERROR
        assert entry.source_operation == "a / b"

    def test_registered_site_is_registered(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("div_1")
        reg.register_error_site(sid, ErrorKind.ZERO_DIVISION_ERROR, OperationKind.DIVISION)
        assert reg.is_registered(sid)

    def test_unregistered_site_not_registered(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("unknown")
        assert not reg.is_registered(sid)

    def test_guarded_site(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("guarded_err")
        reg.register_error_site(
            sid, ErrorKind.KEY_ERROR, OperationKind.DICT_LOOKUP, guarded=True,
        )
        assert sid in reg.get_guarded_sites()
        assert sid not in reg.get_unguarded_sites()

    def test_unguarded_site(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("unguarded_err")
        reg.register_error_site(
            sid, ErrorKind.INDEX_ERROR, OperationKind.LIST_ACCESS, guarded=False,
        )
        assert sid in reg.get_unguarded_sites()
        assert sid not in reg.get_guarded_sites()

    def test_explicit_raise(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("explicit")
        entry = reg.register_error_site(
            sid, ErrorKind.VALUE_ERROR, OperationKind.CALL,
            is_explicit_raise=True,
        )
        assert entry.is_explicit_raise is True


# ============================================================================
# Viability queries
# ============================================================================


class TestViabilityQueries:

    def test_get_viability_for_registered_site(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("div_v")
        reg.register_error_site(sid, ErrorKind.ZERO_DIVISION_ERROR, OperationKind.DIVISION)
        viab = reg.get_viability(sid)
        assert viab != "unknown"
        assert isinstance(viab, str)

    def test_get_viability_for_unknown_site(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("no_such_site")
        assert reg.get_viability(sid) == "unknown"

    def test_override_viability(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("overridden")
        reg.register_error_site(sid, ErrorKind.TYPE_ERROR, OperationKind.CALL)
        override = _make_viability("custom override", ErrorKind.TYPE_ERROR, OperationKind.CALL)
        reg.override_viability(sid, override)
        assert reg.get_viability(sid) == "custom override"

    def test_get_viability_predicate(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("pred_test")
        reg.register_error_site(sid, ErrorKind.KEY_ERROR, OperationKind.DICT_LOOKUP)
        pred = reg.get_viability_predicate(sid)
        assert pred is not None
        assert isinstance(pred, ViabilityPredicate)

    def test_is_viable(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("viable_test")
        reg.register_error_site(sid, ErrorKind.INDEX_ERROR, OperationKind.LIST_ACCESS)
        assert reg.is_viable(sid)

    def test_is_viable_unknown_site(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("unknown_viable")
        # Unknown sites are conservatively viable
        assert reg.is_viable(sid)


# ============================================================================
# Aggregate queries
# ============================================================================


class TestAggregateQueries:

    def test_all_error_sites(self):
        reg = ErrorSiteRegistry()
        s1 = _make_error_site_id("e1")
        s2 = _make_error_site_id("e2")
        reg.register_error_site(s1, ErrorKind.TYPE_ERROR, OperationKind.CALL)
        reg.register_error_site(s2, ErrorKind.KEY_ERROR, OperationKind.DICT_LOOKUP)
        all_sites = reg.all_error_sites
        assert s1 in all_sites
        assert s2 in all_sites

    def test_site_count(self):
        reg = ErrorSiteRegistry()
        assert reg.site_count == 0
        s1 = _make_error_site_id("e1")
        reg.register_error_site(s1, ErrorKind.TYPE_ERROR, OperationKind.CALL)
        assert reg.site_count == 1

    def test_error_kind_histogram(self):
        reg = ErrorSiteRegistry()
        for i in range(3):
            reg.register_error_site(
                _make_error_site_id(f"te_{i}"), ErrorKind.TYPE_ERROR, OperationKind.CALL
            )
        reg.register_error_site(
            _make_error_site_id("ke_0"), ErrorKind.KEY_ERROR, OperationKind.DICT_LOOKUP
        )
        hist = reg.error_kind_histogram()
        assert hist[ErrorKind.TYPE_ERROR] == 3
        assert hist[ErrorKind.KEY_ERROR] == 1

    def test_operation_histogram(self):
        reg = ErrorSiteRegistry()
        reg.register_error_site(
            _make_error_site_id("op1"), ErrorKind.TYPE_ERROR, OperationKind.CALL
        )
        reg.register_error_site(
            _make_error_site_id("op2"), ErrorKind.INDEX_ERROR, OperationKind.SUBSCRIPT
        )
        hist = reg.operation_histogram()
        assert hist[OperationKind.CALL] == 1
        assert hist[OperationKind.SUBSCRIPT] == 1

    def test_get_error_sites_for_operation(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("div_op")
        reg.register_error_site(
            sid, ErrorKind.ZERO_DIVISION_ERROR, OperationKind.DIVISION
        )
        sites = reg.get_error_sites_for_operation(OperationKind.DIVISION)
        assert sid in sites

    def test_get_error_sites_for_error(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("te_query")
        reg.register_error_site(sid, ErrorKind.TYPE_ERROR, OperationKind.CALL)
        sites = reg.get_error_sites_for_error(ErrorKind.TYPE_ERROR)
        assert sid in sites


# ============================================================================
# Merge and clear
# ============================================================================


class TestMergeAndClear:

    def test_merge_registries(self):
        r1 = ErrorSiteRegistry(load_defaults=False)
        r2 = ErrorSiteRegistry(load_defaults=False)
        s1 = _make_error_site_id("merge_1")
        s2 = _make_error_site_id("merge_2")
        r1.register_error_site(s1, ErrorKind.TYPE_ERROR, OperationKind.CALL)
        r2.register_error_site(s2, ErrorKind.KEY_ERROR, OperationKind.DICT_LOOKUP)
        r1.merge(r2)
        assert r1.is_registered(s1)
        assert r1.is_registered(s2)

    def test_clear_sites(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("clear_me")
        reg.register_error_site(sid, ErrorKind.TYPE_ERROR, OperationKind.CALL)
        reg.clear_sites()
        assert reg.site_count == 0
        assert not reg.is_registered(sid)
        # Patterns should still be there
        assert reg.pattern_count > 0


# ============================================================================
# ErrorKind.from_exception_name
# ============================================================================


class TestErrorKindFromName:

    def test_known_names(self):
        assert ErrorKind.from_exception_name("IndexError") == ErrorKind.INDEX_ERROR
        assert ErrorKind.from_exception_name("KeyError") == ErrorKind.KEY_ERROR
        assert ErrorKind.from_exception_name("TypeError") == ErrorKind.TYPE_ERROR

    def test_unknown_name(self):
        assert ErrorKind.from_exception_name("WeirdError") == ErrorKind.CUSTOM


# ============================================================================
# ViabilityPredicate properties
# ============================================================================


class TestViabilityPredicateProps:

    def test_properties(self):
        vp = ViabilityPredicate(
            _description="divisor == 0",
            _error_kind=ErrorKind.ZERO_DIVISION_ERROR,
            _operation=OperationKind.DIVISION,
            _guard_variable="divisor",
            _negation_description="divisor != 0",
            _confidence=0.9,
        )
        assert vp.description == "divisor == 0"
        assert vp.guard_variable == "divisor"
        assert vp.negation_description == "divisor != 0"
        assert vp.confidence == 0.9
        assert not vp.is_always_viable

    def test_always_viable(self):
        vp = ViabilityPredicate(
            _description="always",
            _error_kind=ErrorKind.RUNTIME_ERROR,
            _operation=OperationKind.CALL,
            _is_always_viable=True,
        )
        assert vp.is_always_viable

    def test_negation_default(self):
        vp = ViabilityPredicate(
            _description="some condition",
            _error_kind=ErrorKind.TYPE_ERROR,
            _operation=OperationKind.CALL,
        )
        assert "not(" in vp.negation_description


# ============================================================================
# Summary report
# ============================================================================


class TestSummaryReport:

    def test_summary_report(self):
        reg = ErrorSiteRegistry()
        sid = _make_error_site_id("report_test")
        reg.register_error_site(sid, ErrorKind.TYPE_ERROR, OperationKind.CALL)
        report = reg.summary_report()
        assert "ErrorSiteRegistry" in report

    def test_repr(self):
        reg = ErrorSiteRegistry()
        assert "ErrorSiteRegistry" in repr(reg)
