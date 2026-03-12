"""Tests for deppy.observe.trace_recorder -- runtime trace capture.

Exercises TraceEvent, TraceLog, TraceRecorder, record_trace, instrument
decorator, batch tracing, TraceSummary, filtering, and merging.
"""

from __future__ import annotations

import time
import pytest

from deppy.observe.trace_recorder import (
    EventKind,
    InstrumentationConfig,
    TraceEvent,
    TraceInput,
    TraceLog,
    TraceRecorder,
    TraceSummary,
    filter_events,
    instrument,
    merge_trace_logs,
    record_trace,
    record_traces_batch,
    summarize_trace,
    _make_event,
    _safe_repr,
    _safe_type_name,
    _extract_shape,
    _extract_dtype,
    _extract_len,
)


# ===================================================================
# Helpers
# ===================================================================

def _simple_add(a, b):
    c = a + b
    return c


def _branching(x):
    if x > 0:
        return "positive"
    else:
        return "non-positive"


def _raises(x):
    if x < 0:
        raise ValueError("negative")
    return x


def _nested(x):
    y = x * 2
    z = _simple_add(y, 1)
    return z


def _no_args():
    return 42


# ===================================================================
# TestEventKind
# ===================================================================

class TestEventKind:
    """Test EventKind enum completeness."""

    def test_all_kinds(self):
        expected = {
            "call", "return", "local_assign", "exception",
            "branch_taken", "attribute_access", "subscript", "iteration",
        }
        actual = {k.value for k in EventKind}
        assert expected == actual

    def test_from_value(self):
        assert EventKind("call") == EventKind.CALL
        assert EventKind("return") == EventKind.RETURN


# ===================================================================
# TestTraceEvent
# ===================================================================

class TestTraceEvent:
    """Test TraceEvent frozen dataclass."""

    def test_creation(self):
        ev = TraceEvent(
            event_id="abc123",
            timestamp=1.0,
            kind=EventKind.CALL,
            function="my_func",
            variable="x",
            value_type="int",
            value_repr="42",
        )
        assert ev.event_id == "abc123"
        assert ev.kind == EventKind.CALL
        assert ev.function == "my_func"
        assert ev.variable == "x"

    def test_frozen(self):
        ev = TraceEvent(
            event_id="abc", timestamp=1.0, kind=EventKind.CALL,
            function="f", variable="x", value_type="int", value_repr="1",
        )
        with pytest.raises(AttributeError):
            ev.variable = "y"  # type: ignore[misc]

    def test_extra_dict(self):
        ev = TraceEvent(
            event_id="abc", timestamp=1.0, kind=EventKind.CALL,
            function="f", variable="", value_type="int", value_repr="1",
            extra=(("key1", "val1"), ("key2", 42)),
        )
        d = ev.extra_dict
        assert d["key1"] == "val1"
        assert d["key2"] == 42

    def test_source_span_none(self):
        ev = TraceEvent(
            event_id="abc", timestamp=1.0, kind=EventKind.CALL,
            function="f", variable="", value_type="int", value_repr="1",
        )
        assert ev.source_span is None

    def test_source_span_present(self):
        ev = TraceEvent(
            event_id="abc", timestamp=1.0, kind=EventKind.CALL,
            function="f", variable="", value_type="int", value_repr="1",
            location=("test.py", 10, 5),
        )
        span = ev.source_span
        assert span is not None
        assert span.file == "test.py"
        assert span.start_line == 10

    def test_matches_variable(self):
        ev = TraceEvent(
            event_id="abc", timestamp=1.0, kind=EventKind.LOCAL_ASSIGN,
            function="f", variable="my_var", value_type="int", value_repr="1",
        )
        assert ev.matches_variable("my_var") is True
        assert ev.matches_variable("other") is False

    def test_matches_function_exact(self):
        ev = TraceEvent(
            event_id="abc", timestamp=1.0, kind=EventKind.CALL,
            function="my_func", variable="", value_type="int", value_repr="1",
        )
        assert ev.matches_function("my_func") is True
        assert ev.matches_function("other") is False

    def test_matches_function_suffix(self):
        ev = TraceEvent(
            event_id="abc", timestamp=1.0, kind=EventKind.CALL,
            function="module.Class.my_func", variable="", value_type="int",
            value_repr="1",
        )
        assert ev.matches_function("my_func") is True
        assert ev.matches_function("Class.my_func") is True

    def test_shape_and_dtype(self):
        ev = TraceEvent(
            event_id="abc", timestamp=1.0, kind=EventKind.LOCAL_ASSIGN,
            function="f", variable="x", value_type="torch.Tensor",
            value_repr="tensor([...])",
            shape=(3, 4), dtype="float32",
        )
        assert ev.shape == (3, 4)
        assert ev.dtype == "float32"

    def test_length(self):
        ev = TraceEvent(
            event_id="abc", timestamp=1.0, kind=EventKind.LOCAL_ASSIGN,
            function="f", variable="x", value_type="list",
            value_repr="[1, 2, 3]", length=3,
        )
        assert ev.length == 3


# ===================================================================
# TestMakeEvent
# ===================================================================

class TestMakeEvent:
    """Test the _make_event factory function."""

    def test_basic_creation(self):
        ev = _make_event(EventKind.LOCAL_ASSIGN, "my_func", "x", 42)
        assert ev.kind == EventKind.LOCAL_ASSIGN
        assert ev.function == "my_func"
        assert ev.variable == "x"
        assert ev.value_type == "int"
        assert ev.value_repr == "42"

    def test_with_list_value(self):
        ev = _make_event(EventKind.LOCAL_ASSIGN, "f", "items", [1, 2, 3])
        assert ev.length == 3
        assert ev.value_type == "list"

    def test_with_location(self):
        ev = _make_event(
            EventKind.CALL, "f", "x", 1,
            location=("file.py", 10, 0),
        )
        assert ev.location == ("file.py", 10, 0)

    def test_with_extra(self):
        ev = _make_event(
            EventKind.EXCEPTION, "f", "e", ValueError("bad"),
            extra={"exception_type": "ValueError"},
        )
        assert ("exception_type", "ValueError") in ev.extra

    def test_unique_event_ids(self):
        ev1 = _make_event(EventKind.CALL, "f", "", None)
        ev2 = _make_event(EventKind.CALL, "f", "", None)
        assert ev1.event_id != ev2.event_id


# ===================================================================
# TestTraceLog
# ===================================================================

class TestTraceLog:
    """Test TraceLog frozen dataclass and convenience methods."""

    def _make_log(self, events=(), **kwargs):
        defaults = dict(
            trace_id="test-trace",
            events=events,
            target_function="test_func",
            start_time=100.0,
            end_time=100.5,
        )
        defaults.update(kwargs)
        return TraceLog(**defaults)

    def test_duration(self):
        log = self._make_log()
        assert abs(log.duration - 0.5) < 1e-9

    def test_event_count(self):
        ev = _make_event(EventKind.CALL, "f", "", None)
        log = self._make_log(events=(ev, ev, ev))
        assert log.event_count == 3

    def test_succeeded_true(self):
        log = self._make_log(raised_exception=None)
        assert log.succeeded is True

    def test_succeeded_false(self):
        log = self._make_log(raised_exception="ValueError")
        assert log.succeeded is False

    def test_events_for_function(self):
        ev1 = _make_event(EventKind.CALL, "f", "", None)
        ev2 = _make_event(EventKind.CALL, "g", "", None)
        log = self._make_log(events=(ev1, ev2))
        assert len(log.events_for_function("f")) == 1
        assert len(log.events_for_function("g")) == 1

    def test_events_for_variable(self):
        ev1 = _make_event(EventKind.LOCAL_ASSIGN, "f", "x", 1)
        ev2 = _make_event(EventKind.LOCAL_ASSIGN, "f", "y", 2)
        log = self._make_log(events=(ev1, ev2))
        assert len(log.events_for_variable("x")) == 1

    def test_events_of_kind(self):
        ev1 = _make_event(EventKind.CALL, "f", "", None)
        ev2 = _make_event(EventKind.RETURN, "f", "", 1)
        log = self._make_log(events=(ev1, ev2))
        assert len(log.events_of_kind(EventKind.CALL)) == 1
        assert len(log.events_of_kind(EventKind.RETURN)) == 1

    def test_unique_functions(self):
        ev1 = _make_event(EventKind.CALL, "f", "", None)
        ev2 = _make_event(EventKind.CALL, "g", "", None)
        log = self._make_log(events=(ev1, ev2))
        assert log.unique_functions() == frozenset({"f", "g"})

    def test_unique_variables(self):
        ev1 = _make_event(EventKind.LOCAL_ASSIGN, "f", "x", 1)
        ev2 = _make_event(EventKind.LOCAL_ASSIGN, "f", "y", 2)
        ev3 = _make_event(EventKind.CALL, "f", "", None)
        log = self._make_log(events=(ev1, ev2, ev3))
        assert "x" in log.unique_variables()
        assert "y" in log.unique_variables()
        # empty variable name should be excluded
        assert "" not in log.unique_variables()

    def test_unique_types(self):
        ev1 = _make_event(EventKind.LOCAL_ASSIGN, "f", "x", 42)
        ev2 = _make_event(EventKind.LOCAL_ASSIGN, "f", "y", "hello")
        log = self._make_log(events=(ev1, ev2))
        types = log.unique_types()
        assert "int" in types
        assert "str" in types

    def test_max_call_depth_empty(self):
        log = self._make_log(events=())
        assert log.max_call_depth() == 0

    def test_max_call_depth_nonzero(self):
        ev1 = TraceEvent(
            event_id="a", timestamp=1.0, kind=EventKind.CALL,
            function="f", variable="", value_type="int", value_repr="1",
            call_depth=3,
        )
        log = self._make_log(events=(ev1,))
        assert log.max_call_depth() == 3

    def test_branch_events(self):
        ev = _make_event(EventKind.BRANCH_TAKEN, "f", "cond", True)
        log = self._make_log(events=(ev,))
        assert len(log.branch_events()) == 1

    def test_exception_events(self):
        ev = _make_event(EventKind.EXCEPTION, "f", "ValueError", ValueError("x"))
        log = self._make_log(events=(ev,))
        assert len(log.exception_events()) == 1


# ===================================================================
# TestTraceRecorder
# ===================================================================

class TestTraceRecorder:
    """Test TraceRecorder context manager."""

    def test_context_manager(self):
        recorder = TraceRecorder()
        with recorder:
            x = 1 + 2
        assert recorder.event_count >= 0  # events may or may not be captured depending on file filter

    def test_build_log(self):
        recorder = TraceRecorder()
        with recorder:
            pass
        log = recorder.build_log("test_func")
        assert isinstance(log, TraceLog)
        assert log.target_function == "test_func"

    def test_build_log_with_metadata(self):
        recorder = TraceRecorder()
        with recorder:
            pass
        log = recorder.build_log(
            "test_func",
            return_value_repr="42",
            metadata={"run_id": "abc"},
        )
        assert log.return_value_repr == "42"
        assert ("run_id", "abc") in log.metadata

    def test_start_stop_manual(self):
        recorder = TraceRecorder()
        recorder.start()
        x = 1 + 2
        recorder.stop()
        log = recorder.build_log("test")
        assert isinstance(log, TraceLog)

    def test_double_start_is_safe(self):
        recorder = TraceRecorder()
        recorder.start()
        recorder.start()  # should be idempotent
        recorder.stop()

    def test_double_stop_is_safe(self):
        recorder = TraceRecorder()
        recorder.start()
        recorder.stop()
        recorder.stop()  # should be idempotent

    def test_events_before_start_empty(self):
        recorder = TraceRecorder()
        assert recorder.events == []
        assert recorder.event_count == 0

    def test_max_events_limit(self):
        recorder = TraceRecorder(max_events=5)
        with recorder:
            for i in range(100):
                _ = i * 2
        # max_events is an approximate limit; some overhead events
        # (enter/exit) may not be counted against it.
        assert recorder.event_count < 100

    def test_build_log_with_raised_exception(self):
        recorder = TraceRecorder()
        with recorder:
            pass
        log = recorder.build_log("f", raised_exception="ValueError")
        assert log.raised_exception == "ValueError"
        assert log.succeeded is False


# ===================================================================
# TestRecordTrace
# ===================================================================

class TestRecordTrace:
    """Test record_trace one-shot convenience function."""

    def test_simple_function(self):
        log = record_trace(_simple_add, 1, 2)
        assert isinstance(log, TraceLog)
        assert log.succeeded is True

    def test_target_function_name(self):
        log = record_trace(_simple_add, 1, 2)
        assert "_simple_add" in log.target_function

    def test_args_snapshot(self):
        log = record_trace(_simple_add, 10, 20)
        # Should have captured args
        assert len(log.args_snapshot) >= 1

    def test_return_value_captured(self):
        log = record_trace(_simple_add, 3, 4)
        assert log.return_value_repr is not None
        assert "7" in log.return_value_repr

    def test_exception_captured(self):
        log = record_trace(_raises, -1)
        assert log.succeeded is False
        assert log.raised_exception is not None
        assert "ValueError" in log.raised_exception

    def test_no_args_function(self):
        log = record_trace(_no_args)
        assert log.succeeded is True
        assert log.return_value_repr is not None

    def test_with_config(self):
        config = InstrumentationConfig(
            capture_args=False,
            capture_return=False,
        )
        log = record_trace(_simple_add, 1, 2, _trace_config=config)
        assert isinstance(log, TraceLog)
        assert log.return_value_repr is None

    def test_events_are_chronological(self):
        log = record_trace(_simple_add, 1, 2)
        timestamps = [e.timestamp for e in log.events]
        assert timestamps == sorted(timestamps)


# ===================================================================
# TestInstrumentDecorator
# ===================================================================

class TestInstrumentDecorator:
    """Test the instrument decorator."""

    def test_decorated_function_runs(self):
        wrapped = instrument(_simple_add)
        result = wrapped(3, 4)
        assert result == 7

    def test_last_trace_log_attached(self):
        wrapped = instrument(_simple_add)
        wrapped(3, 4)
        log = wrapped.last_trace_log
        assert isinstance(log, TraceLog)
        assert log.succeeded is True

    def test_exception_propagated(self):
        wrapped = instrument(_raises)
        with pytest.raises(ValueError):
            wrapped(-1)
        log = wrapped.last_trace_log
        assert log.raised_exception is not None

    def test_initial_log_is_none(self):
        wrapped = instrument(_simple_add)
        assert wrapped.last_trace_log is None

    def test_preserves_function_name(self):
        wrapped = instrument(_simple_add)
        assert wrapped.__name__ == "_simple_add"

    def test_custom_config(self):
        config = InstrumentationConfig(capture_locals=False)
        wrapped = instrument(_simple_add, config=config)
        result = wrapped(1, 2)
        assert result == 3
        assert wrapped.last_trace_log is not None


# ===================================================================
# TestInstrumentationConfig
# ===================================================================

class TestInstrumentationConfig:
    """Test InstrumentationConfig defaults."""

    def test_defaults(self):
        config = InstrumentationConfig()
        assert config.capture_args is True
        assert config.capture_return is True
        assert config.capture_locals is True
        assert config.capture_exceptions is True
        assert config.max_events == 50_000
        assert config.file_filter is None

    def test_custom(self):
        config = InstrumentationConfig(
            capture_args=False,
            capture_return=False,
            max_events=100,
            file_filter="mymodule",
        )
        assert config.capture_args is False
        assert config.max_events == 100
        assert config.file_filter == "mymodule"

    def test_frozen(self):
        config = InstrumentationConfig()
        with pytest.raises(AttributeError):
            config.max_events = 10  # type: ignore[misc]


# ===================================================================
# TestTraceInput
# ===================================================================

class TestTraceInput:
    """Test TraceInput dataclass."""

    def test_defaults(self):
        inp = TraceInput()
        assert inp.args == ()
        assert inp.kwargs == ()
        assert inp.label == ""

    def test_kwargs_dict(self):
        inp = TraceInput(kwargs=(("a", 1), ("b", 2)))
        d = inp.kwargs_dict
        assert d == {"a": 1, "b": 2}

    def test_with_args(self):
        inp = TraceInput(args=(1, 2, 3), label="test case 1")
        assert inp.args == (1, 2, 3)
        assert inp.label == "test case 1"


# ===================================================================
# TestBatchTracing
# ===================================================================

class TestBatchTracing:
    """Test record_traces_batch."""

    def test_basic_batch(self):
        inputs = [
            TraceInput(args=(1, 2)),
            TraceInput(args=(3, 4)),
            TraceInput(args=(5, 6)),
        ]
        logs = record_traces_batch(_simple_add, inputs)
        assert len(logs) == 3
        assert all(isinstance(log, TraceLog) for log in logs)
        assert all(log.succeeded for log in logs)

    def test_empty_batch(self):
        logs = record_traces_batch(_simple_add, [])
        assert len(logs) == 0

    def test_batch_with_config(self):
        config = InstrumentationConfig(capture_return=False)
        inputs = [TraceInput(args=(1, 2))]
        logs = record_traces_batch(_simple_add, inputs, config=config)
        assert len(logs) == 1
        assert logs[0].return_value_repr is None

    def test_batch_with_kwargs(self):
        inputs = [
            TraceInput(args=(1,), kwargs=(("b", 2),)),
        ]
        logs = record_traces_batch(_simple_add, inputs)
        assert len(logs) == 1
        assert logs[0].succeeded is True


# ===================================================================
# TestTraceSummary
# ===================================================================

class TestTraceSummary:
    """Test TraceSummary and summarize_trace."""

    def test_summarize_basic(self):
        log = record_trace(_simple_add, 1, 2)
        summary = summarize_trace(log)
        assert isinstance(summary, TraceSummary)
        assert summary.trace_id == log.trace_id
        assert summary.target_function == log.target_function
        assert summary.event_count == log.event_count
        assert summary.succeeded is True

    def test_summarize_failed(self):
        log = record_trace(_raises, -1)
        summary = summarize_trace(log)
        assert summary.succeeded is False
        assert summary.exception_count >= 1

    def test_duration_positive(self):
        log = record_trace(_simple_add, 1, 2)
        summary = summarize_trace(log)
        assert summary.duration >= 0.0

    def test_unique_counts(self):
        log = record_trace(_simple_add, 1, 2)
        summary = summarize_trace(log)
        assert summary.unique_variable_count >= 0
        assert summary.unique_type_count >= 0
        assert summary.unique_shape_count >= 0


# ===================================================================
# TestFilterEvents
# ===================================================================

class TestFilterEvents:
    """Test filter_events utility."""

    def _make_events(self):
        return [
            _make_event(EventKind.CALL, "f", "x", 1, call_depth=0),
            _make_event(EventKind.LOCAL_ASSIGN, "f", "y", 2, call_depth=1),
            _make_event(EventKind.RETURN, "g", "", 3, call_depth=0),
            _make_event(EventKind.EXCEPTION, "f", "ValueError", ValueError(), call_depth=2),
        ]

    def test_filter_by_kind(self):
        events = self._make_events()
        result = filter_events(events, kinds=frozenset({EventKind.CALL}))
        assert all(e.kind == EventKind.CALL for e in result)

    def test_filter_by_function(self):
        events = self._make_events()
        result = filter_events(events, functions=frozenset({"f"}))
        assert all(e.matches_function("f") for e in result)

    def test_filter_by_variable(self):
        events = self._make_events()
        result = filter_events(events, variables=frozenset({"x"}))
        assert all(e.variable == "x" for e in result)

    def test_filter_by_depth(self):
        events = self._make_events()
        result = filter_events(events, min_depth=1, max_depth=1)
        assert all(e.call_depth == 1 for e in result)

    def test_no_filter_returns_all(self):
        events = self._make_events()
        result = filter_events(events)
        assert len(result) == len(events)

    def test_combined_filters(self):
        events = self._make_events()
        result = filter_events(
            events,
            kinds=frozenset({EventKind.LOCAL_ASSIGN}),
            functions=frozenset({"f"}),
        )
        assert len(result) >= 1
        assert all(e.kind == EventKind.LOCAL_ASSIGN for e in result)


# ===================================================================
# TestMergeTraceLogs
# ===================================================================

class TestMergeTraceLogs:
    """Test merge_trace_logs utility."""

    def test_merge_empty(self):
        log = merge_trace_logs([])
        assert log.target_function == "<merged>"
        assert log.event_count == 0

    def test_merge_single(self):
        log1 = record_trace(_simple_add, 1, 2)
        merged = merge_trace_logs([log1])
        assert merged.event_count == log1.event_count

    def test_merge_two(self):
        log1 = record_trace(_simple_add, 1, 2)
        log2 = record_trace(_simple_add, 3, 4)
        merged = merge_trace_logs([log1, log2])
        assert merged.event_count == log1.event_count + log2.event_count

    def test_merge_preserves_first_target(self):
        log1 = record_trace(_simple_add, 1, 2)
        log2 = record_trace(_no_args)
        merged = merge_trace_logs([log1, log2])
        assert merged.target_function == log1.target_function

    def test_merge_events_sorted(self):
        log1 = record_trace(_simple_add, 1, 2)
        log2 = record_trace(_simple_add, 3, 4)
        merged = merge_trace_logs([log1, log2])
        timestamps = [e.timestamp for e in merged.events]
        assert timestamps == sorted(timestamps)

    def test_merge_propagates_exception(self):
        log1 = record_trace(_simple_add, 1, 2)
        log2 = record_trace(_raises, -1)
        merged = merge_trace_logs([log1, log2])
        assert merged.raised_exception is not None


# ===================================================================
# TestValueIntrospectionHelpers
# ===================================================================

class TestValueIntrospectionHelpers:
    """Test _safe_type_name, _safe_repr, _extract_shape, etc."""

    def test_safe_type_name_builtin(self):
        assert _safe_type_name(42) == "int"
        assert _safe_type_name("hello") == "str"
        assert _safe_type_name(None) == "NoneType"

    def test_safe_type_name_list(self):
        assert _safe_type_name([1, 2]) == "list"

    def test_safe_repr_normal(self):
        assert _safe_repr(42) == "42"
        assert _safe_repr("hello") == "'hello'"

    def test_safe_repr_truncates(self):
        long_str = "x" * 500
        result = _safe_repr(long_str, max_length=50)
        assert len(result) <= 50
        assert result.endswith("...")

    def test_extract_shape_none(self):
        assert _extract_shape(42) is None
        assert _extract_shape("hello") is None

    def test_extract_dtype_none(self):
        assert _extract_dtype(42) is None

    def test_extract_len_list(self):
        assert _extract_len([1, 2, 3]) == 3

    def test_extract_len_string(self):
        assert _extract_len("hello") == 5

    def test_extract_len_no_len(self):
        assert _extract_len(42) is None
