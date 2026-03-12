"""Instrument and record runtime traces for dynamic observation.

This module provides the core tracing infrastructure that captures runtime
behaviour of Python functions.  Captured traces are later parsed into
structured observations and converted into local sections with
``TrustLevel.TRACE_BACKED``.

The primary entry-point is :func:`record_trace`, which instruments a
callable and returns a :class:`TraceLog` containing every observed
:class:`TraceEvent`.  Two instrumentation strategies are available:

1. **sys.settrace-based** -- low-overhead, captures every local assignment
   and return value via the CPython trace hook.
2. **decorator-based** -- wraps the target callable with explicit
   recording logic (used when settrace is unavailable or when
   fine-grained control is preferred).

Both strategies produce the same :class:`TraceEvent` / :class:`TraceLog`
representation so that downstream consumers (``trace_parser``,
``trace_to_section``) are agnostic to the recording mechanism.
"""

from __future__ import annotations

import contextlib
import copy
import enum
import functools
import inspect
import sys
import threading
import time
import types as builtin_types
import uuid
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterable,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    TypeVar,
    Union,
)

from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.static_analysis.observation_sites import SourceSpan, TraceSiteData


# ---------------------------------------------------------------------------
# Value introspection helpers
# ---------------------------------------------------------------------------

_F = TypeVar("_F", bound=Callable[..., Any])


def _safe_type_name(value: Any) -> str:
    """Return the fully-qualified type name, safely."""
    try:
        tp = type(value)
        module = getattr(tp, "__module__", "")
        qualname = getattr(tp, "__qualname__", tp.__name__)
        if module and module != "builtins":
            return f"{module}.{qualname}"
        return qualname
    except Exception:
        return "<unknown>"


def _safe_repr(value: Any, max_length: int = 200) -> str:
    """Return a truncated repr that never raises."""
    try:
        r = repr(value)
        if len(r) > max_length:
            return r[: max_length - 3] + "..."
        return r
    except Exception:
        return "<unrepresentable>"


def _extract_shape(value: Any) -> Optional[Tuple[int, ...]]:
    """Extract tensor/array shape if the value has a ``.shape`` attribute."""
    try:
        shape_attr = getattr(value, "shape", None)
        if shape_attr is not None:
            shape_tuple = tuple(int(d) for d in shape_attr)
            return shape_tuple
    except Exception:
        pass
    return None


def _extract_dtype(value: Any) -> Optional[str]:
    """Extract tensor/array dtype if available."""
    try:
        dtype_attr = getattr(value, "dtype", None)
        if dtype_attr is not None:
            return str(dtype_attr)
    except Exception:
        pass
    return None


def _extract_len(value: Any) -> Optional[int]:
    """Extract length for sized containers."""
    try:
        if hasattr(value, "__len__"):
            return len(value)
    except Exception:
        pass
    return None


# ---------------------------------------------------------------------------
# Event kind enumeration
# ---------------------------------------------------------------------------

class EventKind(enum.Enum):
    """Classifies what a :class:`TraceEvent` captures."""
    CALL = "call"
    RETURN = "return"
    LOCAL_ASSIGN = "local_assign"
    EXCEPTION = "exception"
    BRANCH_TAKEN = "branch_taken"
    ATTRIBUTE_ACCESS = "attribute_access"
    SUBSCRIPT = "subscript"
    ITERATION = "iteration"


# ---------------------------------------------------------------------------
# TraceEvent
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TraceEvent:
    """A single observed event during dynamic execution.

    Frozen so that trace logs are tamper-proof once recorded.

    Attributes
    ----------
    event_id : str
        UUID uniquely identifying this event.
    timestamp : float
        Wall-clock time (``time.monotonic()``) when the event was captured.
    kind : EventKind
        Classification of the event.
    function : str
        Qualified name of the function in which the event occurred.
    variable : str
        Name of the variable or expression being observed, or ``""``
        for call/return events that have no specific variable.
    value_type : str
        Fully-qualified type name of the observed value.
    value_repr : str
        Truncated ``repr`` of the observed value.
    shape : Optional[Tuple[int, ...]]
        Tensor / array shape, if applicable.
    dtype : Optional[str]
        Element dtype for tensors / arrays, if applicable.
    length : Optional[int]
        Container length, if applicable.
    location : Optional[Tuple[str, int, int]]
        ``(file, line, col)`` identifying the source position.
    call_depth : int
        Nesting depth relative to the outermost traced call.
    thread_id : int
        OS-level thread identifier.
    extra : Dict[str, Any]
        Arbitrary additional metadata attached by instrumentation hooks.
    """

    event_id: str
    timestamp: float
    kind: EventKind
    function: str
    variable: str
    value_type: str
    value_repr: str
    shape: Optional[Tuple[int, ...]] = None
    dtype: Optional[str] = None
    length: Optional[int] = None
    location: Optional[Tuple[str, int, int]] = None
    call_depth: int = 0
    thread_id: int = 0
    extra: Tuple[Tuple[str, Any], ...] = ()

    # Convenience ---------------------------------------------------------

    @property
    def extra_dict(self) -> Dict[str, Any]:
        """Return *extra* as a mutable dictionary."""
        return dict(self.extra)

    @property
    def source_span(self) -> Optional[SourceSpan]:
        """Convert *location* to a :class:`SourceSpan`, if set."""
        if self.location is None:
            return None
        f, line, col = self.location
        return SourceSpan(file=f, start_line=line, start_col=col)

    def matches_variable(self, name: str) -> bool:
        """Return ``True`` if *variable* equals *name* (case-sensitive)."""
        return self.variable == name

    def matches_function(self, name: str) -> bool:
        """Return ``True`` if *function* ends with *name*."""
        return self.function == name or self.function.endswith(f".{name}")


# ---------------------------------------------------------------------------
# TraceEvent factory
# ---------------------------------------------------------------------------

def _make_event(
    kind: EventKind,
    function: str,
    variable: str,
    value: Any,
    *,
    location: Optional[Tuple[str, int, int]] = None,
    call_depth: int = 0,
    extra: Optional[Dict[str, Any]] = None,
) -> TraceEvent:
    """Construct a :class:`TraceEvent` from a raw observed *value*."""
    return TraceEvent(
        event_id=uuid.uuid4().hex[:16],
        timestamp=time.monotonic(),
        kind=kind,
        function=function,
        variable=variable,
        value_type=_safe_type_name(value),
        value_repr=_safe_repr(value),
        shape=_extract_shape(value),
        dtype=_extract_dtype(value),
        length=_extract_len(value),
        location=location,
        call_depth=call_depth,
        thread_id=threading.get_ident(),
        extra=tuple(sorted((extra or {}).items())),
    )


# ---------------------------------------------------------------------------
# TraceLog
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TraceLog:
    """Immutable collection of :class:`TraceEvent` objects from a single run.

    Attributes
    ----------
    trace_id : str
        UUID for the overall trace session.
    events : Tuple[TraceEvent, ...]
        Chronologically ordered events.
    target_function : str
        Qualified name of the function that was traced.
    start_time : float
        Monotonic timestamp when recording began.
    end_time : float
        Monotonic timestamp when recording ended.
    args_snapshot : Tuple[Tuple[str, str], ...]
        ``(param_name, repr)`` for each positional/keyword argument.
    return_value_repr : Optional[str]
        Truncated repr of the return value, if the call completed normally.
    raised_exception : Optional[str]
        Type name of the exception raised, if the call failed.
    metadata : Tuple[Tuple[str, Any], ...]
        Extra session-level metadata.
    """

    trace_id: str
    events: Tuple[TraceEvent, ...]
    target_function: str
    start_time: float
    end_time: float
    args_snapshot: Tuple[Tuple[str, str], ...] = ()
    return_value_repr: Optional[str] = None
    raised_exception: Optional[str] = None
    metadata: Tuple[Tuple[str, Any], ...] = ()

    # Convenience ---------------------------------------------------------

    @property
    def duration(self) -> float:
        """Wall-clock duration in seconds."""
        return self.end_time - self.start_time

    @property
    def event_count(self) -> int:
        return len(self.events)

    @property
    def succeeded(self) -> bool:
        """True when the traced call returned without raising."""
        return self.raised_exception is None

    def events_for_function(self, name: str) -> Tuple[TraceEvent, ...]:
        """Filter events belonging to a specific function."""
        return tuple(e for e in self.events if e.matches_function(name))

    def events_for_variable(self, name: str) -> Tuple[TraceEvent, ...]:
        """Filter events that observe a specific variable."""
        return tuple(e for e in self.events if e.matches_variable(name))

    def events_of_kind(self, kind: EventKind) -> Tuple[TraceEvent, ...]:
        """Filter events by :class:`EventKind`."""
        return tuple(e for e in self.events if e.kind == kind)

    def unique_functions(self) -> FrozenSet[str]:
        """Return all distinct function names observed."""
        return frozenset(e.function for e in self.events)

    def unique_variables(self) -> FrozenSet[str]:
        """Return all distinct variable names observed."""
        return frozenset(e.variable for e in self.events if e.variable)

    def unique_types(self) -> FrozenSet[str]:
        """Return all distinct value types observed."""
        return frozenset(e.value_type for e in self.events)

    def unique_shapes(self) -> FrozenSet[Optional[Tuple[int, ...]]]:
        """Return all distinct shapes observed."""
        return frozenset(e.shape for e in self.events if e.shape is not None)

    def max_call_depth(self) -> int:
        """Return the maximum call depth reached."""
        if not self.events:
            return 0
        return max(e.call_depth for e in self.events)

    def branch_events(self) -> Tuple[TraceEvent, ...]:
        """Return events corresponding to branch decisions."""
        return self.events_of_kind(EventKind.BRANCH_TAKEN)

    def exception_events(self) -> Tuple[TraceEvent, ...]:
        """Return events corresponding to raised exceptions."""
        return self.events_of_kind(EventKind.EXCEPTION)


# ---------------------------------------------------------------------------
# TraceRecorder -- settrace-based strategy
# ---------------------------------------------------------------------------

class _SettraceState:
    """Per-thread mutable state for the settrace callback."""

    __slots__ = (
        "events",
        "root_function",
        "depth",
        "file_filter",
        "max_events",
        "active",
    )

    def __init__(
        self,
        root_function: str,
        file_filter: Optional[str],
        max_events: int,
    ) -> None:
        self.events: List[TraceEvent] = []
        self.root_function = root_function
        self.depth = 0
        self.file_filter = file_filter
        self.max_events = max_events
        self.active = True


def _settrace_callback(
    state: _SettraceState,
    frame: builtin_types.FrameType,
    event: str,
    arg: Any,
) -> Optional[Callable[..., Any]]:
    """CPython trace callback that populates *state.events*."""
    if not state.active or len(state.events) >= state.max_events:
        return None

    filename = frame.f_code.co_filename
    if state.file_filter and state.file_filter not in filename:
        return functools.partial(_settrace_callback, state)

    func_name = frame.f_code.co_qualname if hasattr(frame.f_code, "co_qualname") else frame.f_code.co_name
    lineno = frame.f_lineno
    location = (filename, lineno, 0)

    if event == "call":
        state.depth += 1
        # Record argument values from locals
        sig_params = _extract_params_from_frame(frame)
        for pname, pval in sig_params:
            state.events.append(
                _make_event(
                    EventKind.CALL,
                    func_name,
                    pname,
                    pval,
                    location=location,
                    call_depth=state.depth,
                )
            )
        if not sig_params:
            state.events.append(
                _make_event(
                    EventKind.CALL,
                    func_name,
                    "",
                    None,
                    location=location,
                    call_depth=state.depth,
                )
            )
        return functools.partial(_settrace_callback, state)

    if event == "return":
        state.events.append(
            _make_event(
                EventKind.RETURN,
                func_name,
                "",
                arg,
                location=location,
                call_depth=state.depth,
            )
        )
        state.depth = max(0, state.depth - 1)
        return functools.partial(_settrace_callback, state)

    if event == "exception":
        exc_type, exc_value, _tb = arg if isinstance(arg, tuple) else (arg, arg, None)
        state.events.append(
            _make_event(
                EventKind.EXCEPTION,
                func_name,
                _safe_type_name(exc_type) if exc_type else "",
                exc_value,
                location=location,
                call_depth=state.depth,
                extra={"exception_type": _safe_type_name(exc_type) if exc_type else ""},
            )
        )
        return functools.partial(_settrace_callback, state)

    if event == "line":
        # Capture local variable assignments by diffing locals
        _record_locals_snapshot(state, frame, func_name, location)
        return functools.partial(_settrace_callback, state)

    return functools.partial(_settrace_callback, state)


def _extract_params_from_frame(
    frame: builtin_types.FrameType,
) -> List[Tuple[str, Any]]:
    """Extract parameter (name, value) pairs from a call frame."""
    code = frame.f_code
    nargs = code.co_argcount + code.co_kwonlyargcount
    varnames = code.co_varnames[:nargs]
    result: List[Tuple[str, Any]] = []
    for name in varnames:
        if name in frame.f_locals:
            result.append((name, frame.f_locals[name]))
    return result


_LOCALS_PREV: Dict[int, Dict[str, str]] = {}


def _record_locals_snapshot(
    state: _SettraceState,
    frame: builtin_types.FrameType,
    func_name: str,
    location: Tuple[str, int, int],
) -> None:
    """Compare locals to the previous snapshot and emit assignment events."""
    frame_id = id(frame)
    current_locals: Dict[str, str] = {}
    for vname, vval in frame.f_locals.items():
        if vname.startswith("__") or vname.startswith("@"):
            continue
        current_locals[vname] = _safe_repr(vval, 80)
    prev = _LOCALS_PREV.get(frame_id, {})
    for vname in current_locals:
        if vname not in prev or prev[vname] != current_locals[vname]:
            raw_val = frame.f_locals.get(vname)
            state.events.append(
                _make_event(
                    EventKind.LOCAL_ASSIGN,
                    func_name,
                    vname,
                    raw_val,
                    location=location,
                    call_depth=state.depth,
                )
            )
    _LOCALS_PREV[frame_id] = current_locals


# ---------------------------------------------------------------------------
# TraceRecorder context manager
# ---------------------------------------------------------------------------

class TraceRecorder:
    """Context manager that instruments functions via ``sys.settrace``.

    Usage::

        recorder = TraceRecorder(file_filter="mymodule")
        with recorder:
            result = my_function(42)
        log = recorder.build_log("my_function")

    The recorder is thread-aware: each thread gets its own settrace hook
    and events are tagged with ``threading.get_ident()``.

    Parameters
    ----------
    file_filter : str or None
        If given, only trace frames whose filename contains this substring.
    max_events : int
        Stop recording after this many events to bound memory usage.
    capture_locals : bool
        Whether to capture local variable snapshots on each line event.
    """

    def __init__(
        self,
        *,
        file_filter: Optional[str] = None,
        max_events: int = 50_000,
        capture_locals: bool = True,
    ) -> None:
        self._file_filter = file_filter
        self._max_events = max_events
        self._capture_locals = capture_locals
        self._state: Optional[_SettraceState] = None
        self._prev_trace: Any = None
        self._start_time: float = 0.0
        self._end_time: float = 0.0
        self._active = False

    # Context manager protocol -------------------------------------------

    def __enter__(self) -> TraceRecorder:
        self.start()
        return self

    def __exit__(
        self,
        exc_type: Optional[type],
        exc_val: Optional[BaseException],
        exc_tb: Any,
    ) -> None:
        self.stop()

    def start(self) -> None:
        """Begin recording."""
        if self._active:
            return
        self._state = _SettraceState(
            root_function="<root>",
            file_filter=self._file_filter,
            max_events=self._max_events,
        )
        self._start_time = time.monotonic()
        self._prev_trace = sys.gettrace()
        sys.settrace(functools.partial(_settrace_callback, self._state))
        self._active = True

    def stop(self) -> None:
        """Stop recording and restore the previous trace hook."""
        if not self._active:
            return
        sys.settrace(self._prev_trace)
        self._end_time = time.monotonic()
        self._active = False
        if self._state is not None:
            self._state.active = False

    @property
    def events(self) -> List[TraceEvent]:
        """Access the raw list of captured events."""
        if self._state is None:
            return []
        return list(self._state.events)

    @property
    def event_count(self) -> int:
        if self._state is None:
            return 0
        return len(self._state.events)

    def build_log(
        self,
        target_function: str,
        *,
        args_snapshot: Optional[Sequence[Tuple[str, str]]] = None,
        return_value_repr: Optional[str] = None,
        raised_exception: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> TraceLog:
        """Assemble a :class:`TraceLog` from the captured events."""
        events = tuple(self._state.events) if self._state else ()
        return TraceLog(
            trace_id=uuid.uuid4().hex[:16],
            events=events,
            target_function=target_function,
            start_time=self._start_time,
            end_time=self._end_time or time.monotonic(),
            args_snapshot=tuple(args_snapshot or ()),
            return_value_repr=return_value_repr,
            raised_exception=raised_exception,
            metadata=tuple(sorted((metadata or {}).items())),
        )


# ---------------------------------------------------------------------------
# Decorator-based instrumentation
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class InstrumentationConfig:
    """Configuration for decorator-based instrumentation.

    Attributes
    ----------
    capture_args : bool
        Whether to record function arguments.
    capture_return : bool
        Whether to record the return value.
    capture_locals : bool
        Whether to capture local variable snapshots at each assignment.
    capture_exceptions : bool
        Whether to record raised exceptions.
    max_events : int
        Hard cap on events per invocation.
    file_filter : Optional[str]
        Only record events whose filename contains this substring.
    """

    capture_args: bool = True
    capture_return: bool = True
    capture_locals: bool = True
    capture_exceptions: bool = True
    max_events: int = 50_000
    file_filter: Optional[str] = None


_DEFAULT_CONFIG = InstrumentationConfig()


def instrument(
    func: _F,
    *,
    config: InstrumentationConfig = _DEFAULT_CONFIG,
) -> _F:
    """Decorator that wraps *func* to record a :class:`TraceLog` on each call.

    The log is attached to the return wrapper as ``.last_trace_log``.
    """
    sig = inspect.signature(func)
    func_qualname = getattr(func, "__qualname__", func.__name__)
    source_file = inspect.getfile(func) if hasattr(func, "__code__") else "<unknown>"

    @functools.wraps(func)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
        events: List[TraceEvent] = []
        bound = sig.bind(*args, **kwargs)
        bound.apply_defaults()
        start_time = time.monotonic()

        # Record arguments
        args_snap: List[Tuple[str, str]] = []
        if config.capture_args:
            for pname, pval in bound.arguments.items():
                args_snap.append((pname, _safe_repr(pval)))
                events.append(
                    _make_event(
                        EventKind.CALL,
                        func_qualname,
                        pname,
                        pval,
                        location=(source_file, 0, 0),
                        call_depth=0,
                    )
                )

        raised: Optional[str] = None
        return_repr: Optional[str] = None
        result: Any = None

        try:
            if config.capture_locals:
                recorder = TraceRecorder(
                    file_filter=config.file_filter or source_file,
                    max_events=config.max_events,
                    capture_locals=True,
                )
                with recorder:
                    result = func(*args, **kwargs)
                events.extend(recorder.events)
            else:
                result = func(*args, **kwargs)
        except Exception as exc:
            if config.capture_exceptions:
                raised = _safe_type_name(exc)
                events.append(
                    _make_event(
                        EventKind.EXCEPTION,
                        func_qualname,
                        _safe_type_name(exc),
                        exc,
                        location=(source_file, 0, 0),
                        call_depth=0,
                        extra={"exception_type": _safe_type_name(exc)},
                    )
                )
            raise
        else:
            if config.capture_return:
                return_repr = _safe_repr(result)
                events.append(
                    _make_event(
                        EventKind.RETURN,
                        func_qualname,
                        "",
                        result,
                        location=(source_file, 0, 0),
                        call_depth=0,
                    )
                )
        finally:
            end_time = time.monotonic()
            log = TraceLog(
                trace_id=uuid.uuid4().hex[:16],
                events=tuple(events),
                target_function=func_qualname,
                start_time=start_time,
                end_time=end_time,
                args_snapshot=tuple(args_snap),
                return_value_repr=return_repr,
                raised_exception=raised,
            )
            wrapper.last_trace_log = log  # type: ignore[attr-defined]

        return result

    wrapper.last_trace_log = None  # type: ignore[attr-defined]
    return wrapper  # type: ignore[return-value]


# ---------------------------------------------------------------------------
# record_trace -- one-shot convenience API
# ---------------------------------------------------------------------------

def record_trace(
    func: Callable[..., Any],
    *args: Any,
    _trace_config: Optional[InstrumentationConfig] = None,
    **kwargs: Any,
) -> TraceLog:
    """Execute *func(*args, **kwargs)* and return its :class:`TraceLog`.

    This is the primary public entry-point for single-invocation tracing.
    It records call/return events, local assignments, and exceptions.

    Parameters
    ----------
    func : Callable
        The function to trace.
    *args, **kwargs
        Arguments forwarded to *func*.
    _trace_config : InstrumentationConfig or None
        Optional custom configuration.

    Returns
    -------
    TraceLog
        The complete trace log.

    Example
    -------
    >>> def add(a, b):
    ...     return a + b
    >>> log = record_trace(add, 1, 2)
    >>> log.succeeded
    True
    """
    config = _trace_config or _DEFAULT_CONFIG
    func_qualname = getattr(func, "__qualname__", getattr(func, "__name__", "<lambda>"))
    source_file = "<unknown>"
    try:
        source_file = inspect.getfile(func)
    except (TypeError, OSError):
        pass

    sig: Optional[inspect.Signature] = None
    try:
        sig = inspect.signature(func)
    except (ValueError, TypeError):
        pass

    events: List[TraceEvent] = []
    args_snap: List[Tuple[str, str]] = []

    # Record arguments
    if sig is not None and config.capture_args:
        try:
            bound = sig.bind(*args, **kwargs)
            bound.apply_defaults()
            for pname, pval in bound.arguments.items():
                args_snap.append((pname, _safe_repr(pval)))
                events.append(
                    _make_event(
                        EventKind.CALL,
                        func_qualname,
                        pname,
                        pval,
                        location=(source_file, 0, 0),
                        call_depth=0,
                    )
                )
        except TypeError:
            pass

    start_time = time.monotonic()
    raised: Optional[str] = None
    return_repr: Optional[str] = None

    recorder = TraceRecorder(
        file_filter=config.file_filter or source_file,
        max_events=config.max_events,
        capture_locals=config.capture_locals,
    )

    try:
        with recorder:
            result = func(*args, **kwargs)
    except Exception as exc:
        raised = _safe_type_name(exc)
        if config.capture_exceptions:
            events.append(
                _make_event(
                    EventKind.EXCEPTION,
                    func_qualname,
                    _safe_type_name(exc),
                    exc,
                    location=(source_file, 0, 0),
                    call_depth=0,
                    extra={"exception_type": _safe_type_name(exc)},
                )
            )
    else:
        if config.capture_return:
            return_repr = _safe_repr(result)
            events.append(
                _make_event(
                    EventKind.RETURN,
                    func_qualname,
                    "",
                    result,
                    location=(source_file, 0, 0),
                    call_depth=0,
                )
            )

    end_time = time.monotonic()

    # Merge recorder events with our envelope events
    all_events = events + recorder.events
    all_events.sort(key=lambda e: e.timestamp)

    return TraceLog(
        trace_id=uuid.uuid4().hex[:16],
        events=tuple(all_events),
        target_function=func_qualname,
        start_time=start_time,
        end_time=end_time,
        args_snapshot=tuple(args_snap),
        return_value_repr=return_repr,
        raised_exception=raised,
    )


# ---------------------------------------------------------------------------
# Batch tracing utilities
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TraceInput:
    """A single input case for batch tracing.

    Attributes
    ----------
    args : Tuple[Any, ...]
        Positional arguments.
    kwargs : Dict[str, Any]
        Keyword arguments.
    label : str
        Human-readable label for this input.
    """

    args: Tuple[Any, ...] = ()
    kwargs: Tuple[Tuple[str, Any], ...] = ()
    label: str = ""

    @property
    def kwargs_dict(self) -> Dict[str, Any]:
        return dict(self.kwargs)


def record_traces_batch(
    func: Callable[..., Any],
    inputs: Sequence[TraceInput],
    *,
    config: Optional[InstrumentationConfig] = None,
) -> List[TraceLog]:
    """Run *func* once per input and return all :class:`TraceLog` objects.

    Parameters
    ----------
    func : Callable
        The function to trace.
    inputs : Sequence[TraceInput]
        A list of input configurations.
    config : InstrumentationConfig or None
        Optional shared configuration.

    Returns
    -------
    List[TraceLog]
        One log per input.
    """
    logs: List[TraceLog] = []
    for inp in inputs:
        log = record_trace(
            func,
            *inp.args,
            _trace_config=config,
            **inp.kwargs_dict,
        )
        logs.append(log)
    return logs


# ---------------------------------------------------------------------------
# Trace summary helpers
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TraceSummary:
    """Lightweight summary statistics for a :class:`TraceLog`.

    Attributes
    ----------
    trace_id : str
        Same as the parent log's ``trace_id``.
    target_function : str
        Function that was traced.
    event_count : int
        Total number of events.
    unique_variable_count : int
        Number of distinct variables observed.
    unique_type_count : int
        Number of distinct types observed.
    unique_shape_count : int
        Number of distinct tensor shapes observed.
    max_depth : int
        Maximum call depth reached.
    duration : float
        Wall-clock duration in seconds.
    succeeded : bool
        Whether the traced call returned normally.
    branch_count : int
        Number of branch decision events.
    exception_count : int
        Number of exception events.
    """

    trace_id: str
    target_function: str
    event_count: int
    unique_variable_count: int
    unique_type_count: int
    unique_shape_count: int
    max_depth: int
    duration: float
    succeeded: bool
    branch_count: int
    exception_count: int


def summarize_trace(log: TraceLog) -> TraceSummary:
    """Compute a :class:`TraceSummary` from a :class:`TraceLog`."""
    return TraceSummary(
        trace_id=log.trace_id,
        target_function=log.target_function,
        event_count=log.event_count,
        unique_variable_count=len(log.unique_variables()),
        unique_type_count=len(log.unique_types()),
        unique_shape_count=len(log.unique_shapes()),
        max_depth=log.max_call_depth(),
        duration=log.duration,
        succeeded=log.succeeded,
        branch_count=len(log.branch_events()),
        exception_count=len(log.exception_events()),
    )


# ---------------------------------------------------------------------------
# Filtering helpers
# ---------------------------------------------------------------------------

def filter_events(
    events: Iterable[TraceEvent],
    *,
    kinds: Optional[FrozenSet[EventKind]] = None,
    functions: Optional[FrozenSet[str]] = None,
    variables: Optional[FrozenSet[str]] = None,
    min_depth: int = 0,
    max_depth: int = 999_999,
) -> List[TraceEvent]:
    """Filter a sequence of events by multiple criteria."""
    result: List[TraceEvent] = []
    for ev in events:
        if kinds and ev.kind not in kinds:
            continue
        if functions and not any(ev.matches_function(f) for f in functions):
            continue
        if variables and ev.variable not in variables:
            continue
        if ev.call_depth < min_depth or ev.call_depth > max_depth:
            continue
        result.append(ev)
    return result


def merge_trace_logs(logs: Sequence[TraceLog]) -> TraceLog:
    """Merge multiple logs into a single combined :class:`TraceLog`."""
    if not logs:
        return TraceLog(
            trace_id=uuid.uuid4().hex[:16],
            events=(),
            target_function="<merged>",
            start_time=0.0,
            end_time=0.0,
        )
    all_events: List[TraceEvent] = []
    for log in logs:
        all_events.extend(log.events)
    all_events.sort(key=lambda e: e.timestamp)
    return TraceLog(
        trace_id=uuid.uuid4().hex[:16],
        events=tuple(all_events),
        target_function=logs[0].target_function,
        start_time=min(l.start_time for l in logs),
        end_time=max(l.end_time for l in logs),
        args_snapshot=logs[0].args_snapshot,
        return_value_repr=logs[-1].return_value_repr,
        raised_exception=next(
            (l.raised_exception for l in logs if l.raised_exception), None
        ),
    )
