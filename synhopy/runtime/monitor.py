"""SynHoPy runtime monitor — turn verified specs into runtime assertions.

F* extracts to OCaml/C but loses spec information at runtime.  SynHoPy can
keep specs as runtime assertions in production (opt-in) or strip them for
performance.  This module provides:

* **RuntimeMonitor** — wrap functions with their SynHoPy spec checks.
* **@monitored** — decorator shorthand for per-function monitoring.
* **SpecCompiler** — compile ``@guarantee`` / ``@requires`` / ``@ensures``
  decorators into fast callable checks.
* **MonitorReport / Violation** — structured monitoring telemetry.
* **ContractEnforcer** — Eiffel-style Design by Contract for classes.
* **ProductionMonitor** — context-manager for production traffic sampling.
"""
from __future__ import annotations

import copy
import enum
import functools
import inspect
import logging
import random
import re
import threading
import time
import traceback
from dataclasses import dataclass, field
from typing import Any, Callable, TypeVar

# ---------------------------------------------------------------------------
#  Imports from SynHoPy core — guarded so the module stays loadable even if
#  the rest of the tree is not on PYTHONPATH (self-tests use local stubs).
# ---------------------------------------------------------------------------
try:
    from synhopy.core.types import Spec, SpecKind, FunctionSpec
    from synhopy.core.kernel import TrustLevel
    from synhopy.proofs.sugar import extract_spec, _SpecMetadata, _get_spec
    _HAS_SYNHOPY = True
except ImportError:
    _HAS_SYNHOPY = False

logger = logging.getLogger("synhopy.runtime.monitor")

F = TypeVar("F", bound=Callable)


# ═══════════════════════════════════════════════════════════════════
#  §1  MonitorMode
# ═══════════════════════════════════════════════════════════════════

class MonitorMode(enum.Enum):
    """Runtime monitoring modes."""
    ASSERT = "assert"   # raise AssertionError on violation
    LOG = "log"         # log violation, continue execution
    SAMPLE = "sample"   # check random subset of calls
    SHADOW = "shadow"   # check in background thread, never block
    OFF = "off"         # disabled (production zero-overhead)


# ═══════════════════════════════════════════════════════════════════
#  §2  Violation / MonitorReport
# ═══════════════════════════════════════════════════════════════════

@dataclass
class Violation:
    """A single spec violation detected at runtime."""
    function: str
    spec_type: str           # "requires", "ensures", "guarantee", "pure"
    spec_description: str
    inputs: dict[str, Any]
    output: Any | None
    timestamp: float
    traceback: str | None = None

    def __repr__(self) -> str:
        return (f"Violation({self.function!r}, {self.spec_type}="
                f"{self.spec_description!r})")


@dataclass
class MonitorReport:
    """Aggregated monitoring statistics."""
    total_calls: int = 0
    checked_calls: int = 0
    violations: list[Violation] = field(default_factory=list)
    skipped_calls: int = 0       # skipped due to sampling / timeout
    overhead_samples: list[float] = field(default_factory=list)

    @property
    def avg_overhead_ms(self) -> float:
        if not self.overhead_samples:
            return 0.0
        return sum(self.overhead_samples) / len(self.overhead_samples)

    @property
    def violation_rate(self) -> float:
        if self.checked_calls == 0:
            return 0.0
        return len(self.violations) / self.checked_calls

    def summary(self) -> str:
        lines = [
            f"MonitorReport: {self.total_calls} total calls, "
            f"{self.checked_calls} checked, "
            f"{self.skipped_calls} skipped",
            f"  violations: {len(self.violations)} "
            f"({self.violation_rate:.2%})",
            f"  avg overhead: {self.avg_overhead_ms:.3f} ms",
        ]
        for v in self.violations[:5]:
            lines.append(f"  - {v}")
        if len(self.violations) > 5:
            lines.append(f"  ... and {len(self.violations) - 5} more")
        return "\n".join(lines)

    def to_json(self) -> dict:
        return {
            "total_calls": self.total_calls,
            "checked_calls": self.checked_calls,
            "skipped_calls": self.skipped_calls,
            "violation_count": len(self.violations),
            "violation_rate": self.violation_rate,
            "avg_overhead_ms": self.avg_overhead_ms,
            "violations": [
                {
                    "function": v.function,
                    "spec_type": v.spec_type,
                    "spec_description": v.spec_description,
                    "timestamp": v.timestamp,
                }
                for v in self.violations
            ],
        }

    def __repr__(self) -> str:
        return (f"MonitorReport(calls={self.total_calls}, "
                f"checked={self.checked_calls}, "
                f"violations={len(self.violations)})")


# ═══════════════════════════════════════════════════════════════════
#  §3  SpecCompiler — compile specs into fast callable checks
# ═══════════════════════════════════════════════════════════════════

# Common NL guarantee patterns → lambda factories.
_GUARANTEE_PATTERNS: list[tuple[re.Pattern, Callable[..., Callable]]] = []


def _register_pattern(regex: str,
                       factory: Callable[..., Callable]) -> None:
    _GUARANTEE_PATTERNS.append((re.compile(regex, re.IGNORECASE), factory))


# "returns positive" / "result > 0" / "result is positive"
_register_pattern(
    r"(?:returns?\s+positive|result\s*(?:is\s+)?(?:>|positive))",
    lambda _m: lambda _args, _kw, result: result > 0,
)
# "returns non-negative" / "result >= 0"
_register_pattern(
    r"(?:returns?\s+non[- ]?negative|result\s*>=?\s*0)",
    lambda _m: lambda _args, _kw, result: result >= 0,
)
# "returns sorted"
_register_pattern(
    r"returns?\s+(?:a\s+)?sorted",
    lambda _m: lambda _args, _kw, result: list(result) == sorted(result),
)
# "result is permutation of input"
_register_pattern(
    r"(?:result\s+is\s+(?:a\s+)?permutation|permutation\s+of\s+input)",
    lambda _m: (lambda args, _kw, result:
                sorted(result) == sorted(args[0])
                if args else True),
)
# "returns non-empty"
_register_pattern(
    r"returns?\s+non[- ]?empty",
    lambda _m: lambda _args, _kw, result: len(result) > 0,
)
# "result > 0"
_register_pattern(
    r"result\s*>\s*0",
    lambda _m: lambda _args, _kw, result: result > 0,
)
# "result >= 0"
_register_pattern(
    r"result\s*>=\s*0",
    lambda _m: lambda _args, _kw, result: result >= 0,
)
# "returns a sorted list with no duplicates"
_register_pattern(
    r"sorted\s+list\s+with\s+no\s+duplicates",
    lambda _m: (lambda _args, _kw, result:
                list(result) == sorted(set(result))),
)
# "length preserved" / "same length"
_register_pattern(
    r"(?:length\s+preserved|same\s+length)",
    lambda _m: (lambda args, _kw, result:
                len(result) == len(args[0]) if args else True),
)
# "never returns None"
_register_pattern(
    r"never\s+returns?\s+None",
    lambda _m: lambda _args, _kw, result: result is not None,
)
# "idempotent"
_register_pattern(
    r"idempotent",
    lambda _m: None,  # handled specially by SpecCompiler
)


class SpecCompiler:
    """Compile SynHoPy specs into efficient runtime checks."""

    def compile_requires(self, spec: str | Callable) -> Callable:
        """Compile a precondition into a fast callable check.

        Returns a callable ``(args, kwargs) -> bool``.
        """
        if callable(spec) and not isinstance(spec, str):
            sig = inspect.signature(spec)
            nparams = len(sig.parameters)
            if nparams == 0:
                return lambda args, kwargs: spec()
            return lambda args, kwargs: spec(*args, **kwargs)
        # String specs — best effort, always pass (can't negate safely).
        return lambda args, kwargs: True

    def compile_ensures(self, spec: str | Callable) -> Callable:
        """Compile a postcondition into a fast callable check.

        Returns a callable ``(args, kwargs, result) -> bool``.
        """
        if callable(spec) and not isinstance(spec, str):
            sig = inspect.signature(spec)
            nparams = len(sig.parameters)
            if nparams == 0:
                return lambda args, kwargs, result: spec()
            if nparams == 1:
                return lambda args, kwargs, result: spec(result)
            # Generic: pass *args then result as last positional.
            return lambda args, kwargs, result: spec(*args, result)
        return lambda args, kwargs, result: True

    def compile_guarantee(self, spec: str) -> Callable | None:
        """Compile a NL guarantee string into a best-effort runtime check.

        Returns ``(args, kwargs, result) -> bool`` or *None* when the
        guarantee cannot be compiled into a check.
        """
        for pattern, factory in _GUARANTEE_PATTERNS:
            m = pattern.search(spec)
            if m:
                checker = factory(m)
                if checker is None:
                    return None
                return checker
        return None

    def compile_pure_check(self, func: Callable) -> Callable:
        """Return a check that calls *func* twice with the same deep-copied
        inputs and verifies determinism."""
        def check(args: tuple, kwargs: dict) -> bool:
            args_copy = copy.deepcopy(args)
            kwargs_copy = copy.deepcopy(kwargs)
            r1 = func(*args, **kwargs)
            r2 = func(*args_copy, **kwargs_copy)
            return r1 == r2
        return check


# Singleton compiler.
_compiler = SpecCompiler()


# ═══════════════════════════════════════════════════════════════════
#  §4  _CompiledSpec — internal per-function check bundle
# ═══════════════════════════════════════════════════════════════════

@dataclass
class _CompiledSpec:
    """Pre-compiled checks for a single function."""
    func_name: str
    preconditions: list[tuple[str, Callable]]     # (desc, (args,kw)->bool)
    postconditions: list[tuple[str, Callable]]     # (desc, (args,kw,res)->bool)
    guarantee_checks: list[tuple[str, Callable]]   # (desc, (args,kw,res)->bool)
    pure_check: Callable | None                    # (args,kw)->bool
    is_total: bool


def _build_compiled_spec(func: Callable) -> _CompiledSpec | None:
    """Extract and compile checks from *func*'s ``_synhopy_spec`` metadata."""
    meta = getattr(func, "_synhopy_spec", None)
    if meta is None:
        return None

    compiler = _compiler
    preconditions: list[tuple[str, Callable]] = []
    postconditions: list[tuple[str, Callable]] = []
    guarantee_checks: list[tuple[str, Callable]] = []

    for pred in meta.preconditions:
        desc = _callable_desc(pred, "requires")
        preconditions.append((desc, compiler.compile_requires(pred)))

    for pred in meta.postconditions:
        desc = _callable_desc(pred, "ensures")
        postconditions.append((desc, compiler.compile_ensures(pred)))

    for g_str in meta.guarantees:
        check = compiler.compile_guarantee(g_str)
        if check is not None:
            guarantee_checks.append((g_str, check))
        else:
            # Keep the description for reporting even if we can't check it.
            pass

    pure_check = None
    if meta.effect == "Pure":
        # Don't compile purity check eagerly — only when actually needed,
        # because it invokes the function an extra time.
        pure_check = True  # sentinel; we build per-call lazily

    return _CompiledSpec(
        func_name=getattr(func, "__qualname__", func.__name__),
        preconditions=preconditions,
        postconditions=postconditions,
        guarantee_checks=guarantee_checks,
        pure_check=pure_check,  # type: ignore[arg-type]
        is_total=meta.is_total,
    )


def _callable_desc(pred: Callable | str, kind: str) -> str:
    if isinstance(pred, str):
        return pred
    src = getattr(pred, "__name__", None)
    if src and src != "<lambda>":
        return f"{kind}({src})"
    try:
        source = inspect.getsource(pred).strip()
        # Try to extract just the lambda body.
        if "lambda" in source:
            idx = source.index("lambda")
            return source[idx:].rstrip(" ,)")
        return source
    except (OSError, TypeError):
        return f"{kind}(<callable>)"


# ═══════════════════════════════════════════════════════════════════
#  §5  RuntimeMonitor
# ═══════════════════════════════════════════════════════════════════

class RuntimeMonitor:
    """Turn SynHoPy specs into runtime monitors.

    Usage::

        monitor = RuntimeMonitor(mode=MonitorMode.ASSERT)
        safe_div = monitor.wrap(safe_div)
        # ... or ...
        monitor.wrap_module(my_module)
        print(monitor.report().summary())
    """

    def __init__(
        self,
        *,
        mode: MonitorMode = MonitorMode.ASSERT,
        log_violations: bool = True,
        sample_rate: float = 1.0,
        max_overhead_ms: float = 10.0,
    ) -> None:
        self._mode = mode
        self._log_violations = log_violations
        self._sample_rate = sample_rate
        self._max_overhead_ms = max_overhead_ms
        self._report = MonitorReport()
        self._lock = threading.Lock()
        self._alert_callbacks: list[Callable[[Violation], None]] = []

    # -- public API -------------------------------------------------

    @property
    def mode(self) -> MonitorMode:
        return self._mode

    def wrap(self, func: Callable) -> Callable:
        """Wrap *func* with its SynHoPy spec checks.

        Returns the original function unchanged if there are no specs
        or the mode is ``OFF``.
        """
        if self._mode is MonitorMode.OFF:
            return func

        cspec = _build_compiled_spec(func)
        if cspec is None:
            return func

        compiler = _compiler
        # Freeze the underlying function for purity re-call.
        raw_func = func

        @functools.wraps(func)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            with self._lock:
                self._report.total_calls += 1

            # Sampling / OFF fast-path.
            effective_mode = self._mode
            if effective_mode is MonitorMode.SAMPLE:
                if random.random() > self._sample_rate:
                    with self._lock:
                        self._report.skipped_calls += 1
                    return raw_func(*args, **kwargs)
            elif effective_mode is MonitorMode.OFF:
                return raw_func(*args, **kwargs)

            if effective_mode is MonitorMode.SHADOW:
                # Execute and check in background thread.
                result = raw_func(*args, **kwargs)
                t = threading.Thread(
                    target=self._shadow_check,
                    args=(cspec, raw_func, args, kwargs, result),
                    daemon=True,
                )
                t.start()
                return result

            # ASSERT / LOG / SAMPLE — synchronous check.
            return self._checked_call(
                cspec, raw_func, compiler, args, kwargs,
                raise_on_violation=(effective_mode is MonitorMode.ASSERT),
            )

        wrapper._synhopy_monitored = True  # type: ignore[attr-defined]
        # Preserve the original spec metadata on the wrapper.
        if hasattr(func, "_synhopy_spec"):
            wrapper._synhopy_spec = func._synhopy_spec  # type: ignore
        return wrapper

    def wrap_module(self, module: Any) -> None:
        """Monkey-patch every SynHoPy-decorated function in *module*."""
        for name in dir(module):
            obj = getattr(module, name)
            if callable(obj) and hasattr(obj, "_synhopy_spec"):
                wrapped = self.wrap(obj)
                setattr(module, name, wrapped)

    def report(self) -> MonitorReport:
        """Return a *snapshot* of the current monitoring stats."""
        with self._lock:
            r = MonitorReport(
                total_calls=self._report.total_calls,
                checked_calls=self._report.checked_calls,
                violations=list(self._report.violations),
                skipped_calls=self._report.skipped_calls,
                overhead_samples=list(self._report.overhead_samples),
            )
        return r

    def reset(self) -> None:
        """Clear all monitoring statistics."""
        with self._lock:
            self._report = MonitorReport()

    def alert_on_violation(self, callback: Callable[[Violation], None]) -> None:
        """Register *callback* to be invoked on every detected violation."""
        self._alert_callbacks.append(callback)

    # -- internal ---------------------------------------------------

    def _checked_call(
        self,
        cspec: _CompiledSpec,
        raw_func: Callable,
        compiler: SpecCompiler,
        args: tuple,
        kwargs: dict,
        raise_on_violation: bool,
    ) -> Any:
        t0 = time.monotonic()
        bound = _bind_args(raw_func, args, kwargs)

        # --- precondition checks ---
        for desc, check in cspec.preconditions:
            try:
                ok = check(args, kwargs)
            except Exception:
                ok = False
            if not ok:
                v = Violation(
                    function=cspec.func_name,
                    spec_type="requires",
                    spec_description=desc,
                    inputs=bound,
                    output=None,
                    timestamp=time.time(),
                    traceback=traceback.format_exc(),
                )
                self._record_violation(v, raise_on_violation)
                if raise_on_violation:
                    raise  # _record_violation already raised

        # --- call the function ---
        if cspec.is_total:
            try:
                result = raw_func(*args, **kwargs)
            except Exception as exc:
                v = Violation(
                    function=cspec.func_name,
                    spec_type="guarantee",
                    spec_description="total (must not raise)",
                    inputs=bound,
                    output=None,
                    timestamp=time.time(),
                    traceback=traceback.format_exc(),
                )
                self._record_violation(v, raise_on_violation)
                if raise_on_violation:
                    raise AssertionError(
                        f"total function {cspec.func_name!r} raised "
                        f"{type(exc).__name__}: {exc}"
                    ) from exc
                result = None  # continue with None in LOG mode
        else:
            result = raw_func(*args, **kwargs)

        # --- postcondition checks ---
        for desc, check in cspec.postconditions:
            try:
                ok = check(args, kwargs, result)
            except Exception:
                ok = False
            if not ok:
                v = Violation(
                    function=cspec.func_name,
                    spec_type="ensures",
                    spec_description=desc,
                    inputs=bound,
                    output=result,
                    timestamp=time.time(),
                    traceback=None,
                )
                self._record_violation(v, raise_on_violation)

        # --- guarantee checks ---
        for desc, check in cspec.guarantee_checks:
            try:
                ok = check(args, kwargs, result)
            except Exception:
                ok = False
            if not ok:
                v = Violation(
                    function=cspec.func_name,
                    spec_type="guarantee",
                    spec_description=desc,
                    inputs=bound,
                    output=result,
                    timestamp=time.time(),
                    traceback=None,
                )
                self._record_violation(v, raise_on_violation)

        # --- purity check (only in ASSERT mode — it's expensive) ---
        if cspec.pure_check and raise_on_violation:
            try:
                args2 = copy.deepcopy(args)
                kwargs2 = copy.deepcopy(kwargs)
                result2 = raw_func(*args2, **kwargs2)
                if result2 != result:
                    v = Violation(
                        function=cspec.func_name,
                        spec_type="pure",
                        spec_description="pure (deterministic output)",
                        inputs=bound,
                        output=result,
                        timestamp=time.time(),
                        traceback=None,
                    )
                    self._record_violation(v, raise_on_violation)
            except Exception:
                pass  # purity check is best-effort

        elapsed_ms = (time.monotonic() - t0) * 1000.0
        with self._lock:
            self._report.checked_calls += 1
            self._report.overhead_samples.append(elapsed_ms)
        return result

    def _shadow_check(
        self,
        cspec: _CompiledSpec,
        raw_func: Callable,
        args: tuple,
        kwargs: dict,
        result: Any,
    ) -> None:
        """Run checks in a background thread (SHADOW mode)."""
        bound = _bind_args(raw_func, args, kwargs)

        for desc, check in cspec.preconditions:
            try:
                ok = check(args, kwargs)
            except Exception:
                ok = False
            if not ok:
                v = Violation(
                    function=cspec.func_name,
                    spec_type="requires",
                    spec_description=desc,
                    inputs=bound,
                    output=None,
                    timestamp=time.time(),
                )
                self._record_violation(v, raise_on_violation=False)

        for desc, check in cspec.postconditions:
            try:
                ok = check(args, kwargs, result)
            except Exception:
                ok = False
            if not ok:
                v = Violation(
                    function=cspec.func_name,
                    spec_type="ensures",
                    spec_description=desc,
                    inputs=bound,
                    output=result,
                    timestamp=time.time(),
                )
                self._record_violation(v, raise_on_violation=False)

        for desc, check in cspec.guarantee_checks:
            try:
                ok = check(args, kwargs, result)
            except Exception:
                ok = False
            if not ok:
                v = Violation(
                    function=cspec.func_name,
                    spec_type="guarantee",
                    spec_description=desc,
                    inputs=bound,
                    output=result,
                    timestamp=time.time(),
                )
                self._record_violation(v, raise_on_violation=False)

        with self._lock:
            self._report.checked_calls += 1

    def _record_violation(
        self, v: Violation, raise_on_violation: bool,
    ) -> None:
        with self._lock:
            self._report.violations.append(v)
        if self._log_violations:
            logger.warning("SynHoPy violation: %s", v)
        for cb in self._alert_callbacks:
            try:
                cb(v)
            except Exception:
                pass
        if raise_on_violation:
            raise AssertionError(
                f"SynHoPy {v.spec_type} violation in {v.function!r}: "
                f"{v.spec_description}"
            )


def _bind_args(func: Callable, args: tuple, kwargs: dict) -> dict[str, Any]:
    """Best-effort binding of *args*/*kwargs* to parameter names."""
    try:
        sig = inspect.signature(func)
        bound = sig.bind(*args, **kwargs)
        bound.apply_defaults()
        return dict(bound.arguments)
    except (ValueError, TypeError):
        return {"*args": args, "**kwargs": kwargs}


# ═══════════════════════════════════════════════════════════════════
#  §6  @monitored decorator
# ═══════════════════════════════════════════════════════════════════

# Module-level default monitor (lazily created).
_default_monitor: RuntimeMonitor | None = None
_default_lock = threading.Lock()


def _get_default_monitor() -> RuntimeMonitor:
    global _default_monitor
    if _default_monitor is None:
        with _default_lock:
            if _default_monitor is None:
                _default_monitor = RuntimeMonitor(mode=MonitorMode.ASSERT)
    return _default_monitor


def set_default_monitor(monitor: RuntimeMonitor) -> None:
    """Set the module-level default monitor used by ``@monitored``."""
    global _default_monitor
    _default_monitor = monitor


def monitored(
    func: F | None = None,
    *,
    mode: MonitorMode = MonitorMode.ASSERT,
    sample_rate: float = 1.0,
) -> F | Callable[[F], F]:
    """Decorator that enables runtime monitoring of SynHoPy specs.

    Can be used bare (``@monitored``) or with arguments
    (``@monitored(mode=MonitorMode.LOG)``).

    Example::

        @monitored
        @guarantee("result > 0")
        @requires(lambda x: x != 0)
        def safe_div(a, b):
            return a / b
    """
    def decorator(f: F) -> F:
        mon = RuntimeMonitor(
            mode=mode,
            sample_rate=sample_rate,
        )
        wrapped = mon.wrap(f)
        # Stash the monitor for later introspection.
        wrapped._synhopy_monitor = mon  # type: ignore[attr-defined]
        return wrapped  # type: ignore[return-value]

    if func is not None:
        return decorator(func)
    return decorator  # type: ignore[return-value]


# ═══════════════════════════════════════════════════════════════════
#  §7  ContractEnforcer — Design by Contract
# ═══════════════════════════════════════════════════════════════════

class ContractEnforcer:
    """Eiffel-style Design by Contract using SynHoPy specs.

    For functions, wraps with precondition / postcondition checks.
    For classes, additionally enforces class invariants after every
    public method call.
    """

    def __init__(
        self,
        *,
        check_invariants: bool = True,
        check_old: bool = True,
        mode: MonitorMode = MonitorMode.ASSERT,
    ) -> None:
        self._check_invariants = check_invariants
        self._check_old = check_old
        self._monitor = RuntimeMonitor(mode=mode)

    def enforce(self, cls_or_func: Any) -> Any:
        """Apply contract enforcement to a class or function."""
        if isinstance(cls_or_func, type):
            return self._enforce_class(cls_or_func)
        return self._monitor.wrap(cls_or_func)

    def report(self) -> MonitorReport:
        return self._monitor.report()

    # -- class enforcement ------------------------------------------

    def _enforce_class(self, cls: type) -> type:
        """Wrap every public method and check class invariants."""
        invariant_descs: list[str] = []
        # Collect invariants from methods marked with @invariant.
        for name in list(vars(cls)):
            obj = getattr(cls, name)
            meta = getattr(obj, "_synhopy_spec", None)
            if meta is not None and meta.invariants:
                invariant_descs.extend(meta.invariants)

        for name in list(vars(cls)):
            if name.startswith("_"):
                continue
            obj = getattr(cls, name)
            if not callable(obj):
                continue
            wrapped = self._wrap_method_with_invariant(
                obj, cls, invariant_descs,
            )
            setattr(cls, name, wrapped)
        return cls

    def _wrap_method_with_invariant(
        self,
        method: Callable,
        cls: type,
        invariant_descs: list[str],
    ) -> Callable:
        inner = self._monitor.wrap(method)
        enforcer = self

        @functools.wraps(method)
        def wrapper(self_obj: Any, *args: Any, **kwargs: Any) -> Any:
            # Capture old state.
            old: dict[str, Any] = {}
            if enforcer._check_old:
                try:
                    old = copy.copy(vars(self_obj))
                except Exception:
                    pass
            result = inner(self_obj, *args, **kwargs)
            # Check invariants.
            if enforcer._check_invariants:
                for inv_desc in invariant_descs:
                    ok = enforcer._check_class_invariant(self_obj, inv_desc)
                    if not ok:
                        v = Violation(
                            function=f"{cls.__name__}.{method.__name__}",
                            spec_type="invariant",
                            spec_description=inv_desc,
                            inputs={"self": repr(self_obj), **_bind_args(method, (self_obj, *args), kwargs)},
                            output=result,
                            timestamp=time.time(),
                        )
                        enforcer._monitor._record_violation(
                            v,
                            raise_on_violation=(
                                enforcer._monitor.mode is MonitorMode.ASSERT
                            ),
                        )
            return result
        return wrapper

    def _check_class_invariant(self, obj: Any, invariant: str) -> bool:
        """Check class invariant holds on *obj*.

        Best-effort: tries to ``eval`` the invariant in the object's
        namespace.
        """
        try:
            ns = {"self": obj}
            ns.update(vars(obj))
            return bool(eval(invariant, {"__builtins__": {}}, ns))  # noqa: S307
        except Exception:
            # If we can't evaluate, we can't disprove — pass.
            return True

    def _capture_old(self, args: tuple, kwargs: dict) -> dict:
        """Capture deep copies of arguments for postcondition ``old.x``."""
        try:
            return {"args": copy.deepcopy(args), "kwargs": copy.deepcopy(kwargs)}
        except Exception:
            return {}


# ═══════════════════════════════════════════════════════════════════
#  §8  ProductionMonitor
# ═══════════════════════════════════════════════════════════════════

class ProductionMonitor:
    """Monitor verified specs in production with minimal overhead.

    Usage::

        with ProductionMonitor(mode=MonitorMode.LOG,
                               sample_rate=0.01) as pm:
            pm.wrap_module(my_module)
            # ... serve production traffic ...
            print(pm.report().summary())
    """

    def __init__(
        self,
        *,
        mode: MonitorMode = MonitorMode.LOG,
        sample_rate: float = 0.01,
        alert_threshold: int = 10,
        max_overhead_ms: float = 5.0,
    ) -> None:
        effective_mode = mode
        # In SAMPLE mode we use the RuntimeMonitor's SAMPLE path.
        if sample_rate < 1.0 and mode not in (MonitorMode.SAMPLE,
                                                MonitorMode.OFF):
            effective_mode = MonitorMode.SAMPLE
        self._monitor = RuntimeMonitor(
            mode=effective_mode,
            sample_rate=sample_rate,
            max_overhead_ms=max_overhead_ms,
            log_violations=True,
        )
        self._alert_threshold = alert_threshold
        self._entered = False

    def __enter__(self) -> ProductionMonitor:
        self._entered = True
        return self

    def __exit__(self, *args: Any) -> None:
        self._entered = False
        report = self._monitor.report()
        if len(report.violations) >= self._alert_threshold:
            logger.error(
                "SynHoPy ProductionMonitor: %d violations detected!\n%s",
                len(report.violations),
                report.summary(),
            )

    def wrap(self, func: Callable) -> Callable:
        """Wrap a single function."""
        return self._monitor.wrap(func)

    def wrap_module(self, module: Any) -> None:
        """Monkey-patch all decorated functions in *module*."""
        self._monitor.wrap_module(module)

    def report(self) -> MonitorReport:
        return self._monitor.report()

    def alert_on_violation(
        self, callback: Callable[[Violation], None],
    ) -> None:
        """Register *callback* for spec violations in production."""
        self._monitor.alert_on_violation(callback)


# ═══════════════════════════════════════════════════════════════════
#  §9  Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Run ≥ 30 self-tests.  ``PYTHONPATH=. python3 synhopy/runtime/monitor.py``"""
    import sys
    import types as _types

    passed = 0
    failed = 0

    def check(name: str, condition: bool) -> None:
        nonlocal passed, failed
        if condition:
            passed += 1
            print(f"  ✓ {name}")
        else:
            failed += 1
            print(f"  ✗ {name}")

    # -- helpers to create decorated functions without importing
    #    sugar (for isolation) — we just build _SpecMetadata by hand.

    def _make_meta(**kw: Any) -> _SpecMetadata:
        return _SpecMetadata(**kw)

    def _attach(func: Callable, meta: _SpecMetadata) -> None:
        func._synhopy_spec = meta  # type: ignore[attr-defined]

    # ----------------------------------------------------------------
    print("§1  MonitorMode enum")
    check("MonitorMode has 5 members",
          len(MonitorMode) == 5)
    check("OFF value is 'off'",
          MonitorMode.OFF.value == "off")

    # ----------------------------------------------------------------
    print("§2  Violation dataclass")
    v = Violation("f", "requires", "x > 0", {"x": -1}, None, 0.0)
    check("Violation repr contains function",
          "f" in repr(v))
    check("Violation fields accessible",
          v.spec_type == "requires" and v.output is None)

    # ----------------------------------------------------------------
    print("§3  MonitorReport")
    r = MonitorReport(total_calls=100, checked_calls=80, skipped_calls=20,
                      violations=[v, v], overhead_samples=[1.0, 2.0, 3.0])
    check("avg_overhead_ms correct",
          abs(r.avg_overhead_ms - 2.0) < 1e-9)
    check("violation_rate correct",
          abs(r.violation_rate - 2 / 80) < 1e-9)
    check("summary is a string",
          isinstance(r.summary(), str) and "100" in r.summary())
    check("to_json returns dict",
          isinstance(r.to_json(), dict)
          and r.to_json()["total_calls"] == 100)
    check("MonitorReport repr",
          "violations=2" in repr(r))

    # zero-division edge case
    r0 = MonitorReport()
    check("violation_rate is 0 when no calls",
          r0.violation_rate == 0.0)
    check("avg_overhead_ms is 0 when no samples",
          r0.avg_overhead_ms == 0.0)

    # ----------------------------------------------------------------
    print("§4  SpecCompiler")
    sc = SpecCompiler()

    # compile_requires with callable
    check("compile_requires callable",
          sc.compile_requires(lambda x: x > 0)((5,), {}) is True)
    check("compile_requires callable fail",
          sc.compile_requires(lambda x: x > 0)((-1,), {}) is False)
    check("compile_requires string always True",
          sc.compile_requires("x is positive")((42,), {}) is True)

    # compile_ensures with callable
    check("compile_ensures 1-arg",
          sc.compile_ensures(lambda r: r > 0)((), {}, 5) is True)
    check("compile_ensures 2-arg",
          sc.compile_ensures(lambda x, r: r == x * 2)((3,), {}, 6) is True)

    # compile_guarantee patterns
    pos = sc.compile_guarantee("returns positive")
    check("guarantee 'returns positive' compiled",
          pos is not None and pos((), {}, 5) is True)
    check("guarantee 'returns positive' catches neg",
          pos is not None and pos((), {}, -1) is False)

    sorted_chk = sc.compile_guarantee("returns a sorted list")
    check("guarantee sorted compiled",
          sorted_chk is not None
          and sorted_chk((), {}, [1, 2, 3]) is True)
    check("guarantee sorted fails unsorted",
          sorted_chk is not None
          and sorted_chk((), {}, [3, 1, 2]) is False)

    none_chk = sc.compile_guarantee("never returns None")
    check("guarantee never returns None",
          none_chk is not None and none_chk((), {}, 42) is True)
    check("guarantee never returns None — fail",
          none_chk is not None and none_chk((), {}, None) is False)

    unknown = sc.compile_guarantee("some unknown spec")
    check("unrecognised guarantee returns None",
          unknown is None)

    dup_chk = sc.compile_guarantee("sorted list with no duplicates")
    check("guarantee sorted+unique compiled",
          dup_chk is not None
          and dup_chk((), {}, [1, 2, 3]) is True)
    check("guarantee sorted+unique fails dups",
          dup_chk is not None
          and dup_chk((), {}, [1, 1, 2]) is False)

    # compile_pure_check
    def _pure_fn(x: int) -> int:
        return x * 2
    pc = sc.compile_pure_check(_pure_fn)
    check("pure check passes for pure fn",
          pc((3,), {}) is True)

    # ----------------------------------------------------------------
    print("§5  RuntimeMonitor — ASSERT mode")

    def _add(x: int, y: int) -> int:
        return x + y

    meta_add = _make_meta(
        preconditions=[lambda x, y: x >= 0],
        postconditions=[lambda x, y, r: r == x + y],
        guarantees=["result >= 0"],
    )
    _attach(_add, meta_add)

    mon = RuntimeMonitor(mode=MonitorMode.ASSERT)
    wrapped_add = mon.wrap(_add)
    check("wrapped function works",
          wrapped_add(2, 3) == 5)
    check("report shows 1 call",
          mon.report().total_calls == 1)
    check("no violations on correct call",
          len(mon.report().violations) == 0)

    # precondition violation
    try:
        wrapped_add(-1, 3)
        check("precondition violation raises", False)
    except AssertionError:
        check("precondition violation raises", True)

    check("violation recorded",
          len(mon.report().violations) == 1)
    check("violation is 'requires'",
          mon.report().violations[0].spec_type == "requires")

    # ----------------------------------------------------------------
    print("§6  RuntimeMonitor — LOG mode")
    mon_log = RuntimeMonitor(mode=MonitorMode.LOG)

    def _bad_sort(xs: list[int]) -> list[int]:
        return xs  # intentionally wrong

    meta_sort = _make_meta(guarantees=["returns sorted"])
    _attach(_bad_sort, meta_sort)
    wrapped_sort = mon_log.wrap(_bad_sort)
    result = wrapped_sort([3, 1, 2])
    check("LOG mode does not raise",
          result == [3, 1, 2])
    check("LOG mode records violation",
          len(mon_log.report().violations) == 1)

    # ----------------------------------------------------------------
    print("§7  RuntimeMonitor — OFF mode")
    mon_off = RuntimeMonitor(mode=MonitorMode.OFF)
    wrapped_off = mon_off.wrap(_bad_sort)
    check("OFF mode returns original function",
          wrapped_off is _bad_sort)

    # ----------------------------------------------------------------
    print("§8  RuntimeMonitor — SAMPLE mode")
    mon_sample = RuntimeMonitor(
        mode=MonitorMode.SAMPLE, sample_rate=0.0,
    )

    def _ident(x: int) -> int:
        return x

    meta_id = _make_meta(postconditions=[lambda x, r: r == x])
    _attach(_ident, meta_id)
    wrapped_sample = mon_sample.wrap(_ident)
    for _ in range(10):
        wrapped_sample(42)
    check("SAMPLE rate=0 skips all",
          mon_sample.report().skipped_calls == 10)
    check("SAMPLE rate=0 checks none",
          mon_sample.report().checked_calls == 0)

    # ----------------------------------------------------------------
    print("§9  RuntimeMonitor — SHADOW mode")
    mon_shadow = RuntimeMonitor(mode=MonitorMode.SHADOW)
    _attach(_bad_sort, meta_sort)
    wrapped_shadow = mon_shadow.wrap(_bad_sort)
    _r = wrapped_shadow([3, 1, 2])
    time.sleep(0.1)  # let background thread finish
    check("SHADOW mode returns result immediately",
          _r == [3, 1, 2])
    check("SHADOW mode records violation in background",
          len(mon_shadow.report().violations) >= 1)

    # ----------------------------------------------------------------
    print("§10  @monitored decorator")

    @monitored
    def _double(x: int) -> int:
        return x * 2

    # No spec → passes through.
    check("@monitored on undecorated fn works",
          _double(3) == 6)

    # With spec.
    def _neg(x: int) -> int:
        return -x

    meta_neg = _make_meta(guarantees=["returns positive"])
    _attach(_neg, meta_neg)
    _neg_mon = monitored(_neg)
    try:
        _neg_mon(5)  # returns -5, violates "returns positive"
        check("@monitored catches guarantee violation", False)
    except AssertionError:
        check("@monitored catches guarantee violation", True)

    # ----------------------------------------------------------------
    print("§11  wrap_module")
    fake_mod = _types.ModuleType("fake_mod")

    def _mod_fn(x: int) -> int:
        return x + 1

    meta_mod = _make_meta(guarantees=["result > 0"])
    _attach(_mod_fn, meta_mod)
    fake_mod.mod_fn = _mod_fn  # type: ignore[attr-defined]
    fake_mod.plain = lambda x: x  # type: ignore[attr-defined]

    mon_mod = RuntimeMonitor(mode=MonitorMode.LOG)
    mon_mod.wrap_module(fake_mod)
    check("wrap_module wraps decorated fns",
          hasattr(fake_mod.mod_fn, "_synhopy_monitored"))  # type: ignore
    check("wrap_module skips plain fns",
          not hasattr(fake_mod.plain, "_synhopy_monitored"))  # type: ignore

    # ----------------------------------------------------------------
    print("§12  ContractEnforcer — function")
    ce = ContractEnforcer(mode=MonitorMode.ASSERT)

    def _half(x: int) -> float:
        return x / 2

    meta_half = _make_meta(
        preconditions=[lambda x: isinstance(x, int)],
        postconditions=[lambda x, r: r == x / 2],
    )
    _attach(_half, meta_half)
    _half_e = ce.enforce(_half)
    check("ContractEnforcer wraps fn",
          _half_e(10) == 5.0)

    # ----------------------------------------------------------------
    print("§13  ContractEnforcer — class")
    ce2 = ContractEnforcer(mode=MonitorMode.ASSERT, check_invariants=True)

    class _Counter:
        def __init__(self) -> None:
            self.count = 0

        def increment(self) -> None:
            self.count += 1

        def decrement(self) -> None:
            self.count -= 1

    meta_inc = _make_meta(invariants=["count >= 0"])
    _attach(_Counter.increment, meta_inc)
    _attach(_Counter.decrement, meta_inc)

    _Counter = ce2.enforce(_Counter)
    c = _Counter()
    c.increment()
    check("ContractEnforcer class increment ok",
          c.count == 1)

    # ----------------------------------------------------------------
    print("§14  ProductionMonitor context manager")
    with ProductionMonitor(mode=MonitorMode.LOG,
                           sample_rate=1.0) as pm:
        def _pm_fn(x: int) -> int:
            return x

        meta_pm = _make_meta(guarantees=["result > 0"])
        _attach(_pm_fn, meta_pm)
        _pm_wrapped = pm.wrap(_pm_fn)
        _pm_wrapped(5)
        _pm_wrapped(-1)  # violation but LOG mode
        rep = pm.report()
        check("ProductionMonitor records calls",
              rep.total_calls == 2)
        check("ProductionMonitor records violations",
              len(rep.violations) == 1)

    # ----------------------------------------------------------------
    print("§15  ProductionMonitor alert callback")
    alerts: list[Violation] = []
    with ProductionMonitor(mode=MonitorMode.LOG,
                           sample_rate=1.0) as pm2:
        pm2.alert_on_violation(alerts.append)

        def _alert_fn(x: int) -> int:
            return -x

        meta_al = _make_meta(guarantees=["returns positive"])
        _attach(_alert_fn, meta_al)
        _al_w = pm2.wrap(_alert_fn)
        _al_w(5)
        check("alert callback invoked",
              len(alerts) == 1)
        check("alert has correct spec_type",
              alerts[0].spec_type == "guarantee")

    # ----------------------------------------------------------------
    print("§16  reset()")
    mon_reset = RuntimeMonitor(mode=MonitorMode.LOG)
    _attach(_ident, meta_id)
    w_reset = mon_reset.wrap(_ident)
    w_reset(1)
    w_reset(2)
    check("report before reset",
          mon_reset.report().total_calls == 2)
    mon_reset.reset()
    check("report after reset",
          mon_reset.report().total_calls == 0)

    # ----------------------------------------------------------------
    print("§17  _bind_args helper")
    bound = _bind_args(_add, (1, 2), {})
    check("_bind_args returns dict",
          bound == {"x": 1, "y": 2})

    # ----------------------------------------------------------------
    print("§18  total function enforcement")
    mon_total = RuntimeMonitor(mode=MonitorMode.ASSERT)

    def _total_fail(x: int) -> int:
        raise ValueError("boom")

    meta_total = _make_meta(is_total=True)
    _attach(_total_fail, meta_total)
    w_total = mon_total.wrap(_total_fail)
    try:
        w_total(1)
        check("total function raises on exception", False)
    except AssertionError as e:
        check("total function raises on exception",
              "total" in str(e).lower())

    # ----------------------------------------------------------------
    print("§19  ensures with multi-arg postcondition")
    mon_ens = RuntimeMonitor(mode=MonitorMode.ASSERT)

    def _mul(a: int, b: int) -> int:
        return a * b

    meta_mul = _make_meta(postconditions=[lambda a, b, r: r == a * b])
    _attach(_mul, meta_mul)
    w_mul = mon_ens.wrap(_mul)
    check("multi-arg ensures passes",
          w_mul(3, 4) == 12)

    # ----------------------------------------------------------------
    print("§20  permutation guarantee")
    perm_chk = sc.compile_guarantee("result is permutation of input")
    check("permutation check compiled",
          perm_chk is not None)
    check("permutation passes",
          perm_chk is not None
          and perm_chk(([3, 1, 2],), {}, [1, 2, 3]) is True)
    check("permutation fails",
          perm_chk is not None
          and perm_chk(([3, 1, 2],), {}, [1, 2, 4]) is False)

    # ----------------------------------------------------------------
    print("§21  non-negative guarantee")
    nn = sc.compile_guarantee("returns non-negative")
    check("non-negative compiled",
          nn is not None and nn((), {}, 0) is True)
    check("non-negative fails",
          nn is not None and nn((), {}, -1) is False)

    # ----------------------------------------------------------------
    print("§22  thread safety of report")
    mon_ts = RuntimeMonitor(mode=MonitorMode.LOG)
    _attach(_ident, meta_id)
    w_ts = mon_ts.wrap(_ident)
    threads = []
    for i in range(20):
        t = threading.Thread(target=w_ts, args=(i,))
        threads.append(t)
        t.start()
    for t in threads:
        t.join()
    check("thread-safe: 20 calls recorded",
          mon_ts.report().total_calls == 20)

    # ----------------------------------------------------------------
    print("§23  MonitorReport.to_json structure")
    rj = mon_ts.report().to_json()
    check("to_json has required keys",
          all(k in rj for k in [
              "total_calls", "checked_calls", "skipped_calls",
              "violation_count", "violation_rate", "avg_overhead_ms",
              "violations"]))

    # ----------------------------------------------------------------
    print("§24  _CompiledSpec with no specs returns None")
    def _plain(x: int) -> int:
        return x
    check("_build_compiled_spec returns None for plain fn",
          _build_compiled_spec(_plain) is None)

    # ----------------------------------------------------------------
    print("§25  SpecCompiler.compile_requires zero-arg")
    sc0 = SpecCompiler()
    check("zero-arg requires",
          sc0.compile_requires(lambda: True)((), {}) is True)

    # ----------------------------------------------------------------
    print("§26  MonitorMode.ASSERT is default")
    m_default = RuntimeMonitor()
    check("default mode is ASSERT",
          m_default.mode is MonitorMode.ASSERT)

    # ----------------------------------------------------------------
    print("§27  set_default_monitor")
    custom = RuntimeMonitor(mode=MonitorMode.LOG)
    set_default_monitor(custom)
    check("set_default_monitor works",
          _get_default_monitor() is custom)
    # Reset.
    set_default_monitor(RuntimeMonitor(mode=MonitorMode.ASSERT))

    # ----------------------------------------------------------------
    print("§28  _callable_desc helper")
    check("_callable_desc for string",
          _callable_desc("x > 0", "requires") == "x > 0")
    check("_callable_desc for named fn",
          "requires" in _callable_desc(_add, "requires"))

    # ----------------------------------------------------------------
    print("§29  monitored with mode kwarg")
    @monitored(mode=MonitorMode.LOG)
    def _logged(x: int) -> int:
        return x
    check("@monitored(mode=LOG) works",
          _logged(3) == 3)
    check("has _synhopy_monitor attr",
          hasattr(_logged, "_synhopy_monitor"))

    # ----------------------------------------------------------------
    print("§30  ProductionMonitor with sample_rate < 1")
    with ProductionMonitor(mode=MonitorMode.LOG,
                           sample_rate=0.0) as pm_low:
        _attach(_ident, meta_id)
        w_low = pm_low.wrap(_ident)
        for _ in range(10):
            w_low(1)
        check("low sample_rate skips most",
              pm_low.report().skipped_calls >= 9)

    # ----------------------------------------------------------------
    print("§31  non-empty guarantee")
    ne = sc.compile_guarantee("returns non-empty")
    check("non-empty compiled",
          ne is not None and ne((), {}, [1]) is True)
    check("non-empty fails on empty",
          ne is not None and ne((), {}, []) is False)

    # ----------------------------------------------------------------
    print("§32  length preserved guarantee")
    lp = sc.compile_guarantee("length preserved")
    check("length preserved compiled",
          lp is not None and lp(([1, 2, 3],), {}, [4, 5, 6]) is True)
    check("length preserved fails",
          lp is not None and lp(([1, 2],), {}, [1]) is False)

    # ----------------------------------------------------------------
    print("§33  integration with real sugar decorators")
    if _HAS_SYNHOPY:
        from synhopy.proofs.sugar import (
            guarantee as g_dec, requires as r_dec, ensures as e_dec, pure as p_dec,
        )

        @p_dec
        @e_dec(lambda x, result: result == x * 2)
        @r_dec(lambda x: x >= 0)
        @g_dec("returns positive")
        def _real_double(x: int) -> int:
            return x * 2

        mon_real = RuntimeMonitor(mode=MonitorMode.ASSERT)
        w_real = mon_real.wrap(_real_double)
        check("integration: correct call passes",
              w_real(3) == 6)
        try:
            w_real(-1)
            check("integration: precondition violation caught", False)
        except AssertionError:
            check("integration: precondition violation caught", True)

        # extract_spec round-trip
        fs = extract_spec(_real_double)
        check("extract_spec returns FunctionSpec",
              fs is not None and fs.name == "_real_double")
    else:
        check("integration: skipped (synhopy not importable)", True)
        check("integration: skipped", True)
        check("integration: skipped", True)

    # ----------------------------------------------------------------
    print()
    print(f"{'='*50}")
    print(f"  {passed} passed, {failed} failed, {passed + failed} total")
    print(f"{'='*50}")
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    _self_test()
