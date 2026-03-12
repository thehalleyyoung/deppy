"""Tests for exception flow analysis.

Covers HandlerInfo, RaiseInfo, ExceptionFlowResult, ExceptionAnalyzer.analyze,
implicit exception detection, handler processing, uncaught exception
computation, and exception hierarchy checking.
"""

from __future__ import annotations

import ast
import textwrap

import pytest

from deppy.native_python.exception_analyzer import (
    ExceptionAnalyzer,
    ExceptionFlowResult,
    HandlerInfo,
    RaiseInfo,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _parse_func(source: str) -> ast.FunctionDef:
    tree = ast.parse(textwrap.dedent(source))
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return node
    raise ValueError("No function found")


def _analyze(source: str, *, include_implicit: bool = True) -> ExceptionFlowResult:
    func = _parse_func(source)
    analyzer = ExceptionAnalyzer(include_implicit=include_implicit)
    return analyzer.analyze(func)


# ===================================================================
#  HandlerInfo
# ===================================================================


class TestHandlerInfo:
    """Tests for HandlerInfo."""

    def test_basic(self):
        hi = HandlerInfo(_exception_types=("ValueError",), _line=10)
        assert hi.exception_types == ("ValueError",)
        assert hi.line == 10
        assert not hi.is_bare
        assert not hi.catches_all

    def test_bare_handler(self):
        hi = HandlerInfo(_is_bare=True)
        assert hi.is_bare
        assert hi.catches_all

    def test_catches_exception(self):
        hi = HandlerInfo(_exception_types=("Exception",))
        assert hi.catches_all

    def test_reraises(self):
        hi = HandlerInfo(_exception_types=("ValueError",), _reraises=True)
        assert hi.reraises

    def test_transforms(self):
        hi = HandlerInfo(
            _exception_types=("ValueError",),
            _transforms_to="RuntimeError",
        )
        assert hi.transforms_to == "RuntimeError"


# ===================================================================
#  RaiseInfo
# ===================================================================


class TestRaiseInfo:
    """Tests for RaiseInfo."""

    def test_basic(self):
        ri = RaiseInfo(_exception_type="ValueError", _line=5)
        assert ri.exception_type == "ValueError"
        assert ri.line == 5
        assert not ri.is_reraise
        assert not ri.is_conditional

    def test_reraise(self):
        ri = RaiseInfo(_is_reraise=True)
        assert ri.is_reraise
        assert ri.exception_type is None

    def test_conditional(self):
        ri = RaiseInfo(
            _exception_type="ValueError",
            _is_conditional=True,
            _condition_text="x < 0",
        )
        assert ri.is_conditional


# ===================================================================
#  ExceptionAnalyzer - explicit raises
# ===================================================================


class TestExceptionAnalyzerExplicit:
    """Tests for analyzing explicit raise statements."""

    def test_simple_raise(self):
        result = _analyze("""\
        def f():
            raise ValueError("bad")
        """)
        assert "ValueError" in result.raised_exceptions
        assert "ValueError" in result.uncaught_exceptions

    def test_multiple_raises(self):
        result = _analyze("""\
        def f(x):
            if x < 0:
                raise ValueError("negative")
            if x > 100:
                raise OverflowError("too big")
        """)
        assert "ValueError" in result.raised_exceptions
        assert "OverflowError" in result.raised_exceptions

    def test_raise_from(self):
        result = _analyze("""\
        def f():
            try:
                pass
            except Exception as e:
                raise RuntimeError("wrapped") from e
        """)
        assert "RuntimeError" in result.raised_exceptions

    def test_no_raises(self):
        result = _analyze("""\
        def f():
            return 42
        """, include_implicit=False)
        assert len(result.raised_exceptions) == 0


# ===================================================================
#  ExceptionAnalyzer - caught exceptions
# ===================================================================


class TestExceptionAnalyzerCaught:
    """Tests for exception handler analysis."""

    def test_caught_exception(self):
        result = _analyze("""\
        def f():
            try:
                raise ValueError("bad")
            except ValueError:
                pass
        """)
        assert "ValueError" in result.caught_exceptions

    def test_bare_except(self):
        result = _analyze("""\
        def f():
            try:
                raise ValueError("bad")
            except:
                pass
        """)
        assert result._suppresses_all or len(result.uncaught_exceptions) == 0

    def test_handler_with_alias(self):
        result = _analyze("""\
        def f():
            try:
                pass
            except ValueError as e:
                print(e)
        """)
        handlers = result.handlers
        assert len(handlers) >= 1
        assert handlers[0].alias == "e"

    def test_multiple_handlers(self):
        result = _analyze("""\
        def f():
            try:
                pass
            except ValueError:
                pass
            except TypeError:
                pass
        """)
        assert len(result.handlers) == 2

    def test_tuple_handler(self):
        result = _analyze("""\
        def f():
            try:
                pass
            except (ValueError, TypeError):
                pass
        """)
        assert len(result.handlers) == 1
        types = result.handlers[0].exception_types
        assert "ValueError" in types
        assert "TypeError" in types


# ===================================================================
#  ExceptionAnalyzer - uncaught / propagation
# ===================================================================


class TestExceptionAnalyzerPropagation:
    """Tests for uncaught exception computation."""

    def test_uncaught_when_not_handled(self):
        result = _analyze("""\
        def f():
            raise KeyError("missing")
        """)
        assert "KeyError" in result.uncaught_exceptions

    def test_caught_does_not_propagate(self):
        result = _analyze("""\
        def f():
            try:
                raise KeyError("missing")
            except KeyError:
                pass
        """, include_implicit=False)
        assert "KeyError" not in result.uncaught_exceptions

    def test_reraise_propagates(self):
        result = _analyze("""\
        def f():
            try:
                raise ValueError("bad")
            except ValueError:
                raise
        """)
        assert "ValueError" in result.uncaught_exceptions

    def test_transform_propagates(self):
        result = _analyze("""\
        def f():
            try:
                raise ValueError("bad")
            except ValueError:
                raise RuntimeError("wrapped")
        """)
        assert "RuntimeError" in result.uncaught_exceptions

    def test_is_exception_safe(self):
        result = _analyze("""\
        def f():
            try:
                raise ValueError()
            except ValueError:
                pass
        """, include_implicit=False)
        assert result.is_exception_safe

    def test_has_finally(self):
        result = _analyze("""\
        def f():
            try:
                pass
            finally:
                cleanup()
        """)
        assert result.has_finally


# ===================================================================
#  ExceptionAnalyzer - implicit exceptions
# ===================================================================


class TestExceptionAnalyzerImplicit:
    """Tests for implicit exception detection."""

    def test_subscript_implicit(self):
        result = _analyze("""\
        def f(lst):
            return lst[0]
        """)
        assert "IndexError" in result._implicit_exceptions or "KeyError" in result._implicit_exceptions

    def test_division_implicit(self):
        result = _analyze("""\
        def f(a, b):
            return a / b
        """)
        assert "ZeroDivisionError" in result._implicit_exceptions

    def test_attribute_implicit(self):
        result = _analyze("""\
        def f(obj):
            return obj.name
        """)
        assert "AttributeError" in result._implicit_exceptions

    def test_conversion_implicit(self):
        result = _analyze("""\
        def f(s):
            return int(s)
        """)
        implicits = result._implicit_exceptions
        assert "ValueError" in implicits or "TypeError" in implicits

    def test_no_implicit_when_disabled(self):
        result = _analyze("""\
        def f(lst):
            return lst[0]
        """, include_implicit=False)
        assert len(result._implicit_exceptions) == 0

    def test_all_exception_types(self):
        result = _analyze("""\
        def f(lst):
            try:
                return lst[0]
            except IndexError:
                raise ValueError("empty")
        """)
        all_types = result.all_exception_types
        assert "IndexError" in all_types or "ValueError" in all_types


# ===================================================================
#  ExceptionAnalyzer - hierarchy
# ===================================================================


class TestExceptionHierarchy:
    """Tests for exception hierarchy checking."""

    def test_parent_catches_child(self):
        result = _analyze("""\
        def f():
            try:
                raise FileNotFoundError()
            except OSError:
                pass
        """, include_implicit=False)
        assert "FileNotFoundError" not in result.uncaught_exceptions

    def test_exception_catches_all_children(self):
        result = _analyze("""\
        def f():
            try:
                raise KeyError("bad")
            except Exception:
                pass
        """, include_implicit=False)
        assert "KeyError" not in result.uncaught_exceptions

    def test_cache(self):
        source = textwrap.dedent("""\
        def f():
            raise ValueError()
        """)
        func = _parse_func(source)
        analyzer = ExceptionAnalyzer()
        r1 = analyzer.analyze(func)
        r2 = analyzer.analyze(func)
        assert r1 is r2  # Same cached object

    def test_clear_cache(self):
        source = textwrap.dedent("""\
        def f():
            raise ValueError()
        """)
        func = _parse_func(source)
        analyzer = ExceptionAnalyzer()
        r1 = analyzer.analyze(func)
        analyzer.clear_cache()
        r2 = analyzer.analyze(func)
        assert r1 is not r2
