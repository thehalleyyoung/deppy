"""
Comprehensive tests for SynHoPy annotation stripping and roundtrip fidelity.

Proves the workflow is fully reversible:
    annotate → verify → strip → recover original code

Uses pytest.importorskip so all tests gracefully skip when the stripper
module has not been implemented yet.
"""
from __future__ import annotations

import ast
import textwrap

import pytest

# ── graceful skip if stripper not yet available ──────────────────────
stripper = pytest.importorskip(
    "synhopy.tools.stripper",
    reason="synhopy.tools.stripper not yet implemented",
)

# After the importorskip succeeds we can reference the public API.
strip_source: callable = stripper.strip_source  # type: ignore[attr-defined]


# ═════════════════════════════════════════════════════════════════════
#  Helpers
# ═════════════════════════════════════════════════════════════════════

def _dedent(src: str) -> str:
    """Dedent + strip leading/trailing blank lines for readability."""
    return textwrap.dedent(src).strip()


def ast_equal(source1: str, source2: str) -> bool:
    """Compare two Python sources by AST structure (ignore formatting)."""
    return ast.dump(ast.parse(source1)) == ast.dump(ast.parse(source2))


def assert_strips_to(annotated: str, expected: str) -> None:
    """Assert that stripping *annotated* yields code AST-equal to *expected*."""
    stripped = strip_source(_dedent(annotated))
    exp = _dedent(expected)
    assert ast_equal(stripped, exp), (
        f"AST mismatch.\n--- stripped ---\n{stripped}\n--- expected ---\n{exp}"
    )


def assert_source_equal(annotated: str, expected: str) -> None:
    """Assert exact textual equality after stripping (modulo surrounding ws)."""
    stripped = strip_source(_dedent(annotated)).strip()
    exp = _dedent(expected)
    assert stripped == exp, (
        f"Text mismatch.\n--- stripped ---\n{stripped}\n--- expected ---\n{exp}"
    )


# ═════════════════════════════════════════════════════════════════════
#  §1  Decorator stripping
# ═════════════════════════════════════════════════════════════════════

class TestDecoratorStripping:
    """Individual SynHoPy decorators are removed, leaving bare functions."""

    def test_strip_guarantee(self):
        assert_strips_to(
            '''
            @guarantee("returns positive")
            def f(x):
                return abs(x)
            ''',
            '''
            def f(x):
                return abs(x)
            ''',
        )

    def test_strip_requires(self):
        assert_strips_to(
            '''
            @requires(lambda x: x > 0)
            def f(x):
                return x
            ''',
            '''
            def f(x):
                return x
            ''',
        )

    def test_strip_ensures(self):
        assert_strips_to(
            '''
            @ensures(lambda x, r: r >= 0)
            def g(x):
                return x * x
            ''',
            '''
            def g(x):
                return x * x
            ''',
        )

    def test_strip_pure(self):
        assert_strips_to(
            '''
            @pure
            def add(a, b):
                return a + b
            ''',
            '''
            def add(a, b):
                return a + b
            ''',
        )

    def test_strip_reads(self):
        assert_strips_to(
            '''
            @reads
            def get_len(xs):
                return len(xs)
            ''',
            '''
            def get_len(xs):
                return len(xs)
            ''',
        )

    def test_strip_mutates(self):
        assert_strips_to(
            '''
            @mutates
            def append_one(xs):
                xs.append(1)
            ''',
            '''
            def append_one(xs):
                xs.append(1)
            ''',
        )

    def test_strip_total(self):
        assert_strips_to(
            '''
            @total
            def identity(x):
                return x
            ''',
            '''
            def identity(x):
                return x
            ''',
        )

    def test_strip_partial_fn(self):
        assert_strips_to(
            '''
            @partial_fn
            def maybe_div(a, b):
                return a / b
            ''',
            '''
            def maybe_div(a, b):
                return a / b
            ''',
        )

    def test_strip_invariant(self):
        assert_strips_to(
            '''
            @invariant("self.balance >= 0")
            def withdraw(self, amount):
                self.balance -= amount
            ''',
            '''
            def withdraw(self, amount):
                self.balance -= amount
            ''',
        )

    def test_strip_decreases(self):
        assert_strips_to(
            '''
            @decreases("len(xs)")
            def quicksort(xs):
                if len(xs) <= 1:
                    return xs
                pivot = xs[0]
                lo = [x for x in xs[1:] if x <= pivot]
                hi = [x for x in xs[1:] if x > pivot]
                return quicksort(lo) + [pivot] + quicksort(hi)
            ''',
            '''
            def quicksort(xs):
                if len(xs) <= 1:
                    return xs
                pivot = xs[0]
                lo = [x for x in xs[1:] if x <= pivot]
                hi = [x for x in xs[1:] if x > pivot]
                return quicksort(lo) + [pivot] + quicksort(hi)
            ''',
        )

    def test_strip_verify(self):
        assert_strips_to(
            '''
            @verify
            def checked(x):
                return x + 1
            ''',
            '''
            def checked(x):
                return x + 1
            ''',
        )

    def test_strip_stacked_decorators(self):
        assert_strips_to(
            '''
            @verify
            @guarantee("positive result")
            @requires(lambda x: x > 0)
            @ensures(lambda x, r: r > x)
            @pure
            def double(x):
                return x * 2
            ''',
            '''
            def double(x):
                return x * 2
            ''',
        )

    def test_preserve_non_synhopy_decorators(self):
        assert_strips_to(
            '''
            @staticmethod
            @guarantee("always works")
            def helper():
                return 42
            ''',
            '''
            @staticmethod
            def helper():
                return 42
            ''',
        )

    def test_preserve_functools_wraps(self):
        assert_strips_to(
            '''
            import functools

            @guarantee("wrapper preserves semantics")
            @functools.wraps
            def wrapper(f):
                return f
            ''',
            '''
            import functools

            @functools.wraps
            def wrapper(f):
                return f
            ''',
        )

    def test_strip_decorator_on_class(self):
        assert_strips_to(
            '''
            @invariant("balance >= 0")
            class BankAccount:
                def __init__(self):
                    self.balance = 0
            ''',
            '''
            class BankAccount:
                def __init__(self):
                    self.balance = 0
            ''',
        )

    def test_strip_about_decorator(self):
        assert_strips_to(
            '''
            @about(target_func)
            def proof_of_target():
                pass
            ''',
            '''
            def proof_of_target():
                pass
            ''',
        )


# ═════════════════════════════════════════════════════════════════════
#  §2  Import stripping
# ═════════════════════════════════════════════════════════════════════

class TestImportStripping:
    """SynHoPy-related imports are removed; others survive."""

    def test_strip_from_synhopy_import(self):
        assert_strips_to(
            '''
            from synhopy.proofs.sugar import guarantee, requires

            def f(x):
                return x
            ''',
            '''
            def f(x):
                return x
            ''',
        )

    def test_strip_star_import(self):
        assert_strips_to(
            '''
            from synhopy import *

            def f():
                pass
            ''',
            '''
            def f():
                pass
            ''',
        )

    def test_strip_plain_import_synhopy(self):
        assert_strips_to(
            '''
            import synhopy

            x = 1
            ''',
            '''
            x = 1
            ''',
        )

    def test_preserve_unrelated_imports(self):
        assert_strips_to(
            '''
            import os
            from synhopy.proofs.sugar import guarantee
            import math

            def f(x):
                return math.sqrt(x)
            ''',
            '''
            import os
            import math

            def f(x):
                return math.sqrt(x)
            ''',
        )

    def test_strip_multiple_synhopy_import_lines(self):
        assert_strips_to(
            '''
            from synhopy.proofs.sugar import guarantee, pure
            from synhopy.core.kernel import ProofKernel
            from synhopy.effects.effect_types import EffectChecker

            def f():
                pass
            ''',
            '''
            def f():
                pass
            ''',
        )

    def test_strip_import_synhopy_submodule(self):
        assert_strips_to(
            '''
            import synhopy.proofs.sugar as sugar

            def f():
                pass
            ''',
            '''
            def f():
                pass
            ''',
        )


# ═════════════════════════════════════════════════════════════════════
#  §3  Statement stripping
# ═════════════════════════════════════════════════════════════════════

class TestStatementStripping:
    """Standalone SynHoPy proof/assertion calls are removed."""

    def test_strip_assume_call(self):
        assert_strips_to(
            '''
            def f(x):
                assume(x > 0)
                return x + 1
            ''',
            '''
            def f(x):
                return x + 1
            ''',
        )

    def test_strip_check_call(self):
        assert_strips_to(
            '''
            def f(x):
                result = x * 2
                check(result > 0)
                return result
            ''',
            '''
            def f(x):
                result = x * 2
                return result
            ''',
        )

    def test_strip_given_call(self):
        assert_strips_to(
            '''
            given("commutativity of addition")

            def add(a, b):
                return a + b
            ''',
            '''
            def add(a, b):
                return a + b
            ''',
        )

    def test_strip_proof_assignment(self):
        assert_strips_to(
            '''
            result = Proof("sorted(sorted(xs)) == sorted(xs)").by_axiom("sorted_idem", "builtins").qed()

            def f():
                pass
            ''',
            '''
            def f():
                pass
            ''',
        )

    def test_strip_library_trust_block(self):
        assert_strips_to(
            '''
            with library_trust("sympy") as sp:
                sp.axiom("expand(a+b) == expand(a) + expand(b)")
                sp.axiom("simplify is idempotent")

            def f(x):
                return x
            ''',
            '''
            def f(x):
                return x
            ''',
        )

    def test_strip_multiple_statements(self):
        assert_strips_to(
            '''
            given("associativity of +")
            assume(True)

            def f(x):
                check(x > 0)
                return x
            ''',
            '''
            def f(x):
                return x
            ''',
        )


# ═════════════════════════════════════════════════════════════════════
#  §4  Roundtrip tests  (original → annotated → strip → AST-equal)
# ═════════════════════════════════════════════════════════════════════

class TestRoundtrip:
    """After annotating clean code then stripping, we recover the original AST."""

    def test_roundtrip_simple_function(self):
        original = _dedent('''
            def add(a, b):
                return a + b
        ''')
        annotated = _dedent('''
            from synhopy.proofs.sugar import guarantee, pure

            @guarantee("returns sum")
            @pure
            def add(a, b):
                return a + b
        ''')
        stripped = strip_source(annotated)
        assert ast_equal(original, stripped)

    def test_roundtrip_class_with_methods(self):
        original = _dedent('''
            class Stack:
                def __init__(self):
                    self._items = []

                def push(self, item):
                    self._items.append(item)

                def pop(self):
                    return self._items.pop()

                def is_empty(self):
                    return len(self._items) == 0
        ''')
        annotated = _dedent('''
            from synhopy.proofs.sugar import guarantee, requires, invariant, pure, mutates

            @invariant("self._items is a list")
            class Stack:
                def __init__(self):
                    self._items = []

                @mutates
                @guarantee("item is added to top")
                def push(self, item):
                    self._items.append(item)

                @requires(lambda self: len(self._items) > 0)
                @mutates
                def pop(self):
                    return self._items.pop()

                @pure
                def is_empty(self):
                    return len(self._items) == 0
        ''')
        stripped = strip_source(annotated)
        assert ast_equal(original, stripped)

    def test_roundtrip_multiple_functions(self):
        original = _dedent('''
            def square(x):
                return x * x

            def cube(x):
                return x * x * x
        ''')
        annotated = _dedent('''
            from synhopy.proofs.sugar import guarantee, pure, ensures

            @guarantee("returns x squared")
            @pure
            def square(x):
                return x * x

            @guarantee("returns x cubed")
            @ensures(lambda x, r: r == x ** 3)
            @pure
            def cube(x):
                return x * x * x
        ''')
        stripped = strip_source(annotated)
        assert ast_equal(original, stripped)

    def test_roundtrip_function_with_existing_decorators(self):
        original = _dedent('''
            import functools

            class MyClass:
                @staticmethod
                def helper():
                    return 42

                @classmethod
                def from_value(cls, v):
                    return cls(v)
        ''')
        annotated = _dedent('''
            import functools
            from synhopy.proofs.sugar import guarantee, pure

            class MyClass:
                @staticmethod
                @guarantee("returns constant 42")
                @pure
                def helper():
                    return 42

                @classmethod
                @guarantee("constructs from value")
                def from_value(cls, v):
                    return cls(v)
        ''')
        stripped = strip_source(annotated)
        assert ast_equal(original, stripped)

    def test_roundtrip_with_inline_statements(self):
        original = _dedent('''
            def safe_div(a, b):
                if b == 0:
                    raise ValueError("division by zero")
                return a / b
        ''')
        annotated = _dedent('''
            from synhopy.proofs.sugar import guarantee, requires

            @guarantee("returns a / b when b != 0")
            @requires(lambda a, b: b != 0)
            def safe_div(a, b):
                assume(b != 0)
                if b == 0:
                    raise ValueError("division by zero")
                result = a / b
                check(result * b == a)
                return result
        ''')
        # After stripping, the assume and check calls are removed,
        # and the temp variable stays — so we compare ASTs.
        stripped = strip_source(annotated)
        # The stripped version will have the temp var but no assume/check.
        expected = _dedent('''
            def safe_div(a, b):
                if b == 0:
                    raise ValueError("division by zero")
                result = a / b
                return result
        ''')
        assert ast_equal(stripped, expected)


# ═════════════════════════════════════════════════════════════════════
#  §5  Realistic roundtrips
# ═════════════════════════════════════════════════════════════════════

class TestRealisticRoundtrip:
    """Full-module-level annotate→strip roundtrips."""

    def test_full_module_roundtrip(self):
        original = _dedent('''
            import math

            PI = 3.14159265

            class Circle:
                def __init__(self, radius):
                    self.radius = radius

                def area(self):
                    return math.pi * self.radius ** 2

                def circumference(self):
                    return 2 * math.pi * self.radius

            def distance(x1, y1, x2, y2):
                return math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2)
        ''')
        annotated = _dedent('''
            import math
            from synhopy.proofs.sugar import guarantee, pure, requires, invariant
            from synhopy.core.kernel import ProofKernel

            given("pi is irrational")

            PI = 3.14159265

            @invariant("self.radius >= 0")
            class Circle:
                def __init__(self, radius):
                    assume(radius >= 0)
                    self.radius = radius

                @pure
                @guarantee("returns non-negative area")
                def area(self):
                    return math.pi * self.radius ** 2

                @pure
                @guarantee("returns non-negative circumference")
                def circumference(self):
                    return 2 * math.pi * self.radius

            @pure
            @guarantee("returns Euclidean distance")
            def distance(x1, y1, x2, y2):
                return math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2)
        ''')
        stripped = strip_source(annotated)
        # __init__ lost its assume() call, so we build the expected version:
        expected = _dedent('''
            import math

            PI = 3.14159265

            class Circle:
                def __init__(self, radius):
                    self.radius = radius

                def area(self):
                    return math.pi * self.radius ** 2

                def circumference(self):
                    return 2 * math.pi * self.radius

            def distance(x1, y1, x2, y2):
                return math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2)
        ''')
        assert ast_equal(stripped, expected)

    def test_sympy_like_module_roundtrip(self):
        original = _dedent('''
            def expand(expr):
                return expr

            def simplify(expr):
                return expr

            def factor(expr):
                return expr
        ''')
        annotated = _dedent('''
            from synhopy.proofs.sugar import guarantee, pure

            with library_trust("sympy") as sp:
                sp.axiom("simplify(simplify(e)) == simplify(e)", name="simplify_idem")

            @guarantee("expands expression")
            @pure
            def expand(expr):
                return expr

            @guarantee("simplifies expression")
            @pure
            def simplify(expr):
                return expr

            @guarantee("factors expression")
            @pure
            def factor(expr):
                return expr
        ''')
        stripped = strip_source(annotated)
        assert ast_equal(stripped, original)

    def test_mixed_synhopy_and_regular_code(self):
        original = _dedent('''
            import os
            import json

            CONFIG_PATH = "config.json"

            def load_config(path=CONFIG_PATH):
                with open(path) as f:
                    return json.load(f)

            def get_env(key, default=None):
                return os.environ.get(key, default)

            class AppConfig:
                def __init__(self, data):
                    self.data = data

                def get(self, key):
                    return self.data.get(key)
        ''')
        annotated = _dedent('''
            import os
            import json
            from synhopy.proofs.sugar import guarantee, pure, reads

            CONFIG_PATH = "config.json"

            @reads
            @guarantee("returns parsed JSON config")
            def load_config(path=CONFIG_PATH):
                with open(path) as f:
                    return json.load(f)

            @pure
            def get_env(key, default=None):
                return os.environ.get(key, default)

            class AppConfig:
                def __init__(self, data):
                    self.data = data

                @pure
                def get(self, key):
                    return self.data.get(key)
        ''')
        stripped = strip_source(annotated)
        assert ast_equal(stripped, original)


# ═════════════════════════════════════════════════════════════════════
#  §6  Edge cases
# ═════════════════════════════════════════════════════════════════════

class TestEdgeCases:
    """Corner cases that a robust stripper must handle."""

    def test_empty_file(self):
        stripped = strip_source("").strip()
        # An empty module may strip to "" or "pass" — both are valid empty Python.
        assert stripped == "" or stripped == "pass"

    def test_no_synhopy_annotations(self):
        source = _dedent('''
            def hello():
                print("hi")
        ''')
        stripped = strip_source(source)
        assert ast_equal(stripped, source)

    def test_deeply_nested_function(self):
        assert_strips_to(
            '''
            class Outer:
                class Inner:
                    @guarantee("deep")
                    @pure
                    def method(self):
                        return 1
            ''',
            '''
            class Outer:
                class Inner:
                    def method(self):
                        return 1
            ''',
        )

    def test_lambda_based_requires(self):
        assert_strips_to(
            '''
            @requires(lambda x: x > 0)
            @requires(lambda x: x < 100)
            def bounded(x):
                return x
            ''',
            '''
            def bounded(x):
                return x
            ''',
        )

    def test_multiline_decorator_argument(self):
        assert_strips_to(
            '''
            @guarantee(
                "returns a sorted list "
                "with no duplicates"
            )
            def unique_sorted(lst):
                return sorted(set(lst))
            ''',
            '''
            def unique_sorted(lst):
                return sorted(set(lst))
            ''',
        )

    def test_string_mentioning_guarantee_not_stripped(self):
        source = _dedent('''
            def f():
                return "guarantee this is kept"
        ''')
        stripped = strip_source(source)
        assert ast_equal(stripped, source)

    def test_comments_mentioning_synhopy_preserved(self):
        source = _dedent('''
            # This function uses synhopy guarantee for verification.
            def f():
                # check that x > 0 (not a synhopy call)
                return 1
        ''')
        stripped = strip_source(source)
        assert ast_equal(stripped, source)

    def test_variable_named_guarantee_not_stripped(self):
        source = _dedent('''
            guarantee = "some string"
            check = True
            assume = 42
        ''')
        stripped = strip_source(source)
        assert ast_equal(stripped, source)

    def test_function_named_check_not_stripped(self):
        """A user-defined function called 'check' must be preserved."""
        source = _dedent('''
            def check(condition):
                if not condition:
                    raise AssertionError
        ''')
        stripped = strip_source(source)
        assert ast_equal(stripped, source)

    def test_only_synhopy_imports(self):
        """A file that is ONLY synhopy imports strips to empty/pass."""
        source = _dedent('''
            from synhopy.proofs.sugar import guarantee, pure
            from synhopy.core.kernel import ProofKernel
            import synhopy
        ''')
        stripped = strip_source(source).strip()
        # Empty module may be "" or "pass" — both represent no meaningful code.
        assert stripped == "" or stripped == "pass"

    def test_decorator_with_no_args(self):
        """Bare decorators like @pure and @verify have no parentheses."""
        assert_strips_to(
            '''
            @pure
            @verify
            def f():
                return 1
            ''',
            '''
            def f():
                return 1
            ''',
        )

    def test_async_function_decorator_strip(self):
        assert_strips_to(
            '''
            @guarantee("returns awaited result")
            @pure
            async def fetch(url):
                return await get(url)
            ''',
            '''
            async def fetch(url):
                return await get(url)
            ''',
        )

    def test_multiple_classes_and_functions(self):
        assert_strips_to(
            '''
            from synhopy.proofs.sugar import guarantee, invariant, pure

            @invariant("x >= 0")
            class A:
                pass

            @guarantee("does nothing")
            def noop():
                pass

            @invariant("y >= 0")
            class B:
                pass
            ''',
            '''
            class A:
                pass

            def noop():
                pass

            class B:
                pass
            ''',
        )

    def test_assume_inside_if_block(self):
        assert_strips_to(
            '''
            def f(x):
                if x > 0:
                    assume(x > 0)
                    return x
                return 0
            ''',
            '''
            def f(x):
                if x > 0:
                    return x
                return 0
            ''',
        )

    def test_check_in_loop_body(self):
        assert_strips_to(
            '''
            def sum_positive(xs):
                total = 0
                for x in xs:
                    check(total >= 0)
                    total += x
                return total
            ''',
            '''
            def sum_positive(xs):
                total = 0
                for x in xs:
                    total += x
                return total
            ''',
        )


# ═════════════════════════════════════════════════════════════════════
#  §7  Idempotency & stability
# ═════════════════════════════════════════════════════════════════════

class TestStability:
    """Stripping is idempotent and stable on non-synhopy code."""

    def test_strip_is_idempotent(self):
        source = _dedent('''
            from synhopy.proofs.sugar import guarantee, pure

            @guarantee("sorted")
            @pure
            def sort(xs):
                return sorted(xs)
        ''')
        once = strip_source(source)
        twice = strip_source(once)
        assert ast_equal(once, twice)

    def test_strip_plain_python_is_identity(self):
        source = _dedent('''
            import os

            def walk(path):
                for root, dirs, files in os.walk(path):
                    yield from files
        ''')
        stripped = strip_source(source)
        assert ast_equal(source, stripped)

    def test_strip_preserves_type_hints(self):
        assert_strips_to(
            '''
            from synhopy.proofs.sugar import guarantee

            @guarantee("typed addition")
            def add(a: int, b: int) -> int:
                return a + b
            ''',
            '''
            def add(a: int, b: int) -> int:
                return a + b
            ''',
        )

    def test_strip_preserves_docstrings(self):
        assert_strips_to(
            '''
            @guarantee("documented")
            def f(x):
                """Return x unchanged."""
                return x
            ''',
            '''
            def f(x):
                """Return x unchanged."""
                return x
            ''',
        )
