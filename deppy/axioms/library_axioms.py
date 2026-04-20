"""
Deppy Library Axiom System
=============================

Provides a framework for declaring and using axioms about external Python
libraries (sympy, numpy, torch, etc.) in proofs.  These are **trusted
assumptions** — they live at ``TrustLevel.AXIOM_TRUSTED`` and become proof
obligations that can later be discharged by property-based testing.

Usage::

    from deppy.axioms.library_axioms import (
        AxiomRegistry, SympyAxioms, NumpyAxioms,
        TorchAxioms, BuiltinAxioms,
    )

    registry = AxiomRegistry()
    SympyAxioms.register_all(registry)
    ax = registry.lookup("sympy", "expand_add")
"""
from __future__ import annotations

import hashlib
import random
import time
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Callable

from deppy.core.kernel import AxiomInvocation, AxiomEntry, ProofKernel


# ═══════════════════════════════════════════════════════════════════
# Library Axiom Dataclass
# ═══════════════════════════════════════════════════════════════════

@dataclass
class LibraryAxiom:
    """A trusted axiom about an external library.

    Parameters
    ----------
    name : str
        Short identifier, e.g. ``"expand_add"``.
    module : str
        Library module, e.g. ``"sympy"``.
    statement : str
        Formal-ish statement of the axiom.
    description : str
        Human-readable description.
    params : list[str]
        Names of parameters the axiom is quantified over.
    verified_by_testing : bool
        Whether the axiom has been empirically tested.
    test_count : int
        Number of successful tests run so far.
    counterexample : str | None
        String representation of a counterexample, if one was found.
    """
    name: str
    module: str
    statement: str
    description: str
    params: list[str] = field(default_factory=list)
    verified_by_testing: bool = False
    test_count: int = 0
    counterexample: str | None = None

    # ── helpers ────────────────────────────────────────────────────

    @property
    def qualified_name(self) -> str:
        """Return ``module.name``."""
        return f"{self.module}.{self.name}" if self.module else self.name

    @property
    def is_refuted(self) -> bool:
        return self.counterexample is not None

    def to_kernel_entry(self) -> AxiomEntry:
        """Convert to a kernel-level ``AxiomEntry``."""
        return AxiomEntry(
            name=self.name,
            statement=self.statement,
            module=self.module,
            verified_by_testing=self.verified_by_testing,
        )

    def to_invocation(self) -> AxiomInvocation:
        """Create a proof term invoking this axiom."""
        return AxiomInvocation(name=self.name, module=self.module)

    def fingerprint(self) -> str:
        """Deterministic hash of the axiom content."""
        blob = f"{self.module}:{self.name}:{self.statement}"
        return hashlib.sha256(blob.encode()).hexdigest()[:16]

    def __repr__(self) -> str:
        status = "✓" if self.verified_by_testing else ("✗" if self.is_refuted else "?")
        return f"LibraryAxiom({status} {self.qualified_name}: {self.statement!r})"


# ═══════════════════════════════════════════════════════════════════
# Test Results
# ═══════════════════════════════════════════════════════════════════

class TestVerdict(Enum):
    PASSED = auto()
    FAILED = auto()
    ERROR = auto()
    SKIPPED = auto()


@dataclass
class TestResult:
    """Result of property-based testing of an axiom."""
    axiom_name: str
    verdict: TestVerdict
    tests_run: int = 0
    failures: int = 0
    errors: int = 0
    counterexample: str | None = None
    elapsed_seconds: float = 0.0

    @property
    def passed(self) -> bool:
        return self.verdict == TestVerdict.PASSED

    def __repr__(self) -> str:
        v = self.verdict.name
        return f"TestResult({self.axiom_name}: {v}, {self.tests_run} tests)"


# ═══════════════════════════════════════════════════════════════════
# Axiom Registry
# ═══════════════════════════════════════════════════════════════════

class AxiomRegistry:
    """Central registry of library axioms.

    Axioms are indexed by ``(module, name)`` pairs and can be looked up
    individually or listed by module.
    """

    def __init__(self) -> None:
        self._axioms: dict[tuple[str, str], LibraryAxiom] = {}
        self._by_module: dict[str, list[LibraryAxiom]] = {}

    # ── mutation ───────────────────────────────────────────────────

    def register(self, axiom: LibraryAxiom) -> None:
        """Register a library axiom.

        Raises ``ValueError`` if an axiom with the same ``(module, name)``
        already exists.
        """
        key = (axiom.module, axiom.name)
        if key in self._axioms:
            raise ValueError(
                f"Axiom already registered: {axiom.qualified_name}"
            )
        self._axioms[key] = axiom
        self._by_module.setdefault(axiom.module, []).append(axiom)

    def register_many(self, axioms: list[LibraryAxiom]) -> None:
        """Register multiple axioms at once."""
        for ax in axioms:
            self.register(ax)

    def unregister(self, module: str, name: str) -> bool:
        """Remove an axiom from the registry.  Returns ``True`` if removed."""
        key = (module, name)
        ax = self._axioms.pop(key, None)
        if ax is None:
            return False
        mod_list = self._by_module.get(module, [])
        self._by_module[module] = [a for a in mod_list if a.name != name]
        return True

    # ── queries ────────────────────────────────────────────────────

    def lookup(self, module: str, name: str) -> LibraryAxiom | None:
        """Look up an axiom by *module* and *name*."""
        return self._axioms.get((module, name))

    def contains(self, module: str, name: str) -> bool:
        return (module, name) in self._axioms

    def all_axioms(self, module: str | None = None) -> list[LibraryAxiom]:
        """Return all axioms, optionally filtered by *module*."""
        if module is not None:
            return list(self._by_module.get(module, []))
        return list(self._axioms.values())

    def modules(self) -> list[str]:
        """Return a sorted list of registered modules."""
        return sorted(self._by_module.keys())

    def __len__(self) -> int:
        return len(self._axioms)

    # ── kernel integration ─────────────────────────────────────────

    def install_into_kernel(self, kernel: ProofKernel) -> int:
        """Register every axiom in this registry into a :class:`ProofKernel`.

        Returns the number of axioms installed.
        """
        count = 0
        for ax in self._axioms.values():
            key = ax.qualified_name
            if key not in kernel.axiom_registry:
                kernel.register_axiom(ax.name, ax.statement, ax.module)
                count += 1
        return count

    # ── testing integration ────────────────────────────────────────

    def verify_by_testing(
        self,
        axiom: LibraryAxiom,
        num_tests: int = 100,
        tester: AxiomTester | None = None,
    ) -> bool:
        """Run property-based tests on *axiom* and update its state.

        Returns ``True`` if all tests pass.
        """
        if tester is None:
            tester = AxiomTester()
        result = tester.test_axiom(axiom, num_tests=num_tests)
        axiom.test_count += result.tests_run
        if result.passed:
            axiom.verified_by_testing = True
            return True
        axiom.counterexample = result.counterexample
        return False

    def verify_all(
        self,
        module: str | None = None,
        num_tests: int = 100,
    ) -> dict[str, TestResult]:
        """Test every axiom that has a registered test function.

        Returns a mapping from qualified name to :class:`TestResult`.
        """
        tester = AxiomTester()
        results: dict[str, TestResult] = {}
        for ax in self.all_axioms(module):
            result = tester.test_axiom(ax, num_tests=num_tests)
            ax.test_count += result.tests_run
            if result.passed:
                ax.verified_by_testing = True
            else:
                ax.counterexample = result.counterexample
            results[ax.qualified_name] = result
        return results

    # ── display ────────────────────────────────────────────────────

    def summary(self, module: str | None = None) -> str:
        """Human-readable summary table."""
        axioms = self.all_axioms(module)
        if not axioms:
            return "(no axioms registered)"
        lines = [f"{'Name':40s} {'Module':12s} {'Tests':>6s} Status"]
        lines.append("-" * 70)
        for ax in axioms:
            if ax.is_refuted:
                status = "REFUTED"
            elif ax.verified_by_testing:
                status = f"tested({ax.test_count})"
            else:
                status = "untested"
            lines.append(
                f"{ax.name:40s} {ax.module:12s} {ax.test_count:6d} {status}"
            )
        return "\n".join(lines)

    def __repr__(self) -> str:
        return f"AxiomRegistry({len(self)} axioms, modules={self.modules()})"


# ═══════════════════════════════════════════════════════════════════
# Axiom Tester (property-based)
# ═══════════════════════════════════════════════════════════════════

# Type-tag → generator used by AxiomTester.generate_inputs
_GENERATORS: dict[str, Callable[[], Any]] = {}


def _register_generator(tag: str, gen: Callable[[], Any]) -> None:
    _GENERATORS[tag] = gen


# Default generators for common types
_register_generator("int", lambda: random.randint(-100, 100))
_register_generator("float", lambda: random.uniform(-100.0, 100.0))
_register_generator("posint", lambda: random.randint(1, 100))
_register_generator("nonnegint", lambda: random.randint(0, 100))
_register_generator("bool", lambda: random.choice([True, False]))
_register_generator("str", lambda: "".join(
    random.choices("abcdefghijklmnopqrstuvwxyz", k=random.randint(0, 10))
))
_register_generator(
    "list[int]",
    lambda: [random.randint(-50, 50) for _ in range(random.randint(0, 15))],
)
_register_generator(
    "list[str]",
    lambda: [
        "".join(random.choices("abc", k=random.randint(1, 4)))
        for _ in range(random.randint(0, 8))
    ],
)


class AxiomTester:
    """Property-based tester for library axioms.

    Axioms that carry a ``_test_func`` attribute (added via
    :func:`axiom` decorator with a ``test`` argument, or manually) will be
    invoked with randomly generated inputs.  Axioms without a test function
    receive a ``SKIPPED`` verdict.
    """

    def __init__(self) -> None:
        self.generators: dict[str, Callable[[], Any]] = dict(_GENERATORS)

    def register_generator(self, tag: str, gen: Callable[[], Any]) -> None:
        """Register a custom input generator for *tag*."""
        self.generators[tag] = gen

    # ── main entry ─────────────────────────────────────────────────

    def test_axiom(
        self,
        axiom: LibraryAxiom,
        num_tests: int = 100,
    ) -> TestResult:
        """Run *num_tests* random trials against *axiom*.

        The axiom must have a ``_test_func`` attribute — a callable that
        accepts a dict of parameter values and returns ``True`` when the
        axiom holds.  If ``_test_func`` is missing the test is skipped.
        """
        test_fn: Callable[..., bool] | None = getattr(axiom, "_test_func", None)
        if test_fn is None:
            return TestResult(
                axiom_name=axiom.qualified_name,
                verdict=TestVerdict.SKIPPED,
            )

        t0 = time.monotonic()
        failures = 0
        errors = 0
        counterexample: str | None = None

        for _ in range(num_tests):
            try:
                inputs = self.generate_inputs(axiom.params)
                ok = test_fn(*inputs)
                if not ok:
                    failures += 1
                    if counterexample is None:
                        counterexample = repr(inputs)
            except Exception as exc:  # noqa: BLE001
                errors += 1
                if counterexample is None:
                    counterexample = f"Exception: {exc}"

        elapsed = time.monotonic() - t0

        if failures > 0 or errors > 0:
            verdict = TestVerdict.FAILED
        else:
            verdict = TestVerdict.PASSED

        return TestResult(
            axiom_name=axiom.qualified_name,
            verdict=verdict,
            tests_run=num_tests,
            failures=failures,
            errors=errors,
            counterexample=counterexample,
            elapsed_seconds=elapsed,
        )

    # ── input generation ───────────────────────────────────────────

    def generate_inputs(self, param_types: list[str]) -> list[Any]:
        """Generate a random value for each type tag in *param_types*."""
        result: list[Any] = []
        for tag in param_types:
            gen = self.generators.get(tag)
            if gen is None:
                gen = self.generators.get("int")
            assert gen is not None
            result.append(gen())
        return result


# ═══════════════════════════════════════════════════════════════════
# Decorator-based Axiom Declaration
# ═══════════════════════════════════════════════════════════════════

def library(module: str):
    """Class decorator that sets *module* on all :class:`LibraryAxiom`
    class-attributes of the decorated class.

    Usage::

        @library("sympy")
        class SympyAxioms:
            expand_add = LibraryAxiom(
                name="expand_add", module="sympy", ...
            )
    """
    def decorator(cls: type) -> type:
        cls._library_module = module  # type: ignore[attr-defined]
        for attr_name in list(vars(cls)):
            val = getattr(cls, attr_name)
            if isinstance(val, LibraryAxiom) and not val.module:
                val.module = module
        return cls
    return decorator


def axiom(
    statement: str,
    description: str = "",
    params: list[str] | None = None,
    test: Callable[..., bool] | None = None,
):
    """Method decorator that converts a no-op method into a
    :class:`LibraryAxiom` stored on the class.

    The decorated function is replaced by the axiom object so you can
    reference ``MyAxioms.my_axiom`` as a :class:`LibraryAxiom`.

    Parameters
    ----------
    statement : str
        The formal statement.
    description : str
        Human-readable description.
    params : list[str] | None
        Parameter type-tags for random testing.
    test : callable | None
        A callable ``(*generated_values) -> bool`` for property testing.
    """
    def decorator(fn: Callable[..., Any]) -> LibraryAxiom:
        ax = LibraryAxiom(
            name=fn.__name__,
            module="",
            statement=statement,
            description=description or fn.__doc__ or "",
            params=params or [],
        )
        if test is not None:
            ax._test_func = test  # type: ignore[attr-defined]
        return ax  # type: ignore[return-value]
    return decorator


# ═══════════════════════════════════════════════════════════════════
# SymPy Axioms
# ═══════════════════════════════════════════════════════════════════

def _make(
    name: str,
    module: str,
    statement: str,
    description: str,
    params: list[str] | None = None,
) -> LibraryAxiom:
    return LibraryAxiom(
        name=name,
        module=module,
        statement=statement,
        description=description,
        params=params or [],
    )


@library("sympy")
class SympyAxioms:
    """Axioms about the SymPy computer algebra library.

    Categories: algebraic identities, solve correctness, calculus,
    matrix algebra, simplification, and series.
    """

    # ── algebraic identities ──────────────────────────────────────
    expand_add = _make(
        "expand_add", "sympy",
        "expand(a + b) = expand(a) + expand(b)",
        "expand distributes over addition",
        ["expr", "expr"],
    )
    expand_mul = _make(
        "expand_mul", "sympy",
        "expand(a * b) = expand(a) * expand(b) when a,b are polynomials",
        "expand distributes over multiplication for polynomials",
        ["poly", "poly"],
    )
    simplify_idem = _make(
        "simplify_idem", "sympy",
        "simplify(simplify(e)) = simplify(e)",
        "simplify is idempotent",
        ["expr"],
    )
    factor_expand = _make(
        "factor_expand", "sympy",
        "factor(expand(e)) = e when e is polynomial",
        "factor inverts expand for polynomials",
        ["poly"],
    )
    expand_factor = _make(
        "expand_factor", "sympy",
        "expand(factor(e)) = expand(e) when e is polynomial",
        "expand of factor equals expand",
        ["poly"],
    )
    cancel_ratio = _make(
        "cancel_ratio", "sympy",
        "cancel(p/q) removes common factors of p and q",
        "cancel simplifies rational functions",
        ["poly", "poly"],
    )
    apart_together = _make(
        "apart_together", "sympy",
        "together(apart(e)) = cancel(e) for rational functions",
        "apart and together are inverses up to cancel",
        ["rational"],
    )

    # ── solve correctness ─────────────────────────────────────────
    solve_correct = _make(
        "solve_correct", "sympy",
        "for s in solve(eq, x): eq.subs(x, s) == 0",
        "solutions returned by solve satisfy the equation",
        ["equation", "symbol"],
    )
    solve_linear = _make(
        "solve_linear", "sympy",
        "solve(a*x + b, x) == [-b/a] when a != 0",
        "solve gives the correct root for linear equations",
        ["nonzero", "int"],
    )
    solveset_superset = _make(
        "solveset_superset", "sympy",
        "solve(eq, x) ⊆ solveset(eq, x)",
        "solveset returns at least as many solutions as solve",
        ["equation", "symbol"],
    )

    # ── calculus ──────────────────────────────────────────────────
    diff_sum = _make(
        "diff_sum", "sympy",
        "diff(f + g, x) = diff(f, x) + diff(g, x)",
        "differentiation is linear (addition)",
        ["expr", "expr", "symbol"],
    )
    diff_product = _make(
        "diff_product", "sympy",
        "diff(f * g, x) = f * diff(g, x) + diff(f, x) * g",
        "product rule for differentiation",
        ["expr", "expr", "symbol"],
    )
    diff_chain = _make(
        "diff_chain", "sympy",
        "diff(f(g(x)), x) = f'(g(x)) * g'(x)",
        "chain rule for differentiation",
        ["expr", "expr", "symbol"],
    )
    diff_const = _make(
        "diff_const", "sympy",
        "diff(c, x) = 0 when c is constant w.r.t. x",
        "derivative of a constant is zero",
        ["const", "symbol"],
    )
    integrate_diff = _make(
        "integrate_diff", "sympy",
        "integrate(diff(f, x), x) = f + C",
        "fundamental theorem of calculus",
        ["expr", "symbol"],
    )
    diff_power = _make(
        "diff_power", "sympy",
        "diff(x**n, x) = n * x**(n-1)",
        "power rule for differentiation",
        ["symbol", "posint"],
    )
    integrate_linear = _make(
        "integrate_linear", "sympy",
        "integrate(a*f + b*g, x) = a*integrate(f, x) + b*integrate(g, x)",
        "integration is linear",
        ["int", "expr", "int", "expr", "symbol"],
    )

    # ── limits ────────────────────────────────────────────────────
    limit_sum = _make(
        "limit_sum", "sympy",
        "limit(f + g, x, a) = limit(f, x, a) + limit(g, x, a)",
        "limit distributes over addition when both limits exist",
        ["expr", "expr", "symbol", "int"],
    )
    limit_product = _make(
        "limit_product", "sympy",
        "limit(f * g, x, a) = limit(f, x, a) * limit(g, x, a)",
        "limit distributes over multiplication when both limits exist",
        ["expr", "expr", "symbol", "int"],
    )

    # ── matrix algebra ────────────────────────────────────────────
    matrix_mul_assoc = _make(
        "matrix_mul_assoc", "sympy",
        "(A * B) * C = A * (B * C)",
        "matrix multiplication is associative",
        ["matrix", "matrix", "matrix"],
    )
    matrix_inv = _make(
        "matrix_inv", "sympy",
        "A * A.inv() = eye(n) when A is invertible",
        "matrix times its inverse is identity",
        ["invertible_matrix"],
    )
    matrix_det_product = _make(
        "matrix_det_product", "sympy",
        "det(A * B) = det(A) * det(B)",
        "determinant of product equals product of determinants",
        ["square_matrix", "square_matrix"],
    )
    matrix_transpose_product = _make(
        "matrix_transpose_product", "sympy",
        "(A * B).T = B.T * A.T",
        "transpose reverses product order",
        ["matrix", "matrix"],
    )

    # ── series ────────────────────────────────────────────────────
    series_exp = _make(
        "series_exp", "sympy",
        "series(exp(x), x, 0, n) truncates to sum(x**k/k!, k=0..n-1)",
        "Taylor series of exp around 0",
        ["symbol", "posint"],
    )
    series_add = _make(
        "series_add", "sympy",
        "series(f+g, x) = series(f, x) + series(g, x) up to order",
        "series distributes over addition",
        ["expr", "expr", "symbol"],
    )

    # ── assumptions ───────────────────────────────────────────────
    positive_square = _make(
        "positive_square", "sympy",
        "x**2 >= 0 when x is real",
        "square of a real number is non-negative",
        ["real"],
    )
    abs_nonneg = _make(
        "abs_nonneg", "sympy",
        "Abs(x) >= 0",
        "absolute value is non-negative",
        ["expr"],
    )
    abs_mul = _make(
        "abs_mul", "sympy",
        "Abs(a * b) = Abs(a) * Abs(b)",
        "absolute value distributes over multiplication",
        ["expr", "expr"],
    )

    @staticmethod
    def register_all(registry: AxiomRegistry) -> None:
        """Register every SymPy axiom into *registry*."""
        for attr in vars(SympyAxioms).values():
            if isinstance(attr, LibraryAxiom):
                if not registry.contains(attr.module, attr.name):
                    registry.register(attr)


# ═══════════════════════════════════════════════════════════════════
# NumPy Axioms
# ═══════════════════════════════════════════════════════════════════

@library("numpy")
class NumpyAxioms:
    """Axioms about NumPy array operations."""

    # ── linear algebra ────────────────────────────────────────────
    dot_assoc = _make(
        "dot_assoc", "numpy",
        "np.dot(np.dot(A, B), C) = np.dot(A, np.dot(B, C))",
        "dot product is associative for compatible shapes",
        ["matrix", "matrix", "matrix"],
    )
    dot_distribute = _make(
        "dot_distribute", "numpy",
        "np.dot(A, B + C) = np.dot(A, B) + np.dot(A, C)",
        "dot distributes over addition",
        ["matrix", "matrix", "matrix"],
    )
    transpose_involution = _make(
        "transpose_involution", "numpy",
        "A.T.T = A",
        "transpose is an involution",
        ["ndarray"],
    )
    transpose_product = _make(
        "transpose_product", "numpy",
        "(A @ B).T = B.T @ A.T",
        "transpose reverses matrix product",
        ["matrix", "matrix"],
    )
    matmul_shape = _make(
        "matmul_shape", "numpy",
        "(A @ B).shape = (A.shape[0], B.shape[1]) for 2-d arrays",
        "matmul output shape follows inner-dimension rule",
        ["matrix", "matrix"],
    )

    # ── element-wise identities ───────────────────────────────────
    zeros_identity = _make(
        "zeros_identity", "numpy",
        "np.zeros(n) + x = x",
        "zero array is additive identity (broadcast)",
        ["ndarray"],
    )
    ones_scaling = _make(
        "ones_scaling", "numpy",
        "np.ones(n) * x = x",
        "ones array is multiplicative identity (broadcast)",
        ["ndarray"],
    )
    add_commutative = _make(
        "add_commutative", "numpy",
        "A + B = B + A",
        "element-wise addition is commutative",
        ["ndarray", "ndarray"],
    )
    mul_commutative = _make(
        "mul_commutative", "numpy",
        "A * B = B * A",
        "element-wise multiplication is commutative",
        ["ndarray", "ndarray"],
    )

    # ── shape rules ───────────────────────────────────────────────
    broadcast_shape = _make(
        "broadcast_shape", "numpy",
        "broadcast rules: trailing dims must match or be 1",
        "NumPy broadcasting shape compatibility rules",
    )
    reshape_size = _make(
        "reshape_size", "numpy",
        "A.reshape(s).size == A.size",
        "reshape preserves total element count",
        ["ndarray", "shape"],
    )
    concatenate_len = _make(
        "concatenate_len", "numpy",
        "np.concatenate([A, B], axis=k).shape[k] = A.shape[k] + B.shape[k]",
        "concatenation adds lengths along the concat axis",
        ["ndarray", "ndarray"],
    )

    # ── reductions ────────────────────────────────────────────────
    sum_zeros = _make(
        "sum_zeros", "numpy",
        "np.sum(np.zeros(n)) == 0",
        "sum of zeros is zero",
        ["posint"],
    )
    sum_add = _make(
        "sum_add", "numpy",
        "np.sum(A + B) = np.sum(A) + np.sum(B)",
        "sum distributes over element-wise addition",
        ["ndarray", "ndarray"],
    )
    max_ge_mean = _make(
        "max_ge_mean", "numpy",
        "np.max(A) >= np.mean(A) when A is non-empty",
        "maximum is at least as large as the mean",
        ["nonempty_ndarray"],
    )
    min_le_mean = _make(
        "min_le_mean", "numpy",
        "np.min(A) <= np.mean(A) when A is non-empty",
        "minimum is at most as large as the mean",
        ["nonempty_ndarray"],
    )

    # ── dtype / copying ───────────────────────────────────────────
    copy_equal = _make(
        "copy_equal", "numpy",
        "np.array_equal(A, A.copy())",
        "copy produces an equal array",
        ["ndarray"],
    )
    astype_roundtrip = _make(
        "astype_roundtrip", "numpy",
        "A.astype(float).astype(int) may lose precision but is defined",
        "dtype casting is well-defined",
        ["ndarray"],
    )
    eye_matmul = _make(
        "eye_matmul", "numpy",
        "np.eye(n) @ A = A for A with n rows",
        "identity matrix is the left identity for matmul",
        ["posint", "matrix"],
    )

    @staticmethod
    def register_all(registry: AxiomRegistry) -> None:
        """Register every NumPy axiom into *registry*."""
        for attr in vars(NumpyAxioms).values():
            if isinstance(attr, LibraryAxiom):
                if not registry.contains(attr.module, attr.name):
                    registry.register(attr)


# ═══════════════════════════════════════════════════════════════════
# PyTorch Axioms
# ═══════════════════════════════════════════════════════════════════

@library("torch")
class TorchAxioms:
    """Axioms about PyTorch tensor operations and autograd."""

    # ── tensor shape ──────────────────────────────────────────────
    tensor_shape_matmul = _make(
        "tensor_shape_matmul", "torch",
        "torch.matmul(A, B).shape = (*batch, A.shape[-2], B.shape[-1])",
        "matmul follows batched inner-dimension rule",
        ["tensor", "tensor"],
    )
    tensor_shape_add = _make(
        "tensor_shape_add", "torch",
        "(A + B).shape follows broadcasting rules",
        "addition broadcasts following NumPy rules",
        ["tensor", "tensor"],
    )
    tensor_shape_cat = _make(
        "tensor_shape_cat", "torch",
        "torch.cat(ts, dim=d).shape[d] = sum(t.shape[d] for t in ts)",
        "cat concatenates along the given dimension",
        ["tensor_list", "int"],
    )
    tensor_shape_stack = _make(
        "tensor_shape_stack", "torch",
        "torch.stack(ts, dim=d).shape[d] = len(ts)",
        "stack creates a new dimension",
        ["tensor_list", "int"],
    )

    # ── dtype ─────────────────────────────────────────────────────
    tensor_dtype_preserve = _make(
        "tensor_dtype_preserve", "torch",
        "result dtype follows PyTorch promotion rules",
        "dtype promotion is consistent and deterministic",
        ["tensor", "tensor"],
    )
    tensor_to_device = _make(
        "tensor_to_device", "torch",
        "x.to(device).device == device",
        "to() moves tensor to the specified device",
        ["tensor", "device"],
    )

    # ── autograd ──────────────────────────────────────────────────
    grad_linear = _make(
        "grad_linear", "torch",
        "grad(a*f + b*g) = a*grad(f) + b*grad(g)",
        "autograd is linear",
        ["scalar", "tensor", "scalar", "tensor"],
    )
    grad_chain = _make(
        "grad_chain", "torch",
        "grad(f(g(x))) = grad(f)(g(x)) * grad(g)(x)",
        "autograd implements the chain rule",
        ["differentiable", "differentiable", "tensor"],
    )
    grad_detach = _make(
        "grad_detach", "torch",
        "x.detach() stops gradient flow",
        "detach severs the computation graph",
        ["tensor"],
    )
    no_grad_context = _make(
        "no_grad_context", "torch",
        "inside torch.no_grad(), requires_grad is False for new tensors",
        "no_grad context disables gradient tracking",
    )
    grad_accumulate = _make(
        "grad_accumulate", "torch",
        "loss.backward() accumulates into .grad (does not replace)",
        "gradients accumulate unless zeroed explicitly",
        ["tensor"],
    )

    # ── module ────────────────────────────────────────────────────
    module_forward = _make(
        "module_forward", "torch",
        "module(x) calls module.forward(x)",
        "__call__ dispatches to forward with hooks",
        ["module", "tensor"],
    )
    parameter_update = _make(
        "parameter_update", "torch",
        "after optimizer.step(), params change by -lr * grad (for SGD)",
        "SGD updates parameters by -lr * gradient",
        ["optimizer"],
    )
    module_eval_mode = _make(
        "module_eval_mode", "torch",
        "module.eval() disables dropout and uses running stats for batchnorm",
        "eval mode changes behaviour of dropout and batchnorm",
        ["module"],
    )
    module_parameters = _make(
        "module_parameters", "torch",
        "list(module.parameters()) returns all learnable parameters",
        "parameters() iterates over all Parameter tensors",
        ["module"],
    )

    # ── numerical ─────────────────────────────────────────────────
    softmax_sum_one = _make(
        "softmax_sum_one", "torch",
        "torch.softmax(x, dim=d).sum(dim=d) ≈ 1.0",
        "softmax outputs sum to 1 along the specified dim",
        ["tensor", "int"],
    )
    relu_nonneg = _make(
        "relu_nonneg", "torch",
        "torch.relu(x) >= 0",
        "ReLU outputs are non-negative",
        ["tensor"],
    )
    sigmoid_range = _make(
        "sigmoid_range", "torch",
        "0 <= torch.sigmoid(x) <= 1",
        "sigmoid outputs lie in [0, 1]",
        ["tensor"],
    )
    log_softmax_le_zero = _make(
        "log_softmax_le_zero", "torch",
        "torch.log_softmax(x, dim=d) <= 0",
        "log-softmax outputs are non-positive",
        ["tensor", "int"],
    )
    batchnorm_mean_zero = _make(
        "batchnorm_mean_zero", "torch",
        "after BatchNorm, channel means ≈ 0 (in train mode)",
        "batch normalization centers activations",
        ["tensor"],
    )

    # ── loss ──────────────────────────────────────────────────────
    cross_entropy_nonneg = _make(
        "cross_entropy_nonneg", "torch",
        "F.cross_entropy(logits, target) >= 0",
        "cross-entropy loss is non-negative",
        ["tensor", "int_tensor"],
    )
    mse_nonneg = _make(
        "mse_nonneg", "torch",
        "F.mse_loss(pred, target) >= 0",
        "mean squared error is non-negative",
        ["tensor", "tensor"],
    )
    mse_zero_at_equal = _make(
        "mse_zero_at_equal", "torch",
        "F.mse_loss(x, x) == 0",
        "MSE is zero when prediction equals target",
        ["tensor"],
    )

    @staticmethod
    def register_all(registry: AxiomRegistry) -> None:
        """Register every PyTorch axiom into *registry*."""
        for attr in vars(TorchAxioms).values():
            if isinstance(attr, LibraryAxiom):
                if not registry.contains(attr.module, attr.name):
                    registry.register(attr)


# ═══════════════════════════════════════════════════════════════════
# Python Builtins Axioms
# ═══════════════════════════════════════════════════════════════════

@library("builtins")
class BuiltinAxioms:
    """Axioms about Python built-in types and functions."""

    # ── len ────────────────────────────────────────────────────────
    len_nonneg = _make(
        "len_nonneg", "builtins",
        "len(x) >= 0",
        "length is non-negative",
        ["list[int]"],
    )
    len_empty_list = _make(
        "len_empty_list", "builtins",
        "len([]) == 0",
        "empty list has length zero",
    )
    len_append = _make(
        "len_append", "builtins",
        "len(xs + [x]) == len(xs) + 1",
        "appending one element increments length by one",
        ["list[int]", "int"],
    )
    len_concat = _make(
        "len_concat", "builtins",
        "len(xs + ys) == len(xs) + len(ys)",
        "length distributes over list concatenation",
        ["list[int]", "list[int]"],
    )
    len_range = _make(
        "len_range", "builtins",
        "len(range(n)) == max(0, n)",
        "range length is max(0, n)",
        ["int"],
    )

    # ── sorted ────────────────────────────────────────────────────
    sorted_idempotent = _make(
        "sorted_idempotent", "builtins",
        "sorted(sorted(xs)) == sorted(xs)",
        "sorted is idempotent",
        ["list[int]"],
    )
    sorted_length = _make(
        "sorted_length", "builtins",
        "len(sorted(xs)) == len(xs)",
        "sorted preserves length",
        ["list[int]"],
    )
    sorted_elements = _make(
        "sorted_elements", "builtins",
        "set(sorted(xs)) == set(xs)",
        "sorted preserves elements",
        ["list[int]"],
    )
    sorted_ordered = _make(
        "sorted_ordered", "builtins",
        "all(sorted(xs)[i] <= sorted(xs)[i+1] for i in range(len(xs)-1))",
        "sorted output is in non-decreasing order",
        ["list[int]"],
    )

    # ── dict ──────────────────────────────────────────────────────
    dict_get_set = _make(
        "dict_get_set", "builtins",
        "d[k] after d[k] = v gives v",
        "dict __setitem__ then __getitem__ round-trips",
        ["str", "int"],
    )
    dict_del_absent = _make(
        "dict_del_absent", "builtins",
        "k not in d after del d[k]",
        "del removes the key from the dict",
        ["str"],
    )
    dict_len_set = _make(
        "dict_len_set", "builtins",
        "len(d) increases by at most 1 after d[k] = v",
        "setting a key adds at most one entry",
        ["str", "int"],
    )
    dict_keys_values = _make(
        "dict_keys_values", "builtins",
        "len(d.keys()) == len(d.values()) == len(d)",
        "keys and values have same length as dict",
    )

    # ── str ────────────────────────────────────────────────────────
    str_concat_assoc = _make(
        "str_concat_assoc", "builtins",
        "(a + b) + c == a + (b + c) for strings",
        "string concatenation is associative",
        ["str", "str", "str"],
    )
    str_concat_len = _make(
        "str_concat_len", "builtins",
        "len(a + b) == len(a) + len(b) for strings",
        "concatenation lengths add",
        ["str", "str"],
    )
    str_empty_identity = _make(
        "str_empty_identity", "builtins",
        'a + "" == "" + a == a',
        "empty string is the identity for concatenation",
        ["str"],
    )

    # ── isinstance / type ─────────────────────────────────────────
    isinstance_subclass = _make(
        "isinstance_subclass", "builtins",
        "isinstance(x, B) if isinstance(x, A) and issubclass(A, B)",
        "isinstance respects subclass hierarchy",
    )
    type_isinstance = _make(
        "type_isinstance", "builtins",
        "isinstance(x, type(x)) is True",
        "every object is an instance of its own type",
    )

    # ── range ──────────────────────────────────────────────────────
    range_len = _make(
        "range_len", "builtins",
        "len(range(n)) == max(0, n)",
        "range length equals max(0, n) for non-negative step",
        ["int"],
    )
    range_contains = _make(
        "range_contains", "builtins",
        "i in range(n) iff 0 <= i < n",
        "range membership check",
        ["int", "int"],
    )

    @staticmethod
    def register_all(registry: AxiomRegistry) -> None:
        """Register every builtin axiom into *registry*."""
        for attr in vars(BuiltinAxioms).values():
            if isinstance(attr, LibraryAxiom):
                if not registry.contains(attr.module, attr.name):
                    registry.register(attr)


# ═══════════════════════════════════════════════════════════════════
# Convenience: create a pre-loaded registry
# ═══════════════════════════════════════════════════════════════════

def default_registry() -> AxiomRegistry:
    """Return an :class:`AxiomRegistry` loaded with all built-in axiom sets."""
    reg = AxiomRegistry()
    SympyAxioms.register_all(reg)
    NumpyAxioms.register_all(reg)
    TorchAxioms.register_all(reg)
    BuiltinAxioms.register_all(reg)
    return reg


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Quick smoke test — run with ``python -m deppy.axioms.library_axioms``."""

    # 1. Registry basics
    reg = AxiomRegistry()
    assert len(reg) == 0

    SympyAxioms.register_all(reg)
    assert reg.contains("sympy", "expand_add")
    assert reg.lookup("sympy", "expand_add") is not None
    ax = reg.lookup("sympy", "expand_add")
    assert ax is not None
    assert ax.qualified_name == "sympy.expand_add"
    assert ax.statement == "expand(a + b) = expand(a) + expand(b)"
    sympy_count = len(reg.all_axioms("sympy"))
    assert sympy_count >= 28, f"Expected ≥28 sympy axioms, got {sympy_count}"

    # 2. Register remaining libraries
    NumpyAxioms.register_all(reg)
    TorchAxioms.register_all(reg)
    BuiltinAxioms.register_all(reg)

    assert "numpy" in reg.modules()
    assert "torch" in reg.modules()
    assert "builtins" in reg.modules()
    total = len(reg)
    assert total >= 90, f"Expected ≥90 total axioms, got {total}"

    # 3. default_registry helper
    reg2 = default_registry()
    assert len(reg2) == total

    # 4. Lookup missing axiom
    assert reg.lookup("sympy", "nonexistent") is None

    # 5. Duplicate registration raises
    duplicate_raised = False
    try:
        reg.register(SympyAxioms.expand_add)
    except ValueError:
        duplicate_raised = True
    assert duplicate_raised, "Expected ValueError for duplicate axiom"

    # 6. Unregister
    assert reg.unregister("sympy", "expand_add")
    assert not reg.contains("sympy", "expand_add")
    assert not reg.unregister("sympy", "expand_add")  # already gone

    # 7. Kernel integration
    kernel = ProofKernel()
    reg3 = default_registry()
    installed = reg3.install_into_kernel(kernel)
    assert installed == len(reg3)
    assert "sympy.diff_sum" in kernel.axiom_registry or "diff_sum" in kernel.axiom_registry

    # 8. to_invocation round-trip
    ax2 = reg3.lookup("numpy", "dot_assoc")
    assert ax2 is not None
    inv = ax2.to_invocation()
    assert isinstance(inv, AxiomInvocation)
    assert inv.name == "dot_assoc"
    assert inv.module == "numpy"

    # 9. Fingerprint stability
    ax3 = reg3.lookup("torch", "relu_nonneg")
    assert ax3 is not None
    fp1 = ax3.fingerprint()
    fp2 = ax3.fingerprint()
    assert fp1 == fp2

    # 10. Summary smoke
    summary = reg3.summary("builtins")
    assert "len_nonneg" in summary

    print(f"✓ All self-tests passed  ({total} axioms across {len(reg3.modules())} modules)")


if __name__ == "__main__":
    _self_test()
