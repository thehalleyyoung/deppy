"""Table-driven solver for finite-domain checks.

Many verification conditions in deppy's sheaf-descent system involve
finite-domain lookups:

- **Device compatibility**: Can a CUDA tensor interoperate with a CPU tensor?
- **Dtype promotion**: What is the result dtype of ``float32 + int64``?
- **Framework compatibility**: Can a PyTorch tensor be passed where a
  NumPy array is expected?

These are not worth sending to Z3.  Instead, the ``TableSolver`` maintains
compatibility and promotion tables and resolves checks by direct lookup.

Implements ``LocalSolverInterface``.
"""

from __future__ import annotations

import logging
import time
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Set,
    Tuple,
)

from deppy.predicates.base import Predicate, Var, StrLit
from deppy.solver.solver_interface import (
    LocalSolverInterface,
    SolverObligation,
    SolverResult,
    SolverStatus,
)

logger = logging.getLogger(__name__)


# ═══════════════════════════════════════════════════════════════════════════════
# Compatibility tables
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class CompatibilityTable:
    """A frozen lookup table for pairwise compatibility checks.

    Entries are (left, right) -> bool, indicating whether the combination
    is compatible.

    Attributes:
        name: Human-readable name of the table.
        entries: Mapping from (left, right) string pairs to compatibility.
        symmetric: Whether compatibility is symmetric (a,b) == (b,a).
    """

    name: str
    entries: Tuple[Tuple[Tuple[str, str], bool], ...] = ()
    symmetric: bool = True

    def check(self, left: str, right: str) -> Optional[bool]:
        """Look up whether (left, right) is compatible.

        Returns None if the pair is not in the table.
        """
        for (l, r), compat in self.entries:
            if l == left and r == right:
                return compat
            if self.symmetric and l == right and r == left:
                return compat
        return None

    def all_values(self) -> Set[str]:
        """Return all values mentioned in the table."""
        values: Set[str] = set()
        for (l, r), _ in self.entries:
            values.add(l)
            values.add(r)
        return values


@dataclass(frozen=True)
class PromotionTable:
    """Lookup table for type/dtype promotion.

    Entries are (left, right) -> result, giving the promoted type.

    Attributes:
        name: Human-readable name.
        entries: Mapping from (left, right) to promoted result.
    """

    name: str
    entries: Tuple[Tuple[Tuple[str, str], str], ...] = ()
    symmetric: bool = True

    def promote(self, left: str, right: str) -> Optional[str]:
        """Look up the promoted type for (left, right).

        Returns None if the pair is not in the table.
        """
        for (l, r), result in self.entries:
            if l == left and r == right:
                return result
            if self.symmetric and l == right and r == left:
                return result
        return None


# ═══════════════════════════════════════════════════════════════════════════════
# Built-in tables
# ═══════════════════════════════════════════════════════════════════════════════


def _build_device_compat_table() -> CompatibilityTable:
    """Build the default device compatibility table."""
    entries: List[Tuple[Tuple[str, str], bool]] = []

    devices = ["cpu", "cuda", "cuda:0", "cuda:1", "mps", "xla", "meta"]

    # Same device is always compatible
    for d in devices:
        entries.append(((d, d), True))

    # cpu is compatible with everything for data transfer
    for d in devices:
        if d != "cpu":
            entries.append(((d, "cpu"), True))

    # Different GPU devices are incompatible without explicit transfer
    entries.append((("cuda:0", "cuda:1"), False))
    entries.append((("cuda", "mps"), False))
    entries.append((("cuda", "xla"), False))
    entries.append((("mps", "xla"), False))

    # meta is compatible with everything (shape-only)
    for d in devices:
        if d != "meta":
            entries.append((("meta", d), True))

    return CompatibilityTable(
        name="device_compatibility",
        entries=tuple(entries),
        symmetric=True,
    )


def _build_dtype_promotion_table() -> PromotionTable:
    """Build the default dtype promotion table (NumPy/PyTorch rules)."""
    entries: List[Tuple[Tuple[str, str], str]] = []

    # Integer promotions
    int_dtypes = ["bool", "int8", "int16", "int32", "int64",
                  "uint8", "uint16", "uint32", "uint64"]
    float_dtypes = ["float16", "bfloat16", "float32", "float64"]
    complex_dtypes = ["complex64", "complex128"]

    int_rank = {d: i for i, d in enumerate(int_dtypes)}
    float_rank = {d: i for i, d in enumerate(float_dtypes)}

    # Int + int -> wider int
    for a in int_dtypes:
        for b in int_dtypes:
            ra, rb = int_rank[a], int_rank[b]
            result = a if ra >= rb else b
            entries.append(((a, b), result))

    # Float + float -> wider float
    for a in float_dtypes:
        for b in float_dtypes:
            ra, rb = float_rank[a], float_rank[b]
            result = a if ra >= rb else b
            entries.append(((a, b), result))

    # Int + float -> float (at least float32)
    for a in int_dtypes:
        for b in float_dtypes:
            entries.append(((a, b), b if float_rank[b] >= 2 else "float32"))

    # Float + complex -> complex
    for a in float_dtypes:
        entries.append(((a, "complex64"), "complex64"))
        entries.append(((a, "complex128"), "complex128"))

    # Complex + complex
    entries.append((("complex64", "complex128"), "complex128"))
    entries.append((("complex64", "complex64"), "complex64"))
    entries.append((("complex128", "complex128"), "complex128"))

    return PromotionTable(
        name="dtype_promotion",
        entries=tuple(entries),
        symmetric=True,
    )


def _build_dtype_compat_table() -> CompatibilityTable:
    """Build dtype compatibility table (which dtypes can interop)."""
    entries: List[Tuple[Tuple[str, str], bool]] = []

    all_dtypes = [
        "bool", "int8", "int16", "int32", "int64",
        "uint8", "uint16", "uint32", "uint64",
        "float16", "bfloat16", "float32", "float64",
        "complex64", "complex128",
    ]

    # All numeric dtypes are mutually compatible (with promotion)
    for a in all_dtypes:
        for b in all_dtypes:
            entries.append(((a, b), True))

    # String dtypes are only compatible with themselves
    entries.append((("string", "string"), True))
    for d in all_dtypes:
        entries.append(((d, "string"), False))

    return CompatibilityTable(
        name="dtype_compatibility",
        entries=tuple(entries),
        symmetric=True,
    )


def _build_framework_compat_table() -> CompatibilityTable:
    """Build framework compatibility table."""
    entries: List[Tuple[Tuple[str, str], bool]] = []

    frameworks = ["torch", "numpy", "jax", "tensorflow"]

    # Same framework always compatible
    for f in frameworks:
        entries.append(((f, f), True))

    # numpy is interoperable with most frameworks
    for f in frameworks:
        if f != "numpy":
            entries.append((("numpy", f), True))

    # torch and jax can interoperate via DLPack
    entries.append((("torch", "jax"), True))

    # tensorflow is less interoperable
    entries.append((("torch", "tensorflow"), False))
    entries.append((("jax", "tensorflow"), False))

    return CompatibilityTable(
        name="framework_compatibility",
        entries=tuple(entries),
        symmetric=True,
    )


# Default table instances
DEVICE_COMPAT = _build_device_compat_table()
DTYPE_PROMOTION = _build_dtype_promotion_table()
DTYPE_COMPAT = _build_dtype_compat_table()
FRAMEWORK_COMPAT = _build_framework_compat_table()


# ═══════════════════════════════════════════════════════════════════════════════
# Table Solver
# ═══════════════════════════════════════════════════════════════════════════════


class TableSolver:
    """Table-driven solver for finite-domain verification conditions.

    Resolves device/dtype/framework compatibility checks by direct
    table lookup.  For obligations that do not match any known table
    pattern, returns UNKNOWN.

    Implements ``LocalSolverInterface``.
    """

    def __init__(
        self,
        device_table: Optional[CompatibilityTable] = None,
        dtype_promo_table: Optional[PromotionTable] = None,
        dtype_compat_table: Optional[CompatibilityTable] = None,
        framework_table: Optional[CompatibilityTable] = None,
    ) -> None:
        self._device_table = device_table or DEVICE_COMPAT
        self._dtype_promo = dtype_promo_table or DTYPE_PROMOTION
        self._dtype_compat = dtype_compat_table or DTYPE_COMPAT
        self._framework_table = framework_table or FRAMEWORK_COMPAT
        self._asserted: List[Predicate] = []
        self._stack: List[List[Predicate]] = []

    def check(self, obligation: SolverObligation) -> SolverResult:
        t_start = time.perf_counter()

        # Try to match the obligation against known patterns
        result = self._try_resolve(obligation.formula)
        if result is not None:
            elapsed = (time.perf_counter() - t_start) * 1000
            return result._replace_time(elapsed)

        # Try resolving context + formula together
        for ctx in obligation.context:
            result = self._try_resolve(ctx)
            if result is not None and result.status == SolverStatus.UNSAT:
                elapsed = (time.perf_counter() - t_start) * 1000
                return SolverResult(
                    status=SolverStatus.UNSAT,
                    time_ms=elapsed,
                    explanation="Context predicate is unsatisfiable by table lookup",
                )

        elapsed = (time.perf_counter() - t_start) * 1000
        return SolverResult(
            status=SolverStatus.UNKNOWN,
            time_ms=elapsed,
            explanation="No matching table pattern",
        )

    def push(self) -> None:
        self._stack.append(list(self._asserted))

    def pop(self) -> None:
        if self._stack:
            self._asserted = self._stack.pop()
        else:
            self._asserted.clear()

    def assert_formula(self, formula: Predicate) -> None:
        self._asserted.append(formula)

    def get_model(self) -> Dict[str, Any]:
        return {}

    def reset(self) -> None:
        self._asserted.clear()
        self._stack.clear()

    # -------------------------------------------------------------------
    # Pattern matching and resolution
    # -------------------------------------------------------------------

    def _try_resolve(self, pred: Predicate) -> Optional[_TableResult]:
        """Try to resolve a predicate using table lookup.

        Returns a ``_TableResult`` if resolved, None otherwise.
        """
        from deppy.predicates.tensor import DtypePred, DevicePred
        from deppy.predicates.nullability import IsNone, IsNotNone, IsInstance
        from deppy.predicates.arithmetic import Comparison
        from deppy.predicates.boolean import And, Not

        # DtypePred: check if the dtype is known
        if isinstance(pred, DtypePred):
            return self._resolve_dtype(pred)

        # DevicePred: check if the device is known
        if isinstance(pred, DevicePred):
            return self._resolve_device(pred)

        # IsInstance: check type against known types
        if isinstance(pred, IsInstance):
            return self._resolve_isinstance(pred)

        # IsNone / IsNotNone: trivially decidable
        if isinstance(pred, IsNone):
            return _TableResult(
                status=SolverStatus.SAT,
                model={"__is_none": True},
                explanation="IsNone is satisfiable (value can be None)",
            )
        if isinstance(pred, IsNotNone):
            return _TableResult(
                status=SolverStatus.SAT,
                model={"__is_none": False},
                explanation="IsNotNone is satisfiable (value can be non-None)",
            )

        # Equality comparison on string literals
        if isinstance(pred, Comparison) and pred.op == "==":
            if isinstance(pred.left, StrLit) and isinstance(pred.right, StrLit):
                if pred.left.value == pred.right.value:
                    return _TableResult(
                        status=SolverStatus.SAT,
                        model={},
                        explanation=f"String equality: {pred.left.value!r} == {pred.right.value!r}",
                    )
                else:
                    return _TableResult(
                        status=SolverStatus.UNSAT,
                        explanation=f"String inequality: {pred.left.value!r} != {pred.right.value!r}",
                    )

        # And: resolve each conjunct
        if isinstance(pred, And):
            for c in pred.conjuncts:
                result = self._try_resolve(c)
                if result is not None and result.status == SolverStatus.UNSAT:
                    return result
            return None

        return None

    def _resolve_dtype(self, pred: Any) -> Optional[_TableResult]:
        """Resolve a DtypePred against the dtype compatibility table."""
        dtype = pred.dtype if hasattr(pred, "dtype") else None
        if dtype is None:
            return None

        known_dtypes = self._dtype_compat.all_values()
        if dtype in known_dtypes:
            return _TableResult(
                status=SolverStatus.SAT,
                model={"dtype": dtype},
                explanation=f"Dtype {dtype!r} is a known dtype",
            )
        return _TableResult(
            status=SolverStatus.UNKNOWN,
            explanation=f"Dtype {dtype!r} not in compatibility table",
        )

    def _resolve_device(self, pred: Any) -> Optional[_TableResult]:
        """Resolve a DevicePred against the device compatibility table."""
        device = pred.device if hasattr(pred, "device") else None
        if device is None:
            return None

        known_devices = self._device_table.all_values()
        if device in known_devices:
            return _TableResult(
                status=SolverStatus.SAT,
                model={"device": device},
                explanation=f"Device {device!r} is a known device",
            )
        return _TableResult(
            status=SolverStatus.UNKNOWN,
            explanation=f"Device {device!r} not in compatibility table",
        )

    def _resolve_isinstance(self, pred: Any) -> Optional[_TableResult]:
        """Resolve isinstance checks for known types."""
        known_types = {
            "int", "float", "str", "bool", "bytes", "NoneType",
            "list", "dict", "tuple", "set", "frozenset",
        }
        type_name = pred.type_name if hasattr(pred, "type_name") else None
        if type_name in known_types:
            return _TableResult(
                status=SolverStatus.SAT,
                model={"__type": type_name},
                explanation=f"isinstance({type_name!r}) is satisfiable",
            )
        return None

    # -------------------------------------------------------------------
    # Table query helpers
    # -------------------------------------------------------------------

    def check_device_compat(self, device_a: str, device_b: str) -> Optional[bool]:
        """Check device compatibility directly."""
        return self._device_table.check(device_a, device_b)

    def get_dtype_promotion(self, dtype_a: str, dtype_b: str) -> Optional[str]:
        """Get the promoted dtype for two input dtypes."""
        return self._dtype_promo.promote(dtype_a, dtype_b)

    def check_dtype_compat(self, dtype_a: str, dtype_b: str) -> Optional[bool]:
        """Check dtype compatibility directly."""
        return self._dtype_compat.check(dtype_a, dtype_b)

    def check_framework_compat(self, fw_a: str, fw_b: str) -> Optional[bool]:
        """Check framework compatibility directly."""
        return self._framework_table.check(fw_a, fw_b)


# ═══════════════════════════════════════════════════════════════════════════════
# Internal result type
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class _TableResult:
    """Internal result type for table lookups."""
    status: SolverStatus = SolverStatus.UNKNOWN
    model: Optional[Dict[str, Any]] = None
    explanation: str = ""

    def _replace_time(self, time_ms: float) -> SolverResult:
        return SolverResult(
            status=self.status,
            model=self.model,
            time_ms=time_ms,
            explanation=self.explanation,
        )
