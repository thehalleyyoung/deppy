"""Abstract interface for local solvers in the sheaf-descent verification kernel.

Defines the protocol that every solver backend must implement, along with the
core result/status types that flow back from the solver to the kernel.

The key types are:

- **SolverStatus**: Enum capturing the four possible outcomes of a check.
- **SolverResult**: Frozen dataclass bundling status, model, proof certificate,
  and timing information from a single ``check`` call.
- **LocalSolverInterface**: The protocol (structural subtyping) that any solver
  backend must satisfy -- ``check``, ``push``/``pop``, ``assert_formula``,
  ``get_model``.
- **SolverObligation**: A self-contained verification obligation ready for
  dispatch to a solver, carrying site metadata and trust level.

Design note: ``SolverResult`` deliberately carries an *opaque*
``proof_certificate`` (``Any``) so that different backends can attach their
own certificate formats without introducing a hard dependency here.  The
``proof_certificate`` module defines the concrete type.
"""

from __future__ import annotations

import enum
import hashlib
import time
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    ContextManager,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Protocol,
    Sequence,
    Set,
    Tuple,
    TypeVar,
    Union,
    runtime_checkable,
)

from deppy.core._protocols import SiteId, TrustLevel
from deppy.predicates.base import Predicate


# ═══════════════════════════════════════════════════════════════════════════════
# Solver status
# ═══════════════════════════════════════════════════════════════════════════════


class SolverStatus(enum.Enum):
    """Possible outcomes from a solver check."""

    SAT = "sat"
    """The formula is satisfiable; a model exists."""

    UNSAT = "unsat"
    """The formula is unsatisfiable; a proof certificate may exist."""

    UNKNOWN = "unknown"
    """The solver could not determine satisfiability (resource limits, etc.)."""

    TIMEOUT = "timeout"
    """The solver exceeded the configured time budget."""

    ERROR = "error"
    """An internal solver error occurred."""


# ═══════════════════════════════════════════════════════════════════════════════
# Solver result
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class SolverResult:
    """Immutable result of a single solver check.

    Attributes:
        status: The satisfiability outcome.
        model: If SAT, a mapping from variable names to concrete values.
        proof_certificate: If UNSAT, an optional proof certificate
            (format depends on the backend).
        time_ms: Wall-clock time in milliseconds spent in the solver.
        unsat_core: If UNSAT and supported, a minimal subset of asserted
            formulas that are unsatisfiable.
        statistics: Backend-specific solver statistics (conflicts, decisions, ...).
        explanation: Human-readable explanation of the result.
    """

    status: SolverStatus
    model: Optional[Dict[str, Any]] = None
    proof_certificate: Optional[Any] = None
    time_ms: float = 0.0
    unsat_core: Optional[List[Any]] = None
    statistics: Optional[Dict[str, Any]] = None
    explanation: str = ""

    @property
    def is_sat(self) -> bool:
        return self.status is SolverStatus.SAT

    @property
    def is_unsat(self) -> bool:
        return self.status is SolverStatus.UNSAT

    @property
    def is_definitive(self) -> bool:
        """True when the result is either SAT or UNSAT (no ambiguity)."""
        return self.status in {SolverStatus.SAT, SolverStatus.UNSAT}

    @property
    def is_error_or_timeout(self) -> bool:
        return self.status in {SolverStatus.TIMEOUT, SolverStatus.ERROR}


# ═══════════════════════════════════════════════════════════════════════════════
# Solver obligation
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class SolverObligation:
    """A verification obligation ready for dispatch to a solver.

    This is the solver-layer counterpart of the kernel's ``Obligation``.  It
    carries the formula (as a deppy ``Predicate``), the originating site, the
    required trust level, and optional context (e.g. enclosing assertions).

    Attributes:
        site_id: The observation site this obligation originates from.
        formula: The predicate to check for validity / satisfiability.
        trust_level: Minimum trust required for the result to be accepted.
        context: Extra assertions that are assumed true (the background theory).
        description: Human-readable label for diagnostics.
        timeout_ms: Per-obligation timeout override (0 = use solver default).
    """

    site_id: SiteId
    formula: Predicate
    trust_level: TrustLevel = TrustLevel.TRUSTED_AUTO
    context: Tuple[Predicate, ...] = ()
    description: str = ""
    timeout_ms: float = 0.0

    @property
    def context_list(self) -> List[Predicate]:
        return list(self.context)

    def with_context(self, *extra: Predicate) -> SolverObligation:
        """Return a new obligation with additional context predicates."""
        return SolverObligation(
            site_id=self.site_id,
            formula=self.formula,
            trust_level=self.trust_level,
            context=self.context + tuple(extra),
            description=self.description,
            timeout_ms=self.timeout_ms,
        )

    def with_timeout(self, timeout_ms: float) -> SolverObligation:
        """Return a copy with a different timeout."""
        return SolverObligation(
            site_id=self.site_id,
            formula=self.formula,
            trust_level=self.trust_level,
            context=self.context,
            description=self.description,
            timeout_ms=timeout_ms,
        )

    def formula_hash(self) -> str:
        """Content-based hash for caching."""
        h = hashlib.sha256()
        h.update(repr(self.formula).encode("utf-8"))
        for ctx in self.context:
            h.update(repr(ctx).encode("utf-8"))
        return h.hexdigest()


# ═══════════════════════════════════════════════════════════════════════════════
# Solver configuration
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class SolverConfig:
    """Configuration for a solver backend.

    Attributes:
        timeout_ms: Default per-query timeout in milliseconds.
        max_memory_mb: Maximum memory in megabytes (0 = unlimited).
        enable_proof_generation: Whether to request proof certificates.
        enable_unsat_core: Whether to request UNSAT cores.
        enable_model_completion: Whether to complete partial models.
        random_seed: Seed for deterministic solving (0 = non-deterministic).
        incremental: Whether to use incremental solving (push/pop).
    """

    timeout_ms: float = 5000.0
    max_memory_mb: int = 0
    enable_proof_generation: bool = False
    enable_unsat_core: bool = False
    enable_model_completion: bool = True
    random_seed: int = 0
    incremental: bool = True

    def effective_timeout(self, obligation: SolverObligation) -> float:
        """Return the timeout to use for an obligation (obligation-level overrides)."""
        if obligation.timeout_ms > 0:
            return obligation.timeout_ms
        return self.timeout_ms


# ═══════════════════════════════════════════════════════════════════════════════
# Local solver interface (protocol)
# ═══════════════════════════════════════════════════════════════════════════════


@runtime_checkable
class LocalSolverInterface(Protocol):
    """Protocol that every local solver backend must satisfy.

    A local solver handles obligations that belong to a single decidable
    fragment.  The ``FragmentDispatcher`` routes obligations to the appropriate
    ``LocalSolverInterface`` implementation.

    Lifecycle:

    1. Optionally call ``push()`` to create a backtracking point.
    2. Call ``assert_formula(phi)`` one or more times to add background
       assertions.
    3. Call ``check(obligation)`` to determine satisfiability.
    4. If SAT, call ``get_model()`` to retrieve a satisfying assignment.
    5. Call ``pop()`` to retract assertions back to the last ``push()``.
    """

    def check(self, obligation: SolverObligation) -> SolverResult:
        """Check whether the obligation's formula is satisfiable.

        Returns a ``SolverResult`` with status, optional model, and timing.
        """
        ...

    def push(self) -> None:
        """Create a backtracking point (assertion stack frame)."""
        ...

    def pop(self) -> None:
        """Retract assertions back to the most recent ``push()``."""
        ...

    def assert_formula(self, formula: Predicate) -> None:
        """Add a formula to the current assertion set."""
        ...

    def get_model(self) -> Dict[str, Any]:
        """Retrieve the model from the last SAT check.

        Raises ``RuntimeError`` if the last check was not SAT.
        """
        ...

    def reset(self) -> None:
        """Reset the solver to its initial state, clearing all assertions."""
        ...


# ═══════════════════════════════════════════════════════════════════════════════
# Validity checking helper
# ═══════════════════════════════════════════════════════════════════════════════


def check_validity(
    solver: LocalSolverInterface,
    obligation: SolverObligation,
) -> SolverResult:
    """Check whether the obligation's formula is *valid* (always true).

    Validity is checked by negating the formula and checking for
    unsatisfiability.  If the negation is UNSAT, the original formula is valid.

    Args:
        solver: The solver backend to use.
        obligation: The obligation whose formula should be checked for validity.

    Returns:
        A ``SolverResult`` where:
        - UNSAT means the original formula is VALID (tautology).
        - SAT means the original formula is INVALID (counterexample in model).
        - UNKNOWN/TIMEOUT propagated as-is.
    """
    from deppy.predicates.boolean import Not

    negated_formula = Not(obligation.formula)
    negated_obligation = SolverObligation(
        site_id=obligation.site_id,
        formula=negated_formula,
        trust_level=obligation.trust_level,
        context=obligation.context,
        description=f"validity check: {obligation.description}",
        timeout_ms=obligation.timeout_ms,
    )
    return solver.check(negated_obligation)


# ═══════════════════════════════════════════════════════════════════════════════
# Solver context manager
# ═══════════════════════════════════════════════════════════════════════════════


class SolverScope:
    """Context manager for push/pop scoping on a solver.

    Usage::

        with SolverScope(solver):
            solver.assert_formula(phi)
            result = solver.check(obligation)
        # Assertions from the block are now retracted.
    """

    __slots__ = ("_solver",)

    def __init__(self, solver: LocalSolverInterface) -> None:
        self._solver = solver

    def __enter__(self) -> LocalSolverInterface:
        self._solver.push()
        return self._solver

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        self._solver.pop()


# ═══════════════════════════════════════════════════════════════════════════════
# Solver statistics aggregation
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class SolverStatistics:
    """Aggregated statistics across multiple solver calls.

    Useful for profiling and reporting in the pipeline.
    """

    total_checks: int = 0
    sat_count: int = 0
    unsat_count: int = 0
    unknown_count: int = 0
    timeout_count: int = 0
    error_count: int = 0
    total_time_ms: float = 0.0
    cache_hits: int = 0
    cache_misses: int = 0

    def record(self, result: SolverResult) -> None:
        """Record a solver result into the running statistics."""
        self.total_checks += 1
        self.total_time_ms += result.time_ms
        if result.status is SolverStatus.SAT:
            self.sat_count += 1
        elif result.status is SolverStatus.UNSAT:
            self.unsat_count += 1
        elif result.status is SolverStatus.UNKNOWN:
            self.unknown_count += 1
        elif result.status is SolverStatus.TIMEOUT:
            self.timeout_count += 1
        elif result.status is SolverStatus.ERROR:
            self.error_count += 1

    @property
    def average_time_ms(self) -> float:
        if self.total_checks == 0:
            return 0.0
        return self.total_time_ms / self.total_checks

    @property
    def success_rate(self) -> float:
        """Fraction of checks that yielded a definitive answer."""
        if self.total_checks == 0:
            return 0.0
        return (self.sat_count + self.unsat_count) / self.total_checks

    def summary(self) -> Dict[str, Any]:
        return {
            "total_checks": self.total_checks,
            "sat": self.sat_count,
            "unsat": self.unsat_count,
            "unknown": self.unknown_count,
            "timeout": self.timeout_count,
            "error": self.error_count,
            "total_time_ms": round(self.total_time_ms, 2),
            "avg_time_ms": round(self.average_time_ms, 2),
            "success_rate": round(self.success_rate, 4),
            "cache_hits": self.cache_hits,
            "cache_misses": self.cache_misses,
        }


# ═══════════════════════════════════════════════════════════════════════════════
# Kernel ↔ Solver bridge helpers
# ═══════════════════════════════════════════════════════════════════════════════


def obligation_to_solver_obligation(
    kernel_obligation: Any,
) -> SolverObligation:
    """Convert a kernel ``Obligation`` to a ``SolverObligation``.

    This bridges the kernel protocol layer (``deppy.kernel._protocols.Obligation``)
    to the solver layer.  The kernel obligation's ``proposition`` field is expected
    to be a ``Predicate``; if it is not, a ``TypeError`` is raised.
    """
    from deppy.kernel._protocols import Obligation

    if not isinstance(kernel_obligation, Obligation):
        raise TypeError(
            f"Expected kernel Obligation, got {type(kernel_obligation).__name__}"
        )

    proposition = kernel_obligation.proposition
    if not isinstance(proposition, Predicate):
        raise TypeError(
            f"Obligation proposition must be a Predicate, "
            f"got {type(proposition).__name__}"
        )

    context_preds: List[Predicate] = []
    raw_context = kernel_obligation.context
    if isinstance(raw_context, dict):
        for key, val in raw_context.items():
            if isinstance(val, Predicate):
                context_preds.append(val)

    return SolverObligation(
        site_id=kernel_obligation.site_id,
        formula=proposition,
        trust_level=kernel_obligation.trust_required,
        context=tuple(context_preds),
        description=f"kernel obligation at {kernel_obligation.site_id}",
    )


def solver_result_to_verification_result(
    solver_result: SolverResult,
    kernel_obligation: Any,
) -> Any:
    """Convert a ``SolverResult`` back to a kernel ``VerificationResult``.

    Returns a ``deppy.kernel._protocols.VerificationResult`` with the
    appropriate status mapping.
    """
    from deppy.kernel._protocols import (
        Obligation,
        VerificationResult,
        VerificationStatus,
    )

    status_map = {
        SolverStatus.SAT: VerificationStatus.SAT,
        SolverStatus.UNSAT: VerificationStatus.UNSAT,
        SolverStatus.UNKNOWN: VerificationStatus.UNKNOWN,
        SolverStatus.TIMEOUT: VerificationStatus.TIMEOUT,
        SolverStatus.ERROR: VerificationStatus.UNKNOWN,
    }

    return VerificationResult(
        status=status_map[solver_result.status],
        obligation=kernel_obligation,
        model=solver_result.model,
        unsat_core=solver_result.unsat_core,
        proof_term=solver_result.proof_certificate,
        elapsed_ms=solver_result.time_ms,
    )
