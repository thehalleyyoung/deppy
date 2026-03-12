"""Z3 solver backend for deppy verification conditions.

Wraps the Z3 SMT solver behind the ``LocalSolverInterface`` protocol,
providing push/pop context management, timeout handling, model extraction,
proof certificate generation, and UNSAT-core computation.

The backend lazily imports Z3 so that the rest of deppy remains usable
when Z3 is not installed.  If Z3 is unavailable and a call is made, the
backend returns ``SolverStatus.ERROR`` with an explanatory message.

Architecture
------------
::

    SolverObligation
        |
        v
    Z3Encoder  ──>  z3.ExprRef
        |
        v
    z3.Solver.check()
        |
        v
    Z3Decoder  ──>  SolverResult / CounterExample

Usage::

    from deppy.solver.z3_backend import Z3Backend
    from deppy.solver.solver_interface import SolverObligation, SolverConfig

    backend = Z3Backend(config=SolverConfig(timeout_ms=3000))
    result = backend.check(obligation)
    if result.is_sat:
        model = backend.get_model()
"""

from __future__ import annotations

import logging
import time
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Set,
    Tuple,
)

from deppy.predicates.base import Predicate
from deppy.solver.solver_interface import (
    LocalSolverInterface,
    SolverConfig,
    SolverObligation,
    SolverResult,
    SolverStatus,
)

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Lazy Z3 import
# ---------------------------------------------------------------------------

_z3: Any = None
_z3_available: Optional[bool] = None


def _try_import_z3() -> Tuple[Any, bool]:
    """Attempt to import z3.  Returns (module_or_None, available)."""
    global _z3, _z3_available
    if _z3_available is not None:
        return _z3, _z3_available
    try:
        import z3 as z3_mod
        _z3 = z3_mod
        _z3_available = True
        return _z3, True
    except ImportError:
        _z3 = None
        _z3_available = False
        return None, False


def z3_available() -> bool:
    """Check whether the Z3 solver is available."""
    _, avail = _try_import_z3()
    return avail


# ---------------------------------------------------------------------------
# Error result helpers
# ---------------------------------------------------------------------------


def _error_result(msg: str, time_ms: float = 0.0) -> SolverResult:
    return SolverResult(
        status=SolverStatus.ERROR,
        explanation=msg,
        time_ms=time_ms,
    )


def _z3_not_available_result() -> SolverResult:
    return _error_result(
        "Z3 is not installed.  Install with: pip install z3-solver"
    )


# ---------------------------------------------------------------------------
# Z3 Backend
# ---------------------------------------------------------------------------


class Z3Backend:
    """Z3 solver backend implementing ``LocalSolverInterface``.

    This class manages a single Z3 solver instance with push/pop
    stack management, timeout configuration, and model extraction.

    Parameters:
        config: Solver configuration (timeout, proof generation, etc.).

    Note:
        Although this class does not inherit from ``LocalSolverInterface``
        (it is a protocol / structural type), it satisfies the protocol and
        is runtime-checkable as such.
    """

    def __init__(self, config: Optional[SolverConfig] = None) -> None:
        self._config = config or SolverConfig()
        self._z3_mod: Any = None
        self._solver: Any = None
        self._encoder: Any = None
        self._decoder: Any = None
        self._last_model: Any = None
        self._last_status: Optional[SolverStatus] = None
        self._assertion_count: int = 0
        self._push_depth: int = 0
        self._initialized: bool = False

    # -------------------------------------------------------------------
    # Lazy initialization
    # -------------------------------------------------------------------

    def _ensure_init(self) -> bool:
        """Initialize Z3 solver on first use.  Returns True if Z3 is available."""
        if self._initialized:
            return self._z3_mod is not None
        self._initialized = True
        z3_mod, available = _try_import_z3()
        if not available:
            logger.warning("Z3 is not available; Z3Backend will return ERROR results")
            return False

        self._z3_mod = z3_mod
        self._solver = z3_mod.Solver()

        # Apply configuration
        self._apply_config()

        # Create encoder and decoder
        from deppy.solver.z3_encoder import Z3Encoder, VariableEnvironment
        from deppy.solver.z3_decoder import Z3Decoder

        self._encoder = Z3Encoder()
        self._decoder = Z3Decoder()

        return True

    def _apply_config(self) -> None:
        """Apply solver configuration to the Z3 solver instance."""
        if self._solver is None or self._z3_mod is None:
            return

        z3 = self._z3_mod
        solver = self._solver

        # Timeout
        timeout_ms = int(self._config.timeout_ms)
        if timeout_ms > 0:
            solver.set("timeout", timeout_ms)

        # Random seed
        if self._config.random_seed > 0:
            solver.set("random_seed", self._config.random_seed)

        # Proof generation
        if self._config.enable_proof_generation:
            z3.set_param("proof", True)

        # UNSAT core tracking
        if self._config.enable_unsat_core:
            solver.set("unsat_core", True)

    # -------------------------------------------------------------------
    # LocalSolverInterface implementation
    # -------------------------------------------------------------------

    def check(self, obligation: SolverObligation) -> SolverResult:
        """Check whether the obligation's formula is satisfiable.

        Workflow:
        1. Push a new scope.
        2. Assert context predicates.
        3. Assert the obligation formula.
        4. Call z3.Solver.check().
        5. Extract model/unsat-core as appropriate.
        6. Pop scope (cleanup).

        Returns a ``SolverResult`` with status, model, and timing.
        """
        if not self._ensure_init():
            return _z3_not_available_result()

        z3 = self._z3_mod
        solver = self._solver
        encoder = self._encoder

        t_start = time.perf_counter()

        # Per-obligation timeout
        effective_timeout = self._config.effective_timeout(obligation)
        if effective_timeout > 0 and effective_timeout != self._config.timeout_ms:
            solver.set("timeout", int(effective_timeout))

        # Push scope for this check
        solver.push()
        self._push_depth += 1

        try:
            # Assert context
            for ctx_pred in obligation.context:
                try:
                    z3_ctx = encoder.encode_predicate(ctx_pred)
                    solver.add(z3_ctx)
                except Exception as e:
                    logger.warning("Failed to encode context predicate: %s", e)

            # Assert the main formula
            try:
                z3_formula = encoder.encode_predicate(obligation.formula)
                solver.add(z3_formula)
            except Exception as e:
                elapsed = (time.perf_counter() - t_start) * 1000
                return _error_result(
                    f"Failed to encode obligation formula: {e}",
                    time_ms=elapsed,
                )

            # Check satisfiability
            try:
                z3_result = solver.check()
            except Exception as e:
                elapsed = (time.perf_counter() - t_start) * 1000
                return _error_result(
                    f"Z3 solver error: {e}",
                    time_ms=elapsed,
                )

            elapsed = (time.perf_counter() - t_start) * 1000

            # Interpret result
            if z3_result == z3.sat:
                model = solver.model()
                self._last_model = model
                self._last_status = SolverStatus.SAT

                # Decode model to Python values
                decoded = self._decoder.decode_model(model, encoder.env)

                # Build solver statistics
                stats = self._extract_statistics()

                return SolverResult(
                    status=SolverStatus.SAT,
                    model=decoded,
                    time_ms=elapsed,
                    statistics=stats,
                    explanation=f"Satisfiable with {len(decoded)} variable(s)",
                )

            elif z3_result == z3.unsat:
                self._last_model = None
                self._last_status = SolverStatus.UNSAT

                # Extract UNSAT core if enabled
                unsat_core = None
                if self._config.enable_unsat_core:
                    try:
                        raw_core = solver.unsat_core()
                        unsat_core = [str(c) for c in raw_core]
                    except Exception:
                        pass

                # Extract proof if enabled
                proof_cert = None
                if self._config.enable_proof_generation:
                    try:
                        proof_cert = solver.proof()
                    except Exception:
                        pass

                stats = self._extract_statistics()

                return SolverResult(
                    status=SolverStatus.UNSAT,
                    unsat_core=unsat_core,
                    proof_certificate=proof_cert,
                    time_ms=elapsed,
                    statistics=stats,
                    explanation="Unsatisfiable",
                )

            else:
                # z3.unknown
                self._last_model = None
                self._last_status = SolverStatus.UNKNOWN
                reason = str(solver.reason_unknown())

                # Distinguish timeout from other unknowns
                if "timeout" in reason.lower():
                    return SolverResult(
                        status=SolverStatus.TIMEOUT,
                        time_ms=elapsed,
                        explanation=f"Solver timeout: {reason}",
                    )

                return SolverResult(
                    status=SolverStatus.UNKNOWN,
                    time_ms=elapsed,
                    explanation=f"Unknown: {reason}",
                )

        finally:
            # Pop the scope
            solver.pop()
            self._push_depth -= 1

            # Restore default timeout if we changed it
            if effective_timeout > 0 and effective_timeout != self._config.timeout_ms:
                solver.set("timeout", int(self._config.timeout_ms))

    def push(self) -> None:
        """Create a backtracking point on the Z3 solver."""
        if not self._ensure_init():
            return
        self._solver.push()
        self._push_depth += 1

    def pop(self) -> None:
        """Retract to the most recent push point."""
        if not self._ensure_init():
            return
        if self._push_depth > 0:
            self._solver.pop()
            self._push_depth -= 1
        else:
            logger.warning("pop() called without matching push()")

    def assert_formula(self, formula: Predicate) -> None:
        """Assert a formula into the solver's current scope."""
        if not self._ensure_init():
            return
        try:
            z3_expr = self._encoder.encode_predicate(formula)
            self._solver.add(z3_expr)
            self._assertion_count += 1
        except Exception as e:
            logger.error("Failed to assert formula: %s", e)

    def get_model(self) -> Dict[str, Any]:
        """Retrieve the model from the last SAT check.

        Raises:
            RuntimeError: If the last check was not SAT.
        """
        if self._last_status is not SolverStatus.SAT:
            raise RuntimeError(
                f"get_model() called but last status was "
                f"{self._last_status}, not SAT"
            )
        if self._last_model is None:
            raise RuntimeError("No model available")
        return self._decoder.decode_model(self._last_model, self._encoder.env)

    def reset(self) -> None:
        """Reset the solver to its initial state."""
        if not self._ensure_init():
            return
        self._solver.reset()
        self._apply_config()
        self._last_model = None
        self._last_status = None
        self._assertion_count = 0
        self._push_depth = 0
        # Reset encoder environment
        if self._encoder is not None:
            self._encoder.env.clear()

    # -------------------------------------------------------------------
    # Extended API
    # -------------------------------------------------------------------

    def check_validity(self, obligation: SolverObligation) -> SolverResult:
        """Check if the obligation formula is *valid* (a tautology).

        Negates the formula and checks for UNSAT.  If the negation is UNSAT,
        the formula is valid.
        """
        from deppy.solver.solver_interface import check_validity
        return check_validity(self, obligation)

    def get_counterexample(
        self, obligation: Optional[SolverObligation] = None
    ) -> Any:
        """Get a ``CounterExample`` from the last SAT model.

        More informative than ``get_model()`` -- includes explanation
        and violated constraint identification.
        """
        if self._last_status is not SolverStatus.SAT:
            raise RuntimeError("get_counterexample() requires last status to be SAT")
        if self._last_model is None:
            raise RuntimeError("No model available")
        return self._decoder.decode_counterexample(
            self._last_model, self._encoder.env, obligation
        )

    def assert_predicate_list(self, predicates: List[Predicate]) -> int:
        """Assert a list of predicates.  Returns count of successfully asserted."""
        count = 0
        for pred in predicates:
            try:
                self.assert_formula(pred)
                count += 1
            except Exception as e:
                logger.debug("Skipping predicate assertion: %s", e)
        return count

    def check_incremental(
        self,
        obligations: List[SolverObligation],
    ) -> List[SolverResult]:
        """Check a sequence of obligations incrementally.

        Each obligation shares the context of all previous context predicates.
        Uses push/pop to isolate each obligation's specific formula while
        retaining the accumulated context.
        """
        results: List[SolverResult] = []
        for obl in obligations:
            result = self.check(obl)
            results.append(result)
        return results

    @property
    def config(self) -> SolverConfig:
        return self._config

    @property
    def is_available(self) -> bool:
        """Check if Z3 is available without initializing."""
        return z3_available()

    @property
    def assertion_count(self) -> int:
        return self._assertion_count

    @property
    def push_depth(self) -> int:
        return self._push_depth

    # -------------------------------------------------------------------
    # Statistics extraction
    # -------------------------------------------------------------------

    def _extract_statistics(self) -> Optional[Dict[str, Any]]:
        """Extract solver statistics from Z3."""
        if self._solver is None:
            return None
        try:
            stats = self._solver.statistics()
            result: Dict[str, Any] = {}
            for key in stats.keys():
                try:
                    result[key] = stats.get_key_value(key)
                except Exception:
                    pass
            return result if result else None
        except Exception:
            return None

    # -------------------------------------------------------------------
    # String representation
    # -------------------------------------------------------------------

    def __repr__(self) -> str:
        avail = "available" if z3_available() else "not available"
        return (
            f"Z3Backend({avail}, timeout={self._config.timeout_ms}ms, "
            f"assertions={self._assertion_count}, depth={self._push_depth})"
        )


# ---------------------------------------------------------------------------
# Z3 Stub Backend (when Z3 is not installed)
# ---------------------------------------------------------------------------


class Z3StubBackend:
    """Stub backend that returns ERROR results when Z3 is not installed.

    This allows the rest of the system to reference a Z3 backend type
    without hard-failing at import time.
    """

    def __init__(self, config: Optional[SolverConfig] = None) -> None:
        self._config = config or SolverConfig()

    def check(self, obligation: SolverObligation) -> SolverResult:
        return _z3_not_available_result()

    def push(self) -> None:
        pass

    def pop(self) -> None:
        pass

    def assert_formula(self, formula: Predicate) -> None:
        pass

    def get_model(self) -> Dict[str, Any]:
        raise RuntimeError("Z3 is not installed")

    def reset(self) -> None:
        pass

    def __repr__(self) -> str:
        return "Z3StubBackend(z3 not available)"


# ---------------------------------------------------------------------------
# Factory
# ---------------------------------------------------------------------------


def create_z3_backend(
    config: Optional[SolverConfig] = None,
) -> Z3Backend | Z3StubBackend:
    """Create a Z3 backend, falling back to the stub if Z3 is unavailable.

    This is the recommended entry point for creating Z3 backends.

    Returns:
        A ``Z3Backend`` if Z3 is installed, otherwise a ``Z3StubBackend``.
    """
    if z3_available():
        return Z3Backend(config=config)
    logger.info("Z3 not available; using stub backend")
    return Z3StubBackend(config=config)


# ---------------------------------------------------------------------------
# Quick check utility
# ---------------------------------------------------------------------------


def quick_check(
    formula: Predicate,
    context: Optional[List[Predicate]] = None,
    timeout_ms: float = 2000.0,
) -> SolverResult:
    """One-shot satisfiability check without creating a persistent backend.

    Useful for quick checks in interactive or testing contexts.

    Args:
        formula: The predicate to check for satisfiability.
        context: Optional list of context predicates (assumed true).
        timeout_ms: Timeout in milliseconds.

    Returns:
        A ``SolverResult``.
    """
    from deppy.core._protocols import SiteId, SiteKind

    config = SolverConfig(timeout_ms=timeout_ms)
    backend = create_z3_backend(config=config)

    site_id = SiteId(kind=SiteKind.PROOF, name="quick_check")
    obl = SolverObligation(
        site_id=site_id,
        formula=formula,
        context=tuple(context) if context else (),
    )
    return backend.check(obl)
