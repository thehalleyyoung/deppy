"""Route verification obligations to the appropriate solver by decidability fragment.

The ``FragmentDispatcher`` is the central routing layer in the solver subsystem.
It classifies each incoming ``SolverObligation`` by its decidability fragment
(QF_LIA, propositional, finite-domain, etc.) and dispatches it to the solver
backend that is most efficient for that fragment.

Routing strategy:

- **PROPOSITIONAL** -> ``BooleanSolver`` (lightweight DPLL / truth table).
- **FINITE_DOMAIN** -> ``TableSolver`` (lookup tables for device/dtype).
- **QF_LIA** -> ``ArithmeticSolver`` (interval-based, fallback to Z3).
- **QF_LRA, QF_BV, QF_AX, QF_UF, QF_NIA** -> ``Z3Backend`` (full SMT).
- **UNDECIDABLE** -> ``Z3Backend`` with timeout + best-effort.
- **UNKNOWN** -> ``Z3Backend`` (default fallback).

The dispatcher also supports a priority chain: if the first-choice solver
returns UNKNOWN, the dispatcher can escalate to a more powerful solver.
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Type,
)

from deppy.predicates.base import Predicate
from deppy.predicates.kinds import DecidabilityFragment, FragmentClassifier
from deppy.solver.solver_interface import (
    LocalSolverInterface,
    SolverConfig,
    SolverObligation,
    SolverResult,
    SolverStatus,
    SolverStatistics,
)

logger = logging.getLogger(__name__)


# ═══════════════════════════════════════════════════════════════════════════════
# Fragment classification for obligations
# ═══════════════════════════════════════════════════════════════════════════════


class ObligationClassifier:
    """Classifies a ``SolverObligation`` into a decidability fragment.

    Wraps the predicate-level ``FragmentClassifier`` and adds obligation-level
    heuristics (e.g., checking context predicates, trust-level escalation).
    """

    def __init__(self) -> None:
        self._pred_classifier = FragmentClassifier()

    def classify(self, obligation: SolverObligation) -> DecidabilityFragment:
        """Return the decidability fragment for the obligation's formula."""
        formula_frag = self._pred_classifier.classify(obligation.formula)

        # Also consider context predicates; the overall fragment is the join
        for ctx in obligation.context:
            ctx_frag = self._pred_classifier.classify(ctx)
            formula_frag = _join_fragment(formula_frag, ctx_frag)

        return formula_frag

    def is_decidable(self, obligation: SolverObligation) -> bool:
        """Check if the obligation falls within a decidable fragment."""
        frag = self.classify(obligation)
        return frag in _DECIDABLE_FRAGMENTS

    def classify_batch(
        self, obligations: Sequence[SolverObligation]
    ) -> Dict[DecidabilityFragment, List[SolverObligation]]:
        """Partition a batch of obligations by fragment.

        Returns a dict from fragment to list of obligations in that fragment.
        """
        result: Dict[DecidabilityFragment, List[SolverObligation]] = {}
        for obl in obligations:
            frag = self.classify(obl)
            result.setdefault(frag, []).append(obl)
        return result


# Fragment join / ordering (mirrors predicates.kinds but at the dispatcher level)

_FRAGMENT_STRENGTH: Dict[DecidabilityFragment, int] = {
    DecidabilityFragment.PROPOSITIONAL: 0,
    DecidabilityFragment.FINITE_DOMAIN: 1,
    DecidabilityFragment.QF_LIA: 2,
    DecidabilityFragment.QF_LRA: 3,
    DecidabilityFragment.QF_BV: 3,
    DecidabilityFragment.QF_UF: 3,
    DecidabilityFragment.QF_AX: 4,
    DecidabilityFragment.QF_NIA: 5,
    DecidabilityFragment.UNKNOWN: 6,
    DecidabilityFragment.UNDECIDABLE: 7,
}

_DECIDABLE_FRAGMENTS: frozenset[DecidabilityFragment] = frozenset({
    DecidabilityFragment.PROPOSITIONAL,
    DecidabilityFragment.FINITE_DOMAIN,
    DecidabilityFragment.QF_LIA,
    DecidabilityFragment.QF_LRA,
    DecidabilityFragment.QF_BV,
    DecidabilityFragment.QF_UF,
    DecidabilityFragment.QF_AX,
    DecidabilityFragment.QF_NIA,
})


def _join_fragment(
    a: DecidabilityFragment, b: DecidabilityFragment
) -> DecidabilityFragment:
    if a is b:
        return a
    sa = _FRAGMENT_STRENGTH.get(a, 6)
    sb = _FRAGMENT_STRENGTH.get(b, 6)
    return a if sa >= sb else b


# ═══════════════════════════════════════════════════════════════════════════════
# Solver registry
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class SolverEntry:
    """An entry in the solver registry."""
    fragment: DecidabilityFragment
    solver: LocalSolverInterface
    priority: int = 0  # Lower = higher priority
    name: str = ""

    def __repr__(self) -> str:
        return f"SolverEntry({self.fragment.value}, {self.name}, pri={self.priority})"


class SolverRegistry:
    """Manages the mapping from fragments to solver backends.

    Supports multiple solvers per fragment with priority ordering.
    """

    def __init__(self) -> None:
        self._entries: Dict[DecidabilityFragment, List[SolverEntry]] = {}
        self._fallback: Optional[LocalSolverInterface] = None

    def register(
        self,
        fragment: DecidabilityFragment,
        solver: LocalSolverInterface,
        priority: int = 0,
        name: str = "",
    ) -> None:
        """Register a solver for a fragment."""
        entry = SolverEntry(
            fragment=fragment,
            solver=solver,
            priority=priority,
            name=name or type(solver).__name__,
        )
        self._entries.setdefault(fragment, []).append(entry)
        # Keep sorted by priority (lower = higher priority)
        self._entries[fragment].sort(key=lambda e: e.priority)

    def set_fallback(self, solver: LocalSolverInterface) -> None:
        """Set the fallback solver for unregistered fragments."""
        self._fallback = solver

    def get_solvers(self, fragment: DecidabilityFragment) -> List[SolverEntry]:
        """Get registered solvers for a fragment, ordered by priority."""
        return list(self._entries.get(fragment, []))

    def get_primary(
        self, fragment: DecidabilityFragment
    ) -> Optional[LocalSolverInterface]:
        """Get the highest-priority solver for a fragment."""
        entries = self._entries.get(fragment)
        if entries:
            return entries[0].solver
        return self._fallback

    def get_fallback(self) -> Optional[LocalSolverInterface]:
        return self._fallback

    @property
    def registered_fragments(self) -> Set[DecidabilityFragment]:
        return set(self._entries.keys())

    def summary(self) -> Dict[str, List[str]]:
        """Return a summary of registered solvers."""
        result: Dict[str, List[str]] = {}
        for frag, entries in self._entries.items():
            result[frag.value] = [e.name for e in entries]
        if self._fallback:
            result["fallback"] = [type(self._fallback).__name__]
        return result


# ═══════════════════════════════════════════════════════════════════════════════
# Dispatch strategy
# ═══════════════════════════════════════════════════════════════════════════════


class DispatchStrategy:
    """Strategy for handling solver results and escalation.

    Controls whether to escalate to a more powerful solver when the
    primary solver returns UNKNOWN.
    """

    def __init__(
        self,
        enable_escalation: bool = True,
        max_escalation_depth: int = 2,
    ) -> None:
        self._enable_escalation = enable_escalation
        self._max_depth = max_escalation_depth

    def should_escalate(
        self, result: SolverResult, depth: int
    ) -> bool:
        """Decide whether to try a more powerful solver."""
        if not self._enable_escalation:
            return False
        if depth >= self._max_depth:
            return False
        return result.status in {SolverStatus.UNKNOWN, SolverStatus.TIMEOUT}

    def escalation_timeout_factor(self, depth: int) -> float:
        """Timeout multiplier for escalated attempts."""
        return 2.0 ** depth


# ═══════════════════════════════════════════════════════════════════════════════
# Fragment Dispatcher
# ═══════════════════════════════════════════════════════════════════════════════


class FragmentDispatcher:
    """Routes obligations to the appropriate solver by decidability fragment.

    This is the main entry point for the solver subsystem.  The kernel
    submits obligations here, and the dispatcher:

    1. Classifies the obligation's fragment.
    2. Looks up the best solver for that fragment.
    3. Dispatches the check.
    4. Optionally escalates to a more powerful solver if the first returns UNKNOWN.

    Usage::

        dispatcher = FragmentDispatcher.create_default()
        result = dispatcher.dispatch(obligation)
    """

    def __init__(
        self,
        registry: Optional[SolverRegistry] = None,
        classifier: Optional[ObligationClassifier] = None,
        strategy: Optional[DispatchStrategy] = None,
    ) -> None:
        self._registry = registry or SolverRegistry()
        self._classifier = classifier or ObligationClassifier()
        self._strategy = strategy or DispatchStrategy()
        self._stats = SolverStatistics()

    # -------------------------------------------------------------------
    # Public API
    # -------------------------------------------------------------------

    def dispatch(self, obligation: SolverObligation) -> SolverResult:
        """Dispatch a single obligation to the appropriate solver.

        Returns a ``SolverResult``.
        """
        fragment = self._classifier.classify(obligation)
        logger.debug("Obligation classified as %s", fragment.value)

        result = self._dispatch_with_escalation(obligation, fragment, depth=0)
        self._stats.record(result)
        return result

    def dispatch_batch(
        self, obligations: Sequence[SolverObligation]
    ) -> List[SolverResult]:
        """Dispatch a batch of obligations, grouping by fragment.

        Obligations in the same fragment are processed together for efficiency.
        """
        grouped = self._classifier.classify_batch(obligations)
        # Maintain original order in results
        obl_to_idx: Dict[int, int] = {id(o): i for i, o in enumerate(obligations)}
        results: List[Optional[SolverResult]] = [None] * len(obligations)

        for fragment, obls in grouped.items():
            for obl in obls:
                result = self._dispatch_with_escalation(obl, fragment, depth=0)
                self._stats.record(result)
                idx = obl_to_idx[id(obl)]
                results[idx] = result

        # Fill any None results (should not happen, but safety)
        return [
            r if r is not None else SolverResult(
                status=SolverStatus.ERROR,
                explanation="Dispatch error: obligation not processed",
            )
            for r in results
        ]

    def classify(self, obligation: SolverObligation) -> DecidabilityFragment:
        """Classify an obligation without dispatching."""
        return self._classifier.classify(obligation)

    @property
    def statistics(self) -> SolverStatistics:
        return self._stats

    @property
    def registry(self) -> SolverRegistry:
        return self._registry

    # -------------------------------------------------------------------
    # Internal dispatch logic
    # -------------------------------------------------------------------

    def _dispatch_with_escalation(
        self,
        obligation: SolverObligation,
        fragment: DecidabilityFragment,
        depth: int,
    ) -> SolverResult:
        """Dispatch with optional escalation on UNKNOWN."""
        solver = self._registry.get_primary(fragment)
        if solver is None:
            # Try fallback
            solver = self._registry.get_fallback()
            if solver is None:
                return SolverResult(
                    status=SolverStatus.ERROR,
                    explanation=(
                        f"No solver registered for fragment {fragment.value} "
                        f"and no fallback configured"
                    ),
                )

        result = solver.check(obligation)

        # Escalation: if UNKNOWN/TIMEOUT, try a more powerful solver
        if self._strategy.should_escalate(result, depth):
            escalated_solver = self._find_escalation_solver(fragment)
            if escalated_solver is not None and escalated_solver is not solver:
                factor = self._strategy.escalation_timeout_factor(depth)
                escalated_obl = obligation.with_timeout(
                    obligation.timeout_ms * factor if obligation.timeout_ms > 0
                    else self._registry.get_primary(fragment) is not None and 5000.0 * factor
                    or 5000.0 * factor
                )
                escalated_result = escalated_solver.check(escalated_obl)
                if escalated_result.is_definitive:
                    return escalated_result

        return result

    def _find_escalation_solver(
        self, current_fragment: DecidabilityFragment
    ) -> Optional[LocalSolverInterface]:
        """Find a more powerful solver for escalation.

        Strategy: try the fallback (typically Z3 full backend).
        """
        return self._registry.get_fallback()

    # -------------------------------------------------------------------
    # Factory
    # -------------------------------------------------------------------

    @classmethod
    def create_default(
        cls,
        config: Optional[SolverConfig] = None,
    ) -> FragmentDispatcher:
        """Create a dispatcher with default solver registrations.

        Registers:
        - BooleanSolver for PROPOSITIONAL
        - TableSolver for FINITE_DOMAIN
        - ArithmeticSolver for QF_LIA
        - Z3Backend as fallback for everything else
        """
        cfg = config or SolverConfig()
        registry = SolverRegistry()

        # Import specialized solvers
        from deppy.solver.boolean_solver import BooleanSolver
        from deppy.solver.table_solver import TableSolver
        from deppy.solver.arithmetic_solver import ArithmeticSolver
        from deppy.solver.z3_backend import create_z3_backend

        # Register specialized solvers
        bool_solver = BooleanSolver()
        registry.register(
            DecidabilityFragment.PROPOSITIONAL,
            bool_solver,
            priority=0,
            name="BooleanSolver",
        )

        table_solver = TableSolver()
        registry.register(
            DecidabilityFragment.FINITE_DOMAIN,
            table_solver,
            priority=0,
            name="TableSolver",
        )

        arith_solver = ArithmeticSolver(config=cfg)
        registry.register(
            DecidabilityFragment.QF_LIA,
            arith_solver,
            priority=0,
            name="ArithmeticSolver",
        )

        # Z3 as fallback for all other fragments
        z3_backend = create_z3_backend(config=cfg)
        registry.set_fallback(z3_backend)

        # Also register Z3 for heavier fragments
        for frag in [
            DecidabilityFragment.QF_LRA,
            DecidabilityFragment.QF_BV,
            DecidabilityFragment.QF_UF,
            DecidabilityFragment.QF_AX,
            DecidabilityFragment.QF_NIA,
            DecidabilityFragment.UNDECIDABLE,
            DecidabilityFragment.UNKNOWN,
        ]:
            registry.register(frag, z3_backend, priority=0, name="Z3Backend")

        return cls(registry=registry)
