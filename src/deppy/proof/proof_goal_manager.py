"""Proof goal manager: track open proof goals and discharge them.

Manages the lifecycle of proof goals from creation through discharge,
providing progress tracking and reporting capabilities.
"""

from __future__ import annotations

import enum
import logging
import time
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.types.witnesses import ProofTerm, ReflProof
from deppy.proof._protocols import ProofObligation, ObligationStatus

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Goal status
# ---------------------------------------------------------------------------


class GoalStatus(enum.Enum):
    """Status of a proof goal in its lifecycle."""

    OPEN = "open"
    IN_PROGRESS = "in_progress"
    DISCHARGED = "discharged"
    FAILED = "failed"
    DEFERRED = "deferred"
    TRIVIAL = "trivial"
    CANCELLED = "cancelled"


# ---------------------------------------------------------------------------
# Goal priority
# ---------------------------------------------------------------------------


class GoalPriority(enum.Enum):
    """Priority levels for proof goals."""

    CRITICAL = 0
    HIGH = 1
    NORMAL = 2
    LOW = 3
    BACKGROUND = 4


# ---------------------------------------------------------------------------
# Proof goal
# ---------------------------------------------------------------------------


@dataclass
class ProofGoal:
    """A single proof goal to be discharged.

    Mutable dataclass because goals change status over their lifecycle.

    Attributes:
        _goal_id: Unique identifier for this goal.
        _obligation: The underlying proof obligation.
        _status: Current lifecycle status.
        _priority: Goal priority.
        _proof_term: The proof term (once discharged).
        _trust_level: Trust level of the discharge.
        _created_at: Timestamp of creation.
        _discharged_at: Timestamp of discharge (if discharged).
        _attempts: Number of discharge attempts.
        _parent_id: ID of parent goal (for sub-goals).
        _children_ids: IDs of child sub-goals.
        _tags: Tags for categorization.
        _notes: Human-readable notes about the goal.
    """

    _goal_id: str
    _obligation: ProofObligation
    _status: GoalStatus = GoalStatus.OPEN
    _priority: GoalPriority = GoalPriority.NORMAL
    _proof_term: Optional[ProofTerm] = None
    _trust_level: TrustLevel = TrustLevel.RESIDUAL
    _created_at: float = field(default_factory=time.time)
    _discharged_at: Optional[float] = None
    _attempts: int = 0
    _parent_id: Optional[str] = None
    _children_ids: List[str] = field(default_factory=list)
    _tags: Set[str] = field(default_factory=set)
    _notes: str = ""

    @property
    def goal_id(self) -> str:
        return self._goal_id

    @property
    def obligation(self) -> ProofObligation:
        return self._obligation

    @property
    def status(self) -> GoalStatus:
        return self._status

    @property
    def priority(self) -> GoalPriority:
        return self._priority

    @property
    def proof_term(self) -> Optional[ProofTerm]:
        return self._proof_term

    @property
    def trust_level(self) -> TrustLevel:
        return self._trust_level

    @property
    def created_at(self) -> float:
        return self._created_at

    @property
    def discharged_at(self) -> Optional[float]:
        return self._discharged_at

    @property
    def attempts(self) -> int:
        return self._attempts

    @property
    def is_open(self) -> bool:
        return self._status in (GoalStatus.OPEN, GoalStatus.IN_PROGRESS)

    @property
    def is_discharged(self) -> bool:
        return self._status in (GoalStatus.DISCHARGED, GoalStatus.TRIVIAL)

    @property
    def is_terminal(self) -> bool:
        return self._status in (
            GoalStatus.DISCHARGED,
            GoalStatus.FAILED,
            GoalStatus.TRIVIAL,
            GoalStatus.CANCELLED,
        )

    @property
    def has_children(self) -> bool:
        return len(self._children_ids) > 0

    @property
    def elapsed_seconds(self) -> Optional[float]:
        if self._discharged_at is not None:
            return self._discharged_at - self._created_at
        return None

    def __repr__(self) -> str:
        return (
            f"ProofGoal({self._goal_id!r}, status={self._status.value}, "
            f"priority={self._priority.value})"
        )


# ---------------------------------------------------------------------------
# Discharged goal
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class DischargedGoal:
    """A proof goal that has been successfully discharged.

    Frozen snapshot of a discharged goal for reporting.

    Attributes:
        _goal_id: The goal identifier.
        _obligation: The original obligation.
        _proof_term: The proof term that discharged the goal.
        _trust_level: Trust level of the proof.
        _elapsed_seconds: Time taken to discharge.
        _attempts: Number of attempts before success.
    """

    _goal_id: str
    _obligation: ProofObligation
    _proof_term: ProofTerm
    _trust_level: TrustLevel = TrustLevel.PROOF_BACKED
    _elapsed_seconds: float = 0.0
    _attempts: int = 1

    @property
    def goal_id(self) -> str:
        return self._goal_id

    @property
    def obligation(self) -> ProofObligation:
        return self._obligation

    @property
    def proof_term(self) -> ProofTerm:
        return self._proof_term

    @property
    def trust_level(self) -> TrustLevel:
        return self._trust_level

    @property
    def elapsed_seconds(self) -> float:
        return self._elapsed_seconds

    @property
    def attempts(self) -> int:
        return self._attempts

    def __repr__(self) -> str:
        return (
            f"DischargedGoal({self._goal_id!r}, "
            f"trust={self._trust_level.value})"
        )


# ---------------------------------------------------------------------------
# Proof progress
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ProofProgress:
    """Progress report on proof goals.

    Attributes:
        _total: Total number of goals.
        _open: Number of open goals.
        _in_progress: Number of in-progress goals.
        _discharged: Number of discharged goals.
        _failed: Number of failed goals.
        _deferred: Number of deferred goals.
        _trivial: Number of trivially discharged goals.
        _cancelled: Number of cancelled goals.
        _trust_distribution: Count of goals by trust level.
        _priority_distribution: Count of open goals by priority.
        _total_attempts: Total discharge attempts across all goals.
        _average_elapsed: Average elapsed seconds for discharged goals.
    """

    _total: int = 0
    _open: int = 0
    _in_progress: int = 0
    _discharged: int = 0
    _failed: int = 0
    _deferred: int = 0
    _trivial: int = 0
    _cancelled: int = 0
    _trust_distribution: Dict[str, int] = field(default_factory=dict)
    _priority_distribution: Dict[str, int] = field(default_factory=dict)
    _total_attempts: int = 0
    _average_elapsed: float = 0.0

    @property
    def total(self) -> int:
        return self._total

    @property
    def open(self) -> int:
        return self._open

    @property
    def in_progress(self) -> int:
        return self._in_progress

    @property
    def discharged(self) -> int:
        return self._discharged

    @property
    def failed(self) -> int:
        return self._failed

    @property
    def deferred(self) -> int:
        return self._deferred

    @property
    def trivial(self) -> int:
        return self._trivial

    @property
    def cancelled(self) -> int:
        return self._cancelled

    @property
    def completion_ratio(self) -> float:
        if self._total == 0:
            return 1.0
        return (self._discharged + self._trivial) / self._total

    @property
    def is_complete(self) -> bool:
        return self._open == 0 and self._in_progress == 0

    @property
    def has_failures(self) -> bool:
        return self._failed > 0

    def __repr__(self) -> str:
        return (
            f"ProofProgress(total={self._total}, "
            f"done={self._discharged + self._trivial}, "
            f"open={self._open}, failed={self._failed})"
        )


# ---------------------------------------------------------------------------
# Proof goal manager
# ---------------------------------------------------------------------------


class ProofGoalManager:
    """Track open proof goals and discharge them.

    Manages the full lifecycle of proof goals: creation, status tracking,
    discharge, sub-goal decomposition, and progress reporting.

    Attributes:
        _goals: All goals indexed by goal ID.
        _counter: Counter for generating unique goal IDs.
        _prefix: Prefix for goal IDs.
        _auto_trivial: Whether to auto-mark trivial goals.
    """

    def __init__(
        self,
        prefix: str = "goal",
        auto_trivial: bool = True,
    ) -> None:
        self._goals: Dict[str, ProofGoal] = {}
        self._counter: int = 0
        self._prefix: str = prefix
        self._auto_trivial: bool = auto_trivial

    def _next_id(self) -> str:
        """Generate the next unique goal ID."""
        self._counter += 1
        return f"{self._prefix}_{self._counter}"

    # -- Goal creation -----------------------------------------------------

    def add_goal(
        self,
        obligation: ProofObligation,
        priority: GoalPriority = GoalPriority.NORMAL,
        parent_id: Optional[str] = None,
        tags: Optional[Set[str]] = None,
    ) -> str:
        """Add a new proof goal from an obligation.

        Args:
            obligation: The proof obligation to track.
            priority: Priority of the goal.
            parent_id: Optional parent goal ID (for sub-goals).
            tags: Optional tags for categorization.

        Returns:
            The generated goal ID.
        """
        goal_id = self._next_id()
        goal = ProofGoal(
            _goal_id=goal_id,
            _obligation=obligation,
            _status=GoalStatus.OPEN,
            _priority=priority,
            _parent_id=parent_id,
            _tags=tags or set(),
        )

        # Check for trivial obligations
        if self._auto_trivial and self._is_trivial(obligation):
            goal._status = GoalStatus.TRIVIAL
            goal._proof_term = ReflProof()
            goal._trust_level = TrustLevel.PROOF_BACKED
            goal._discharged_at = time.time()

        self._goals[goal_id] = goal

        # Register as child of parent
        if parent_id is not None and parent_id in self._goals:
            self._goals[parent_id]._children_ids.append(goal_id)

        logger.debug("Added goal %s (status=%s)", goal_id, goal.status.value)
        return goal_id

    def add_goals_from_obligations(
        self,
        obligations: List[ProofObligation],
        priority: GoalPriority = GoalPriority.NORMAL,
    ) -> List[str]:
        """Add multiple goals from a list of obligations."""
        return [
            self.add_goal(obl, priority=priority) for obl in obligations
        ]

    # -- Goal decomposition ------------------------------------------------

    def decompose_goal(
        self,
        goal_id: str,
        sub_obligations: List[ProofObligation],
    ) -> List[str]:
        """Decompose a goal into sub-goals.

        The parent goal status becomes IN_PROGRESS and will be
        discharged when all sub-goals are discharged.
        """
        goal = self._goals.get(goal_id)
        if goal is None:
            raise KeyError(f"Goal {goal_id} not found")
        if goal.is_terminal:
            raise ValueError(f"Cannot decompose terminal goal {goal_id}")

        goal._status = GoalStatus.IN_PROGRESS
        sub_ids: List[str] = []
        for obl in sub_obligations:
            sub_id = self.add_goal(obl, priority=goal.priority, parent_id=goal_id)
            sub_ids.append(sub_id)
        return sub_ids

    # -- Goal discharge ----------------------------------------------------

    def discharge(
        self,
        goal_id: str,
        proof_term: ProofTerm,
        trust_level: TrustLevel = TrustLevel.PROOF_BACKED,
    ) -> bool:
        """Discharge a goal with a proof term.

        Args:
            goal_id: The goal to discharge.
            proof_term: The proof term witnessing the obligation.
            trust_level: Trust level of the proof.

        Returns:
            True if the goal was successfully discharged.
        """
        goal = self._goals.get(goal_id)
        if goal is None:
            logger.warning("Attempted to discharge unknown goal %s", goal_id)
            return False
        if goal.is_terminal:
            logger.warning("Goal %s already terminal (%s)", goal_id, goal.status.value)
            return False

        goal._proof_term = proof_term
        goal._trust_level = trust_level
        goal._status = GoalStatus.DISCHARGED
        goal._discharged_at = time.time()
        goal._attempts += 1

        # Update the obligation status
        goal._obligation.status = ObligationStatus.DISCHARGED
        goal._obligation.proof = proof_term

        # Check if parent can be discharged
        if goal._parent_id is not None:
            self._try_discharge_parent(goal._parent_id)

        logger.debug("Discharged goal %s (trust=%s)", goal_id, trust_level.value)
        return True

    def mark_failed(self, goal_id: str, reason: str = "") -> bool:
        """Mark a goal as failed."""
        goal = self._goals.get(goal_id)
        if goal is None:
            return False
        if goal.is_terminal:
            return False
        goal._status = GoalStatus.FAILED
        goal._attempts += 1
        if reason:
            goal._notes = reason
        return True

    def mark_deferred(self, goal_id: str, reason: str = "") -> bool:
        """Mark a goal as deferred (to be attempted later)."""
        goal = self._goals.get(goal_id)
        if goal is None:
            return False
        if goal.is_terminal:
            return False
        goal._status = GoalStatus.DEFERRED
        if reason:
            goal._notes = reason
        return True

    def cancel_goal(self, goal_id: str, reason: str = "") -> bool:
        """Cancel a goal."""
        goal = self._goals.get(goal_id)
        if goal is None:
            return False
        if goal.is_terminal:
            return False
        goal._status = GoalStatus.CANCELLED
        if reason:
            goal._notes = reason
        # Also cancel children
        for child_id in goal._children_ids:
            self.cancel_goal(child_id, reason=f"Parent {goal_id} cancelled")
        return True

    def reopen_goal(self, goal_id: str) -> bool:
        """Reopen a deferred or failed goal."""
        goal = self._goals.get(goal_id)
        if goal is None:
            return False
        if goal.status not in (GoalStatus.DEFERRED, GoalStatus.FAILED):
            return False
        goal._status = GoalStatus.OPEN
        goal._proof_term = None
        return True

    def attempt_discharge(self, goal_id: str) -> None:
        """Record an unsuccessful discharge attempt."""
        goal = self._goals.get(goal_id)
        if goal is not None:
            goal._attempts += 1

    def _try_discharge_parent(self, parent_id: str) -> None:
        """Try to discharge a parent goal if all children are done."""
        parent = self._goals.get(parent_id)
        if parent is None:
            return
        if parent.is_terminal:
            return
        children = [
            self._goals[cid] for cid in parent._children_ids
            if cid in self._goals
        ]
        if not children:
            return
        if all(c.is_discharged for c in children):
            # Compose child proofs
            child_proofs = [
                c.proof_term for c in children if c.proof_term is not None
            ]
            if child_proofs:
                from deppy.types.witnesses import CompositeProof
                combined = CompositeProof(
                    sub_proofs=tuple(child_proofs),
                    combiner="conjunction",
                )
                trust = self._weakest_trust(
                    [c.trust_level for c in children]
                )
                self.discharge(parent_id, combined, trust)

    # -- Goal queries ------------------------------------------------------

    def get_goal(self, goal_id: str) -> Optional[ProofGoal]:
        """Get a goal by ID."""
        return self._goals.get(goal_id)

    def get_open_goals(self) -> List[ProofGoal]:
        """Get all open (undischarged) goals, sorted by priority."""
        goals = [
            g for g in self._goals.values()
            if g.status in (GoalStatus.OPEN, GoalStatus.IN_PROGRESS)
        ]
        goals.sort(key=lambda g: (g.priority.value, g.created_at))
        return goals

    def get_discharged(self) -> List[DischargedGoal]:
        """Get all discharged goals as frozen DischargedGoal snapshots."""
        discharged: List[DischargedGoal] = []
        for g in self._goals.values():
            if g.is_discharged and g.proof_term is not None:
                elapsed = g.elapsed_seconds or 0.0
                discharged.append(DischargedGoal(
                    _goal_id=g.goal_id,
                    _obligation=g.obligation,
                    _proof_term=g.proof_term,
                    _trust_level=g.trust_level,
                    _elapsed_seconds=elapsed,
                    _attempts=g.attempts,
                ))
        return discharged

    def get_failed_goals(self) -> List[ProofGoal]:
        """Get all failed goals."""
        return [g for g in self._goals.values() if g.status == GoalStatus.FAILED]

    def get_deferred_goals(self) -> List[ProofGoal]:
        """Get all deferred goals."""
        return [g for g in self._goals.values() if g.status == GoalStatus.DEFERRED]

    def get_goals_by_tag(self, tag: str) -> List[ProofGoal]:
        """Get all goals with a specific tag."""
        return [g for g in self._goals.values() if tag in g._tags]

    def get_goals_by_site(self, site_id: SiteId) -> List[ProofGoal]:
        """Get all goals associated with a specific site."""
        return [
            g for g in self._goals.values()
            if g.obligation.site_id == site_id
        ]

    def get_children(self, goal_id: str) -> List[ProofGoal]:
        """Get child sub-goals of a goal."""
        goal = self._goals.get(goal_id)
        if goal is None:
            return []
        return [
            self._goals[cid] for cid in goal._children_ids
            if cid in self._goals
        ]

    # -- Progress reporting ------------------------------------------------

    def progress_report(self) -> ProofProgress:
        """Generate a progress report on all goals."""
        status_counts: Dict[GoalStatus, int] = {}
        trust_dist: Dict[str, int] = {}
        priority_dist: Dict[str, int] = {}
        total_attempts = 0
        total_elapsed = 0.0
        discharged_count = 0

        for g in self._goals.values():
            status_counts[g.status] = status_counts.get(g.status, 0) + 1
            total_attempts += g.attempts
            if g.is_discharged:
                trust_key = g.trust_level.value
                trust_dist[trust_key] = trust_dist.get(trust_key, 0) + 1
                elapsed = g.elapsed_seconds
                if elapsed is not None:
                    total_elapsed += elapsed
                    discharged_count += 1
            if g.is_open:
                pri_key = g.priority.name
                priority_dist[pri_key] = priority_dist.get(pri_key, 0) + 1

        avg_elapsed = (
            total_elapsed / discharged_count if discharged_count > 0 else 0.0
        )

        return ProofProgress(
            _total=len(self._goals),
            _open=status_counts.get(GoalStatus.OPEN, 0),
            _in_progress=status_counts.get(GoalStatus.IN_PROGRESS, 0),
            _discharged=status_counts.get(GoalStatus.DISCHARGED, 0),
            _failed=status_counts.get(GoalStatus.FAILED, 0),
            _deferred=status_counts.get(GoalStatus.DEFERRED, 0),
            _trivial=status_counts.get(GoalStatus.TRIVIAL, 0),
            _cancelled=status_counts.get(GoalStatus.CANCELLED, 0),
            _trust_distribution=trust_dist,
            _priority_distribution=priority_dist,
            _total_attempts=total_attempts,
            _average_elapsed=avg_elapsed,
        )

    # -- Helpers -----------------------------------------------------------

    def _is_trivial(self, obligation: ProofObligation) -> bool:
        """Check if an obligation is trivially dischargeable."""
        prop = obligation.prop
        if isinstance(prop, tuple):
            if len(prop) >= 1 and prop[0] == "True":
                return True
            if (
                len(prop) == 3
                and prop[0] == "eq"
                and prop[1] == prop[2]
            ):
                return True
        if obligation.status == ObligationStatus.DISCHARGED:
            return True
        return False

    def _weakest_trust(self, levels: List[TrustLevel]) -> TrustLevel:
        """Return the weakest (least trusted) trust level."""
        _ordering = {
            TrustLevel.PROOF_BACKED: 5,
            TrustLevel.TRUSTED_AUTO: 4,
            TrustLevel.BOUNDED_AUTO: 3,
            TrustLevel.TRACE_BACKED: 2,
            TrustLevel.ASSUMED: 1,
            TrustLevel.RESIDUAL: 0,
        }
        if not levels:
            return TrustLevel.RESIDUAL
        return min(levels, key=lambda tl: _ordering.get(tl, 0))

    @property
    def total_goals(self) -> int:
        """Total number of goals tracked."""
        return len(self._goals)

    @property
    def open_count(self) -> int:
        """Number of open goals."""
        return sum(1 for g in self._goals.values() if g.is_open)

    @property
    def discharged_count(self) -> int:
        """Number of discharged goals."""
        return sum(1 for g in self._goals.values() if g.is_discharged)

    def clear(self) -> None:
        """Remove all goals."""
        self._goals.clear()
        self._counter = 0

    def statistics(self) -> Dict[str, Any]:
        """Return detailed statistics."""
        progress = self.progress_report()
        return {
            "total_goals": progress.total,
            "open": progress.open,
            "in_progress": progress.in_progress,
            "discharged": progress.discharged,
            "trivial": progress.trivial,
            "failed": progress.failed,
            "deferred": progress.deferred,
            "cancelled": progress.cancelled,
            "completion_ratio": progress.completion_ratio,
            "trust_distribution": progress._trust_distribution,
            "total_attempts": progress._total_attempts,
            "average_elapsed_seconds": progress._average_elapsed,
        }

    def __repr__(self) -> str:
        return (
            f"ProofGoalManager(total={self.total_goals}, "
            f"open={self.open_count}, "
            f"discharged={self.discharged_count})"
        )
