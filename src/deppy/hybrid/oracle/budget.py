"""Oracle budget and cost control — the oracle monad annotated with costs.

Cost-annotated oracle calls
───────────────────────────
Every oracle call in the hybrid verification pipeline carries a cost
(tokens consumed, dollars spent).  This module provides the bookkeeping
infrastructure so that:

1. **Budget caps** are enforced — the system never exceeds a user-specified
   token or dollar budget.
2. **Cost estimation** is available *before* a call is made, allowing the
   allocator to decide whether the ROI justifies the expenditure.
3. **Budget allocation** across multiple proof obligations uses an
   ROI-priority queue so the most impactful obligations are checked first.
4. **Reporting** breaks down costs by model, pipeline phase, and trust level
   so the user can tune their workflow.

Verification modes
──────────────────
============  ========  ============================================
Mode          $/KLOC    Description
============  ========  ============================================
FREE          $0.00     Z3-only, no oracle calls
CHEAP         ~$0.01    One oracle call per function
STANDARD      ~$0.05    Oracle + cross-validation
THOROUGH      ~$0.20    Oracle + Lean translation + cross-validation
============  ========  ============================================
"""
from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.solver import SolverObligation, SolverResult
    from deppy.proof._protocols import ProofObligation as _CoreProofObligation
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

import heapq
import json
import logging
import math
import time
from dataclasses import dataclass, field
from enum import Enum, unique
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

if TYPE_CHECKING:
    from deppy.hybrid.core.trust import TrustLevel

# ── Optional Z3 ──────────────────────────────────────────────────────────────

try:
    import z3

    _Z3_AVAILABLE = True
except ImportError:

    z3 = None  # type: ignore[assignment]
    _Z3_AVAILABLE = False

logger = logging.getLogger(__name__)

# ─── Constants ────────────────────────────────────────────────────────────────

_DEFAULT_MAX_TOKENS = 500_000
_DEFAULT_MAX_COST_USD = 10.0
_TOKENS_PER_LINE_ESTIMATE = 12  # rough average for Python source

# ─── VerificationMode ─────────────────────────────────────────────────────────

@unique
class VerificationMode(Enum):
    """Verification intensity levels with associated oracle budgets.

    Each mode defines how aggressively the system uses oracle (LLM) calls
    versus purely local (Z3) verification.
    """

    FREE = "free"
    CHEAP = "cheap"
    STANDARD = "standard"
    THOROUGH = "thorough"

@dataclass(frozen=True)
class VerificationModeConfig:
    """Configuration for a single :class:`VerificationMode`."""

    mode: VerificationMode
    oracle_calls_per_function: float
    trust_ceiling: float
    cost_per_kloc_usd: float
    description: str

    @property
    def uses_oracle(self) -> bool:
        return self.oracle_calls_per_function > 0

VERIFICATION_MODE_CONFIGS: Dict[VerificationMode, VerificationModeConfig] = {
    VerificationMode.FREE: VerificationModeConfig(
        mode=VerificationMode.FREE,
        oracle_calls_per_function=0.0,
        trust_ceiling=0.6,
        cost_per_kloc_usd=0.0,
        description="Z3-only — no oracle calls, no cost",
    ),
    VerificationMode.CHEAP: VerificationModeConfig(
        mode=VerificationMode.CHEAP,
        oracle_calls_per_function=1.0,
        trust_ceiling=0.8,
        cost_per_kloc_usd=0.01,
        description="One oracle call per function for quick feedback",
    ),
    VerificationMode.STANDARD: VerificationModeConfig(
        mode=VerificationMode.STANDARD,
        oracle_calls_per_function=2.5,
        trust_ceiling=0.9,
        cost_per_kloc_usd=0.05,
        description="Oracle + cross-validation for high-confidence results",
    ),
    VerificationMode.THOROUGH: VerificationModeConfig(
        mode=VerificationMode.THOROUGH,
        oracle_calls_per_function=5.0,
        trust_ceiling=0.99,
        cost_per_kloc_usd=0.20,
        description="Oracle + Lean translation + full cross-validation",
    ),
}

def get_mode_config(mode: VerificationMode) -> VerificationModeConfig:
    """Retrieve the configuration for a verification mode."""
    return VERIFICATION_MODE_CONFIGS[mode]

# ─── OracleCost ───────────────────────────────────────────────────────────────

@dataclass
class OracleCost:
    """Cost of a single oracle (LLM) interaction.

    Accumulates input/output token counts and the associated dollar cost.
    Supports ``+`` and ``sum()`` for ergonomic aggregation.
    """

    input_tokens: int = 0
    output_tokens: int = 0
    model: str = ""
    cost_usd: float = 0.0

    # -- arithmetic ------------------------------------------------------------

    def __add__(self, other: OracleCost) -> OracleCost:
        if not isinstance(other, OracleCost):
            return NotImplemented
        return OracleCost(
            input_tokens=self.input_tokens + other.input_tokens,
            output_tokens=self.output_tokens + other.output_tokens,
            model=self.model or other.model,
            cost_usd=self.cost_usd + other.cost_usd,
        )

    def __radd__(self, other: Any) -> OracleCost:
        """Support ``sum(costs)`` — ``sum`` starts with ``0 + first``."""
        if other == 0 or other is None:
            return self
        if isinstance(other, OracleCost):
            return other.__add__(self)
        return NotImplemented

    # -- properties ------------------------------------------------------------

    @property
    def total_tokens(self) -> int:
        return self.input_tokens + self.output_tokens

    def __str__(self) -> str:
        return (
            f"OracleCost({self.total_tokens} tok, ${self.cost_usd:.4f}"
            f", model={self.model!r})"
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "input_tokens": self.input_tokens,
            "output_tokens": self.output_tokens,
            "model": self.model,
            "cost_usd": self.cost_usd,
        }

    @classmethod
    def zero(cls) -> OracleCost:
        """A zero-cost sentinel."""
        return cls()

# ─── OracleBudget ─────────────────────────────────────────────────────────────

class OracleBudget:
    """Token and dollar budget for oracle calls with enforcement.

    The budget acts as a finite resource pool: every oracle call must
    :meth:`charge` its cost, and callers should :meth:`can_afford` before
    dispatching.

    Example::

        budget = OracleBudget(max_tokens=100_000, max_cost_usd=5.0)
        if budget.can_afford(estimated_tokens=2000):
            result = oracle_call(...)
            budget.charge(result.cost)
    """

    def __init__(
        self,
        max_tokens: int = _DEFAULT_MAX_TOKENS,
        max_cost_usd: float = _DEFAULT_MAX_COST_USD,
    ) -> None:
        self._max_tokens = max_tokens
        self._max_cost_usd = max_cost_usd
        self._used_tokens: int = 0
        self._used_cost_usd: float = 0.0
        self._charges: List[OracleCost] = []
        self._created_at: float = time.time()

    # -- read-only properties --------------------------------------------------

    @property
    def max_tokens(self) -> int:
        return self._max_tokens

    @property
    def max_cost_usd(self) -> float:
        return self._max_cost_usd

    @property
    def used_tokens(self) -> int:
        return self._used_tokens

    @property
    def used_cost_usd(self) -> float:
        return self._used_cost_usd

    # -- budget queries --------------------------------------------------------

    def can_afford(self, estimated_tokens: int) -> bool:
        """Check whether the budget can accommodate *estimated_tokens* more."""
        if self._used_tokens + estimated_tokens > self._max_tokens:
            return False
        return True

    def can_afford_cost(self, estimated_cost_usd: float) -> bool:
        """Check whether the budget can accommodate *estimated_cost_usd* more."""
        return self._used_cost_usd + estimated_cost_usd <= self._max_cost_usd

    def can_afford_full(
        self, estimated_tokens: int, estimated_cost_usd: float
    ) -> bool:
        """Check both token and dollar limits."""
        return self.can_afford(estimated_tokens) and self.can_afford_cost(
            estimated_cost_usd
        )

    def remaining_tokens(self) -> int:
        """Tokens still available in the budget."""
        return max(self._max_tokens - self._used_tokens, 0)

    def remaining_cost(self) -> float:
        """Dollars still available in the budget."""
        return max(self._max_cost_usd - self._used_cost_usd, 0.0)

    def utilization(self) -> float:
        """Fraction of total budget used (max of token and dollar utilization)."""
        token_util = (
            self._used_tokens / self._max_tokens if self._max_tokens > 0 else 0.0
        )
        cost_util = (
            self._used_cost_usd / self._max_cost_usd
            if self._max_cost_usd > 0
            else 0.0
        )
        return max(token_util, cost_util)

    def exceeded(self) -> bool:
        """True if the budget has been exceeded on either dimension."""
        return (
            self._used_tokens > self._max_tokens
            or self._used_cost_usd > self._max_cost_usd
        )

    # -- mutations -------------------------------------------------------------

    def charge(self, cost: OracleCost) -> None:
        """Deduct *cost* from the budget."""
        self._used_tokens += cost.total_tokens
        self._used_cost_usd += cost.cost_usd
        self._charges.append(cost)

    def reserve(self, tokens: int) -> bool:
        """Try to reserve *tokens*.  Returns *False* if insufficient budget."""
        if not self.can_afford(tokens):
            return False
        self._used_tokens += tokens
        return True

    def release(self, tokens: int) -> None:
        """Return previously reserved tokens that were not actually used."""
        self._used_tokens = max(self._used_tokens - tokens, 0)

    def reset(self) -> None:
        """Reset all usage counters (budget limits stay the same)."""
        self._used_tokens = 0
        self._used_cost_usd = 0.0
        self._charges.clear()

    # -- introspection ---------------------------------------------------------

    @property
    def charge_history(self) -> List[OracleCost]:
        """All charges applied to this budget (immutable copy)."""
        return list(self._charges)

    def summary(self) -> str:
        """Human-readable budget status."""
        return (
            f"Budget: {self._used_tokens}/{self._max_tokens} tokens"
            f" (${self._used_cost_usd:.4f}/${self._max_cost_usd:.2f})"
            f" — {self.utilization():.1%} utilised"
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "max_tokens": self._max_tokens,
            "max_cost_usd": self._max_cost_usd,
            "used_tokens": self._used_tokens,
            "used_cost_usd": self._used_cost_usd,
            "remaining_tokens": self.remaining_tokens(),
            "remaining_cost_usd": self.remaining_cost(),
            "utilization": self.utilization(),
            "exceeded": self.exceeded(),
            "num_charges": len(self._charges),
        }

# ─── CostModel ────────────────────────────────────────────────────────────────

class CostModel:
    """Per-model pricing and token-cost estimation.

    Provides :meth:`estimate_cost` for individual calls and
    :meth:`estimate_verification_cost` for whole-codebase projections at
    each :class:`VerificationMode`.
    """

    # (input_cost_per_1k, output_cost_per_1k) in USD
    MODEL_COSTS: Dict[str, Tuple[float, float]] = {
        # OpenAI
        "gpt-4": (0.03, 0.06),
        "gpt-4-turbo": (0.01, 0.03),
        "gpt-4o": (0.005, 0.015),
        "gpt-4o-mini": (0.00015, 0.0006),
        "gpt-3.5-turbo": (0.0005, 0.0015),
        "o1": (0.015, 0.06),
        "o1-mini": (0.003, 0.012),
        "o3-mini": (0.0011, 0.0044),
        # Anthropic
        "claude-3-opus": (0.015, 0.075),
        "claude-3-sonnet": (0.003, 0.015),
        "claude-3-haiku": (0.00025, 0.00125),
        "claude-3.5-sonnet": (0.003, 0.015),
        "claude-3.5-haiku": (0.0008, 0.004),
        "claude-4-sonnet": (0.003, 0.015),
        # Google
        "gemini-1.5-pro": (0.00125, 0.005),
        "gemini-1.5-flash": (0.000075, 0.0003),
        "gemini-2.0-flash": (0.0001, 0.0004),
        # Open models (via API providers — rough averages)
        "llama-3-70b": (0.0008, 0.0008),
        "llama-3-8b": (0.0001, 0.0001),
        "deepseek-v2": (0.00014, 0.00028),
        "deepseek-r1": (0.00055, 0.00219),
        # Default / unknown model fallback
        "default": (0.005, 0.015),
    }

    def __init__(
        self,
        custom_costs: Optional[Dict[str, Tuple[float, float]]] = None,
    ) -> None:
        self._costs = dict(self.MODEL_COSTS)
        if custom_costs:
            self._costs.update(custom_costs)

    # -- per-call estimation ---------------------------------------------------

    def estimate_cost(
        self,
        prompt_tokens: int,
        model: str,
        completion_tokens: Optional[int] = None,
    ) -> OracleCost:
        """Estimate the cost of a single oracle call.

        Parameters
        ----------
        prompt_tokens:
            Number of input (prompt) tokens.
        model:
            Model identifier (must be in :attr:`MODEL_COSTS` or ``"default"``
            is used as fallback).
        completion_tokens:
            Expected output tokens.  If *None*, defaults to ``prompt_tokens // 2``
            as a rough heuristic.
        """
        if completion_tokens is None:
            completion_tokens = max(prompt_tokens // 2, 1)

        in_cost_per_k, out_cost_per_k = self._costs.get(
            model, self._costs["default"]
        )
        cost_usd = (
            prompt_tokens / 1000 * in_cost_per_k
            + completion_tokens / 1000 * out_cost_per_k
        )
        return OracleCost(
            input_tokens=prompt_tokens,
            output_tokens=completion_tokens,
            model=model,
            cost_usd=cost_usd,
        )

    def estimate_verification_cost(
        self,
        num_functions: int,
        mode: VerificationMode,
        model: str = "gpt-4o",
        avg_tokens_per_function: int = 500,
    ) -> OracleCost:
        """Estimate total cost to verify *num_functions* at the given *mode*.

        The estimate uses the mode's ``oracle_calls_per_function`` multiplied
        by the average token cost per call.

        Parameters
        ----------
        num_functions:
            Number of functions (proof obligations) to verify.
        mode:
            The :class:`VerificationMode` governing how many oracle calls
            each function triggers.
        model:
            Which LLM model to price against.
        avg_tokens_per_function:
            Average prompt size per oracle call (in tokens).
        """
        cfg = get_mode_config(mode)
        if not cfg.uses_oracle:
            return OracleCost.zero()

        num_calls = int(math.ceil(num_functions * cfg.oracle_calls_per_function))
        total_input = num_calls * avg_tokens_per_function
        total_output = num_calls * (avg_tokens_per_function // 2)

        in_cost_per_k, out_cost_per_k = self._costs.get(
            model, self._costs["default"]
        )
        cost_usd = (
            total_input / 1000 * in_cost_per_k
            + total_output / 1000 * out_cost_per_k
        )
        return OracleCost(
            input_tokens=total_input,
            output_tokens=total_output,
            model=model,
            cost_usd=cost_usd,
        )

    def estimate_from_kloc(
        self,
        kloc: float,
        mode: VerificationMode,
    ) -> OracleCost:
        """Quick estimate from thousands-of-lines-of-code and mode."""
        cfg = get_mode_config(mode)
        cost_usd = kloc * cfg.cost_per_kloc_usd
        # Back-compute approximate tokens
        est_tokens = int(kloc * 1000 * _TOKENS_PER_LINE_ESTIMATE)
        return OracleCost(
            input_tokens=est_tokens,
            output_tokens=est_tokens // 2,
            model="estimate",
            cost_usd=cost_usd,
        )

    def cheapest_model_for_budget(
        self,
        budget_usd: float,
        required_tokens: int,
    ) -> Optional[str]:
        """Find the cheapest model that fits within *budget_usd*."""
        candidates: List[Tuple[float, str]] = []
        for model, (in_k, out_k) in self._costs.items():
            if model == "default":
                continue
            cost = (
                required_tokens / 1000 * in_k
                + (required_tokens // 2) / 1000 * out_k
            )
            if cost <= budget_usd:
                candidates.append((cost, model))
        if not candidates:
            return None
        candidates.sort()
        return candidates[0][1]

    def model_names(self) -> List[str]:
        """Return all known model names (excluding 'default')."""
        return [m for m in self._costs if m != "default"]

# ─── ProofObligation (lightweight data class for allocator) ───────────────────

@dataclass
class ProofObligation:
    """A single proof obligation awaiting oracle verification.

    Used by :class:`BudgetAllocator` to decide which obligations to
    spend oracle tokens on.
    """

    id: str
    site_id: str
    severity: float = 1.0
    estimated_tokens: int = 500
    confidence_gain: float = 0.3
    estimated_cost: Optional[OracleCost] = None
    priority: float = 0.0

    def __lt__(self, other: ProofObligation) -> bool:
        """Higher priority = should be processed first (max-heap via negation)."""
        return self.priority > other.priority

# ─── BudgetAllocator ──────────────────────────────────────────────────────────

class BudgetAllocator:
    """Allocates oracle budget across proof obligations using a priority queue.

    The priority of each obligation is computed as::

        priority = severity × confidence_gain / estimated_cost

    This **ROI-based** ranking ensures that the most impactful obligations
    (high severity, high confidence gain, low cost) are verified first,
    maximising the H¹ reduction per dollar spent.
    """

    def __init__(
        self,
        cost_model: Optional[CostModel] = None,
        model: str = "gpt-4o",
    ) -> None:
        self._cost_model = cost_model or CostModel()
        self._model = model

    # -- public API ------------------------------------------------------------

    def allocate(
        self,
        obligations: List[ProofObligation],
        budget: OracleBudget,
    ) -> List[Tuple[ProofObligation, OracleCost]]:
        """Allocate budget to obligations using the default strategy (greedy).

        Returns a list of ``(obligation, estimated_cost)`` tuples for the
        obligations that fit within the budget, ordered by priority.
        """
        return self.greedy_allocate(obligations, budget)

    def greedy_allocate(
        self,
        obligations: List[ProofObligation],
        budget: OracleBudget,
    ) -> List[Tuple[ProofObligation, OracleCost]]:
        """Greedy allocation: sort by priority descending, fill until budget exhausted.

        Simple and effective — O(n log n) in the number of obligations.
        """
        scored = self._score_all(obligations)
        scored.sort(key=lambda o: o.priority, reverse=True)

        allocated: List[Tuple[ProofObligation, OracleCost]] = []
        for ob in scored:
            cost = ob.estimated_cost or self._cost_model.estimate_cost(
                ob.estimated_tokens, self._model
            )
            if budget.can_afford_full(cost.total_tokens, cost.cost_usd):
                budget.charge(cost)
                allocated.append((ob, cost))

        return allocated

    def knapsack_allocate(
        self,
        obligations: List[ProofObligation],
        budget: OracleBudget,
    ) -> List[Tuple[ProofObligation, OracleCost]]:
        """Optimal allocation via 0/1 knapsack (dynamic programming).

        More expensive — O(n × W) where W is the token budget granularity —
        but guarantees the *optimal* set of obligations to verify for a given
        budget.  Practical when n ≤ ~500 and budget granularity ≤ ~1000.
        """
        scored = self._score_all(obligations)

        # Prepare items: (value, weight, obligation, cost)
        items: List[Tuple[float, int, ProofObligation, OracleCost]] = []
        for ob in scored:
            cost = ob.estimated_cost or self._cost_model.estimate_cost(
                ob.estimated_tokens, self._model
            )
            value = ob.priority
            weight = cost.total_tokens
            items.append((value, weight, ob, cost))

        if not items:
            return []

        capacity = budget.remaining_tokens()
        # Granularity reduction for large budgets (prevents OOM)
        granularity = max(capacity // 1000, 1)
        scaled_capacity = capacity // granularity

        n = len(items)
        # DP table: dp[i][w] = best value using items[:i] with weight ≤ w
        dp: List[List[float]] = [
            [0.0] * (scaled_capacity + 1) for _ in range(n + 1)
        ]

        scaled_weights = [max(w // granularity, 1) for _, w, _, _ in items]

        for i in range(1, n + 1):
            val_i = items[i - 1][0]
            w_i = scaled_weights[i - 1]
            for w in range(scaled_capacity + 1):
                dp[i][w] = dp[i - 1][w]
                if w_i <= w:
                    candidate = dp[i - 1][w - w_i] + val_i
                    if candidate > dp[i][w]:
                        dp[i][w] = candidate

        # Back-trace to find selected items
        selected_indices: List[int] = []
        w = scaled_capacity
        for i in range(n, 0, -1):
            if dp[i][w] != dp[i - 1][w]:
                selected_indices.append(i - 1)
                w -= scaled_weights[i - 1]

        # Charge budget and build result
        allocated: List[Tuple[ProofObligation, OracleCost]] = []
        for idx in sorted(selected_indices):
            _, _, ob, cost = items[idx]
            if budget.can_afford_full(cost.total_tokens, cost.cost_usd):
                budget.charge(cost)
                allocated.append((ob, cost))

        return allocated

    # -- priority scoring ------------------------------------------------------

    def _score_all(
        self,
        obligations: List[ProofObligation],
    ) -> List[ProofObligation]:
        """Score all obligations and return copies with ``priority`` set."""
        result: List[ProofObligation] = []
        for ob in obligations:
            scored = ProofObligation(
                id=ob.id,
                site_id=ob.site_id,
                severity=ob.severity,
                estimated_tokens=ob.estimated_tokens,
                confidence_gain=ob.confidence_gain,
                estimated_cost=ob.estimated_cost,
                priority=self._priority(ob),
            )
            result.append(scored)
        return result

    def _priority(self, obligation: ProofObligation) -> float:
        """Compute ROI-based priority for a single obligation.

        ``priority = severity × confidence_gain / estimated_cost_usd``

        A small epsilon is added to cost to avoid division by zero for
        free (Z3-only) obligations.
        """
        cost = obligation.estimated_cost or self._cost_model.estimate_cost(
            obligation.estimated_tokens, self._model
        )
        cost_usd = cost.cost_usd + 1e-9  # epsilon for numerical stability
        return obligation.severity * obligation.confidence_gain / cost_usd

    def top_k(
        self,
        obligations: List[ProofObligation],
        k: int,
    ) -> List[ProofObligation]:
        """Return the *k* highest-priority obligations (no budget check)."""
        scored = self._score_all(obligations)
        return heapq.nlargest(k, scored, key=lambda o: o.priority)

# ─── BudgetReport ─────────────────────────────────────────────────────────────

@dataclass
class BudgetReport:
    """Comprehensive cost report for a verification run.

    Breaks down oracle expenditure by model, pipeline phase, and trust
    level, and includes an ROI analysis (cost per H¹ reduction).
    """

    total_spent: OracleCost = field(default_factory=OracleCost.zero)
    by_model: Dict[str, OracleCost] = field(default_factory=dict)
    by_phase: Dict[str, OracleCost] = field(default_factory=dict)
    by_trust_level: Dict[str, OracleCost] = field(default_factory=dict)
    roi_analysis: Dict[str, Any] = field(default_factory=dict)

    budget: Optional[OracleBudget] = field(default=None, repr=False)
    elapsed_seconds: float = 0.0

    # -- builders --------------------------------------------------------------

    def record(
        self,
        cost: OracleCost,
        phase: str = "unknown",
        trust_level: str = "unknown",
    ) -> None:
        """Record a single oracle charge into all breakdowns."""
        self.total_spent = self.total_spent + cost

        model = cost.model or "unknown"
        if model in self.by_model:
            self.by_model[model] = self.by_model[model] + cost
        else:
            self.by_model[model] = cost

        if phase in self.by_phase:
            self.by_phase[phase] = self.by_phase[phase] + cost
        else:
            self.by_phase[phase] = cost

        if trust_level in self.by_trust_level:
            self.by_trust_level[trust_level] = (
                self.by_trust_level[trust_level] + cost
            )
        else:
            self.by_trust_level[trust_level] = cost

    def set_roi(
        self,
        h1_before: int,
        h1_after: int,
        total_obligations: int = 0,
        obligations_verified: int = 0,
    ) -> None:
        """Compute and store ROI analysis metrics."""
        h1_reduction = max(h1_before - h1_after, 0)
        cost_usd = self.total_spent.cost_usd

        self.roi_analysis = {
            "h1_before": h1_before,
            "h1_after": h1_after,
            "h1_reduction": h1_reduction,
            "cost_per_h1_reduction": (
                cost_usd / h1_reduction if h1_reduction > 0 else float("inf")
            ),
            "total_obligations": total_obligations,
            "obligations_verified": obligations_verified,
            "verification_rate": (
                obligations_verified / total_obligations
                if total_obligations > 0
                else 0.0
            ),
            "total_cost_usd": cost_usd,
            "total_tokens": self.total_spent.total_tokens,
        }

    # -- rendering -------------------------------------------------------------

    def to_markdown(self) -> str:
        """Render the report as a Markdown string."""
        lines: List[str] = []
        lines.append("# Oracle Budget Report\n")

        lines.append(f"**Total spent:** {self.total_spent}")
        if self.budget is not None:
            lines.append(f"**Budget utilisation:** {self.budget.utilization():.1%}")
            lines.append(f"**Remaining:** {self.budget.remaining_tokens()} tokens"
                         f" / ${self.budget.remaining_cost():.4f}")
        lines.append("")

        # By model
        if self.by_model:
            lines.append("## Cost by Model\n")
            lines.append("| Model | Input Tokens | Output Tokens | Cost (USD) |")
            lines.append("|-------|-------------|--------------|------------|")
            for model, cost in sorted(self.by_model.items()):
                lines.append(
                    f"| {model} | {cost.input_tokens:,} | "
                    f"{cost.output_tokens:,} | ${cost.cost_usd:.4f} |"
                )
            lines.append("")

        # By phase
        if self.by_phase:
            lines.append("## Cost by Phase\n")
            lines.append("| Phase | Tokens | Cost (USD) |")
            lines.append("|-------|--------|------------|")
            for phase, cost in sorted(self.by_phase.items()):
                lines.append(
                    f"| {phase} | {cost.total_tokens:,} | ${cost.cost_usd:.4f} |"
                )
            lines.append("")

        # By trust level
        if self.by_trust_level:
            lines.append("## Cost by Trust Level\n")
            lines.append("| Trust Level | Tokens | Cost (USD) |")
            lines.append("|------------|--------|------------|")
            for level, cost in sorted(self.by_trust_level.items()):
                lines.append(
                    f"| {level} | {cost.total_tokens:,} | ${cost.cost_usd:.4f} |"
                )
            lines.append("")

        # ROI analysis
        if self.roi_analysis:
            lines.append("## ROI Analysis\n")
            roi = self.roi_analysis
            lines.append(f"- **H¹ reduction:** {roi.get('h1_before', '?')}"
                         f" → {roi.get('h1_after', '?')}"
                         f" (Δ = {roi.get('h1_reduction', '?')})")
            cph = roi.get("cost_per_h1_reduction", float("inf"))
            if cph < float("inf"):
                lines.append(f"- **Cost per H¹ reduction:** ${cph:.4f}")
            else:
                lines.append("- **Cost per H¹ reduction:** N/A (no reduction)")
            lines.append(
                f"- **Obligations verified:** "
                f"{roi.get('obligations_verified', 0)}"
                f" / {roi.get('total_obligations', 0)}"
                f" ({roi.get('verification_rate', 0):.1%})"
            )
            lines.append("")

        if self.elapsed_seconds > 0:
            lines.append(f"*Report generated in {self.elapsed_seconds:.2f}s*")

        return "\n".join(lines)

    def to_json(self) -> Dict[str, Any]:
        """Serialisable JSON-compatible dictionary."""
        return {
            "total_spent": self.total_spent.to_dict(),
            "by_model": {k: v.to_dict() for k, v in self.by_model.items()},
            "by_phase": {k: v.to_dict() for k, v in self.by_phase.items()},
            "by_trust_level": {
                k: v.to_dict() for k, v in self.by_trust_level.items()
            },
            "roi_analysis": self.roi_analysis,
            "elapsed_seconds": self.elapsed_seconds,
        }

    def __str__(self) -> str:
        return (
            f"BudgetReport(spent={self.total_spent}, "
            f"models={len(self.by_model)}, phases={len(self.by_phase)})"
        )

# ─── Convenience constructors ────────────────────────────────────────────────

def budget_for_mode(
    mode: VerificationMode,
    kloc: float = 1.0,
    headroom: float = 1.5,
) -> OracleBudget:
    """Create an :class:`OracleBudget` sized for the given mode and codebase.

    Parameters
    ----------
    mode:
        Verification intensity.
    kloc:
        Estimated codebase size in thousands of lines.
    headroom:
        Multiplier applied to the cost estimate to provide safety margin.
    """
    cfg = get_mode_config(mode)
    estimated_cost = kloc * cfg.cost_per_kloc_usd * headroom
    estimated_tokens = int(kloc * 1000 * _TOKENS_PER_LINE_ESTIMATE * headroom)
    return OracleBudget(
        max_tokens=max(estimated_tokens, 1000),
        max_cost_usd=max(estimated_cost, 0.01),
    )

def free_budget() -> OracleBudget:
    """A zero-cost budget for ``FREE`` mode (Z3-only)."""
    return OracleBudget(max_tokens=0, max_cost_usd=0.0)

def unlimited_budget() -> OracleBudget:
    """An effectively-unlimited budget (for testing / CI-with-no-limits)."""
    return OracleBudget(max_tokens=10**9, max_cost_usd=10**6)
