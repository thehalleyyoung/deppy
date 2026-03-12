"""Proof renderer: render proof goals, terms, and progress as human-readable text.

Provides structured, indented output for displaying proof states to users,
including goals, obligations, proof terms, and progress summaries.
"""

from __future__ import annotations

import textwrap
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Sequence,
    Tuple,
)

from deppy.core._protocols import SiteId, TrustLevel
from deppy.types.base import TypeBase
from deppy.types.witnesses import (
    ProofTerm,
    ReflProof,
    AssumptionProof,
    RuntimeCheckProof,
    StaticProof,
    CompositeProof,
    TransitivityProof,
    SymmetryProof,
    CongruenceProof,
    WitnessCarrier,
    TransportWitness,
)
from deppy.proof._protocols import ProofObligation, ObligationStatus
from deppy.proof.proof_goal_manager import (
    ProofGoal,
    GoalStatus,
    GoalPriority,
    DischargedGoal,
    ProofProgress,
)
from deppy.proof.witness_combinators import (
    TransitivityWitness,
    SymmetryWitness,
    CongruenceWitness,
    ExistentialPackWitness,
    UniversalWitness,
    PairWitness,
    ProjectionWitness,
    ModusPonensWitness,
    LeftInjectionWitness,
    RightInjectionWitness,
    CaseAnalysisWitness,
    AbsurdityWitness,
    TransportProofWitness,
)
from deppy.proof.decreases_checker import DecreasesResult, DecreasesVerdict


# ---------------------------------------------------------------------------
# Rendering configuration
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RenderConfig:
    """Configuration for proof rendering.

    Attributes:
        _indent_size: Number of spaces per indentation level.
        _max_width: Maximum line width.
        _show_site_ids: Whether to include site IDs in output.
        _show_trust_levels: Whether to include trust levels.
        _show_line_numbers: Whether to include source line numbers.
        _use_unicode: Whether to use unicode symbols.
        _verbose: Whether to include extra detail.
    """

    _indent_size: int = 2
    _max_width: int = 80
    _show_site_ids: bool = True
    _show_trust_levels: bool = True
    _show_line_numbers: bool = True
    _use_unicode: bool = True
    _verbose: bool = False

    @property
    def indent_size(self) -> int:
        return self._indent_size

    @property
    def max_width(self) -> int:
        return self._max_width


_DEFAULT_CONFIG = RenderConfig()


# ---------------------------------------------------------------------------
# Symbol tables
# ---------------------------------------------------------------------------


_UNICODE_SYMBOLS = {
    "check": "\u2713",
    "cross": "\u2717",
    "arrow": "\u2192",
    "double_arrow": "\u21d2",
    "bullet": "\u2022",
    "dash": "\u2500",
    "vbar": "\u2502",
    "corner": "\u2514",
    "tee": "\u251c",
    "forall": "\u2200",
    "exists": "\u2203",
    "and": "\u2227",
    "or": "\u2228",
    "not": "\u00ac",
    "equiv": "\u2261",
    "leq": "\u2264",
    "geq": "\u2265",
    "neq": "\u2260",
    "bot": "\u22a5",
    "top": "\u22a4",
}

_ASCII_SYMBOLS = {
    "check": "[ok]",
    "cross": "[FAIL]",
    "arrow": "->",
    "double_arrow": "=>",
    "bullet": "*",
    "dash": "-",
    "vbar": "|",
    "corner": "`-",
    "tee": "|-",
    "forall": "forall",
    "exists": "exists",
    "and": "/\\",
    "or": "\\/",
    "not": "~",
    "equiv": "==",
    "leq": "<=",
    "geq": ">=",
    "neq": "!=",
    "bot": "_|_",
    "top": "T",
}


def _sym(name: str, config: RenderConfig = _DEFAULT_CONFIG) -> str:
    """Get a symbol, using unicode or ASCII based on config."""
    table = _UNICODE_SYMBOLS if config._use_unicode else _ASCII_SYMBOLS
    return table.get(name, name)


# ---------------------------------------------------------------------------
# Trust level rendering
# ---------------------------------------------------------------------------


_TRUST_DISPLAY = {
    TrustLevel.PROOF_BACKED: ("PROOF", "proof-backed"),
    TrustLevel.TRUSTED_AUTO: ("AUTO", "auto-verified"),
    TrustLevel.BOUNDED_AUTO: ("BOUNDED", "bounded-auto"),
    TrustLevel.TRACE_BACKED: ("TRACE", "trace-backed"),
    TrustLevel.ASSUMED: ("ASSUMED", "assumed"),
    TrustLevel.RESIDUAL: ("RESIDUAL", "residual"),
}


def _render_trust(trust: TrustLevel, config: RenderConfig = _DEFAULT_CONFIG) -> str:
    """Render a trust level as a short string."""
    short, _long = _TRUST_DISPLAY.get(trust, ("?", "unknown"))
    return short


def _render_trust_long(trust: TrustLevel) -> str:
    """Render a trust level as a descriptive string."""
    _short, long = _TRUST_DISPLAY.get(trust, ("?", "unknown"))
    return long


# ---------------------------------------------------------------------------
# Goal status rendering
# ---------------------------------------------------------------------------


_STATUS_DISPLAY = {
    GoalStatus.OPEN: ("OPEN", "open"),
    GoalStatus.IN_PROGRESS: ("PROG", "in progress"),
    GoalStatus.DISCHARGED: ("DONE", "discharged"),
    GoalStatus.FAILED: ("FAIL", "failed"),
    GoalStatus.DEFERRED: ("DEFER", "deferred"),
    GoalStatus.TRIVIAL: ("TRIV", "trivial"),
    GoalStatus.CANCELLED: ("CANCEL", "cancelled"),
}


def _render_status_icon(status: GoalStatus, config: RenderConfig = _DEFAULT_CONFIG) -> str:
    """Render a status as a short icon."""
    if status in (GoalStatus.DISCHARGED, GoalStatus.TRIVIAL):
        return _sym("check", config)
    if status == GoalStatus.FAILED:
        return _sym("cross", config)
    short, _ = _STATUS_DISPLAY.get(status, ("?", "?"))
    return f"[{short}]"


# ---------------------------------------------------------------------------
# Indentation helper
# ---------------------------------------------------------------------------


def _indent(text: str, level: int, config: RenderConfig = _DEFAULT_CONFIG) -> str:
    """Indent text by the given number of levels."""
    prefix = " " * (level * config.indent_size)
    return textwrap.indent(text, prefix)


# ---------------------------------------------------------------------------
# Proof renderer
# ---------------------------------------------------------------------------


class ProofRenderer:
    """Render proof goals, terms, and progress as human-readable text.

    Produces structured, indented output suitable for terminal display
    or logging.

    Attributes:
        _config: Rendering configuration.
    """

    def __init__(self, config: Optional[RenderConfig] = None) -> None:
        self._config: RenderConfig = config or _DEFAULT_CONFIG

    @property
    def config(self) -> RenderConfig:
        return self._config

    # -- Goal rendering ----------------------------------------------------

    def render_goal(self, goal: ProofGoal) -> str:
        """Render a proof goal as human-readable text."""
        lines: List[str] = []
        icon = _render_status_icon(goal.status, self._config)
        header = f"{icon} Goal {goal.goal_id}"
        if self._config._show_trust_levels:
            header += f" [{_render_trust(goal.trust_level, self._config)}]"
        lines.append(header)

        # Obligation info
        obl = goal.obligation
        lines.append(f"  Proposition: {self._render_prop(obl.prop)}")
        if self._config._show_site_ids:
            lines.append(f"  Site: {obl.site_id}")
        if self._config._show_line_numbers and obl.source_location:
            lines.append(f"  Location: {obl.source_location}")

        # Status details
        status_short, status_long = _STATUS_DISPLAY.get(
            goal.status, ("?", "unknown")
        )
        lines.append(f"  Status: {status_long}")

        if goal.priority != GoalPriority.NORMAL:
            lines.append(f"  Priority: {goal.priority.name}")

        if goal.attempts > 0:
            lines.append(f"  Attempts: {goal.attempts}")

        elapsed = goal.elapsed_seconds
        if elapsed is not None:
            lines.append(f"  Elapsed: {elapsed:.3f}s")

        # Proof term (if discharged)
        if goal.proof_term is not None:
            proof_text = self.render_proof(goal.proof_term)
            lines.append(f"  Proof:")
            lines.append(_indent(proof_text, 2, self._config))

        # Notes
        if goal._notes:
            lines.append(f"  Notes: {goal._notes}")

        # Children
        if goal.has_children:
            lines.append(f"  Sub-goals: {len(goal._children_ids)}")

        return "\n".join(lines)

    def render_goals(self, goals: List[ProofGoal]) -> str:
        """Render multiple goals."""
        if not goals:
            return "No proof goals."
        parts = [self.render_goal(g) for g in goals]
        return "\n\n".join(parts)

    # -- Proof term rendering ----------------------------------------------

    def render_proof(self, proof_term: ProofTerm, depth: int = 0) -> str:
        """Render a proof term as human-readable text."""
        if depth > 20:
            return "..."

        if isinstance(proof_term, ReflProof):
            term_str = f"({proof_term.term!r})" if proof_term.term is not None else ""
            return f"refl{term_str}"

        if isinstance(proof_term, AssumptionProof):
            return f"assume({proof_term.name})"

        if isinstance(proof_term, RuntimeCheckProof):
            return f"runtime_check({proof_term.check_description})"

        if isinstance(proof_term, StaticProof):
            return f"static({proof_term.method}: {proof_term.detail})"

        if isinstance(proof_term, TransitivityProof):
            left = self.render_proof(proof_term.left, depth + 1)
            right = self.render_proof(proof_term.right, depth + 1)
            return f"trans(\n{_indent(left, depth + 1, self._config)},\n{_indent(right, depth + 1, self._config)})"

        if isinstance(proof_term, SymmetryProof):
            inner = self.render_proof(proof_term.inner, depth + 1)
            return f"sym({inner})"

        if isinstance(proof_term, CongruenceProof):
            inner = self.render_proof(proof_term.inner, depth + 1)
            return f"cong({proof_term.function_name}, {inner})"

        if isinstance(proof_term, CompositeProof):
            parts = [
                self.render_proof(p, depth + 1) for p in proof_term.sub_proofs
            ]
            if len(parts) <= 2 and all(len(p) < 40 for p in parts):
                joined = ", ".join(parts)
                return f"{proof_term.combiner}({joined})"
            formatted = ",\n".join(
                _indent(p, depth + 1, self._config) for p in parts
            )
            return f"{proof_term.combiner}(\n{formatted})"

        # Combinator types
        if isinstance(proof_term, TransitivityWitness):
            chain = [
                self.render_proof(p, depth + 1) for p in proof_term.chain
            ]
            if len(chain) <= 3 and all(len(c) < 30 for c in chain):
                return f"trans({' ; '.join(chain)})"
            steps = "\n".join(
                f"{_indent(_sym('tee', self._config) + ' ', depth + 1, self._config)}{c}"
                for c in chain
            )
            return f"trans(\n{steps})"

        if isinstance(proof_term, SymmetryWitness):
            inner = self.render_proof(proof_term._inner, depth + 1)
            return f"sym({inner})"

        if isinstance(proof_term, CongruenceWitness):
            inner = self.render_proof(proof_term._inner, depth + 1)
            return f"cong({proof_term._function_name}, {inner})"

        if isinstance(proof_term, PairWitness):
            first = self.render_proof(proof_term._first, depth + 1)
            second = self.render_proof(proof_term._second, depth + 1)
            return f"{_sym('and', self._config)}-intro({first}, {second})"

        if isinstance(proof_term, ProjectionWitness):
            pair = self.render_proof(proof_term._pair, depth + 1)
            proj = "fst" if proof_term._index == 0 else "snd"
            return f"{proj}({pair})"

        if isinstance(proof_term, ModusPonensWitness):
            impl = self.render_proof(proof_term._implication, depth + 1)
            ante = self.render_proof(proof_term._antecedent, depth + 1)
            return f"mp({impl}, {ante})"

        if isinstance(proof_term, UniversalWitness):
            body = self.render_proof(proof_term._body_proof, depth + 1)
            type_str = repr(proof_term._binder_type) if proof_term._binder_type else "?"
            return f"{_sym('forall', self._config)} {proof_term._binder_name}:{type_str}. {body}"

        if isinstance(proof_term, ExistentialPackWitness):
            prop_proof = self.render_proof(proof_term._property_proof, depth + 1)
            return (
                f"{_sym('exists', self._config)} {proof_term._binder_name} = "
                f"{proof_term._witness_term!r}. {prop_proof}"
            )

        if isinstance(proof_term, LeftInjectionWitness):
            inner = self.render_proof(proof_term._inner, depth + 1)
            return f"inl({inner})"

        if isinstance(proof_term, RightInjectionWitness):
            inner = self.render_proof(proof_term._inner, depth + 1)
            return f"inr({inner})"

        if isinstance(proof_term, CaseAnalysisWitness):
            disj = self.render_proof(proof_term._disjunction, depth + 1)
            left = self.render_proof(proof_term._left_case, depth + 1)
            right = self.render_proof(proof_term._right_case, depth + 1)
            return (
                f"cases({disj},\n"
                f"{_indent('left: ' + left, depth + 1, self._config)},\n"
                f"{_indent('right: ' + right, depth + 1, self._config)})"
            )

        if isinstance(proof_term, AbsurdityWitness):
            inner = self.render_proof(proof_term._false_proof, depth + 1)
            return f"absurd({inner})"

        if isinstance(proof_term, TransportProofWitness):
            eq = self.render_proof(proof_term._equality_proof, depth + 1)
            src = repr(proof_term._source_type) if proof_term._source_type else "?"
            tgt = repr(proof_term._target_type) if proof_term._target_type else "?"
            return f"transport({src} {_sym('arrow', self._config)} {tgt}, {eq})"

        # Fallback
        return proof_term.description()

    # -- Obligation rendering ----------------------------------------------

    def render_obligation(self, obligation: ProofObligation) -> str:
        """Render a proof obligation as human-readable text."""
        lines: List[str] = []

        status_icon = {
            ObligationStatus.GENERATED: "[?]",
            ObligationStatus.SOLVER_ATTEMPTED: "[~]",
            ObligationStatus.DISCHARGED: _sym("check", self._config),
            ObligationStatus.TRIAGED: "[!]",
            ObligationStatus.PROOF_PROVIDED: "[P]",
            ObligationStatus.VERIFIED: _sym("check", self._config),
            ObligationStatus.EXPORTED: "[E]",
            ObligationStatus.RESIDUAL: "[R]",
        }.get(obligation.status, "[?]")

        lines.append(f"{status_icon} Obligation at {obligation.site_id}")
        lines.append(f"  Proposition: {self._render_prop(obligation.prop)}")
        lines.append(f"  Status: {obligation.status.value}")

        if obligation.source_location:
            lines.append(f"  Location: {obligation.source_location}")

        if obligation.context:
            kind = obligation.context.get("kind", "")
            if kind:
                lines.append(f"  Kind: {kind}")
            func = obligation.context.get("function", "")
            if func:
                lines.append(f"  Function: {func}")

        if obligation.proof is not None:
            proof_text = self.render_proof(obligation.proof)
            lines.append(f"  Proof: {proof_text}")

        return "\n".join(lines)

    def render_obligations(self, obligations: List[ProofObligation]) -> str:
        """Render multiple obligations."""
        if not obligations:
            return "No proof obligations."
        parts = [self.render_obligation(o) for o in obligations]
        header = f"Proof Obligations ({len(obligations)} total):"
        return header + "\n\n" + "\n\n".join(parts)

    # -- Progress rendering ------------------------------------------------

    def render_progress(self, progress: ProofProgress) -> str:
        """Render a proof progress report as human-readable text."""
        lines: List[str] = []

        # Header bar
        bar_width = 30
        if progress.total > 0:
            filled = int(bar_width * progress.completion_ratio)
            bar = "#" * filled + "-" * (bar_width - filled)
        else:
            bar = "-" * bar_width
        pct = progress.completion_ratio * 100
        lines.append(f"Proof Progress: [{bar}] {pct:.0f}%")
        lines.append("")

        # Summary counts
        lines.append(f"  Total goals:    {progress.total}")
        if progress.discharged > 0:
            lines.append(
                f"  {_sym('check', self._config)} Discharged:  {progress.discharged}"
            )
        if progress.trivial > 0:
            lines.append(
                f"  {_sym('check', self._config)} Trivial:     {progress.trivial}"
            )
        if progress.open > 0:
            lines.append(f"  [ ] Open:        {progress.open}")
        if progress.in_progress > 0:
            lines.append(f"  [~] In progress: {progress.in_progress}")
        if progress.failed > 0:
            lines.append(
                f"  {_sym('cross', self._config)} Failed:      {progress.failed}"
            )
        if progress.deferred > 0:
            lines.append(f"  [>] Deferred:    {progress.deferred}")
        if progress.cancelled > 0:
            lines.append(f"  [-] Cancelled:   {progress.cancelled}")

        # Trust distribution
        if progress._trust_distribution:
            lines.append("")
            lines.append("  Trust distribution:")
            for trust_name, count in sorted(progress._trust_distribution.items()):
                lines.append(f"    {trust_name}: {count}")

        # Priority distribution
        if progress._priority_distribution:
            lines.append("")
            lines.append("  Open goals by priority:")
            for pri_name, count in sorted(progress._priority_distribution.items()):
                lines.append(f"    {pri_name}: {count}")

        # Timing
        if progress._average_elapsed > 0:
            lines.append("")
            lines.append(
                f"  Avg discharge time: {progress._average_elapsed:.3f}s"
            )

        # Completion status
        lines.append("")
        if progress.is_complete:
            if progress.has_failures:
                lines.append(
                    f"  Status: Complete with {progress.failed} failure(s)"
                )
            else:
                lines.append("  Status: All goals discharged!")
        else:
            remaining = progress.open + progress.in_progress
            lines.append(f"  Status: {remaining} goal(s) remaining")

        return "\n".join(lines)

    # -- Decreases result rendering ----------------------------------------

    def render_decreases(self, result: DecreasesResult) -> str:
        """Render a decreases check result."""
        lines: List[str] = []

        verdict_icon = {
            DecreasesVerdict.VERIFIED: _sym("check", self._config),
            DecreasesVerdict.LIKELY: "~",
            DecreasesVerdict.UNKNOWN: "?",
            DecreasesVerdict.FAILED: _sym("cross", self._config),
        }.get(result.verdict, "?")

        lines.append(
            f"{verdict_icon} Termination check: {result.verdict.value}"
        )
        lines.append(
            f"  Ranking function: {result.ranking_function_text}"
        )
        lines.append(f"  Measure kind: {result.measure_kind.value}")

        if result.recursive_calls:
            lines.append(
                f"  Recursive calls: {len(result.recursive_calls)}"
            )
        if result.loop_iterations:
            lines.append(f"  Loops: {len(result.loop_iterations)}")

        if result.evidence:
            lines.append("  Evidence:")
            for ev in result.evidence:
                icon = _sym("check", self._config) if ev.verified else "?"
                lines.append(f"    {icon} {ev.decrease_reason}")

        if result.unverified_calls:
            lines.append("  Unverified calls:")
            for call in result.unverified_calls:
                lines.append(f"    {_sym('cross', self._config)} {call}")

        lines.append(f"  {result.explanation}")
        return "\n".join(lines)

    # -- Discharged goal rendering -----------------------------------------

    def render_discharged(self, discharged: DischargedGoal) -> str:
        """Render a discharged goal summary."""
        proof_text = self.render_proof(discharged.proof_term)
        trust = _render_trust(discharged.trust_level, self._config)
        return (
            f"{_sym('check', self._config)} {discharged.goal_id} "
            f"[{trust}] ({discharged.elapsed_seconds:.3f}s, "
            f"{discharged.attempts} attempt(s))\n"
            f"  Proof: {proof_text}"
        )

    def render_discharged_list(self, goals: List[DischargedGoal]) -> str:
        """Render a list of discharged goals."""
        if not goals:
            return "No discharged goals."
        header = f"Discharged Goals ({len(goals)}):"
        parts = [self.render_discharged(g) for g in goals]
        return header + "\n\n" + "\n\n".join(parts)

    # -- Summary rendering -------------------------------------------------

    def render_summary(
        self,
        goals: List[ProofGoal],
        progress: ProofProgress,
    ) -> str:
        """Render a combined summary of goals and progress."""
        lines: List[str] = []

        lines.append("=" * min(60, self._config.max_width))
        lines.append("PROOF STATE SUMMARY")
        lines.append("=" * min(60, self._config.max_width))
        lines.append("")
        lines.append(self.render_progress(progress))

        open_goals = [g for g in goals if g.is_open]
        if open_goals:
            lines.append("")
            lines.append("-" * min(40, self._config.max_width))
            lines.append(f"Open Goals ({len(open_goals)}):")
            lines.append("-" * min(40, self._config.max_width))
            for g in open_goals[:10]:
                lines.append("")
                lines.append(self.render_goal(g))
            if len(open_goals) > 10:
                lines.append(f"\n... and {len(open_goals) - 10} more")

        failed_goals = [g for g in goals if g.status == GoalStatus.FAILED]
        if failed_goals:
            lines.append("")
            lines.append("-" * min(40, self._config.max_width))
            lines.append(f"Failed Goals ({len(failed_goals)}):")
            lines.append("-" * min(40, self._config.max_width))
            for g in failed_goals[:5]:
                lines.append("")
                lines.append(self.render_goal(g))

        lines.append("")
        lines.append("=" * min(60, self._config.max_width))
        return "\n".join(lines)

    # -- Helpers -----------------------------------------------------------

    def _render_prop(self, prop: Any) -> str:
        """Render a proposition value as a string."""
        if isinstance(prop, tuple):
            if len(prop) == 3 and prop[0] == "eq":
                return f"{prop[1]!r} = {prop[2]!r}"
            if len(prop) == 3 and prop[0] == "subtype":
                return f"{prop[1]!r} <: {prop[2]!r}"
            if len(prop) >= 2 and prop[0] == "requires":
                return f"requires: {prop[1]}"
            if len(prop) >= 2 and prop[0] == "ensures":
                return f"ensures: {prop[1]}"
            if len(prop) >= 2 and prop[0] == "invariant":
                return f"invariant: {prop[1]}"
            if len(prop) >= 2 and prop[0] == "theorem":
                return f"theorem: {prop[1]}"
            if len(prop) >= 2 and prop[0] == "lemma":
                return f"lemma: {prop[1]}"
            if len(prop) >= 2 and prop[0] == "decreases":
                return f"decreases: {prop[1]}"
            parts = ", ".join(repr(p) for p in prop)
            return f"({parts})"
        if isinstance(prop, str):
            return prop
        return repr(prop)
