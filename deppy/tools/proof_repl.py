"""
Deppy Proof REPL — Interactive proof mode for stepping through proofs.

Goes beyond F*'s Meta-F* by providing an interactive, exploratory proof
experience in the terminal.  Every command mutates proof state and can be
undone.  Proofs can be saved/replayed as transcripts.

Usage (interactive)::

    python -m deppy.tools.proof_repl

Usage (programmatic)::

    repl = ProofREPL()
    out  = repl.process_command('goal "x + 0 == x"')
"""
from __future__ import annotations

import copy
import json
import os
import re
import sys
import time
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, TextIO

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyIntType, PyListType,
    PiType, RefinementType,
    Var, Literal,
)
from deppy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Sym, Trans, Cong, Z3Proof,
    NatInduction, ListInduction, Cases,
    AxiomInvocation, Unfold, Rewrite, Structural,
    Assume, Cut, AxiomEntry,
)
from deppy.axioms.library_axioms import (
    AxiomRegistry, LibraryAxiom,
    BuiltinAxioms, SympyAxioms, NumpyAxioms, TorchAxioms,
    default_registry,
)

# ═══════════════════════════════════════════════════════════════════
# ANSI Color Helpers
# ═══════════════════════════════════════════════════════════════════

_NO_COLOR = os.environ.get("NO_COLOR") is not None


def _green(s: str) -> str:
    return s if _NO_COLOR else f"\033[32m{s}\033[0m"


def _red(s: str) -> str:
    return s if _NO_COLOR else f"\033[31m{s}\033[0m"


def _yellow(s: str) -> str:
    return s if _NO_COLOR else f"\033[33m{s}\033[0m"


def _cyan(s: str) -> str:
    return s if _NO_COLOR else f"\033[36m{s}\033[0m"


def _bold(s: str) -> str:
    return s if _NO_COLOR else f"\033[1m{s}\033[0m"


def _dim(s: str) -> str:
    return s if _NO_COLOR else f"\033[2m{s}\033[0m"


# ═══════════════════════════════════════════════════════════════════
# Data Structures
# ═══════════════════════════════════════════════════════════════════

@dataclass
class GoalState:
    """A single proof goal with its formula, context, and optional label."""
    formula: str
    context: dict[str, str] = field(default_factory=dict)
    label: str = ""
    hypotheses: list[str] = field(default_factory=list)


@dataclass
class ProvedGoal:
    """A goal that has been proved, with the method used."""
    formula: str
    method: str
    trust: TrustLevel = TrustLevel.KERNEL
    is_sorry: bool = False


@dataclass
class REPLState:
    """Snapshot of REPL state for undo."""
    goals: list[GoalState]
    proved: list[ProvedGoal]
    context_vars: dict[str, str]
    step_description: str


# ═══════════════════════════════════════════════════════════════════
# Proof Transcript — save / replay
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProofTranscript:
    """A recorded proof session that can be replayed."""
    commands: list[str] = field(default_factory=list)
    results: list[str] = field(default_factory=list)
    final_trust: TrustLevel = TrustLevel.UNTRUSTED

    def save(self, path: str) -> None:
        """Save the transcript to a JSON file."""
        data = {
            "commands": self.commands,
            "results": self.results,
            "final_trust": self.final_trust.name,
        }
        with open(path, "w") as f:
            json.dump(data, f, indent=2)

    def replay(self, repl: ProofREPL) -> bool:
        """Replay all commands against *repl*.  Returns True if all succeed."""
        for cmd in self.commands:
            out = repl.process_command(cmd)
            if out.startswith("Error"):
                return False
        return True

    @classmethod
    def load(cls, path: str) -> ProofTranscript:
        """Load a transcript from a JSON file."""
        with open(path) as f:
            data = json.load(f)
        return cls(
            commands=data["commands"],
            results=data.get("results", []),
            final_trust=TrustLevel[data.get("final_trust", "UNTRUSTED")],
        )


# ═══════════════════════════════════════════════════════════════════
# Goal Printer
# ═══════════════════════════════════════════════════════════════════

class GoalPrinter:
    """Pretty-print proof goals, context, and proof state."""

    def format_goal(self, goal: GoalState, index: int) -> str:
        """Format a single goal with its index."""
        label = goal.label or f"Goal {index}"
        parts: list[str] = []
        if goal.context:
            ctx_str = ", ".join(f"{k} : {v}" for k, v in goal.context.items())
            parts.append(f"  {_dim(ctx_str)}")
        if goal.hypotheses:
            for h in goal.hypotheses:
                parts.append(f"  {_dim('IH: ' + h)}")
        parts.append(f"  {_bold(label)}: {goal.formula}")
        return "\n".join(parts)

    def format_context(self, ctx_vars: dict[str, str]) -> str:
        """Format the current typing context."""
        if not ctx_vars:
            return "  (empty context)"
        lines = []
        for name, ty in ctx_vars.items():
            lines.append(f"  {name} : {ty}")
        return "\n".join(lines)

    def format_proof_tree(self, proved: list[ProvedGoal]) -> str:
        """Format the list of proved goals as a tree."""
        if not proved:
            return "  (no goals proved yet)"
        lines = []
        for i, p in enumerate(proved, 1):
            trust_sym = "✓" if not p.is_sorry else "⚠"
            trust_tag = p.trust.name if not p.is_sorry else "UNTRUSTED"
            marker = _green(trust_sym) if not p.is_sorry else _yellow(trust_sym)
            lines.append(f"  {marker} {p.formula}  [{trust_tag}] by {p.method}")
        return "\n".join(lines)

    def format_status(self, goals: list[GoalState],
                      proved: list[ProvedGoal]) -> str:
        """Format an overview of the proof state."""
        total = len(goals) + len(proved)
        n_proved = len(proved)
        n_sorry = sum(1 for p in proved if p.is_sorry)
        lines = [f"  Proved: {n_proved} of {total} goals"]
        if n_sorry:
            lines.append(f"  {_yellow('⚠')} {n_sorry} admitted (sorry)")
        if goals:
            lines.append("  Remaining:")
            printer = GoalPrinter()
            for i, g in enumerate(goals, n_proved + 1):
                lines.append("  " + printer.format_goal(g, i))
        else:
            lines.append(f"  {_green('All goals proved.')}")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# Command Parser
# ═══════════════════════════════════════════════════════════════════

class CommandParser:
    """Parse REPL commands with tab completion support."""

    COMMANDS: dict[str, str] = {
        "goal": "Set a new proof goal",
        "intro": "Introduce a variable",
        "z3": "Discharge current goal to Z3",
        "axiom": "Apply a named axiom",
        "induction": "Apply induction on a variable",
        "cases": "Case analysis",
        "unfold": "Unfold a definition",
        "rewrite": "Rewrite using a lemma",
        "apply": "Apply a proof term",
        "have": "Introduce a sub-lemma",
        "show": "Show current proof state",
        "check": "Quick Z3 check",
        "search": "Search axioms",
        "load": "Load library axioms",
        "undo": "Undo last step",
        "sorry": "Admit current goal (untrusted)",
        "qed": "Complete the proof",
        "save": "Save proof transcript",
        "history": "Show proof history",
        "context": "Show context",
        "assumptions": "Show assumptions",
        "help": "Show help",
        "reset": "Reset state",
        "exit": "Exit REPL",
    }

    def parse(self, line: str) -> tuple[str, list[str]]:
        """Parse a command line into (command, args).

        Handles quoted arguments so ``goal "x + 0 == x"`` parses correctly.
        """
        line = line.strip()
        if not line:
            return ("", [])

        # Tokenize respecting quotes
        tokens: list[str] = []
        current = ""
        in_quote: str | None = None
        for ch in line:
            if in_quote:
                if ch == in_quote:
                    in_quote = None
                else:
                    current += ch
            elif ch in ('"', "'"):
                in_quote = ch
            elif ch == " ":
                if current:
                    tokens.append(current)
                    current = ""
            else:
                current += ch
        if current:
            tokens.append(current)

        if not tokens:
            return ("", [])
        return (tokens[0].lower(), tokens[1:])

    def complete(self, prefix: str) -> list[str]:
        """Return command names matching *prefix*."""
        return [c for c in self.COMMANDS if c.startswith(prefix.lower())]


# ═══════════════════════════════════════════════════════════════════
# The Proof REPL
# ═══════════════════════════════════════════════════════════════════

class ProofREPL:
    """Interactive proof REPL for Deppy."""

    BANNER = (
        f"{_bold('Deppy Proof REPL')} — interactive proof mode\n"
        f"Type {_cyan('help')} for commands, {_cyan('exit')} to quit.\n"
    )

    def __init__(self, kernel: ProofKernel | None = None) -> None:
        self.kernel = kernel or ProofKernel()
        self._goals: list[GoalState] = []
        self._proved: list[ProvedGoal] = []
        self._context_vars: dict[str, str] = {}
        self._undo_stack: list[REPLState] = []
        self._transcript = ProofTranscript()
        self._axiom_registry = AxiomRegistry()
        self._parser = CommandParser()
        self._printer = GoalPrinter()
        self._history: list[str] = []
        self._goal_counter: int = 0

        # Load builtins by default
        BuiltinAxioms.register_all(self._axiom_registry)
        self._axiom_registry.install_into_kernel(self.kernel)

    # ── snapshot / undo ───────────────────────────────────────────

    def _snapshot(self, description: str) -> None:
        """Push current state onto the undo stack."""
        self._undo_stack.append(REPLState(
            goals=[GoalState(
                formula=g.formula,
                context=dict(g.context),
                label=g.label,
                hypotheses=list(g.hypotheses),
            ) for g in self._goals],
            proved=[ProvedGoal(
                formula=p.formula,
                method=p.method,
                trust=p.trust,
                is_sorry=p.is_sorry,
            ) for p in self._proved],
            context_vars=dict(self._context_vars),
            step_description=description,
        ))

    def _restore(self, state: REPLState) -> None:
        """Restore state from a snapshot."""
        self._goals = state.goals
        self._proved = state.proved
        self._context_vars = state.context_vars

    # ── public API ────────────────────────────────────────────────

    def start(self) -> None:
        """Start the interactive REPL (blocks until exit)."""
        # Set up readline if available
        try:
            import readline

            def _completer(text: str, state: int) -> str | None:
                matches = self._parser.complete(text)
                return matches[state] if state < len(matches) else None

            readline.set_completer(_completer)
            readline.parse_and_bind("tab: complete")
        except ImportError:
            pass

        print(self.BANNER)
        while True:
            try:
                line = input(_cyan("deppy> "))
            except (EOFError, KeyboardInterrupt):
                print()
                break
            output = self.process_command(line)
            if output:
                print(output)
            if line.strip().lower() == "exit":
                break

    def process_command(self, line: str) -> str:
        """Process a single REPL command.  Returns output string."""
        cmd, args = self._parser.parse(line)
        if not cmd:
            return ""

        self._history.append(line.strip())
        self._transcript.commands.append(line.strip())

        handler = getattr(self, f"_cmd_{cmd}", None)
        if handler is None:
            result = f"Error: unknown command '{cmd}'.  Type 'help' for commands."
        else:
            try:
                result = handler(args)
            except Exception as e:
                result = f"Error: {e}"

        self._transcript.results.append(result)
        return result

    # ── goal management ───────────────────────────────────────────

    def _current_goal(self) -> GoalState | None:
        return self._goals[0] if self._goals else None

    def _cmd_goal(self, args: list[str]) -> str:
        """Set a new proof goal."""
        if not args:
            return "Error: usage: goal \"<formula>\""
        formula = " ".join(args)
        self._snapshot(f"goal \"{formula}\"")
        self._goal_counter += 1
        g = GoalState(formula=formula, label=f"Goal {self._goal_counter}")
        self._goals.append(g)
        return self._printer.format_goal(g, self._goal_counter)

    def _cmd_show(self, args: list[str]) -> str:
        """Show current proof state."""
        if not self._goals and not self._proved:
            return "  No active proof."
        return self._printer.format_status(self._goals, self._proved)

    def _cmd_context(self, args: list[str]) -> str:
        """Show current typing context."""
        return self._printer.format_context(self._context_vars)

    def _cmd_assumptions(self, args: list[str]) -> str:
        """Show available assumptions (hypotheses on current goal)."""
        goal = self._current_goal()
        if goal is None:
            return "  No active goal."
        lines = []
        if goal.context:
            for name, ty in goal.context.items():
                lines.append(f"  {name} : {ty}")
        if goal.hypotheses:
            for h in goal.hypotheses:
                lines.append(f"  IH: {h}")
        if not lines:
            lines.append("  (no assumptions)")
        return "\n".join(lines)

    # ── tactics ───────────────────────────────────────────────────

    def _cmd_intro(self, args: list[str]) -> str:
        """Introduce a variable (peel off a leading ∀)."""
        goal = self._current_goal()
        if goal is None:
            return "Error: no active goal."
        if not args:
            return "Error: usage: intro <var_name> [: <type>]"

        var_name = args[0]
        var_type = args[2] if len(args) >= 3 and args[1] == ":" else "auto"

        self._snapshot(f"intro {var_name}")

        # Try to strip ∀ quantifier from the formula
        formula = goal.formula
        new_formula = self._strip_forall(formula, var_name)

        if var_type == "auto":
            var_type = self._infer_var_type(formula, var_name)

        goal.context[var_name] = var_type
        self._context_vars[var_name] = var_type
        goal.formula = new_formula

        lines = [f"  {var_name} : {var_type}"]
        lines.append(self._printer.format_goal(goal, self._goal_counter))
        return "\n".join(lines)

    def _cmd_z3(self, args: list[str]) -> str:
        """Discharge current goal to Z3."""
        goal = self._current_goal()
        if goal is None:
            return "Error: no active goal."

        self._snapshot(f"z3 on {goal.label}")
        t0 = time.monotonic()

        proved = self._try_z3(goal.formula)
        elapsed = time.monotonic() - t0

        if proved:
            label = goal.label
            self._goals.pop(0)
            self._proved.append(ProvedGoal(
                formula=goal.formula,
                method=f"Z3 ({elapsed:.3f}s)",
                trust=TrustLevel.Z3_VERIFIED,
            ))
            return f"  {_green('✓')} {label} proved by Z3 ({elapsed:.3f}s)"
        else:
            # Undo the snapshot since the tactic failed
            self._undo_stack.pop()
            return f"  {_red('✗')} Z3 could not discharge {goal.label}"

    def _cmd_axiom(self, args: list[str]) -> str:
        """Apply a named axiom:  axiom <name> [<module>]"""
        goal = self._current_goal()
        if goal is None:
            return "Error: no active goal."
        if not args:
            return "Error: usage: axiom <name> [<module>]"

        axiom_name = args[0]
        module = args[1] if len(args) >= 2 else ""

        # Look up in registry
        ax = self._find_axiom(axiom_name, module)
        if ax is None:
            return f"Error: axiom '{axiom_name}' not found.  Use 'search' to find axioms."

        self._snapshot(f"axiom {ax.qualified_name}")
        label = goal.label
        self._goals.pop(0)
        self._proved.append(ProvedGoal(
            formula=goal.formula,
            method=f"axiom {ax.qualified_name}",
            trust=TrustLevel.AXIOM_TRUSTED,
        ))
        return f"  {_green('✓')} {label} proved by axiom {ax.qualified_name}"

    def _cmd_induction(self, args: list[str]) -> str:
        """Structural induction on a variable."""
        goal = self._current_goal()
        if goal is None:
            return "Error: no active goal."
        if not args:
            return "Error: usage: induction <var>"

        var = args[0]
        var_type = goal.context.get(var, self._context_vars.get(var, "list"))

        self._snapshot(f"induction {var}")

        label = goal.label
        formula = goal.formula
        self._goals.pop(0)

        base_formula = self._make_base_case(formula, var, var_type)
        step_formula = self._make_step_case(formula, var, var_type)
        ih = formula

        sub_idx = self._goal_counter
        base_goal = GoalState(
            formula=base_formula,
            context=dict(goal.context),
            label=f"Subgoal {sub_idx}.1 (base)",
        )
        step_goal = GoalState(
            formula=step_formula,
            context=dict(goal.context),
            label=f"Subgoal {sub_idx}.2 (step)",
            hypotheses=[ih],
        )

        self._goals = [base_goal, step_goal] + self._goals

        lines = [self._printer.format_goal(base_goal, sub_idx)]
        lines.append(self._printer.format_goal(step_goal, sub_idx))
        return "\n".join(lines)

    def _cmd_cases(self, args: list[str]) -> str:
        """Case analysis on a variable or expression."""
        goal = self._current_goal()
        if goal is None:
            return "Error: no active goal."
        if not args:
            return "Error: usage: cases <var> [<case1> <case2> ...]"

        var = args[0]
        case_names = args[1:] if len(args) > 1 else ["True", "False"]

        self._snapshot(f"cases {var}")

        label = goal.label
        formula = goal.formula
        self._goals.pop(0)

        sub_idx = self._goal_counter
        new_goals = []
        for i, case in enumerate(case_names, 1):
            g = GoalState(
                formula=formula,
                context={**goal.context, var: case},
                label=f"Subgoal {sub_idx}.{i} ({var} = {case})",
            )
            new_goals.append(g)

        self._goals = new_goals + self._goals

        lines = []
        for g in new_goals:
            lines.append(self._printer.format_goal(g, sub_idx))
        return "\n".join(lines)

    def _cmd_unfold(self, args: list[str]) -> str:
        """Unfold a definition in the current goal."""
        goal = self._current_goal()
        if goal is None:
            return "Error: no active goal."
        if not args:
            return "Error: usage: unfold <definition>"

        defn = args[0]
        self._snapshot(f"unfold {defn}")

        new_formula = self._unfold_definition(goal.formula, defn)
        goal.formula = new_formula
        return self._printer.format_goal(goal, self._goal_counter)

    def _cmd_rewrite(self, args: list[str]) -> str:
        """Rewrite using a lemma or equation."""
        goal = self._current_goal()
        if goal is None:
            return "Error: no active goal."
        if not args:
            return "Error: usage: rewrite <lemma_name_or_equation>"

        lemma = " ".join(args)
        self._snapshot(f"rewrite {lemma}")

        # Try to find it as an axiom and apply its equation
        ax = self._find_axiom(lemma, "")
        if ax is not None:
            goal.formula = self._apply_rewrite(goal.formula, ax.statement)
            return self._printer.format_goal(goal, self._goal_counter)

        # Otherwise treat the argument as a direct equation a = b
        goal.formula = self._apply_rewrite(goal.formula, lemma)
        return self._printer.format_goal(goal, self._goal_counter)

    def _cmd_apply(self, args: list[str]) -> str:
        """Apply a proof term or lemma to the current goal."""
        goal = self._current_goal()
        if goal is None:
            return "Error: no active goal."
        if not args:
            return "Error: usage: apply <proof_term>"

        name = args[0]
        self._snapshot(f"apply {name}")

        # Check if it's a proved lemma
        for p in self._proved:
            if name in p.formula or name == p.method:
                label = goal.label
                self._goals.pop(0)
                self._proved.append(ProvedGoal(
                    formula=goal.formula,
                    method=f"apply {name}",
                    trust=p.trust,
                ))
                return f"  {_green('✓')} {label} proved by {name}"

        return f"Error: cannot apply '{name}' — not found in proved lemmas."

    def _cmd_have(self, args: list[str]) -> str:
        """Introduce a sub-lemma:  have <name> : <formula>"""
        if not args:
            return "Error: usage: have <name> : <formula>"

        # Split on ":"
        full = " ".join(args)
        if ":" not in full:
            return "Error: usage: have <name> : <formula>"

        name, formula = full.split(":", 1)
        name = name.strip()
        formula = formula.strip()

        self._snapshot(f"have {name}")
        self._goal_counter += 1
        sub = GoalState(
            formula=formula,
            context=dict(self._context_vars),
            label=f"Subgoal ({name})",
        )
        self._goals.insert(0, sub)
        return f"  New subgoal for {_bold(name)}:\n" + \
               self._printer.format_goal(sub, self._goal_counter)

    # ── finishing ─────────────────────────────────────────────────

    def _cmd_sorry(self, args: list[str]) -> str:
        """Admit the current goal without proof (UNTRUSTED)."""
        goal = self._current_goal()
        if goal is None:
            return "Error: no active goal."

        self._snapshot(f"sorry {goal.label}")
        label = goal.label
        self._goals.pop(0)
        self._proved.append(ProvedGoal(
            formula=goal.formula,
            method="sorry",
            trust=TrustLevel.UNTRUSTED,
            is_sorry=True,
        ))
        return f"  {_yellow('⚠')} {label} admitted (UNTRUSTED)"

    def _cmd_qed(self, args: list[str]) -> str:
        """Complete the proof."""
        if self._goals:
            remaining = len(self._goals)
            return f"Error: {remaining} goal(s) remaining.  Use 'show' to see them."

        if not self._proved:
            return "Error: nothing to prove.  Use 'goal' first."

        n_sorry = sum(1 for p in self._proved if p.is_sorry)
        trust = self._compute_trust()
        self._transcript.final_trust = trust

        trust_name = trust.name
        if n_sorry:
            parts = [f"  {_green('✓')} Theorem proved (trust: {trust_name}, {n_sorry} sorry)"]
        else:
            parts = [f"  {_green('✓')} Theorem proved (trust: {trust_name})"]

        parts.append(self._printer.format_proof_tree(self._proved))
        return "\n".join(parts)

    # ── Z3 quick check ────────────────────────────────────────────

    def _cmd_check(self, args: list[str]) -> str:
        """Quick Z3 validity check (does not affect proof state)."""
        if not args:
            return "Error: usage: check \"<formula>\""
        formula = " ".join(args)
        t0 = time.monotonic()
        proved = self._try_z3(formula)
        elapsed = time.monotonic() - t0
        if proved:
            return f"  {_green('✓')} Verified by Z3 ({elapsed:.3f}s)"
        else:
            return f"  {_red('✗')} Z3 could not verify"

    # ── axiom management ──────────────────────────────────────────

    def _cmd_load(self, args: list[str]) -> str:
        """Load library axioms:  load <module>"""
        if not args:
            return "Error: usage: load <module>  (sympy, numpy, torch, builtins)"

        module = args[0].lower()
        loader_map: dict[str, Any] = {
            "sympy": SympyAxioms,
            "numpy": NumpyAxioms,
            "torch": TorchAxioms,
            "builtins": BuiltinAxioms,
        }
        loader = loader_map.get(module)
        if loader is None:
            return f"Error: unknown module '{module}'.  Available: {', '.join(loader_map)}"

        before = len(self._axiom_registry)
        try:
            loader.register_all(self._axiom_registry)
        except ValueError:
            pass  # already registered
        self._axiom_registry.install_into_kernel(self.kernel)
        after = len(self._axiom_registry)
        loaded = after - before
        total = len(self._axiom_registry.all_axioms(module))
        return f"  Loaded {loaded} new axioms from {module} ({total} total)"

    def _cmd_search(self, args: list[str]) -> str:
        """Search axioms by keyword."""
        if not args:
            return "Error: usage: search \"<keyword>\""
        query = " ".join(args).lower()
        matches = []
        for ax in self._axiom_registry.all_axioms():
            if (query in ax.name.lower()
                    or query in ax.statement.lower()
                    or query in ax.description.lower()):
                matches.append(ax)

        if not matches:
            return f"  No axioms matching '{query}'."

        lines = []
        for ax in matches[:20]:
            lines.append(f"  {_cyan(ax.qualified_name)}: {ax.statement}")
        if len(matches) > 20:
            lines.append(f"  ... and {len(matches) - 20} more")
        return "\n".join(lines)

    # ── state management ──────────────────────────────────────────

    def _cmd_undo(self, args: list[str]) -> str:
        """Undo the last step."""
        if not self._undo_stack:
            return "  Nothing to undo."
        state = self._undo_stack.pop()
        self._restore(state)
        return f"  Undone: {state.step_description}"

    def _cmd_reset(self, args: list[str]) -> str:
        """Reset all proof state."""
        self._goals.clear()
        self._proved.clear()
        self._context_vars.clear()
        self._undo_stack.clear()
        self._goal_counter = 0
        return "  State reset."

    def _cmd_save(self, args: list[str]) -> str:
        """Save proof transcript:  save <path>"""
        if not args:
            return "Error: usage: save <path>"
        path = args[0]
        self._transcript.final_trust = self._compute_trust()
        self._transcript.save(path)
        return f"  Transcript saved to {path}"

    def _cmd_history(self, args: list[str]) -> str:
        """Show proof step history."""
        if not self._history:
            return "  (no steps yet)"
        lines = []
        for i, h in enumerate(self._history, 1):
            lines.append(f"  {_dim(str(i) + '.')} {h}")
        return "\n".join(lines)

    def _cmd_help(self, args: list[str]) -> str:
        """Show available commands."""
        lines = [f"  {_bold('Deppy Proof REPL Commands')}:", ""]
        max_width = max(len(c) for c in CommandParser.COMMANDS)
        for cmd, desc in CommandParser.COMMANDS.items():
            lines.append(f"  {_cyan(cmd.ljust(max_width + 2))}{desc}")
        return "\n".join(lines)

    def _cmd_exit(self, args: list[str]) -> str:
        """Exit the REPL."""
        return "  Bye."

    # ── Z3 integration ────────────────────────────────────────────

    def _try_z3(self, formula: str) -> bool:
        """Attempt to prove *formula* with Z3.  Returns True if valid."""
        try:
            from deppy.core.z3_bridge import quick_prove, _HAS_Z3
            if not _HAS_Z3:
                return False
            return quick_prove(formula)
        except Exception:
            return False

    # ── axiom lookup ──────────────────────────────────────────────

    def _find_axiom(self, name: str, module: str) -> LibraryAxiom | None:
        """Find an axiom by name, optionally scoped to module."""
        # Try qualified lookup first
        if module:
            ax = self._axiom_registry.lookup(module, name)
            if ax:
                return ax

        # Search all modules
        for ax in self._axiom_registry.all_axioms():
            if ax.name == name:
                return ax
            if ax.qualified_name == name:
                return ax

        # Fuzzy: check if name is a prefix
        for ax in self._axiom_registry.all_axioms():
            if name in ax.name or name in ax.qualified_name:
                return ax

        return None

    # ── formula manipulation helpers ──────────────────────────────

    @staticmethod
    def _strip_forall(formula: str, var: str) -> str:
        """Strip a leading ∀ quantifier for *var* from *formula*.

        Handles patterns like:
          ∀x:int. body     →  body
          forall x:int. body → body
          ∀x. body          →  body
        """
        patterns = [
            rf"[∀]?\s*{re.escape(var)}\s*:\s*\w+\.\s*",
            rf"forall\s+{re.escape(var)}\s*:\s*\w+\.\s*",
            rf"[∀]\s*{re.escape(var)}\s*\.\s*",
            rf"forall\s+{re.escape(var)}\s*\.\s*",
        ]
        for pat in patterns:
            m = re.match(pat, formula)
            if m:
                return formula[m.end():]
        return formula

    @staticmethod
    def _infer_var_type(formula: str, var: str) -> str:
        """Try to infer a variable's type from the formula."""
        m = re.search(rf"{re.escape(var)}\s*:\s*(\w+)", formula)
        if m:
            return m.group(1)
        # Heuristic: if formula mentions list ops, guess list
        list_hints = ["++", "len(", "sorted(", "::"]
        if any(h in formula for h in list_hints):
            return "list"
        return "int"

    @staticmethod
    def _make_base_case(formula: str, var: str, var_type: str) -> str:
        """Create the base case formula for induction."""
        if "list" in var_type.lower():
            return formula.replace(var, "[]")
        return formula.replace(var, "0")

    @staticmethod
    def _make_step_case(formula: str, var: str, var_type: str) -> str:
        """Create the step case formula for induction."""
        if "list" in var_type.lower():
            return formula.replace(var, f"(x::{var})")
        return formula.replace(var, f"({var} + 1)")

    @staticmethod
    def _unfold_definition(formula: str, defn: str) -> str:
        """Unfold a known definition in the formula.

        Handles common operators like ++, len, sorted for illustration.
        """
        rewrites: dict[str, list[tuple[str, str]]] = {
            "++": [
                ("[] ++ ys", "ys"),
                ("(x::xs) ++ ys", "x :: (xs ++ ys)"),
            ],
            "len": [
                ("len([])", "0"),
                ("len(x::xs)", "1 + len(xs)"),
            ],
        }
        if defn in rewrites:
            for lhs, rhs in rewrites[defn]:
                if lhs in formula:
                    formula = formula.replace(lhs, rhs)
                    return formula
        # If no known rewrite, just return as-is with a note
        return formula

    @staticmethod
    def _apply_rewrite(formula: str, equation: str) -> str:
        """Apply an equational rewrite to *formula*.

        *equation* should have the form  ``lhs = rhs`` or ``lhs == rhs``.
        """
        # Split on = or ==
        for sep in (" == ", " = "):
            if sep in equation:
                parts = equation.split(sep, 1)
                lhs = parts[0].strip()
                rhs = parts[1].strip()
                if lhs in formula:
                    return formula.replace(lhs, rhs, 1)
                if rhs in formula:
                    return formula.replace(rhs, lhs, 1)
                break
        return formula

    # ── trust computation ─────────────────────────────────────────

    def _compute_trust(self) -> TrustLevel:
        """Compute the overall trust level of the current proof."""
        if not self._proved:
            return TrustLevel.UNTRUSTED

        has_sorry = any(p.is_sorry for p in self._proved)
        if has_sorry:
            return TrustLevel.UNTRUSTED

        levels = [p.trust for p in self._proved]
        return min(levels, key=lambda t: t.value)


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Comprehensive self-tests using non-interactive mode."""
    passed = 0
    failed = 0

    def _assert(cond: bool, msg: str) -> None:
        nonlocal passed, failed
        if cond:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {msg}")

    # ── CommandParser ─────────────────────────────────────────────
    parser = CommandParser()

    cmd, args = parser.parse('goal "x + 0 == x"')
    _assert(cmd == "goal", "parse: command extracted")
    _assert(args == ["x + 0 == x"], "parse: quoted arg extracted")

    cmd, args = parser.parse("intro x : int")
    _assert(cmd == "intro", "parse: intro command")
    _assert(args == ["x", ":", "int"], "parse: intro args")

    cmd, args = parser.parse("z3")
    _assert(cmd == "z3", "parse: z3 command")
    _assert(args == [], "parse: z3 no args")

    cmd, args = parser.parse("")
    _assert(cmd == "", "parse: empty line")

    completions = parser.complete("go")
    _assert("goal" in completions, "complete: goal for 'go'")

    completions = parser.complete("s")
    _assert("show" in completions, "complete: show for 's'")
    _assert("search" in completions, "complete: search for 's'")
    _assert("save" in completions, "complete: save for 's'")
    _assert("sorry" in completions, "complete: sorry for 's'")
    print(f"  CommandParser       ✓ ({passed} checks)")

    # ── GoalPrinter ───────────────────────────────────────────────
    printer = GoalPrinter()
    g = GoalState(formula="x + 0 == x", context={"x": "int"}, label="Goal 1")
    fmt = printer.format_goal(g, 1)
    _assert("x + 0 == x" in fmt, "format_goal: formula present")
    _assert("x : int" in fmt, "format_goal: context present")

    ctx_fmt = printer.format_context({"a": "int", "b": "list"})
    _assert("a : int" in ctx_fmt, "format_context: binding present")

    proved_list = [ProvedGoal("x==x", "refl", TrustLevel.KERNEL)]
    tree_fmt = printer.format_proof_tree(proved_list)
    _assert("x==x" in tree_fmt, "format_proof_tree: formula present")

    status = printer.format_status(
        [GoalState(formula="a==b")],
        [ProvedGoal("c==c", "refl", TrustLevel.KERNEL)],
    )
    _assert("1 of 2" in status, "format_status: counts correct")
    print(f"  GoalPrinter         ✓ ({passed} checks)")

    # ── ProofREPL basic flow ──────────────────────────────────────
    repl = ProofREPL()

    out = repl.process_command("help")
    _assert("goal" in out.lower(), "help: mentions goal command")
    _assert("z3" in out.lower(), "help: mentions z3 command")

    out = repl.process_command("show")
    _assert("No active proof" in out, "show: no active proof")

    out = repl.process_command('goal "x + 0 == x"')
    _assert("x + 0 == x" in out, "goal: formula shown")

    out = repl.process_command("show")
    _assert("Remaining" in out or "Goal" in out, "show: shows remaining")

    out = repl.process_command("context")
    _assert("empty" in out, "context: empty at start")

    # ── intro ─────────────────────────────────────────────────────
    repl2 = ProofREPL()
    repl2.process_command('goal "∀x:int. x + 0 == x"')
    out = repl2.process_command("intro x")
    _assert("x : int" in out, "intro: variable introduced with inferred type")

    # ── axiom ─────────────────────────────────────────────────────
    repl3 = ProofREPL()
    repl3.process_command('goal "sorted(sorted(xs)) == sorted(xs)"')
    out = repl3.process_command("axiom sorted_idempotent builtins")
    _assert("✓" in out or "proved" in out.lower(),
            "axiom: builtin axiom applies")

    # ── sorry ─────────────────────────────────────────────────────
    repl4 = ProofREPL()
    repl4.process_command('goal "hard conjecture"')
    out = repl4.process_command("sorry")
    _assert("UNTRUSTED" in out, "sorry: marked untrusted")

    # ── qed ───────────────────────────────────────────────────────
    out = repl4.process_command("qed")
    _assert("proved" in out.lower(), "qed: proof complete")
    _assert("sorry" in out.lower() or "UNTRUSTED" in out, "qed: sorry noted")

    # ── qed with remaining goals fails ────────────────────────────
    repl5 = ProofREPL()
    repl5.process_command('goal "a == a"')
    out = repl5.process_command("qed")
    _assert("remaining" in out.lower() or "Error" in out,
            "qed: error if goals remain")

    # ── undo ──────────────────────────────────────────────────────
    repl6 = ProofREPL()
    repl6.process_command('goal "a == b"')
    repl6.process_command("sorry")
    _assert(len(repl6._proved) == 1, "undo: proved before undo")
    repl6.process_command("undo")
    _assert(len(repl6._goals) == 1, "undo: goal restored")
    _assert(len(repl6._proved) == 0, "undo: proved cleared")

    # ── reset ─────────────────────────────────────────────────────
    repl6.process_command("reset")
    _assert(len(repl6._goals) == 0, "reset: goals cleared")
    _assert(len(repl6._proved) == 0, "reset: proved cleared")

    # ── induction ─────────────────────────────────────────────────
    repl7 = ProofREPL()
    repl7.process_command('goal "len(xs ++ ys) == len(xs) + len(ys)"')
    repl7._context_vars["xs"] = "list"
    repl7._goals[0].context["xs"] = "list"
    out = repl7.process_command("induction xs")
    _assert("base" in out.lower(), "induction: base case created")
    _assert("step" in out.lower(), "induction: step case created")
    _assert(len(repl7._goals) == 2, "induction: two subgoals")

    # ── unfold ────────────────────────────────────────────────────
    repl8 = ProofREPL()
    repl8.process_command('goal "len([] ++ ys) == 0 + len(ys)"')
    out = repl8.process_command("unfold ++")
    _assert("len(ys)" in out, "unfold: ++ unfolded")

    # ── cases ─────────────────────────────────────────────────────
    repl9 = ProofREPL()
    repl9.process_command('goal "P(b)"')
    out = repl9.process_command("cases b True False")
    _assert("True" in out, "cases: True case")
    _assert("False" in out, "cases: False case")
    _assert(len(repl9._goals) == 2, "cases: two subgoals")

    # ── search ────────────────────────────────────────────────────
    repl10 = ProofREPL()
    out = repl10.process_command('search "idempotent"')
    _assert("sorted_idempotent" in out, "search: finds builtin axiom")

    # ── load ──────────────────────────────────────────────────────
    repl11 = ProofREPL()
    out = repl11.process_command("load sympy")
    _assert("sympy" in out.lower(), "load: sympy loaded")

    out = repl11.process_command('search "expand"')
    _assert("expand" in out, "load+search: sympy axioms searchable")

    # ── check ─────────────────────────────────────────────────────
    repl12 = ProofREPL()
    out = repl12.process_command('check "1 + 1 == 2"')
    # May or may not have Z3 installed; just verify no crash
    _assert("✓" in out or "✗" in out, "check: produces verdict")

    # ── history ───────────────────────────────────────────────────
    repl13 = ProofREPL()
    repl13.process_command('goal "x == x"')
    repl13.process_command("sorry")
    out = repl13.process_command("history")
    _assert("goal" in out, "history: records commands")
    _assert("sorry" in out, "history: includes sorry")

    # ── have ──────────────────────────────────────────────────────
    repl14 = ProofREPL()
    repl14.process_command('goal "a + b == b + a"')
    out = repl14.process_command("have commutativity : a + b == b + a")
    _assert("commutativity" in out, "have: sub-lemma created")
    _assert(len(repl14._goals) == 2, "have: adds subgoal")

    # ── rewrite ───────────────────────────────────────────────────
    repl15 = ProofREPL()
    repl15.process_command('goal "sorted(sorted(xs)) == sorted(xs)"')
    out = repl15.process_command("rewrite sorted_idempotent")
    _assert("sorted" in out, "rewrite: applied")

    # ── ProofTranscript ───────────────────────────────────────────
    repl16 = ProofREPL()
    repl16.process_command('goal "p == p"')
    repl16.process_command("sorry")
    repl16.process_command("qed")

    transcript = repl16._transcript
    _assert(len(transcript.commands) >= 3, "transcript: commands recorded")

    # Save and reload
    save_path = "._proof_repl_test_transcript.json"
    transcript.save(save_path)
    loaded = ProofTranscript.load(save_path)
    _assert(loaded.commands == transcript.commands,
            "transcript: save/load roundtrips")

    # Replay
    repl17 = ProofREPL()
    ok = loaded.replay(repl17)
    _assert(ok, "transcript: replay succeeds")

    # Clean up
    try:
        os.remove(save_path)
    except OSError:
        pass

    # ── unknown command ───────────────────────────────────────────
    repl18 = ProofREPL()
    out = repl18.process_command("foobar baz")
    _assert("Error" in out or "unknown" in out.lower(),
            "unknown: error message")

    # ── assumptions ───────────────────────────────────────────────
    repl19 = ProofREPL()
    out = repl19.process_command("assumptions")
    _assert("No active goal" in out, "assumptions: no goal")

    repl19.process_command('goal "∀x:int. x == x"')
    repl19.process_command("intro x")
    out = repl19.process_command("assumptions")
    _assert("x : int" in out, "assumptions: shows introduced var")

    # ── exit ──────────────────────────────────────────────────────
    out = repl19.process_command("exit")
    _assert("Bye" in out, "exit: farewell message")

    # ── full proof walkthrough ────────────────────────────────────
    repl20 = ProofREPL()
    repl20.process_command('goal "sorted(sorted(xs)) == sorted(xs)"')
    repl20.process_command("axiom sorted_idempotent builtins")
    out = repl20.process_command("qed")
    _assert("proved" in out.lower(), "walkthrough: proof completes")
    _assert("AXIOM_TRUSTED" in out, "walkthrough: trust level correct")

    # ── multiple goals ────────────────────────────────────────────
    repl21 = ProofREPL()
    repl21.process_command('goal "A"')
    repl21.process_command('goal "B"')
    _assert(len(repl21._goals) == 2, "multi-goal: two goals active")
    repl21.process_command("sorry")
    _assert(len(repl21._goals) == 1, "multi-goal: one dismissed")
    repl21.process_command("sorry")
    out = repl21.process_command("qed")
    _assert("2 sorry" in out, "multi-goal: both sorries noted")

    # ── strip_forall ──────────────────────────────────────────────
    _assert(
        ProofREPL._strip_forall("∀x:int. x > 0", "x") == "x > 0",
        "strip_forall: unicode ∀ with type",
    )
    _assert(
        ProofREPL._strip_forall("forall x:int. x > 0", "x") == "x > 0",
        "strip_forall: keyword forall with type",
    )
    _assert(
        ProofREPL._strip_forall("∀x. x > 0", "x") == "x > 0",
        "strip_forall: ∀ without type",
    )

    # ── trust computation ─────────────────────────────────────────
    repl22 = ProofREPL()
    repl22._proved = [
        ProvedGoal("a", "z3", TrustLevel.Z3_VERIFIED),
        ProvedGoal("b", "axiom", TrustLevel.AXIOM_TRUSTED),
    ]
    _assert(repl22._compute_trust() == TrustLevel.AXIOM_TRUSTED,
            "trust: min of Z3_VERIFIED and AXIOM_TRUSTED")

    repl22._proved.append(ProvedGoal("c", "sorry", TrustLevel.UNTRUSTED, True))
    _assert(repl22._compute_trust() == TrustLevel.UNTRUSTED,
            "trust: sorry makes it UNTRUSTED")

    # ── summary ───────────────────────────────────────────────────
    total = passed + failed
    print(f"\n  Self-tests: {passed}/{total} passed", end="")
    if failed:
        print(f", {_red(str(failed) + ' FAILED')}")
    else:
        print(f"  {_green('ALL PASSED')}")


if __name__ == "__main__":
    import sys
    if "--test" in sys.argv:
        _self_test()
    else:
        ProofREPL().start()
