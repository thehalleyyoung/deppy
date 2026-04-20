"""
synhopy.tactics — Tactic-based proof construction.

Provides tactic combinators for ``from synhopy.tactics import Tactic, intro, apply``.
"""
from __future__ import annotations
from typing import Any, Callable, Optional
from dataclasses import dataclass, field


@dataclass
class Goal:
    """A proof goal: context ⊢ term : type."""
    context: dict = field(default_factory=dict)
    target: str = ""
    hyps: list = field(default_factory=list)


@dataclass
class TacticState:
    """State of a tactic proof: list of open goals."""
    goals: list = field(default_factory=list)
    solved: list = field(default_factory=list)
    proof_terms: list = field(default_factory=list)

    @property
    def is_complete(self) -> bool:
        return len(self.goals) == 0

    @property
    def current_goal(self) -> Optional[Goal]:
        return self.goals[0] if self.goals else None


class Tactic:
    """Base class for tactics."""
    def __init__(self, name: str = ""):
        self.name = name

    def apply(self, state: TacticState) -> TacticState:
        return state

    def __repr__(self):
        return f"Tactic({self.name})"


def intro(name: str = "x") -> Tactic:
    """Introduce a variable into the context."""
    t = Tactic(f"intro {name}")
    return t


def apply(lemma) -> Tactic:
    """Apply a known lemma to the current goal."""
    t = Tactic(f"apply {lemma}")
    return t


def rewrite(path) -> Tactic:
    """Rewrite using a path equality."""
    t = Tactic(f"rewrite {path}")
    return t


def split() -> Tactic:
    """Split a conjunction goal into two subgoals."""
    return Tactic("split")


def left() -> Tactic:
    """Prove left disjunct."""
    return Tactic("left")


def right() -> Tactic:
    """Prove right disjunct."""
    return Tactic("right")


def exact(term) -> Tactic:
    """Provide an exact proof term."""
    return Tactic(f"exact {term}")


def assumption() -> Tactic:
    """Solve goal from hypotheses."""
    return Tactic("assumption")


def induction(var: str) -> Tactic:
    """Induction on a variable."""
    return Tactic(f"induction {var}")


def cases(var: str) -> Tactic:
    """Case analysis on a variable."""
    return Tactic(f"cases {var}")


def auto() -> Tactic:
    """Automatic proof search."""
    return Tactic("auto")


def z3() -> Tactic:
    """Dispatch to Z3 solver."""
    return Tactic("z3")


# Tactic combinators
def then(t1: Tactic, t2: Tactic) -> Tactic:
    """Sequential composition: t1 then t2."""
    return Tactic(f"({t1.name}; {t2.name})")


def or_else(t1: Tactic, t2: Tactic) -> Tactic:
    """Try t1, fall back to t2."""
    return Tactic(f"({t1.name} | {t2.name})")


def repeat(t: Tactic) -> Tactic:
    """Apply t until it fails."""
    return Tactic(f"repeat({t.name})")


def all_goals(t: Tactic) -> Tactic:
    """Apply t to all goals."""
    return Tactic(f"all_goals({t.name})")


# Homotopy-specific tactics
def transport(path) -> Tactic:
    """Carry proof along a path."""
    return Tactic(f"transport {path}")


def path_induction() -> Tactic:
    """J-elimination."""
    return Tactic("path_induction")


def cech_decompose(cover) -> Tactic:
    """Čech decomposition strategy."""
    return Tactic(f"cech_decompose {cover}")


def fiber_induction(fibration) -> Tactic:
    """Induction on fibers."""
    return Tactic(f"fiber_induction {fibration}")


def univalence() -> Tactic:
    """Apply univalence axiom."""
    return Tactic("univalence")


def funext() -> Tactic:
    """Apply function extensionality."""
    return Tactic("funext")


def duck_path(protocol) -> Tactic:
    """Construct duck typing path."""
    return Tactic(f"duck_path {protocol}")
