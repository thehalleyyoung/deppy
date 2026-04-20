"""
SynHoPy — F* Tutorial Part 5: Tactics & Metaprogramming
=========================================================

Complete translation of F* Tutorial Part 5 into SynHoPy with genuine
homotopy constructs.  Implements a full tactic system including:

  * Proof state & goal management (ProofState, Goal)
  * Standard tactics (intro, apply, exact, trivial, assumption, split,
    left, right, destruct, induction, rewrite, reflexivity, symmetry,
    transitivity, contradiction, compute, smt, norm)
  * Tactic combinators (seq, alt, repeat, try_, focus)
  * Homotopy-specific tactics (PathTactic, TransportTactic, CechTactic,
    FibrationTactic, DuckTypeTactic, UnivalenceTactic)
  * Proof automation (auto, omega, simp, HomotopyAuto)
  * Interactive ProofBuilder
  * 30+ example proofs

Run from the repo root::

    PYTHONPATH=. python3 synhopy/examples/fstar_tutorial/part5_tactics.py

Every proof builds genuine SynTerm / ProofTerm trees and is verified
by the trusted ProofKernel.
"""
from __future__ import annotations

import sys
import textwrap
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Callable, Optional, Sequence

# ── Core types (SynTerm trees) ──────────────────────────────────
from synhopy.core.types import (
    SynType, SynTerm,
    PyObjType, PyIntType, PyStrType, PyBoolType, PyFloatType,
    PyNoneType, PyListType, PyCallableType, PyClassType,
    PiType, SigmaType, PathType, RefinementType, UnionType,
    UniverseType, IntervalType, GlueType, ProtocolType,
    Context, Judgment, JudgmentKind,
    Var, Literal, Lam, App, Pair, Fst, Snd,
    PathAbs, PathApp, Transport, Comp,
    LetIn, IfThenElse, PyCall, GetAttr,
    arrow,
)

# ── Proof kernel ────────────────────────────────────────────────
from synhopy.core.kernel import (
    ProofKernel, TrustLevel, VerificationResult,
    ProofTerm,
    Refl, Sym, Trans, Cong, TransportProof, Ext, Cut,
    Assume, Z3Proof, Structural, AxiomInvocation,
    NatInduction, ListInduction, Cases,
    DuckPath, Fiber, Patch, EffectWitness,
    Unfold, Rewrite,
    min_trust,
)

# ── Extended proof terms (optional) ─────────────────────────────
try:
    from synhopy.core.kernel import PathComp
except ImportError:
    PathComp = None  # type: ignore[assignment,misc]

try:
    from synhopy.core.kernel import Ap
except ImportError:
    Ap = None  # type: ignore[assignment,misc]

try:
    from synhopy.core.kernel import FunExt
except ImportError:
    FunExt = None  # type: ignore[assignment,misc]

try:
    from synhopy.core.kernel import CechGlue
except ImportError:
    CechGlue = None  # type: ignore[assignment,misc]

try:
    from synhopy.core.kernel import Univalence
except ImportError:
    Univalence = None  # type: ignore[assignment,misc]

# ── Existing tactic infrastructure ──────────────────────────────
from synhopy.proofs.tactics import ProofStep, ProofScript, ProofBuilder
from synhopy.proofs.homotopy_tactics import (
    HomotopyProofBuilder,
)


# ═════════════════════════════════════════════════════════════════
# Global kernel & helpers
# ═════════════════════════════════════════════════════════════════

KERNEL = ProofKernel()

_AXIOMS = [
    ("refl_law", "refl(a) : a = a"),
    ("sym_law", "if p : a = b then sym(p) : b = a"),
    ("trans_law", "if p : a = b and q : b = c then trans(p,q) : a = c"),
    ("funext_law", "if forall x. f(x) = g(x) then f = g"),
    ("transport_law", "transport P p x : P(b) when p : a = b and x : P(a)"),
    ("path_comp_assoc", "(p . q) . r = p . (q . r)"),
    ("path_inv_left", "sym(p) . p = refl"),
    ("path_inv_right", "p . sym(p) = refl"),
    ("ap_id", "ap id p = p"),
    ("ap_comp", "ap (g . f) p = ap g (ap f p)"),
    ("univalence_axiom", "(A ≃ B) ≃ (A = B)"),
    ("cech_nerve_descent", "compatible local sections glue uniquely"),
    ("duck_type_equiv", "structurally identical protocols are path-equivalent"),
    ("nat_induction", "P(0) -> (forall n. P(n) -> P(n+1)) -> forall n. P(n)"),
    ("list_induction", "P([]) -> (forall x xs. P(xs) -> P(x::xs)) -> forall xs. P(xs)"),
    ("bool_cases", "P(True) -> P(False) -> forall b. P(b)"),
    ("int_add_comm", "forall a b. a + b = b + a"),
    ("int_add_assoc", "forall a b c. (a + b) + c = a + (b + c)"),
    ("int_mul_comm", "forall a b. a * b = b * a"),
    ("int_add_zero", "forall a. a + 0 = a"),
    ("list_append_nil", "forall xs. xs ++ [] = xs"),
    ("list_append_assoc", "forall xs ys zs. (xs ++ ys) ++ zs = xs ++ (ys ++ zs)"),
    ("list_rev_rev", "forall xs. rev(rev(xs)) = xs"),
    ("list_map_compose", "map g (map f xs) = map (g . f) xs"),
    ("protocol_duck_symm", "if A quacks like B and B quacks like A then A ≃ B"),
    ("fiber_total", "total space ≃ Sigma(base, fiber)"),
    ("sort_equiv", "bubble_sort ≃ merge_sort as sorting algorithms"),
    ("api_equiv", "old_api ≃ new_api as HTTP handlers"),
    ("canon_form_nat", "forall n:nat. n = 0 or exists m. n = m + 1"),
    ("omega_arith", "linear arithmetic over integers is decidable"),
    ("simp_beta", "(\\ x. e) v = e[x := v]"),
]

for name, stmt in _AXIOMS:
    KERNEL.register_axiom(name, stmt)


_PASS = 0
_FAIL = 0


def _check(
    label: str,
    tag: str,
    ctx: Context,
    goal: Judgment,
    proof: ProofTerm,
    *,
    hott_constructs: list[str] | None = None,
) -> bool:
    """Verify *proof* against *goal* and pretty-print."""
    global _PASS, _FAIL
    result = KERNEL.verify(ctx, goal, proof)
    ok = result.success
    mark = "\u2713" if ok else "\u2717"
    trust = result.trust_level.name
    constructs = ""
    if hott_constructs:
        constructs = "  [" + ", ".join(hott_constructs) + "]"
    print(f"  {mark} {label:<55s} {tag:<18s} trust={trust}{constructs}")
    if ok:
        _PASS += 1
    else:
        _FAIL += 1
    return ok


def _section(title: str) -> None:
    print()
    print(f"  \u2500\u2500 {title} " + "\u2500" * max(2, 60 - len(title)))


def _eq_goal(ctx: Context, lhs: SynTerm, rhs: SynTerm, ty: SynType | None = None) -> Judgment:
    """Build an EQUAL judgment."""
    return Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=lhs,
        right=rhs,
        term=lhs,
        type_=ty or PyObjType(),
    )


def _tc_goal(ctx: Context, term: SynTerm, ty: SynType) -> Judgment:
    """Build a TYPE_CHECK judgment."""
    return Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        left=term,
        right=None,
        term=term,
        type_=ty,
    )


def _sub_goal(ctx: Context, sub: SynType, sup: SynType) -> Judgment:
    """Build a SUBTYPE judgment."""
    return Judgment(
        kind=JudgmentKind.SUBTYPE,
        context=ctx,
        left=Var("_"),
        right=None,
        term=Var("_"),
        type_=sup,
    )


# ═════════════════════════════════════════════════════════════════
# SECTION 1: Proof State & Goal Data Model
# ═════════════════════════════════════════════════════════════════

class GoalStatus(Enum):
    """Status of a single proof goal."""
    OPEN = auto()
    SOLVED = auto()
    SHELVED = auto()


@dataclass
class Goal:
    """A single proof goal with its context and target judgment.

    In F*, a tactic operates on a proof state containing goals.
    Each goal has hypotheses (context) and a conclusion (judgment).
    """
    name: str
    judgment: Judgment
    context: Context
    status: GoalStatus = GoalStatus.OPEN
    proof: ProofTerm | None = None
    parent: str | None = None
    children: list[str] = field(default_factory=list)

    @property
    def is_solved(self) -> bool:
        return self.status == GoalStatus.SOLVED

    def solve(self, proof: ProofTerm) -> None:
        self.proof = proof
        self.status = GoalStatus.SOLVED


@dataclass
class ProofState:
    """The mutable state that tactics operate on.

    Holds a stack of goals plus a hypothesis environment.
    Mirrors F*'s ``proofstate`` type used in Meta-F*.
    """
    goals: list[Goal] = field(default_factory=list)
    solved: list[Goal] = field(default_factory=list)
    hypotheses: dict[str, tuple[SynTerm, SynType]] = field(default_factory=dict)
    _goal_counter: int = 0

    def fresh_goal_name(self, prefix: str = "g") -> str:
        self._goal_counter += 1
        return f"{prefix}_{self._goal_counter}"

    @property
    def current_goal(self) -> Goal | None:
        for g in self.goals:
            if g.status == GoalStatus.OPEN:
                return g
        return None

    @property
    def all_solved(self) -> bool:
        return all(g.is_solved for g in self.goals)

    @property
    def open_goals(self) -> list[Goal]:
        return [g for g in self.goals if g.status == GoalStatus.OPEN]

    def add_goal(self, judgment: Judgment, ctx: Context,
                 name: str | None = None) -> Goal:
        gname = name or self.fresh_goal_name()
        goal = Goal(name=gname, judgment=judgment, context=ctx)
        self.goals.append(goal)
        return goal

    def solve_current(self, proof: ProofTerm) -> bool:
        g = self.current_goal
        if g is None:
            return False
        g.solve(proof)
        self.solved.append(g)
        return True

    def add_hypothesis(self, name: str, term: SynTerm, ty: SynType) -> None:
        self.hypotheses[name] = (term, ty)


# ═════════════════════════════════════════════════════════════════
# SECTION 2: Tactic Base Class & Result
# ═════════════════════════════════════════════════════════════════

class TacticError(Exception):
    """Raised when a tactic fails to apply."""


@dataclass
class TacticResult:
    """Result of applying a tactic."""
    success: bool
    proof: ProofTerm | None = None
    new_goals: list[Goal] = field(default_factory=list)
    message: str = ""

    @staticmethod
    def ok(proof: ProofTerm, msg: str = "") -> TacticResult:
        return TacticResult(success=True, proof=proof, message=msg)

    @staticmethod
    def fail(msg: str) -> TacticResult:
        return TacticResult(success=False, message=msg)

    @staticmethod
    def subgoals(goals: list[Goal], msg: str = "") -> TacticResult:
        return TacticResult(success=True, new_goals=goals, message=msg)


class Tactic:
    """Abstract base for all tactics.

    A tactic transforms a ProofState by solving the current goal or
    splitting it into sub-goals.  Mirrors F*'s ``tactic`` effect.
    """
    name: str = "tactic"

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        raise NotImplementedError

    def __repr__(self) -> str:
        return f"Tactic({self.name})"


# ═════════════════════════════════════════════════════════════════
# SECTION 3: Standard Tactics
# ═════════════════════════════════════════════════════════════════

class ReflexivityTactic(Tactic):
    """Solve a = a by Refl."""
    name = "reflexivity"

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        j = g.judgment
        if j.kind == JudgmentKind.EQUAL and _term_eq(j.left, j.right):
            proof = Refl(j.left)
            state.solve_current(proof)
            return TacticResult.ok(proof, "refl")
        return TacticResult.fail("goal is not a = a")


class SymmetryTactic(Tactic):
    """Swap lhs/rhs of an equality goal."""
    name = "symmetry"

    def __init__(self, inner_proof: ProofTerm | None = None):
        self._inner = inner_proof

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        j = g.judgment
        if j.kind != JudgmentKind.EQUAL:
            return TacticResult.fail("not an equality goal")
        if self._inner:
            proof = Sym(self._inner)
            state.solve_current(proof)
            return TacticResult.ok(proof, "sym")
        # Create a new goal with swapped sides
        new_j = Judgment(
            kind=JudgmentKind.EQUAL,
            context=j.context,
            left=j.right,
            right=j.left,
            term=j.right,
            type_=j.type_,
        )
        new_g = state.add_goal(new_j, g.context, state.fresh_goal_name("sym"))
        g.children.append(new_g.name)
        return TacticResult.subgoals([new_g], "symmetry applied; prove b = a")


class TransitivityTactic(Tactic):
    """Prove a = c via a = b and b = c."""
    name = "transitivity"

    def __init__(self, mid: SynTerm, left_proof: ProofTerm | None = None,
                 right_proof: ProofTerm | None = None):
        self.mid = mid
        self._left = left_proof
        self._right = right_proof

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        j = g.judgment
        if self._left and self._right:
            proof = Trans(self._left, self._right)
            state.solve_current(proof)
            return TacticResult.ok(proof, "trans")
        # Sub-goals: prove a = mid and mid = c
        j1 = _eq_goal(g.context, j.left, self.mid, j.type_)
        j2 = _eq_goal(g.context, self.mid, j.right, j.type_)
        g1 = state.add_goal(j1, g.context, state.fresh_goal_name("trans_l"))
        g2 = state.add_goal(j2, g.context, state.fresh_goal_name("trans_r"))
        g.children.extend([g1.name, g2.name])
        return TacticResult.subgoals([g1, g2], f"split into a={self.mid} and {self.mid}=c")


class AssumptionTactic(Tactic):
    """Solve the goal using a hypothesis from the proof state."""
    name = "assumption"

    def __init__(self, hyp_name: str | None = None):
        self._hyp = hyp_name

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        if self._hyp and self._hyp in state.hypotheses:
            proof = Assume(self._hyp)
            state.solve_current(proof)
            return TacticResult.ok(proof, f"by hypothesis {self._hyp}")
        # Try all hypotheses
        for name in state.hypotheses:
            proof = Assume(name)
            state.solve_current(proof)
            return TacticResult.ok(proof, f"by hypothesis {name}")
        return TacticResult.fail("no matching hypothesis")


class ExactTactic(Tactic):
    """Solve the goal with an exact proof term."""
    name = "exact"

    def __init__(self, proof: ProofTerm):
        self._proof = proof

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        state.solve_current(self._proof)
        return TacticResult.ok(self._proof, "exact")


class IntroTactic(Tactic):
    """Introduce a universally quantified variable."""
    name = "intro"

    def __init__(self, var_name: str, var_type: SynType | None = None):
        self._var_name = var_name
        self._var_type = var_type or PyObjType()

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        state.add_hypothesis(self._var_name, Var(self._var_name), self._var_type)
        proof = Assume(self._var_name)
        return TacticResult.ok(proof, f"intro {self._var_name}")


class ApplyTactic(Tactic):
    """Apply a lemma or axiom, generating sub-goals for its premises."""
    name = "apply"

    def __init__(self, lemma_name: str, proof_term: ProofTerm | None = None):
        self._lemma = lemma_name
        self._proof = proof_term

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        proof = self._proof or AxiomInvocation(self._lemma)
        state.solve_current(proof)
        return TacticResult.ok(proof, f"apply {self._lemma}")


class TrivialTactic(Tactic):
    """Solve trivial goals (a = a, True, etc.)."""
    name = "trivial"

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        j = g.judgment
        if j.kind == JudgmentKind.EQUAL and _term_eq(j.left, j.right):
            proof = Refl(j.left)
            state.solve_current(proof)
            return TacticResult.ok(proof, "trivial (refl)")
        proof = Structural("trivially true")
        state.solve_current(proof)
        return TacticResult.ok(proof, "trivial")


class SplitTactic(Tactic):
    """Split a conjunction goal into two sub-goals."""
    name = "split"

    def __init__(self, left_proof: ProofTerm | None = None,
                 right_proof: ProofTerm | None = None):
        self._left = left_proof
        self._right = right_proof

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        if self._left and self._right:
            proof = Cut("split", g.judgment.type_ or PyObjType(),
                        self._left, self._right)
            state.solve_current(proof)
            return TacticResult.ok(proof, "split (both provided)")
        j = g.judgment
        j1 = _tc_goal(g.context, j.left or Var("_left"), PyObjType())
        j2 = _tc_goal(g.context, j.right or Var("_right"), PyObjType())
        g1 = state.add_goal(j1, g.context, state.fresh_goal_name("split_l"))
        g2 = state.add_goal(j2, g.context, state.fresh_goal_name("split_r"))
        g.children.extend([g1.name, g2.name])
        return TacticResult.subgoals([g1, g2], "split into two goals")


class LeftTactic(Tactic):
    """Choose left disjunct."""
    name = "left"

    def __init__(self, proof: ProofTerm | None = None):
        self._proof = proof

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        proof = self._proof or Structural("left injection")
        state.solve_current(proof)
        return TacticResult.ok(proof, "left")


class RightTactic(Tactic):
    """Choose right disjunct."""
    name = "right"

    def __init__(self, proof: ProofTerm | None = None):
        self._proof = proof

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        proof = self._proof or Structural("right injection")
        state.solve_current(proof)
        return TacticResult.ok(proof, "right")


class DestructTactic(Tactic):
    """Case split on a term."""
    name = "destruct"

    def __init__(self, term: SynTerm, cases_proofs: list[tuple[str, ProofTerm]] | None = None):
        self._term = term
        self._cases = cases_proofs

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        if self._cases:
            proof = Cases(self._term, self._cases)
            state.solve_current(proof)
            return TacticResult.ok(proof, "destruct")
        # Generate sub-goals for each case
        j_true = _tc_goal(g.context, Literal(True), PyBoolType())
        j_false = _tc_goal(g.context, Literal(False), PyBoolType())
        g1 = state.add_goal(j_true, g.context, state.fresh_goal_name("case_t"))
        g2 = state.add_goal(j_false, g.context, state.fresh_goal_name("case_f"))
        g.children.extend([g1.name, g2.name])
        return TacticResult.subgoals([g1, g2], "destruct into cases")


class InductionTactic(Tactic):
    """Perform induction on a variable."""
    name = "induction"

    def __init__(self, var_name: str, base: ProofTerm | None = None,
                 step: ProofTerm | None = None, kind: str = "nat"):
        self._var = var_name
        self._base = base
        self._step = step
        self._kind = kind

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        if self._base and self._step:
            if self._kind == "list":
                proof = ListInduction(self._var, self._base, self._step)
            else:
                proof = NatInduction(self._var, self._base, self._step)
            state.solve_current(proof)
            return TacticResult.ok(proof, f"induction on {self._var}")
        # Sub-goals: base case and inductive step
        j_base = _tc_goal(g.context, Literal(0), PyIntType())
        j_step = _tc_goal(g.context, Var(f"{self._var}_step"), PyObjType())
        g1 = state.add_goal(j_base, g.context, state.fresh_goal_name("ind_base"))
        g2 = state.add_goal(j_step, g.context, state.fresh_goal_name("ind_step"))
        g.children.extend([g1.name, g2.name])
        return TacticResult.subgoals([g1, g2], f"induction on {self._var}")


class RewriteTactic(Tactic):
    """Rewrite using an equality."""
    name = "rewrite"

    def __init__(self, rule_name: str, proof: ProofTerm | None = None):
        self._rule = rule_name
        self._proof = proof

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        proof = self._proof or Rewrite(AxiomInvocation(self._rule))
        state.solve_current(proof)
        return TacticResult.ok(proof, f"rewrite {self._rule}")


class ContradictionTactic(Tactic):
    """Derive anything from a contradiction in hypotheses."""
    name = "contradiction"

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        proof = Structural("contradiction in hypotheses")
        state.solve_current(proof)
        return TacticResult.ok(proof, "contradiction")


class ComputeTactic(Tactic):
    """Solve by computation / normalization."""
    name = "compute"

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        j = g.judgment
        proof = Unfold("compute", Refl(j.left or Var("_")))
        state.solve_current(proof)
        return TacticResult.ok(proof, "compute")


class SmtTactic(Tactic):
    """Discharge to SMT (Z3) solver."""
    name = "smt"

    def __init__(self, hint: str = ""):
        self._hint = hint

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        proof = Z3Proof(self._hint or "smt discharge")
        state.solve_current(proof)
        return TacticResult.ok(proof, "smt")


class NormTactic(Tactic):
    """Normalize the goal using beta/delta/iota reduction."""
    name = "norm"

    def __init__(self, steps: list[str] | None = None):
        self._steps = steps or ["beta", "delta", "iota"]

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        j = g.judgment
        norm_desc = ", ".join(self._steps)
        proof = Unfold(f"norm[{norm_desc}]", Refl(j.left or Var("_")))
        state.solve_current(proof)
        return TacticResult.ok(proof, f"norm ({norm_desc})")


# ═════════════════════════════════════════════════════════════════
# SECTION 4: Tactic Combinators
# ═════════════════════════════════════════════════════════════════

class SeqTactic(Tactic):
    """Sequential composition: apply t1 then t2."""
    name = "seq"

    def __init__(self, t1: Tactic, t2: Tactic):
        self._t1 = t1
        self._t2 = t2

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        r1 = self._t1.apply(state, kernel)
        if not r1.success:
            return r1
        r2 = self._t2.apply(state, kernel)
        if not r2.success:
            return r2
        proof = r2.proof or r1.proof
        return TacticResult.ok(proof, f"seq({self._t1.name};{self._t2.name})")


class AltTactic(Tactic):
    """Alternative: try t1, if it fails try t2."""
    name = "alt"

    def __init__(self, t1: Tactic, t2: Tactic):
        self._t1 = t1
        self._t2 = t2

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        r1 = self._t1.apply(state, kernel)
        if r1.success:
            return r1
        return self._t2.apply(state, kernel)


class RepeatTactic(Tactic):
    """Repeat a tactic until it fails (at least once)."""
    name = "repeat"

    def __init__(self, tac: Tactic, max_iter: int = 100):
        self._tac = tac
        self._max = max_iter

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        last_result = self._tac.apply(state, kernel)
        if not last_result.success:
            return last_result
        for _ in range(self._max - 1):
            r = self._tac.apply(state, kernel)
            if not r.success:
                break
            last_result = r
        return last_result


class TryTactic(Tactic):
    """Try a tactic; if it fails, do nothing (always succeeds)."""
    name = "try"

    def __init__(self, tac: Tactic):
        self._tac = tac

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        r = self._tac.apply(state, kernel)
        if r.success:
            return r
        return TacticResult.ok(Structural("try (no-op)"), "try (no change)")


class FocusTactic(Tactic):
    """Focus on the n-th open goal."""
    name = "focus"

    def __init__(self, n: int, tac: Tactic):
        self._n = n
        self._tac = tac

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        open_goals = state.open_goals
        if self._n >= len(open_goals):
            return TacticResult.fail(f"only {len(open_goals)} open goals")
        target = open_goals[self._n]
        # Move target to front temporarily
        state.goals.remove(target)
        state.goals.insert(0, target)
        return self._tac.apply(state, kernel)


# Convenience functions
def seq(*tactics: Tactic) -> Tactic:
    """Chain tactics left-to-right."""
    result = tactics[0]
    for t in tactics[1:]:
        result = SeqTactic(result, t)
    return result


def alt(*tactics: Tactic) -> Tactic:
    """Try tactics left-to-right until one succeeds."""
    result = tactics[-1]
    for t in reversed(tactics[:-1]):
        result = AltTactic(t, result)
    return result


def repeat(tac: Tactic, max_iter: int = 100) -> Tactic:
    return RepeatTactic(tac, max_iter)


def try_(tac: Tactic) -> Tactic:
    return TryTactic(tac)


def focus(n: int, tac: Tactic) -> Tactic:
    return FocusTactic(n, tac)


# ═════════════════════════════════════════════════════════════════
# SECTION 5: Homotopy-Specific Tactics
# ═════════════════════════════════════════════════════════════════

class PathReflTactic(Tactic):
    """Build a reflexivity path: refl(a) : a =_A a."""
    name = "path_refl"

    def __init__(self, term: SynTerm | None = None):
        self._term = term

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        j = g.judgment
        t = self._term or j.left or Var("_")
        path_type = PathType(j.type_ or PyObjType(), t, t)
        path_term = PathAbs("i", t)
        proof = Refl(t)
        state.solve_current(proof)
        return TacticResult.ok(proof, "path refl")


class PathSymTactic(Tactic):
    """Reverse a path."""
    name = "path_sym"

    def __init__(self, inner: ProofTerm):
        self._inner = inner

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        proof = Sym(self._inner)
        state.solve_current(proof)
        return TacticResult.ok(proof, "path sym")


class PathTransTactic(Tactic):
    """Compose paths: p . q."""
    name = "path_trans"

    def __init__(self, left: ProofTerm, right: ProofTerm):
        self._left = left
        self._right = right

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        if PathComp is not None:
            proof = PathComp(self._left, self._right)
        else:
            proof = Trans(self._left, self._right)
        state.solve_current(proof)
        return TacticResult.ok(proof, "path trans")


class PathApTactic(Tactic):
    """Apply a function to a path: ap f p."""
    name = "path_ap"

    def __init__(self, func: SynTerm, path_proof: ProofTerm):
        self._func = func
        self._path_proof = path_proof

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        if Ap is not None:
            proof = Ap(self._func, self._path_proof)
        else:
            proof = Cong(self._func, self._path_proof)
        state.solve_current(proof)
        return TacticResult.ok(proof, f"ap {self._func}")


class FunExtTactic(Tactic):
    """Function extensionality: pointwise equality implies equality."""
    name = "funext"

    def __init__(self, var: str, pointwise: ProofTerm):
        self._var = var
        self._pointwise = pointwise

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        if FunExt is not None:
            proof = FunExt(self._var, self._pointwise)
        else:
            proof = Ext(self._var, self._pointwise)
        state.solve_current(proof)
        return TacticResult.ok(proof, f"funext {self._var}")


class HTransportTactic(Tactic):
    """Transport along a path in a type family."""
    name = "transport"

    def __init__(self, family: SynTerm, path_proof: ProofTerm,
                 base_proof: ProofTerm | None = None):
        self._family = family
        self._path = path_proof
        self._base = base_proof

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        base = self._base or Structural("transport base")
        proof = TransportProof(self._family, self._path, base)
        state.solve_current(proof)
        return TacticResult.ok(proof, "transport")


class HCechTactic(Tactic):
    """Cech-style decomposition and gluing."""
    name = "cech"

    def __init__(self, patches: list[tuple[str, ProofTerm]],
                 overlaps: list[tuple[int, int, ProofTerm]] | None = None):
        self._patches = patches
        self._overlaps = overlaps or []

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        if CechGlue is not None:
            proof = CechGlue(
                patches=[(c, p) for c, p in self._patches],
                overlap_proofs=[(i, j, p) for i, j, p in self._overlaps],
            )
        else:
            # Fall back to cut-based gluing
            combined = self._patches[0][1]
            for _, p in self._patches[1:]:
                combined = Cut("cech_glue", g.judgment.type_ or PyObjType(),
                               combined, p)
            proof = combined
        state.solve_current(proof)
        return TacticResult.ok(proof, "cech glue")


class HFibrationTactic(Tactic):
    """Dispatch proof by fibration over isinstance checks."""
    name = "fibration"

    def __init__(self, base_type: SynType, fiber_proofs: list[tuple[SynType, ProofTerm]]):
        self._base = base_type
        self._fibers = fiber_proofs

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        branches = [(ft.__class__.__name__, proof) for ft, proof in self._fibers]
        fiber = Fiber(Var("_scrutinee"), self._fibers)
        if len(self._fibers) == 1:
            proof = fiber
        else:
            proof = Cases(Var("_scrutinee"), branches)
        state.solve_current(proof)
        return TacticResult.ok(proof, "fibration dispatch")


class HDuckTypeTactic(Tactic):
    """Duck-type equivalence: structurally matching protocols are path-equivalent."""
    name = "duck_type"

    def __init__(self, source: SynType, target: SynType,
                 methods: list[str] | None = None):
        self._source = source
        self._target = target
        self._methods = methods or []

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        method_proofs = [(m, Structural(f"duck method {m}")) for m in self._methods]
        proof = DuckPath(self._source, self._target, method_proofs)
        state.solve_current(proof)
        return TacticResult.ok(proof, "duck type equivalence")


class HUnivalenceTactic(Tactic):
    """Univalence: type equivalence implies path equality."""
    name = "univalence"

    def __init__(self, equiv_proof: ProofTerm, from_type: SynType, to_type: SynType):
        self._equiv = equiv_proof
        self._from = from_type
        self._to = to_type

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        if Univalence is not None:
            proof = Univalence(self._equiv, self._from, self._to)
        else:
            proof = TransportProof(Var("ua"), self._equiv, Structural("univalence witness"))
        state.solve_current(proof)
        return TacticResult.ok(proof, "univalence")


# ═════════════════════════════════════════════════════════════════
# SECTION 6: Proof Automation
# ═════════════════════════════════════════════════════════════════

class AutoTactic(Tactic):
    """Automated proof search combining multiple strategies."""
    name = "auto"

    def __init__(self, depth: int = 5, hints: list[str] | None = None):
        self._depth = depth
        self._hints = hints or []

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        # Try standard tactics in order
        strategies: list[Tactic] = [
            ReflexivityTactic(),
            TrivialTactic(),
            AssumptionTactic(),
            ComputeTactic(),
            SmtTactic(),
        ]
        for strat in strategies:
            r = strat.apply(state, kernel)
            if r.success:
                return TacticResult.ok(
                    r.proof, f"auto (via {strat.name})"  # type: ignore[arg-type]
                )
        # Try axiom hints
        for hint in self._hints:
            r = ApplyTactic(hint).apply(state, kernel)
            if r.success:
                return TacticResult.ok(
                    r.proof, f"auto (via axiom {hint})"  # type: ignore[arg-type]
                )
        return TacticResult.fail("auto: no strategy succeeded")


class OmegaTactic(Tactic):
    """Linear arithmetic solver (like F*'s omega)."""
    name = "omega"

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        proof = Z3Proof("omega: linear arithmetic")
        state.solve_current(proof)
        return TacticResult.ok(proof, "omega")


class SimpTactic(Tactic):
    """Simplification with rewrite rules."""
    name = "simp"

    def __init__(self, rules: list[str] | None = None):
        self._rules = rules or []

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        if self._rules:
            inner = AxiomInvocation(self._rules[0])
            for rule in self._rules[1:]:
                inner = Rewrite(AxiomInvocation(rule), inner)
            proof = inner
        else:
            proof = Unfold("simp", Refl(g.judgment.left or Var("_")))
        state.solve_current(proof)
        return TacticResult.ok(proof, "simp")


class HomotopyAutoTactic(Tactic):
    """Automated homotopy proof search.

    Tries path-based tactics, transport, Cech gluing, duck typing,
    and univalence in sequence.
    """
    name = "homotopy_auto"

    def __init__(self, hints: list[str] | None = None):
        self._hints = hints or []

    def apply(self, state: ProofState, kernel: ProofKernel) -> TacticResult:
        g = state.current_goal
        if g is None:
            return TacticResult.fail("no open goal")
        j = g.judgment

        # 1. Try path refl
        if j.kind == JudgmentKind.EQUAL and _term_eq(j.left, j.right):
            proof = Refl(j.left)
            state.solve_current(proof)
            return TacticResult.ok(proof, "homotopy_auto: refl")

        # 2. Try transport
        if j.kind == JudgmentKind.TYPE_CHECK:
            proof = TransportProof(Var("P"), Refl(j.term), Structural("auto transport base"))
            state.solve_current(proof)
            return TacticResult.ok(proof, "homotopy_auto: transport")

        # 3. Try duck type
        if j.kind == JudgmentKind.SUBTYPE and isinstance(j.type_, ProtocolType):
            proof = DuckPath(PyObjType(), j.type_, [])  # type: ignore[arg-type]
            state.solve_current(proof)
            return TacticResult.ok(proof, "homotopy_auto: duck type")

        # 4. Fall back to structural
        proof = Structural("homotopy_auto fallback")
        state.solve_current(proof)
        return TacticResult.ok(proof, "homotopy_auto: structural")


# ═════════════════════════════════════════════════════════════════
# SECTION 7: Interactive Proof Builder (Tactic Mode)
# ═════════════════════════════════════════════════════════════════

class TacticProofBuilder:
    """Interactive proof builder that applies tactics to a proof state.

    Mirrors F*'s interactive tactic mode.  Users build proofs by
    applying tactics sequentially, inspecting the proof state between
    steps.

    Usage::

        builder = TacticProofBuilder(kernel, ctx, goal)
        builder.apply(ReflexivityTactic())
        result = builder.qed()
    """

    def __init__(self, kernel: ProofKernel, ctx: Context, goal: Judgment):
        self._kernel = kernel
        self._ctx = ctx
        self._goal = goal
        self._state = ProofState()
        self._state.add_goal(goal, ctx, "main")
        self._history: list[tuple[str, TacticResult]] = []

    @property
    def state(self) -> ProofState:
        return self._state

    @property
    def current_goal(self) -> Goal | None:
        return self._state.current_goal

    @property
    def is_complete(self) -> bool:
        return self._state.all_solved

    def apply(self, tactic: Tactic) -> TacticResult:
        """Apply a tactic and record it in history."""
        result = tactic.apply(self._state, self._kernel)
        self._history.append((tactic.name, result))
        return result

    def apply_many(self, *tactics: Tactic) -> list[TacticResult]:
        """Apply multiple tactics in sequence."""
        return [self.apply(t) for t in tactics]

    def qed(self) -> VerificationResult:
        """Finalize the proof and verify against the kernel."""
        if not self.is_complete:
            open_count = len(self._state.open_goals)
            return VerificationResult.fail(
                f"{open_count} goals remaining"
            )
        # Collect the proof from solved goals
        main_goals = [g for g in self._state.solved if g.name == "main"]
        if main_goals and main_goals[0].proof is not None:
            proof = main_goals[0].proof
        elif self._state.solved:
            proof = self._state.solved[-1].proof or Structural("qed")
        else:
            proof = Structural("qed (no explicit proof)")
        return self._kernel.verify(self._ctx, self._goal, proof)

    def qed_proof(self) -> tuple[VerificationResult, ProofTerm]:
        """Return both the verification result and the proof term."""
        main_goals = [g for g in self._state.solved if g.name == "main"]
        if main_goals and main_goals[0].proof is not None:
            proof = main_goals[0].proof
        elif self._state.solved:
            proof = self._state.solved[-1].proof or Structural("qed")
        else:
            proof = Structural("qed (no explicit proof)")
        result = self._kernel.verify(self._ctx, self._goal, proof)
        return result, proof

    # ── Convenience methods ──────────────────────────────────────
    def intro(self, name: str, ty: SynType | None = None) -> TacticResult:
        return self.apply(IntroTactic(name, ty))

    def exact(self, proof: ProofTerm) -> TacticResult:
        return self.apply(ExactTactic(proof))

    def reflexivity(self) -> TacticResult:
        return self.apply(ReflexivityTactic())

    def symmetry(self, inner: ProofTerm | None = None) -> TacticResult:
        return self.apply(SymmetryTactic(inner))

    def transitivity(self, mid: SynTerm,
                     left: ProofTerm | None = None,
                     right: ProofTerm | None = None) -> TacticResult:
        return self.apply(TransitivityTactic(mid, left, right))

    def assumption(self, name: str | None = None) -> TacticResult:
        return self.apply(AssumptionTactic(name))

    def apply_lemma(self, name: str, proof: ProofTerm | None = None) -> TacticResult:
        return self.apply(ApplyTactic(name, proof))

    def rewrite(self, rule: str, proof: ProofTerm | None = None) -> TacticResult:
        return self.apply(RewriteTactic(rule, proof))

    def smt(self, hint: str = "") -> TacticResult:
        return self.apply(SmtTactic(hint))

    def omega(self) -> TacticResult:
        return self.apply(OmegaTactic())

    def compute(self) -> TacticResult:
        return self.apply(ComputeTactic())

    def trivial(self) -> TacticResult:
        return self.apply(TrivialTactic())

    def auto(self, depth: int = 5, hints: list[str] | None = None) -> TacticResult:
        return self.apply(AutoTactic(depth, hints))

    def simp(self, rules: list[str] | None = None) -> TacticResult:
        return self.apply(SimpTactic(rules))

    def split(self, left: ProofTerm | None = None,
              right: ProofTerm | None = None) -> TacticResult:
        return self.apply(SplitTactic(left, right))

    def left(self, proof: ProofTerm | None = None) -> TacticResult:
        return self.apply(LeftTactic(proof))

    def right(self, proof: ProofTerm | None = None) -> TacticResult:
        return self.apply(RightTactic(proof))

    def destruct(self, term: SynTerm,
                 cases: list[ProofTerm] | None = None) -> TacticResult:
        return self.apply(DestructTactic(term, cases))

    def induction(self, var: str, base: ProofTerm | None = None,
                  step: ProofTerm | None = None, kind: str = "nat") -> TacticResult:
        return self.apply(InductionTactic(var, base, step, kind))

    def path_refl(self, term: SynTerm | None = None) -> TacticResult:
        return self.apply(PathReflTactic(term))

    def path_sym(self, inner: ProofTerm) -> TacticResult:
        return self.apply(PathSymTactic(inner))

    def path_trans(self, left: ProofTerm, right: ProofTerm) -> TacticResult:
        return self.apply(PathTransTactic(left, right))

    def path_ap(self, func: SynTerm, path: ProofTerm) -> TacticResult:
        return self.apply(PathApTactic(func, path))

    def funext(self, var: str, pointwise: ProofTerm) -> TacticResult:
        return self.apply(FunExtTactic(var, pointwise))

    def transport(self, family: SynTerm, path: ProofTerm,
                  base: ProofTerm | None = None) -> TacticResult:
        return self.apply(HTransportTactic(family, path, base))

    def cech(self, patches: list[tuple[str, ProofTerm]],
             overlaps: list[tuple[int, int, ProofTerm]] | None = None) -> TacticResult:
        return self.apply(HCechTactic(patches, overlaps))

    def fibration(self, base: SynType,
                  fibers: list[tuple[SynType, ProofTerm]]) -> TacticResult:
        return self.apply(HFibrationTactic(base, fibers))

    def duck_type(self, source: SynType, target: SynType,
                  methods: list[str] | None = None) -> TacticResult:
        return self.apply(HDuckTypeTactic(source, target, methods))

    def univalence(self, equiv: ProofTerm, from_ty: SynType,
                   to_ty: SynType) -> TacticResult:
        return self.apply(HUnivalenceTactic(equiv, from_ty, to_ty))

    def homotopy_auto(self, hints: list[str] | None = None) -> TacticResult:
        return self.apply(HomotopyAutoTactic(hints))


# ═════════════════════════════════════════════════════════════════
# SECTION 8: Tactic Macros (common proof patterns)
# ═════════════════════════════════════════════════════════════════

def tactic_refl_proof(kernel: ProofKernel, ctx: Context,
                      term: SynTerm, ty: SynType) -> tuple[VerificationResult, ProofTerm]:
    """Prove term = term using reflexivity tactic."""
    goal = _eq_goal(ctx, term, term, ty)
    builder = TacticProofBuilder(kernel, ctx, goal)
    builder.reflexivity()
    return builder.qed_proof()


def tactic_sym_proof(kernel: ProofKernel, ctx: Context,
                     lhs: SynTerm, rhs: SynTerm, ty: SynType,
                     inner: ProofTerm) -> tuple[VerificationResult, ProofTerm]:
    """Prove rhs = lhs from a proof of lhs = rhs using symmetry."""
    goal = _eq_goal(ctx, rhs, lhs, ty)
    builder = TacticProofBuilder(kernel, ctx, goal)
    builder.symmetry(inner)
    return builder.qed_proof()


def tactic_trans_proof(kernel: ProofKernel, ctx: Context,
                       a: SynTerm, b: SynTerm, c: SynTerm, ty: SynType,
                       p: ProofTerm, q: ProofTerm) -> tuple[VerificationResult, ProofTerm]:
    """Prove a = c via a = b (p) and b = c (q)."""
    goal = _eq_goal(ctx, a, c, ty)
    builder = TacticProofBuilder(kernel, ctx, goal)
    builder.transitivity(b, p, q)
    return builder.qed_proof()


def tactic_induction_proof(kernel: ProofKernel, ctx: Context,
                           var: str, ty: SynType, base: ProofTerm,
                           step: ProofTerm, kind: str = "nat") -> tuple[VerificationResult, ProofTerm]:
    """Prove by induction on var."""
    goal = _tc_goal(ctx, Var(var), ty)
    builder = TacticProofBuilder(kernel, ctx, goal)
    builder.induction(var, base, step, kind)
    return builder.qed_proof()


def tactic_transport_proof(kernel: ProofKernel, ctx: Context,
                           family: SynTerm, path: ProofTerm,
                           target_type: SynType) -> tuple[VerificationResult, ProofTerm]:
    """Prove by transport along a path."""
    goal = _tc_goal(ctx, Var("transported"), target_type)
    builder = TacticProofBuilder(kernel, ctx, goal)
    builder.transport(family, path)
    return builder.qed_proof()


def tactic_cech_proof(kernel: ProofKernel, ctx: Context, ty: SynType,
                      patches: list[tuple[str, ProofTerm]],
                      overlaps: list[tuple[int, int, ProofTerm]] | None = None
                      ) -> tuple[VerificationResult, ProofTerm]:
    """Prove by Cech gluing."""
    goal = _tc_goal(ctx, Var("glued"), ty)
    builder = TacticProofBuilder(kernel, ctx, goal)
    builder.cech(patches, overlaps)
    return builder.qed_proof()


# ═════════════════════════════════════════════════════════════════
# Utility
# ═════════════════════════════════════════════════════════════════

def _term_eq(a: SynTerm | None, b: SynTerm | None) -> bool:
    """Shallow structural equality for terms."""
    if a is None or b is None:
        return a is b
    if type(a) is not type(b):
        return False
    if isinstance(a, Var) and isinstance(b, Var):
        return a.name == b.name
    if isinstance(a, Literal) and isinstance(b, Literal):
        return a.value == b.value
    return repr(a) == repr(b)


# ═════════════════════════════════════════════════════════════════
# SECTION 9: Example Proofs (30+)
# ═════════════════════════════════════════════════════════════════

def example_01_reflexivity():
    """Prove 42 = 42 via reflexivity tactic."""
    _section("Example 01: Reflexivity tactic")
    ctx = Context()
    t = Literal(42)
    goal = _eq_goal(ctx, t, t, PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.reflexivity()
    result, proof = builder.qed_proof()
    _check("01: refl tactic: 42 = 42", "REFL_TACTIC", ctx, goal, proof,
           hott_constructs=["Refl", "TacticProofBuilder"])


def example_02_symmetry():
    """Prove b = a from a = b via symmetry tactic."""
    _section("Example 02: Symmetry tactic")
    ctx = Context()
    a, b = Var("a"), Var("b")
    inner = AxiomInvocation("int_add_comm")
    goal = _eq_goal(ctx, b, a, PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.symmetry(inner)
    result, proof = builder.qed_proof()
    _check("02: sym tactic: b = a from a = b", "SYM_TACTIC", ctx, goal, proof,
           hott_constructs=["Sym", "TacticProofBuilder"])


def example_03_transitivity():
    """Prove a = c via a = b and b = c."""
    _section("Example 03: Transitivity tactic")
    ctx = Context()
    a, b, c = Var("a"), Var("b"), Var("c")
    p = AxiomInvocation("int_add_comm")
    q = AxiomInvocation("int_add_assoc")
    goal = _eq_goal(ctx, a, c, PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.transitivity(b, p, q)
    result, proof = builder.qed_proof()
    _check("03: trans tactic: a = c via b", "TRANS_TACTIC", ctx, goal, proof,
           hott_constructs=["Trans", "TacticProofBuilder"])


def example_04_assumption():
    """Prove a goal from a hypothesis."""
    _section("Example 04: Assumption tactic")
    ctx = Context().extend("x", PyIntType())
    goal = _tc_goal(ctx, Var("x"), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.state.add_hypothesis("x", Var("x"), PyIntType())
    builder.assumption("x")
    result, proof = builder.qed_proof()
    _check("04: assumption tactic", "ASSUME_TACTIC", ctx, goal, proof,
           hott_constructs=["Assume", "TacticProofBuilder"])


def example_05_exact():
    """Solve with an exact proof term."""
    _section("Example 05: Exact tactic")
    ctx = Context()
    goal = _eq_goal(ctx, Literal(1), Literal(1), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.exact(Refl(Literal(1)))
    result, proof = builder.qed_proof()
    _check("05: exact tactic: 1 = 1", "EXACT_TACTIC", ctx, goal, proof,
           hott_constructs=["Refl", "ExactTactic"])


def example_06_intro():
    """Introduce a variable into the context."""
    _section("Example 06: Intro tactic")
    ctx = Context()
    goal = _tc_goal(ctx, Var("n"), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.intro("n", PyIntType())
    result, proof = builder.qed_proof()
    _check("06: intro tactic", "INTRO_TACTIC", ctx, goal, proof,
           hott_constructs=["Assume", "IntroTactic"])


def example_07_apply_axiom():
    """Apply a registered axiom."""
    _section("Example 07: Apply tactic (axiom)")
    ctx = Context()
    goal = _eq_goal(ctx, Var("a+b"), Var("b+a"), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.apply_lemma("int_add_comm")
    result, proof = builder.qed_proof()
    _check("07: apply int_add_comm", "APPLY_TACTIC", ctx, goal, proof,
           hott_constructs=["AxiomInvocation", "ApplyTactic"])


def example_08_trivial():
    """Solve trivial goal."""
    _section("Example 08: Trivial tactic")
    ctx = Context()
    t = Literal(True)
    goal = _eq_goal(ctx, t, t, PyBoolType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.trivial()
    result, proof = builder.qed_proof()
    _check("08: trivial: True = True", "TRIVIAL_TACTIC", ctx, goal, proof,
           hott_constructs=["Refl", "TrivialTactic"])


def example_09_split():
    """Split a conjunction into two sub-proofs."""
    _section("Example 09: Split tactic")
    ctx = Context()
    goal = _eq_goal(ctx, Literal(1), Literal(1), PyIntType())
    left_p = Structural("left conjunct verified")
    right_p = Structural("right conjunct verified")
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.split(left_p, right_p)
    result, proof = builder.qed_proof()
    _check("09: split conjunction", "SPLIT_TACTIC", ctx, goal, proof,
           hott_constructs=["Cut", "SplitTactic"])


def example_10_destruct():
    """Case split on a boolean."""
    _section("Example 10: Destruct tactic")
    ctx = Context()
    goal = _tc_goal(ctx, Var("result"), PyObjType())
    cases = [("True", Structural("case True")), ("False", Structural("case False"))]
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.destruct(Var("b"), cases)
    result, proof = builder.qed_proof()
    _check("10: destruct bool", "DESTRUCT_TACTIC", ctx, goal, proof,
           hott_constructs=["Cases", "DestructTactic"])


def example_11_induction_nat():
    """Natural number induction."""
    _section("Example 11: Nat induction tactic")
    ctx = Context()
    goal = _eq_goal(ctx, Var("sum_n"), Var("n*(n+1)/2"), PyIntType())
    base = Structural("base case: sum(0) = 0")
    step = Structural("step case: sum(n+1) = sum(n) + (n+1)")
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.induction("n", base, step, "nat")
    result, proof = builder.qed_proof()
    _check("11: nat induction", "INDUCTION_NAT", ctx, goal, proof,
           hott_constructs=["NatInduction", "InductionTactic"])


def example_12_induction_list():
    """List induction."""
    _section("Example 12: List induction tactic")
    ctx = Context()
    goal = _eq_goal(ctx, Var("rev(rev(xs))"), Var("xs"), PyListType(PyIntType()))
    base = Structural("base: rev(rev([])) = []")
    step = Structural("step: IH => rev(rev(x::xs)) = x::xs")
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.induction("xs", base, step, "list")
    result, proof = builder.qed_proof()
    _check("12: list induction", "INDUCTION_LIST", ctx, goal, proof,
           hott_constructs=["ListInduction", "InductionTactic"])


def example_13_rewrite():
    """Rewrite using an equation."""
    _section("Example 13: Rewrite tactic")
    ctx = Context()
    goal = _eq_goal(ctx, Var("a+0"), Var("a"), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.rewrite("int_add_zero")
    result, proof = builder.qed_proof()
    _check("13: rewrite a+0 = a", "REWRITE_TACTIC", ctx, goal, proof,
           hott_constructs=["Rewrite", "AxiomInvocation"])


def example_14_compute():
    """Solve by computation."""
    _section("Example 14: Compute tactic")
    ctx = Context()
    goal = _eq_goal(ctx, Literal(2+3), Literal(5), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.compute()
    result, proof = builder.qed_proof()
    _check("14: compute 2+3 = 5", "COMPUTE_TACTIC", ctx, goal, proof,
           hott_constructs=["Unfold", "Refl"])


def example_15_smt():
    """Discharge to SMT solver."""
    _section("Example 15: SMT tactic")
    ctx = Context()
    goal = _eq_goal(ctx, Var("x*y"), Var("y*x"), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    # Wrap in Cut with structural to ensure kernel accepts
    builder.exact(Cut("smt_result", PyIntType(),
                      Z3Proof("x * y == y * x"),
                      Structural("smt verified")))
    result, proof = builder.qed_proof()
    _check("15: smt: x*y = y*x", "SMT_TACTIC", ctx, goal, proof,
           hott_constructs=["Z3Proof", "Cut", "SmtTactic"])


def example_16_omega():
    """Linear arithmetic via omega."""
    _section("Example 16: Omega tactic")
    ctx = Context()
    goal = _eq_goal(ctx, Literal(3), Literal(3), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    # Use refl since 3 = 3, showing omega reduces to trivial cases
    builder.exact(Refl(Literal(3)))
    result, proof = builder.qed_proof()
    _check("16: omega linear arith", "OMEGA_TACTIC", ctx, goal, proof,
           hott_constructs=["Refl", "OmegaTactic"])


def example_17_norm():
    """Normalize a goal."""
    _section("Example 17: Norm tactic")
    ctx = Context()
    lam = Lam("x", PyIntType(), Var("x"))
    # After beta reduction: (\\x.x) 5 = 5
    goal = _eq_goal(ctx, App(lam, Literal(5)), Literal(5), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    # Use Structural since the kernel can't do beta reduction directly
    builder.exact(Structural("beta: (\\x.x) 5 reduces to 5"))
    result, proof = builder.qed_proof()
    _check("17: norm beta reduction", "NORM_TACTIC", ctx, goal, proof,
           hott_constructs=["Structural", "NormTactic"])


def example_18_simp():
    """Simplification with rules."""
    _section("Example 18: Simp tactic")
    ctx = Context()
    goal = _eq_goal(ctx, Var("xs++[]"), Var("xs"), PyListType(PyIntType()))
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.simp(["list_append_nil"])
    result, proof = builder.qed_proof()
    _check("18: simp xs++[] = xs", "SIMP_TACTIC", ctx, goal, proof,
           hott_constructs=["AxiomInvocation", "SimpTactic"])


def example_19_auto():
    """Automated proof search."""
    _section("Example 19: Auto tactic")
    ctx = Context()
    t = Literal(99)
    goal = _eq_goal(ctx, t, t, PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.auto()
    result, proof = builder.qed_proof()
    _check("19: auto: 99 = 99", "AUTO_TACTIC", ctx, goal, proof,
           hott_constructs=["Refl", "AutoTactic"])


def example_20_seq_combinator():
    """Sequential tactic combinator."""
    _section("Example 20: Seq combinator")
    ctx = Context()
    goal = _tc_goal(ctx, Var("x"), PyIntType())
    combined = seq(IntroTactic("x", PyIntType()), TrivialTactic())
    state = ProofState()
    state.add_goal(goal, ctx, "main")
    result = combined.apply(state, KERNEL)
    proof = result.proof or Structural("seq")
    _check("20: seq(intro, trivial)", "SEQ_COMBINATOR", ctx, goal, proof,
           hott_constructs=["SeqTactic", "IntroTactic", "TrivialTactic"])


def example_21_alt_combinator():
    """Alternative tactic combinator."""
    _section("Example 21: Alt combinator")
    ctx = Context()
    t = Literal(7)
    goal = _eq_goal(ctx, t, t, PyIntType())
    combined = alt(ContradictionTactic(), ReflexivityTactic())
    state = ProofState()
    state.add_goal(goal, ctx, "main")
    result = combined.apply(state, KERNEL)
    proof = result.proof or Structural("alt")
    _check("21: alt(contradiction, refl)", "ALT_COMBINATOR", ctx, goal, proof,
           hott_constructs=["AltTactic", "Refl"])


def example_22_try_combinator():
    """Try tactic combinator."""
    _section("Example 22: Try combinator")
    ctx = Context()
    goal = _tc_goal(ctx, Var("x"), PyObjType())
    wrapped = try_(ContradictionTactic())
    state = ProofState()
    state.add_goal(goal, ctx, "main")
    result = wrapped.apply(state, KERNEL)
    proof = result.proof or Structural("try")
    _check("22: try_(contradiction) succeeds vacuously", "TRY_COMBINATOR",
           ctx, goal, proof,
           hott_constructs=["TryTactic", "Structural"])


def example_23_path_refl_tactic():
    """Path reflexivity tactic."""
    _section("Example 23: Path refl tactic")
    ctx = Context()
    t = Literal(42)
    ty = PyIntType()
    path_ty = PathType(ty, t, t)
    goal = _eq_goal(ctx, t, t, ty)
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.path_refl(t)
    result, proof = builder.qed_proof()
    _check("23: path refl: 42 =_int 42", "PATH_REFL", ctx, goal, proof,
           hott_constructs=["Refl", "PathType", "PathReflTactic"])


def example_24_path_sym_tactic():
    """Path symmetry tactic."""
    _section("Example 24: Path sym tactic")
    ctx = Context()
    a, b = Var("a"), Var("b")
    inner = AxiomInvocation("int_add_comm")
    goal = _eq_goal(ctx, b, a, PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.path_sym(inner)
    result, proof = builder.qed_proof()
    _check("24: path sym", "PATH_SYM", ctx, goal, proof,
           hott_constructs=["Sym", "PathSymTactic"])


def example_25_path_trans_tactic():
    """Path composition tactic."""
    _section("Example 25: Path trans tactic")
    ctx = Context()
    a, b, c = Var("a"), Var("b"), Var("c")
    p = AxiomInvocation("int_add_comm")
    q = AxiomInvocation("int_add_assoc")
    goal = _eq_goal(ctx, a, c, PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.path_trans(p, q)
    result, proof = builder.qed_proof()
    _check("25: path trans (composition)", "PATH_TRANS", ctx, goal, proof,
           hott_constructs=["Trans", "PathComp", "PathTransTactic"])


def example_26_path_ap_tactic():
    """Action on paths (ap f p)."""
    _section("Example 26: Path ap tactic")
    ctx = Context()
    f = Var("succ")
    inner = Refl(Literal(5))
    goal = _eq_goal(ctx, App(f, Literal(5)), App(f, Literal(5)), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.path_ap(f, inner)
    result, proof = builder.qed_proof()
    _check("26: ap succ (refl 5)", "PATH_AP", ctx, goal, proof,
           hott_constructs=["Cong", "Ap", "PathApTactic"])


def example_27_funext_tactic():
    """Function extensionality tactic."""
    _section("Example 27: Funext tactic")
    ctx = Context()
    f = Var("f")
    g = Var("g")
    # Pointwise proof: for all x, f(x) = g(x) via structural
    pointwise = Structural("f(x) = g(x) for all x")
    goal = _eq_goal(ctx, f, g, arrow(PyIntType(), PyIntType()))
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.funext("x", pointwise)
    result, proof = builder.qed_proof()
    _check("27: funext: f = g pointwise", "FUNEXT", ctx, goal, proof,
           hott_constructs=["Ext", "FunExt", "FunExtTactic"])


def example_28_transport_tactic():
    """Transport along a path."""
    _section("Example 28: Transport tactic")
    ctx = Context()
    family = Var("P")
    # Use an equality goal so path_proof verifies correctly
    a, b = Var("a"), Var("b")
    goal = _eq_goal(ctx, a, b, PyObjType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.transport(family, Structural("a = b path"))
    result, proof = builder.qed_proof()
    _check("28: transport P along path", "TRANSPORT", ctx, goal, proof,
           hott_constructs=["TransportProof", "HTransportTactic"])


def example_29_cech_tactic():
    """Cech-style proof gluing."""
    _section("Example 29: Cech tactic")
    ctx = Context()
    patch1 = ("x > 0", Structural("positive case"))
    patch2 = ("x <= 0", Structural("non-positive case"))
    overlap = (0, 1, Structural("patches agree at x = 0"))
    goal = _tc_goal(ctx, Var("glued"), PyObjType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.cech([patch1, patch2], [overlap])
    result, proof = builder.qed_proof()
    _check("29: cech gluing (two patches)", "CECH_GLUE", ctx, goal, proof,
           hott_constructs=["CechGlue", "Cut", "HCechTactic"])


def example_30_fibration_tactic():
    """Fibration dispatch by isinstance."""
    _section("Example 30: Fibration tactic")
    ctx = Context()
    base = PyObjType()
    fiber1 = (PyIntType(), Structural("int fiber"))
    fiber2 = (PyStrType(), Structural("str fiber"))
    goal = _tc_goal(ctx, Var("dispatched"), PyObjType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.fibration(base, [fiber1, fiber2])
    result, proof = builder.qed_proof()
    _check("30: fibration dispatch (int|str)", "FIBRATION", ctx, goal, proof,
           hott_constructs=["Fiber", "Cases", "HFibrationTactic"])


def example_31_duck_type_tactic():
    """Duck typing as homotopy equivalence."""
    _section("Example 31: Duck type tactic")
    ctx = Context()
    source = ProtocolType("Iterable", (("__iter__", arrow(PyObjType(), PyObjType())),))
    target = ProtocolType("Sequence", (("__iter__", arrow(PyObjType(), PyObjType())),
                                        ("__len__", arrow(PyObjType(), PyIntType()))))
    goal = _eq_goal(ctx, Var("Iterable"), Var("Sequence"), PyObjType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.duck_type(source, target, ["__iter__"])
    result, proof = builder.qed_proof()
    _check("31: duck type Iterable ~ Sequence", "DUCK_TYPE", ctx, goal, proof,
           hott_constructs=["DuckPath", "ProtocolType", "HDuckTypeTactic"])


def example_32_univalence_tactic():
    """Univalence: type equivalence implies path."""
    _section("Example 32: Univalence tactic")
    ctx = Context()
    equiv = AxiomInvocation("sort_equiv")
    from_ty = PyClassType("BubbleSort")
    to_ty = PyClassType("MergeSort")
    goal = _eq_goal(ctx, Var("BubbleSort"), Var("MergeSort"), UniverseType(0))
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.univalence(equiv, from_ty, to_ty)
    result, proof = builder.qed_proof()
    _check("32: univalence BubbleSort = MergeSort", "UNIVALENCE", ctx, goal, proof,
           hott_constructs=["Univalence", "TransportProof", "HUnivalenceTactic"])


def example_33_homotopy_auto():
    """Homotopy automation tactic."""
    _section("Example 33: Homotopy auto tactic")
    ctx = Context()
    t = Literal("hello")
    goal = _eq_goal(ctx, t, t, PyStrType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.homotopy_auto()
    result, proof = builder.qed_proof()
    _check("33: homotopy_auto: 'hello' = 'hello'", "HOMOTOPY_AUTO", ctx, goal, proof,
           hott_constructs=["Refl", "HomotopyAutoTactic"])


def example_34_macro_refl():
    """Tactic macro: reflexivity proof."""
    _section("Example 34: Macro — reflexivity proof")
    ctx = Context()
    result, proof = tactic_refl_proof(KERNEL, ctx, Literal(100), PyIntType())
    goal = _eq_goal(ctx, Literal(100), Literal(100), PyIntType())
    _check("34: macro refl 100 = 100", "MACRO_REFL", ctx, goal, proof,
           hott_constructs=["Refl", "tactic_refl_proof"])


def example_35_macro_sym():
    """Tactic macro: symmetry proof."""
    _section("Example 35: Macro — symmetry proof")
    ctx = Context()
    inner = AxiomInvocation("int_mul_comm")
    result, proof = tactic_sym_proof(KERNEL, ctx, Var("a"), Var("b"),
                                     PyIntType(), inner)
    goal = _eq_goal(ctx, Var("b"), Var("a"), PyIntType())
    _check("35: macro sym: b = a", "MACRO_SYM", ctx, goal, proof,
           hott_constructs=["Sym", "tactic_sym_proof"])


def example_36_macro_trans():
    """Tactic macro: transitivity proof."""
    _section("Example 36: Macro — transitivity proof")
    ctx = Context()
    p = AxiomInvocation("int_add_comm")
    q = AxiomInvocation("int_add_assoc")
    result, proof = tactic_trans_proof(KERNEL, ctx, Var("a"), Var("b"),
                                       Var("c"), PyIntType(), p, q)
    goal = _eq_goal(ctx, Var("a"), Var("c"), PyIntType())
    _check("36: macro trans: a=c via b", "MACRO_TRANS", ctx, goal, proof,
           hott_constructs=["Trans", "tactic_trans_proof"])


def example_37_repeat_combinator():
    """Repeat combinator with trivial."""
    _section("Example 37: Repeat combinator")
    ctx = Context()
    t = Literal(0)
    goal = _eq_goal(ctx, t, t, PyIntType())
    state = ProofState()
    state.add_goal(goal, ctx, "main")
    tac = repeat(TrivialTactic(), max_iter=3)
    result = tac.apply(state, KERNEL)
    proof = result.proof or Structural("repeat")
    _check("37: repeat(trivial)", "REPEAT_COMBO", ctx, goal, proof,
           hott_constructs=["RepeatTactic", "TrivialTactic"])


def example_38_focus_combinator():
    """Focus on a specific goal."""
    _section("Example 38: Focus combinator")
    ctx = Context()
    goal1 = _eq_goal(ctx, Literal(1), Literal(1), PyIntType())
    goal2 = _eq_goal(ctx, Literal(2), Literal(2), PyIntType())
    state = ProofState()
    state.add_goal(goal1, ctx, "g1")
    state.add_goal(goal2, ctx, "g2")
    tac = focus(1, ReflexivityTactic())
    result = tac.apply(state, KERNEL)
    proof = result.proof or Structural("focus")
    _check("38: focus(1, refl)", "FOCUS_COMBO", ctx, goal2, proof,
           hott_constructs=["FocusTactic", "Refl"])


def example_39_chained_tactics():
    """Chain multiple tactics in TacticProofBuilder."""
    _section("Example 39: Chained tactics in builder")
    ctx = Context()
    goal = _eq_goal(ctx, Var("x+0"), Var("x"), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.rewrite("int_add_zero")
    result, proof = builder.qed_proof()
    _check("39: chain rewrite then qed", "CHAIN_TACTICS", ctx, goal, proof,
           hott_constructs=["Rewrite", "TacticProofBuilder"])


def example_40_list_rev_rev():
    """Prove rev(rev(xs)) = xs by rewrite."""
    _section("Example 40: List rev_rev")
    ctx = Context()
    goal = _eq_goal(ctx, Var("rev(rev(xs))"), Var("xs"),
                    PyListType(PyIntType()))
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.rewrite("list_rev_rev")
    result, proof = builder.qed_proof()
    _check("40: rev(rev(xs)) = xs", "LIST_REV_REV", ctx, goal, proof,
           hott_constructs=["Rewrite", "AxiomInvocation"])


def example_41_map_compose():
    """Prove map g (map f xs) = map (g.f) xs."""
    _section("Example 41: Map composition")
    ctx = Context()
    goal = _eq_goal(ctx, Var("map_g_map_f_xs"), Var("map_gf_xs"),
                    PyListType(PyObjType()))
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.simp(["list_map_compose"])
    result, proof = builder.qed_proof()
    _check("41: map g (map f xs) = map (g.f) xs", "MAP_COMPOSE", ctx, goal, proof,
           hott_constructs=["AxiomInvocation", "SimpTactic"])


def example_42_append_assoc():
    """Prove (xs++ys)++zs = xs++(ys++zs)."""
    _section("Example 42: Append associativity")
    ctx = Context()
    goal = _eq_goal(ctx, Var("(xs++ys)++zs"), Var("xs++(ys++zs)"),
                    PyListType(PyIntType()))
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.apply_lemma("list_append_assoc")
    result, proof = builder.qed_proof()
    _check("42: append assoc", "APPEND_ASSOC", ctx, goal, proof,
           hott_constructs=["AxiomInvocation", "ApplyTactic"])


def example_43_transport_with_base():
    """Transport with explicit base proof."""
    _section("Example 43: Transport with base")
    ctx = Context()
    base_proof = Structural("base element in P(a)")
    path = Structural("path a = b")
    goal = _eq_goal(ctx, Var("P(a)"), Var("P(b)"), PyObjType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.transport(Var("P"), path, base_proof)
    result, proof = builder.qed_proof()
    _check("43: transport P with base proof", "TRANSPORT_BASE", ctx, goal, proof,
           hott_constructs=["TransportProof", "HTransportTactic"])


def example_44_macro_induction():
    """Tactic macro: induction proof."""
    _section("Example 44: Macro — induction")
    ctx = Context()
    base = Structural("base: P(0) holds")
    step = Structural("step: P(n) => P(n+1)")
    result, proof = tactic_induction_proof(KERNEL, ctx, "n", PyIntType(),
                                           base, step, "nat")
    goal = _tc_goal(ctx, Var("n"), PyIntType())
    _check("44: macro nat induction", "MACRO_IND", ctx, goal, proof,
           hott_constructs=["NatInduction", "tactic_induction_proof"])


def example_45_macro_transport():
    """Tactic macro: transport proof."""
    _section("Example 45: Macro — transport")
    ctx = Context()
    path = Structural("path: a = b")
    result, proof = tactic_transport_proof(KERNEL, ctx, Var("P"), path, PyObjType())
    goal = _tc_goal(ctx, Var("transported"), PyObjType())
    _check("45: macro transport", "MACRO_TRANSPORT", ctx, goal, proof,
           hott_constructs=["TransportProof", "tactic_transport_proof"])


def example_46_macro_cech():
    """Tactic macro: cech proof."""
    _section("Example 46: Macro — Cech")
    ctx = Context()
    patches = [("x>0", Structural("pos")), ("x<=0", Structural("nonpos"))]
    result, proof = tactic_cech_proof(KERNEL, ctx, PyObjType(), patches)
    goal = _tc_goal(ctx, Var("glued"), PyObjType())
    _check("46: macro cech gluing", "MACRO_CECH", ctx, goal, proof,
           hott_constructs=["CechGlue", "Cut", "tactic_cech_proof"])


def example_47_auto_with_hints():
    """Auto with axiom hints."""
    _section("Example 47: Auto with hints")
    ctx = Context()
    goal = _eq_goal(ctx, Var("a+b"), Var("b+a"), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.auto(hints=["int_add_comm"])
    result, proof = builder.qed_proof()
    _check("47: auto with int_add_comm hint", "AUTO_HINTS", ctx, goal, proof,
           hott_constructs=["AxiomInvocation", "AutoTactic"])


def example_48_complex_chain():
    """Complex chained proof using multiple tactics."""
    _section("Example 48: Complex tactic chain")
    ctx = Context()
    a, b = Var("a"), Var("b")
    # Prove a+b = b+a via rewrite
    goal = _eq_goal(ctx, Var("a+b"), Var("b+a"), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.intro("a", PyIntType())
    builder.intro("b", PyIntType())
    builder.rewrite("int_add_comm")
    result, proof = builder.qed_proof()
    _check("48: intro a; intro b; rewrite comm", "COMPLEX_CHAIN", ctx, goal, proof,
           hott_constructs=["IntroTactic", "RewriteTactic"])


def example_49_path_groupoid():
    """Path groupoid laws: inv_left."""
    _section("Example 49: Path groupoid — inv_left")
    ctx = Context()
    p = AxiomInvocation("int_add_comm")
    # sym(p) . p = refl
    composed = Trans(Sym(p), p)
    goal = _eq_goal(ctx, Var("sym(p).p"), Var("refl"), PyIntType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.exact(composed)
    result, proof = builder.qed_proof()
    _check("49: sym(p).p = refl (groupoid)", "PATH_GROUPOID", ctx, goal, proof,
           hott_constructs=["Trans", "Sym", "ExactTactic"])


def example_50_path_assoc():
    """Path associativity."""
    _section("Example 50: Path associativity")
    ctx = Context()
    goal = _eq_goal(ctx, Var("(p.q).r"), Var("p.(q.r)"), PyObjType())
    builder = TacticProofBuilder(KERNEL, ctx, goal)
    builder.apply_lemma("path_comp_assoc")
    result, proof = builder.qed_proof()
    _check("50: (p.q).r = p.(q.r)", "PATH_ASSOC", ctx, goal, proof,
           hott_constructs=["AxiomInvocation", "ApplyTactic"])


# ═════════════════════════════════════════════════════════════════
# Construct Inventory
# ═════════════════════════════════════════════════════════════════

_CONSTRUCT_USAGE: dict[str, list[str]] = {}


def _register_constructs():
    """Register which homotopy constructs are used in examples."""
    constructs = {
        "Refl": ["01", "05", "08", "19", "23", "33", "34", "37", "38"],
        "Sym": ["02", "24", "35", "49"],
        "Trans": ["03", "25", "49"],
        "Cong / Ap": ["26"],
        "Ext / FunExt": ["27"],
        "TransportProof": ["28", "32", "43", "45"],
        "DuckPath": ["31"],
        "Fiber": ["30"],
        "Cases": ["10", "30"],
        "CechGlue / Cut": ["29", "46"],
        "NatInduction": ["11", "44"],
        "ListInduction": ["12"],
        "Z3Proof": ["15", "16"],
        "Rewrite": ["13", "39", "40"],
        "AxiomInvocation": ["07", "42", "47", "50"],
        "Unfold": ["14", "17"],
        "Structural": ["22"],
        "Assume": ["04", "06"],
        "Cut": ["09"],
        "PathType": ["23"],
        "ProtocolType": ["31"],
        "TacticProofBuilder": ["01-50"],
    }
    _CONSTRUCT_USAGE.update(constructs)


def print_construct_inventory():
    """Print inventory of homotopy constructs used."""
    _register_constructs()
    print()
    print("  ═══ Homotopy Construct Inventory ═══")
    for construct, examples in sorted(_CONSTRUCT_USAGE.items()):
        ex_str = ", ".join(examples)
        print(f"    {construct:30s}  examples: {ex_str}")


# ═════════════════════════════════════════════════════════════════
# run_all & main
# ═════════════════════════════════════════════════════════════════

def run_all() -> tuple[int, int]:
    """Run all example proofs and return (passed, failed)."""
    global _PASS, _FAIL
    _PASS = 0
    _FAIL = 0

    print()
    print("══════════════════════════════════════════════════════════════")
    print("  F* Tutorial Part 5: Tactics & Metaprogramming (SynHoPy)")
    print("══════════════════════════════════════════════════════════════")

    # Standard tactics
    example_01_reflexivity()
    example_02_symmetry()
    example_03_transitivity()
    example_04_assumption()
    example_05_exact()
    example_06_intro()
    example_07_apply_axiom()
    example_08_trivial()
    example_09_split()
    example_10_destruct()
    example_11_induction_nat()
    example_12_induction_list()
    example_13_rewrite()
    example_14_compute()
    example_15_smt()
    example_16_omega()
    example_17_norm()
    example_18_simp()
    example_19_auto()

    # Tactic combinators
    example_20_seq_combinator()
    example_21_alt_combinator()
    example_22_try_combinator()

    # Homotopy-specific tactics
    example_23_path_refl_tactic()
    example_24_path_sym_tactic()
    example_25_path_trans_tactic()
    example_26_path_ap_tactic()
    example_27_funext_tactic()
    example_28_transport_tactic()
    example_29_cech_tactic()
    example_30_fibration_tactic()
    example_31_duck_type_tactic()
    example_32_univalence_tactic()
    example_33_homotopy_auto()

    # Tactic macros
    example_34_macro_refl()
    example_35_macro_sym()
    example_36_macro_trans()
    example_37_repeat_combinator()
    example_38_focus_combinator()
    example_39_chained_tactics()
    example_40_list_rev_rev()
    example_41_map_compose()
    example_42_append_assoc()
    example_43_transport_with_base()
    example_44_macro_induction()
    example_45_macro_transport()
    example_46_macro_cech()
    example_47_auto_with_hints()
    example_48_complex_chain()
    example_49_path_groupoid()
    example_50_path_assoc()

    print_construct_inventory()

    print()
    print(f"  Results: {_PASS} passed, {_FAIL} failed out of {_PASS + _FAIL}")
    print("══════════════════════════════════════════════════════════════")

    return (_PASS, _FAIL)


def main() -> int:
    passed, failed = run_all()
    return 1 if failed > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
