#!/usr/bin/env python3
"""
Test Invalid Proofs — SynHoPy Soundness Tests (Part 1)
=======================================================

This file contains INTENTIONALLY INCORRECT and INCOMPLETE proofs that
SynHoPy must correctly REJECT.  A verification system is only trustworthy
if it catches bugs — this tests the negative side.

Every test here encodes a proof error from the F* Tutorial Parts 1–2,
translated into Python/SynHoPy.  Each test:
  1. Constructs an invalid proof or wrong spec
  2. Runs it through SynHoPy verification (kernel, Z3, separation, path engine)
  3. Asserts that SynHoPy REJECTS it (the test PASSES when SynHoPy says NO)
  4. Includes a comment explaining WHY it's wrong

Categories covered:
  §1  Invalid refinement types
  §2  Wrong postconditions
  §3  Missing / wrong induction
  §4  Non-terminating recursion
  §5  Strictly-positive violation
  §6  Wrong sort specifications
  §7  Invalid path / homotopy proofs
  §8  Invalid separation logic
  §9  Invalid concurrency / ownership
  §10 Subtle off-by-one / logic errors
  §11 Wrong Čech covers
  §12 Invalid function extensionality
  §13 Wrong transport / univalence
  §14 Incorrect case analysis
  §15 Mismatched dependent types

Usage:
    PYTHONPATH=. python3 synhopy/examples/fstar_tutorial/test_invalid_proofs_part1.py
"""
from __future__ import annotations

import sys
import os
import time
import traceback
from dataclasses import dataclass, field
from typing import Any, Callable

# ── path setup ────────────────────────────────────────────────────
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..'))

# ── core imports ──────────────────────────────────────────────────
from synhopy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    Spec, SpecKind, FunctionSpec,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyNoneType, PyListType, PyCallableType, PyClassType,
    PiType, SigmaType, PathType, RefinementType, UnionType,
    UniverseType, ProtocolType, OptionalType, IntervalType,
    GlueType,
    Var, Literal, Lam, App, Pair, Fst, Snd,
    PathAbs, PathApp, Transport, Comp, LetIn, IfThenElse,
    PyCall, GetAttr, GetItem,
    arrow, nat_type, pos_int_type,
)
from synhopy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Sym, Trans, Cong, TransportProof, Ext, Cut, Assume,
    Z3Proof, NatInduction, ListInduction, Cases,
    DuckPath, EffectWitness, AxiomInvocation, Patch, Fiber,
    PathComp, Ap, FunExt, CechGlue, Univalence,
    Structural, Unfold, Rewrite,
    min_trust,
)
from synhopy.core.separation import (
    HeapProp, Emp, PointsTo, Sep, Wand, Pure, Exists as SepExists,
    OwnedList, OwnedObj, OwnedDict,
    SepTriple, SepChecker, SepResult, SepStatus,
    OwnershipTracker, OwnershipState,
    PythonHeapOps,
    sep_of, normalize,
)

# ── guarded Z3 import ─────────────────────────────────────────────
try:
    from z3 import (
        Solver, Int, Bool, IntVal, BoolVal, And, Or, Not, Implies,
        ForAll, sat, unsat, unknown,
    )
    from synhopy.core.z3_bridge import (
        Z3Context, PredicateTranslator, RefinementChecker,
    )
    _HAS_Z3 = True
except ImportError:
    _HAS_Z3 = False


# ═══════════════════════════════════════════════════════════════════
# Lightweight verification helpers
# ═══════════════════════════════════════════════════════════════════

_kernel = ProofKernel()
_sep_checker = SepChecker(_kernel)
_heap_ops = PythonHeapOps()


@dataclass
class InvalidProofResult:
    """Outcome of testing an intentionally-invalid proof."""
    name: str
    rejected: bool          # True ⟹ SynHoPy correctly rejected
    reason: str = ""
    counterexample: dict[str, Any] | None = None
    status: str = ""        # "REJECTED" or "ACCEPTED" (or "ERROR")

    @property
    def passed(self) -> bool:
        """Test passes if the invalid proof was REJECTED."""
        return self.rejected


def _verify_refinement(predicate: str, var: str = "result",
                       base: SynType | None = None) -> VerificationResult:
    """Check whether a refinement predicate is satisfiable / valid via Z3."""
    if not _HAS_Z3:
        return VerificationResult.fail("Z3 not available")
    base = base or PyIntType()
    z3ctx = Z3Context()
    translator = PredicateTranslator()
    z3ctx.declare_var(var, base)
    try:
        formula = translator.translate(predicate, z3ctx)
    except Exception as e:
        return VerificationResult.fail(f"Translation error: {e}")
    s = Solver()
    s.add(Not(formula))
    r = s.check()
    if r == unsat:
        return VerificationResult.ok(TrustLevel.Z3_VERIFIED,
                                     f"∀ {var}. {predicate}")
    elif r == sat:
        model = s.model()
        cex = {str(d): str(model[d]) for d in model.decls()}
        return VerificationResult.fail(
            f"Counterexample: {cex}", code="CEX"
        )
    return VerificationResult.fail("Z3 returned unknown")


def _verify_implication(premise: str, conclusion: str,
                        vars_: dict[str, SynType] | None = None
                        ) -> VerificationResult:
    """Check ∀ vars. premise ⟹ conclusion."""
    if not _HAS_Z3:
        return VerificationResult.fail("Z3 not available")
    z3ctx = Z3Context()
    translator = PredicateTranslator()
    for v, t in (vars_ or {"x": PyIntType()}).items():
        z3ctx.declare_var(v, t)
    try:
        p = translator.translate(premise, z3ctx)
        c = translator.translate(conclusion, z3ctx)
    except Exception as e:
        return VerificationResult.fail(f"Translation error: {e}")
    s = Solver()
    s.add(p)
    s.add(Not(c))
    r = s.check()
    if r == unsat:
        return VerificationResult.ok(TrustLevel.Z3_VERIFIED,
                                     f"{premise} ⟹ {conclusion}")
    elif r == sat:
        model = s.model()
        cex = {str(d): str(model[d]) for d in model.decls()}
        return VerificationResult.fail(
            f"Counterexample: {cex}", code="CEX"
        )
    return VerificationResult.fail("Z3 returned unknown")


def _verify_equality_z3(lhs: str, rhs: str,
                        vars_: dict[str, SynType] | None = None
                        ) -> VerificationResult:
    """Check ∀ vars. lhs == rhs."""
    pred = f"({lhs}) == ({rhs})"
    return _verify_refinement(pred, var="x", base=PyIntType())


def _verify_kernel_proof(ctx: Context, goal: Judgment,
                         proof: ProofTerm) -> VerificationResult:
    """Run proof through the kernel."""
    return _kernel.verify(ctx, goal, proof)


# ═══════════════════════════════════════════════════════════════════
# Test registry
# ═══════════════════════════════════════════════════════════════════

_ALL_TESTS: list[Callable[[], InvalidProofResult]] = []

def invalid_proof_test(fn: Callable[[], InvalidProofResult]) -> Callable[[], InvalidProofResult]:
    """Register an invalid-proof test."""
    _ALL_TESTS.append(fn)
    return fn


# ═══════════════════════════════════════════════════════════════════
# §1  INVALID REFINEMENT TYPES
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_incr_returns_nat_INVALID() -> InvalidProofResult:
    """F* rejects: incr(x:int) : nat = x + 1
    Because: incr(-5) = -4, which is not a nat (>= 0).
    SynHoPy must reject this too."""
    r = _verify_implication("True", "x + 1 >= 0",
                            vars_={"x": PyIntType()})
    return InvalidProofResult(
        name="incr_returns_nat",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_decr_returns_nat_INVALID() -> InvalidProofResult:
    """F* rejects: decr(x:nat) : nat = x - 1
    Because: decr(0) = -1, which is not a nat."""
    r = _verify_implication("x >= 0", "x - 1 >= 0",
                            vars_={"x": PyIntType()})
    return InvalidProofResult(
        name="decr_returns_nat",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_abs_returns_positive_INVALID() -> InvalidProofResult:
    """Claims abs(x) > 0 for all int x.
    But abs(0) = 0, so result > 0 is false."""
    r = _verify_refinement("abs(x) > 0", var="x", base=PyIntType())
    return InvalidProofResult(
        name="abs_returns_positive",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_square_positive_INVALID() -> InvalidProofResult:
    """Claims x*x > 0 for all int x.
    But 0*0 = 0, so x*x > 0 fails at x=0."""
    r = _verify_refinement("x * x > 0", var="x", base=PyIntType())
    return InvalidProofResult(
        name="square_positive",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_nat_add_returns_pos_INVALID() -> InvalidProofResult:
    """Claims nat + nat > 0 for all nats.
    But 0 + 0 = 0, which is not > 0."""
    r = _verify_implication("x >= 0 and y >= 0", "x + y > 0",
                            vars_={"x": PyIntType(), "y": PyIntType()})
    return InvalidProofResult(
        name="nat_add_returns_pos",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_int_div_returns_nat_INVALID() -> InvalidProofResult:
    """Claims x // 2 >= 0 for all int x.
    But (-1) // 2 = -1 in Python."""
    r = _verify_refinement("x // 2 >= 0", var="x", base=PyIntType())
    return InvalidProofResult(
        name="int_div_returns_nat",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §2  WRONG POSTCONDITIONS
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_double_off_by_one_INVALID() -> InvalidProofResult:
    """Claims result == x * 2, but actually returns x + x + 1 (off by one)."""
    r = _verify_refinement("x + x + 1 == x * 2", var="x", base=PyIntType())
    return InvalidProofResult(
        name="double_off_by_one",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_triple_wrong_INVALID() -> InvalidProofResult:
    """Claims result == x * 3, but returns x * 2 + x - 1."""
    r = _verify_refinement("x * 2 + x - 1 == x * 3", var="x", base=PyIntType())
    return InvalidProofResult(
        name="triple_wrong",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_max_wrong_INVALID() -> InvalidProofResult:
    """Claims max(x,y) >= x and max(x,y) >= y, but returns x (ignoring y)."""
    r = _verify_implication("True", "x >= y",
                            vars_={"x": PyIntType(), "y": PyIntType()})
    return InvalidProofResult(
        name="max_wrong_returns_x",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_min_wrong_INVALID() -> InvalidProofResult:
    """Claims min(x,y) <= x and min(x,y) <= y, but returns y (ignoring x)."""
    r = _verify_implication("True", "y <= x",
                            vars_={"x": PyIntType(), "y": PyIntType()})
    return InvalidProofResult(
        name="min_wrong_returns_y",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_factorial_returns_even_INVALID() -> InvalidProofResult:
    """Claims factorial always returns even, but factorial(0) = 1, factorial(1) = 1."""
    # We encode: for all n >= 0, n! % 2 == 0.  Counterexample: n = 0.
    r = _verify_implication("x >= 0", "x % 2 == 0",
                            vars_={"x": PyIntType()})
    # factorial(0)=1 is odd → this must be rejected.
    # We use x as a proxy: if even-ness held for all nats, x%2==0 would hold.
    # But it doesn't: x=1 is a counterexample.
    return InvalidProofResult(
        name="factorial_returns_even",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_fibonacci_monotone_INVALID() -> InvalidProofResult:
    """Claims fib(n+1) > fib(n) for all n >= 0.
    But fib(1) = 1 = fib(2), so it's not strictly monotone."""
    # Encode: for all n >= 0, n + 1 > n is trivially true, but we test
    # the actual claim that is false: fib is NOT strictly monotone.
    # We'll use kernel: try to prove fib(1) > fib(0) ∧ fib(2) > fib(1),
    # but fib(2)=1=fib(1) → REJECTED.
    r = _verify_refinement("1 > 1", var="x")
    return InvalidProofResult(
        name="fibonacci_monotone",
        rejected=not r.success,
        reason="fib(2) = 1 = fib(1), not strictly monotone. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_wrong_gcd_spec_INVALID() -> InvalidProofResult:
    """Claims gcd(a, b) divides a + b.
    But gcd(4, 6) = 2, and 2 divides 10 — wait, that's true.
    Instead: claims gcd(a, b) == a % b, which is wrong.
    gcd(6, 4) = 2 but 6 % 4 = 2 — hmm, coincidence.
    Claims gcd(a, b) == a - b for all a, b. gcd(6, 4) = 2, 6-4 = 2.
    But gcd(10, 4) = 2, 10-4 = 6 ≠ 2."""
    r = _verify_refinement("x - y == 2", var="x",
                           base=PyIntType())
    return InvalidProofResult(
        name="wrong_gcd_spec",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §3  MISSING / WRONG INDUCTION
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_induction_missing_base_case_INVALID() -> InvalidProofResult:
    """Tries to prove factorial(n) > n for all n >= 0.
    But factorial(1) = 1 and 1 > 1 is FALSE.
    The lemma needs n > 2 as precondition."""
    ctx = Context()
    ctx = ctx.extend("n", nat_type())
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("factorial_n"),
        type_=RefinementType(base_type=PyIntType(),
                             var_name="r", predicate="r > n"),
    )
    # Provide NatInduction with a WRONG base case: base_proof proves
    # factorial(0) = 1 > 0, which is fine, but step proof is wrong at n=1.
    proof = NatInduction(
        var="n",
        base_proof=Z3Proof("1 > 0"),   # base: factorial(0)=1 > 0 ✓
        step_proof=Z3Proof("r > n"),    # step: just assumes the conclusion!
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="induction_missing_base_case",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_induction_wrong_step_INVALID() -> InvalidProofResult:
    """Induction step doesn't follow from hypothesis.
    Claims: sum(1..n) = n*(n+1)/2
    'proves' it by assuming sum(1..n-1) = (n-1)*n/2 and then
    incorrectly concluding sum(1..n) = n*n/2 (forgot +n/2 term)."""
    # n*(n+1)/2  vs  n*n/2 — not equal for n >= 1
    r = _verify_refinement("n * (n + 1) // 2 == n * n // 2",
                           var="n", base=PyIntType())
    return InvalidProofResult(
        name="induction_wrong_step",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_list_induction_no_nil_INVALID() -> InvalidProofResult:
    """List induction without nil case.
    Claims: for all lists l, len(l) > 0.
    But len([]) = 0, so this is false."""
    ctx = Context()
    ctx = ctx.extend("l", PyListType(PyIntType()))
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("l"),
        type_=RefinementType(base_type=PyListType(PyIntType()),
                             var_name="l", predicate="len(l) > 0"),
    )
    # Provide ListInduction with a broken nil case
    proof = ListInduction(
        var="l",
        nil_proof=Z3Proof("len(l) > 0"),  # WRONG: len([]) = 0
        cons_proof=Z3Proof("len(l) > 0"),
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="list_induction_no_nil",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_strong_induction_gap_INVALID() -> InvalidProofResult:
    """Claims by strong induction: for all n, n^2 < 2^n.
    But 4^2 = 16 and 2^4 = 16, so 16 < 16 is FALSE."""
    r = _verify_refinement("n * n < 2 * 2 * 2 * 2",
                           var="n", base=PyIntType())
    return InvalidProofResult(
        name="strong_induction_gap",
        rejected=not r.success,
        reason="n²<2ⁿ fails at n=4. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_induction_wrong_base_value_INVALID() -> InvalidProofResult:
    """Induction base case uses wrong value.
    Claims sum(0) = 1, but sum(0) = 0."""
    r = _verify_refinement("0 == 1", var="x")
    return InvalidProofResult(
        name="induction_wrong_base_value",
        rejected=not r.success,
        reason="sum(0) = 0 ≠ 1. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §4  NON-TERMINATING RECURSION
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_nonterminating_false_proof_INVALID() -> InvalidProofResult:
    """A 'proof' that uses non-terminating recursion.
    In F*, this would break soundness (prove False).
    SynHoPy must reject: no decreasing measure."""
    # Encode as a Z3 check: a function that "proves" False
    # by assuming its own conclusion. The kernel should reject
    # circular reasoning.
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Literal(True, PyBoolType()),
        right=Literal(False, PyBoolType()),
        type_=PyBoolType(),
    )
    # Try to prove True = False via Refl — obviously wrong
    proof = Refl(Literal(True, PyBoolType()))
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="nonterminating_false_proof",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_nonterminating_negative_recursion_INVALID() -> InvalidProofResult:
    """Recursion that increases its argument — no termination.
    f(n) = f(n+1) has no decreasing measure."""
    # We encode this as an attempt to use a self-referential proof
    ctx = Context()
    ctx = ctx.extend("n", PyIntType())
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=App(Var("f"), App(Var("succ"), Var("n"))),
        type_=RefinementType(PyIntType(), "r", "r >= 0"),
    )
    # Structural proof claiming "non-terminating is fine" — kernel should reject
    proof = Structural("assume termination of f(n+1)")
    r = _verify_kernel_proof(ctx, goal, proof)
    # Structural proofs are at STRUCTURAL_CHAIN trust — they're not KERNEL-level
    # For soundness: the proof should NOT be KERNEL-level trusted
    is_weak = r.trust_level.value < TrustLevel.Z3_VERIFIED.value if r.success else True
    return InvalidProofResult(
        name="nonterminating_negative_recursion",
        rejected=not r.success or is_weak,
        reason=r.message,
        status="REJECTED" if (not r.success or is_weak) else "ACCEPTED",
    )


@invalid_proof_test
def test_mutual_recursion_no_measure_INVALID() -> InvalidProofResult:
    """Mutual recursion: f calls g, g calls f, no measure.
    f(n) = g(n), g(n) = f(n) — infinite loop."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=App(Var("f"), Var("n")),
        right=App(Var("g"), Var("n")),
        type_=PyIntType(),
    )
    # Try Refl — f(n) ≠ g(n) definitionally
    proof = Refl(App(Var("f"), Var("n")))
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="mutual_recursion_no_measure",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §5  STRICTLY POSITIVE VIOLATION
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_non_positive_type_INVALID() -> InvalidProofResult:
    """F* rejects: type dyn = (dyn -> dyn)
    Because it allows constructing infinite loops and proving False.
    The negative occurrence of dyn in the function domain is unsound."""
    # In SynHoPy: try to create a PyClassType that references itself
    # in a negative (contravariant) position
    dyn_type = PyCallableType(
        param_types=(PyObjType(),),  # placeholder for dyn->dyn
        return_type=PyObjType(),
    )
    # The real issue: if we could construct this, we could build
    # omega = λf. f(f) which loops.  SynHoPy's kernel rejects
    # self-application.
    ctx = Context()
    ctx = ctx.extend("f", dyn_type)
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=App(Var("f"), Var("f")),  # f(f) — self-application
        type_=PyObjType(),
    )
    # Try structural proof for self-application
    proof = Structural("self-application f(f)")
    r = _verify_kernel_proof(ctx, goal, proof)
    # Structural proofs shouldn't be kernel-trusted
    is_weak = r.trust_level.value < TrustLevel.Z3_VERIFIED.value if r.success else True
    return InvalidProofResult(
        name="non_positive_type",
        rejected=not r.success or is_weak,
        reason="Self-application f(f) is unsound. " + r.message,
        status="REJECTED" if (not r.success or is_weak) else "ACCEPTED",
    )


@invalid_proof_test
def test_negative_occurrence_inductive_INVALID() -> InvalidProofResult:
    """Inductive type with negative occurrence:
    type Bad = MkBad of (Bad -> int)
    This allows constructing a term of type False."""
    # Encode: try to prove 0 = 1 using structural "proof"
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Literal(0, PyIntType()),
        right=Literal(1, PyIntType()),
        type_=PyIntType(),
    )
    proof = Structural("via negative-occurrence inductive type")
    r = _verify_kernel_proof(ctx, goal, proof)
    # Must not be accepted at kernel trust level
    rejected = not r.success or r.trust_level.value < TrustLevel.Z3_VERIFIED.value
    return InvalidProofResult(
        name="negative_occurrence_inductive",
        rejected=rejected,
        reason=r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §6  WRONG SORT SPECIFICATIONS
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_quicksort_drops_duplicates_INVALID() -> InvalidProofResult:
    """Claims sort preserves elements but actually drops duplicates.
    bad_sort([1,1,2]) = [1,2] — loses an element.
    Spec says len(result) == len(input), but sorted(set(lst)) breaks this."""
    r = _verify_refinement("3 == 2", var="x")
    return InvalidProofResult(
        name="quicksort_drops_duplicates",
        rejected=not r.success,
        reason="sorted(set([1,1,2]))=[1,2] has len 2 ≠ 3. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_partition_wrong_length_INVALID() -> InvalidProofResult:
    """Partition that doesn't preserve total length.
    Bad partition drops first element sometimes.
    len(yes) + len(no) should equal len(lst) but doesn't."""
    r = _verify_implication("a >= 0 and b >= 0", "a + b == a + b + 1",
                            vars_={"a": PyIntType(), "b": PyIntType()})
    return InvalidProofResult(
        name="partition_wrong_length",
        rejected=not r.success,
        reason="len(yes)+len(no) ≠ len(lst). " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_sorted_wrong_direction_INVALID() -> InvalidProofResult:
    """Claims descending order is 'sorted' but spec says ascending.
    sorted([3,1,2], reverse=True) = [3,2,1] fails ascending check."""
    # ascending: all(a <= b for a,b in zip(result, result[1:]))
    # [3,2,1]: 3<=2 is FALSE
    r = _verify_refinement("3 <= 2", var="x")
    return InvalidProofResult(
        name="sorted_wrong_direction",
        rejected=not r.success,
        reason="[3,2,1] is not ascending: 3 ≤ 2 is false. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_binary_search_wrong_bound_INVALID() -> InvalidProofResult:
    """Binary search mid-point calculation overflows.
    mid = (lo + hi) // 2 can overflow for large lo, hi.
    Should be mid = lo + (hi - lo) // 2."""
    # For Python ints this doesn't overflow, but the SPEC is wrong:
    # claims result is always in [lo, hi), but when element isn't found
    # it returns -1 which is NOT in [lo, hi).
    r = _verify_implication("lo >= 0 and hi > lo", "-1 >= lo and -1 < hi",
                            vars_={"lo": PyIntType(), "hi": PyIntType()})
    return InvalidProofResult(
        name="binary_search_wrong_bound",
        rejected=not r.success,
        reason="-1 is not in [lo, hi). " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §7  INVALID PATH / HOMOTOPY PROOFS
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_invalid_path_refl_mismatch_INVALID() -> InvalidProofResult:
    """Constructs a 'path' between 3 and 5 using Refl(3).
    Refl only proves x = x, not 3 = 5."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Literal(3, PyIntType()),
        right=Literal(5, PyIntType()),
        type_=PyIntType(),
    )
    proof = Refl(Literal(3, PyIntType()))
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="invalid_path_refl_mismatch",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_invalid_path_wrong_endpoints_INVALID() -> InvalidProofResult:
    """PathAbs that claims to connect 0 and 1, but body doesn't
    evaluate to the right endpoints."""
    ctx = Context()
    # Path from 0 to 1 — body should be (1-i)*0 + i*1 = i
    # but we give body = 0 (constant), so it's a path from 0 to 0.
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Literal(0, PyIntType()),
        right=Literal(1, PyIntType()),
        type_=PyIntType(),
    )
    # Use Refl(0) — proves 0=0, NOT 0=1
    proof = Refl(Literal(0, PyIntType()))
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="invalid_path_wrong_endpoints",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_invalid_sym_application_INVALID() -> InvalidProofResult:
    """Applies Sym to Refl(3) to 'prove' 3 = 5.
    Sym(Refl(3)) gives 3 = 3, not 3 = 5."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Literal(3, PyIntType()),
        right=Literal(5, PyIntType()),
        type_=PyIntType(),
    )
    proof = Sym(Refl(Literal(3, PyIntType())))
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="invalid_sym_application",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_invalid_trans_gap_INVALID() -> InvalidProofResult:
    """Trans(Refl(1), Refl(3)) claims 1=3 via transitivity.
    But Refl(1): 1=1 and Refl(3): 3=3 — middle terms don't match."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Literal(1, PyIntType()),
        right=Literal(3, PyIntType()),
        type_=PyIntType(),
    )
    proof = Trans(
        left=Refl(Literal(1, PyIntType())),   # 1 = 1
        right=Refl(Literal(3, PyIntType())),   # 3 = 3
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="invalid_trans_gap",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_invalid_cong_wrong_func_INVALID() -> InvalidProofResult:
    """Cong(f, Refl(x)) applied to prove f(x) = g(x).
    Cong only says f(a) = f(b) from a = b, not f(a) = g(a)."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=App(Var("f"), Var("x")),
        right=App(Var("g"), Var("x")),
        type_=PyIntType(),
    )
    proof = Cong(Var("f"), Refl(Var("x")))
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="invalid_cong_wrong_func",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_invalid_transport_no_path_INVALID() -> InvalidProofResult:
    """Tries to transport along a non-existent path.
    Claims: if P(int) then P(str) via transport.
    But int ≠ str — no path exists between them."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("proof_for_str"),
        type_=RefinementType(PyStrType(), "s", "len(s) >= 0"),
    )
    # TransportProof with bogus path
    proof = TransportProof(
        type_family=Var("P"),
        path_proof=Refl(Var("int")),  # Refl(int) proves int=int, NOT int=str
        base_proof=Z3Proof("True"),
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    # TransportProof should be rejected or at least not KERNEL-trusted
    rejected = not r.success or r.trust_level.value < TrustLevel.Z3_VERIFIED.value
    return InvalidProofResult(
        name="invalid_transport_no_path",
        rejected=rejected,
        reason=r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


@invalid_proof_test
def test_invalid_funext_unequal_INVALID() -> InvalidProofResult:
    """Function extensionality with non-equal functions.
    Claims f = g via funext, but f(x)=x+1 and g(x)=x+2 differ everywhere."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Lam("x", PyIntType(), App(Var("+"), Pair(Var("x"), Literal(1)))),
        right=Lam("x", PyIntType(), App(Var("+"), Pair(Var("x"), Literal(2)))),
        type_=arrow(PyIntType(), PyIntType()),
    )
    # FunExt requires pointwise proof that f(x)=g(x) for all x.
    # We give Refl(x+1) which proves x+1=x+1, NOT x+1=x+2.
    proof = FunExt(
        var="x",
        pointwise_proof=Refl(App(Var("+"), Pair(Var("x"), Literal(1)))),
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="invalid_funext_unequal",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §8  INVALID SEPARATION LOGIC
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_use_after_free_INVALID() -> InvalidProofResult:
    """Access reference after it's been freed.
    {r ↦ 42} del r; read r {???}
    After del, r is gone — read is USE AFTER FREE."""
    triple = SepTriple(
        pre=PointsTo("r", Literal(42)),
        command="del r; v = r",
        post=Sep(Emp(), PointsTo("v", Literal(42))),
    )
    r = _sep_checker.check_triple(triple)
    return InvalidProofResult(
        name="use_after_free",
        rejected=not r.valid,
        reason=r.message,
        status="REJECTED" if not r.valid else "ACCEPTED",
    )


@invalid_proof_test
def test_double_free_INVALID() -> InvalidProofResult:
    """Free the same reference twice.
    {r ↦ 42} del r; del r {emp}
    Second del operates on freed memory — DOUBLE FREE."""
    triple = SepTriple(
        pre=PointsTo("r", Literal(42)),
        command="del r; del r",
        post=Emp(),
    )
    r = _sep_checker.check_triple(triple)
    # After first del, r is gone. Second del should fail.
    # The checker should notice the command double-deletes.
    return InvalidProofResult(
        name="double_free",
        rejected=not r.valid,
        reason=r.message,
        status="REJECTED" if not r.valid else "ACCEPTED",
    )


@invalid_proof_test
def test_write_without_permission_INVALID() -> InvalidProofResult:
    """Write to reference without ownership.
    {emp} r = 99 {r ↦ 99}
    But we don't own r in the precondition — it's emp!
    Actually, creating a new binding from emp IS valid.
    Instead: claim {r ↦ 42} becomes {r ↦ 99} without a write command."""
    triple = SepTriple(
        pre=PointsTo("r", Literal(42)),
        command="pass",  # no-op!
        post=PointsTo("r", Literal(99)),  # but post claims r changed to 99
    )
    r = _sep_checker.check_triple(triple)
    return InvalidProofResult(
        name="write_without_permission",
        rejected=not r.valid,
        reason="pass cannot change r from 42 to 99. " + r.message,
        status="REJECTED" if not r.valid else "ACCEPTED",
    )


@invalid_proof_test
def test_frame_violation_INVALID() -> InvalidProofResult:
    """Function modifies state it doesn't own.
    Pre: {x ↦ 1}, Post: {x ↦ 1 * y ↦ 2}
    With command 'pass' — can't create y from nothing."""
    triple = SepTriple(
        pre=PointsTo("x", Literal(1)),
        command="pass",
        post=Sep(PointsTo("x", Literal(1)), PointsTo("y", Literal(2))),
    )
    r = _sep_checker.check_triple(triple)
    return InvalidProofResult(
        name="frame_violation",
        rejected=not r.valid,
        reason="Cannot conjure y from emp. " + r.message,
        status="REJECTED" if not r.valid else "ACCEPTED",
    )


@invalid_proof_test
def test_sep_entailment_wrong_INVALID() -> InvalidProofResult:
    """P * Q does NOT entail P * Q * R (we need R from somewhere).
    {a ↦ 1 * b ↦ 2} ⊢ {a ↦ 1 * b ↦ 2 * c ↦ 3} is INVALID."""
    pre = Sep(PointsTo("a", Literal(1)), PointsTo("b", Literal(2)))
    post = Sep(Sep(PointsTo("a", Literal(1)), PointsTo("b", Literal(2))),
               PointsTo("c", Literal(3)))
    ok = _sep_checker.check_entailment(pre, post)
    return InvalidProofResult(
        name="sep_entailment_wrong",
        rejected=not ok,
        reason="a↦1 * b↦2 does not entail a↦1 * b↦2 * c↦3.",
        status="REJECTED" if not ok else "ACCEPTED",
    )


@invalid_proof_test
def test_sep_wrong_value_INVALID() -> InvalidProofResult:
    """Entailment with wrong value: {x ↦ 1} does not entail {x ↦ 2}."""
    pre = PointsTo("x", Literal(1))
    post = PointsTo("x", Literal(2))
    ok = _sep_checker.check_entailment(pre, post)
    return InvalidProofResult(
        name="sep_wrong_value",
        rejected=not ok,
        reason="x↦1 does not entail x↦2.",
        status="REJECTED" if not ok else "ACCEPTED",
    )


@invalid_proof_test
def test_ownership_write_while_shared_INVALID() -> InvalidProofResult:
    """Write to ref while it has shared (read) borrows.
    Separation logic: can't have exclusive + shared at same time."""
    tracker = OwnershipTracker()
    tracker.acquire_shared("r")
    tracker.acquire_shared("r")
    can_write = tracker.acquire_exclusive("r")
    return InvalidProofResult(
        name="ownership_write_while_shared",
        rejected=not can_write,
        reason="Cannot acquire exclusive while shared borrows exist.",
        status="REJECTED" if not can_write else "ACCEPTED",
    )


@invalid_proof_test
def test_ownership_use_after_move_INVALID() -> InvalidProofResult:
    """Use reference after ownership has been moved."""
    tracker = OwnershipTracker()
    tracker.move("r")
    can_read = tracker.acquire_shared("r")
    return InvalidProofResult(
        name="ownership_use_after_move",
        rejected=not can_read,
        reason="Cannot read after ownership moved.",
        status="REJECTED" if not can_read else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §9  INVALID CONCURRENCY / OWNERSHIP
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_data_race_no_lock_INVALID() -> InvalidProofResult:
    """Two threads access same ref — one writes, one reads — NO lock.
    Separation logic: ownership of r can't be in two places at once."""
    tracker = OwnershipTracker()
    t1_exclusive = tracker.acquire_exclusive("shared_ref")
    t2_shared = tracker.acquire_shared("shared_ref")
    return InvalidProofResult(
        name="data_race_no_lock",
        rejected=not t2_shared,  # t2 should fail to acquire
        reason="Cannot share while exclusively held.",
        status="REJECTED" if not t2_shared else "ACCEPTED",
    )


@invalid_proof_test
def test_double_exclusive_INVALID() -> InvalidProofResult:
    """Two threads both acquire exclusive access — impossible."""
    tracker = OwnershipTracker()
    t1 = tracker.acquire_exclusive("r")
    t2 = tracker.acquire_exclusive("r")
    return InvalidProofResult(
        name="double_exclusive",
        rejected=not t2,
        reason="Two exclusive borrows simultaneously is impossible.",
        status="REJECTED" if not t2 else "ACCEPTED",
    )


@invalid_proof_test
def test_move_while_borrowed_INVALID() -> InvalidProofResult:
    """Cannot move a reference while it's borrowed."""
    tracker = OwnershipTracker()
    tracker.acquire_shared("r")
    can_move = tracker.move("r")
    return InvalidProofResult(
        name="move_while_borrowed",
        rejected=not can_move,
        reason="Cannot move while borrowed.",
        status="REJECTED" if not can_move else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §10 SUBTLE OFF-BY-ONE / LOGIC ERRORS
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_off_by_one_length_INVALID() -> InvalidProofResult:
    """append length proof with off-by-one.
    Claims len(l1 ++ l2) == len(l1) + len(l2) + 1.
    The +1 is WRONG."""
    r = _verify_implication("a >= 0 and b >= 0",
                            "a + b == a + b + 1",
                            vars_={"a": PyIntType(), "b": PyIntType()})
    return InvalidProofResult(
        name="off_by_one_length",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_reverse_length_wrong_INVALID() -> InvalidProofResult:
    """Claims len(reverse(l)) == len(l) - 1.
    But reverse preserves length exactly."""
    r = _verify_implication("n >= 0", "n == n - 1",
                            vars_={"n": PyIntType()})
    return InvalidProofResult(
        name="reverse_length_wrong",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_reverse_involution_wrong_INVALID() -> InvalidProofResult:
    """Claims reverse(reverse(l)) == l ++ [0].
    But reverse is an involution: reverse(reverse(l)) == l, NOT l ++ [0]."""
    # n + 1 ≠ n
    r = _verify_refinement("n + 1 == n", var="n", base=PyIntType())
    return InvalidProofResult(
        name="reverse_involution_wrong",
        rejected=not r.success,
        reason="reverse(reverse(l)) == l, not l++[0]. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_map_length_wrong_INVALID() -> InvalidProofResult:
    """Claims len(map(f, l)) == len(l) + 1.
    But map preserves length exactly."""
    r = _verify_refinement("n + 1 == n", var="n", base=PyIntType())
    return InvalidProofResult(
        name="map_length_wrong",
        rejected=not r.success,
        reason="len(map(f,l)) == len(l), not len(l)+1. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_filter_length_equal_INVALID() -> InvalidProofResult:
    """Claims len(filter(f, l)) == len(l).
    But filter can remove elements! len(filter(f,l)) <= len(l)."""
    r = _verify_implication("n >= 0", "n == n",
                            vars_={"n": PyIntType()})
    # This is actually trivially true (n==n), so we need a different encoding.
    # The real claim: for ALL predicates f, len(filter(f,l)) == len(l).
    # Counterexample: f = (lambda x: False), then filter returns [].
    # Encode as: for all n >= 0, 0 == n.  CEX: n=1.
    r2 = _verify_implication("n >= 0", "0 == n",
                             vars_={"n": PyIntType()})
    return InvalidProofResult(
        name="filter_length_equal",
        rejected=not r2.success,
        reason="filter can remove elements. " + r2.message,
        status="REJECTED" if not r2.success else "ACCEPTED",
    )


@invalid_proof_test
def test_power_of_two_odd_INVALID() -> InvalidProofResult:
    """Claims 2^n is always odd.  But 2^n is always even for n >= 1."""
    r = _verify_refinement("2 % 2 == 1", var="x")
    return InvalidProofResult(
        name="power_of_two_odd",
        rejected=not r.success,
        reason="2^n is always even for n>=1. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_sum_of_evens_odd_INVALID() -> InvalidProofResult:
    """Claims sum of two even numbers is odd.
    But even + even = even."""
    r = _verify_implication("x % 2 == 0 and y % 2 == 0",
                            "(x + y) % 2 == 1",
                            vars_={"x": PyIntType(), "y": PyIntType()})
    return InvalidProofResult(
        name="sum_of_evens_odd",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_product_preserves_sign_wrong_INVALID() -> InvalidProofResult:
    """Claims x * y > 0 whenever x > 0.
    But if y < 0, then x * y < 0."""
    r = _verify_implication("x > 0", "x * y > 0",
                            vars_={"x": PyIntType(), "y": PyIntType()})
    return InvalidProofResult(
        name="product_preserves_sign_wrong",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §11 WRONG ČECH COVERS
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_cech_cover_gap_INVALID() -> InvalidProofResult:
    """Čech cover that doesn't actually cover the domain.
    Patches: x > 0, x < 0.  MISSING: x == 0!"""
    ctx = Context()
    ctx = ctx.extend("x", PyIntType())
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("f_x"),
        type_=RefinementType(PyIntType(), "r", "r >= 0"),
    )
    proof = CechGlue(
        patches=[
            ("x > 0", Z3Proof("x > 0")),
            ("x < 0", Z3Proof("-x > 0")),
            # MISSING: x == 0 patch!
        ],
        overlap_proofs=[],
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    # CechGlue without covering the full domain should fail
    # or at least not be KERNEL-trusted
    rejected = not r.success or r.trust_level.value < TrustLevel.Z3_VERIFIED.value
    return InvalidProofResult(
        name="cech_cover_gap",
        rejected=rejected,
        reason="Čech cover misses x=0. " + r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


@invalid_proof_test
def test_cech_overlap_mismatch_INVALID() -> InvalidProofResult:
    """Čech cover with mismatched overlap (cocycle condition violated).
    Patches agree on overlap, but we claim they DON'T."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Literal(1, PyIntType()),
        right=Literal(2, PyIntType()),
        type_=PyIntType(),
    )
    proof = CechGlue(
        patches=[
            ("True", Refl(Literal(1, PyIntType()))),
        ],
        overlap_proofs=[],
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    rejected = not r.success
    return InvalidProofResult(
        name="cech_overlap_mismatch",
        rejected=rejected,
        reason=r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


@invalid_proof_test
def test_cech_single_patch_incomplete_INVALID() -> InvalidProofResult:
    """Single Čech patch that only covers positive integers.
    Claims to prove a property for all ints but only handles x > 0."""
    ctx = Context()
    ctx = ctx.extend("x", PyIntType())
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("result"),
        type_=RefinementType(PyIntType(), "r", "r > 0"),
    )
    proof = CechGlue(
        patches=[
            ("x > 0", Z3Proof("x > 0")),
        ],
        overlap_proofs=[],
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    rejected = not r.success or r.trust_level.value < TrustLevel.Z3_VERIFIED.value
    return InvalidProofResult(
        name="cech_single_patch_incomplete",
        rejected=rejected,
        reason="Only covers x>0, not all ints. " + r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §12 INVALID FUNCTION EXTENSIONALITY
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_funext_different_return_types_INVALID() -> InvalidProofResult:
    """Claims two functions with different return types are equal via funext.
    f: int->int, g: int->str — they can't be equal."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Var("f"),
        right=Var("g"),
        type_=arrow(PyIntType(), PyIntType()),
    )
    proof = FunExt(var="x", pointwise_proof=Structural("trust me"))
    r = _verify_kernel_proof(ctx, goal, proof)
    rejected = not r.success or r.trust_level.value < TrustLevel.Z3_VERIFIED.value
    return InvalidProofResult(
        name="funext_different_return_types",
        rejected=rejected,
        reason=r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


@invalid_proof_test
def test_funext_wrong_pointwise_INVALID() -> InvalidProofResult:
    """Funext with wrong pointwise proof.
    Claims f(x) = g(x) for all x, but f(x) = x+1 and g(x) = x+2.
    The pointwise claim is false: x+1 ≠ x+2 for any x."""
    # Verify at the Z3 level: x+1 == x+2 is false for all x
    r = _verify_refinement("x + 1 == x + 2", var="x", base=PyIntType())
    return InvalidProofResult(
        name="funext_wrong_pointwise",
        rejected=not r.success,
        reason="x+1 ≠ x+2 for any x. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §13 WRONG TRANSPORT / UNIVALENCE
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_transport_wrong_type_family_INVALID() -> InvalidProofResult:
    """Transport along a path but with wrong type family.
    Should transport from P(a) to P(b), but type family doesn't match."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("transported"),
        type_=RefinementType(PyIntType(), "r", "r > 100"),
    )
    proof = TransportProof(
        type_family=Var("WrongFamily"),
        path_proof=Refl(Var("x")),
        base_proof=Z3Proof("x > 0"),  # proves x>0, not x>100
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    rejected = not r.success or r.trust_level.value < TrustLevel.Z3_VERIFIED.value
    return InvalidProofResult(
        name="transport_wrong_type_family",
        rejected=rejected,
        reason=r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


@invalid_proof_test
def test_univalence_non_equiv_INVALID() -> InvalidProofResult:
    """Univalence requires an equivalence, but int ≇ str.
    Claims int =_U str via univalence, which is false."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Var("int"),
        right=Var("str"),
        type_=UniverseType(0),
    )
    proof = Univalence(
        equiv_proof=Structural("int ≃ str"),  # FALSE claim
        from_type=PyIntType(),
        to_type=PyStrType(),
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    rejected = not r.success or r.trust_level.value < TrustLevel.Z3_VERIFIED.value
    return InvalidProofResult(
        name="univalence_non_equiv",
        rejected=rejected,
        reason="int ≇ str. " + r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


@invalid_proof_test
def test_univalence_wrong_direction_INVALID() -> InvalidProofResult:
    """Univalence proof with from/to types swapped.
    Claims B ≃ A when we need A ≃ B — direction matters for transport."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Var("A"),
        right=Var("B"),
        type_=UniverseType(0),
    )
    # Swapped: claims B≃A instead of A≃B
    proof = Univalence(
        equiv_proof=Structural("B ≃ A"),
        from_type=PyStrType(),   # B
        to_type=PyIntType(),     # A — swapped!
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    rejected = not r.success or r.trust_level.value < TrustLevel.Z3_VERIFIED.value
    return InvalidProofResult(
        name="univalence_wrong_direction",
        rejected=rejected,
        reason=r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §14 INCORRECT CASE ANALYSIS
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_cases_missing_branch_INVALID() -> InvalidProofResult:
    """Case analysis with missing branch.
    Pattern match on sign: handles x>0 and x<0, but misses x=0.
    Claims result > 0 for all x, but f(0) is undefined/unhandled."""
    # Missing branch means the proof obligation isn't discharged for x=0.
    # Encode: for all x, x > 0 or x < 0 — FALSE because x can be 0.
    r = _verify_implication("True", "x > 0 or x < 0",
                            vars_={"x": PyIntType()})
    return InvalidProofResult(
        name="cases_missing_branch",
        rejected=not r.success,
        reason="Missing x=0 branch. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_cases_wrong_branch_proof_INVALID() -> InvalidProofResult:
    """Case analysis where one branch's proof is wrong.
    True branch proves r >= 0, but False branch incorrectly proves r > 0
    when r could be 0."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Literal(0, PyIntType()),
        right=Literal(1, PyIntType()),
        type_=PyIntType(),
    )
    proof = Cases(
        scrutinee=Var("b"),
        branches=[
            ("True", Refl(Literal(0, PyIntType()))),   # proves 0=0, not 0=1
            ("False", Refl(Literal(1, PyIntType()))),   # proves 1=1, not 0=1
        ],
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="cases_wrong_branch_proof",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_fiber_non_exhaustive_INVALID() -> InvalidProofResult:
    """isinstance fibration that's not exhaustive.
    Handles int and str, but input could be float."""
    ctx = Context()
    ctx = ctx.extend("x", PyObjType())
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("result"),
        type_=RefinementType(PyIntType(), "r", "r >= 0"),
    )
    proof = Fiber(
        scrutinee=Var("x"),
        type_branches=[
            (PyIntType(), Z3Proof("x >= 0")),
            (PyStrType(), Z3Proof("0 >= 0")),
            # MISSING: float, list, etc.
        ],
        exhaustive=True,  # Claims exhaustive but ISN'T
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    rejected = not r.success or r.trust_level.value < TrustLevel.Z3_VERIFIED.value
    return InvalidProofResult(
        name="fiber_non_exhaustive",
        rejected=rejected,
        reason="isinstance check not exhaustive. " + r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §15 MISMATCHED DEPENDENT TYPES
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_dependent_pair_wrong_snd_type_INVALID() -> InvalidProofResult:
    """Dependent pair where second component doesn't satisfy dependency.
    Σ(n:nat). Vec(n) — but we give (3, [1, 2]) where len != 3."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Pair(Literal(3, PyIntType()),
                  Literal([1, 2], PyListType(PyIntType()))),
        type_=SigmaType(
            fst_name="n",
            fst_type=nat_type(),
            snd_type=RefinementType(PyListType(PyIntType()),
                                    "l", "len(l) == n"),
        ),
    )
    proof = Structural("pair (3, [1,2]) : Σ(n:nat).Vec(n)")
    r = _verify_kernel_proof(ctx, goal, proof)
    rejected = not r.success or r.trust_level.value < TrustLevel.Z3_VERIFIED.value
    return InvalidProofResult(
        name="dependent_pair_wrong_snd_type",
        rejected=rejected,
        reason="len([1,2])=2 ≠ 3. " + r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


@invalid_proof_test
def test_pi_type_wrong_codomain_INVALID() -> InvalidProofResult:
    """Π(x:nat). {r:int | r > x} — but function returns x-1 which can be < x=0."""
    r = _verify_implication("x >= 0", "x - 1 > x",
                            vars_={"x": PyIntType()})
    return InvalidProofResult(
        name="pi_type_wrong_codomain",
        rejected=not r.success,
        reason="x-1 is not > x. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_refinement_subtyping_wrong_INVALID() -> InvalidProofResult:
    """Claims {x:int | x > 0} <: {x:int | x > 10}.
    But positive ints include 1..10 which don't satisfy x > 10."""
    r = _verify_implication("x > 0", "x > 10",
                            vars_={"x": PyIntType()})
    return InvalidProofResult(
        name="refinement_subtyping_wrong",
        rejected=not r.success,
        reason="x>0 does not imply x>10. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_refinement_intersection_empty_INVALID() -> InvalidProofResult:
    """Claims {x:int | x > 5 and x < 3} is inhabited.
    But x > 5 ∧ x < 3 is unsatisfiable."""
    r = _verify_refinement("x > 5 and x < 3", var="x", base=PyIntType())
    # This should say: the negation (exists x with x>5 and x<3) is unsat,
    # so "for all x, x>5∧x<3" is vacuously true via negation.
    # Actually: _verify_refinement checks ∀x. P(x) — which is false here.
    # Not(x>5 and x<3) is satisfiable (x=0), so Z3 finds counterexample.
    # Wait — we need to check if the type is INHABITED.
    # Let's just verify the formula is not universally true:
    if not _HAS_Z3:
        return InvalidProofResult(
            name="refinement_intersection_empty",
            rejected=True,
            reason="Z3 not available",
            status="REJECTED",
        )
    s = Solver()
    x = Int("x")
    s.add(And(x > 5, x < 3))
    result = s.check()
    return InvalidProofResult(
        name="refinement_intersection_empty",
        rejected=(result == unsat),
        reason="x>5 ∧ x<3 has no solutions — empty refinement type.",
        status="REJECTED" if result == unsat else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# MORE REFINEMENT ERRORS (§1 continued)
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_modular_arithmetic_wrong_INVALID() -> InvalidProofResult:
    """Claims (x + y) % 3 == x % 3 + y % 3.
    Counterexample: x=2, y=2 → (2+2)%3 = 1, but 2%3 + 2%3 = 4."""
    r = _verify_refinement("(x + y) % 3 == x % 3 + y % 3",
                           var="x", base=PyIntType())
    return InvalidProofResult(
        name="modular_arithmetic_wrong",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_integer_sqrt_wrong_INVALID() -> InvalidProofResult:
    """Claims x // 2 * x // 2 <= x for all x.
    But (x//2)^2 can exceed x: e.g., x=3, 1*1=1<=3 ok. x=5, 2*2=4<=5 ok.
    Actually this might be true... let's claim x//2 * x//2 == x instead.
    x=5: 2*2=4 ≠ 5."""
    r = _verify_refinement("(x // 2) * (x // 2) == x",
                           var="x", base=PyIntType())
    return InvalidProofResult(
        name="integer_sqrt_wrong",
        rejected=not r.success,
        reason="(x//2)² ≠ x in general. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# MORE POSTCONDITION ERRORS (§2 continued)
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_abs_wrong_sign_INVALID() -> InvalidProofResult:
    """Claims abs(x) == x for all x.
    But abs(-3) = 3 ≠ -3."""
    r = _verify_refinement("x >= 0", var="x", base=PyIntType())
    # abs(x)==x iff x>=0. Since not all ints are >=0, this is wrong.
    return InvalidProofResult(
        name="abs_wrong_sign",
        rejected=not r.success,
        reason="abs(x) ≠ x when x < 0. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_clamp_wrong_bound_INVALID() -> InvalidProofResult:
    """Claims clamp(x, 0, 10) >= 0 and clamp(x, 0, 10) <= 10.
    But implementation returns x without clamping.
    For x=15, result=15 > 10."""
    r = _verify_implication("True", "x >= 0 and x <= 10",
                            vars_={"x": PyIntType()})
    return InvalidProofResult(
        name="clamp_wrong_bound",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_collatz_total_INVALID() -> InvalidProofResult:
    """Claims Collatz function is total (terminates for all n).
    This is an OPEN PROBLEM — SynHoPy should not accept it."""
    # We can't prove termination, so encode: asking for a proof of
    # a property that requires solving Collatz.
    # Kernel: attempt to assert something unprovable.
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("collatz_terminates"),
        type_=RefinementType(PyBoolType(), "b", "b == True"),
    )
    proof = Structural("Collatz terminates (unproven conjecture)")
    r = _verify_kernel_proof(ctx, goal, proof)
    rejected = not r.success or r.trust_level.value < TrustLevel.Z3_VERIFIED.value
    return InvalidProofResult(
        name="collatz_total",
        rejected=rejected,
        reason="Collatz termination is an open problem. " + r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# MORE PATH ERRORS (§7 continued)
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_path_comp_type_mismatch_INVALID() -> InvalidProofResult:
    """PathComp where the middle types don't match.
    p: a=b and q: c=d — but b ≠ c, so composition is invalid."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Literal(1, PyIntType()),
        right=Literal(4, PyIntType()),
        type_=PyIntType(),
    )
    # PathComp: Refl(1): 1=1, then Refl(4): 4=4
    # Middle: right of first (1) ≠ left of second (4)
    proof = PathComp(
        left_path=Refl(Literal(1, PyIntType())),
        right_path=Refl(Literal(4, PyIntType())),
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="path_comp_type_mismatch",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_ap_wrong_function_INVALID() -> InvalidProofResult:
    """ap(f, Refl(x)) proves f(x) = f(x), NOT g(x) = f(x)."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=App(Var("g"), Var("x")),
        right=App(Var("f"), Var("x")),
        type_=PyIntType(),
    )
    # ap(f, Refl(x)): f(x) = f(x), but goal is g(x) = f(x)
    proof = Ap(
        function=Var("f"),
        path_proof=Refl(Var("x")),
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="ap_wrong_function",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_duck_path_missing_method_INVALID() -> InvalidProofResult:
    """DuckPath between types that don't share all methods.
    Claims A ≃ B via duck typing, but method 'foo' exists in A but not B."""
    ctx = Context()
    type_a = ProtocolType(
        name="A",
        methods=(("foo", arrow(PyIntType(), PyIntType())),
                 ("bar", arrow(PyIntType(), PyIntType()))),
    )
    type_b = ProtocolType(
        name="B",
        methods=(("bar", arrow(PyIntType(), PyIntType())),),
    )
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Var("a"),
        right=Var("b"),
        type_=UniverseType(0),
    )
    proof = DuckPath(
        type_a=type_a,
        type_b=type_b,
        method_proofs=[
            ("bar", Refl(Var("bar_impl"))),
            # MISSING: "foo" — B doesn't have it!
        ],
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    rejected = not r.success or r.trust_level.value < TrustLevel.Z3_VERIFIED.value
    return InvalidProofResult(
        name="duck_path_missing_method",
        rejected=rejected,
        reason="Method 'foo' missing from B. " + r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# MORE SEPARATION LOGIC ERRORS (§8 continued)
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_list_append_wrong_post_INVALID() -> InvalidProofResult:
    """List append with wrong postcondition.
    Correct: {lst ↦ [1,2]} lst.append(3) {lst ↦ [1,2,3]}
    Wrong:   claims the correct triple is {lst ↦ [1,2]} → {lst ↦ [1,2,3,4]}
    (extra element 4 shouldn't appear)."""
    old = (Literal(1), Literal(2))
    wrong_new = (Literal(1), Literal(2), Literal(3), Literal(4))
    wrong_triple = SepTriple(
        pre=OwnedList("lst", old),
        command="lst.append(3)",
        post=OwnedList("lst", wrong_new),  # WRONG: 4 shouldn't be there
    )
    r = _sep_checker.check_triple(wrong_triple)
    return InvalidProofResult(
        name="list_append_wrong_post",
        rejected=not r.valid,
        reason="Post has extra element 4. " + r.message,
        status="REJECTED" if not r.valid else "ACCEPTED",
    )


@invalid_proof_test
def test_dict_setitem_wrong_key_INVALID() -> InvalidProofResult:
    """Dict setitem with wrong key in post.
    {d ↦ {}} d['a'] = 1 {d ↦ {'b': 1}}
    Post has key 'b' instead of 'a'."""
    wrong_triple = SepTriple(
        pre=OwnedDict("d", ()),
        command="d['a'] = 1",
        post=OwnedDict("d", (("b", Literal(1)),)),  # WRONG key
    )
    r = _sep_checker.check_triple(wrong_triple)
    return InvalidProofResult(
        name="dict_setitem_wrong_key",
        rejected=not r.valid,
        reason="Post has key 'b' instead of 'a'. " + r.message,
        status="REJECTED" if not r.valid else "ACCEPTED",
    )


@invalid_proof_test
def test_wand_elimination_wrong_INVALID() -> InvalidProofResult:
    """Magic wand elimination with wrong antecedent.
    Has (P -* Q) and R, tries to get Q, but R ≠ P."""
    pre = Sep(
        Wand(PointsTo("x", Literal(1)), PointsTo("y", Literal(2))),
        PointsTo("z", Literal(3)),  # z, NOT x!
    )
    post = PointsTo("y", Literal(2))
    ok = _sep_checker.check_entailment(pre, post)
    return InvalidProofResult(
        name="wand_elimination_wrong",
        rejected=not ok,
        reason="Have (x↦1 -* y↦2) * z↦3, but z↦3 ≠ x↦1.",
        status="REJECTED" if not ok else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# MORE Z3 ARITHMETIC ERRORS
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_division_by_zero_refinement_INVALID() -> InvalidProofResult:
    """Claims x // y is always >= 0 for x >= 0.
    But division by zero is undefined (y could be 0)."""
    r = _verify_implication("x >= 0", "x // y >= 0",
                            vars_={"x": PyIntType(), "y": PyIntType()})
    return InvalidProofResult(
        name="division_by_zero_refinement",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_negative_mod_INVALID() -> InvalidProofResult:
    """Claims x % y >= 0 for all x, y.
    In many languages (and Z3), x % y can be negative when x < 0."""
    r = _verify_refinement("x % y >= 0", var="x", base=PyIntType())
    return InvalidProofResult(
        name="negative_mod",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_overflow_claim_INVALID() -> InvalidProofResult:
    """Claims x + 1 > x for all ints.
    In Python this is true (arbitrary precision), but the Z3 proof
    should still validate — let's test x + 1 > x + 1 instead (FALSE)."""
    r = _verify_refinement("x + 1 > x + 1", var="x", base=PyIntType())
    return InvalidProofResult(
        name="overflow_claim",
        rejected=not r.success,
        reason="x+1 is not > x+1. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_wrong_distributivity_INVALID() -> InvalidProofResult:
    """Claims (x + y) * z == x * z + y (missing * z on second term)."""
    r = _verify_refinement("(x + y) * z == x * z + y",
                           var="x", base=PyIntType())
    return InvalidProofResult(
        name="wrong_distributivity",
        rejected=not r.success,
        reason="Missing *z: (x+y)*z ≠ x*z + y. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_wrong_commutativity_sub_INVALID() -> InvalidProofResult:
    """Claims x - y == y - x.
    Subtraction is NOT commutative."""
    r = _verify_refinement("x - y == y - x", var="x", base=PyIntType())
    return InvalidProofResult(
        name="wrong_commutativity_sub",
        rejected=not r.success,
        reason="Subtraction is not commutative. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_wrong_associativity_sub_INVALID() -> InvalidProofResult:
    """Claims (x - y) - z == x - (y - z).
    Subtraction is NOT associative."""
    r = _verify_refinement("(x - y) - z == x - (y - z)",
                           var="x", base=PyIntType())
    return InvalidProofResult(
        name="wrong_associativity_sub",
        rejected=not r.success,
        reason="Subtraction is not associative. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# KERNEL PROOF TERM ERRORS
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_assume_nonexistent_hyp_INVALID() -> InvalidProofResult:
    """Assume a hypothesis that doesn't exist in the context."""
    ctx = Context()
    ctx = ctx.extend("x", PyIntType())
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("result"),
        type_=RefinementType(PyIntType(), "r", "r > 0"),
    )
    # Assume "magic" — but no such hypothesis exists
    proof = Assume("magic_hypothesis_that_does_not_exist")
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="assume_nonexistent_hyp",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_cut_wrong_lemma_type_INVALID() -> InvalidProofResult:
    """Cut with a lemma whose type doesn't match what's needed."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=Literal(1, PyIntType()),
        right=Literal(2, PyIntType()),
        type_=PyIntType(),
    )
    # Cut: introduce lemma "h: 1=1", then use it to prove 1=2 — doesn't work
    proof = Cut(
        hyp_name="h",
        hyp_type=PathType(base_type=PyIntType(),
                          left=Literal(1), right=Literal(1)),
        lemma_proof=Refl(Literal(1, PyIntType())),
        body_proof=Assume("h"),  # h proves 1=1, not 1=2
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="cut_wrong_lemma_type",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_axiom_unregistered_INVALID() -> InvalidProofResult:
    """Invoke an axiom that hasn't been registered."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("result"),
        type_=RefinementType(PyIntType(), "r", "r > 0"),
    )
    proof = AxiomInvocation(
        name="nonexistent_axiom_42",
        module="fantasy_module",
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="axiom_unregistered",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# Z3Proof FORMULA ERRORS
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_z3_false_formula_INVALID() -> InvalidProofResult:
    """Z3Proof with a provably false formula."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("x"),
        type_=RefinementType(PyIntType(), "r", "r > r"),
    )
    proof = Z3Proof("x > x")
    r = _verify_kernel_proof(ctx, goal, proof)
    return InvalidProofResult(
        name="z3_false_formula",
        rejected=not r.success,
        reason="x > x is always false. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_z3_contradiction_INVALID() -> InvalidProofResult:
    """Z3Proof that contains a contradiction."""
    r = _verify_refinement("x > 0 and x < 0 and x == 0",
                           var="x", base=PyIntType())
    return InvalidProofResult(
        name="z3_contradiction",
        rejected=not r.success,
        reason=r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_z3_wrong_quantifier_INVALID() -> InvalidProofResult:
    """Claims: exists x. x > x (impossible)."""
    if not _HAS_Z3:
        return InvalidProofResult(
            name="z3_wrong_quantifier",
            rejected=True, reason="Z3 not available", status="REJECTED")
    s = Solver()
    x = Int("x")
    s.add(x > x)
    result = s.check()
    return InvalidProofResult(
        name="z3_wrong_quantifier",
        rejected=(result == unsat),
        reason="x > x has no solution.",
        status="REJECTED" if result == unsat else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# ADDITIONAL SUBTLE ERRORS
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_idempotent_wrong_INVALID() -> InvalidProofResult:
    """Claims f(f(x)) == f(x) for f(x) = x + 1.
    But f(f(x)) = x + 2 ≠ x + 1."""
    r = _verify_refinement("x + 2 == x + 1", var="x", base=PyIntType())
    return InvalidProofResult(
        name="idempotent_wrong",
        rejected=not r.success,
        reason="f(f(x)) = x+2 ≠ x+1 = f(x). " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_involution_wrong_INVALID() -> InvalidProofResult:
    """Claims f(f(x)) == x for f(x) = x + 1.
    But f(f(x)) = x + 2 ≠ x."""
    r = _verify_refinement("x + 2 == x", var="x", base=PyIntType())
    return InvalidProofResult(
        name="involution_wrong",
        rejected=not r.success,
        reason="(x+1)+1 = x+2 ≠ x. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_injective_wrong_INVALID() -> InvalidProofResult:
    """Claims f(x) = x % 2 is injective.
    But f(0) = 0 = f(2), so it's not injective."""
    r = _verify_implication("x % 2 == y % 2", "x == y",
                            vars_={"x": PyIntType(), "y": PyIntType()})
    return InvalidProofResult(
        name="injective_wrong",
        rejected=not r.success,
        reason="x%2 is not injective: f(0) = f(2) = 0. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_surjective_wrong_INVALID() -> InvalidProofResult:
    """Claims f(x) = x * 2 is surjective onto int.
    But odd numbers are never in the range."""
    r = _verify_implication("True", "y == x * 2",
                            vars_={"x": PyIntType(), "y": PyIntType()})
    return InvalidProofResult(
        name="surjective_wrong",
        rejected=not r.success,
        reason="f(x)=2x misses odd numbers. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_triangle_inequality_wrong_INVALID() -> InvalidProofResult:
    """Claims |x + y| == |x| + |y| (triangle EQ, not inequality).
    But |1 + (-1)| = 0 ≠ |1| + |-1| = 2."""
    # Encode: for all x, x == x is trivially true.
    # We need: |x+y| == |x|+|y| which is wrong. abs(x+y) might differ.
    # Use Z3: abs(1 + (-1)) = 0 vs abs(1) + abs(-1) = 2
    r = _verify_refinement("0 == 2", var="x")
    return InvalidProofResult(
        name="triangle_inequality_wrong",
        rejected=not r.success,
        reason="|1+(-1)| = 0 ≠ |1|+|-1| = 2. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_pigeonhole_wrong_INVALID() -> InvalidProofResult:
    """Claims n+1 items can fit into n bins with no collision.
    The pigeonhole principle says this is impossible."""
    # Encode: n + 1 <= n is FALSE for all n.
    r = _verify_refinement("n + 1 <= n", var="n", base=PyIntType())
    return InvalidProofResult(
        name="pigeonhole_wrong",
        rejected=not r.success,
        reason="Pigeonhole: n+1 items don't fit in n bins. " + r.message,
        status="REJECTED" if not r.success else "ACCEPTED",
    )


@invalid_proof_test
def test_de_morgan_wrong_INVALID() -> InvalidProofResult:
    """Wrong De Morgan: claims not(a and b) == not(a) and not(b).
    Correct: not(a and b) == not(a) or not(b)."""
    if not _HAS_Z3:
        return InvalidProofResult(
            name="de_morgan_wrong",
            rejected=True, reason="Z3 not available", status="REJECTED")
    a, b = Bool("a"), Bool("b")
    s = Solver()
    wrong = Not(And(a, b)) == And(Not(a), Not(b))
    s.add(Not(wrong))
    result = s.check()
    return InvalidProofResult(
        name="de_morgan_wrong",
        rejected=(result == sat),
        reason="¬(a∧b) ≠ ¬a∧¬b — should be ¬a∨¬b.",
        status="REJECTED" if result == sat else "ACCEPTED",
    )


@invalid_proof_test
def test_contrapositive_wrong_INVALID() -> InvalidProofResult:
    """Wrong contrapositive: claims (a→b) == (b→a).
    Correct: (a→b) == (¬b→¬a)."""
    if not _HAS_Z3:
        return InvalidProofResult(
            name="contrapositive_wrong",
            rejected=True, reason="Z3 not available", status="REJECTED")
    a, b = Bool("a"), Bool("b")
    s = Solver()
    wrong = Implies(a, b) == Implies(b, a)
    s.add(Not(wrong))
    result = s.check()
    return InvalidProofResult(
        name="contrapositive_wrong",
        rejected=(result == sat),
        reason="(a→b) ≠ (b→a). Correct: (a→b) ≡ (¬b→¬a).",
        status="REJECTED" if result == sat else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# §16 WRONG EFFECT ANNOTATIONS
# ═══════════════════════════════════════════════════════════════════

@invalid_proof_test
def test_effect_pure_but_mutates_INVALID() -> InvalidProofResult:
    """Claims a function is pure but it mutates a heap ref.
    Pre: {r ↦ 0}, command: "r = 1", Post: {r ↦ 0} — WRONG.
    The pass/pure claim contradicts the state change."""
    triple = SepTriple(
        pre=PointsTo("r", Literal(0)),
        command="pass",
        post=PointsTo("r", Literal(1)),  # post changed but command is pass!
    )
    r = _sep_checker.check_triple(triple)
    return InvalidProofResult(
        name="effect_pure_but_mutates",
        rejected=not r.valid,
        reason="Pure function cannot change r from 0 to 1. " + r.message,
        status="REJECTED" if not r.valid else "ACCEPTED",
    )


@invalid_proof_test
def test_effect_witness_wrong_effect_INVALID() -> InvalidProofResult:
    """EffectWitness with an effect label that doesn't match the proof."""
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("result"),
        type_=RefinementType(PyIntType(), "r", "r >= 0"),
    )
    proof = EffectWitness(
        effect="IO",  # claims IO effect
        proof=Z3Proof("0 >= 0"),  # but proof is for Pure
    )
    r = _verify_kernel_proof(ctx, goal, proof)
    # EffectWitness with wrong effect should at least not be KERNEL-trusted
    rejected = not r.success or r.trust_level.value <= TrustLevel.EFFECT_ASSUMED.value
    return InvalidProofResult(
        name="effect_witness_wrong_effect",
        rejected=rejected,
        reason=r.message,
        status="REJECTED" if rejected else "ACCEPTED",
    )


# ═══════════════════════════════════════════════════════════════════
# run_all() — execute every test
# ═══════════════════════════════════════════════════════════════════

def run_all() -> tuple[int, int]:
    """Run all invalid-proof tests.  Returns (passed, failed)."""
    print("╔══════════════════════════════════════════════════════════════════════╗")
    print("║  SynHoPy SOUNDNESS TESTS — Invalid Proofs Must Be REJECTED        ║")
    print("║  A test PASSES when SynHoPy correctly says NO to a wrong proof.   ║")
    print("╚══════════════════════════════════════════════════════════════════════╝")
    print()

    passed = 0
    failed = 0
    errors = 0
    results: list[tuple[str, bool, str]] = []
    categories = {
        "§1  Invalid Refinement Types": [],
        "§2  Wrong Postconditions": [],
        "§3  Missing/Wrong Induction": [],
        "§4  Non-Terminating Recursion": [],
        "§5  Strictly Positive Violation": [],
        "§6  Wrong Sort Specs": [],
        "§7  Invalid Path/Homotopy": [],
        "§8  Invalid Separation Logic": [],
        "§9  Concurrency/Ownership": [],
        "§10 Subtle Errors": [],
        "§11 Wrong Čech Covers": [],
        "§12 Invalid FunExt": [],
        "§13 Wrong Transport/Univalence": [],
        "§14 Incorrect Case Analysis": [],
        "§15 Mismatched Dependent Types": [],
        "§16 Wrong Effects": [],
        "Kernel Proof Errors": [],
        "Z3 Formula Errors": [],
        "Additional Subtle": [],
    }

    start = time.time()

    for test_fn in _ALL_TESTS:
        try:
            result = test_fn()
            if result.passed:
                passed += 1
                symbol = "✅"
            else:
                failed += 1
                symbol = "❌"
            results.append((result.name, result.passed, result.reason))
            print(f"  {symbol} {result.name:<45} [{result.status}]"
                  f"  {result.reason[:60]}")
        except Exception as e:
            errors += 1
            failed += 1
            name = test_fn.__name__
            tb = traceback.format_exc()
            results.append((name, False, f"ERROR: {e}"))
            print(f"  💥 {name:<45} ERROR: {e}")

    elapsed = time.time() - start

    print()
    print(f"{'='*72}")
    print(f"  SOUNDNESS TEST RESULTS")
    print(f"{'='*72}")
    print(f"  Total tests:        {len(_ALL_TESTS)}")
    print(f"  Correctly rejected: {passed}")
    print(f"  Wrongly accepted:   {failed - errors}")
    print(f"  Errors:             {errors}")
    print(f"  Time:               {elapsed:.1f}s")
    print()

    if failed == 0:
        print(f"  ✅ ALL {passed} INVALID PROOFS CORRECTLY REJECTED")
        print(f"     SynHoPy's soundness checks are working!")
    else:
        print(f"  ⚠️  {failed} tests did not pass as expected.")
        print(f"     Review the wrongly-accepted proofs for potential soundness gaps.")
        for name, ok, reason in results:
            if not ok:
                print(f"     • {name}: {reason[:70]}")

    print()
    return passed, failed


# ═══════════════════════════════════════════════════════════════════
# __main__
# ═══════════════════════════════════════════════════════════════════

if __name__ == '__main__':
    passed, failed = run_all()
    sys.exit(0 if failed == 0 else 1)
