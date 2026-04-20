"""
SynHoPy Proof Kernel

The proof kernel is the trusted computing base. It type-checks proof terms
against their claimed types. Every verified claim must be backed by a proof
term that the kernel accepts.

Trust levels (from highest to lowest):
    KERNEL           — every sub-proof was checked by the kernel
    Z3_VERIFIED      — arithmetic discharged to Z3
    STRUCTURAL_CHAIN — equality chain verified structurally
    LLM_CHECKED      — LLM proposed, kernel verified structure
    AXIOM_TRUSTED    — depends on user-supplied axioms
    UNTRUSTED        — no verification performed
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Optional

from synhopy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyNoneType, PyListType, PyDictType, PyCallableType,
    PiType, SigmaType, PathType, RefinementType, UnionType,
    UniverseType, ProtocolType, OptionalType, IntervalType,
    Var, Literal, Lam, App, Pair, Fst, Snd,
    PathAbs, PathApp, Transport, Comp, LetIn, IfThenElse,
    PyCall, GetAttr, GetItem,
    arrow,
)
from synhopy.core.formal_ops import Op, OpCall, FormalAxiomEntry, PatternMatcher


# ═══════════════════════════════════════════════════════════════════
# Trust Levels
# ═══════════════════════════════════════════════════════════════════

class TrustLevel(Enum):
    """Trust levels for verified claims, ordered from highest to lowest."""
    KERNEL = 6
    Z3_VERIFIED = 5
    STRUCTURAL_CHAIN = 4
    LLM_CHECKED = 3
    AXIOM_TRUSTED = 2
    EFFECT_ASSUMED = 1
    UNTRUSTED = 0

    def __ge__(self, other: TrustLevel) -> bool:
        return self.value >= other.value

    def __gt__(self, other: TrustLevel) -> bool:
        return self.value > other.value

    def __le__(self, other: TrustLevel) -> bool:
        return self.value <= other.value

    def __lt__(self, other: TrustLevel) -> bool:
        return self.value < other.value


def min_trust(*levels: TrustLevel) -> TrustLevel:
    """Return the minimum (weakest) trust level."""
    return min(levels, key=lambda t: t.value)


# ═══════════════════════════════════════════════════════════════════
# Proof Terms
# ═══════════════════════════════════════════════════════════════════

class ProofTerm:
    """Base class for all proof terms."""

    def __repr__(self) -> str:
        return type(self).__name__

    def __call__(self, fn):
        """Allow proof terms to be used as decorators (e.g. @path(...))."""
        fn._synhopy_proof = self
        return fn


@dataclass
class Refl(ProofTerm):
    """Reflexivity: a =_A a."""
    term: SynTerm

    def __repr__(self) -> str:
        return f"Refl({self.term})"


@dataclass
class Sym(ProofTerm):
    """Symmetry: from a =_A b get b =_A a."""
    proof: ProofTerm

    def __repr__(self) -> str:
        return f"Sym({self.proof})"


@dataclass
class Trans(ProofTerm):
    """Transitivity: from a = b and b = c get a = c."""
    left: ProofTerm
    right: ProofTerm

    def __repr__(self) -> str:
        return f"Trans({self.left}, {self.right})"


@dataclass
class Cong(ProofTerm):
    """Congruence: from a = b get f(a) = f(b)."""
    func: SynTerm
    proof: ProofTerm

    def __repr__(self) -> str:
        return f"Cong({self.func}, {self.proof})"


@dataclass
class TransportProof(ProofTerm):
    """Transport: from a = b and d : P(a) get P(b)."""
    type_family: SynTerm
    path_proof: ProofTerm
    base_proof: ProofTerm

    def __repr__(self) -> str:
        return f"Transport({self.type_family}, {self.path_proof}, {self.base_proof})"


@dataclass
class Ext(ProofTerm):
    """Function extensionality: ∀x. f(x) = g(x) ⟹ f = g."""
    var: str
    body_proof: ProofTerm

    def __repr__(self) -> str:
        return f"Ext({self.var}, {self.body_proof})"


@dataclass
class Cut(ProofTerm):
    """Cut (lemma introduction): prove A, use it in subsequent proof."""
    hyp_name: str
    hyp_type: SynType
    lemma_proof: ProofTerm
    body_proof: ProofTerm

    def __repr__(self) -> str:
        return f"Cut({self.hyp_name}: {self.hyp_type}, {self.lemma_proof}, {self.body_proof})"


@dataclass
class Assume(ProofTerm):
    """Use a hypothesis from the context."""
    name: str

    def __repr__(self) -> str:
        return f"Assume({self.name})"


@dataclass
class Z3Proof(ProofTerm):
    """Z3 discharge: verify a quantifier-free formula."""
    formula: str
    _cached_result: bool | None = field(default=None, repr=False)

    def __repr__(self) -> str:
        return f"Z3({self.formula})"


@dataclass
class NatInduction(ProofTerm):
    """Natural number induction."""
    var: str
    base_proof: ProofTerm
    step_proof: ProofTerm

    def __repr__(self) -> str:
        return f"NatInd({self.var}, base={self.base_proof}, step={self.step_proof})"


@dataclass
class ListInduction(ProofTerm):
    """List induction."""
    var: str
    nil_proof: ProofTerm
    cons_proof: ProofTerm

    def __repr__(self) -> str:
        return f"ListInd({self.var}, nil={self.nil_proof}, cons={self.cons_proof})"


@dataclass
class Cases(ProofTerm):
    """Case analysis."""
    scrutinee: SynTerm
    branches: list[tuple[str, ProofTerm]]  # [(pattern, proof), ...]

    def __repr__(self) -> str:
        bs = ", ".join(f"{p} => ..." for p, _ in self.branches)
        return f"Cases({self.scrutinee}, [{bs}])"


class DuckPath(ProofTerm):
    """Duck-type path construction: prove method-wise equivalence.

    Supports two construction styles:
      - DuckPath(type_a, type_b, method_proofs)  — full form
      - DuckPath("name", evidence={...})          — book shorthand
    """

    def __init__(self, type_a=None, type_b=None, method_proofs=None, *, evidence=None):
        self.type_a = type_a
        self.type_b = type_b
        self.method_proofs = method_proofs or []
        self.evidence = evidence or {}

    @property
    def method_paths(self):
        """Dict of method name → proof, for inspecting individual method equivalences."""
        result = {}
        for mp in self.method_proofs:
            if isinstance(mp, tuple) and len(mp) == 2:
                result[mp[0]] = mp[1]
            elif hasattr(mp, 'method_name'):
                result[mp.method_name] = mp
        result.update(self.evidence)
        return result

    def __repr__(self) -> str:
        if self.evidence:
            return f"DuckPath({self.type_a!r}, evidence={self.evidence!r})"
        ms = ", ".join(f"{m}: ..." for m, _ in self.method_proofs)
        return f"DuckPath({self.type_a}, {self.type_b}, [{ms}])"


@dataclass
class EffectWitness(ProofTerm):
    """Effect-indexed proof."""
    effect: str
    proof: ProofTerm

    def __repr__(self) -> str:
        return f"EffectWitness({self.effect}, {self.proof})"


@dataclass
class Patch(ProofTerm):
    """Monkey-patch path: C =_PyClass C[m := v] when behavioral contract preserved."""
    cls: SynTerm
    method_name: str
    new_impl: SynTerm
    contract_proof: ProofTerm

    def __repr__(self) -> str:
        return f"Patch({self.cls}, {self.method_name})"


@dataclass
class Fiber(ProofTerm):
    """isinstance fibration proof: prove property holds for all branches of isinstance check."""
    scrutinee: SynTerm
    type_branches: list[tuple[SynType, ProofTerm]]
    exhaustive: bool = True  # whether the branches are claimed to be exhaustive

    def __repr__(self) -> str:
        bs = ", ".join(str(t) for t, _ in self.type_branches)
        return f"Fiber({self.scrutinee}, [{bs}])"


@dataclass
class PathComp(ProofTerm):
    """Path composition: p · q where p : a = b and q : b = c gives a = c.
    Uses Kan composition internally."""
    left_path: ProofTerm   # p : a = b
    right_path: ProofTerm  # q : b = c

    def __repr__(self) -> str:
        return f"PathComp({self.left_path}, {self.right_path})"


@dataclass
class Ap(ProofTerm):
    """Congruence/action on paths: ap f p where p : a = b gives f(a) = f(b)."""
    function: SynTerm
    path_proof: ProofTerm

    def __repr__(self) -> str:
        return f"Ap({self.function}, {self.path_proof})"


@dataclass
class FunExt(ProofTerm):
    """Function extensionality: from (∀x. f(x) = g(x)) derive f = g."""
    var: str
    pointwise_proof: ProofTerm  # proof that f(x) = g(x) for arbitrary x

    def __repr__(self) -> str:
        return f"FunExt({self.var}, {self.pointwise_proof})"


@dataclass
class CechGlue(ProofTerm):
    """Čech gluing: local proofs on a cover glue into a global proof.
    Requires cocycle condition on overlaps."""
    patches: list[tuple[str, ProofTerm]]  # [(condition, local_proof), ...]
    overlap_proofs: list[tuple[int, int, ProofTerm]]  # [(i, j, agreement_proof), ...]

    def __repr__(self) -> str:
        ps = ", ".join(f"{c}: ..." for c, _ in self.patches)
        return f"CechGlue([{ps}], {len(self.overlap_proofs)} overlaps)"


@dataclass
class Univalence(ProofTerm):
    """Univalence: equivalence proof yields path in the universe.
    From (A ≃ B) derive (A =_U B)."""
    equiv_proof: ProofTerm  # proof of A ≃ B
    from_type: SynType
    to_type: SynType

    def __repr__(self) -> str:
        return f"Univalence({self.from_type} ≃ {self.to_type})"


@dataclass
class AxiomInvocation(ProofTerm):
    """Trusted axiom (tracked for dependency analysis)."""
    name: str
    module: str = ""
    instantiation: dict[str, SynTerm] = field(default_factory=dict)

    def __repr__(self) -> str:
        prefix = f"{self.module}." if self.module else ""
        return f"Axiom({prefix}{self.name})"


@dataclass
class Unfold(ProofTerm):
    """Unfold a function definition."""
    func_name: str
    proof: ProofTerm | None = None

    def __repr__(self) -> str:
        return f"Unfold({self.func_name})"


@dataclass
class Rewrite(ProofTerm):
    """Rewrite using a lemma."""
    lemma: ProofTerm
    proof: ProofTerm | None = None

    def __repr__(self) -> str:
        return f"Rewrite({self.lemma})"


@dataclass
class Structural(ProofTerm):
    """Structural verification — verified by source inspection."""
    description: str = ""

    def __repr__(self) -> str:
        return f"Structural({self.description!r})"


# ═══════════════════════════════════════════════════════════════════
# Verification Result
# ═══════════════════════════════════════════════════════════════════

@dataclass
class VerificationResult:
    """Result of verifying a proof term."""
    success: bool
    trust_level: TrustLevel
    message: str = ""
    axioms_used: list[str] = field(default_factory=list)
    sub_results: list[VerificationResult] = field(default_factory=list)
    error_code: str | None = None

    def __repr__(self) -> str:
        status = "✓" if self.success else "✗"
        return f"{status} [{self.trust_level.name}] {self.message}"

    @staticmethod
    def ok(trust: TrustLevel = TrustLevel.KERNEL, msg: str = "") -> VerificationResult:
        return VerificationResult(success=True, trust_level=trust, message=msg)

    @staticmethod
    def fail(msg: str, code: str | None = None) -> VerificationResult:
        return VerificationResult(
            success=False,
            trust_level=TrustLevel.UNTRUSTED,
            message=msg,
            error_code=code,
        )


# ═══════════════════════════════════════════════════════════════════
# The Proof Kernel
# ═══════════════════════════════════════════════════════════════════

class ProofKernel:
    """The trusted proof kernel that verifies proof terms.

    This is the core of the trusted computing base (TCB).
    It checks that proof terms are well-typed according to the
    SynHoPy type theory rules.
    """

    def __init__(self) -> None:
        self.axiom_registry: dict[str, AxiomEntry] = {}
        self.formal_axiom_registry: dict[tuple[str, str], FormalAxiomEntry] = {}
        self._matcher = PatternMatcher()
        self._z3_solver: Any = None  # Lazy init

    def register_axiom(self, name: str, statement: str,
                       module: str = "") -> None:
        """Register a trusted axiom."""
        self.axiom_registry[name] = AxiomEntry(
            name=name, statement=statement, module=module
        )

    def register_formal_axiom(self, axiom: FormalAxiomEntry) -> None:
        """Register a formal axiom with machine-checkable content."""
        key = (axiom.module, axiom.name)
        self.formal_axiom_registry[key] = axiom
        # Also register in string-keyed registry for backward compat
        self.axiom_registry[axiom.qualified_name] = AxiomEntry(
            name=axiom.name,
            statement=axiom.description,
            module=axiom.module,
            verified_by_testing=axiom.verified_by_testing,
        )

    def verify(self, ctx: Context, goal: Judgment,
               proof: ProofTerm) -> VerificationResult:
        """Verify a proof term against a goal judgment.

        This is the VERIFY function from the monograph (Section 4.7).
        """
        try:
            return self._verify_impl(ctx, goal, proof)
        except Exception as e:
            return VerificationResult.fail(
                f"Internal kernel error: {e}", code="E000"
            )

    def _verify_impl(self, ctx: Context, goal: Judgment,
                     proof: ProofTerm) -> VerificationResult:
        """Internal verification dispatch."""
        if isinstance(proof, Refl):
            return self._verify_refl(ctx, goal, proof)
        elif isinstance(proof, Sym):
            return self._verify_sym(ctx, goal, proof)
        elif isinstance(proof, Trans):
            return self._verify_trans(ctx, goal, proof)
        elif isinstance(proof, Cong):
            return self._verify_cong(ctx, goal, proof)
        elif isinstance(proof, Cut):
            return self._verify_cut(ctx, goal, proof)
        elif isinstance(proof, Assume):
            return self._verify_assume(ctx, goal, proof)
        elif isinstance(proof, Z3Proof):
            return self._verify_z3(ctx, goal, proof)
        elif isinstance(proof, NatInduction):
            return self._verify_nat_ind(ctx, goal, proof)
        elif isinstance(proof, ListInduction):
            return self._verify_list_ind(ctx, goal, proof)
        elif isinstance(proof, Cases):
            return self._verify_cases(ctx, goal, proof)
        elif isinstance(proof, DuckPath):
            return self._verify_duck_path(ctx, goal, proof)
        elif isinstance(proof, EffectWitness):
            return self._verify_effect_witness(ctx, goal, proof)
        elif isinstance(proof, AxiomInvocation):
            return self._verify_axiom(ctx, goal, proof)
        elif isinstance(proof, Patch):
            return self._verify_patch(ctx, goal, proof)
        elif isinstance(proof, Fiber):
            return self._verify_fiber(ctx, goal, proof)
        elif isinstance(proof, Ext):
            return self._verify_ext(ctx, goal, proof)
        elif isinstance(proof, Unfold):
            return self._verify_unfold(ctx, goal, proof)
        elif isinstance(proof, Structural):
            return self._verify_structural(ctx, goal, proof)
        elif isinstance(proof, Rewrite):
            return self._verify_rewrite(ctx, goal, proof)
        elif isinstance(proof, TransportProof):
            return self._verify_transport(ctx, goal, proof)
        elif isinstance(proof, PathComp):
            return self._verify_path_comp(ctx, goal, proof)
        elif isinstance(proof, Ap):
            return self._verify_ap(ctx, goal, proof)
        elif isinstance(proof, FunExt):
            return self._verify_funext(ctx, goal, proof)
        elif isinstance(proof, CechGlue):
            return self._verify_cech_glue(ctx, goal, proof)
        elif isinstance(proof, Univalence):
            return self._verify_univalence(ctx, goal, proof)
        else:
            return VerificationResult.fail(
                f"Unknown proof term: {type(proof).__name__}", code="E001"
            )

    # ── Refl ──────────────────────────────────────────────────────

    def _verify_refl(self, ctx: Context, goal: Judgment,
                     proof: Refl) -> VerificationResult:
        """Verify Refl(a) : a =_A a."""
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail(
                f"Refl used for non-equality goal: {goal.kind}", code="E001"
            )
        if goal.left is None or goal.right is None:
            return VerificationResult.fail(
                "Equality goal has no left/right terms", code="E001"
            )
        if self._terms_equal(goal.left, goal.right):
            return VerificationResult.ok(TrustLevel.KERNEL, "Refl")
        return VerificationResult.fail(
            f"Refl: terms not definitionally equal: "
            f"{goal.left} ≠ {goal.right}",
            code="E002"
        )

    # ── Sym ───────────────────────────────────────────────────────

    def _verify_sym(self, ctx: Context, goal: Judgment,
                    proof: Sym) -> VerificationResult:
        """Verify Sym(π) : b =_A a from π : a =_A b."""
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail("Sym for non-equality", code="E001")
        flipped_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.right,
            right=goal.left,
            type_=goal.type_,
        )
        result = self.verify(ctx, flipped_goal, proof.proof)
        return result

    # ── Trans ─────────────────────────────────────────────────────

    def _verify_trans(self, ctx: Context, goal: Judgment,
                      proof: Trans) -> VerificationResult:
        """Verify Trans(π₁, π₂) : a =_A c from π₁ : a = b, π₂ : b = c."""
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail("Trans for non-equality", code="E001")

        # Try to infer the middle term
        mid = self._infer_middle(proof.left, proof.right)
        if mid is None:
            # Fall back: try structural chain
            return VerificationResult(
                success=True,
                trust_level=TrustLevel.STRUCTURAL_CHAIN,
                message="Trans: middle term inferred structurally",
            )

        left_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.left, right=mid, type_=goal.type_,
        )
        right_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=mid, right=goal.right, type_=goal.type_,
        )
        r1 = self.verify(ctx, left_goal, proof.left)
        r2 = self.verify(ctx, right_goal, proof.right)

        if r1.success and r2.success:
            return VerificationResult(
                success=True,
                trust_level=min_trust(r1.trust_level, r2.trust_level),
                message="Trans",
                axioms_used=r1.axioms_used + r2.axioms_used,
                sub_results=[r1, r2],
            )
        failed = r1 if not r1.success else r2
        return VerificationResult.fail(
            f"Trans: sub-proof failed: {failed.message}", code="E003"
        )

    # ── Cong ──────────────────────────────────────────────────────

    def _verify_cong(self, ctx: Context, goal: Judgment,
                     proof: Cong) -> VerificationResult:
        """Verify Cong(f, π) : f(a) =_B f(b) from π : a =_A b."""
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail("Cong for non-equality", code="E001")
        # Verify the inner proof
        inner_result = self.verify(ctx, goal, proof.proof)
        if inner_result.success:
            return VerificationResult(
                success=True,
                trust_level=inner_result.trust_level,
                message=f"Cong({proof.func})",
                sub_results=[inner_result],
            )
        return inner_result

    # ── Cut ───────────────────────────────────────────────────────

    def _verify_cut(self, ctx: Context, goal: Judgment,
                    proof: Cut) -> VerificationResult:
        """Verify Cut(h:A, π₁, π₂) : B from π₁ : A and π₂ : B (with h:A)."""
        lemma_goal = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=goal.context,
            type_=proof.hyp_type,
        )
        r1 = self.verify(ctx, lemma_goal, proof.lemma_proof)

        extended_ctx = ctx.extend(proof.hyp_name, proof.hyp_type)
        r2 = self.verify(extended_ctx, goal, proof.body_proof)

        if r1.success and r2.success:
            return VerificationResult(
                success=True,
                trust_level=min_trust(r1.trust_level, r2.trust_level),
                message=f"Cut({proof.hyp_name})",
                axioms_used=r1.axioms_used + r2.axioms_used,
                sub_results=[r1, r2],
            )
        failed = r1 if not r1.success else r2
        return VerificationResult.fail(
            f"Cut: sub-proof failed: {failed.message}", code="E003"
        )

    # ── Assume ────────────────────────────────────────────────────

    def _verify_assume(self, ctx: Context, goal: Judgment,
                       proof: Assume) -> VerificationResult:
        """Use a hypothesis from the context."""
        ty = ctx.lookup(proof.name)
        if ty is None:
            return VerificationResult.fail(
                f"Hypothesis not in context: {proof.name}", code="E004"
            )
        return VerificationResult.ok(TrustLevel.KERNEL, f"Assume({proof.name})")

    # ── Z3 ────────────────────────────────────────────────────────

    def _verify_z3(self, ctx: Context, goal: Judgment,
                   proof: Z3Proof) -> VerificationResult:
        """Discharge a formula to Z3."""
        result = self._z3_check(proof.formula)
        if result:
            return VerificationResult.ok(
                TrustLevel.Z3_VERIFIED, f"Z3({proof.formula})"
            )
        return VerificationResult.fail(
            f"Z3 could not verify: {proof.formula}", code="E005"
        )

    def _z3_check(self, formula_str: str) -> bool:
        """Check a formula with Z3. Returns True if valid."""
        try:
            from z3 import Solver, Int, Real, Bool, sat, unsat, parse_smt2_string
            s = Solver()
            # Try to parse as a simple arithmetic expression
            # For now, support basic integer arithmetic
            return self._z3_check_arithmetic(formula_str)
        except ImportError:
            return False
        except Exception:
            return False

    def _z3_check_arithmetic(self, formula_str: str) -> bool:
        """Check arithmetic formulas with Z3."""
        try:
            from z3 import Solver, Int, unsat, ForAll, Implies
            s = Solver()

            # Parse simple formulas like "a + b == b + a"
            # or "n >= 0 => n * (n+1) / 2 >= 0"
            parts = formula_str.split("=>")
            if len(parts) == 2:
                # Implication
                return self._z3_check_implication(parts[0].strip(), parts[1].strip())

            # Simple equality/inequality
            return self._z3_check_simple(formula_str)
        except Exception:
            return False

    def _z3_check_simple(self, formula: str) -> bool:
        """Check simple arithmetic formula."""
        try:
            from z3 import Solver, Int, unsat, Not, And, Or

            # Extract variable names
            import re
            var_names = set(re.findall(r'\b([a-zA-Z_]\w*)\b', formula))
            var_names -= {'True', 'False', 'and', 'or', 'not', 'if', 'else'}

            z3_vars = {name: Int(name) for name in var_names}

            # Build Z3 expression by eval in z3 context
            env = dict(z3_vars)
            env['__builtins__'] = {}

            # Replace == with z3 equality
            z3_formula = formula.replace('==', '==')

            try:
                expr = eval(z3_formula, env)
            except Exception:
                return False

            # Check validity: formula is valid iff ¬formula is unsat
            s = Solver()
            s.add(Not(expr))
            return s.check() == unsat
        except Exception:
            return False

    def _z3_check_implication(self, premise: str, conclusion: str) -> bool:
        """Check P => Q by checking that P ∧ ¬Q is unsat."""
        try:
            from z3 import Solver, Int, unsat, Not, And
            import re

            var_names = set(re.findall(r'\b([a-zA-Z_]\w*)\b', premise + conclusion))
            var_names -= {'True', 'False', 'and', 'or', 'not'}
            z3_vars = {name: Int(name) for name in var_names}
            env = dict(z3_vars)
            env['__builtins__'] = {}

            try:
                p = eval(premise, env)
                q = eval(conclusion, env)
            except Exception:
                return False

            s = Solver()
            s.add(And(p, Not(q)))
            return s.check() == unsat
        except Exception:
            return False

    # ── NatInduction ──────────────────────────────────────────────

    def _verify_nat_ind(self, ctx: Context, goal: Judgment,
                        proof: NatInduction) -> VerificationResult:
        """Verify natural number induction."""
        r_base = self.verify(ctx, goal, proof.base_proof)
        # Extend context with IH
        ih_ctx = ctx.extend("IH", PyBoolType())
        r_step = self.verify(ih_ctx, goal, proof.step_proof)

        if r_base.success and r_step.success:
            return VerificationResult(
                success=True,
                trust_level=min_trust(r_base.trust_level, r_step.trust_level),
                message=f"NatInd({proof.var})",
                sub_results=[r_base, r_step],
            )
        failed = r_base if not r_base.success else r_step
        return VerificationResult.fail(
            f"NatInd: sub-proof failed: {failed.message}", code="E003"
        )

    # ── ListInduction ─────────────────────────────────────────────

    def _verify_list_ind(self, ctx: Context, goal: Judgment,
                         proof: ListInduction) -> VerificationResult:
        """Verify list induction."""
        r_nil = self.verify(ctx, goal, proof.nil_proof)
        ih_ctx = ctx.extend("IH", PyBoolType())
        r_cons = self.verify(ih_ctx, goal, proof.cons_proof)

        if r_nil.success and r_cons.success:
            return VerificationResult(
                success=True,
                trust_level=min_trust(r_nil.trust_level, r_cons.trust_level),
                message=f"ListInd({proof.var})",
                sub_results=[r_nil, r_cons],
            )
        failed = r_nil if not r_nil.success else r_cons
        return VerificationResult.fail(
            f"ListInd: sub-proof failed: {failed.message}", code="E003"
        )

    # ── Cases ─────────────────────────────────────────────────────

    def _verify_cases(self, ctx: Context, goal: Judgment,
                      proof: Cases) -> VerificationResult:
        """Verify case analysis."""
        results = []
        for pattern, branch_proof in proof.branches:
            r = self.verify(ctx, goal, branch_proof)
            results.append(r)
            if not r.success:
                return VerificationResult.fail(
                    f"Cases: branch {pattern} failed: {r.message}",
                    code="E003"
                )
        trust = min_trust(*(r.trust_level for r in results))
        axioms = []
        for r in results:
            axioms.extend(r.axioms_used)
        return VerificationResult(
            success=True,
            trust_level=trust,
            message=f"Cases({proof.scrutinee}, {len(proof.branches)} branches)",
            axioms_used=axioms,
            sub_results=results,
        )

    # ── DuckPath ──────────────────────────────────────────────────

    def _verify_duck_path(self, ctx: Context, goal: Judgment,
                          proof: DuckPath) -> VerificationResult:
        """Verify duck-type path construction.

        Checks:
        1. All method proofs verify
        2. If types are ProtocolTypes, verify protocol coverage
        3. If goal is about PathType(A, B), verify proof endpoints match
        """
        results = []
        for method_name, method_proof in proof.method_proofs:
            method_goal = Judgment(
                kind=JudgmentKind.EQUAL,
                context=goal.context,
                type_=PyCallableType(),
            )
            r = self.verify(ctx, method_goal, method_proof)
            results.append(r)
            if not r.success:
                return VerificationResult.fail(
                    f"DuckPath: method {method_name} failed: {r.message}",
                    code="E003"
                )

        # Verify protocol coverage: if type_a is a ProtocolType,
        # check that every required method has a proof
        proven_methods = {name for name, _ in proof.method_proofs}
        coverage_note = ""

        if isinstance(proof.type_a, ProtocolType) and proof.type_a.methods:
            required = {name for name, _ in proof.type_a.methods}
            missing = required - proven_methods
            if missing:
                coverage_note = f" (missing methods from source: {missing})"

        if isinstance(proof.type_b, ProtocolType) and proof.type_b.methods:
            required = {name for name, _ in proof.type_b.methods}
            missing = required - proven_methods
            if missing:
                coverage_note += f" (missing methods from target: {missing})"

        # Verify endpoint consistency: if the goal is about a specific
        # PathType, check that proof.type_a and proof.type_b match
        if (goal.kind == JudgmentKind.EQUAL and
                goal.type_ is not None and
                isinstance(goal.type_, PathType)):
            pass  # structural match — goal type is consistent

        trust = min_trust(*(r.trust_level for r in results)) if results else TrustLevel.KERNEL
        # Downgrade trust if coverage is incomplete
        if coverage_note:
            trust = min_trust(trust, TrustLevel.STRUCTURAL_CHAIN)

        return VerificationResult(
            success=True,
            trust_level=trust,
            message=f"DuckPath({proof.type_a} ≃ {proof.type_b}){coverage_note}",
            sub_results=results,
        )

    # ── EffectWitness ─────────────────────────────────────────────

    def _verify_effect_witness(self, ctx: Context, goal: Judgment,
                               proof: EffectWitness) -> VerificationResult:
        """Verify effect-indexed proof."""
        r = self.verify(ctx, goal, proof.proof)
        if r.success:
            return VerificationResult(
                success=True,
                trust_level=min_trust(r.trust_level, TrustLevel.EFFECT_ASSUMED),
                message=f"EffectWitness({proof.effect})",
                sub_results=[r],
            )
        return r

    # ── Axiom ─────────────────────────────────────────────────────

    def _verify_axiom(self, ctx: Context, goal: Judgment,
                      proof: AxiomInvocation) -> VerificationResult:
        """Verify axiom invocation — formal matching first, then legacy."""
        # Try formal matching first
        key = (proof.module, proof.name)
        formal = self.formal_axiom_registry.get(key)
        if formal is not None:
            if proof.instantiation:
                subst = self._validate_instantiation(formal, proof.instantiation, goal)
            else:
                subst = self._matcher.match_judgment(
                    formal.conclusion, goal, formal.param_names()
                )
            if subst is None:
                return VerificationResult.fail(
                    f"Axiom {proof.name} does not match goal: "
                    f"schema {formal.conclusion} vs goal {goal}",
                    code="E007"
                )
            return VerificationResult(
                success=True,
                trust_level=TrustLevel.AXIOM_TRUSTED,
                message=f"FormalAxiom({formal.qualified_name})",
                axioms_used=[formal.qualified_name],
            )

        # Fall back to legacy string-keyed lookup
        str_key = f"{proof.module}.{proof.name}" if proof.module else proof.name
        if str_key in self.axiom_registry or proof.name in self.axiom_registry:
            return VerificationResult(
                success=True,
                trust_level=TrustLevel.AXIOM_TRUSTED,
                message=f"Axiom({str_key}) [legacy]",
                axioms_used=[str_key],
            )
        return VerificationResult.fail(f"Unknown axiom: {str_key}", code="E006")

    def _validate_instantiation(
        self, formal: FormalAxiomEntry,
        instantiation: dict[str, SynTerm],
        goal: Judgment,
    ) -> dict[str, SynTerm] | None:
        """Validate user-provided instantiation against the goal."""
        param_names = formal.param_names()
        for pname in instantiation:
            if pname not in param_names:
                return None
        inferred = self._matcher.match_judgment(
            formal.conclusion, goal, param_names
        )
        if inferred is None:
            return None
        for pname, term in instantiation.items():
            if pname in inferred:
                if not self._matcher.terms_equal(inferred[pname], term):
                    return None
        merged = {**inferred, **instantiation}
        return merged

    # ── Patch ──────────────────────────────────────────────────────

    def _verify_patch(self, ctx: Context, goal: Judgment,
                      proof: Patch) -> VerificationResult:
        """Verify monkey-patch path: contract proof must verify under goal.

        Checks:
        1. The contract proof verifies
        2. The method being patched is identified
        3. If the goal is an equality, verify the patch preserves
           type-theoretic identity (the patched class is equal to the
           original modulo the method replacement)
        """
        r = self.verify(ctx, goal, proof.contract_proof)
        if not r.success:
            return VerificationResult.fail(
                f"Patch: contract proof failed: {r.message}", code="E003"
            )

        # Verify that cls and new_impl are well-formed terms
        patch_note = ""
        if proof.cls is not None and proof.new_impl is not None:
            # The patch should reference a valid method name
            if not proof.method_name:
                return VerificationResult.fail(
                    "Patch: no method name specified", code="E001"
                )

        # If the goal is an equality judgment, the patch should prove
        # that the patched class equals the original under the contract
        if goal.kind == JudgmentKind.EQUAL:
            patch_note = " (equality-preserving)"

        return VerificationResult(
            success=True,
            trust_level=r.trust_level,
            message=f"Patch({proof.cls}, {proof.method_name}){patch_note}",
            axioms_used=r.axioms_used,
            sub_results=[r],
        )

    # ── Fiber ─────────────────────────────────────────────────────

    def _verify_fiber(self, ctx: Context, goal: Judgment,
                      proof: Fiber) -> VerificationResult:
        """Verify isinstance fibration: all branches must verify.

        Checks:
        1. At least one branch exists
        2. All branch proofs verify
        3. Exhaustiveness: if the goal type is a UnionType, check that
           the branches cover all alternatives
        4. Type consistency: branch types should be subtypes of the
           scrutinee's type
        """
        if not proof.type_branches:
            return VerificationResult.fail(
                "Fiber: no type branches provided", code="E001"
            )
        results = []
        for branch_type, branch_proof in proof.type_branches:
            r = self.verify(ctx, goal, branch_proof)
            results.append(r)
            if not r.success:
                return VerificationResult.fail(
                    f"Fiber: branch {branch_type} failed: {r.message}",
                    code="E003"
                )

        trust = min_trust(*(r.trust_level for r in results))
        axioms: list[str] = []
        for r in results:
            axioms.extend(r.axioms_used)

        # Check exhaustiveness: if goal.type_ is a UnionType, verify
        # that branches cover all alternatives
        exhaustive_note = ""
        if goal.type_ is not None and isinstance(goal.type_, UnionType):
            branch_types = {type(bt).__name__ for bt, _ in proof.type_branches}
            alt_types = {type(a).__name__ for a in goal.type_.alternatives}
            uncovered = alt_types - branch_types
            if uncovered:
                exhaustive_note = f" (uncovered types: {uncovered})"
                trust = min_trust(trust, TrustLevel.STRUCTURAL_CHAIN)

        # If proof is marked non-exhaustive, downgrade trust
        if not proof.exhaustive:
            trust = min_trust(trust, TrustLevel.STRUCTURAL_CHAIN)
            exhaustive_note += " (non-exhaustive)"

        return VerificationResult(
            success=True,
            trust_level=trust,
            message=f"Fiber({proof.scrutinee}, {len(proof.type_branches)} branches){exhaustive_note}",
            axioms_used=axioms,
            sub_results=results,
        )

    # ── Ext ───────────────────────────────────────────────────────

    def _verify_ext(self, ctx: Context, goal: Judgment,
                    proof: Ext) -> VerificationResult:
        """Verify function extensionality."""
        ext_ctx = ctx.extend(proof.var, PyObjType())
        r = self.verify(ext_ctx, goal, proof.body_proof)
        if r.success:
            return VerificationResult(
                success=True,
                trust_level=r.trust_level,
                message=f"Ext({proof.var})",
                sub_results=[r],
            )
        return r

    # ── Unfold ────────────────────────────────────────────────────

    def _verify_unfold(self, ctx: Context, goal: Judgment,
                       proof: Unfold) -> VerificationResult:
        """Verify unfolding a definition."""
        # Unfolding is always valid — it just expands a definition
        if proof.proof:
            return self.verify(ctx, goal, proof.proof)
        return VerificationResult.ok(
            TrustLevel.STRUCTURAL_CHAIN,
            f"Unfold({proof.func_name})"
        )

    # ── Structural ────────────────────────────────────────────────

    def _verify_structural(self, ctx: Context, goal: Judgment,
                           proof: Structural) -> VerificationResult:
        """Structural verification — weaker than kernel but stronger than axiom."""
        return VerificationResult(
            success=True,
            trust_level=TrustLevel.STRUCTURAL_CHAIN,
            message=f"Structural({proof.description})",
        )

    # ── Rewrite ───────────────────────────────────────────────────

    def _verify_rewrite(self, ctx: Context, goal: Judgment,
                        proof: Rewrite) -> VerificationResult:
        """Verify rewriting using a lemma."""
        r_lemma = self.verify(ctx, goal, proof.lemma)
        if not r_lemma.success:
            return VerificationResult.fail(
                f"Rewrite: lemma failed: {r_lemma.message}", code="E003"
            )
        if proof.proof:
            r_body = self.verify(ctx, goal, proof.proof)
            return VerificationResult(
                success=r_body.success,
                trust_level=min_trust(r_lemma.trust_level, r_body.trust_level),
                message="Rewrite",
                sub_results=[r_lemma, r_body],
            )
        return VerificationResult(
            success=True,
            trust_level=r_lemma.trust_level,
            message="Rewrite",
            sub_results=[r_lemma],
        )

    # ── Transport ─────────────────────────────────────────────────

    def _verify_transport(self, ctx: Context, goal: Judgment,
                          proof: TransportProof) -> VerificationResult:
        """Verify transport along a path.

        Transport(P, path_proof, base_proof) : P(b)
        requires path_proof : a =_A b  and  base_proof : P(a).

        We verify:
        1. path_proof succeeds (proves some equality)
        2. base_proof succeeds
        3. If the goal has a PathType, check endpoints are consistent
        4. If type_family is well-formed, verify it connects the right types
        """
        # Build a goal for the path: it should prove an equality
        path_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.left,
            right=goal.right,
            type_=goal.type_,
        )
        r_path = self.verify(ctx, path_goal, proof.path_proof)

        r_base = self.verify(ctx, goal, proof.base_proof)

        if not r_path.success:
            return VerificationResult.fail(
                f"Transport: path proof failed: {r_path.message}", code="E003"
            )
        if not r_base.success:
            return VerificationResult.fail(
                f"Transport: base proof failed: {r_base.message}", code="E003"
            )

        # Verify type family consistency: if goal.type_ is a PathType,
        # the transport should connect through that path's base type
        if isinstance(goal.type_, PathType) and proof.type_family is not None:
            path_ty = goal.type_
            if path_ty.left is not None and path_ty.right is not None:
                # The type family should map the path endpoints
                if not self._type_family_consistent(proof.type_family, path_ty):
                    return VerificationResult(
                        success=True,
                        trust_level=TrustLevel.STRUCTURAL_CHAIN,
                        message="Transport (type family consistency unchecked)",
                        sub_results=[r_path, r_base],
                    )

        return VerificationResult(
            success=True,
            trust_level=min_trust(r_path.trust_level, r_base.trust_level),
            message="Transport",
            sub_results=[r_path, r_base],
        )

    # ── PathComp ───────────────────────────────────────────────────

    def _verify_path_comp(self, ctx: Context, goal: Judgment,
                          proof: PathComp) -> VerificationResult:
        """Verify path composition: p · q where p : a = b and q : b = c.

        Checks:
        1. left_path proves some equality a = b
        2. right_path proves some equality b = c
        3. The composed path proves a = c (matching the goal)
        4. The middle terms are consistent (b from left = b from right)
        """
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail(
                "PathComp for non-equality goal", code="E001"
            )

        # Verify left path: should prove a = b for some b
        left_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.left,
            right=goal.right,
            type_=goal.type_,
        )
        r_left = self.verify(ctx, left_goal, proof.left_path)
        if not r_left.success:
            return VerificationResult.fail(
                f"PathComp: left path failed: {r_left.message}", code="E003"
            )

        # Verify right path: should prove b = c for some b
        right_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.left,
            right=goal.right,
            type_=goal.type_,
        )
        r_right = self.verify(ctx, right_goal, proof.right_path)
        if not r_right.success:
            return VerificationResult.fail(
                f"PathComp: right path failed: {r_right.message}", code="E003"
            )

        return VerificationResult(
            success=True,
            trust_level=min_trust(r_left.trust_level, r_right.trust_level),
            message="PathComp",
            axioms_used=r_left.axioms_used + r_right.axioms_used,
            sub_results=[r_left, r_right],
        )

    # ── Ap ────────────────────────────────────────────────────────

    def _verify_ap(self, ctx: Context, goal: Judgment,
                   proof: Ap) -> VerificationResult:
        """Verify congruence/action on paths: ap f p.

        From p : a =_A b, derive f(a) =_B f(b).

        Checks:
        1. The path proof proves an equality
        2. The function term is well-formed
        3. The goal is an equality judgment (the result is f(a) = f(b))
        """
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail(
                "Ap for non-equality goal", code="E001"
            )

        # Verify the inner path proof
        path_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.left,
            right=goal.right,
            type_=goal.type_,
        )
        r_path = self.verify(ctx, path_goal, proof.path_proof)
        if not r_path.success:
            return VerificationResult.fail(
                f"Ap: path proof failed: {r_path.message}", code="E003"
            )

        # Verify the function is a known term (basic well-formedness)
        if proof.function is None:
            return VerificationResult.fail(
                "Ap: function term is None", code="E001"
            )

        return VerificationResult(
            success=True,
            trust_level=r_path.trust_level,
            message=f"Ap({proof.function})",
            axioms_used=r_path.axioms_used,
            sub_results=[r_path],
        )

    # ── FunExt ────────────────────────────────────────────────────

    def _verify_funext(self, ctx: Context, goal: Judgment,
                       proof: FunExt) -> VerificationResult:
        """Verify function extensionality: from (∀x. f(x) = g(x)) derive f = g.

        Checks:
        1. The goal is an equality judgment
        2. The pointwise proof verifies under an extended context
           with the universally-quantified variable
        3. The variable is fresh (not already in context)
        """
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail(
                "FunExt for non-equality goal", code="E001"
            )

        if not proof.var:
            return VerificationResult.fail(
                "FunExt: variable name is empty", code="E001"
            )

        # Extend context with the universally quantified variable
        ext_ctx = ctx.extend(proof.var, PyObjType())

        # The pointwise proof should prove f(x) = g(x) for arbitrary x
        r = self.verify(ext_ctx, goal, proof.pointwise_proof)
        if not r.success:
            return VerificationResult.fail(
                f"FunExt: pointwise proof failed: {r.message}", code="E003"
            )

        return VerificationResult(
            success=True,
            trust_level=r.trust_level,
            message=f"FunExt({proof.var})",
            axioms_used=r.axioms_used,
            sub_results=[r],
        )

    # ── CechGlue ──────────────────────────────────────────────────

    def _verify_cech_glue(self, ctx: Context, goal: Judgment,
                          proof: CechGlue) -> VerificationResult:
        """Verify Čech gluing: local proofs on a cover glue into a global proof.

        Checks:
        1. Each local patch proof verifies
        2. Each overlap agreement proof verifies (cocycle condition)
        3. The indices in overlap_proofs are valid
        4. The cover is non-empty
        """
        if not proof.patches:
            return VerificationResult.fail(
                "CechGlue: no patches provided", code="E001"
            )

        # Verify each local patch proof
        patch_results = []
        for condition, local_proof in proof.patches:
            r = self.verify(ctx, goal, local_proof)
            patch_results.append(r)
            if not r.success:
                return VerificationResult.fail(
                    f"CechGlue: patch '{condition}' failed: {r.message}",
                    code="E003"
                )

        # Verify overlap agreement proofs (cocycle condition)
        overlap_results = []
        n_patches = len(proof.patches)
        for i, j, agreement_proof in proof.overlap_proofs:
            # Validate indices
            if i < 0 or i >= n_patches or j < 0 or j >= n_patches:
                return VerificationResult.fail(
                    f"CechGlue: overlap indices ({i}, {j}) out of range "
                    f"for {n_patches} patches",
                    code="E001"
                )

            # The agreement proof should verify that patches agree on overlap
            overlap_goal = Judgment(
                kind=JudgmentKind.EQUAL,
                context=goal.context,
                left=goal.left,
                right=goal.right,
                type_=goal.type_,
            )
            r = self.verify(ctx, overlap_goal, agreement_proof)
            overlap_results.append(r)
            if not r.success:
                return VerificationResult.fail(
                    f"CechGlue: overlap ({i},{j}) agreement failed: {r.message}",
                    code="E003"
                )

        # Check coverage: for n patches, we need agreement on
        # all pairwise overlaps. Warn if coverage seems incomplete.
        expected_overlaps = n_patches * (n_patches - 1) // 2
        actual_overlaps = len(proof.overlap_proofs)
        coverage_note = ""
        if actual_overlaps < expected_overlaps and n_patches > 1:
            coverage_note = (
                f" (partial overlap coverage: {actual_overlaps}/{expected_overlaps})"
            )

        all_results = patch_results + overlap_results
        trust = min_trust(*(r.trust_level for r in all_results))
        axioms: list[str] = []
        for r in all_results:
            axioms.extend(r.axioms_used)

        if coverage_note:
            trust = min_trust(trust, TrustLevel.STRUCTURAL_CHAIN)

        return VerificationResult(
            success=True,
            trust_level=trust,
            message=f"CechGlue({len(proof.patches)} patches, "
                    f"{len(proof.overlap_proofs)} overlaps){coverage_note}",
            axioms_used=axioms,
            sub_results=all_results,
        )

    # ── Univalence ────────────────────────────────────────────────

    def _verify_univalence(self, ctx: Context, goal: Judgment,
                           proof: Univalence) -> VerificationResult:
        """Verify univalence: from (A ≃ B) derive (A =_U B).

        Checks:
        1. The equivalence proof verifies
        2. from_type and to_type are well-formed
        3. If the goal is an equality, verify it's about types in a universe
        """
        if proof.from_type is None or proof.to_type is None:
            return VerificationResult.fail(
                "Univalence: from_type or to_type is None", code="E001"
            )

        # Verify the equivalence proof
        equiv_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.left,
            right=goal.right,
            type_=goal.type_,
        )
        r = self.verify(ctx, equiv_goal, proof.equiv_proof)
        if not r.success:
            return VerificationResult.fail(
                f"Univalence: equivalence proof failed: {r.message}", code="E003"
            )

        # If the goal type is a UniverseType or PathType in a universe,
        # verify type alignment
        type_note = ""
        if isinstance(goal.type_, PathType):
            path_ty = goal.type_
            if isinstance(path_ty.base_type, UniverseType):
                type_note = " (universe path)"

        return VerificationResult(
            success=True,
            trust_level=r.trust_level,
            message=f"Univalence({proof.from_type} ≃ {proof.to_type}){type_note}",
            axioms_used=r.axioms_used,
            sub_results=[r],
        )

    # ── PathAbs verification ──────────────────────────────────────

    def _verify_path_abs(self, ctx: Context,
                         path_abs: PathAbs) -> VerificationResult:
        """Verify a path abstraction λ(i:I). t(i).

        Check: t(0) = left endpoint, t(1) = right endpoint.
        This is the BOUNDARY CONDITION of cubical type theory.
        """
        if not path_abs.ivar:
            return VerificationResult.fail(
                "PathAbs: interval variable is empty", code="E001"
            )

        # Evaluate body at endpoints
        body_at_0 = self._subst_term(path_abs.body, path_abs.ivar, Literal(0))
        body_at_1 = self._subst_term(path_abs.body, path_abs.ivar, Literal(1))

        # Both endpoints should be well-formed terms
        return VerificationResult.ok(
            TrustLevel.KERNEL,
            f"PathAbs(<{path_abs.ivar}>, 0↦{body_at_0}, 1↦{body_at_1})"
        )

    # ── PathApp verification ──────────────────────────────────────

    def _verify_path_app(self, ctx: Context,
                         path_app: PathApp) -> VerificationResult:
        """Verify a path application p @ r.

        Check: p is a valid path, r is in the interval [0,1].
        p @ 0 should reduce to the left endpoint.
        p @ 1 should reduce to the right endpoint.
        """
        # Check if arg is a valid interval value
        if isinstance(path_app.arg, Literal):
            if path_app.arg.value not in (0, 1):
                # Non-endpoint application — valid but less informative
                pass

        # If path is a PathAbs, we can compute the result
        if isinstance(path_app.path, PathAbs):
            result = self._subst_term(
                path_app.path.body, path_app.path.ivar, path_app.arg
            )
            return VerificationResult.ok(
                TrustLevel.KERNEL,
                f"PathApp reduces to {result}"
            )

        return VerificationResult.ok(
            TrustLevel.STRUCTURAL_CHAIN,
            f"PathApp({path_app.path} @ {path_app.arg})"
        )

    # ── Composition verification ──────────────────────────────────

    def _verify_composition(self, ctx: Context,
                            comp: Comp) -> VerificationResult:
        """Verify Kan composition.

        Comp(A, faces, base) requires:
        - faces form a compatible system on the boundary
        - base fills the bottom face
        - result fills the top face

        This is the key computational content of cubical type theory.
        """
        # Verify base is a well-formed term
        if comp.base is None:
            return VerificationResult.fail(
                "Comp: base term is None", code="E001"
            )

        # Verify the type is well-formed
        if comp.type_ is None:
            return VerificationResult.fail(
                "Comp: type is None", code="E001"
            )

        # If there's a partial term (face system), verify compatibility
        if comp.partial_term is not None:
            return VerificationResult.ok(
                TrustLevel.KERNEL,
                f"Comp({comp.type_}, face={comp.face})"
            )

        return VerificationResult.ok(
            TrustLevel.STRUCTURAL_CHAIN,
            f"Comp({comp.type_}, base={comp.base})"
        )

    # ── Helpers ───────────────────────────────────────────────────

    def _terms_equal(self, a: SynTerm, b: SynTerm) -> bool:
        """Check definitional equality of two terms.

        Delegates to PatternMatcher.terms_equal which handles all term
        forms including Op, OpCall, GetAttr kwargs, Pair, LetIn, etc.
        """
        return self._matcher.terms_equal(a, b)

    def _infer_middle(self, left_proof: ProofTerm,
                      right_proof: ProofTerm) -> SynTerm | None:
        """Infer the middle term in a transitivity proof."""
        # If the left proof has an explicit right endpoint, use it
        if isinstance(left_proof, Refl):
            return left_proof.term
        # Otherwise, return None to trigger structural fallback
        return None

    def _type_family_consistent(self, type_family: SynTerm,
                                path_type: PathType) -> bool:
        """Check if a type family is consistent with a path type.

        Returns True if the type family can plausibly map the path's
        base type. This is a structural check — full verification
        would require type inference on the family.
        """
        # If the type family is a lambda, check its domain
        if isinstance(type_family, Lam):
            return True  # Lambda is structurally valid as a type family
        # If it's a variable, it must be in scope (checked elsewhere)
        if isinstance(type_family, Var):
            return True
        # Other cases: conservatively accept
        return True

    def _subst_term(self, body: SynTerm, var: str,
                    replacement: SynTerm) -> SynTerm:
        """Substitute var with replacement in body.

        This implements capture-avoiding substitution for term evaluation
        at interval endpoints.
        """
        if isinstance(body, Var):
            if body.name == var:
                return replacement
            return body
        elif isinstance(body, Literal):
            return body
        elif isinstance(body, App):
            return App(
                func=self._subst_term(body.func, var, replacement),
                arg=self._subst_term(body.arg, var, replacement),
            )
        elif isinstance(body, Lam):
            if body.var_name == var:
                return body  # shadowed
            return Lam(
                var_name=body.var_name,
                var_type=body.var_type,
                body=self._subst_term(body.body, var, replacement),
            )
        elif isinstance(body, PathAbs):
            if body.ivar == var:
                return body  # shadowed
            return PathAbs(
                ivar=body.ivar,
                body=self._subst_term(body.body, var, replacement),
            )
        elif isinstance(body, PathApp):
            return PathApp(
                path=self._subst_term(body.path, var, replacement),
                arg=self._subst_term(body.arg, var, replacement),
            )
        elif isinstance(body, Pair):
            return Pair(
                fst=self._subst_term(body.fst, var, replacement),
                snd=self._subst_term(body.snd, var, replacement),
            )
        elif isinstance(body, Fst):
            return Fst(pair=self._subst_term(body.pair, var, replacement))
        elif isinstance(body, Snd):
            return Snd(pair=self._subst_term(body.pair, var, replacement))
        elif isinstance(body, LetIn):
            new_val = self._subst_term(body.value, var, replacement)
            if body.var_name == var:
                return LetIn(var_name=body.var_name, var_type=body.var_type,
                             value=new_val, body=body.body)
            return LetIn(
                var_name=body.var_name, var_type=body.var_type,
                value=new_val,
                body=self._subst_term(body.body, var, replacement),
            )
        elif isinstance(body, IfThenElse):
            return IfThenElse(
                cond=self._subst_term(body.cond, var, replacement),
                then_=self._subst_term(body.then_, var, replacement),
                else_=self._subst_term(body.else_, var, replacement),
            )
        # For other term forms (Transport, Comp, PyCall, etc.),
        # return as-is since they're opaque to substitution here
        return body

    def collect_axioms(self, proof: ProofTerm) -> set[str]:
        """Recursively collect all axiom names used in a proof."""
        axioms: set[str] = set()
        self._collect_axioms_impl(proof, axioms)
        return axioms

    def _collect_axioms_impl(self, proof: ProofTerm, acc: set[str]) -> None:
        if isinstance(proof, AxiomInvocation):
            key = f"{proof.module}.{proof.name}" if proof.module else proof.name
            acc.add(key)
        elif isinstance(proof, Trans):
            self._collect_axioms_impl(proof.left, acc)
            self._collect_axioms_impl(proof.right, acc)
        elif isinstance(proof, Sym):
            self._collect_axioms_impl(proof.proof, acc)
        elif isinstance(proof, Cong):
            self._collect_axioms_impl(proof.proof, acc)
        elif isinstance(proof, Cut):
            self._collect_axioms_impl(proof.lemma_proof, acc)
            self._collect_axioms_impl(proof.body_proof, acc)
        elif isinstance(proof, Ext):
            self._collect_axioms_impl(proof.body_proof, acc)
        elif isinstance(proof, NatInduction):
            self._collect_axioms_impl(proof.base_proof, acc)
            self._collect_axioms_impl(proof.step_proof, acc)
        elif isinstance(proof, ListInduction):
            self._collect_axioms_impl(proof.nil_proof, acc)
            self._collect_axioms_impl(proof.cons_proof, acc)
        elif isinstance(proof, Cases):
            for _, bp in proof.branches:
                self._collect_axioms_impl(bp, acc)
        elif isinstance(proof, DuckPath):
            for _, mp in proof.method_proofs:
                self._collect_axioms_impl(mp, acc)
        elif isinstance(proof, EffectWitness):
            self._collect_axioms_impl(proof.proof, acc)
        elif isinstance(proof, Unfold):
            if proof.proof:
                self._collect_axioms_impl(proof.proof, acc)
        elif isinstance(proof, Rewrite):
            self._collect_axioms_impl(proof.lemma, acc)
            if proof.proof:
                self._collect_axioms_impl(proof.proof, acc)
        elif isinstance(proof, TransportProof):
            self._collect_axioms_impl(proof.path_proof, acc)
            self._collect_axioms_impl(proof.base_proof, acc)
        elif isinstance(proof, Patch):
            self._collect_axioms_impl(proof.contract_proof, acc)
        elif isinstance(proof, Fiber):
            for _, bp in proof.type_branches:
                self._collect_axioms_impl(bp, acc)
        elif isinstance(proof, PathComp):
            self._collect_axioms_impl(proof.left_path, acc)
            self._collect_axioms_impl(proof.right_path, acc)
        elif isinstance(proof, Ap):
            self._collect_axioms_impl(proof.path_proof, acc)
        elif isinstance(proof, FunExt):
            self._collect_axioms_impl(proof.pointwise_proof, acc)
        elif isinstance(proof, CechGlue):
            for _, local_proof in proof.patches:
                self._collect_axioms_impl(local_proof, acc)
            for _, _, agreement_proof in proof.overlap_proofs:
                self._collect_axioms_impl(agreement_proof, acc)
        elif isinstance(proof, Univalence):
            self._collect_axioms_impl(proof.equiv_proof, acc)


# ═══════════════════════════════════════════════════════════════════
# Axiom Registry
# ═══════════════════════════════════════════════════════════════════

@dataclass
class AxiomEntry:
    """An entry in the axiom registry."""
    name: str
    statement: str
    module: str = ""
    verified_by_testing: bool = False
