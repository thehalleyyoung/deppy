"""C⁴ Proof DSL — a Pythonic language for writing proofs.

This module provides a pretty, readable DSL for constructing C⁴ proof terms.
Instead of building ProofTerm trees manually, proofs read like mathematical
arguments:

    @c4_proof
    def factorial_equiv(pb):
        '''fact_rec ≡ fact_iter'''
        pb.by_induction(on='n', over=FACT_REC)
        pb.base(pb.refl(lit(1)))
        pb.step(
            pb.calc(
                pb.have('ih', 'fact_rec(n) = fact_iter(n)'),
                pb.rewrite('ih'),
            )
        )

The DSL compiles to the existing ProofTerm types — it is syntactic sugar,
not a new proof system. The checker verifies the compiled terms.

Inspired by Lean 4's tactic mode and calc blocks.
"""
from __future__ import annotations

import functools
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Tuple, Union

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

from cctt.proof_theory.terms import (
    ProofTerm,
    Refl, Sym, Trans, Cong,
    Beta, Delta, Eta,
    NatInduction, ListInduction, WellFoundedInduction,
    AxiomApp, MathlibTheorem,
    LoopInvariant, Simulation, AbstractionRefinement,
    CommDiagram, FunctorMap,
    Z3Discharge,
    FiberDecomposition, CechGluing,
    Assume, Cut, LetProof,
    CasesSplit, Ext,
    Rewrite, RewriteChain,
    ArithmeticSimp, ListSimp, Definitional,
    FiberRestrict, Descent, PathCompose, MathLibAxiom, FiberwiseUnivalence,
    normalize_term, free_vars, terms_equal,
    var, lit, op, app, lam, fold_term, case, fix, seq, abstract, unknown,
)

from cctt.proof_theory.checker import (
    check_proof, VerificationResult, ProofContext,
)


# ═══════════════════════════════════════════════════════════════════
# Proof builder — accumulates proof steps
# ═══════════════════════════════════════════════════════════════════

@dataclass
class CalcStep:
    """A single step in a calculational proof."""
    term: OTerm
    justification: ProofTerm
    label: str = ''


@dataclass
class ProofBuilder:
    """Accumulates proof steps and compiles them to ProofTerms.

    This is the main entry point for the DSL. Create one via @c4_proof
    or manually, then call methods to build your proof.
    """
    lhs: Optional[OTerm] = None
    rhs: Optional[OTerm] = None
    _result: Optional[ProofTerm] = None
    _lemmas: Dict[str, Tuple[OTerm, OTerm, ProofTerm]] = field(default_factory=dict)
    _calc_steps: List[CalcStep] = field(default_factory=list)
    _assumptions: Dict[str, Tuple[OTerm, OTerm]] = field(default_factory=dict)
    _context: Optional[ProofContext] = None

    @property
    def result(self) -> Optional[ProofTerm]:
        """The compiled proof term, if building is complete."""
        return self._result

    # ─── Structural rules ─────────────────────────────────────────

    def refl(self, term: Optional[OTerm] = None) -> ProofTerm:
        """Reflexivity: a ≡ a."""
        t = term or self.lhs or OLit(0)
        proof = Refl(term=t)
        self._result = proof
        return proof

    def sym(self, proof: ProofTerm) -> ProofTerm:
        """Symmetry: flip a ≡ b to b ≡ a."""
        result = Sym(proof=proof)
        self._result = result
        return result

    def trans(self, left: ProofTerm, right: ProofTerm,
              via: Optional[OTerm] = None) -> ProofTerm:
        """Transitivity: chain a ≡ b and b ≡ c."""
        result = Trans(left=left, right=right, middle=via)
        self._result = result
        return result

    def congr(self, func: str, *arg_proofs: ProofTerm) -> ProofTerm:
        """Congruence: lift proofs through a function."""
        result = Cong(func=func, arg_proofs=tuple(arg_proofs))
        self._result = result
        return result

    # ─── Computation rules ────────────────────────────────────────

    def unfold(self, func_name: str, *args: OTerm,
               body: Optional[OTerm] = None) -> ProofTerm:
        """δ-reduction: unfold a definition."""
        result = Delta(func_name=func_name, args=tuple(args), body=body)
        self._result = result
        return result

    def beta(self, lam_term: OTerm, arg: OTerm) -> ProofTerm:
        """β-reduction: apply a lambda."""
        result = Beta(lam=lam_term, arg=arg)
        self._result = result
        return result

    def eta(self, term: OTerm) -> ProofTerm:
        """η-reduction: λx.f(x) ≡ f."""
        result = Eta(term=term)
        self._result = result
        return result

    # ─── Intermediate lemmas ──────────────────────────────────────

    def have(self, name: str, lhs: OTerm, rhs: OTerm,
             by: Optional[ProofTerm] = None) -> ProofTerm:
        """Introduce a named lemma (like Lean's 'have').

        If ``by`` is provided, it's the proof. Otherwise an Assume is created.
        """
        if by is not None:
            proof = by
        else:
            proof = Assume(label=name, assumed_lhs=lhs, assumed_rhs=rhs)

        self._lemmas[name] = (lhs, rhs, proof)
        return proof

    def suffices(self, name: str, lhs: OTerm, rhs: OTerm,
                 then: Optional[ProofTerm] = None) -> ProofTerm:
        """It suffices to show lhs ≡ rhs (like Lean's 'suffices')."""
        return self.have(name, lhs, rhs, by=then)

    def show(self, proof: ProofTerm) -> ProofTerm:
        """Finalize: set the proof result."""
        self._result = proof
        return proof

    def assume(self, name: str, lhs: OTerm, rhs: OTerm) -> ProofTerm:
        """Record an assumption (hypothesis)."""
        proof = Assume(label=name, assumed_lhs=lhs, assumed_rhs=rhs)
        self._assumptions[name] = (lhs, rhs)
        return proof

    # ─── Induction ────────────────────────────────────────────────

    def by_induction(
        self,
        on: str,
        base: ProofTerm,
        step: ProofTerm,
        structure: str = 'nat',
        base_value: Optional[OTerm] = None,
    ) -> ProofTerm:
        """Proof by induction.

        Parameters
        ----------
        on : str
            Variable to induct on.
        base : ProofTerm
            Base case proof.
        step : ProofTerm
            Inductive step proof.
        structure : 'nat' or 'list'
            Induction principle.
        base_value : OTerm, optional
            Base value (default: 0 for nat, [] for list).
        """
        if structure == 'list':
            result = ListInduction(
                nil_case=base,
                cons_case=step,
                variable=on,
            )
        else:
            bv = base_value or OLit(0)
            result = NatInduction(
                base_case=base,
                inductive_step=step,
                variable=on,
                base_value=bv,
            )
        self._result = result
        return result

    def by_strong_induction(
        self,
        measure: str,
        step: ProofTerm,
    ) -> ProofTerm:
        """Well-founded induction on a measure."""
        result = WellFoundedInduction(
            measure=measure,
            step=step,
        )
        self._result = result
        return result

    # ─── Case analysis ────────────────────────────────────────────

    def by_cases(
        self,
        on: OTerm,
        cases: Dict[str, ProofTerm],
    ) -> ProofTerm:
        """Proof by case analysis."""
        result = CasesSplit(discriminant=on, cases=cases)
        self._result = result
        return result

    # ─── Calculational proofs ─────────────────────────────────────

    def calc_chain(self, *steps: Tuple[OTerm, ProofTerm]) -> ProofTerm:
        """Build a calculational proof chain.

        Each step is (intermediate_term, justification_proof).

        Example::

            pb.calc_chain(
                (term_b, proof_a_eq_b),
                (term_c, proof_b_eq_c),
                (term_d, proof_c_eq_d),
            )

        Produces: trans(proof_a_eq_b, trans(proof_b_eq_c, proof_c_eq_d))
        """
        if not steps:
            return self.refl()

        if len(steps) == 1:
            _, proof = steps[0]
            self._result = proof
            return proof

        intermediates = tuple(s[0] for s in steps[:-1])
        proofs = tuple(s[1] for s in steps)
        result = RewriteChain(steps=proofs, intermediates=intermediates)
        self._result = result
        return result

    def calc_trans(self, *proofs: ProofTerm) -> ProofTerm:
        """Chain multiple proofs transitively.

        Shorthand for nested Trans when intermediates are implicit.
        """
        if not proofs:
            return self.refl()
        if len(proofs) == 1:
            self._result = proofs[0]
            return proofs[0]

        result = proofs[0]
        for p in proofs[1:]:
            result = Trans(left=result, right=p)
        self._result = result
        return result

    # ─── Rewriting ────────────────────────────────────────────────

    def rewrite(self, equation: ProofTerm, in_lhs: bool = True,
                position: Tuple[int, ...] = ()) -> ProofTerm:
        """Rewrite using an equation."""
        result = Rewrite(equation=equation, in_lhs=in_lhs, position=position)
        self._result = result
        return result

    # ─── Tactics ──────────────────────────────────────────────────

    def simp(self, lhs: OTerm, rhs: OTerm) -> ProofTerm:
        """Simplification (arithmetic)."""
        result = ArithmeticSimp(lhs_expr=lhs, rhs_expr=rhs)
        self._result = result
        return result

    def ring(self, lhs: OTerm, rhs: OTerm) -> ProofTerm:
        """Ring arithmetic simplification."""
        return self.simp(lhs, rhs)

    def omega(self, formula: str, **variables: str) -> ProofTerm:
        """Linear arithmetic via Z3."""
        result = Z3Discharge(
            formula=formula,
            fragment='linear_arithmetic',
            variables=variables,
        )
        self._result = result
        return result

    def z3(self, formula: str, fragment: str = 'qf_lia',
           timeout_ms: int = 5000, **variables: str) -> ProofTerm:
        """Discharge to Z3."""
        result = Z3Discharge(
            formula=formula,
            fragment=fragment,
            timeout_ms=timeout_ms,
            variables=variables,
        )
        self._result = result
        return result

    # ─── Strategy combinators ─────────────────────────────────────

    def by_simulation(
        self,
        relation: str,
        init: ProofTerm,
        step: ProofTerm,
        output: ProofTerm,
    ) -> ProofTerm:
        """Prove by bisimulation."""
        result = Simulation(
            relation=relation,
            init_proof=init,
            step_proof=step,
            output_proof=output,
        )
        self._result = result
        return result

    def by_abstraction(
        self,
        spec_name: str,
        abs_f: ProofTerm,
        abs_g: ProofTerm,
        abstraction_func: Optional[str] = None,
    ) -> ProofTerm:
        """Prove by abstraction refinement."""
        result = AbstractionRefinement(
            spec_name=spec_name,
            abstraction_f=abs_f,
            abstraction_g=abs_g,
            abstraction_func=abstraction_func,
        )
        self._result = result
        return result

    def by_invariant(
        self,
        invariant: str,
        init: ProofTerm,
        preservation: ProofTerm,
        termination: ProofTerm,
        post: ProofTerm,
    ) -> ProofTerm:
        """Prove via loop invariant."""
        result = LoopInvariant(
            invariant=invariant,
            init_proof=init,
            preservation=preservation,
            termination=termination,
            post_proof=post,
        )
        self._result = result
        return result

    # ─── Fiber / cohomological tactics ────────────────────────────

    def fiber_split(self, fiber_proofs: Dict[str, ProofTerm]) -> ProofTerm:
        """Decompose into per-fiber obligations."""
        result = FiberDecomposition(fiber_proofs=fiber_proofs)
        self._result = result
        return result

    def glue(
        self,
        local_proofs: List[ProofTerm],
        overlap_proofs: List[ProofTerm],
    ) -> ProofTerm:
        """Čech gluing."""
        result = CechGluing(
            local_proofs=tuple(local_proofs),
            overlap_proofs=tuple(overlap_proofs),
        )
        self._result = result
        return result

    def by_descent(
        self,
        fiber_proofs: Dict[str, ProofTerm],
        overlap_proofs: Optional[Dict[Tuple[str, str], ProofTerm]] = None,
    ) -> ProofTerm:
        """Prove by descent (effective Čech gluing)."""
        result = Descent(
            fiber_proofs=fiber_proofs,
            overlap_proofs=overlap_proofs or {},
        )
        self._result = result
        return result

    # ─── Cut / let ────────────────────────────────────────────────

    def cut(
        self,
        name: str,
        lemma_lhs: OTerm,
        lemma_rhs: OTerm,
        lemma_proof: ProofTerm,
        main_proof: ProofTerm,
    ) -> ProofTerm:
        """Cut rule: prove a lemma, then use it in the main proof."""
        result = Cut(
            lemma_lhs=lemma_lhs,
            lemma_rhs=lemma_rhs,
            lemma_proof=lemma_proof,
            main_proof=main_proof,
            label=name,
        )
        self._result = result
        return result

    def let(
        self,
        name: str,
        lhs: OTerm,
        rhs: OTerm,
        sub_proof: ProofTerm,
        body: ProofTerm,
    ) -> ProofTerm:
        """Let binding in proofs."""
        result = LetProof(
            label=name,
            sub_lhs=lhs,
            sub_rhs=rhs,
            sub_proof=sub_proof,
            body=body,
        )
        self._result = result
        return result

    # ─── Extensionality ───────────────────────────────────────────

    def ext(self, var_name: str, body_proof: ProofTerm) -> ProofTerm:
        """Function extensionality: ∀x. f(x) ≡ g(x) → f ≡ g."""
        result = Ext(var=var_name, body_proof=body_proof)
        self._result = result
        return result

    # ─── Mathlib integration ──────────────────────────────────────

    def mathlib(self, theorem_name: str,
                **instantiation: OTerm) -> ProofTerm:
        """Apply a Mathlib theorem."""
        result = MathLibAxiom(
            theorem_name=theorem_name,
            instantiation=instantiation,
        )
        self._result = result
        return result

    def axiom(self, name: str, direction: str, target: OTerm,
              **bindings: OTerm) -> ProofTerm:
        """Apply a named axiom."""
        result = AxiomApp(
            axiom_name=name,
            direction=direction,
            target=target,
            bindings=bindings,
        )
        self._result = result
        return result

    # ─── Definitional equality ────────────────────────────────────

    def definitional(self) -> ProofTerm:
        """Prove by definitional equality (normalization)."""
        result = Definitional()
        self._result = result
        return result

    # ─── Build / verify ───────────────────────────────────────────

    def build(self) -> ProofTerm:
        """Return the constructed proof term."""
        if self._result is None:
            raise ValueError('No proof constructed — call a proof method first')

        # If we have lemmas, wrap in Cut/LetProof
        proof = self._result
        for name, (l, r, lemma_proof) in reversed(list(self._lemmas.items())):
            if not isinstance(proof, (Cut, LetProof)):
                # Only wrap if the lemma was explicitly proved (not just Assume)
                if not isinstance(lemma_proof, Assume):
                    proof = Cut(
                        lemma_lhs=l,
                        lemma_rhs=r,
                        lemma_proof=lemma_proof,
                        main_proof=proof,
                        label=name,
                    )

        return proof

    def verify(self, lhs: Optional[OTerm] = None,
               rhs: Optional[OTerm] = None,
               ctx: Optional[ProofContext] = None) -> VerificationResult:
        """Build and verify the proof."""
        proof = self.build()
        l = lhs or self.lhs
        r = rhs or self.rhs
        if l is None or r is None:
            raise ValueError('Must provide lhs and rhs to verify')
        return check_proof(proof, l, r, ctx)


# ═══════════════════════════════════════════════════════════════════
# @c4_proof decorator
# ═══════════════════════════════════════════════════════════════════

def c4_proof(
    fn: Optional[Callable] = None,
    *,
    lhs: Optional[OTerm] = None,
    rhs: Optional[OTerm] = None,
) -> Any:
    """Decorator that marks a function as a C⁴ proof builder.

    The decorated function receives a ProofBuilder as its first argument
    and should use it to construct the proof.

    Usage::

        @c4_proof(lhs=FACT_REC, rhs=FACT_ITER)
        def factorial_equiv(pb):
            base = pb.refl(lit(1))
            ih = pb.assume('ih', FACT_REC, FACT_ITER)
            step = pb.trans(
                pb.congr('*', pb.refl(var('n')), ih),
                pb.axiom('fold_spec', 'backward', FACT_ITER),
            )
            pb.by_induction(on='n', base=base, step=step)

    The decorator returns the ProofBuilder (not the function).
    Call ``.build()`` to get the ProofTerm, ``.verify()`` to check it.
    """
    def wrapper(f: Callable) -> ProofBuilder:
        pb = ProofBuilder(lhs=lhs, rhs=rhs)
        f(pb)
        pb._doc = f.__doc__ or ''
        return pb

    if fn is not None:
        return wrapper(fn)
    return wrapper


# ═══════════════════════════════════════════════════════════════════
# Proof script — imperative proof construction
# ═══════════════════════════════════════════════════════════════════

class ProofScript:
    """An imperative proof script that reads like a mathematical argument.

    Usage::

        script = ProofScript(lhs=FACT_REC, rhs=FACT_ITER)
        script.intro('n')
        script.induction('n')
        script.base_case(refl(lit(1)))
        script.inductive_step(
            script.calc(
                (FACT_REC_N1, delta('fact_rec', var('n+1'))),
                (MUL_STEP, cong('*', refl(var('n')), script.ih())),
                (FACT_ITER_N1, axiom_app('fold_spec', 'backward', FACT_ITER)),
            )
        )
        proof = script.qed()
    """

    def __init__(self, lhs: OTerm, rhs: OTerm,
                 ctx: Optional[ProofContext] = None):
        self.lhs = lhs
        self.rhs = rhs
        self.ctx = ctx or ProofContext()
        self._builder = ProofBuilder(lhs=lhs, rhs=rhs)
        self._mode: Optional[str] = None
        self._base: Optional[ProofTerm] = None
        self._step: Optional[ProofTerm] = None
        self._var: Optional[str] = None
        self._cases: Dict[str, ProofTerm] = {}
        self._ih_name: str = 'ih'

    def intro(self, *var_names: str) -> 'ProofScript':
        """Introduce universally quantified variables."""
        for v in var_names:
            self._builder._assumptions[v] = (OVar(v), OVar(v))
        return self

    def induction(self, variable: str, structure: str = 'nat') -> 'ProofScript':
        """Enter induction mode."""
        self._mode = 'induction'
        self._var = variable
        self._structure = structure
        return self

    def base_case(self, proof: ProofTerm) -> 'ProofScript':
        """Provide the base case proof."""
        self._base = proof
        return self

    def inductive_step(self, proof: ProofTerm) -> 'ProofScript':
        """Provide the inductive step proof."""
        self._step = proof
        return self

    def ih(self) -> ProofTerm:
        """Reference the induction hypothesis."""
        return Assume(
            label=self._ih_name,
            assumed_lhs=self.lhs,
            assumed_rhs=self.rhs,
        )

    def case(self, label: str, proof: ProofTerm) -> 'ProofScript':
        """Add a case to case analysis."""
        self._cases[label] = proof
        return self

    def calc(self, *steps: Tuple[OTerm, ProofTerm]) -> ProofTerm:
        """Build a calculational chain."""
        return self._builder.calc_chain(*steps)

    def have(self, name: str, lhs: OTerm, rhs: OTerm,
             by: Optional[ProofTerm] = None) -> ProofTerm:
        """Introduce a lemma."""
        return self._builder.have(name, lhs, rhs, by=by)

    def apply(self, proof: ProofTerm) -> 'ProofScript':
        """Apply a proof directly."""
        self._builder.show(proof)
        return self

    def qed(self) -> ProofTerm:
        """Finalize the proof and return the proof term."""
        if self._mode == 'induction':
            if self._base is None or self._step is None:
                raise ValueError('Induction requires base_case and inductive_step')
            self._builder.by_induction(
                on=self._var or 'n',
                base=self._base,
                step=self._step,
                structure=getattr(self, '_structure', 'nat'),
            )
        elif self._mode == 'cases' and self._cases:
            self._builder.by_cases(
                on=OVar(self._var or '_disc'),
                cases=self._cases,
            )

        return self._builder.build()

    def verify(self) -> VerificationResult:
        """Build and verify the proof."""
        proof = self.qed()
        return check_proof(proof, self.lhs, self.rhs, self.ctx)


# ═══════════════════════════════════════════════════════════════════
# Convenience re-exports for use in DSL proofs
# ═══════════════════════════════════════════════════════════════════

# Re-export term builders so DSL proofs can use them directly
__all__ = [
    'ProofBuilder', 'ProofScript', 'CalcStep',
    'c4_proof',
    # Re-exported term builders
    'var', 'lit', 'op', 'app', 'lam', 'fold_term', 'case', 'fix',
    'seq', 'abstract', 'unknown',
]
