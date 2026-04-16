"""CCTT Proof Tactics — automated proof-term construction.

Tactics are functions that attempt to BUILD proof terms automatically.
They output ProofTerms that can then be verified by the checker.

Key insight: tactics are OPTIONAL automation.  A human can always
write the proof term directly.  Tactics just make it easier.

Tactic Categories
=================
- **Finishing**: refl, assumption — close the goal immediately
- **Structural**: simp, ring, omega — simplify/solve decidable fragments
- **Decomposition**: induction, cases, ext — break goal into subgoals
- **Rewriting**: rewrite, unfold — transform the goal
- **Strategy**: simulation, by_spec — set up complex proof structures
- **Search**: auto — try multiple tactics automatically
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Set, Tuple, Union

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
    subst_in_term, free_vars, terms_equal, normalize_term,
)

from cctt.proof_theory.checker import (
    check_proof, VerificationResult, ProofContext,
)


# ═══════════════════════════════════════════════════════════════════
# Tactic result
# ═══════════════════════════════════════════════════════════════════

@dataclass
class TacticResult:
    """Result of a tactic application.

    If ``proof`` is not None, the tactic succeeded and ``proof`` is
    the constructed proof term.  Use ``check_proof`` to verify it.
    """
    proof: Optional[ProofTerm]
    reason: str
    subgoals: List[Tuple[OTerm, OTerm]] = field(default_factory=list)

    @property
    def success(self) -> bool:
        return self.proof is not None

    def __repr__(self) -> str:
        if self.success:
            return f'TacticResult(✓ {self.reason})'
        return f'TacticResult(✗ {self.reason})'


# ═══════════════════════════════════════════════════════════════════
# Finishing tactics
# ═══════════════════════════════════════════════════════════════════

def try_refl(lhs: OTerm, rhs: OTerm) -> TacticResult:
    """Try to close the goal by reflexivity.

    Succeeds if lhs and rhs are syntactically equal (up to
    normalization).
    """
    if terms_equal(lhs, rhs):
        return TacticResult(Refl(lhs), 'refl')

    n_lhs = normalize_term(lhs)
    n_rhs = normalize_term(rhs)
    if terms_equal(n_lhs, n_rhs):
        return TacticResult(Refl(n_lhs), 'refl (normalized)')

    if lhs.canon() == rhs.canon():
        return TacticResult(Refl(lhs), 'refl (canon)')

    return TacticResult(None, 'not reflexive')


def try_assumption(lhs: OTerm, rhs: OTerm,
                   ctx: ProofContext) -> TacticResult:
    """Try to close the goal using an assumption from the context."""
    for label, (a_lhs, a_rhs) in ctx.assumptions.items():
        if terms_equal(lhs, a_lhs) and terms_equal(rhs, a_rhs):
            return TacticResult(
                Assume(label, a_lhs, a_rhs),
                f'assumption {label}'
            )
        n_lhs = normalize_term(lhs)
        n_rhs = normalize_term(rhs)
        n_a_lhs = normalize_term(a_lhs)
        n_a_rhs = normalize_term(a_rhs)
        if terms_equal(n_lhs, n_a_lhs) and terms_equal(n_rhs, n_a_rhs):
            return TacticResult(
                Assume(label, a_lhs, a_rhs),
                f'assumption {label} (normalized)'
            )
    return TacticResult(None, 'no matching assumption')


def try_definitional(lhs: OTerm, rhs: OTerm) -> TacticResult:
    """Try definitional equality (normalization check)."""
    n_lhs = normalize_term(lhs)
    n_rhs = normalize_term(rhs)
    if terms_equal(n_lhs, n_rhs):
        return TacticResult(Definitional(), 'definitional')
    return TacticResult(None, 'not definitionally equal')


# ═══════════════════════════════════════════════════════════════════
# Simplification tactics
# ═══════════════════════════════════════════════════════════════════

def simp(lhs: OTerm, rhs: OTerm,
         axioms: Optional[List[str]] = None) -> TacticResult:
    """Simplification tactic — apply simplification rules exhaustively.

    Tries to normalize both sides and check equality.  If axioms are
    given, applies them as rewrite rules.
    """
    # Step 1: try reflexivity
    r = try_refl(lhs, rhs)
    if r.success:
        return r

    # Step 2: try arithmetic simplification
    r = try_arith(lhs, rhs)
    if r.success:
        return r

    # Step 3: try normalizing both sides
    n_lhs = normalize_term(lhs)
    n_rhs = normalize_term(rhs)
    if terms_equal(n_lhs, n_rhs):
        return TacticResult(Definitional(), 'simp (normalized)')

    # Step 4: if axioms given, try each one
    if axioms:
        for axiom_name in axioms:
            r = try_axiom_rewrite(lhs, rhs, axiom_name)
            if r.success:
                return r

    return TacticResult(None, 'simp: could not simplify')


def try_arith(lhs: OTerm, rhs: OTerm) -> TacticResult:
    """Try to prove by arithmetic evaluation."""
    val_l = _eval_const(lhs)
    val_r = _eval_const(rhs)
    if val_l is not None and val_r is not None and val_l == val_r:
        return TacticResult(
            ArithmeticSimp(lhs, rhs),
            f'arith ({val_l})'
        )
    return TacticResult(None, 'not a constant arithmetic equality')


def ring(lhs: OTerm, rhs: OTerm) -> TacticResult:
    """Ring tactic — prove equalities in commutative rings.

    Normalizes both sides as polynomials and checks equality.
    Works for expressions involving +, *, - over integers.
    """
    # Convert to polynomial normal form
    poly_l = _to_polynomial(lhs)
    poly_r = _to_polynomial(rhs)

    if poly_l is not None and poly_r is not None and poly_l == poly_r:
        return TacticResult(
            ArithmeticSimp(lhs, rhs),
            f'ring'
        )

    # Fallback: try Z3
    try:
        from cctt.proof_theory.checker import _oterm_to_z3, _HAS_Z3
        if _HAS_Z3:
            from z3 import Solver, Not, unsat
            s = Solver()
            s.set('timeout', 2000)
            z3_l = _oterm_to_z3(lhs)
            z3_r = _oterm_to_z3(rhs)
            if z3_l is not None and z3_r is not None:
                s.add(Not(z3_l == z3_r))
                if s.check() == unsat:
                    return TacticResult(
                        Z3Discharge(
                            f'{lhs.canon()} == {rhs.canon()}',
                            'QF_NIA'
                        ),
                        'ring (z3)'
                    )
    except Exception:
        pass

    return TacticResult(None, 'ring: could not prove')


def omega(lhs: OTerm, rhs: OTerm) -> TacticResult:
    """Omega tactic — prove linear arithmetic goals.

    For quantifier-free linear integer arithmetic (QF_LIA).
    """
    # Try direct evaluation
    r = try_arith(lhs, rhs)
    if r.success:
        return r

    # Try Z3 QF_LIA
    try:
        from cctt.proof_theory.checker import _oterm_to_z3, _HAS_Z3
        if _HAS_Z3:
            from z3 import Solver, Not, unsat
            s = Solver()
            s.set('timeout', 3000)
            z3_l = _oterm_to_z3(lhs)
            z3_r = _oterm_to_z3(rhs)
            if z3_l is not None and z3_r is not None:
                s.add(Not(z3_l == z3_r))
                if s.check() == unsat:
                    return TacticResult(
                        Z3Discharge(
                            f'{lhs.canon()} == {rhs.canon()}',
                            'QF_LIA'
                        ),
                        'omega (z3)'
                    )
    except Exception:
        pass

    return TacticResult(None, 'omega: could not prove')


# ═══════════════════════════════════════════════════════════════════
# Decomposition tactics
# ═══════════════════════════════════════════════════════════════════

def induction(lhs: OTerm, rhs: OTerm, variable: str,
              structure: str = 'nat') -> TacticResult:
    """Set up an induction proof skeleton.

    Returns a proof with placeholder sub-proofs (Assume) that must
    be filled in by the user.

    Parameters
    ----------
    variable : str
        Variable to induct on.
    structure : str
        'nat' for natural number induction,
        'list' for list induction.
    """
    if structure == 'nat':
        base_val = OLit(0)
        base_lhs = subst_in_term(lhs, variable, base_val)
        base_rhs = subst_in_term(rhs, variable, base_val)

        # Check if base case is trivially true
        base_result = try_refl(base_lhs, base_rhs)
        if base_result.success:
            base_proof = base_result.proof
        else:
            base_proof = Assume('base', base_lhs, base_rhs)

        step_proof = Assume(f'IH_{variable}', lhs, rhs)

        proof = NatInduction(
            base_case=base_proof,
            inductive_step=step_proof,
            variable=variable,
        )
        return TacticResult(proof, f'induction on {variable} (nat)',
                           subgoals=[
                               (base_lhs, base_rhs),
                               (subst_in_term(lhs, variable,
                                              OOp('+', (OVar(variable), OLit(1)))),
                                subst_in_term(rhs, variable,
                                              OOp('+', (OVar(variable), OLit(1)))))
                           ])

    elif structure == 'list':
        nil_lhs = subst_in_term(lhs, variable, OSeq(()))
        nil_rhs = subst_in_term(rhs, variable, OSeq(()))

        nil_result = try_refl(nil_lhs, nil_rhs)
        if nil_result.success:
            nil_proof = nil_result.proof
        else:
            nil_proof = Assume('nil', nil_lhs, nil_rhs)

        cons_proof = Assume(f'IH_{variable}', lhs, rhs)

        proof = ListInduction(
            nil_case=nil_proof,
            cons_case=cons_proof,
            variable=variable,
        )
        return TacticResult(proof, f'induction on {variable} (list)')

    return TacticResult(None, f'unknown induction structure: {structure}')


def cases(lhs: OTerm, rhs: OTerm,
          discriminant: OTerm,
          case_labels: List[str]) -> TacticResult:
    """Set up a case-split proof skeleton."""
    case_proofs = {}
    for label in case_labels:
        case_proofs[label] = Assume(f'case_{label}', lhs, rhs)

    proof = CasesSplit(discriminant, case_proofs)
    return TacticResult(proof, f'cases on {discriminant.canon()[:30]}')


def extensionality(lhs: OTerm, rhs: OTerm,
                   var_name: str = 'x') -> TacticResult:
    """Set up an extensionality proof skeleton."""
    body_proof = Assume(f'ext_{var_name}', lhs, rhs)
    proof = Ext(var_name, body_proof)
    return TacticResult(proof, f'ext ∀{var_name}')


# ═══════════════════════════════════════════════════════════════════
# Rewriting tactics
# ═══════════════════════════════════════════════════════════════════

def unfold(lhs: OTerm, rhs: OTerm, func_name: str,
           ctx: Optional[ProofContext] = None) -> TacticResult:
    """Unfold a function definition.

    If lhs is f(args), produces Delta(f, args) proving
    f(args) ≡ body[params:=args].
    """
    if isinstance(lhs, OOp) and lhs.name == func_name:
        proof = Delta(func_name, tuple(lhs.args))
        return TacticResult(proof, f'unfold {func_name}')

    if isinstance(rhs, OOp) and rhs.name == func_name:
        proof = Sym(Delta(func_name, tuple(rhs.args)))
        return TacticResult(proof, f'fold {func_name}')

    return TacticResult(None, f'unfold: {func_name} not found in goal')


def rewrite_with(lhs: OTerm, rhs: OTerm,
                 equation: ProofTerm,
                 direction: str = 'forward') -> TacticResult:
    """Apply a proven equation as a rewrite rule."""
    if direction == 'forward':
        proof = Rewrite(equation, in_lhs=True)
    else:
        proof = Rewrite(Sym(equation), in_lhs=True)
    return TacticResult(proof, f'rewrite ({direction})')


def try_axiom_rewrite(lhs: OTerm, rhs: OTerm,
                      axiom_name: str) -> TacticResult:
    """Try to apply a CCTT axiom as a rewrite."""
    # Try forward
    proof_fwd = AxiomApp(axiom_name, 'forward', lhs)
    r = check_proof(proof_fwd, lhs, rhs)
    if r.valid:
        return TacticResult(proof_fwd, f'axiom {axiom_name} →')

    # Try backward
    proof_bwd = AxiomApp(axiom_name, 'backward', rhs)
    r = check_proof(proof_bwd, lhs, rhs)
    if r.valid:
        return TacticResult(proof_bwd, f'axiom {axiom_name} ←')

    return TacticResult(None, f'axiom {axiom_name} not applicable')


# ═══════════════════════════════════════════════════════════════════
# Strategy tactics
# ═══════════════════════════════════════════════════════════════════

def by_simulation(lhs: OTerm, rhs: OTerm,
                  relation: str,
                  init_proof: Optional[ProofTerm] = None,
                  step_proof: Optional[ProofTerm] = None,
                  output_proof: Optional[ProofTerm] = None) -> TacticResult:
    """Set up a simulation proof.

    Provides defaults (Assume) for any sub-proof not given.
    """
    ip = init_proof or Assume('sim_init', lhs, rhs)
    sp = step_proof or Assume('sim_step', lhs, rhs)
    op = output_proof or Assume('sim_output', lhs, rhs)

    proof = Simulation(relation, ip, sp, op)
    return TacticResult(proof, f'simulation[R={relation[:30]}]')


def by_spec(lhs: OTerm, rhs: OTerm,
            spec_name: str,
            f_proof: Optional[ProofTerm] = None,
            g_proof: Optional[ProofTerm] = None) -> TacticResult:
    """Prove equivalence by showing both refine the same spec.

    Provides defaults (Assume) for any sub-proof not given.
    """
    fp = f_proof or Assume('f_refines', lhs, OAbstract(spec_name, ()))
    gp = g_proof or Assume('g_refines', rhs, OAbstract(spec_name, ()))

    proof = AbstractionRefinement(spec_name, fp, gp)
    return TacticResult(proof, f'by_spec[{spec_name}]')


def by_loop_invariant(lhs: OTerm, rhs: OTerm,
                      invariant: str,
                      init_proof: Optional[ProofTerm] = None,
                      preservation: Optional[ProofTerm] = None,
                      termination: Optional[ProofTerm] = None,
                      post_proof: Optional[ProofTerm] = None) -> TacticResult:
    """Set up a loop invariant proof."""
    ip = init_proof or Assume('loop_init', lhs, rhs)
    pp = preservation or Assume('loop_pres', lhs, rhs)
    tp = termination or Assume('loop_term', lhs, rhs)
    posp = post_proof or Assume('loop_post', lhs, rhs)

    proof = LoopInvariant(invariant, ip, pp, tp, posp)
    return TacticResult(proof, f'loop_invariant[I={invariant[:30]}]')


def by_comm_diagram(lhs: OTerm, rhs: OTerm,
                    morphism_proof: Optional[ProofTerm] = None,
                    iso_proof: Optional[ProofTerm] = None) -> TacticResult:
    """Set up a commutative diagram proof."""
    mp = morphism_proof or Assume('diagram_comm', lhs, rhs)
    ip = iso_proof or Assume('diagram_iso', lhs, rhs)

    proof = CommDiagram(mp, ip)
    return TacticResult(proof, 'comm_diagram')


def by_fibers(lhs: OTerm, rhs: OTerm,
              fiber_proofs: Dict[str, ProofTerm]) -> TacticResult:
    """Prove by decomposing into fibers."""
    if not fiber_proofs:
        return TacticResult(None, 'no fiber proofs')
    proof = FiberDecomposition(fiber_proofs)
    return TacticResult(proof, f'fibers ({len(fiber_proofs)})')


# ═══════════════════════════════════════════════════════════════════
# Auto tactic — try everything
# ═══════════════════════════════════════════════════════════════════

def auto(lhs: OTerm, rhs: OTerm,
         ctx: Optional[ProofContext] = None,
         depth: int = 3) -> TacticResult:
    """Automatic proof search.

    Tries tactics in order of increasing complexity:
    1. refl (identical terms)
    2. definitional (normalize and compare)
    3. arithmetic (constant folding / Z3)
    4. assumption (from context)
    5. congruence (same head, prove args)
    6. axiom search (try known axioms)

    ``depth`` controls how deep the search goes (to prevent blowup).
    """
    if depth <= 0:
        return TacticResult(None, 'auto: depth exhausted')

    if ctx is None:
        ctx = ProofContext()

    # 1. Reflexivity
    r = try_refl(lhs, rhs)
    if r.success:
        return r

    # 2. Definitional equality
    r = try_definitional(lhs, rhs)
    if r.success:
        return r

    # 3. Arithmetic
    r = try_arith(lhs, rhs)
    if r.success:
        return r

    # 4. Assumption
    r = try_assumption(lhs, rhs, ctx)
    if r.success:
        return r

    # 5. Congruence
    if (isinstance(lhs, OOp) and isinstance(rhs, OOp) and
            lhs.name == rhs.name and len(lhs.args) == len(rhs.args)):
        arg_proofs = []
        all_ok = True
        for la, ra in zip(lhs.args, rhs.args):
            ar = auto(la, ra, ctx, depth - 1)
            if ar.success:
                arg_proofs.append(ar.proof)
            else:
                all_ok = False
                break
        if all_ok and arg_proofs:
            return TacticResult(
                Cong(lhs.name, tuple(arg_proofs)),
                f'cong[{lhs.name}]'
            )

    # 6. Symmetry + auto
    if depth >= 2:
        r = auto(rhs, lhs, ctx, depth - 1)
        if r.success:
            return TacticResult(Sym(r.proof), f'sym + {r.reason}')

    return TacticResult(None, 'auto: no proof found')


# ═══════════════════════════════════════════════════════════════════
# Polynomial normalization for ring tactic
# ═══════════════════════════════════════════════════════════════════

def _to_polynomial(term: OTerm) -> Optional[Dict[Tuple[Tuple[str, int], ...], int]]:
    """Convert an OTerm to a polynomial representation.

    A polynomial is represented as a dict mapping monomial → coefficient.
    A monomial is a sorted tuple of (variable_name, exponent) pairs.

    Returns None if the term can't be interpreted as a polynomial.
    """
    if isinstance(term, OLit):
        if isinstance(term.value, (int, float)):
            return {(): int(term.value)}
        return None

    if isinstance(term, OVar):
        return {((term.name, 1),): 1}

    if isinstance(term, OOp):
        if term.name == '+' and len(term.args) == 2:
            p1 = _to_polynomial(term.args[0])
            p2 = _to_polynomial(term.args[1])
            if p1 is None or p2 is None:
                return None
            return _poly_add(p1, p2)

        if term.name == '-' and len(term.args) == 2:
            p1 = _to_polynomial(term.args[0])
            p2 = _to_polynomial(term.args[1])
            if p1 is None or p2 is None:
                return None
            return _poly_sub(p1, p2)

        if term.name == '*' and len(term.args) == 2:
            p1 = _to_polynomial(term.args[0])
            p2 = _to_polynomial(term.args[1])
            if p1 is None or p2 is None:
                return None
            return _poly_mul(p1, p2)

    return None


Monomial = Tuple[Tuple[str, int], ...]
Polynomial = Dict[Monomial, int]


def _poly_add(p1: Polynomial, p2: Polynomial) -> Polynomial:
    result = dict(p1)
    for mono, coeff in p2.items():
        result[mono] = result.get(mono, 0) + coeff
    return {k: v for k, v in result.items() if v != 0}


def _poly_sub(p1: Polynomial, p2: Polynomial) -> Polynomial:
    result = dict(p1)
    for mono, coeff in p2.items():
        result[mono] = result.get(mono, 0) - coeff
    return {k: v for k, v in result.items() if v != 0}


def _poly_mul(p1: Polynomial, p2: Polynomial) -> Polynomial:
    result: Polynomial = {}
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            m = _mono_mul(m1, m2)
            result[m] = result.get(m, 0) + c1 * c2
    return {k: v for k, v in result.items() if v != 0}


def _mono_mul(m1: Monomial, m2: Monomial) -> Monomial:
    vars_dict: Dict[str, int] = {}
    for name, exp in m1:
        vars_dict[name] = vars_dict.get(name, 0) + exp
    for name, exp in m2:
        vars_dict[name] = vars_dict.get(name, 0) + exp
    return tuple(sorted(vars_dict.items()))


def _eval_const(term: OTerm) -> Optional[Any]:
    """Evaluate a constant OTerm."""
    if isinstance(term, OLit):
        return term.value
    if isinstance(term, OOp) and len(term.args) == 2:
        l = _eval_const(term.args[0])
        r = _eval_const(term.args[1])
        if l is not None and r is not None:
            try:
                ops = {'+': lambda a, b: a + b, '-': lambda a, b: a - b,
                       '*': lambda a, b: a * b}
                if term.name in ops:
                    return ops[term.name](l, r)
            except Exception:
                pass
    return None


# ═══════════════════════════════════════════════════════════════════
# Tactic combinators
# ═══════════════════════════════════════════════════════════════════

def then(t1: TacticResult, t2_fn: Callable[[], TacticResult]) -> TacticResult:
    """Chain tactics: try t1, if it fails try t2."""
    if t1.success:
        return t1
    return t2_fn()


def orelse(*tactics: TacticResult) -> TacticResult:
    """Try multiple tactics, return first success."""
    for t in tactics:
        if t.success:
            return t
    return TacticResult(None, 'all alternatives failed')


def repeat(tactic_fn: Callable[[OTerm, OTerm], TacticResult],
           lhs: OTerm, rhs: OTerm,
           max_iters: int = 100) -> TacticResult:
    """Repeat a tactic until it fails or the goal is solved."""
    current_lhs = lhs
    steps: List[ProofTerm] = []
    intermediates: List[OTerm] = [lhs]

    for _ in range(max_iters):
        if terms_equal(current_lhs, rhs):
            break
        r = tactic_fn(current_lhs, rhs)
        if not r.success:
            break
        steps.append(r.proof)
        # Try to infer the new lhs from the proof
        # For now, break after first application
        break

    if not steps:
        return TacticResult(None, 'repeat: no progress')

    if len(steps) == 1:
        return TacticResult(steps[0], 'repeat (1 step)')

    intermediates.append(rhs)
    return TacticResult(
        RewriteChain(tuple(steps), tuple(intermediates)),
        f'repeat ({len(steps)} steps)'
    )


# ═══════════════════════════════════════════════════════════════════
# Proof construction helpers
# ═══════════════════════════════════════════════════════════════════

def build_chain(steps: List[Tuple[OTerm, ProofTerm]],
                final: OTerm) -> ProofTerm:
    """Build a RewriteChain from a list of (intermediate, proof) pairs.

    steps = [(a₁, p₁), (a₂, p₂), ...]
    where p₁ : a₀ ≡ a₁, p₂ : a₁ ≡ a₂, etc.
    final is the last term.
    """
    if not steps:
        return Refl(final)

    proofs = [p for _, p in steps]
    intermediates = [steps[0][0]]  # Will be filled during construction

    # Build intermediates list
    terms_list = [steps[0][0]]
    for term, _ in steps:
        terms_list.append(term)
    terms_list.append(final)

    if len(proofs) == 1:
        return proofs[0]

    return RewriteChain(tuple(proofs), tuple(terms_list))


def build_trans_chain(proofs: List[ProofTerm],
                      intermediates: List[OTerm]) -> ProofTerm:
    """Build a chain of Trans from a list of proofs.

    proofs[i] : intermediates[i] ≡ intermediates[i+1]
    """
    if not proofs:
        return Refl(intermediates[0] if intermediates else OLit(None))

    if len(proofs) == 1:
        return proofs[0]

    # Right-associate the Trans chain
    result = proofs[-1]
    for i in range(len(proofs) - 2, -1, -1):
        mid = intermediates[i + 1] if i + 1 < len(intermediates) else None
        result = Trans(proofs[i], result, middle=mid)

    return result


# ═══════════════════════════════════════════════════════════════════
# Convenience: verify_auto
# ═══════════════════════════════════════════════════════════════════

def verify_auto(lhs: OTerm, rhs: OTerm,
                ctx: Optional[ProofContext] = None) -> VerificationResult:
    """Try to automatically prove and verify lhs ≡ rhs.

    Combines auto tactic with the checker.  Returns a VerificationResult.
    """
    r = auto(lhs, rhs, ctx)
    if not r.success:
        return VerificationResult(False, f'auto failed: {r.reason}')

    return check_proof(r.proof, lhs, rhs, ctx)


# ═══════════════════════════════════════════════════════════════════
# C⁴ calculus tactics
# ═══════════════════════════════════════════════════════════════════

def by_descent(lhs: OTerm, rhs: OTerm,
               fiber_proofs: Dict[str, ProofTerm],
               overlap_proofs: Optional[Dict[Tuple[str, str], ProofTerm]] = None
               ) -> TacticResult:
    """Prove by cohomological descent: verify on fibers, glue globally.

    Constructs a Descent proof term from per-fiber proofs and
    optional overlap compatibility witnesses.
    """
    if not fiber_proofs:
        return TacticResult(None, 'by_descent: no fiber proofs')
    proof = Descent(fiber_proofs, overlap_proofs or {})
    return TacticResult(proof,
                        f'descent ({len(fiber_proofs)} fibers)')


def by_mathlib(lhs: OTerm, rhs: OTerm,
               theorem_name: str,
               instantiation: Optional[Dict[str, OTerm]] = None
               ) -> TacticResult:
    """Apply a Mathlib theorem as a proof step.

    Looks up the theorem by name and constructs a MathLibAxiom
    proof term.
    """
    proof = MathLibAxiom(theorem_name, instantiation or {})
    return TacticResult(proof, f'mathlib[{theorem_name}]')


def by_fiber(lhs: OTerm, rhs: OTerm,
             fiber_name: str,
             inner_proof: ProofTerm) -> TacticResult:
    """Restrict a proof to a specific fiber."""
    proof = FiberRestrict(fiber_name, inner_proof)
    return TacticResult(proof, f'fiber_restrict[{fiber_name}]')


def by_path_compose(lhs: OTerm, rhs: OTerm,
                    left: ProofTerm,
                    right: ProofTerm,
                    middle: Optional[OTerm] = None) -> TacticResult:
    """Compose two path proofs (cubical path composition)."""
    proof = PathCompose(left, right, middle)
    return TacticResult(proof, 'path_compose')
