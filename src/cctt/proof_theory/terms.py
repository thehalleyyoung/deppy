"""CCTT Proof Terms — the language of equivalence proofs.

Every proof term is a witness that two OTerms are equal.  The proof checker
(checker.py) mechanically verifies these witnesses — no sampling, no oracles.

Proof terms form a type-theoretic proof language:

    Γ ⊢ p : a ≡ b

where Γ is a context of assumptions and definitions, a and b are OTerms,
and p is the explicit evidence.

Design Principles
=================
1. **Soundness over completeness** — the checker never accepts invalid proofs.
2. **Explicit evidence** — every step is traceable; the proof term IS the
   certificate.
3. **Compositionality** — proofs compose via Trans, Cong, etc.
4. **Human-writable** — the language is usable by humans and LLMs.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union
import json

# We import OTerm types from denotation so proofs reference real terms.
from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)


# ═══════════════════════════════════════════════════════════════════
# Base class
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class ProofTerm:
    """Base class for all proof terms.

    A ProofTerm is a witness that two OTerms are equal.  The proof
    checker verifies that the witness is valid — the checker is purely
    structural, deterministic, and terminating.

    Every subclass carries enough information for the checker to
    *mechanically* verify the proof step without any external oracle.
    """

    def tag(self) -> str:
        """Short tag for serialization."""
        return type(self).__name__

    def children(self) -> List['ProofTerm']:
        """All sub-proofs (for recursion depth tracking)."""
        return []

    def depth(self) -> int:
        """Proof depth (max nesting)."""
        kids = self.children()
        if not kids:
            return 1
        return 1 + max(k.depth() for k in kids)

    def size(self) -> int:
        """Total number of proof nodes."""
        return 1 + sum(k.size() for k in self.children())

    def pretty(self, indent: int = 0) -> str:
        """Human-readable proof rendering."""
        pad = '  ' * indent
        return f'{pad}{self.tag()}'


# ═══════════════════════════════════════════════════════════════════
# Structural rules — the core of identity types
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Refl(ProofTerm):
    """Reflexivity: a ≡ a.

    The simplest proof — a term is equal to itself.
    Checker verifies: lhs.canon() == rhs.canon() == term.canon()
    """
    term: OTerm

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        return f'{pad}refl({self.term.canon()})'

    def children(self) -> List[ProofTerm]:
        return []


@dataclass(frozen=True)
class Sym(ProofTerm):
    """Symmetry: if p : a ≡ b then sym(p) : b ≡ a.

    Reverses the direction of an equality proof.
    """
    proof: ProofTerm

    def children(self) -> List[ProofTerm]:
        return [self.proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        sub = self.proof.pretty(indent + 1)
        return f'{pad}sym(\n{sub}\n{pad})'


@dataclass(frozen=True)
class Trans(ProofTerm):
    """Transitivity: if p : a ≡ b and q : b ≡ c then trans(p, q) : a ≡ c.

    The workhorse combinator — chains equalities through intermediate terms.
    The ``middle`` field records the intermediate term b.
    """
    left: ProofTerm
    right: ProofTerm
    middle: Optional[OTerm] = None  # the intermediate term

    def children(self) -> List[ProofTerm]:
        return [self.left, self.right]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        l = self.left.pretty(indent + 1)
        r = self.right.pretty(indent + 1)
        mid = f' via {self.middle.canon()}' if self.middle else ''
        return f'{pad}trans{mid}(\n{l},\n{r}\n{pad})'


@dataclass(frozen=True)
class Cong(ProofTerm):
    """Congruence: if p_i : a_i ≡ b_i then f(a_1,...) ≡ f(b_1,...).

    Lifts pointwise equalities through an operation.
    """
    func: str  # operation name (matches OOp.name)
    arg_proofs: Tuple[ProofTerm, ...]  # one proof per argument position

    def children(self) -> List[ProofTerm]:
        return list(self.arg_proofs)

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        args = ',\n'.join(p.pretty(indent + 1) for p in self.arg_proofs)
        return f'{pad}cong[{self.func}](\n{args}\n{pad})'


# ═══════════════════════════════════════════════════════════════════
# Computation rules — β, η, δ
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Beta(ProofTerm):
    """β-reduction: (λx.body)(arg) ≡ body[x := arg].

    Checker verifies: lhs is an application of lam to arg, and rhs
    is the substitution result.
    """
    lam: OTerm   # must be OLam
    arg: OTerm   # the argument being applied

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        return f'{pad}β({self.lam.canon()}, {self.arg.canon()})'


@dataclass(frozen=True)
class Delta(ProofTerm):
    """δ-reduction: unfold a named definition.

    f(args) ≡ body_of_f[params := args]

    The checker looks up the function definition in the context and
    verifies the substitution.
    """
    func_name: str
    args: Tuple[OTerm, ...]
    body: Optional[OTerm] = None  # if provided, checker verifies body matches definition

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        arg_strs = ', '.join(a.canon() for a in self.args)
        return f'{pad}δ({self.func_name}({arg_strs}))'


@dataclass(frozen=True)
class Eta(ProofTerm):
    """η-reduction: λx.f(x) ≡ f (when x not free in f).

    Checker verifies: the term is an OLam whose body is an application
    of a function to exactly the bound variable.
    """
    term: OTerm  # the function f

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        return f'{pad}η({self.term.canon()})'


# ═══════════════════════════════════════════════════════════════════
# Induction principles
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class NatInduction(ProofTerm):
    """Natural number induction: prove ∀n. P(n).

    Structure:
        base_case   : proof of P(0)
        ind_step    : proof of ∀k. P(k) → P(k+1)
        variable    : the induction variable name

    The property P is implicitly the equality being proved:
    P(n) ≡ (f(n) = g(n))

    The checker verifies:
    1. base_case proves f(0) = g(0)
    2. ind_step, assuming f(k) = g(k), proves f(k+1) = g(k+1)
    """
    base_case: ProofTerm
    inductive_step: ProofTerm
    variable: str
    base_value: OTerm = field(default_factory=lambda: OLit(0))

    def children(self) -> List[ProofTerm]:
        return [self.base_case, self.inductive_step]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        base = self.base_case.pretty(indent + 1)
        step = self.inductive_step.pretty(indent + 1)
        return (f'{pad}nat_induction on {self.variable}:\n'
                f'{pad}  base:\n{base}\n'
                f'{pad}  step:\n{step}')


@dataclass(frozen=True)
class ListInduction(ProofTerm):
    """List induction: prove ∀xs. P(xs).

    Structure:
        nil_case  : proof of P([])
        cons_case : proof of ∀x,xs. P(xs) → P(x::xs)
        variable  : the induction variable name

    Checker verifies the base and step structurally.
    """
    nil_case: ProofTerm
    cons_case: ProofTerm
    variable: str
    elem_var: str = 'x'
    tail_var: str = 'xs'

    def children(self) -> List[ProofTerm]:
        return [self.nil_case, self.cons_case]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        nil = self.nil_case.pretty(indent + 1)
        cons = self.cons_case.pretty(indent + 1)
        return (f'{pad}list_induction on {self.variable}:\n'
                f'{pad}  nil:\n{nil}\n'
                f'{pad}  cons({self.elem_var}::{self.tail_var}):\n{cons}')


@dataclass(frozen=True)
class WellFoundedInduction(ProofTerm):
    """Well-founded induction on a measure function.

    Structure:
        measure : name of the measure function (must map to ℕ)
        step    : proof that (∀y. μ(y) < μ(x) → P(y)) → P(x)

    The measure provides the well-founded ordering; the checker
    verifies the step assumes the IH for all strictly smaller elements.
    """
    measure: str
    step: ProofTerm
    measure_type: str = 'nat'  # 'nat' or 'lexicographic'

    def children(self) -> List[ProofTerm]:
        return [self.step]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        s = self.step.pretty(indent + 1)
        return f'{pad}wf_induction[μ={self.measure}]:\n{s}'


# ═══════════════════════════════════════════════════════════════════
# Axiom invocations — referencing the CCTT axiom system
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class AxiomApp(ProofTerm):
    """Apply a named CCTT axiom as a rewrite step.

    The checker:
    1. Looks up the axiom by name in the axiom registry
    2. Applies it to the target with the given bindings
    3. Verifies the rewrite produces the expected result

    direction: 'forward' applies the axiom left→right;
               'backward' applies right→left.
    """
    axiom_name: str
    direction: str  # 'forward' or 'backward'
    target: OTerm   # the subterm being rewritten
    bindings: Dict[str, OTerm] = field(default_factory=dict)

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        d = '→' if self.direction == 'forward' else '←'
        return f'{pad}axiom[{self.axiom_name} {d}]({self.target.canon()})'


@dataclass(frozen=True)
class MathlibTheorem(ProofTerm):
    """Invoke a machine-checked Lean/Mathlib theorem as an axiom.

    The checker trusts Lean-verified theorems as axioms. The
    ``theorem_name`` must be a fully qualified Lean name known
    to the system.
    """
    theorem_name: str
    instantiation: Dict[str, OTerm] = field(default_factory=dict)

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        binds = ', '.join(f'{k}={v.canon()}' for k, v in self.instantiation.items())
        return f'{pad}mathlib[{self.theorem_name}]({binds})'


# ═══════════════════════════════════════════════════════════════════
# Loop and recursion reasoning
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class LoopInvariant(ProofTerm):
    """Prove a loop correct by establishing a loop invariant.

    Structure (Hoare-style):
        I(init) ∧
        (∀s. I(s) ∧ guard(s) → I(step(s))) ∧
        (∀s. I(s) ∧ ¬guard(s) → post(s))

    Fields:
        invariant    : the invariant predicate (as parseable string)
        init_proof   : proof that I holds on the initial state
        preservation : proof that each step preserves I
        termination  : proof that a measure decreases each step
        post_proof   : proof that I ∧ ¬guard → postcondition
    """
    invariant: str
    init_proof: ProofTerm
    preservation: ProofTerm
    termination: ProofTerm
    post_proof: ProofTerm

    def children(self) -> List[ProofTerm]:
        return [self.init_proof, self.preservation,
                self.termination, self.post_proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [
            f'{pad}loop_invariant[I = {self.invariant}]:',
            f'{pad}  init:',
            self.init_proof.pretty(indent + 2),
            f'{pad}  preserve:',
            self.preservation.pretty(indent + 2),
            f'{pad}  terminate:',
            self.termination.pretty(indent + 2),
            f'{pad}  post:',
            self.post_proof.pretty(indent + 2),
        ]
        return '\n'.join(parts)


@dataclass(frozen=True)
class Simulation(ProofTerm):
    """Prove two programs equivalent by simulation relation (bisimulation).

    A simulation relation R relates states of program f to states of
    program g such that:
        1. Initial states are related: R(s0_f, s0_g)
        2. Steps preserve the relation: R(sf,sg) → R(step_f(sf), step_g(sg))
        3. Related final states produce the same output

    This is the most powerful technique for proving algorithmic equivalences
    like DP-vs-recursive, BFS-vs-DFS, etc.
    """
    relation: str              # simulation relation description
    init_proof: ProofTerm      # proof that initial states are related
    step_proof: ProofTerm      # proof that steps preserve relation
    output_proof: ProofTerm    # proof that related final states ≡ same output

    def children(self) -> List[ProofTerm]:
        return [self.init_proof, self.step_proof, self.output_proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [
            f'{pad}simulation[R = {self.relation}]:',
            f'{pad}  init:',
            self.init_proof.pretty(indent + 2),
            f'{pad}  step:',
            self.step_proof.pretty(indent + 2),
            f'{pad}  output:',
            self.output_proof.pretty(indent + 2),
        ]
        return '\n'.join(parts)


@dataclass(frozen=True)
class AbstractionRefinement(ProofTerm):
    """Prove equivalence by showing both programs refine the same spec.

    If abs(f(x)) = spec(x) and abs(g(x)) = spec(x), then f ≡ g
    (up to the abstraction function).

    Useful for: merge sort ≡ quick sort (both refine "sort"),
    BFS ≡ Union-Find (both compute connected components), etc.
    """
    spec_name: str              # abstract specification name
    abstraction_f: ProofTerm    # proof that f implements spec
    abstraction_g: ProofTerm    # proof that g implements spec
    abstraction_func: Optional[str] = None  # optional: the abstraction function

    def children(self) -> List[ProofTerm]:
        return [self.abstraction_f, self.abstraction_g]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        af = self.abstraction_f.pretty(indent + 1)
        ag = self.abstraction_g.pretty(indent + 1)
        return (f'{pad}abstraction_refinement[spec={self.spec_name}]:\n'
                f'{pad}  f refines spec:\n{af}\n'
                f'{pad}  g refines spec:\n{ag}')


# ═══════════════════════════════════════════════════════════════════
# Algebraic / categorical reasoning
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class CommDiagram(ProofTerm):
    """Prove equivalence via commutative diagram.

    If h∘f = g∘k and h,k are bijections, then f ≡ g (up to encoding).
    This handles representation-change arguments (bitmask ↔ recursion tree,
    adjacency list ↔ matrix, etc.)
    """
    morphism_left: ProofTerm    # proof of h∘f = g∘k
    iso_proof: ProofTerm        # proof that h, k are isomorphisms

    def children(self) -> List[ProofTerm]:
        return [self.morphism_left, self.iso_proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        ml = self.morphism_left.pretty(indent + 1)
        ip = self.iso_proof.pretty(indent + 1)
        return (f'{pad}comm_diagram:\n'
                f'{pad}  commutativity:\n{ml}\n'
                f'{pad}  isomorphism:\n{ip}')


@dataclass(frozen=True)
class FunctorMap(ProofTerm):
    """Functoriality: F(f∘g) = F(f)∘F(g).

    Used for proving map/filter/fold fusion laws.
    """
    functor: str
    compose_proof: ProofTerm

    def children(self) -> List[ProofTerm]:
        return [self.compose_proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        cp = self.compose_proof.pretty(indent + 1)
        return f'{pad}functor[{self.functor}]:\n{cp}'


# ═══════════════════════════════════════════════════════════════════
# Z3 discharge — decidable subgoals
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Z3Discharge(ProofTerm):
    """Discharge a decidable subgoal to Z3.

    For quantifier-free formulas in decidable fragments, Z3 can provide
    a definitive answer.  If Z3 times out, the proof is **REJECTED** —
    we never accept "probably true".

    Supported fragments:
        QF_LIA  — quantifier-free linear integer arithmetic
        QF_NIA  — quantifier-free nonlinear integer arithmetic
        QF_LRA  — quantifier-free linear real arithmetic
        QF_S    — quantifier-free strings
        QF_BV   — quantifier-free bitvectors
        QF_UFLIA — QF_LIA + uninterpreted functions
    """
    formula: str       # SMT-LIB formula or Python-Z3 expression
    fragment: str      # e.g. 'QF_LIA'
    timeout_ms: int = 5000
    variables: Dict[str, str] = field(default_factory=dict)  # name → sort

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        return f'{pad}z3[{self.fragment}]({self.formula[:60]}...)'


# ═══════════════════════════════════════════════════════════════════
# Fiber-wise / cohomological reasoning
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class FiberDecomposition(ProofTerm):
    """Prove equivalence by proving it on each fiber separately.

    (∀τ ∈ fibers. f|_τ ≡ g|_τ) → f ≡ g

    This is the sheaf condition: a global section is determined by
    its restrictions to an open cover.
    """
    fiber_proofs: Dict[str, ProofTerm]  # fiber_name → proof

    def children(self) -> List[ProofTerm]:
        return list(self.fiber_proofs.values())

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}fiber_decomposition:']
        for fiber, proof in self.fiber_proofs.items():
            parts.append(f'{pad}  fiber[{fiber}]:')
            parts.append(proof.pretty(indent + 2))
        return '\n'.join(parts)


@dataclass(frozen=True)
class CechGluing(ProofTerm):
    """Glue local equivalences into a global one via Čech cohomology.

    Given local proofs on an open cover and compatibility proofs on
    overlaps, conclude global equivalence provided H¹ = 0.
    """
    local_proofs: Tuple[ProofTerm, ...]
    overlap_proofs: Tuple[ProofTerm, ...]

    def children(self) -> List[ProofTerm]:
        return list(self.local_proofs) + list(self.overlap_proofs)

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}cech_gluing:']
        for i, p in enumerate(self.local_proofs):
            parts.append(f'{pad}  local[{i}]:')
            parts.append(p.pretty(indent + 2))
        for i, p in enumerate(self.overlap_proofs):
            parts.append(f'{pad}  overlap[{i}]:')
            parts.append(p.pretty(indent + 2))
        return '\n'.join(parts)


# ═══════════════════════════════════════════════════════════════════
# Additional structural combinators
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Assume(ProofTerm):
    """Assume a hypothesis (creates a proof obligation).

    Used inside induction steps and simulation proofs where we have
    an induction hypothesis or simulation invariant.
    ``label`` names the assumption for reference; the checker tracks
    which assumptions are in scope.
    """
    label: str
    assumed_lhs: OTerm
    assumed_rhs: OTerm

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        return (f'{pad}assume[{self.label}]: '
                f'{self.assumed_lhs.canon()} ≡ {self.assumed_rhs.canon()}')


@dataclass(frozen=True)
class Cut(ProofTerm):
    """Introduce a lemma and use it.

    cut(lemma_proof, main_proof) where lemma_proof proves some A ≡ B,
    and main_proof may reference the lemma.
    """
    lemma_lhs: OTerm
    lemma_rhs: OTerm
    lemma_proof: ProofTerm
    main_proof: ProofTerm
    label: str = 'lemma'

    def children(self) -> List[ProofTerm]:
        return [self.lemma_proof, self.main_proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        lp = self.lemma_proof.pretty(indent + 1)
        mp = self.main_proof.pretty(indent + 1)
        return (f'{pad}cut[{self.label}: {self.lemma_lhs.canon()} ≡ {self.lemma_rhs.canon()}]:\n'
                f'{pad}  lemma:\n{lp}\n'
                f'{pad}  then:\n{mp}')


@dataclass(frozen=True)
class LetProof(ProofTerm):
    """Bind an intermediate proof for reuse.

    let label = sub_proof in body_proof
    """
    label: str
    sub_lhs: OTerm
    sub_rhs: OTerm
    sub_proof: ProofTerm
    body: ProofTerm

    def children(self) -> List[ProofTerm]:
        return [self.sub_proof, self.body]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        sp = self.sub_proof.pretty(indent + 1)
        bp = self.body.pretty(indent + 1)
        return (f'{pad}let {self.label} = (\n{sp}\n{pad}) in\n{bp}')


@dataclass(frozen=True)
class CasesSplit(ProofTerm):
    """Prove by case analysis on a discriminant.

    For each possible value of the discriminant, provide a proof
    that lhs = rhs.  The cases must be exhaustive.
    """
    discriminant: OTerm
    cases: Dict[str, ProofTerm]  # case_label → proof for that case

    def children(self) -> List[ProofTerm]:
        return list(self.cases.values())

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}cases on {self.discriminant.canon()}:']
        for label, proof in self.cases.items():
            parts.append(f'{pad}  case {label}:')
            parts.append(proof.pretty(indent + 2))
        return '\n'.join(parts)


@dataclass(frozen=True)
class Ext(ProofTerm):
    """Extensionality: f ≡ g if ∀x. f(x) ≡ g(x).

    Proves function equality from pointwise equality.
    ``var`` is the universally quantified variable name.
    ``body_proof`` proves f(var) ≡ g(var).
    """
    var: str
    body_proof: ProofTerm

    def children(self) -> List[ProofTerm]:
        return [self.body_proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        bp = self.body_proof.pretty(indent + 1)
        return f'{pad}ext ∀{self.var}.\n{bp}'


@dataclass(frozen=True)
class Rewrite(ProofTerm):
    """Single rewrite step: apply a proof of a ≡ b to rewrite a
    subterm of the goal.

    ``equation`` is the proof of a ≡ b.
    ``in_lhs`` indicates whether to rewrite in lhs (True) or rhs (False).
    ``position`` is a path into the term tree (list of argument indices).
    """
    equation: ProofTerm
    in_lhs: bool = True
    position: Tuple[int, ...] = ()

    def children(self) -> List[ProofTerm]:
        return [self.equation]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        side = 'lhs' if self.in_lhs else 'rhs'
        eq = self.equation.pretty(indent + 1)
        pos = '.'.join(str(i) for i in self.position) if self.position else 'root'
        return f'{pad}rewrite[{side}@{pos}]:\n{eq}'


@dataclass(frozen=True)
class RewriteChain(ProofTerm):
    """Chain of rewrite steps: a ≡ a₁ ≡ a₂ ≡ ... ≡ b.

    Each step is a proof of aᵢ ≡ aᵢ₊₁.  Intermediate terms are
    recorded for verification.
    """
    steps: Tuple[ProofTerm, ...]
    intermediates: Tuple[OTerm, ...] = ()  # a, a₁, a₂, ..., b

    def children(self) -> List[ProofTerm]:
        return list(self.steps)

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}rewrite_chain:']
        for i, step in enumerate(self.steps):
            if i < len(self.intermediates):
                parts.append(f'{pad}  {self.intermediates[i].canon()}')
            parts.append(f'{pad}    ≡ (by:')
            parts.append(step.pretty(indent + 3))
            parts.append(f'{pad}    )')
        if self.intermediates and len(self.intermediates) > len(self.steps):
            parts.append(f'{pad}  {self.intermediates[-1].canon()}')
        return '\n'.join(parts)


# ═══════════════════════════════════════════════════════════════════
# Composition helpers
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class ArithmeticSimp(ProofTerm):
    """Arithmetic simplification proof.

    The checker evaluates both sides in the ring ℤ (or ℚ) and checks
    that they are equal.  This handles commutativity, associativity,
    distributivity, etc. automatically.
    """
    lhs_expr: OTerm
    rhs_expr: OTerm

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        return f'{pad}arith({self.lhs_expr.canon()} = {self.rhs_expr.canon()})'


@dataclass(frozen=True)
class ListSimp(ProofTerm):
    """List simplification: apply standard list identities.

    Handles: map-map fusion, filter-map commutation, fold-map fusion,
    append associativity, etc.
    """
    rule: str  # e.g. 'map_map_fusion', 'filter_map_commute'
    target: OTerm

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        return f'{pad}list_simp[{self.rule}]({self.target.canon()})'


@dataclass(frozen=True)
class Definitional(ProofTerm):
    """Definitional equality — both sides reduce to the same normal form.

    The checker normalizes both lhs and rhs (β, δ, ι reductions)
    and checks syntactic equality of the normal forms.
    """

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        return f'{pad}definitional'


# ═══════════════════════════════════════════════════════════════════
# C⁴ Calculus — new proof term constructors
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class FiberRestrict(ProofTerm):
    """Restrict a proof to a specific duck-type fiber.

    Given a proof of lhs ≡ rhs, produce a proof that the equality
    holds when restricted to fiber ``fiber_name``.  This corresponds
    to the restriction rule (Res) in C⁴.
    """
    fiber_name: str
    inner_proof: ProofTerm

    def children(self) -> List[ProofTerm]:
        return [self.inner_proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}fiber_restrict[{self.fiber_name}]:']
        parts.append(self.inner_proof.pretty(indent + 1))
        return '\n'.join(parts)


@dataclass(frozen=True)
class Descent(ProofTerm):
    """Glue fiber-local proofs into a global proof via the descent rule.

    Given local proofs on each fiber of a cover and compatibility
    witnesses on overlaps satisfying the cocycle condition, conclude
    global equality.  This internalizes H¹ = 0 ⟹ global section.
    """
    fiber_proofs: Dict[str, ProofTerm]
    overlap_proofs: Dict[Tuple[str, str], ProofTerm]

    def children(self) -> List[ProofTerm]:
        return list(self.fiber_proofs.values()) + list(self.overlap_proofs.values())

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}descent:']
        for fiber, proof in self.fiber_proofs.items():
            parts.append(f'{pad}  fiber[{fiber}]:')
            parts.append(proof.pretty(indent + 2))
        for (f1, f2), proof in self.overlap_proofs.items():
            parts.append(f'{pad}  overlap[{f1}∩{f2}]:')
            parts.append(proof.pretty(indent + 2))
        return '\n'.join(parts)


@dataclass(frozen=True)
class PathCompose(ProofTerm):
    """Compose two path proofs (transitivity in the cubical sense).

    Given p : a ≡ b and q : b ≡ c, produce p · q : a ≡ c.
    This corresponds to cubical path composition via hcomp.
    """
    left: ProofTerm
    right: ProofTerm
    middle: Optional[OTerm] = None

    def children(self) -> List[ProofTerm]:
        return [self.left, self.right]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        mid = f' via {self.middle.canon()[:30]}' if self.middle else ''
        parts = [f'{pad}path_compose{mid}:']
        parts.append(self.left.pretty(indent + 1))
        parts.append(self.right.pretty(indent + 1))
        return '\n'.join(parts)


@dataclass(frozen=True)
class MathLibAxiom(ProofTerm):
    """Apply a Mathlib theorem looked up from the catalog.

    The theorem_name is a fully qualified Lean name (e.g.,
    'Nat.add_comm').  The instantiation maps free variables to
    OTerms.  The theorem is trusted at LEAN_VERIFIED level.
    """
    theorem_name: str
    instantiation: Dict[str, OTerm] = field(default_factory=dict)

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        binds = ', '.join(f'{k}={v.canon()}' for k, v in self.instantiation.items())
        return f'{pad}mathlib_axiom[{self.theorem_name}]({binds})'


@dataclass(frozen=True)
class FiberwiseUnivalence(ProofTerm):
    """Prove type equality by providing fiberwise equivalences.

    Given equivalences on each fiber that are compatible on overlaps,
    conclude global type equality.  Corresponds to Theorem
    (Fiberwise Univalence) in the C⁴ cubical chapter.
    """
    fiber_equivs: Dict[str, ProofTerm]

    def children(self) -> List[ProofTerm]:
        return list(self.fiber_equivs.values())

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}fiberwise_univalence:']
        for fiber, proof in self.fiber_equivs.items():
            parts.append(f'{pad}  equiv[{fiber}]:')
            parts.append(proof.pretty(indent + 2))
        return '\n'.join(parts)


@dataclass(frozen=True)
class RefinementDescent(ProofTerm):
    """Descent by refinement-type fibers — arbitrary predicates as cover.

    Like Descent, but fibers are refinement types {x : T | φ(x)}
    instead of string-labeled duck-type fibers.  Each fiber's proof
    is checked UNDER the refinement hypothesis φ, and the cover
    is verified exhaustive (∨φᵢ = True).

    The predicates can be arbitrarily complex, including library
    operations:

        fiber "positive":  {x : int | x > 0}
        fiber "zero_mean": {t : Tensor | t.mean() == 0}
        fiber "expanded":  {e : Expr | sympy.expand(e) == e}

    Exhaustiveness verification:
    - Z3-decidable covers: Z3 checks ∨φᵢ is valid
    - Library covers: library axioms + trust
    - Oracle covers: LLM judges exhaustiveness

    Overlap handling:
    - Z3-empty overlaps: no compatibility proof needed
    - Non-empty overlaps: compatibility proof required under φᵢ ∧ φⱼ
    """
    base_type: str                                    # e.g., 'int', 'Tensor'
    bound_var: str                                    # e.g., 'x', 't', 'e'
    fiber_predicates: Dict[str, str]                  # name → predicate string
    fiber_proofs: Dict[str, ProofTerm]                # name → proof under φ
    overlap_proofs: Dict[Tuple[str, str], ProofTerm]  # (a,b) → proof under φ_a ∧ φ_b
    var_sorts: Dict[str, str] = field(default_factory=dict)
    exhaustiveness: str = 'assumed'                   # 'z3_proved' | 'assumed'

    def children(self) -> List[ProofTerm]:
        return (list(self.fiber_proofs.values()) +
                list(self.overlap_proofs.values()))

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}refinement_descent over {self.base_type} '
                 f'(var={self.bound_var}, '
                 f'exhaustive={self.exhaustiveness}):']
        for name, pred_str in self.fiber_predicates.items():
            parts.append(f'{pad}  fiber {name}: {{{self.base_type} | {pred_str}}}')
            if name in self.fiber_proofs:
                parts.append(self.fiber_proofs[name].pretty(indent + 2))
        for (a, b), proof in self.overlap_proofs.items():
            parts.append(f'{pad}  overlap[{a}∩{b}]:')
            parts.append(proof.pretty(indent + 2))
        return '\n'.join(parts)


# ═══════════════════════════════════════════════════════════════════
# Cubical Kan operations — the radically cohomological proof terms
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Transport(ProofTerm):
    """Transport a proof along a type path (cubical transp).

    Given:
      - path_proof : φ₁(x) ≡ φ₂(x)   (a path between predicates)
      - source_proof : proof under hypothesis φ₁
    Produce:
      - proof under hypothesis φ₂

    This is the cubical transport operation applied to the refinement
    lattice.  It moves proofs between fibers of a refinement cover,
    using library axioms or Z3 to justify the predicate path.

    Example: if we know abs(x) == x under {x > 0}, and we have a
    library axiom that "x > 0 implies x >= 0", then Transport gives
    us abs(x) == x under {x >= 0} (with a weaker hypothesis).

    In the Čech picture: transport is the TRANSITION MAP between
    local sections on overlapping opens.  It's the cocycle data
    that makes the sheaf glue.
    """
    path_proof: ProofTerm           # proof that source_pred ⟹ target_pred
    source_proof: ProofTerm         # proof under source predicate
    source_pred: str = ''           # human-readable source predicate
    target_pred: str = ''           # human-readable target predicate

    def children(self) -> List[ProofTerm]:
        return [self.path_proof, self.source_proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}transport ({self.source_pred} ⟹ {self.target_pred}):']
        parts.append(f'{pad}  path:')
        parts.append(self.path_proof.pretty(indent + 2))
        parts.append(f'{pad}  source:')
        parts.append(self.source_proof.pretty(indent + 2))
        return '\n'.join(parts)


@dataclass(frozen=True)
class HComp(ProofTerm):
    """Homogeneous composition — the cubical hcomp operation.

    Given a "box" of proofs (partial proof with boundaries specified),
    fill the interior.  This is how multiple proof paths compose
    when they share boundary conditions.

    In practice: given proofs along multiple cubical faces that agree
    on edges, produce the composite proof.  This generalizes Trans
    from a 1-dimensional chain to an n-dimensional composition.

    Example (2D composition):
      face_i0 : f ≡ g     (proof along dimension i at 0)
      face_i1 : f ≡ g     (proof along dimension i at 1)
      face_j0 : f ≡ g     (proof along dimension j at 0)
      face_j1 : f ≡ g     (proof along dimension j at 1)
      hcomp fills the square.

    In the Čech picture: this is the HIGHER cocycle condition.
    For triple overlaps U_i ∩ U_j ∩ U_k, the transition maps
    must satisfy g_ij · g_jk = g_ik.  HComp verifies this.
    """
    faces: Dict[str, ProofTerm]      # face_name → proof on that face
    base: Optional[ProofTerm] = None  # base proof (if partial box)

    def children(self) -> List[ProofTerm]:
        result = list(self.faces.values())
        if self.base:
            result.append(self.base)
        return result

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}hcomp ({len(self.faces)} faces):']
        for name, proof in self.faces.items():
            parts.append(f'{pad}  face[{name}]:')
            parts.append(proof.pretty(indent + 2))
        if self.base:
            parts.append(f'{pad}  base:')
            parts.append(self.base.pretty(indent + 2))
        return '\n'.join(parts)


@dataclass(frozen=True)
class GluePath(ProofTerm):
    """Glue local cubical paths via Čech descent into a global path.

    This combines the cubical and cohomological structures: given
    local proofs on each fiber of a refinement cover that are
    PATHS (vary over the cubical interval), glue them into a
    global path using the descent condition.

    Unlike plain Descent (which glues equality proofs), GluePath
    glues PATH proofs — proofs that vary continuously over a
    parameter.  This is strictly more powerful because it handles
    parameterized families of equalities.

    Example: proving that two sorting algorithms are equal FOR ALL
    comparison functions.  Each comparison function is a point in
    the space of orderings, and GluePath glues the per-ordering
    proofs into a proof that's uniform over all orderings.

    In the spectral sequence: GluePath computes the E_1 page,
    gluing local H⁰ sections into global H⁰.
    """
    cover_name: str                       # name of the refinement cover
    local_paths: Dict[str, ProofTerm]     # fiber → local path proof
    overlap_paths: Dict[Tuple[str, str], ProofTerm]  # (a,b) → overlap path
    fiber_predicates: Dict[str, str] = field(default_factory=dict)

    def children(self) -> List[ProofTerm]:
        return (list(self.local_paths.values()) +
                list(self.overlap_paths.values()))

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}glue_path[{self.cover_name}] '
                 f'({len(self.local_paths)} fibers):']
        for name, proof in self.local_paths.items():
            pred = self.fiber_predicates.get(name, '')
            parts.append(f'{pad}  path[{name}] ({pred}):')
            parts.append(proof.pretty(indent + 2))
        for (a, b), proof in self.overlap_paths.items():
            parts.append(f'{pad}  overlap_path[{a}∩{b}]:')
            parts.append(proof.pretty(indent + 2))
        return '\n'.join(parts)


@dataclass(frozen=True)
class LibraryTransport(ProofTerm):
    """Transport a proof using a library axiom as the type path.

    This specializes Transport for the common case where the path
    between predicates is justified by a library axiom rather than
    a structural proof.

    Example:
      axiom: sympy.expand(sympy.factor(e)) == e  for polynomial e
      source: proof of P(sympy.factor(e))
      target: proof of P(e)
      path: the library axiom gives factor(e) ≡ e after expand

    This is the key proof term for LIBRARY VERIFICATION: it lets
    library axioms act as transport maps between refinement fibers.

    Trust level: LIBRARY_ASSUMED (inherits from the axiom).
    """
    library: str                     # 'sympy', 'numpy', etc.
    axiom_name: str                  # which library axiom
    source_proof: ProofTerm          # proof at the source
    instantiation: Dict[str, OTerm] = field(default_factory=dict)
    statement: str = ''              # the axiom statement

    def children(self) -> List[ProofTerm]:
        return [self.source_proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        binds = ', '.join(f'{k}={v.canon()}' for k, v in self.instantiation.items())
        parts = [f'{pad}library_transport[{self.library}.{self.axiom_name}]({binds}):']
        parts.append(self.source_proof.pretty(indent + 1))
        return '\n'.join(parts)


# ═══════════════════════════════════════════════════════════════════
# F*-style tactics — weakest precondition, effects, dependent matching
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class WeakestPrecondition(ProofTerm):
    """Weakest precondition calculus for imperative reasoning.

    Given postcondition Q and statement S, computes wp(S, Q) — the
    weakest precondition P such that {P} S {Q}.

    F*-style: wp is a predicate transformer. For sequential code:
        wp(x := e, Q) = Q[x := e]
        wp(S1; S2, Q) = wp(S1, wp(S2, Q))
        wp(if b then S1 else S2, Q) = (b → wp(S1,Q)) ∧ (¬b → wp(S2,Q))

    The proof obligation is: precondition → wp(body, postcondition).
    The precondition_proof discharges this via Z3 or structural reasoning.
    """
    statement_desc: str           # description of the statement being analyzed
    postcondition: str            # the target postcondition Q
    wp_formula: str               # the computed wp(S, Q)
    precondition_proof: ProofTerm  # proof that precondition → wp

    def children(self) -> List[ProofTerm]:
        return [self.precondition_proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [
            f'{pad}wp[{self.statement_desc}]:',
            f'{pad}  post: {self.postcondition}',
            f'{pad}  wp: {self.wp_formula}',
            f'{pad}  discharge:',
            self.precondition_proof.pretty(indent + 2),
        ]
        return '\n'.join(parts)


@dataclass(frozen=True)
class EffectFrame(ProofTerm):
    """Frame condition: proves a function only modifies declared state.

    F*-style effect typing: a function annotated ST s a modifies only
    state variables in its footprint. The frame proof shows that
    everything NOT in the footprint is preserved.

    For Python: the footprint is the set of attributes/keys that may
    be mutated. The frame proof shows all other attributes are unchanged.

    frame_vars: the set of variables/attributes that MAY change
    preserved_proof: proof that everything else is unchanged
    """
    frame_vars: Tuple[str, ...]     # variables in the modification footprint
    function_desc: str              # which function this frames
    preserved_proof: ProofTerm      # proof that non-footprint state is unchanged

    def children(self) -> List[ProofTerm]:
        return [self.preserved_proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        fv = ', '.join(self.frame_vars)
        return (f'{pad}frame[{self.function_desc}](modifies={{{fv}}}):\n'
                f'{self.preserved_proof.pretty(indent + 1)}')


@dataclass(frozen=True)
class ExceptionCase(ProofTerm):
    """Exception path case analysis.

    Models try/except as a disjoint union:
        result = normal_case ⊔ exception_case
    with proof obligations on each branch.

    Python-specific: maps try/except blocks to case analysis where
    the discriminant is "did an exception occur?".
    """
    normal_proof: ProofTerm         # proof for the non-exception path
    exception_proofs: Dict[str, ProofTerm]  # exception_type → proof for that handler
    finally_proof: Optional[ProofTerm] = None  # proof for the finally block

    def children(self) -> List[ProofTerm]:
        kids = [self.normal_proof] + list(self.exception_proofs.values())
        if self.finally_proof:
            kids.append(self.finally_proof)
        return kids

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}exception_case:']
        parts.append(f'{pad}  try:')
        parts.append(self.normal_proof.pretty(indent + 2))
        for exc_type, proof in self.exception_proofs.items():
            parts.append(f'{pad}  except {exc_type}:')
            parts.append(proof.pretty(indent + 2))
        if self.finally_proof:
            parts.append(f'{pad}  finally:')
            parts.append(self.finally_proof.pretty(indent + 2))
        return '\n'.join(parts)


@dataclass(frozen=True)
class Normalize(ProofTerm):
    """Prove equality by normalizing both sides to a canonical form.

    Applies a sequence of reduction steps (β, δ, η, arithmetic simplification)
    and checks that the normal forms are identical.

    This is the workhorse tactic for straightforward code: if both sides
    reduce to the same thing, they're equal.
    """
    reduction_steps: Tuple[str, ...]  # sequence of reductions applied
    normal_form_desc: str = ""        # description of the common normal form

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        steps = ' → '.join(self.reduction_steps) if self.reduction_steps else 'trivial'
        return f'{pad}normalize({steps})'


@dataclass(frozen=True)
class DependentMatch(ProofTerm):
    """Dependent pattern matching with index refinement.

    F*-style: matching on a value of an indexed type refines the
    type indices in each branch. This is crucial for isinstance
    dispatch in Python — matching on isinstance(x, T) refines
    the type of x in that branch.

    discriminant_type: what we're matching on (e.g., "type(x)")
    branches: case_label → (refined_context, proof)
    """
    discriminant: OTerm
    discriminant_type: str
    branches: Dict[str, ProofTerm]
    exhaustiveness_proof: Optional[ProofTerm] = None

    def children(self) -> List[ProofTerm]:
        kids = list(self.branches.values())
        if self.exhaustiveness_proof:
            kids.append(self.exhaustiveness_proof)
        return kids

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}dependent_match[{self.discriminant_type}]:']
        for case, proof in self.branches.items():
            parts.append(f'{pad}  | {case} →')
            parts.append(proof.pretty(indent + 2))
        return '\n'.join(parts)


@dataclass(frozen=True)
class LemmaApp(ProofTerm):
    """Apply a previously proved lemma to the current goal.

    F*-style: lemma application. The lemma has already been verified;
    this step instantiates it at specific terms.

    Differs from AxiomApp: axioms are built-in; lemmas are user-proved.
    The lemma_proof field holds the original proof for trust tracking.
    """
    lemma_name: str
    instantiation: Dict[str, OTerm]
    lemma_proof: ProofTerm  # the original proof of the lemma

    def children(self) -> List[ProofTerm]:
        return [self.lemma_proof]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        binds = ', '.join(f'{k}={v.canon()}' for k, v in self.instantiation.items())
        return f'{pad}lemma[{self.lemma_name}]({binds})'


@dataclass(frozen=True)
class Unfold(ProofTerm):
    """Unfold a definition and simplify.

    Given f(x) = body, proves f(a) = body[x := a] by δ-reduction.
    Then optionally applies further simplification via inner_proof.

    More structured than bare Delta: records the function name,
    the arguments, and allows chained simplification.
    """
    func_name: str
    args: Tuple[OTerm, ...]
    inner_proof: Optional[ProofTerm] = None  # proof after unfolding

    def children(self) -> List[ProofTerm]:
        return [self.inner_proof] if self.inner_proof else []

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        args_str = ', '.join(a.canon() for a in self.args)
        parts = [f'{pad}unfold {self.func_name}({args_str})']
        if self.inner_proof:
            parts.append(self.inner_proof.pretty(indent + 1))
        return '\n'.join(parts)


@dataclass(frozen=True)
class Assert(ProofTerm):
    """Assert an intermediate fact and prove it.

    F*-style assert: introduces a cut where the assertion must be
    proved at this point, then can be used in the continuation.

    Similar to Cut but specifically for intermediate assertions
    in imperative-style proofs.
    """
    assertion: str              # the fact being asserted (as formula)
    assertion_proof: ProofTerm  # proof of the assertion
    continuation: ProofTerm     # proof that uses the assertion

    def children(self) -> List[ProofTerm]:
        return [self.assertion_proof, self.continuation]

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [
            f'{pad}assert ({self.assertion}):',
            self.assertion_proof.pretty(indent + 1),
            f'{pad}in:',
            self.continuation.pretty(indent + 1),
        ]
        return '\n'.join(parts)


# ═══════════════════════════════════════════════════════════════════
# Ex falso quodlibet — from ⊥, derive anything
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class ExFalso(ProofTerm):
    """Ex falso quodlibet — from contradictory hypotheses, derive anything.

    In cubical type theory: a path from ⊥ transports to any type.
    In F*: ``match (proof_of_false : squash False) with`` has any return type.
    In classical logic: ⊥ → P  for any P.

    The compiler verifies this by checking that ``context_formula`` is
    UNSAT in Z3 — i.e., the conjunction of hypotheses in the current
    proof context is contradictory.  If Z3 confirms UNSAT, the proof
    is valid for ANY goal (the goal need not even be parseable).

    This is the fundamental proof term for handling contradictory
    branches: when a fiber guard contradicts a path guard, the path
    is unreachable and ExFalso closes the case.

    Context fields carry enough information for the C4 compiler to
    re-verify the contradiction independently.
    """
    context_formula: str             # ∧-conjunction of contradictory hypotheses
    variables: Dict[str, str]        # variable → Z3 sort (Int, Bool, Real)
    absurdity: str = ""              # human-readable explanation

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        desc = self.absurdity or self.context_formula
        return f'{pad}ex_falso({desc})'


# ═══════════════════════════════════════════════════════════════════
# F*-style proof obligation — code-connected verification request
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class ProofObligation:
    """A code-connected proof obligation in the F* sense.

    In F*, the type checker generates verification conditions (VCs)
    from the code's refinement types.  Each VC is a logical formula
    that must hold for the code to be type-safe.

    A ProofObligation captures the same concept for C4:
    - hypotheses: preconditions + branch guards + result binding
    - goal: the postcondition clause to verify
    - code context: the actual source code, function name, variables

    The proof oracle (LLM or automated) generates a ProofTerm that
    witnesses this obligation.  The C4 compiler then verifies the
    proof term independently.
    """
    hypotheses: Tuple[str, ...]     # requires + path guard + result binding
    goal: str                       # the clause to prove
    return_expr: str                # the actual return expression
    func_name: str                  # function being verified
    source: str                     # source code context
    params: Tuple[str, ...]         # parameter names
    var_sorts: Dict[str, str]       # variable → sort
    fiber_guard: Optional[str] = None  # if this is a fiber clause


def subst_in_term(term: OTerm, var: str, replacement: OTerm) -> OTerm:
    """Substitute ``replacement`` for ``var`` in ``term``."""
    if isinstance(term, OVar):
        return replacement if term.name == var else term
    elif isinstance(term, OLit):
        return term
    elif isinstance(term, OOp):
        new_args = tuple(subst_in_term(a, var, replacement) for a in term.args)
        return OOp(term.name, new_args)
    elif isinstance(term, OFold):
        return OFold(term.op_name,
                     subst_in_term(term.init, var, replacement),
                     subst_in_term(term.collection, var, replacement))
    elif isinstance(term, OCase):
        return OCase(subst_in_term(term.test, var, replacement),
                     subst_in_term(term.true_branch, var, replacement),
                     subst_in_term(term.false_branch, var, replacement))
    elif isinstance(term, OFix):
        if term.name == var:
            return term  # shadowed
        return OFix(term.name, subst_in_term(term.body, var, replacement))
    elif isinstance(term, OSeq):
        new_elems = tuple(subst_in_term(e, var, replacement) for e in term.elements)
        return OSeq(new_elems)
    elif isinstance(term, ODict):
        new_pairs = tuple((subst_in_term(k, var, replacement),
                           subst_in_term(v, var, replacement))
                          for k, v in term.pairs)
        return ODict(new_pairs)
    elif isinstance(term, OUnknown):
        return term
    elif isinstance(term, OQuotient):
        return OQuotient(subst_in_term(term.inner, var, replacement),
                         term.equiv_class)
    elif isinstance(term, OAbstract):
        new_inputs = tuple(subst_in_term(i, var, replacement) for i in term.inputs)
        return OAbstract(term.spec, new_inputs)
    elif isinstance(term, OLam):
        if var in term.params:
            return term  # shadowed
        return OLam(term.params, subst_in_term(term.body, var, replacement))
    elif isinstance(term, OMap):
        fp = (subst_in_term(term.filter_pred, var, replacement)
              if term.filter_pred else None)
        return OMap(subst_in_term(term.transform, var, replacement),
                    subst_in_term(term.collection, var, replacement),
                    fp)
    elif isinstance(term, OCatch):
        return OCatch(subst_in_term(term.body, var, replacement),
                      subst_in_term(term.default, var, replacement))
    else:
        return term


def free_vars(term: OTerm) -> Set[str]:
    """Compute the set of free variable names in an OTerm."""
    if isinstance(term, OVar):
        return {term.name}
    elif isinstance(term, OLit):
        return set()
    elif isinstance(term, OOp):
        result: Set[str] = set()
        for a in term.args:
            result |= free_vars(a)
        return result
    elif isinstance(term, OFold):
        return free_vars(term.init) | free_vars(term.collection)
    elif isinstance(term, OCase):
        return (free_vars(term.test) | free_vars(term.true_branch)
                | free_vars(term.false_branch))
    elif isinstance(term, OFix):
        return free_vars(term.body) - {term.name}
    elif isinstance(term, OSeq):
        result = set()
        for e in term.elements:
            result |= free_vars(e)
        return result
    elif isinstance(term, ODict):
        result = set()
        for k, v in term.pairs:
            result |= free_vars(k) | free_vars(v)
        return result
    elif isinstance(term, OUnknown):
        return set()
    elif isinstance(term, OQuotient):
        return free_vars(term.inner)
    elif isinstance(term, OAbstract):
        result = set()
        for i in term.inputs:
            result |= free_vars(i)
        return result
    elif isinstance(term, OLam):
        return free_vars(term.body) - set(term.params)
    elif isinstance(term, OMap):
        result = free_vars(term.transform) | free_vars(term.collection)
        if term.filter_pred:
            result |= free_vars(term.filter_pred)
        return result
    elif isinstance(term, OCatch):
        return free_vars(term.body) | free_vars(term.default)
    else:
        return set()


def terms_equal(a: OTerm, b: OTerm) -> bool:
    """Syntactic equality of OTerms (via canonical forms)."""
    return a.canon() == b.canon()


def normalize_term(term: OTerm) -> OTerm:
    """Normalize an OTerm by applying basic simplifications.

    This is a simple normalizer (not full β-reduction) that handles:
    - Constant folding for arithmetic
    - Identity operations (x + 0, x * 1, etc.)
    - Flattening nested sequences
    """
    if isinstance(term, (OVar, OLit, OUnknown)):
        return term

    if isinstance(term, OOp):
        nargs = tuple(normalize_term(a) for a in term.args)
        # Constant folding
        if all(isinstance(a, OLit) for a in nargs):
            try:
                vals = [a.value for a in nargs]  # type: ignore
                if term.name == '+' and len(vals) == 2:
                    return OLit(vals[0] + vals[1])
                elif term.name == '-' and len(vals) == 2:
                    return OLit(vals[0] - vals[1])
                elif term.name == '*' and len(vals) == 2:
                    return OLit(vals[0] * vals[1])
                elif term.name == '//' and len(vals) == 2 and vals[1] != 0:
                    return OLit(vals[0] // vals[1])
                elif term.name == '%' and len(vals) == 2 and vals[1] != 0:
                    return OLit(vals[0] % vals[1])
                elif term.name == '==' and len(vals) == 2:
                    return OLit(vals[0] == vals[1])
                elif term.name == '!=' and len(vals) == 2:
                    return OLit(vals[0] != vals[1])
                elif term.name == '<' and len(vals) == 2:
                    return OLit(vals[0] < vals[1])
                elif term.name == '<=' and len(vals) == 2:
                    return OLit(vals[0] <= vals[1])
                elif term.name == '>' and len(vals) == 2:
                    return OLit(vals[0] > vals[1])
                elif term.name == '>=' and len(vals) == 2:
                    return OLit(vals[0] >= vals[1])
                elif term.name == 'min' and len(vals) == 2:
                    return OLit(min(vals[0], vals[1]))
                elif term.name == 'max' and len(vals) == 2:
                    return OLit(max(vals[0], vals[1]))
            except (TypeError, ValueError, ZeroDivisionError):
                pass

        # Identity operations
        if term.name == '+' and len(nargs) == 2:
            if isinstance(nargs[0], OLit) and nargs[0].value == 0:
                return nargs[1]
            if isinstance(nargs[1], OLit) and nargs[1].value == 0:
                return nargs[0]
        if term.name == '*' and len(nargs) == 2:
            if isinstance(nargs[0], OLit) and nargs[0].value == 1:
                return nargs[1]
            if isinstance(nargs[1], OLit) and nargs[1].value == 1:
                return nargs[0]
            if isinstance(nargs[0], OLit) and nargs[0].value == 0:
                return OLit(0)
            if isinstance(nargs[1], OLit) and nargs[1].value == 0:
                return OLit(0)

        return OOp(term.name, nargs)

    if isinstance(term, OFold):
        return OFold(term.op_name,
                     normalize_term(term.init),
                     normalize_term(term.collection))

    if isinstance(term, OCase):
        nt = normalize_term(term.test)
        # Constant condition
        if isinstance(nt, OLit):
            if nt.value:
                return normalize_term(term.true_branch)
            else:
                return normalize_term(term.false_branch)
        return OCase(nt,
                     normalize_term(term.true_branch),
                     normalize_term(term.false_branch))

    if isinstance(term, OFix):
        return OFix(term.name, normalize_term(term.body))

    if isinstance(term, OSeq):
        return OSeq(tuple(normalize_term(e) for e in term.elements))

    if isinstance(term, ODict):
        return ODict(tuple((normalize_term(k), normalize_term(v))
                           for k, v in term.pairs))

    if isinstance(term, OQuotient):
        return OQuotient(normalize_term(term.inner), term.equiv_class)

    if isinstance(term, OAbstract):
        return OAbstract(term.spec,
                         tuple(normalize_term(i) for i in term.inputs))

    if isinstance(term, OLam):
        return OLam(term.params, normalize_term(term.body))

    if isinstance(term, OMap):
        fp = normalize_term(term.filter_pred) if term.filter_pred else None
        return OMap(normalize_term(term.transform),
                    normalize_term(term.collection), fp)

    if isinstance(term, OCatch):
        return OCatch(normalize_term(term.body),
                      normalize_term(term.default))

    return term


def apply_subst_to_term(term: OTerm, subst: Dict[str, OTerm]) -> OTerm:
    """Apply a simultaneous substitution to an OTerm."""
    result = term
    for var, replacement in subst.items():
        result = subst_in_term(result, var, replacement)
    return result


# ═══════════════════════════════════════════════════════════════════
# Term builders — convenience constructors
# ═══════════════════════════════════════════════════════════════════

def var(name: str) -> OVar:
    return OVar(name)

def lit(value: Any) -> OLit:
    return OLit(value)

def op(name: str, *args: OTerm) -> OOp:
    return OOp(name, tuple(args))

def app(func_name: str, *args: OTerm) -> OOp:
    return OOp(func_name, tuple(args))

def lam(params: List[str], body: OTerm) -> OLam:
    return OLam(tuple(params), body)

def fold_term(op_name: str, init: OTerm, coll: OTerm) -> OFold:
    return OFold(op_name, init, coll)

def case(test: OTerm, t: OTerm, f: OTerm) -> OCase:
    return OCase(test, t, f)

def fix(name: str, body: OTerm) -> OFix:
    return OFix(name, body)

def seq(*elems: OTerm) -> OSeq:
    return OSeq(tuple(elems))

def abstract(spec: str, *inputs: OTerm) -> OAbstract:
    return OAbstract(spec, tuple(inputs))

def unknown(desc: str) -> OUnknown:
    return OUnknown(desc)


# ═══════════════════════════════════════════════════════════════════
# Proof builders — convenience constructors
# ═══════════════════════════════════════════════════════════════════

def refl(term: OTerm) -> Refl:
    return Refl(term)

def sym(proof: ProofTerm) -> Sym:
    return Sym(proof)

def trans(left: ProofTerm, right: ProofTerm,
          middle: Optional[OTerm] = None) -> Trans:
    return Trans(left, right, middle)

def cong(func: str, *arg_proofs: ProofTerm) -> Cong:
    return Cong(func, tuple(arg_proofs))

def beta(lam_term: OTerm, arg: OTerm) -> Beta:
    return Beta(lam_term, arg)

def delta(func_name: str, *args: OTerm) -> Delta:
    return Delta(func_name, tuple(args))

def eta(term: OTerm) -> Eta:
    return Eta(term)

def axiom_app(name: str, direction: str, target: OTerm,
              bindings: Optional[Dict[str, OTerm]] = None) -> AxiomApp:
    return AxiomApp(name, direction, target, bindings or {})

def z3_discharge(formula: str, fragment: str = 'QF_LIA',
                 timeout_ms: int = 5000,
                 variables: Optional[Dict[str, str]] = None) -> Z3Discharge:
    return Z3Discharge(formula, fragment, timeout_ms, variables or {})

def simulation(relation: str,
               init_proof: ProofTerm,
               step_proof: ProofTerm,
               output_proof: ProofTerm) -> Simulation:
    return Simulation(relation, init_proof, step_proof, output_proof)

def abstraction_refinement(spec_name: str,
                           abstraction_f: ProofTerm,
                           abstraction_g: ProofTerm) -> AbstractionRefinement:
    return AbstractionRefinement(spec_name, abstraction_f, abstraction_g)

def nat_induction(base_case: ProofTerm,
                  inductive_step: ProofTerm,
                  variable: str) -> NatInduction:
    return NatInduction(base_case, inductive_step, variable)

def list_induction(nil_case: ProofTerm,
                   cons_case: ProofTerm,
                   variable: str) -> ListInduction:
    return ListInduction(nil_case, cons_case, variable)

def wf_induction(measure: str, step: ProofTerm) -> WellFoundedInduction:
    return WellFoundedInduction(measure, step)

def loop_invariant(invariant: str,
                   init_proof: ProofTerm,
                   preservation: ProofTerm,
                   termination: ProofTerm,
                   post_proof: ProofTerm) -> LoopInvariant:
    return LoopInvariant(invariant, init_proof, preservation,
                         termination, post_proof)

def comm_diagram(morphism: ProofTerm,
                 iso: ProofTerm) -> CommDiagram:
    return CommDiagram(morphism, iso)

def functor_map(functor: str,
                compose_proof: ProofTerm) -> FunctorMap:
    return FunctorMap(functor, compose_proof)

def fiber_decomposition(fiber_proofs: Dict[str, ProofTerm]) -> FiberDecomposition:
    return FiberDecomposition(fiber_proofs)

def cech_gluing(local_proofs: List[ProofTerm],
                overlap_proofs: List[ProofTerm]) -> CechGluing:
    return CechGluing(tuple(local_proofs), tuple(overlap_proofs))

def cases_split(discriminant: OTerm,
                cases: Dict[str, ProofTerm]) -> CasesSplit:
    return CasesSplit(discriminant, cases)

def ext(var_name: str, body_proof: ProofTerm) -> Ext:
    return Ext(var_name, body_proof)

def rewrite(equation: ProofTerm, in_lhs: bool = True,
            position: Tuple[int, ...] = ()) -> Rewrite:
    return Rewrite(equation, in_lhs, position)

def rewrite_chain(steps: List[ProofTerm],
                  intermediates: Optional[List[OTerm]] = None) -> RewriteChain:
    return RewriteChain(tuple(steps), tuple(intermediates or []))

def cut(lhs: OTerm, rhs: OTerm,
        lemma_proof: ProofTerm, main_proof: ProofTerm,
        label: str = 'lemma') -> Cut:
    return Cut(lhs, rhs, lemma_proof, main_proof, label)

def let_proof(label: str, lhs: OTerm, rhs: OTerm,
              sub: ProofTerm, body: ProofTerm) -> LetProof:
    return LetProof(label, lhs, rhs, sub, body)

def assume(label: str, lhs: OTerm, rhs: OTerm) -> Assume:
    return Assume(label, lhs, rhs)

def definitional() -> Definitional:
    return Definitional()

def arithmetic_simp(lhs: OTerm, rhs: OTerm) -> ArithmeticSimp:
    return ArithmeticSimp(lhs, rhs)

def list_simp(rule: str, target: OTerm) -> ListSimp:
    return ListSimp(rule, target)


# ── C⁴ calculus proof builders ───────────────────────────────────

def fiber_restrict(fiber_name: str, inner: ProofTerm) -> FiberRestrict:
    return FiberRestrict(fiber_name, inner)

def descent(fiber_proofs: Dict[str, ProofTerm],
            overlap_proofs: Optional[Dict[Tuple[str, str], ProofTerm]] = None) -> Descent:
    return Descent(fiber_proofs, overlap_proofs or {})

def path_compose(left: ProofTerm, right: ProofTerm,
                 middle: Optional[OTerm] = None) -> PathCompose:
    return PathCompose(left, right, middle)

def mathlib_axiom(theorem_name: str,
                  instantiation: Optional[Dict[str, OTerm]] = None) -> MathLibAxiom:
    return MathLibAxiom(theorem_name, instantiation or {})

def fiberwise_univalence(fiber_equivs: Dict[str, ProofTerm]) -> FiberwiseUnivalence:
    return FiberwiseUnivalence(fiber_equivs)


def refinement_descent(
    base_type: str,
    bound_var: str,
    fiber_predicates: Dict[str, str],
    fiber_proofs: Dict[str, ProofTerm],
    overlap_proofs: Optional[Dict[Tuple[str, str], ProofTerm]] = None,
    var_sorts: Optional[Dict[str, str]] = None,
    exhaustiveness: str = 'assumed',
) -> RefinementDescent:
    return RefinementDescent(
        base_type=base_type,
        bound_var=bound_var,
        fiber_predicates=fiber_predicates,
        fiber_proofs=fiber_proofs,
        overlap_proofs=overlap_proofs or {},
        var_sorts=var_sorts or {},
        exhaustiveness=exhaustiveness,
    )
