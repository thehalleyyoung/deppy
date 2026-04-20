"""
SynHoPy Proof Language & Tactics

High-level proof DSL that compiles down to ProofTerm types in
synhopy.core.kernel.  Users write proofs using ProofBuilder (an
imperative tactic interface) or ProofScript (a replayable sequence of
ProofStep objects).  Both ultimately produce ProofTerms verified by the
trusted ProofKernel.

Example
-------
    kernel = ProofKernel()
    ctx    = Context()
    pb     = ProofBuilder(kernel, ctx)

    pb.have("h1", "x > 0",        pb.assume("precond"))
    pb.have("h2", "x + 1 > 1",    pb.z3("x > 0 => x + 1 > 1"))
    result = pb.conclude(pb.by("h2"))
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Sequence

from synhopy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Sym, Trans, Cong, Cut, Assume, Z3Proof,
    NatInduction, ListInduction, Cases, DuckPath,
    EffectWitness, AxiomInvocation, Ext, Unfold, Rewrite,
    Structural, TransportProof, min_trust,
)
from synhopy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    Var, Literal, PyObjType, PyIntType, PyBoolType, RefinementType,
    PathType, App, Lam,
)


# ═══════════════════════════════════════════════════════════════════
#  ProofStep — single tactic invocation
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProofStep:
    """An individual tactic application inside a ProofScript."""

    tactic: str                         # e.g. "have", "rewrite", "induction"
    args: dict[str, Any] = field(       # tactic-specific arguments
        default_factory=dict
    )
    sub_proofs: list[ProofTerm] = field(  # nested sub-proofs if needed
        default_factory=list
    )

    def __repr__(self) -> str:
        subs = f", {len(self.sub_proofs)} sub-proofs" if self.sub_proofs else ""
        return f"ProofStep({self.tactic}, {self.args}{subs})"


# ═══════════════════════════════════════════════════════════════════
#  ProofScript — replayable proof
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProofScript:
    """A proof script that can be replayed.

    Holds an ordered list of ProofSteps and the goal judgment that the
    proof is meant to establish.  ``execute`` replays the script
    through a ProofBuilder to produce a VerificationResult.
    """

    steps: list[ProofStep]
    goal: Judgment

    # ── execution ────────────────────────────────────────────────

    def execute(self, kernel: ProofKernel, ctx: Context) -> VerificationResult:
        """Replay every step and return the final verification result."""
        pb = ProofBuilder(kernel, ctx, goal=self.goal)
        for step in self.steps:
            _apply_step(pb, step)
        proof_term = self.to_proof_term()
        return kernel.verify(ctx, self.goal, proof_term)

    # ── compilation to ProofTerm ─────────────────────────────────

    def to_proof_term(self) -> ProofTerm:
        """Compile the script to a single ProofTerm (outermost Cut chain)."""
        if not self.steps:
            return Structural("empty proof script")

        term = _step_to_proof_term(self.steps[-1])
        for step in reversed(self.steps[:-1]):
            step_term = _step_to_proof_term(step)
            name = step.args.get("name", "_lemma")
            claim = step.args.get("claim", "")
            term = Cut(
                hyp_name=name,
                hyp_type=RefinementType(
                    base_type=PyBoolType(),
                    predicate=claim,
                ),
                lemma_proof=step_term,
                body_proof=term,
            )
        return term


def _step_to_proof_term(step: ProofStep) -> ProofTerm:
    """Convert a single ProofStep to the ProofTerm it represents."""
    if step.sub_proofs:
        return step.sub_proofs[0]

    tactic = step.tactic
    args = step.args

    if tactic == "assume":
        return Assume(name=args.get("name", ""))
    if tactic == "z3":
        return Z3Proof(formula=args.get("formula", ""))
    if tactic == "refl":
        return Refl(term=args.get("term", Literal(None)))
    if tactic == "structural":
        return Structural(description=args.get("desc", ""))
    if tactic == "axiom":
        return AxiomInvocation(
            name=args.get("name", ""),
            module=args.get("module", ""),
        )
    if tactic == "unfold":
        return Unfold(func_name=args.get("func_name", ""))
    return Structural(description=f"tactic:{tactic}")


def _apply_step(pb: ProofBuilder, step: ProofStep) -> None:
    """Apply a ProofStep to a ProofBuilder (side-effecting)."""
    tactic = step.tactic
    args = step.args

    if tactic == "have":
        proof = step.sub_proofs[0] if step.sub_proofs else Structural()
        pb.have(args.get("name", "_"), args.get("claim", ""), proof)
    elif tactic == "suffices":
        proof = step.sub_proofs[0] if step.sub_proofs else Structural()
        pb.suffices(args.get("claim", ""), proof)
    # Other tactics are terminal and handled by to_proof_term.


# ═══════════════════════════════════════════════════════════════════
#  ProofBuilder — the main tactic DSL
# ═══════════════════════════════════════════════════════════════════

class ProofBuilder:
    """High-level proof DSL that compiles to ProofTerms.

    Usage::

        pb = ProofBuilder(kernel, context)
        pb.have("h1", "x > 0", pb.assume("precond"))
        pb.have("h2", "x + 1 > 1", pb.z3("x > 0 => x + 1 > 1"))
        result = pb.conclude(pb.by("h2"))

    The builder accumulates a *proof context* — an extended typing
    context that records every hypothesis introduced via ``have``.
    When ``conclude`` is called the builder wraps the final proof in a
    chain of Cut nodes and feeds the result to the kernel.
    """

    def __init__(
        self,
        kernel: ProofKernel,
        context: Context,
        goal: Judgment | None = None,
    ) -> None:
        self._kernel = kernel
        self._base_ctx = context
        self._ctx = context
        self._goal = goal
        self._steps: list[tuple[str, str, ProofTerm]] = []  # (name, claim, proof)
        self._hypotheses: dict[str, ProofTerm] = {}
        self._history: list[ProofStep] = []

    # ── property accessors ───────────────────────────────────────

    @property
    def context(self) -> Context:
        """Current proof context (base + hypotheses)."""
        return self._ctx

    @property
    def goal(self) -> Judgment | None:
        """The top-level goal, if one was set."""
        return self._goal

    @property
    def history(self) -> list[ProofStep]:
        """History of tactic applications (for building a ProofScript)."""
        return list(self._history)

    # ── core tactics ─────────────────────────────────────────────

    def have(self, name: str, claim: str, proof: ProofTerm) -> ProofBuilder:
        """Introduce a local lemma into the proof context.

        Analogous to Lean's ``have h : P := proof``.
        """
        claim_type = RefinementType(
            base_type=PyBoolType(),
            predicate=claim,
        )
        self._ctx = self._ctx.extend(name, claim_type)
        self._steps.append((name, claim, proof))
        self._hypotheses[name] = proof
        self._history.append(ProofStep(
            tactic="have",
            args={"name": name, "claim": claim},
            sub_proofs=[proof],
        ))
        return self

    def suffices(self, claim: str, proof: ProofTerm) -> ProofBuilder:
        """Reduce the current goal to a weaker one.

        ``suffices`` declares that if *claim* holds then the original
        goal follows.  The *proof* must justify the sufficiency step.
        """
        suffice_type = RefinementType(
            base_type=PyBoolType(),
            predicate=claim,
        )
        self._ctx = self._ctx.extend("_suffices", suffice_type)
        self._steps.append(("_suffices", claim, proof))
        self._history.append(ProofStep(
            tactic="suffices",
            args={"claim": claim},
            sub_proofs=[proof],
        ))
        return self

    def conclude(self, proof: ProofTerm) -> VerificationResult:
        """Finish the proof and verify the result with the kernel.

        The accumulated hypotheses are wrapped in ``Cut`` nodes around
        *proof* and the whole term is handed to the kernel for
        verification.
        """
        full_proof = self._wrap_cuts(proof)
        goal = self._goal or self._default_goal(proof)
        result = self._kernel.verify(self._ctx, goal, full_proof)
        self._history.append(ProofStep(
            tactic="conclude",
            args={},
            sub_proofs=[proof],
        ))
        return result

    # ── proof constructors (return ProofTerm) ────────────────────

    def refl(self, term: SynTerm) -> Refl:
        """Reflexivity: ``term = term``."""
        return Refl(term=term)

    def sym(self, proof: ProofTerm) -> Sym:
        """Symmetry: flip the sides of an equality proof."""
        return Sym(proof=proof)

    def trans(self, p1: ProofTerm, p2: ProofTerm) -> Trans:
        """Transitivity: chain two equality proofs."""
        return Trans(left=p1, right=p2)

    def cong(self, func: SynTerm, proof: ProofTerm) -> Cong:
        """Congruence: lift an equality through a function."""
        return Cong(func=func, proof=proof)

    def assume(self, name: str) -> Assume:
        """Reference a hypothesis from the context."""
        return Assume(name=name)

    def z3(self, formula: str) -> Z3Proof:
        """Discharge a formula to Z3."""
        return Z3Proof(formula=formula)

    def axiom(self, name: str, module: str = "") -> AxiomInvocation:
        """Invoke a registered axiom."""
        return AxiomInvocation(name=name, module=module)

    def unfold(self, func_name: str, then: ProofTerm | None = None) -> Unfold:
        """Unfold a function definition, optionally continuing with *then*."""
        return Unfold(func_name=func_name, proof=then)

    def rewrite(self, lemma: ProofTerm, then: ProofTerm | None = None) -> Rewrite:
        """Rewrite using *lemma*, optionally continuing with *then*."""
        return Rewrite(lemma=lemma, proof=then)

    def structural(self, desc: str = "") -> Structural:
        """Structural verification (weaker trust level)."""
        return Structural(description=desc)

    # ── induction tactics ────────────────────────────────────────

    def by_nat_induction(
        self, var: str, base: ProofTerm, step: ProofTerm
    ) -> NatInduction:
        """Natural-number induction on *var*."""
        return NatInduction(var=var, base_proof=base, step_proof=step)

    def by_list_induction(
        self, var: str, nil: ProofTerm, cons: ProofTerm
    ) -> ListInduction:
        """List induction on *var*."""
        return ListInduction(var=var, nil_proof=nil, cons_proof=cons)

    def by_cases(
        self, scrutinee: SynTerm, branches: list[tuple[str, ProofTerm]]
    ) -> Cases:
        """Case analysis on *scrutinee*."""
        return Cases(scrutinee=scrutinee, branches=branches)

    # ── duck typing ──────────────────────────────────────────────

    def duck_path(
        self,
        type_a: SynType,
        type_b: SynType,
        method_proofs: list[tuple[str, ProofTerm]],
    ) -> DuckPath:
        """Construct a duck-type path between two types."""
        return DuckPath(
            type_a=type_a, type_b=type_b, method_proofs=method_proofs,
        )

    # ── calc chains (Lean-style) ─────────────────────────────────

    def calc_chain(self, *steps: tuple[SynTerm, ProofTerm]) -> ProofTerm:
        """Build a transitivity chain from a series of (term, justification).

        Each successive pair is joined by ``Trans``.  For example::

            pb.calc_chain(
                (a, pb.refl(a)),          # a
                (b, some_proof_a_eq_b),   # = b  by …
                (c, some_proof_b_eq_c),   # = c  by …
            )

        produces ``Trans(some_proof_a_eq_b, some_proof_b_eq_c)``.
        """
        if len(steps) == 0:
            return Structural("empty calc chain")
        if len(steps) == 1:
            _term, proof = steps[0]
            return proof
        # Chain pairwise: ignore the first justification (it anchors
        # the chain); subsequent ones are joined via Trans.
        result: ProofTerm = steps[1][1]
        for i in range(2, len(steps)):
            result = Trans(left=result, right=steps[i][1])
        return result

    # ── effect proofs ────────────────────────────────────────────

    def with_effect(self, effect: str, proof: ProofTerm) -> EffectWitness:
        """Wrap a proof in an effect witness."""
        return EffectWitness(effect=effect, proof=proof)

    # ── transport ────────────────────────────────────────────────

    def transport(
        self,
        type_family: SynTerm,
        path: ProofTerm,
        base: ProofTerm,
    ) -> TransportProof:
        """Transport a proof along a path."""
        return TransportProof(
            type_family=type_family, path_proof=path, base_proof=base,
        )

    # ── function extensionality ──────────────────────────────────

    def ext(self, var: str, body_proof: ProofTerm) -> Ext:
        """Function extensionality: ∀x. f(x)=g(x) ⟹ f=g."""
        return Ext(var=var, body_proof=body_proof)

    # ── convenience: by ──────────────────────────────────────────

    def by(self, name: str) -> ProofTerm:
        """Look up a previously introduced hypothesis by name.

        If the hypothesis was introduced via ``have``, returns the
        proof that justified it.  Otherwise falls back to ``Assume``.
        """
        if name in self._hypotheses:
            return self._hypotheses[name]
        return Assume(name=name)

    # ── conversion to ProofScript ────────────────────────────────

    def to_script(self) -> ProofScript:
        """Snapshot the current history as a replayable ProofScript."""
        goal = self._goal or self._default_goal(Structural())
        return ProofScript(steps=list(self._history), goal=goal)

    # ── internal helpers ─────────────────────────────────────────

    def _wrap_cuts(self, final_proof: ProofTerm) -> ProofTerm:
        """Wrap accumulated ``have`` steps as nested ``Cut`` nodes."""
        if not self._steps:
            return final_proof

        result = final_proof
        for name, claim, lemma_proof in reversed(self._steps):
            result = Cut(
                hyp_name=name,
                hyp_type=RefinementType(
                    base_type=PyBoolType(),
                    predicate=claim,
                ),
                lemma_proof=lemma_proof,
                body_proof=result,
            )
        return result

    def _default_goal(self, proof: ProofTerm) -> Judgment:
        """Synthesise a default equality goal from a proof term.

        When the user did not supply an explicit goal we walk the
        proof term looking for a ``Refl`` leaf so we can construct
        ``Γ ⊢ t = t : PyObj``.  For terms that don't embed an
        obvious equality we fall back to a trivial type-check goal.
        """
        term = self._find_refl_term(proof)
        if term is not None:
            return Judgment(
                kind=JudgmentKind.EQUAL,
                context=self._ctx,
                left=term,
                right=term,
                type_=PyObjType(),
            )
        return Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=self._ctx,
            type_=PyObjType(),
        )

    @staticmethod
    def _find_refl_term(proof: ProofTerm) -> SynTerm | None:
        """Extract the term from a Refl buried inside wrappers."""
        if isinstance(proof, Refl):
            return proof.term
        if isinstance(proof, Sym):
            return ProofBuilder._find_refl_term(proof.proof)
        if isinstance(proof, Cut):
            return ProofBuilder._find_refl_term(proof.body_proof)
        if isinstance(proof, Trans):
            return ProofBuilder._find_refl_term(proof.left)
        return None


# ═══════════════════════════════════════════════════════════════════
#  Tactic Combinators
# ═══════════════════════════════════════════════════════════════════

def then(t1: ProofTerm, t2: ProofTerm) -> ProofTerm:
    """Sequence two proof terms: prove *t1* as a lemma and continue with *t2*.

    Compiled as ``Cut("_seq", ?, t1, t2)``.
    """
    return Cut(
        hyp_name="_seq",
        hyp_type=PyBoolType(),
        lemma_proof=t1,
        body_proof=t2,
    )


def try_tactic(primary: ProofTerm, fallback: ProofTerm) -> ProofTerm:
    """Return *primary* if it is a "safe" proof term, else *fallback*.

    At proof-construction time we cannot run verification, so this is
    a purely structural heuristic: if *primary* is ``Structural`` with
    an empty description we prefer the *fallback*.  In a full
    interactive prover the kernel would attempt the primary first and
    fall back on failure.
    """
    if isinstance(primary, Structural) and not primary.description:
        return fallback
    return primary


def repeat(tactic_fn: Callable[[], ProofTerm | None], max_times: int = 100) -> ProofTerm:
    """Repeatedly apply *tactic_fn* (up to *max_times*) and chain results.

    *tactic_fn* should return ``None`` when it can no longer make
    progress.  The accumulated proofs are chained via ``Trans``.
    """
    proofs: list[ProofTerm] = []
    for _ in range(max_times):
        p = tactic_fn()
        if p is None:
            break
        proofs.append(p)
    if not proofs:
        return Structural("repeat: no progress")
    result = proofs[0]
    for p in proofs[1:]:
        result = Trans(left=result, right=p)
    return result


# ═══════════════════════════════════════════════════════════════════
#  CommonProofs — library of reusable proof patterns
# ═══════════════════════════════════════════════════════════════════

class CommonProofs:
    """Library of common proof patterns.

    Every method returns a fully-formed ProofTerm that can be fed
    directly into a ProofBuilder or into the kernel.
    """

    @staticmethod
    def commutativity(op: str, a: SynTerm, b: SynTerm) -> ProofTerm:
        """``op(a, b) = op(b, a)`` — discharged to Z3 for arithmetic ops."""
        formula = f"{_term_str(a)} {op} {_term_str(b)} == {_term_str(b)} {op} {_term_str(a)}"
        return Z3Proof(formula=formula)

    @staticmethod
    def associativity(
        op: str, a: SynTerm, b: SynTerm, c: SynTerm
    ) -> ProofTerm:
        """``op(op(a, b), c) = op(a, op(b, c))``."""
        la, lb, lc = _term_str(a), _term_str(b), _term_str(c)
        formula = f"({la} {op} {lb}) {op} {lc} == {la} {op} ({lb} {op} {lc})"
        return Z3Proof(formula=formula)

    @staticmethod
    def identity(op: str, e: SynTerm, a: SynTerm) -> ProofTerm:
        """``op(e, a) = a`` (left identity)."""
        le, la = _term_str(e), _term_str(a)
        formula = f"{le} {op} {la} == {la}"
        return Z3Proof(formula=formula)

    @staticmethod
    def list_length_nonneg(lst: SynTerm) -> ProofTerm:
        """``len(lst) >= 0`` — structural / axiomatic."""
        return Structural(description=f"len({lst}) >= 0 by definition")

    @staticmethod
    def sorted_implies_min_first(lst: SynTerm) -> ProofTerm:
        """If *lst* is sorted then ``lst[0]`` is the minimum element."""
        return Structural(
            description=(
                f"sorted({lst}) => {lst}[0] = min({lst}) "
                "by definition of sorted order"
            ),
        )

    @staticmethod
    def reflexivity(term: SynTerm) -> ProofTerm:
        """``term = term``."""
        return Refl(term=term)

    @staticmethod
    def transitivity_chain(proofs: Sequence[ProofTerm]) -> ProofTerm:
        """Chain a non-empty sequence of equality proofs via Trans."""
        if not proofs:
            return Structural("empty chain")
        result = proofs[0]
        for p in proofs[1:]:
            result = Trans(left=result, right=p)
        return result

    @staticmethod
    def modus_ponens(
        implication: ProofTerm, premise: ProofTerm
    ) -> ProofTerm:
        """Modus ponens: from ``P ⟹ Q`` and ``P`` derive ``Q``.

        Encoded as ``Cut("_mp_premise", Bool, premise, implication)``.
        """
        return Cut(
            hyp_name="_mp_premise",
            hyp_type=PyBoolType(),
            lemma_proof=premise,
            body_proof=implication,
        )

    @staticmethod
    def contrapositive(proof: ProofTerm) -> ProofTerm:
        """Structural contrapositive: ``¬Q ⟹ ¬P`` from ``P ⟹ Q``."""
        return Structural(description=f"contrapositive of {proof}")

    @staticmethod
    def induction_on_nat(
        var: str, base: ProofTerm, step: ProofTerm
    ) -> NatInduction:
        """Standard natural-number induction."""
        return NatInduction(var=var, base_proof=base, step_proof=step)

    @staticmethod
    def induction_on_list(
        var: str, nil: ProofTerm, cons: ProofTerm
    ) -> ListInduction:
        """Standard list induction."""
        return ListInduction(var=var, nil_proof=nil, cons_proof=cons)


# ═══════════════════════════════════════════════════════════════════
#  Goal Helpers
# ═══════════════════════════════════════════════════════════════════

def equality_goal(
    ctx: Context, left: SynTerm, right: SynTerm,
    type_: SynType | None = None,
) -> Judgment:
    """Construct an equality judgment ``Γ ⊢ left = right : type_``."""
    return Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=left,
        right=right,
        type_=type_ or PyObjType(),
    )


def type_check_goal(
    ctx: Context, term: SynTerm, type_: SynType,
) -> Judgment:
    """Construct a type-checking judgment ``Γ ⊢ term : type_``."""
    return Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=term,
        type_=type_,
    )


def refinement_goal(
    ctx: Context, predicate: str,
    base_type: SynType | None = None,
) -> Judgment:
    """Construct a refinement type-checking goal."""
    return Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        type_=RefinementType(
            base_type=base_type or PyBoolType(),
            predicate=predicate,
        ),
    )


# ═══════════════════════════════════════════════════════════════════
#  Proof-tree pretty-printer
# ═══════════════════════════════════════════════════════════════════

def pretty_proof(proof: ProofTerm, indent: int = 0) -> str:
    """Return a human-readable, indented rendering of *proof*."""
    pad = "  " * indent
    lines: list[str] = []

    if isinstance(proof, Refl):
        lines.append(f"{pad}refl({proof.term})")
    elif isinstance(proof, Sym):
        lines.append(f"{pad}sym")
        lines.append(pretty_proof(proof.proof, indent + 1))
    elif isinstance(proof, Trans):
        lines.append(f"{pad}trans")
        lines.append(pretty_proof(proof.left, indent + 1))
        lines.append(pretty_proof(proof.right, indent + 1))
    elif isinstance(proof, Cong):
        lines.append(f"{pad}cong({proof.func})")
        lines.append(pretty_proof(proof.proof, indent + 1))
    elif isinstance(proof, Cut):
        lines.append(f"{pad}have {proof.hyp_name} : {proof.hyp_type}")
        lines.append(pretty_proof(proof.lemma_proof, indent + 1))
        lines.append(f"{pad}in")
        lines.append(pretty_proof(proof.body_proof, indent + 1))
    elif isinstance(proof, Assume):
        lines.append(f"{pad}assume({proof.name})")
    elif isinstance(proof, Z3Proof):
        lines.append(f"{pad}z3({proof.formula})")
    elif isinstance(proof, NatInduction):
        lines.append(f"{pad}nat_induction({proof.var})")
        lines.append(f"{pad}  base:")
        lines.append(pretty_proof(proof.base_proof, indent + 2))
        lines.append(f"{pad}  step:")
        lines.append(pretty_proof(proof.step_proof, indent + 2))
    elif isinstance(proof, ListInduction):
        lines.append(f"{pad}list_induction({proof.var})")
        lines.append(f"{pad}  nil:")
        lines.append(pretty_proof(proof.nil_proof, indent + 2))
        lines.append(f"{pad}  cons:")
        lines.append(pretty_proof(proof.cons_proof, indent + 2))
    elif isinstance(proof, Cases):
        lines.append(f"{pad}cases({proof.scrutinee})")
        for pat, bp in proof.branches:
            lines.append(f"{pad}  | {pat} =>")
            lines.append(pretty_proof(bp, indent + 3))
    elif isinstance(proof, DuckPath):
        lines.append(f"{pad}duck_path({proof.type_a} ≃ {proof.type_b})")
        for meth, mp in proof.method_proofs:
            lines.append(f"{pad}  .{meth}:")
            lines.append(pretty_proof(mp, indent + 3))
    elif isinstance(proof, EffectWitness):
        lines.append(f"{pad}with_effect({proof.effect})")
        lines.append(pretty_proof(proof.proof, indent + 1))
    elif isinstance(proof, AxiomInvocation):
        prefix = f"{proof.module}." if proof.module else ""
        lines.append(f"{pad}axiom({prefix}{proof.name})")
    elif isinstance(proof, Ext):
        lines.append(f"{pad}ext({proof.var})")
        lines.append(pretty_proof(proof.body_proof, indent + 1))
    elif isinstance(proof, Unfold):
        sub = f" then …" if proof.proof else ""
        lines.append(f"{pad}unfold({proof.func_name}){sub}")
        if proof.proof:
            lines.append(pretty_proof(proof.proof, indent + 1))
    elif isinstance(proof, Rewrite):
        lines.append(f"{pad}rewrite")
        lines.append(pretty_proof(proof.lemma, indent + 1))
        if proof.proof:
            lines.append(f"{pad}  then")
            lines.append(pretty_proof(proof.proof, indent + 2))
    elif isinstance(proof, Structural):
        desc = f"({proof.description})" if proof.description else ""
        lines.append(f"{pad}structural{desc}")
    elif isinstance(proof, TransportProof):
        lines.append(f"{pad}transport({proof.type_family})")
        lines.append(f"{pad}  path:")
        lines.append(pretty_proof(proof.path_proof, indent + 2))
        lines.append(f"{pad}  base:")
        lines.append(pretty_proof(proof.base_proof, indent + 2))
    else:
        lines.append(f"{pad}{proof!r}")

    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
#  Internal helpers
# ═══════════════════════════════════════════════════════════════════

def _term_str(t: SynTerm) -> str:
    """Best-effort conversion of a SynTerm to a Z3-friendly string."""
    if isinstance(t, Literal):
        return repr(t.value)
    if isinstance(t, Var):
        return t.name
    return repr(t)


# ═══════════════════════════════════════════════════════════════════
#  Self-tests
# ═══════════════════════════════════════════════════════════════════

if __name__ == "__main__":

    # ── 1.  Refl: 42 == 42 ───────────────────────────────────────
    kernel = ProofKernel()
    ctx = Context()
    pb = ProofBuilder(kernel, ctx)
    result = pb.conclude(pb.refl(Literal(42)))
    assert result.success, f"Refl(42) failed: {result}"
    print(f"  [1] Refl(42): {result}")

    # ── 2.  Sym of Refl ──────────────────────────────────────────
    pb2 = ProofBuilder(kernel, ctx)
    result2 = pb2.conclude(pb2.sym(pb2.refl(Literal(7))))
    assert result2.success, f"Sym(Refl(7)) failed: {result2}"
    print(f"  [2] Sym(Refl(7)): {result2}")

    # ── 3.  Have + conclude ──────────────────────────────────────
    pb3 = ProofBuilder(kernel, ctx)
    pb3.have("h", "True", pb3.structural("trivially true"))
    result3 = pb3.conclude(pb3.refl(Literal(0)))
    assert result3.success, f"Have+conclude failed: {result3}"
    print(f"  [3] Have + conclude: {result3}")

    # ── 4.  Calc chain ───────────────────────────────────────────
    a, b, c = Literal(1), Literal(2), Literal(3)
    pb4 = ProofBuilder(kernel, ctx)
    chain = pb4.calc_chain(
        (a, pb4.refl(a)),
        (b, pb4.structural("1 → 2")),
        (c, pb4.structural("2 → 3")),
    )
    assert isinstance(chain, Trans)
    print(f"  [4] Calc chain: {chain}")

    # ── 5.  CommonProofs ─────────────────────────────────────────
    comm = CommonProofs.commutativity("+", Literal(1), Literal(2))
    assert isinstance(comm, Z3Proof)
    print(f"  [5] Commutativity: {comm}")

    nonneg = CommonProofs.list_length_nonneg(Var("xs"))
    assert isinstance(nonneg, Structural)
    print(f"  [6] list_length_nonneg: {nonneg}")

    # ── 6.  Tactic combinators ───────────────────────────────────
    seq = then(Structural("step1"), Structural("step2"))
    assert isinstance(seq, Cut)
    print(f"  [7] then: {seq}")

    fallback = try_tactic(Structural(), Structural("real proof"))
    assert isinstance(fallback, Structural)
    assert fallback.description == "real proof"
    print(f"  [8] try_tactic: {fallback}")

    counter = iter(range(3))
    rep = repeat(lambda: Refl(Literal(next(counter, None))) if next(counter, None) is not None else None, max_times=5)
    print(f"  [9] repeat: {rep}")

    # ── 7.  Nat induction ────────────────────────────────────────
    pb5 = ProofBuilder(kernel, ctx)
    ind = pb5.by_nat_induction(
        "n", pb5.refl(Literal(0)), pb5.structural("inductive step"),
    )
    goal = equality_goal(ctx, Literal(0), Literal(0))
    res_ind = kernel.verify(ctx, goal, ind)
    assert res_ind.success, f"NatInduction failed: {res_ind}"
    print(f" [10] NatInduction: {res_ind}")

    # ── 8.  Pretty-printer ───────────────────────────────────────
    nested = Cut(
        hyp_name="lemma",
        hyp_type=PyBoolType(),
        lemma_proof=Refl(Literal(42)),
        body_proof=Trans(
            left=Assume("lemma"),
            right=Structural("done"),
        ),
    )
    pp = pretty_proof(nested)
    assert "have lemma" in pp
    print(f" [11] pretty_proof:\n{pp}")

    # ── 9.  ProofScript round-trip ───────────────────────────────
    pb6 = ProofBuilder(kernel, ctx, goal=equality_goal(ctx, Literal(1), Literal(1)))
    pb6.have("h", "1 == 1", pb6.refl(Literal(1)))
    script = pb6.to_script()
    assert len(script.steps) == 1
    term = script.to_proof_term()
    assert isinstance(term, (Cut, Refl, Structural))
    print(f" [12] ProofScript round-trip: {term}")

    # ── 10. Transport ────────────────────────────────────────────
    tp = pb.transport(Var("P"), pb.refl(Var("x")), pb.structural("base"))
    assert isinstance(tp, TransportProof)
    print(f" [13] Transport: {tp}")

    print("\nProof language smoke tests passed ✓")
