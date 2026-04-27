"""Construct every ProofTerm subclass deppy defines and submit each
to ``ProofKernel.verify``, recording the kernel's verdict.

Tasks C1–C7 from the audit.  Some ProofTerm shapes will be rejected
by the kernel (we don't have aligned SynTerm endpoints for many)
— that's the *honest* output of the kernel, not a bug.  What
matters here is that every ProofTerm subclass is exercised, so
the audit table can stop reading "27 of 38 never constructed".
"""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class ProofTermProbe:
    proof_term_class: str
    success: bool = False
    trust_level: str = ""
    message: str = ""
    error: str = ""


@dataclass
class ProofTermZooReport:
    probes: list[ProofTermProbe] = field(default_factory=list)

    @property
    def total(self) -> int:
        return len(self.probes)

    @property
    def kernel_accepted(self) -> int:
        return sum(1 for p in self.probes if p.success)


def _try_pt(
    name: str, build_fn, kernel, ctx, goal,
) -> ProofTermProbe:
    try:
        pt = build_fn()
        result = kernel.verify(ctx, goal, pt)
        return ProofTermProbe(
            proof_term_class=name,
            success=result.success,
            trust_level=result.trust_level.name,
            message=result.message[:80],
        )
    except Exception as e:
        return ProofTermProbe(
            proof_term_class=name, error=f"{type(e).__name__}: {e}",
        )


def probe_all_proofterms() -> ProofTermZooReport:
    """Construct every ProofTerm subclass and submit to the kernel."""
    from deppy.core.kernel import (
        ProofKernel,
        Refl, Sym, Trans, Cong, TransportProof, Ext, Cut, Assume,
        Z3Proof, LeanProof, NatInduction, ListInduction, Cases,
        DuckPath, ConditionalDuckPath, FiberedLookup, EffectWitness,
        ConditionalEffectWitness, SourceDischarge, SemanticSafetyWitness,
        ModuleSafetyComposition, TerminationObligation, SafetyObligation,
        Patch, Fiber, PathComp, Ap, FunExt, CechGlue, Univalence,
        Cocycle, CohomologyClass, KanFill, HigherPath, AxiomInvocation,
        Unfold, Rewrite, Structural,
    )
    from deppy.core.types import (
        Context, Judgment, JudgmentKind, Var, PyObjType, PyIntType,
        Literal, PyBoolType, RefinementType,
    )

    kernel = ProofKernel()
    kernel.register_axiom("test_ax", "True", module="probe")
    ctx = Context()
    a = Var("a")
    eq_goal = Judgment(
        kind=JudgmentKind.EQUAL, context=ctx,
        left=a, right=a, type_=PyObjType(),
    )
    tc_goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK, context=ctx,
        term=a, type_=PyObjType(),
    )

    out: list[ProofTermProbe] = []
    out.append(_try_pt("Refl", lambda: Refl(term=a), kernel, ctx, eq_goal))
    out.append(_try_pt("Sym", lambda: Sym(proof=Refl(term=a)), kernel, ctx, eq_goal))
    out.append(_try_pt(
        "Trans",
        lambda: Trans(left=Refl(term=a), right=Refl(term=a)),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "Cong", lambda: Cong(func=Var("f"), proof=Refl(term=a)),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "TransportProof",
        lambda: TransportProof(
            type_family=Var("P"),
            path_proof=Refl(term=a),
            base_proof=Refl(term=a),
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "Ext",
        lambda: Ext(var="x", body_proof=Refl(term=a)),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "Cut",
        lambda: Cut(
            hyp_name="h", hyp_type=PyObjType(),
            lemma_proof=Refl(term=a),
            body_proof=Refl(term=a),
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "Assume",
        lambda: Assume(name="h"),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "Z3Proof",
        lambda: Z3Proof(formula="a + 1 == 1 + a", binders={"a": "int"}),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "LeanProof",
        lambda: LeanProof(
            theorem="theorem t : True := by trivial",
            proof_script="trivial",
        ),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "NatInduction",
        lambda: NatInduction(
            var="n", base_proof=Refl(term=a), step_proof=Refl(term=a),
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "ListInduction",
        lambda: ListInduction(
            var="xs", nil_proof=Refl(term=a), cons_proof=Refl(term=a),
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "Cases",
        lambda: Cases(
            scrutinee=a,
            branches=[("Some", Refl(term=a)), ("None", Refl(term=a))],
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "DuckPath",
        lambda: DuckPath(
            type_a=PyIntType(), type_b=PyIntType(),
            method_proofs=[("foo", Refl(term=a))],
        ),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "ConditionalDuckPath",
        lambda: ConditionalDuckPath(
            condition="True", evidence=Refl(term=a),
            type_a=PyIntType(), type_b=PyIntType(),
        ),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "FiberedLookup",
        lambda: FiberedLookup(
            fiber_over="attr", base_path=Refl(term=a),
            transport_through="attr",
        ),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "EffectWitness",
        lambda: EffectWitness(
            effect="exception_free", proof=Structural("ok"),
        ),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "ConditionalEffectWitness",
        lambda: ConditionalEffectWitness(
            precondition="True", effect="exception_free",
            proof=Structural("ok"), target="probe",
        ),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "SourceDischarge",
        lambda: SourceDischarge(
            source_id="src1", failure_kind="ZERO_DIVISION",
            safety_predicate="b != 0",
            inner=Structural("ok"), note="probe",
        ),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "SemanticSafetyWitness",
        lambda: SemanticSafetyWitness(
            target="probe_fn", precondition="True",
            discharges=[], is_total_escape=False,
        ),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "ModuleSafetyComposition",
        lambda: ModuleSafetyComposition(
            module_path="probe", function_witnesses={},
            module_discharges=[], internal_calls_closed=True,
        ),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "TerminationObligation",
        lambda: TerminationObligation(
            target="f", measure_at_entry="len(xs)",
            measure_at_recursive_call="len(xs) - 1",
            precondition="True", inner=Structural("ok"),
            note="probe",
        ),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "SafetyObligation",
        lambda: SafetyObligation(
            obligation_id="ob1", safety_condition="x >= 0",
            proof=Structural("ok"), failure_kind="GENERIC",
            lineno=1,
        ),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "Patch",
        lambda: Patch(
            cls=Var("C"), method_name="m",
            new_impl=Var("v"), contract_proof=Refl(term=a),
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "Fiber",
        lambda: Fiber(
            scrutinee=a,
            type_branches=[(PyIntType(), Refl(term=a))],
            exhaustive=True,
        ),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "PathComp",
        lambda: PathComp(
            left_path=Refl(term=a), right_path=Refl(term=a),
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "Ap",
        lambda: Ap(function=Var("f"), path_proof=Refl(term=a)),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "FunExt",
        lambda: FunExt(var="x", pointwise_proof=Refl(term=a)),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "CechGlue",
        lambda: CechGlue(
            patches=[("True", Refl(term=a))],
            overlap_proofs=[],
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "Univalence",
        lambda: Univalence(
            equiv_proof=Refl(term=a),
            from_type=PyIntType(), to_type=PyIntType(),
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "Cocycle",
        lambda: Cocycle(
            level=1, components=[Refl(term=a)],
            boundary_pairs=[], overlap_proofs=[],
            boundary_zero=True, label="probe",
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "CohomologyClass",
        lambda: CohomologyClass(
            level=1,
            cocycle=Cocycle(
                level=1, components=[Refl(term=a)],
                boundary_pairs=[], overlap_proofs=[],
                boundary_zero=True, label="probe",
            ),
            coboundary_witness=None, class_id="probe_class",
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "KanFill",
        lambda: KanFill(
            dimension=2, faces=[Refl(term=a), Refl(term=a)],
            face_endpoints=[(a, a), (a, a)],
            missing_face_label="axis_0_eps_1",
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "HigherPath",
        lambda: HigherPath(
            dimension=2, vertices=[a, a],
            boundary_proofs=[Refl(term=a)],
            boundary_endpoints=[(a, a)],
        ),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "AxiomInvocation",
        lambda: AxiomInvocation(name="test_ax", module="probe"),
        kernel, ctx, tc_goal,
    ))
    out.append(_try_pt(
        "Unfold",
        lambda: Unfold(func_name="f", proof=Refl(term=a)),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "Rewrite",
        lambda: Rewrite(lemma=Refl(term=a)),
        kernel, ctx, eq_goal,
    ))
    out.append(_try_pt(
        "Structural",
        lambda: Structural(description="probe"),
        kernel, ctx, tc_goal,
    ))

    return ProofTermZooReport(probes=out)


__all__ = ["ProofTermProbe", "ProofTermZooReport", "probe_all_proofterms"]
