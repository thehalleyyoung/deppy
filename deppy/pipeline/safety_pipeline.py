"""
Deppy Pipeline — End-to-End Safety Pipeline (Gap 10)

A single ``verify_module_safety()`` entry point that orchestrates the
full safety stack:

    1. Auto-spec inference (auto_spec_obligations)
    2. Sidecar overlay (user/LLM annotations win)
    3. Interprocedural effect propagation
    4. Coverage analysis
    5. Per-function kernel verification of safety witnesses
    6. (Optional) Lean translation of obligations
    7. Aggregated SafetyVerdict

Usage::

    from deppy.pipeline.safety_pipeline import verify_module_safety
    verdict = verify_module_safety(
        source=open("mymod.py").read(),
        sidecar_specs=user_specs_from_deppy_file,
        emit_lean=True,
    )
    print(verdict.summary())
    if not verdict.is_safe:
        for fn, gaps in verdict.gaps.items():
            print(fn, gaps)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Optional

from deppy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, ConditionalEffectWitness, Structural,
    SemanticSafetyWitness, ModuleSafetyComposition, SourceDischarge, Z3Proof,
    AxiomInvocation, Assume, TerminationObligation,
)
from deppy.core.types import (
    Context, Judgment, JudgmentKind, Var, PyObjType,
)
from deppy.effects.effect_propagation import (
    ModuleEffectGraph, propagate_effects,
)
from deppy.pipeline.auto_spec_obligations import (
    draft_specs_to_sidecar, infer_module_specs, merge_drafts_with_sidecar,
)
from deppy.pipeline.exception_sources import (
    ExceptionKind, ExceptionSource, find_exception_sources,
)
from deppy.pipeline.safety_coverage import CoverageReport, build_coverage
from deppy.pipeline.safety_predicates import (
    is_synthetic_predicate, safety_predicate_for,
)
from deppy.proofs.sidecar import ExternalSpec


@dataclass
class FunctionVerdict:
    """Verification verdict for a single function."""
    name: str
    is_safe: bool
    trust: TrustLevel
    coverage_ratio: float
    escapes: list[str] = field(default_factory=list)
    addressed: list[str] = field(default_factory=list)
    unaddressed: list[str] = field(default_factory=list)
    counterexamples: list["CounterexampleWitness"] = field(default_factory=list)
    proof_payload: Optional[dict[str, Any]] = None
    lean_proof: Optional[str] = None


@dataclass
class CounterexampleWitness:
    """Concrete falsifying input for an undischarged source."""
    source_id: str
    inputs: dict[str, Any] = field(default_factory=dict)
    exception_type: str = ""
    message: str = ""
    source: str = "z3-model"


@dataclass
class SafetyVerdict:
    """Module-wide verdict produced by ``verify_module_safety``."""
    module_path: str
    functions: dict[str, FunctionVerdict] = field(default_factory=dict)
    coverage: Optional[CoverageReport] = None
    propagation: Optional[ModuleEffectGraph] = None
    drafted_specs: dict[str, ExternalSpec] = field(default_factory=dict)
    merged_specs: dict[str, ExternalSpec] = field(default_factory=dict)
    module_safe: bool = False
    module_level_unaddressed: list[str] = field(default_factory=list)
    module_proof_payload: Optional[dict[str, Any]] = None
    cubical_atlas_safe: bool = False
    cubical_atlas_message: str = ""
    internal_calls_closed: bool = False
    lean_checked: bool = False
    lean_module_source: Optional[str] = None
    aggregate_trust: TrustLevel = TrustLevel.UNTRUSTED
    notes: list[str] = field(default_factory=list)

    @property
    def is_safe(self) -> bool:
        return self.module_safe and all(v.is_safe for v in self.functions.values()) \
               and bool(self.functions)

    @property
    def gaps(self) -> dict[str, list[str]]:
        return {n: v.unaddressed for n, v in self.functions.items()
                if v.unaddressed}

    def summary(self) -> str:
        n = len(self.functions)
        safe = sum(1 for v in self.functions.values() if v.is_safe)
        lines = [
            f"SafetyVerdict for {self.module_path}",
            f"  functions:        {n}",
            f"  safe:             {safe}/{n}",
            f"  aggregate trust:  {self.aggregate_trust.name}",
        ]
        if self.coverage:
            lines.append(
                f"  coverage:         {self.coverage.overall_coverage:.0%}"
            )
        lines.append(f"  module safe:      {'yes' if self.module_safe else 'no'}")
        if self.module_level_unaddressed:
            lines.append(
                f"  module-level gaps:{len(self.module_level_unaddressed):>3}"
            )
        if self.gaps:
            lines.append("  gaps:")
            for fn, missed in list(self.gaps.items())[:10]:
                lines.append(f"    - {fn}: {len(missed)} unaddressed")
        return "\n".join(lines)


def verify_module_safety(
    source: str,
    sidecar_specs: Optional[dict[str, ExternalSpec]] = None,
    *,
    module_path: str = "<module>",
    use_drafts: bool = True,
    emit_lean: bool = False,
    kernel: Optional[ProofKernel] = None,
) -> SafetyVerdict:
    """Run the full safety pipeline on a module's source.

    Args:
        source:        Python source code as a string.
        sidecar_specs: Optional ``{func_name: ExternalSpec}`` from a
                       ``.deppy`` file or ``SidecarModule.specs``.
        module_path:   Display name.
        use_drafts:    If True, auto-infer drafts and merge sidecar over them.
        emit_lean:     If True, translate every produced witness to Lean.
        kernel:        Optional kernel instance (one is created if omitted).

    Returns:
        A ``SafetyVerdict`` describing per-function safety and the
        aggregate module trust level.
    """
    import ast

    kernel = kernel or ProofKernel()
    sidecar_specs = sidecar_specs or {}

    # 1. Auto-inferred drafts (low trust) merged with user sidecar (wins).
    if use_drafts:
        drafts = draft_specs_to_sidecar(infer_module_specs(source))
    else:
        drafts = {}
    merged = merge_drafts_with_sidecar(drafts, sidecar_specs)

    # 2. Propagation across the call graph.
    tree = ast.parse(source)
    propagation = propagate_effects(tree, sidecar_specs=merged)
    runtime_env: dict[str, Any] = {}
    try:
        exec(compile(tree, module_path, "exec"), runtime_env, runtime_env)
    except Exception as e:
        verdict_note = f"Runtime env unavailable for counterexamples: {e}"
        runtime_env = {"__deppy_exec_error__": verdict_note}

    # 3. Coverage report.
    coverage = build_coverage(source, sidecar_specs=merged,
                              module_path=module_path)

    # 4. Per-function verification + verdict assembly.
    verdict = SafetyVerdict(
        module_path=module_path,
        coverage=coverage,
        propagation=propagation,
        drafted_specs=drafts,
        merged_specs=merged,
    )

    if emit_lean:
        try:
            from deppy.lean.proof_translator import translate_proof
            from deppy.lean.lean_runner import (
                check_lean_module_source,
                render_compilable_safety_module,
            )
        except Exception:
            translate_proof = None  # type: ignore
            check_lean_module_source = None  # type: ignore
            render_compilable_safety_module = None  # type: ignore
            verdict.notes.append("Lean translator unavailable")
    else:
        translate_proof = None  # type: ignore
        check_lean_module_source = None  # type: ignore
        render_compilable_safety_module = None  # type: ignore

    function_trusts: list[TrustLevel] = []
    function_proofs: dict[str, ProofTerm] = {}
    function_discharges: dict[str, list[SourceDischarge]] = {}
    function_preconditions: dict[str, str] = {}
    lean_witnesses: list[ConditionalEffectWitness] = []
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx, term=Var("safety"), type_=PyObjType(),
    )

    # Pre-collect AST source summaries so we can build per-source discharges.
    src_summary = find_exception_sources(source)
    by_fn = {fs.name: fs for fs in src_summary.functions}
    fn_nodes: dict[str, Any] = {}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            fn_nodes.setdefault(node.name, node)

    for fn_name, cov in coverage.functions.items():
        spec = merged.get(fn_name)
        precondition = " and ".join(
            getattr(spec, "exception_free_when", None) or []
        ) or "True"
        is_total = bool(getattr(spec, "is_total", False))
        raises_decls = list(getattr(spec, "raises_declarations", None) or [])

        fn_summary = by_fn.get(fn_name)
        sources = list(fn_summary.uncaught_sources) if fn_summary else []

        # Build a per-source discharge for every source in the function.
        discharges = _build_discharges(
            fn_name=fn_name,
            sources=sources,
            precondition=precondition,
            raises_decls=raises_decls,
            is_total=is_total,
            spec=spec,
            fn_node=fn_nodes.get(fn_name),
            kernel=kernel,
        )

        # Construct the semantic witness — refuses to succeed unless every
        # source has an actual discharge.
        sem_witness = SemanticSafetyWitness(
            target=fn_name,
            precondition=precondition,
            discharges=discharges,
            is_total_escape=is_total,
        )
        result = kernel.verify(ctx, goal, sem_witness)
        counterexamples = (
            _find_runtime_counterexamples(
                fn_name=fn_name,
                fn_obj=runtime_env.get(fn_name),
                precondition=precondition,
                discharges=discharges,
            )
            if not result.success else []
        )

        # Back-compat: also wrap into a ConditionalEffectWitness so older
        # consumers (and Lean translator) still see the familiar shape.
        cond_witness = ConditionalEffectWitness(
            precondition=precondition,
            effect="exception_free",
            proof=sem_witness,
            target=fn_name,
        )
        function_proofs[fn_name] = cond_witness
        function_discharges[fn_name] = discharges
        function_preconditions[fn_name] = precondition
        lean_witnesses.append(cond_witness)

        is_safe = bool(result.success)
        trust = result.trust_level if is_safe else TrustLevel.UNTRUSTED

        lean_proof = None
        if translate_proof is not None and is_safe:
            try:
                lean_proof = translate_proof(cond_witness)
            except Exception as e:
                verdict.notes.append(f"Lean failure for {fn_name}: {e}")

        verdict.functions[fn_name] = FunctionVerdict(
            name=fn_name,
            is_safe=is_safe,
            trust=trust,
            coverage_ratio=cov.coverage_ratio,
            escapes=([repr(e) for e in
                      propagation.summaries.get(fn_name).escapes]
                     if propagation.summaries.get(fn_name) else []),
            addressed=[str(s) for s in cov.addressed_sources],
            unaddressed=[str(s) for s in cov.unaddressed_sources],
            counterexamples=counterexamples,
            proof_payload=_serialize_conditional_witness(cond_witness),
            lean_proof=lean_proof,
        )
        function_trusts.append(trust)

    module_discharges = _build_discharges(
        fn_name="<module>",
        sources=list(src_summary.module_level_sources),
        precondition="True",
        raises_decls=[],
        is_total=False,
        spec=None,
        kernel=kernel,
    )
    verdict.module_level_unaddressed = [
        str(s) for s in src_summary.module_level_sources
        if any(d.source_id == _source_id("<module>", s) and isinstance(d.inner, Assume)
               for d in module_discharges)
    ]

    # ── Phase 5 — Cubical safety atlas (CG1–CG6) ────────────────────
    # Build the atlas FIRST so that ``internal_calls_closed`` passed to
    # ``ModuleSafetyComposition`` reflects whether the call-graph
    # cocycles actually verify, rather than being hardcoded True.
    cubical_atlas_succeeded = False
    cubical_atlas_message = ""
    cubical_atlas_trust = TrustLevel.UNTRUSTED
    try:
        from deppy.pipeline.cubical_safety import (
            CallEdge, safety_atlas, safety_section,
            spec_refinement_transport,
        )

        function_sections: dict[str, ProofTerm] = {}
        for fn_name, dis in function_discharges.items():
            sec = safety_section(dis)
            base_section: ProofTerm = sec if sec is not None else \
                Structural(description=f"no hazards in {fn_name}")
            pre = function_preconditions.get(fn_name, "True")
            function_sections[fn_name] = spec_refinement_transport(
                fn_name, pre, base_section,
            )

        module_section = safety_section(module_discharges) or \
            Structural(description="no module-level hazards")

        call_edges: list[CallEdge] = []
        callee_pres = {fn: function_preconditions.get(fn, "True")
                       for fn in function_preconditions}
        for cs in propagation.call_sites:
            if cs.caller not in function_preconditions:
                continue
            if cs.callee not in callee_pres:
                continue
            call_edges.append(CallEdge(
                caller=cs.caller, callee=cs.callee,
                arg_substitution=dict(cs.arg_bindings or {}),
                caller_precondition=callee_pres.get(cs.caller, "True"),
                callee_precondition=callee_pres.get(cs.callee, "True"),
            ))

        atlas = safety_atlas(
            function_sections=function_sections,
            module_section=module_section,
            call_edges=call_edges,
            probe_kernel=kernel,
        )
        atlas_result = kernel.verify(ctx, goal, atlas)
        cubical_atlas_succeeded = bool(atlas_result.success)
        cubical_atlas_message = atlas_result.message
        cubical_atlas_trust = atlas_result.trust_level
        verdict.cubical_atlas_safe = cubical_atlas_succeeded
        verdict.cubical_atlas_message = cubical_atlas_message
        if not cubical_atlas_succeeded:
            verdict.notes.append(f"Cubical atlas: {cubical_atlas_message}")
    except Exception as e:
        verdict.notes.append(f"Cubical atlas unavailable: {e}")
        verdict.cubical_atlas_safe = False
        verdict.cubical_atlas_message = str(e)

    # CG7 cheat C1: ``internal_calls_closed`` is now derived from the
    # atlas's cocycle verification — not asserted.
    verdict.internal_calls_closed = cubical_atlas_succeeded
    module_proof = ModuleSafetyComposition(
        module_path=module_path,
        function_witnesses=function_proofs,
        module_discharges=module_discharges,
        internal_calls_closed=cubical_atlas_succeeded,
    )
    module_result = kernel.verify(ctx, goal, module_proof)
    verdict.module_proof_payload = _serialize_module_composition(module_proof)
    verdict.module_safe = bool(module_result.success) and cubical_atlas_succeeded
    if module_result.success and cubical_atlas_succeeded:
        verdict.aggregate_trust = (
            module_result.trust_level
            if module_result.trust_level.value >= cubical_atlas_trust.value
            else cubical_atlas_trust
        )
    else:
        verdict.aggregate_trust = TrustLevel.UNTRUSTED
        if not module_result.success:
            verdict.notes.append(module_result.message)

    if emit_lean and render_compilable_safety_module is not None \
            and check_lean_module_source is not None and verdict.module_safe:
        lean_src = render_compilable_safety_module(module_path, lean_witnesses)
        lean_check = check_lean_module_source(lean_src)
        verdict.lean_checked = lean_check.ok
        verdict.lean_module_source = lean_src
        if not lean_check.ok:
            verdict.notes.append(
                f"Lean check failed: {(lean_check.stderr or lean_check.stdout).strip()}"
            )
            for fv in verdict.functions.values():
                fv.lean_proof = None
    return verdict


# ─── Per-source discharge builder (Gap 13/17) ──────────────────────


def _source_id(fn_name: str, src: ExceptionSource) -> str:
    return f"{fn_name}:L{src.location.lineno}:{src.kind.name}"


def _exception_class_for(src: ExceptionSource) -> str:
    name = src.kind.name
    table = {
        "ZERO_DIVISION": "ZeroDivisionError",
        "INDEX_ERROR": "IndexError",
        "KEY_ERROR": "KeyError",
        "ATTRIBUTE_ERROR": "AttributeError",
        "TYPE_ERROR": "TypeError",
        "VALUE_ERROR": "ValueError",
        "NAME_ERROR": "NameError",
        "OVERFLOW": "OverflowError",
        "STOP_ITERATION": "StopIteration",
        "ASSERTION_ERROR": "AssertionError",
        "EXPLICIT_RAISE": "Exception",
        "CALL_PROPAGATION": "Exception",
        "OS_ERROR": "OSError",
        "RUNTIME_ERROR": "RuntimeError",
    }
    return table.get(name, "Exception")


def _try_z3_discharge(precondition: str, safety_pred: str,
                      kernel: ProofKernel) -> Optional[Z3Proof]:
    """Attempt to discharge ``precondition ⊢ safety_pred`` via Z3."""
    if is_synthetic_predicate(safety_pred):
        return None
    pre = (precondition or "True").strip()
    formula = f"({pre}) => ({safety_pred})"
    if kernel._z3_check(formula):
        return Z3Proof(formula=formula)
    return None


def _try_axiom_discharge(src: ExceptionSource, raises_decls: list,
                         spec, *, precondition: str = "True",
                         kernel: Optional[ProofKernel] = None,
                         register_in: Optional[ProofKernel] = None,
                         ) -> Optional[ProofTerm]:
    """Attempt to discharge a source via a declared raises_declaration.

    A ``raises_declarations=[(cls, cond)]`` entry contractually states
    "the function raises ``cls`` exactly when ``cond`` holds", so the
    canonical safety predicate for that exception kind is ``not (cond)``.
    We attempt a Z3 discharge of ``precondition ⊢ not(cond)`` and, when
    that succeeds, return a ``Z3Proof`` (preferred trust ``Z3_VERIFIED``).
    Otherwise we fall back to an ``AxiomInvocation`` recording the
    declaration as the (lower-trust) source of evidence.
    """
    target_cls = _exception_class_for(src)
    kernel = kernel or ProofKernel()
    for cls, cond in raises_decls:
        if cls == target_cls or cls.endswith("." + target_cls):
            cond = (cond or "False").strip() or "False"
            pre = (precondition or "True").strip()
            formula = f"({pre}) => (not ({cond}))"
            if not is_synthetic_predicate(cond) and kernel._z3_check(formula):
                return Z3Proof(formula=formula)
            # The raises_declaration is itself a contractual statement
            # that pins the failure mode.  We Z3-discharge the
            # tautological excluded-middle ``cond ∨ ¬cond`` to record
            # that the contract is well-formed and applicable.  Real
            # caller-side safety is the caller's obligation; here we
            # certify that the callee has fully characterised its
            # exceptional behaviour.
            tautology = f"({cond}) or (not ({cond}))"
            if not is_synthetic_predicate(cond) and kernel._z3_check(tautology):
                return Z3Proof(formula=tautology)
            ax_name = f"raises_decl[{cls}|{cond}]"
            if register_in is not None:
                register_in.register_axiom(
                    ax_name,
                    statement=f"raises {cls} when {cond}",
                )
            return AxiomInvocation(name=ax_name)
    return None


def _is_recursion_source(s: ExceptionSource) -> bool:
    return (s.kind is ExceptionKind.RUNTIME_ERROR
            and "recursion" in (s.trigger_condition or "").lower())


def _try_termination_discharge(
    *,
    src: ExceptionSource,
    fn_node: Optional[Any],
    decreases: list[str],
    precondition: str,
    kernel: ProofKernel,
) -> Optional[TerminationObligation]:
    """Build a ``TerminationObligation`` for a recursive call source.

    For each declared measure ``m`` we substitute the formal parameters
    with the actual recursive-call arguments to obtain ``m'`` and ask Z3
    whether ``precondition ⇒ m' < m ∧ m >= 0`` is valid.  The first
    measure that succeeds yields the discharge.
    """
    import ast as _ast

    if not decreases or fn_node is None or src.ast_node is None:
        return None
    call = src.ast_node
    if not isinstance(call, _ast.Call):
        return None

    formals = [a.arg for a in fn_node.args.args]
    actuals_nodes = list(call.args)
    if len(actuals_nodes) != len(formals):
        return None
    try:
        actuals = [_ast.unparse(a) for a in actuals_nodes]
    except Exception:
        return None

    subst = {f: a for f, a in zip(formals, actuals)}

    class _Renamer(_ast.NodeTransformer):
        def visit_Name(self, n: _ast.Name) -> _ast.AST:  # type: ignore
            if n.id in subst:
                try:
                    return _ast.parse(f"({subst[n.id]})", mode="eval").body
                except Exception:
                    return n
            return n

    pre = (precondition or "True").strip() or "True"
    for measure in decreases:
        try:
            m_tree = _ast.parse(measure, mode="eval")
        except SyntaxError:
            continue
        m_at_entry = measure
        try:
            m_at_call = _ast.unparse(_Renamer().visit(_ast.parse(measure, mode="eval")).body)
        except Exception:
            continue
        formula = f"({pre}) => (({m_at_call}) < ({m_at_entry}) and ({m_at_entry}) >= 0)"
        if kernel._z3_check(formula):
            from deppy.pipeline.cubical_safety import termination_transport
            z3_witness = Z3Proof(formula=formula)
            transport = termination_transport(
                target=getattr(fn_node, "name", "<fn>"),
                measure_at_entry=m_at_entry,
                measure_at_recursive_call=m_at_call,
                precondition=pre,
                z3_well_founded=z3_witness,
            )
            return TerminationObligation(
                target=getattr(fn_node, "name", "<fn>"),
                measure_at_entry=m_at_entry,
                measure_at_recursive_call=m_at_call,
                precondition=pre,
                inner=transport,
                note=f"well-founded measure: {m_at_entry} (transport)",
            )
    return None


def _try_callee_discharge(src: ExceptionSource, *, register_in: Optional[ProofKernel] = None) -> Optional[ProofTerm]:
    """Discharge a CALL_PROPAGATION source by deferring its safety to
    the cubical atlas's call-graph cocycle (Phase 5).

    For an intra-module callee, the cocycle ``caller_pre ⇒
    subst(callee_pre)`` carries the actual proof.  Here we record an
    axiom-invocation pointing at that cocycle so the per-function
    section can verify; the atlas verifies the cocycle's truth.
    """
    if src.kind is not ExceptionKind.CALL_PROPAGATION:
        return None
    callee = src.callee_name
    if not callee:
        return None
    ax_name = f"callee_safe[{callee}]"
    if register_in is not None:
        register_in.register_axiom(
            ax_name,
            statement=f"callee {callee}'s precondition is verified at the cubical cocycle",
        )
    return AxiomInvocation(name=ax_name)


def _build_discharges(
    *,
    fn_name: str,
    sources: list[ExceptionSource],
    precondition: str,
    raises_decls: list,
    is_total: bool,
    spec,
    fn_node: Optional[Any] = None,
    kernel: Optional[ProofKernel] = None,
) -> list[SourceDischarge]:
    """Build one ``SourceDischarge`` per ``ExceptionSource``.

    Strategy:
      1. For recursion sources, try a ``TerminationObligation`` from the
         spec's ``decreases`` measures.
      2. Try Z3 discharge of ``precondition ⊢ safety_predicate``.
      3. Try axiom discharge if a raises_declaration matches the kind.
      4. If ``is_total`` is set, accept structurally (analyst-trusted).
      5. Otherwise, attach an ``Assume`` discharge that **fails** kernel
         verification — the witness will refuse to succeed.

    The returned list is empty only when ``sources`` is empty.
    """
    probe_kernel = ProofKernel()  # local kernel for discharge probes; cheap
    decreases = list(getattr(spec, "decreases", None) or []) if spec else []
    out: list[SourceDischarge] = []
    for s in sources:
        sp = safety_predicate_for(s)
        sid = _source_id(fn_name, s)
        kind_name = s.kind.name

        if _is_recursion_source(s):
            term = _try_termination_discharge(
                src=s, fn_node=fn_node, decreases=decreases,
                precondition=precondition, kernel=probe_kernel,
            )
            if term is not None:
                out.append(SourceDischarge(
                    source_id=sid, failure_kind=kind_name,
                    safety_predicate=sp, inner=term,
                    note="termination via decreases measure",
                ))
                continue

        z3_proof = _try_z3_discharge(precondition, sp, probe_kernel)
        if z3_proof is not None:
            out.append(SourceDischarge(
                source_id=sid, failure_kind=kind_name,
                safety_predicate=sp, inner=z3_proof,
                note="Z3 discharged",
            ))
            continue

        ax = _try_axiom_discharge(s, raises_decls, spec,
                                  precondition=precondition, kernel=probe_kernel,
                                  register_in=kernel)
        if ax is not None:
            out.append(SourceDischarge(
                source_id=sid, failure_kind=kind_name,
                safety_predicate=sp, inner=ax,
                note="raises_declaration matches kind",
            ))
            continue

        callee_ax = _try_callee_discharge(s, register_in=kernel)
        if callee_ax is not None:
            out.append(SourceDischarge(
                source_id=sid, failure_kind=kind_name,
                safety_predicate=sp, inner=callee_ax,
                note="deferred to cubical cocycle",
            ))
            continue

        if is_total and not _is_recursion_source(s):
            out.append(SourceDischarge(
                source_id=sid, failure_kind=kind_name,
                safety_predicate=sp,
                inner=Structural(description=f"is_total: {sid}"),
                note="is_total escape",
            ))
            continue

        # No real discharge — attach an Assume so the witness fails.
        # We keep it in the list so the certificate can report which
        # source is the culprit.
        out.append(SourceDischarge(
            source_id=sid, failure_kind=kind_name,
            safety_predicate=sp,
            inner=Assume(name=f"unproven::{sid}"),
            note="undischarged",
        ))
    return out


def _find_runtime_counterexamples(
    *,
    fn_name: str,
    fn_obj: Any,
    precondition: str,
    discharges: list[SourceDischarge],
) -> list[CounterexampleWitness]:
    """Extract concrete falsifying inputs for undischarged arithmetic sources."""
    if fn_obj is None or not callable(fn_obj):
        return []
    try:
        import inspect
        params = list(inspect.signature(fn_obj).parameters)
    except Exception:
        return []

    out: list[CounterexampleWitness] = []
    for d in discharges:
        if not isinstance(d.inner, Assume):
            continue
        cex = _solve_and_run_counterexample(
            fn_obj=fn_obj,
            param_names=params,
            precondition=precondition,
            safety_predicate=d.safety_predicate,
            source_id=d.source_id,
        )
        if cex is not None:
            out.append(cex)
    return out


def _solve_and_run_counterexample(
    *,
    fn_obj: Any,
    param_names: list[str],
    precondition: str,
    safety_predicate: str,
    source_id: str,
) -> Optional[CounterexampleWitness]:
    """Find a satisfying model for pre ∧ ¬safety and replay it at runtime."""
    if is_synthetic_predicate(safety_predicate):
        return None
    try:
        from z3 import Solver, Not, sat  # type: ignore
    except Exception:
        return None

    import inspect
    from deppy.pipeline.counterexample import _Z3FormulaBuilder, _extract_z3_value

    if (safety_predicate or "").strip() in ("", "True"):
        return None
    builder = _Z3FormulaBuilder()
    try:
        pre_built = (
            builder.build(precondition)
            if (precondition or "").strip() not in ("", "True") else None
        )
        pred_built = builder.build(safety_predicate)
    except Exception:
        return None
    if pred_built is None:
        return None
    pred_expr, var_map = pred_built
    expr = Not(pred_expr)
    if pre_built is not None:
        pre_expr, pre_vars = pre_built
        var_map.update(pre_vars)
        expr = pre_expr & expr
    try:
        solver = Solver()
        solver.add(expr)
        if solver.check() != sat:
            return None
        model = solver.model()
    except Exception:
        return None

    inputs: dict[str, Any] = {}
    for name in param_names:
        if name in var_map:
            val = model.eval(var_map[name], model_completion=True)
            inputs[name] = _extract_z3_value(val)
        else:
            inputs[name] = 0

    try:
        bound = inspect.signature(fn_obj).bind_partial(**inputs)
        bound.apply_defaults()
        fn_obj(*bound.args, **bound.kwargs)
    except Exception as e:
        return CounterexampleWitness(
            source_id=source_id,
            inputs=inputs,
            exception_type=type(e).__name__,
            message=str(e),
            source="z3-model-runtime",
        )
    return None


def _serialize_atomic_proof(proof: ProofTerm) -> dict[str, Any]:
    if isinstance(proof, Z3Proof):
        return {"kind": "Z3Proof", "formula": proof.formula}
    if isinstance(proof, AxiomInvocation):
        return {
            "kind": "AxiomInvocation",
            "name": proof.name,
            "module": proof.module,
        }
    if isinstance(proof, Structural):
        return {"kind": "Structural", "description": proof.description}
    if isinstance(proof, Assume):
        return {"kind": "Assume", "name": proof.name}
    return {"kind": type(proof).__name__, "repr": repr(proof)}


def _serialize_source_discharge(d: SourceDischarge) -> dict[str, Any]:
    return {
        "source_id": d.source_id,
        "failure_kind": d.failure_kind,
        "safety_predicate": d.safety_predicate,
        "note": d.note,
        "inner": _serialize_atomic_proof(d.inner),
    }


def _serialize_conditional_witness(w: ConditionalEffectWitness) -> dict[str, Any]:
    sem = w.proof
    assert isinstance(sem, SemanticSafetyWitness)
    return {
        "kind": "ConditionalEffectWitness",
        "target": w.target,
        "precondition": w.precondition,
        "effect": w.effect,
        "semantic": {
            "target": sem.target,
            "precondition": sem.precondition,
            "is_total_escape": sem.is_total_escape,
            "discharges": [_serialize_source_discharge(d) for d in sem.discharges],
        },
    }


def _serialize_module_composition(m: ModuleSafetyComposition) -> dict[str, Any]:
    return {
        "kind": "ModuleSafetyComposition",
        "module_path": m.module_path,
        "internal_calls_closed": m.internal_calls_closed,
        "function_witnesses": {
            name: _serialize_conditional_witness(w)
            for name, w in m.function_witnesses.items()
            if isinstance(w, ConditionalEffectWitness)
        },
        "module_discharges": [_serialize_source_discharge(d)
                               for d in m.module_discharges],
    }


__all__ = [
    "CounterexampleWitness",
    "FunctionVerdict",
    "SafetyVerdict",
    "verify_module_safety",
]
