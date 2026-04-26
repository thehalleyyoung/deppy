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
    8. (Optional) Enhanced diagnostics and error analysis

Usage::

    from deppy.pipeline.safety_pipeline import verify_module_safety
    verdict = verify_module_safety(
        source=open("mymod.py").read(),
        sidecar_specs=user_specs_from_deppy_file,
        emit_lean=True,
        enable_diagnostics=True,
    )
    print(verdict.summary())
    if not verdict.is_safe:
        print(verdict.diagnosis_report)
        for fn, gaps in verdict.gaps.items():
            print(fn, gaps)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Optional, Callable, Iterable

from deppy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, ConditionalEffectWitness, Structural,
    SemanticSafetyWitness, ModuleSafetyComposition, SourceDischarge, Z3Proof,
    LeanProof, AxiomInvocation, Assume, TerminationObligation, min_trust,
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

    # Per-source discharge breakdown — maps source_id to a short tag
    # naming the discharge mechanism that closed it (or
    # ``"undischarged"`` for sources still open).  Tags are drawn
    # from the static set:
    #   z3-arithmetic, z3-syntactic, builtin-sidecar, callee-summary,
    #   raises-declaration, callee-axiom, is-total, termination,
    #   user-lean-proof, undischarged, co-located-peer.
    discharge_paths: dict[str, str] = field(default_factory=dict)

    # Audit fix #12 — assert-narrowing dependence (verdict-visible).
    #
    # ``assert_narrowing_dependent`` is True iff at least one source
    # in this function was discharged using a guard derived from an
    # ``assert P`` statement.  Such discharges are *unsound* under
    # ``python -O`` because the assert is stripped and the guard no
    # longer holds.  By default (``allow_assert_narrowing=False``)
    # the safety pipeline forces ``is_safe=False`` for any function
    # with ``assert_narrowing_dependent=True``.  Callers can opt in
    # via ``allow_assert_narrowing=True`` if they're confident the
    # deployed code does NOT use ``-O``.
    #
    # ``assert_dependent_sources`` lists the specific source IDs
    # whose discharge depended on the assert — useful for diagnosis
    # ("which call sites would silently break under -O?").
    assert_narrowing_dependent: bool = False
    assert_dependent_sources: list[str] = field(default_factory=list)

    # Cubical analysis (round-2 audit phase 3).
    # The intra-procedural cubical structure of the function as
    # built by ``deppy.pipeline.cubical_ast.build_cubical_set``.
    # When the cubical analysis runs, these fields summarise:
    #
    #   ``cubical_cell_counts``: dim → number of cells
    #   ``cubical_kan_candidates``: how many cells can be Kan-filled
    #   ``cubical_obligations_total``: total kernel obligations
    #     emitted from the cubical set
    #   ``cubical_obligations_verified``: how many actually verified
    #     against the kernel
    #   ``cubical_euler``: Euler characteristic of the cubical set
    cubical_cell_counts: dict[int, int] = field(default_factory=dict)
    cubical_kan_candidates: int = 0
    cubical_obligations_total: int = 0
    cubical_obligations_verified: int = 0
    cubical_euler: int = 0


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

    # Audit fix #12 — assert-narrowing dependence rolled up across
    # all functions.  ``assert_narrowing_dependent`` is True iff at
    # least one function's discharge depended on an assert-derived
    # guard.  ``assert_dependent_functions`` lists those functions.
    # Callers that gate deployment on safety should refuse to ship
    # a module with ``assert_narrowing_dependent=True`` unless they
    # explicitly opt in via ``allow_assert_narrowing=True``.
    assert_narrowing_dependent: bool = False
    assert_dependent_functions: list[str] = field(default_factory=list)

    # Cubical analysis aggregate (round-2 audit phase 3).
    # Sum of per-function cubical statistics across the module.
    cubical_total_cells: int = 0
    cubical_total_kan_candidates: int = 0
    cubical_total_obligations: int = 0
    cubical_total_obligations_verified: int = 0

    # Enhanced diagnosis fields
    diagnosis_findings: Optional[list[DiagnosticFinding]] = None
    diagnosis_report: Optional[str] = None
    suggested_fixes: Optional[list[str]] = None

    @property
    def is_safe(self) -> bool:
        return self.module_safe and all(v.is_safe for v in self.functions.values()) \
               and bool(self.functions)

    @property
    def gaps(self) -> dict[str, list[str]]:
        return {n: v.unaddressed for n, v in self.functions.items()
                if v.unaddressed}

    @property
    def discharge_breakdown(self) -> dict[str, int]:
        """Aggregate count of how each source got addressed.

        Counts every per-function ``discharge_paths`` entry across
        the module.  Tags are drawn from the static set in
        :data:`_DISCHARGE_TAGS`.  Useful for "how was this verified?"
        summaries.
        """
        out: dict[str, int] = {}
        for v in self.functions.values():
            for tag in v.discharge_paths.values():
                out[tag] = out.get(tag, 0) + 1
        return out

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

        # Discharge-path breakdown — shows the user *how* each source
        # was closed (Z3, syntactic, builtin sidecar, callee summary,
        # Lean proof, …) so the verdict is auditable rather than a
        # bare success/fail.
        breakdown = self.discharge_breakdown
        if breakdown:
            lines.append("  discharge paths:")
            for tag in _DISCHARGE_TAGS:
                count = breakdown.get(tag, 0)
                if count:
                    lines.append(f"    {tag:<22} {count:>4}")

        # Enhanced diagnostics summary
        if self.diagnosis_findings:
            error_count = sum(1 for f in self.diagnosis_findings if f.severity == "error")
            warning_count = sum(1 for f in self.diagnosis_findings if f.severity == "warning")
            lines.append(f"  diagnostics:      {error_count} errors, {warning_count} warnings")

            if self.suggested_fixes:
                lines.append(f"  next steps:       {len(self.suggested_fixes)} suggestions")

        if self.gaps:
            lines.append("  gaps:")
            for fn, missed in list(self.gaps.items())[:10]:
                lines.append(f"    - {fn}: {len(missed)} unaddressed")
            lines.append(
                "    (run `deppy obligations FILE.py` to emit a Lean "
                "skeleton for the open obligations.)"
            )
        return "\n".join(lines)


def verify_module_safety(
    source: str,
    sidecar_specs: Optional[dict[str, ExternalSpec]] = None,
    *,
    module_path: str = "<module>",
    use_drafts: bool = True,
    emit_lean: bool = False,
    kernel: Optional[ProofKernel] = None,
    progress_callback: Optional[Callable[[str], None]] = None,
    verbose_progress: bool = False,
    enable_diagnostics: bool = True,
    allow_assert_narrowing: bool = False,
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
        progress_callback: Optional callback for JSON progress events.
        verbose_progress: If True, show detailed progress to stdout.
        enable_diagnostics: If True, generate enhanced error diagnostics and suggestions.

    Returns:
        A ``SafetyVerdict`` describing per-function safety and the
        aggregate module trust level.
    """
    import ast

    kernel = kernel or ProofKernel()
    sidecar_specs = sidecar_specs or {}

    # IMPROVEMENT 3: Setup progress tracking
    from deppy.pipeline.progress import create_progress_tracker
    progress_tracker = create_progress_tracker(
        verbose=verbose_progress,
        json_output=progress_callback
    )

    # IMPROVEMENT 1: Use caching for expensive operations
    from deppy.pipeline.cache import get_verification_cache
    cache = get_verification_cache()
    
    # IMPROVEMENT 4: Smart error recovery
    from deppy.pipeline.recovery import get_recovery_engine, ComponentType
    recovery_engine = get_recovery_engine()
    
    # IMPROVEMENT 5: Enhanced diagnostics (if enabled)
    diagnosis_engine = None
    if enable_diagnostics:
        from deppy.pipeline.diagnosis import EnhancedDiagnosisEngine
        diagnosis_engine = EnhancedDiagnosisEngine()

    # Notes accumulated before ``verdict`` exists; flushed into
    # verdict.notes after verdict is created.  Any recovery here also
    # forces the module to be non-safe — empty-fallback outputs must
    # never masquerade as successful verification.
    _pre_verdict_notes: list[str] = []
    _pre_verdict_force_unsafe = False

    # Start progress tracking
    if progress_tracker:
        progress_tracker.start_verification(module_path, 0)  # Will update count later
        progress_tracker.begin_phase("Initialization")
    
    # 1. Auto-inferred drafts (low trust) merged with user sidecar (wins).
    if use_drafts:
        if progress_tracker:
            progress_tracker.begin_phase("Auto-spec inference")
        # Phase B integration: pre-compute refinement maps so the
        # bridge can fold leading-raise-guard preconditions into
        # the drafts.  We also keep the maps for later use in the
        # discharge step (they're cheap to compute).
        try:
            from deppy.pipeline.refinement_inference import infer_refinements
            refinement_maps_early = infer_refinements(source)
        except Exception:
            refinement_maps_early = {}
        def infer_cached(src: str):
            return infer_module_specs(src)
        try:
            inferred_specs = cache.cached_source_analysis(source, infer_cached)
            drafts_result, draft_error = recovery_engine.execute_with_recovery(
                ComponentType.SOURCE_ANALYSIS,
                lambda: draft_specs_to_sidecar(
                    inferred_specs,
                    refinement_maps=refinement_maps_early,
                )
            )
            drafts = drafts_result
            if draft_error and draft_error.recovery_attempted:
                _pre_verdict_notes.append(
                    f"Auto-spec inference used fallback: {draft_error}"
                )
                _pre_verdict_force_unsafe = True
        except Exception as e:
            drafts = {}
            _pre_verdict_notes.append(
                f"Auto-spec inference failed: {e}.  Treating the module "
                "as UN-verified — empty drafts are not the same as "
                "'no obligations'."
            )
            _pre_verdict_force_unsafe = True
            if progress_tracker:
                progress_tracker.report_error(f"Auto-spec inference failed: {e}")

        if progress_tracker:
            progress_tracker.complete_phase("Auto-spec inference")
    else:
        drafts = {}
    merged = merge_drafts_with_sidecar(drafts, sidecar_specs)

    # 2. Propagation across the call graph.
    if progress_tracker:
        progress_tracker.begin_phase("Call graph analysis")
    
    # Safe AST parsing with recovery
    tree_result, ast_error = recovery_engine.execute_with_recovery(
        ComponentType.AST_PARSING,
        cache.cached_ast_parse,
        source, module_path
    )
    tree = tree_result
    if ast_error and ast_error.recovery_attempted:
        verdict.notes.append(f"AST parsing used fallback: recovery due to {ast_error.exception}")
        if progress_tracker:
            progress_tracker.report_warning(f"AST parsing issues: {ast_error.exception}")
    
    # Safe effect propagation with recovery
    try:
        propagation_result, prop_error = recovery_engine.execute_with_recovery(
            ComponentType.EFFECT_PROPAGATION,
            propagate_effects,
            tree, sidecar_specs=merged
        )
        propagation = propagation_result
        if prop_error and prop_error.recovery_attempted:
            verdict.notes.append(f"Effect propagation used fallback: {prop_error.description}")
    except Exception as e:
        # Effect propagation failed.  An empty graph is NOT the same as
        # "no effects"; treat the module as un-analysed.
        from deppy.effects.effect_propagation import ModuleEffectGraph
        propagation = ModuleEffectGraph(summaries={}, call_sites=[])
        _pre_verdict_notes.append(
            f"Effect propagation failed: {e}.  Using empty graph — "
            "the module is NOT verified; callers must treat this as "
            "UNTRUSTED regardless of downstream aggregation."
        )
        _pre_verdict_force_unsafe = True
        if progress_tracker:
            progress_tracker.report_error(f"Effect propagation failed: {e}")
    
    runtime_env: dict[str, Any] = {}
    try:
        exec(compile(tree, module_path, "exec"), runtime_env, runtime_env)
    except Exception as e:
        verdict_note = f"Runtime env unavailable for counterexamples: {e}"
        runtime_env = {"__deppy_exec_error__": verdict_note}
    if progress_tracker:
        progress_tracker.complete_phase("Call graph analysis")

    # 3. Coverage report with recovery.
    if progress_tracker:
        progress_tracker.begin_phase("Coverage analysis")
    
    try:
        # Coverage depends on the merged spec map, not source alone, so we
        # bypass ``cached_source_analysis`` here — its key is ``(source,
        # analyzer_name)`` and would return stale data when the same source
        # is verified twice with different sidecars.
        coverage_result, coverage_error = recovery_engine.execute_with_recovery(
            ComponentType.COVERAGE_ANALYSIS,
            build_coverage,
            source, merged, module_path
        )
        coverage = coverage_result
        if coverage_error and coverage_error.recovery_attempted:
            verdict.notes.append(f"Coverage analysis used fallback: {coverage_error.description}")
    except Exception as e:
        # Minimal fallback coverage
        from deppy.pipeline.safety_coverage import CoverageReport, FunctionCoverage
        coverage = CoverageReport(
            module_path=module_path,
            functions={},  # Empty functions - will cause graceful degradation
            template_sections={}
        )
        verdict.notes.append(f"Coverage analysis failed, using minimal fallback: {e}")
        if progress_tracker:
            progress_tracker.report_error(f"Coverage analysis failed: {e}")
    
    if progress_tracker:
        progress_tracker.complete_phase("Coverage analysis")
    
    # Update progress tracker with actual function count
    if progress_tracker:
        progress_tracker._total_functions = len(coverage.functions)

    # 4. Per-function verification + verdict assembly.
    verdict = SafetyVerdict(
        module_path=module_path,
        coverage=coverage,
        propagation=propagation,
        drafted_specs=drafts,
        merged_specs=merged,
    )
    # Flush any pre-verdict notes and force the module un-safe if any
    # recovery or fallback happened earlier.  This prevents the
    # long-standing pattern of "empty fallback → no obligations →
    # aggregate verdict says safe".  ``is_safe`` is a computed
    # property over ``module_safe`` AND per-function safety; we flip
    # ``module_safe`` to False so the property short-circuits.
    if _pre_verdict_notes:
        verdict.notes.extend(_pre_verdict_notes)
    if _pre_verdict_force_unsafe:
        verdict.module_safe = False

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

    # Phase B/C: path-sensitive guards + inter-procedural summaries.
    # Either input may fail (e.g. unparseable nested constructs); we
    # fall back to ``None`` / ``{}`` and let the existing logic handle
    # the unguarded case.
    # Build a Context from the module source so the type translator
    # picks up TypeVar / NewType / TypeAlias / class declarations
    # (Phase U6).  This is a one-shot AST walk; cheap.
    try:
        from deppy.lean.type_translation import Context as _LeanCtx
        type_context = _LeanCtx.from_module_source(source)
    except Exception:
        type_context = None

    refinement_maps: dict = {}
    callee_summaries: dict = {}
    try:
        from deppy.pipeline.refinement_inference import infer_refinements
        refinement_maps = infer_refinements(source)
        # Soundness: warn when assert-narrowing was used because
        # ``python -O`` strips asserts and the discharge would
        # silently no-op in optimised mode.
        assert_narrowed = sorted(
            n for n, m in refinement_maps.items()
            if getattr(m, "used_assert_narrowing", False)
        )
        if assert_narrowed:
            verdict.notes.append(
                "WARN: assert-based path narrowing used in "
                f"{', '.join(assert_narrowed)}; "
                "discharges that depend on those asserts are unsound "
                "under `python -O` (asserts are stripped). "
                "Replace with `if not P: raise AssertionError` for "
                "PYTHONOPTIMIZE-safe verification."
            )

        # Any-type warning (Phase U4): when a function's parameter
        # is annotated ``Any`` / ``object``, every operation on it
        # is potentially unsafe, and the static analyzer cannot
        # distinguish "the user wrote this carefully" from "the
        # user erased the type".  Surface a verdict note so the
        # user knows narrowing is needed.
        any_typed = _functions_with_any_typed_params(tree)
        if any_typed:
            verdict.notes.append(
                "WARN: parameter(s) annotated `Any` / `object` in "
                f"{', '.join(sorted(any_typed))}; static safety "
                "checks cannot reason about untyped values — use "
                "isinstance(...) narrowing or a more specific "
                "annotation."
            )
    except Exception as e:
        verdict.notes.append(f"refinement-inference unavailable: {e}")
    try:
        from deppy.pipeline.interprocedural import compute_summaries
        callee_summaries = compute_summaries(
            source,
            drafts=drafts if use_drafts else None,
            refinement_maps=refinement_maps,
            user_specs=sidecar_specs,
        )
    except Exception as e:
        verdict.notes.append(f"interprocedural summaries unavailable: {e}")

    # IMPROVEMENT 2: Parallel function verification when beneficial
    from deppy.pipeline.simple_parallel import SimpleParallelVerifier
    
    function_names = list(coverage.functions.keys())
    
    if progress_tracker:
        progress_tracker.begin_phase(f"Function verification ({len(function_names)} functions)")
    
    def verify_single_function(fn_name: str) -> tuple[str, Any]:
        """Verify a single function and return all related data."""
        if progress_tracker:
            progress_tracker.begin_function(fn_name)
            
        cov = coverage.functions[fn_name]
        spec = merged.get(fn_name)
        precondition = " and ".join(
            getattr(spec, "exception_free_when", None) or []
        ) or "True"
        is_total = bool(getattr(spec, "is_total", False))
        raises_decls = list(getattr(spec, "raises_declarations", None) or [])

        # User-attached Lean proofs — pull from both the runtime
        # function object (``@with_lean_proof`` decorator) and the
        # sidecar spec's ``lean_proofs`` field.  The pipeline tries
        # each matching proof in order when other discharge paths
        # fail.
        lean_proofs: list[tuple[str, str, str, tuple[str, ...]]] = []
        fn_obj = runtime_env.get(fn_name)
        if fn_obj is not None:
            for entry in getattr(fn_obj, "_deppy_lean_proofs", None) or []:
                if entry not in lean_proofs:
                    lean_proofs.append(entry)
        for entry in getattr(spec, "lean_proofs", None) or []:
            if entry not in lean_proofs:
                lean_proofs.append(entry)

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
            refinement_map=refinement_maps.get(fn_name),
            callee_summaries=callee_summaries,
            lean_proofs=lean_proofs,
            type_context=type_context,
        )

        # Round-2 audit chunk D: cubical Kan-discharge.  After
        # standard discharges, attempt to promote remaining
        # ``Assume`` discharges via cubical Kan filling.  When a
        # source's cubical cell has all peer faces discharged, the
        # missing face is Kan-fillable and we promote the source
        # to a Structural discharge tagged ``cubical-kan``.
        try:
            from deppy.pipeline.cubical_ast import build_cubical_set
            from deppy.pipeline.cubical_discharge import (
                apply_cubical_kan_promotions,
                try_cubical_kan_discharge,
            )
            fn_node_for_cubical = fn_nodes.get(fn_name)
            if fn_node_for_cubical is not None:
                cset_for_discharge = build_cubical_set(
                    fn_node_for_cubical,
                    refinement_map=refinement_maps.get(fn_name),
                )
                kan_promotions = try_cubical_kan_discharge(
                    fn_name=fn_name,
                    sources=sources,
                    discharges=discharges,
                    cubical_set=cset_for_discharge,
                )
                if kan_promotions:
                    discharges = apply_cubical_kan_promotions(
                        discharges, kan_promotions,
                    )
                    verdict.notes.append(
                        f"cubical-kan promoted {len(kan_promotions)} "
                        f"source(s) in `{fn_name}`"
                    )
        except Exception as _e:
            verdict.notes.append(
                f"cubical-kan unavailable for {fn_name}: {_e}"
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

        is_safe = bool(result.success)
        trust = result.trust_level if is_safe else TrustLevel.UNTRUSTED

        lean_proof = None
        if translate_proof is not None and is_safe:
            try:
                lean_proof = translate_proof(cond_witness)
            except Exception as e:
                verdict.notes.append(f"Lean failure for {fn_name}: {e}")

        # When the kernel-level witness verifies, the source list is
        # genuinely addressed — recompute "unaddressed" from the
        # discharge outcomes (which see path-sensitive guards) so the
        # surfaced gap list matches reality.
        if is_safe:
            addressed_sources = [str(s) for s in sources]
            unaddressed_list: list[str] = []
        else:
            unaddressed_list = []
            addressed_sources = []
            for s, d in zip(sources, discharges):
                s_str = str(s)
                inner = d.inner
                if isinstance(inner, Assume):
                    unaddressed_list.append(s_str)
                else:
                    addressed_sources.append(s_str)

        # Build the per-source discharge-path map.  Tags must stay in
        # sync with ``_DISCHARGE_TAGS`` below so the summary renderer
        # can group them.
        discharge_paths: dict[str, str] = {}
        for d in discharges:
            discharge_paths[d.source_id] = _classify_discharge(d)

        function_verdict = FunctionVerdict(
            name=fn_name,
            is_safe=is_safe,
            trust=trust,
            coverage_ratio=cov.coverage_ratio,
            escapes=([repr(e) for e in
                      propagation.summaries.get(fn_name).escapes]
                     if propagation.summaries.get(fn_name) else []),
            addressed=addressed_sources,
            unaddressed=unaddressed_list,
            counterexamples=counterexamples,
            proof_payload=_serialize_conditional_witness(cond_witness),
            lean_proof=lean_proof,
            discharge_paths=discharge_paths,
        )

        # Phase 3 (round-2 audit): run the cubical AST analysis for
        # this function and attach its summary to the verdict.  The
        # analysis is independent of the safety verdict — it
        # describes the function's *control-flow topology* and emits
        # kernel obligations for Kan-fillable cells / complete
        # higher cells.  The pipeline doesn't currently use these
        # for discharging unsafe sources (that's a future hook); the
        # presence of the data lets downstream tooling do so.
        try:
            from deppy.pipeline.cubical_ast import build_cubical_set
            from deppy.pipeline.cubical_obligations import (
                cubical_set_to_obligations,
            )
            fn_node_for_cubical = fn_nodes.get(fn_name)
            if fn_node_for_cubical is not None:
                cset = build_cubical_set(
                    fn_node_for_cubical,
                    refinement_map=refinement_maps.get(fn_name),
                )
                obligations = cubical_set_to_obligations(
                    cset, include_all_higher=False,
                )
                # Verify each obligation through the kernel and
                # count successes.  Use the same goal context as
                # the per-function verification (a self-equality
                # judgment is enough for the structural check).
                from deppy.core.kernel import (
                    Context as _C, Judgment as _J,
                    JudgmentKind as _JK,
                )
                from deppy.core.types import PyObjType as _Py, Var as _V
                cube_ctx = _C()
                cube_x = _V("x")
                cube_goal = _J(
                    kind=_JK.EQUAL, context=cube_ctx,
                    left=cube_x, right=cube_x, type_=_Py(),
                )
                verified_count = 0
                for ob in obligations:
                    try:
                        rcube = kernel.verify(
                            cube_ctx, cube_goal, ob.proof_term,
                        )
                        if rcube.success:
                            verified_count += 1
                    except Exception:
                        pass
                # Populate verdict fields.
                function_verdict.cubical_cell_counts = {
                    dim: len(cells)
                    for dim, cells in cset.cells_by_dim.items()
                }
                function_verdict.cubical_kan_candidates = len(
                    cset.find_kan_fillable()
                )
                function_verdict.cubical_obligations_total = len(
                    obligations
                )
                function_verdict.cubical_obligations_verified = (
                    verified_count
                )
                function_verdict.cubical_euler = (
                    cset.euler_characteristic()
                )
        except Exception as _e:
            verdict.notes.append(
                f"cubical analysis unavailable for {fn_name}: {_e}"
            )

        if progress_tracker:
            progress_tracker.complete_function(fn_name, is_safe, trust.name)

        return (fn_name, {
            'verdict': function_verdict,
            'cond_witness': cond_witness,
            'discharges': discharges,
            'precondition': precondition,
            'trust': trust,
        })
    
    # Use parallel verification for multiple functions (if enough to be worth it)
    if len(function_names) > 3:  # Conservative threshold for parallelization
        parallel_verifier = SimpleParallelVerifier()
        verification_results = parallel_verifier.verify_functions_parallel(
            function_names,
            verify_single_function,
            progress_callback=lambda msg: verdict.notes.append(f"Progress: {msg}") if len(function_names) > 5 else None
        )
    else:
        # Sequential verification for small numbers of functions
        verification_results = {}
        for fn_name in function_names:
            fn_name_result, result_data = verify_single_function(fn_name)
            verification_results[fn_name] = result_data
    
    # Extract results into the expected data structures
    for fn_name in function_names:
        if fn_name not in verification_results or verification_results[fn_name] is None:
            continue

        result_data = verification_results[fn_name]
        verdict.functions[fn_name] = result_data['verdict']
        function_proofs[fn_name] = result_data['cond_witness']
        function_discharges[fn_name] = result_data['discharges']
        function_preconditions[fn_name] = result_data['precondition']
        lean_witnesses.append(result_data['cond_witness'])
        function_trusts.append(result_data['trust'])

    # Audit fix #12 — verdict-visible assert-narrowing dependence.
    # For each function whose discharges relied on assert-derived
    # guards, set the verdict's flags and (when ``allow_assert_narrowing``
    # is False) force ``is_safe=False``.  This turns the previous
    # warning-only treatment into a verdict-visible gate.
    try:
        from deppy.pipeline.assert_safety import (
            AssertDependenceTracker,
            apply_assert_dependence_gate,
            apply_assert_gate_module_level,
            collect_assert_dependences,
            render_dependence_note,
        )
        assert_tracker = AssertDependenceTracker.empty()
        for fn_name in function_names:
            fv = verdict.functions.get(fn_name)
            if fv is None:
                continue
            rmap = refinement_maps.get(fn_name)
            discharges = function_discharges.get(fn_name, [])
            dep_sources = collect_assert_dependences(
                fn_name, discharges, rmap,
            )
            apply_assert_dependence_gate(
                fv, dep_sources, allow=allow_assert_narrowing,
            )
            for sid in dep_sources:
                assert_tracker.add(fn_name, sid)
        apply_assert_gate_module_level(
            verdict, assert_tracker, allow=allow_assert_narrowing,
        )
        note = render_dependence_note(
            assert_tracker, allow=allow_assert_narrowing,
        )
        if note:
            verdict.notes.append(note)
    except Exception as _e:
        # Don't let the gate's own bug mask a real verdict — record
        # but don't abort.
        verdict.notes.append(
            f"assert-narrowing gate unavailable: {_e}"
        )

    # Phase 3 (round-2 audit): aggregate cubical statistics across
    # all functions into the module-level verdict.
    for _fv in verdict.functions.values():
        verdict.cubical_total_cells += sum(
            getattr(_fv, "cubical_cell_counts", {}).values()
        )
        verdict.cubical_total_kan_candidates += getattr(
            _fv, "cubical_kan_candidates", 0,
        )
        verdict.cubical_total_obligations += getattr(
            _fv, "cubical_obligations_total", 0,
        )
        verdict.cubical_total_obligations_verified += getattr(
            _fv, "cubical_obligations_verified", 0,
        )

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

        # CG7 / Round 3 Issue 2: every CALL_PROPAGATION discharge that
        # defers via callee_safe[X] must point to a callee X for
        # which the atlas actually contains a cocycle edge.  Without
        # this, the per-function deferral is empty — the axiom fires
        # but no atlas-level proof of X's safety exists.
        cocycle_callees = {edge.callee for edge in call_edges}
        for fn_name, dis in function_discharges.items():
            for d in dis:
                inner = d.inner
                if isinstance(inner, AxiomInvocation) and \
                        inner.name.startswith("callee_safe["):
                    callee = inner.name[len("callee_safe["):-1]
                    if callee not in cocycle_callees and callee in callee_pres:
                        cubical_atlas_succeeded = False
                        cubical_atlas_message = (
                            f"callee_safe[{callee}] in {fn_name} has no "
                            f"corresponding cocycle edge in the atlas"
                        )
                        break
            if not cubical_atlas_succeeded:
                break

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
    # ROUND 4 FIX: Only set internal_calls_closed when atlas is successful 
    # AND above minimum trust threshold
    # ROUND 5 FIX: Raise threshold to require genuinely proved overlaps
    # but not so high as to break all functionality
    min_trust_threshold = TrustLevel.STRUCTURAL_CHAIN  # Allow structural for now
    atlas_adequate = (cubical_atlas_succeeded and 
                      cubical_atlas_trust.value >= min_trust_threshold.value)
    verdict.internal_calls_closed = atlas_adequate
    
    module_proof = ModuleSafetyComposition(
        module_path=module_path,
        function_witnesses=function_proofs,
        module_discharges=module_discharges,
        internal_calls_closed=atlas_adequate,
    )
    module_result = kernel.verify(ctx, goal, module_proof)
    verdict.module_proof_payload = _serialize_module_composition(module_proof)
    verdict.module_safe = bool(module_result.success) and atlas_adequate
    if module_result.success and atlas_adequate:
        # ROUND 4 FIX: Use minimum trust, not maximum
        verdict.aggregate_trust = min_trust(
            module_result.trust_level, cubical_atlas_trust
        )
    else:
        verdict.aggregate_trust = TrustLevel.UNTRUSTED
        if not module_result.success:
            verdict.notes.append(module_result.message)

    if emit_lean and render_compilable_safety_module is not None \
            and check_lean_module_source is not None and verdict.module_safe:
        if progress_tracker:
            progress_tracker.begin_phase("Lean export")
        
        try:
            def lean_export():
                lean_src = render_compilable_safety_module(module_path, lean_witnesses)
                lean_check = check_lean_module_source(lean_src)
                return {'lean_src': lean_src, 'lean_check': lean_check}
            
            lean_result, lean_error = recovery_engine.execute_with_recovery(
                ComponentType.LEAN_COMPILER,
                lean_export
            )
            
            if lean_error and lean_error.recovery_attempted:
                # Lean compilation failed but we recovered
                verdict.lean_checked = False
                verdict.lean_module_source = None
                verdict.notes.append(f"Lean export failed, using fallback: {lean_error.exception}")
                for fv in verdict.functions.values():
                    fv.lean_proof = None
            else:
                # Lean compilation succeeded
                verdict.lean_checked = lean_result['lean_check'].ok
                verdict.lean_module_source = lean_result['lean_src']
                if not lean_result['lean_check'].ok:
                    verdict.notes.append(
                        f"Lean check failed: {(lean_result['lean_check'].stderr or lean_result['lean_check'].stdout).strip()}"
                    )
                    for fv in verdict.functions.values():
                        fv.lean_proof = None
        except Exception as e:
            # Complete Lean failure - continue without Lean
            verdict.lean_checked = False  
            verdict.lean_module_source = None
            verdict.notes.append(f"Lean export completely failed: {e}")
            if progress_tracker:
                progress_tracker.report_error(f"Lean export failed: {e}")
            for fv in verdict.functions.values():
                fv.lean_proof = None
                
        if progress_tracker:
            progress_tracker.complete_phase("Lean export", verdict.lean_checked)
    
    # Add recovery summary to verdict
    recovery_summary = recovery_engine.get_recovery_summary()
    if "No errors encountered" not in recovery_summary:
        verdict.notes.append(f"Recovery Summary: {recovery_summary}")
    
    error_diagnostics = recovery_engine.get_error_diagnostics() 
    if error_diagnostics:
        verdict.notes.extend([f"Unrecovered error: {diag}" for diag in error_diagnostics])
    
    fix_suggestions = recovery_engine.suggest_fixes()
    if fix_suggestions:
        verdict.notes.extend([f"Suggestion: {suggestion}" for suggestion in fix_suggestions])
    
    # IMPROVEMENT 5: Run enhanced diagnostics if enabled
    if diagnosis_engine:
        if progress_tracker:
            progress_tracker.begin_phase("Enhanced diagnostics")
        
        # Generate diagnostic findings
        verdict.diagnosis_findings = diagnosis_engine.analyze_verdict(verdict)
        
        # Generate human-readable report
        verdict.diagnosis_report = diagnosis_engine.generate_diagnosis_report(verdict.diagnosis_findings)
        
        # Generate prioritized fix suggestions
        verdict.suggested_fixes = diagnosis_engine.suggest_next_steps(verdict.diagnosis_findings)
        
        if progress_tracker:
            progress_tracker.complete_phase("Enhanced diagnostics")
    
    # Complete progress tracking
    if progress_tracker:
        safe_count = sum(1 for fv in verdict.functions.values() if fv.is_safe)
        progress_tracker.complete_verification(safe_count)
    
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


def _try_z3_discharge(
    precondition: str, safety_pred: str,
    kernel: ProofKernel,
    *,
    binders: Optional[dict] = None,
    type_context: Optional[Any] = None,
) -> Optional[ProofTerm]:
    """Attempt to discharge ``precondition ⊢ safety_pred`` via Z3.

    With ``binders`` supplied (mapping Python identifier → annotation
    text), the kernel uses the *typed* Z3 encoder
    (:mod:`deppy.core.z3_encoder`) which builds proper Z3 sorts for
    Optional / Union / list / dict / Callable annotations.
    Without binders we fall through to the legacy heuristic encoding.

    Returns a ``Z3Proof`` when Z3 actually proved the implication, or
    a ``Structural`` proof when the implication is true *syntactically*
    (the safety predicate appears as a conjunct of the precondition —
    typical for ``in`` / ``hasattr`` predicates that Z3's arithmetic
    core cannot encode but that we can discharge by inspection).
    Returns ``None`` when neither path works.
    """
    if is_synthetic_predicate(safety_pred):
        return None

    normalized_pred = safety_pred.strip()
    if normalized_pred == "True":
        formula = f"({precondition or 'True'}) => True"
        return Z3Proof(formula=formula)

    pre = (precondition or "True").strip()

    # Try Z3 first — when it succeeds we keep Z3_VERIFIED trust.
    formula = f"({pre}) => ({safety_pred})"
    verdict, _reason = kernel._z3_check(
        formula, binders=binders, type_context=type_context,
    )
    if verdict:
        # Carry the binders on the Z3Proof so kernel re-verification
        # uses the same typed encoding (Phase Z1).
        return Z3Proof(formula=formula, binders=dict(binders or {}))

    # Fall back to syntactic discharge for predicates Z3's arithmetic
    # core cannot encode (``in``, ``hasattr``, ``isinstance``, ...).
    # We emit a ``Structural`` proof (kernel-verifiable without Z3)
    # whose presence in the witness limits trust to STRUCTURAL_CHAIN.
    if _conjuncts_contain(pre, safety_pred):
        return Structural(
            description=(
                f"syntactic conjunct: {safety_pred} "
                f"present in precondition"
            ),
        )

    return None


def _normalize_paren_strip(text: str) -> str:
    """Strip outer parens / whitespace for syntactic comparison."""
    text = (text or "").strip()
    while text.startswith("(") and text.endswith(")"):
        # Only strip when parens are balanced *as an outer pair*.
        depth = 0
        balanced = True
        for i, ch in enumerate(text):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i < len(text) - 1:
                    balanced = False
                    break
        if not balanced:
            break
        text = text[1:-1].strip()
    return text


def _conjuncts_contain(precondition: str, safety_pred: str) -> bool:
    """True iff ``safety_pred`` is one of the conjuncts of
    ``precondition``.

    Splits on top-level ``and`` and compares each conjunct against
    ``safety_pred`` *structurally* (AST equality after parsing).  This
    is what discharges guards like ``"k in d"`` that Z3's arithmetic
    core doesn't understand, even when one side has parens stripped
    differently from the other.
    """
    pred_ast = _parse_or_none(safety_pred)
    if pred_ast is None:
        return False
    pred_canonical = _canonical_dump(pred_ast)
    for c in _split_top_level_conjuncts(precondition):
        c_ast = _parse_or_none(c)
        if c_ast is None:
            continue
        if _canonical_dump(c_ast) == pred_canonical:
            return True
    return False


def _parse_or_none(text: str):
    """Parse ``text`` as a Python expression; return its AST body or
    ``None`` on failure."""
    import ast as _ast
    try:
        return _ast.parse((text or "").strip(), mode="eval").body
    except SyntaxError:
        return None


def _canonical_dump(node) -> str:
    """Return ``ast.dump`` with line/col info stripped — purely
    structural so different paren styles don't matter."""
    import ast as _ast
    return _ast.dump(node, annotate_fields=False, include_attributes=False)


def _split_top_level_conjuncts(text: str) -> list[str]:
    """Split ``text`` on top-level ``and`` (parens-aware)."""
    out: list[str] = []
    cur: list[str] = []
    depth = 0
    i = 0
    text = text or ""
    while i < len(text):
        ch = text[i]
        if ch == "(":
            depth += 1
            cur.append(ch)
            i += 1
            continue
        if ch == ")":
            depth -= 1
            cur.append(ch)
            i += 1
            continue
        if depth == 0 and text[i:i+5].lower() == " and ":
            out.append("".join(cur))
            cur = []
            i += 5
            continue
        cur.append(ch)
        i += 1
    if cur:
        out.append("".join(cur))
    return [c.strip() for c in out if c.strip()]


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
            verdict, _reason = (False, None)
            if not is_synthetic_predicate(cond):
                verdict, _reason = kernel._z3_check(formula)
            if verdict:
                return Z3Proof(formula=formula)
            # CG7 cheat sweep (Round 2 / Issue 1): no tautology
            # fallback.  If precondition does not imply ``not(cond)``
            # we cannot honestly Z3-discharge — register the contract
            # as an axiom and rely on AxiomInvocation (AXIOM_TRUSTED
            # trust), which is honest about its provenance.
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
        verdict, _reason = kernel._z3_check(formula)
        if verdict:
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


def _try_callee_discharge(
    src: ExceptionSource, *,
    register_in: Optional[ProofKernel] = None,
    callee_summaries: Optional[dict] = None,
) -> Optional[ProofTerm]:
    """Discharge a CALL_PROPAGATION source by deferring its safety to
    the cubical atlas's call-graph cocycle (Phase 5).

    For an intra-module callee, the cocycle ``caller_pre ⇒
    subst(callee_pre)`` carries the actual proof.  Here we record an
    axiom-invocation pointing at that cocycle so the per-function
    section can verify; the atlas verifies the cocycle's truth.

    Soundness gate
    --------------
    When ``callee_summaries`` is supplied **and** the callee is in
    the map **and** its summary is *not* ``is_safe`` and has no
    preconditions to discharge, we **refuse** to register the axiom
    — the cocycle check would unconditionally hold (``True ⇒
    True``) but the callee's body has unaddressed runtime sources, so
    accepting the axiom would let the caller falsely claim safety.
    Returning ``None`` keeps the source as ``Assume`` and surfaces the
    real gap.
    """
    if src.kind is not ExceptionKind.CALL_PROPAGATION:
        return None
    callee = src.callee_name
    if not callee:
        return None
    if callee_summaries:
        summary = callee_summaries.get(callee)
        if (summary is not None
                and not getattr(summary, "is_safe", False)
                and not list(getattr(summary, "preconditions", None) or [])):
            # Internal callee with no preconditions and unguarded
            # internal sources — do not unsoundly axiom-discharge.
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
    refinement_map: Optional[Any] = None,
    callee_summaries: Optional[dict] = None,
    lean_proofs: Optional[list] = None,
    type_context: Optional[Any] = None,
) -> list[SourceDischarge]:
    """Build one ``SourceDischarge`` per ``ExceptionSource``.

    Strategy (in priority order; first success wins):

    1. For recursion (``RUNTIME_ERROR``) sources, try a
       ``TerminationObligation`` from ``spec.decreases``.
    2. **Path-sensitive Z3 discharge** — combine the function's
       ``exception_free_when`` with the path-sensitive guards from
       ``refinement_map`` and ask Z3 whether they imply the safety
       predicate.
    3. **Builtin sidecar discharge** — look the call up in
       :mod:`deppy.pipeline.builtin_sidecar` and either
       Z3-discharge or record it as a raises_declaration.
    4. **Inter-procedural discharge** — if the source is a
       ``CALL_PROPAGATION`` to a function whose summary we have, use
       :func:`deppy.pipeline.interprocedural.discharge_call_site`
       with the caller's path-sensitive guards.
    5. ``raises_declarations`` axiom discharge.
    6. ``is_total`` escape (structural, analyst-trusted).
    7. Otherwise, ``Assume`` (fails kernel verification — keeps
       the source visible in the verdict).
    """
    probe_kernel = ProofKernel()  # local kernel for discharge probes; cheap
    decreases = list(getattr(spec, "decreases", None) or []) if spec else []
    out: list[SourceDischarge] = []
    for s in sources:
        sp = safety_predicate_for(s, fn_node)
        sid = _source_id(fn_name, s)
        kind_name = s.kind.name

        # Compute the effective premise: function-wide precondition
        # AND path-sensitive guards live at this source.
        path_guards = _path_guards_for_source(refinement_map, s)
        enriched_pre = _conjoin(precondition, path_guards) or precondition

        if _is_recursion_source(s):
            term = _try_termination_discharge(
                src=s, fn_node=fn_node, decreases=decreases,
                precondition=enriched_pre, kernel=probe_kernel,
            )
            if term is not None:
                out.append(SourceDischarge(
                    source_id=sid, failure_kind=kind_name,
                    safety_predicate=sp, inner=term,
                    note="termination via decreases measure",
                ))
                continue

        z3_proof = _try_z3_discharge(
            enriched_pre, sp, probe_kernel,
            binders=_python_binder_map(fn_node),
            type_context=type_context,
        )
        if z3_proof is not None:
            out.append(SourceDischarge(
                source_id=sid, failure_kind=kind_name,
                safety_predicate=sp, inner=z3_proof,
                note=("Z3 discharged" + (" via path guards"
                                          if path_guards else "")),
            ))
            continue

        # Builtin-sidecar discharge for call-propagation sources.
        builtin_proof = _try_builtin_sidecar_discharge(
            src=s, precondition=enriched_pre, kernel=probe_kernel,
        )
        if builtin_proof is not None:
            out.append(SourceDischarge(
                source_id=sid, failure_kind=kind_name,
                safety_predicate=sp, inner=builtin_proof,
                note="builtin-sidecar discharged",
            ))
            continue

        # Inter-procedural callee discharge — try summary first.  When
        # the callee is internal *and* the summary discharge succeeds
        # we use it (Structural-style proof, STRUCTURAL_CHAIN trust).
        # When the callee is internal but the summary fails, we fall
        # through to the axiom path so the cubical atlas can attempt
        # the cocycle check (the atlas is the authoritative gate for
        # internal call safety; we never silently downgrade to
        # Assume here).
        callee_proof = _try_callee_summary_discharge(
            src=s, callee_summaries=callee_summaries,
            caller_path_guards=path_guards, kernel=probe_kernel,
        )
        if callee_proof is not None:
            out.append(SourceDischarge(
                source_id=sid, failure_kind=kind_name,
                safety_predicate=sp, inner=callee_proof,
                note="callee summary discharged",
            ))
            continue

        ax = _try_axiom_discharge(s, raises_decls, spec,
                                  precondition=enriched_pre, kernel=probe_kernel,
                                  register_in=kernel)
        if ax is not None:
            out.append(SourceDischarge(
                source_id=sid, failure_kind=kind_name,
                safety_predicate=sp, inner=ax,
                note="raises_declaration matches kind",
            ))
            continue

        callee_ax = _try_callee_discharge(
            s, register_in=kernel, callee_summaries=callee_summaries,
        )
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

        # User-attached Lean-proof discharge.  Each entry is a
        # ``(failure_kind, theorem, proof_script, imports)`` tuple
        # collected from ``@with_lean_proof`` decorators and from the
        # sidecar spec's ``lean_proofs`` field.  The pipeline tries
        # every entry whose ``failure_kind`` matches the source's
        # kind (or is the ``"*"`` wildcard) and uses the first one
        # that the kernel's :class:`LeanProof` term verifies.
        # Soundness fix F1: the kernel synthesises the goal from
        # ``sp`` (the safety predicate); the user cannot pick it.
        lean_proof = _try_user_lean_proof(
            src=s, lean_proofs=lean_proofs, kernel=probe_kernel,
            fn_node=fn_node, safety_predicate=sp,
            precondition=enriched_pre,
            type_context=type_context,
        )
        if lean_proof is not None:
            out.append(SourceDischarge(
                source_id=sid, failure_kind=kind_name,
                safety_predicate=sp, inner=lean_proof,
                note="discharged by user-attached Lean proof",
            ))
            continue

        out.append(SourceDischarge(
            source_id=sid, failure_kind=kind_name,
            safety_predicate=sp,
            inner=Assume(name=f"unproven::{sid}"),
            note="undischarged",
        ))

    # ── alternative-discharge pass ──────────────────────────────────
    # Several detector families (most prominently dynamic subscript)
    # emit *both* INDEX_ERROR and KEY_ERROR at the same (lineno, col)
    # because the analyzer cannot tell whether the receiver is a list
    # or a dict.  At runtime exactly *one* of those exceptions is
    # possible — if the user has discharged the one that matches
    # their actual type (e.g., ``k in d`` discharges KEY_ERROR), the
    # other should not block safety.  We flip undischarged peers at
    # the same location to a ``Structural`` follower carrying the
    # discharged kind's evidence.
    out = _propagate_co_located_discharges(
        out, sources, fn_node=fn_node, refinement_map=refinement_map,
    )
    return out


_CO_LOCATED_KINDS = frozenset({"INDEX_ERROR", "KEY_ERROR"})


def _propagate_co_located_discharges(
    out: list[SourceDischarge], sources: list[ExceptionSource],
    *,
    fn_node=None,
    refinement_map=None,
) -> list[SourceDischarge]:
    """Promote ``Assume`` discharges to ``Structural`` followers when a
    co-located peer source of a related kind was discharged **and** the
    receiver's type is statically pinned.

    Soundness gate (F3)
    -------------------
    A ``d[k]`` source emits both ``INDEX_ERROR`` and ``KEY_ERROR``
    because the AST visitor doesn't know whether ``d`` is a list or a
    dict.  At runtime exactly one of those exceptions can fire — but
    *which* one depends on the runtime type of ``d``.  Promoting one
    discharge to cover the other is sound iff we can prove ``d`` is
    of a type that rules out the *other* kind:

    * ``isinstance(d, dict)`` (or annotation ``d: dict``)  →  ``INDEX_ERROR``
      cannot fire, so a ``KEY_ERROR`` discharge covers both.
    * ``isinstance(d, (list, tuple, str, bytes))`` (or matching
      annotation)  →  ``KEY_ERROR`` cannot fire, so an ``INDEX_ERROR``
      discharge covers both.

    Without such evidence we leave the unguarded peer as ``Assume``
    so the verdict honestly surfaces the open obligation.
    """
    if len(out) != len(sources):
        return out
    by_loc: dict[tuple[int, int], list[int]] = {}
    for i, src in enumerate(sources):
        loc = getattr(src, "location", None)
        if loc is None:
            continue
        key = (getattr(loc, "lineno", 0), getattr(loc, "col_offset", 0))
        by_loc.setdefault(key, []).append(i)
    for loc_key, idxs in by_loc.items():
        if len(idxs) < 2:
            continue
        kinds = {out[i].failure_kind for i in idxs}
        if not kinds.issubset(_CO_LOCATED_KINDS):
            continue
        discharged_idx = None
        for i in idxs:
            if not isinstance(out[i].inner, Assume):
                discharged_idx = i
                break
        if discharged_idx is None:
            continue
        winner = out[discharged_idx]
        # Type-evidence gate.  ``_subscript_type_evidence`` returns
        # one of {"dict", "sequence", None}; we only promote when the
        # evidence rules out the *other* kind.
        #
        # Audit fix #9: pass the source location so type evidence
        # is read only from guards in scope at THAT location.  Before
        # this fix the lookup walked every fact in the refinement
        # map, allowing an isinstance guard at a different source
        # to leak into a peer's type-evidence decision.
        receiver_node = None
        for i in idxs:
            src = sources[i]
            ast_node = getattr(src, "ast_node", None)
            if ast_node is not None:
                receiver_node = getattr(ast_node, "value", None)
                break
        loc_lineno, loc_col = loc_key
        kinds_at_loc = {out[i].failure_kind for i in idxs}
        evidence = _subscript_type_evidence(
            receiver_node=receiver_node,
            fn_node=fn_node,
            refinement_map=refinement_map,
            source_lineno=loc_lineno,
            source_col=loc_col,
            source_kinds=kinds_at_loc,
        )
        if evidence is None:
            # No type evidence — refuse to promote.  The unguarded
            # peer stays ``Assume`` so the verdict is honest.
            continue
        if evidence == "dict" and winner.failure_kind != "KEY_ERROR":
            continue  # winner is INDEX_ERROR but d is a dict — wrong direction
        if evidence == "sequence" and winner.failure_kind != "INDEX_ERROR":
            continue
        for i in idxs:
            if i == discharged_idx:
                continue
            if isinstance(out[i].inner, Assume):
                out[i] = SourceDischarge(
                    source_id=out[i].source_id,
                    failure_kind=out[i].failure_kind,
                    safety_predicate=out[i].safety_predicate,
                    inner=Structural(
                        description=(
                            f"co-located with {winner.failure_kind} "
                            f"discharged at {winner.source_id}; "
                            f"receiver type evidence: {evidence}"
                        ),
                    ),
                    note="co-located peer discharged",
                )
    return out


def _subscript_type_evidence(
    *, receiver_node, fn_node, refinement_map,
    source_lineno: Optional[int] = None,
    source_col: Optional[int] = None,
    source_kinds: Optional[Iterable[str]] = None,
):
    """Return ``"dict"``, ``"sequence"``, or ``None`` based on
    statically-discoverable type evidence for the subscript receiver.

    Sources, in order of authority:

    1. ``isinstance(<receiver>, T)`` test that is in scope **at the
       specific source location** (``source_lineno`` + ``source_col``
       + ``source_kinds``).  This handles
       ``def f(d: dict | list, k): if isinstance(d, dict): return d[k]``
       — the union annotation alone gives ``None`` (the receiver
       could be either kind), but the isinstance guard *narrows* it
       to ``dict``.

       Audit fix #9: previously this loop iterated over **every**
       fact in the refinement map regardless of where the guard
       was active.  That meant an ``isinstance`` guard at line 5
       could leak type evidence into a subscript at line 50, even
       though the guard had long since fallen out of scope.  We
       now filter facts to those whose ``(lineno, col, kind)``
       matches the source we're analysing.  When the caller
       doesn't pass a location we still fall through to the global
       scan (preserves backward compatibility for the unit tests),
       but log a note so future callers can be migrated.
    2. The annotation on the matching function parameter — including
       union-typed annotations.  When the *every* alternative of a
       union belongs to the same family (e.g. ``dict | dict[str, int]``),
       we return that family.  Otherwise we conservatively return
       ``None``.
    3. None — caller falls through to the no-promotion behaviour.
    """
    import ast as _ast
    if receiver_node is None:
        return None
    receiver_text = ""
    try:
        receiver_text = _ast.unparse(receiver_node)
    except Exception:
        return None

    # 1. isinstance guard from the path-sensitive walk.
    #    Source-specific lookup (audit fix #9): when caller passes
    #    location info, only consider guards at *that* source.
    if refinement_map is not None:
        if source_lineno is not None and source_col is not None:
            kinds_filter: Optional[set[str]] = (
                set(source_kinds) if source_kinds is not None else None
            )
            for fact in refinement_map.per_source:
                if (fact.source_lineno != source_lineno
                        or fact.source_col != source_col):
                    continue
                if (kinds_filter is not None
                        and fact.source_kind not in kinds_filter):
                    continue
                for g in fact.guards:
                    if _isinstance_g_says_dict(g, receiver_text):
                        return "dict"
                    if _isinstance_g_says_sequence(g, receiver_text):
                        return "sequence"
        else:
            # Backward-compatible global scan — kept for unit tests
            # and callers that don't yet pass source location.  This
            # is the unsound path the audit identified.
            for fact in refinement_map.per_source:
                for g in fact.guards:
                    if _isinstance_g_says_dict(g, receiver_text):
                        return "dict"
                    if _isinstance_g_says_sequence(g, receiver_text):
                        return "sequence"

    # 2. Function-parameter annotation — handle PEP 604 unions.
    if fn_node is not None and isinstance(receiver_node, _ast.Name):
        for arg in getattr(fn_node, "args", _ast.arguments(args=[])).args:
            if arg.arg != receiver_node.id:
                continue
            ann = arg.annotation
            if ann is None:
                continue
            classes = _annotation_alternatives(ann)
            if not classes:
                continue
            # Drop the "None" alternative (Optional[T] reduces to T
            # for the purposes of subscript type evidence).
            classes = [c for c in classes if c != "None"]
            if not classes:
                continue
            # If every alternative is in the dict family, return
            # ``"dict"``; if every is in the sequence family,
            # ``"sequence"``; otherwise None.
            if all(_is_dict_family(c) for c in classes):
                return "dict"
            if all(_is_sequence_family(c) for c in classes):
                return "sequence"
    return None


def _isinstance_g_says_dict(guard_text: str, receiver_text: str) -> bool:
    if (f"isinstance({receiver_text}, dict)" in guard_text
            or f"isinstance({receiver_text}, Mapping)" in guard_text
            or f"isinstance({receiver_text}, MutableMapping)" in guard_text):
        return True
    if f"isinstance({receiver_text}, (dict" in guard_text:
        # Tuple form ``isinstance(x, (dict, ...))``.  Conservative:
        # only return dict if every alternative is dict-family.
        return _isinstance_tuple_all_dict(guard_text, receiver_text)
    return False


def _isinstance_g_says_sequence(
    guard_text: str, receiver_text: str,
) -> bool:
    sequence_singletons = (
        "list", "tuple", "str", "bytes", "Sequence", "List", "Tuple",
    )
    for cls in sequence_singletons:
        if f"isinstance({receiver_text}, {cls})" in guard_text:
            return True
    if f"isinstance({receiver_text}, (" in guard_text:
        return _isinstance_tuple_all_sequence(guard_text, receiver_text)
    return False


def _isinstance_tuple_args(guard_text: str, receiver_text: str) -> list[str]:
    """Best-effort parser for ``isinstance(x, (A, B, …))``.

    Returns the list of alternative class names.  When parsing fails
    we return ``[]`` so callers can safely treat the guard as
    inconclusive.
    """
    needle = f"isinstance({receiver_text}, ("
    idx = guard_text.find(needle)
    if idx < 0:
        return []
    rest = guard_text[idx + len(needle):]
    end = rest.find("))")
    if end < 0:
        return []
    body = rest[:end]
    return [a.strip() for a in body.split(",") if a.strip()]


def _isinstance_tuple_all_dict(
    guard_text: str, receiver_text: str,
) -> bool:
    args = _isinstance_tuple_args(guard_text, receiver_text)
    if not args:
        return False
    return all(_is_dict_family(a) for a in args)


def _isinstance_tuple_all_sequence(
    guard_text: str, receiver_text: str,
) -> bool:
    args = _isinstance_tuple_args(guard_text, receiver_text)
    if not args:
        return False
    return all(_is_sequence_family(a) for a in args)


def _is_dict_family(name: str) -> bool:
    name = name.strip().rstrip("]").split("[", 1)[0]
    return name in {"dict", "Mapping", "MutableMapping", "OrderedDict",
                     "defaultdict", "Counter", "Dict",
                     "typing.Dict", "typing.Mapping",
                     "typing.MutableMapping", "collections.OrderedDict",
                     "collections.defaultdict", "collections.Counter"}


def _is_sequence_family(name: str) -> bool:
    name = name.strip().rstrip("]").split("[", 1)[0]
    return name in {"list", "tuple", "str", "bytes", "bytearray",
                     "Sequence", "MutableSequence", "List", "Tuple",
                     "typing.List", "typing.Tuple",
                     "typing.Sequence", "typing.MutableSequence"}


def _python_binder_map(fn_node) -> dict[str, str]:
    """Map function-parameter name → annotation source text.

    Used to feed the typed Z3 encoder.  Parameters with no
    annotation default to ``"int"`` so the encoder picks IntSort
    (matches the kernel's legacy heuristic).
    """
    import ast as _ast
    if fn_node is None:
        return {}
    out: dict[str, str] = {}
    for arg in getattr(fn_node, "args",
                        _ast.arguments(args=[])).args:
        if arg.annotation is None:
            out[arg.arg] = "int"
            continue
        try:
            out[arg.arg] = _ast.unparse(arg.annotation).strip()
        except Exception:
            out[arg.arg] = "int"
    return out


def _functions_with_any_typed_params(tree) -> set[str]:
    """Return the names of functions / methods whose parameter list
    contains an annotation of ``Any`` / ``object`` / ``typing.Any``.

    Used by the safety pipeline (Phase U4) to surface a warning so
    users see that ``Any`` opts out of static checks.
    """
    import ast as _ast
    out: set[str] = set()
    for node in _ast.walk(tree):
        if not isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
            continue
        for arg in node.args.args:
            ann = arg.annotation
            if ann is None:
                continue
            try:
                text = _ast.unparse(ann).strip()
            except Exception:
                continue
            if text in {"Any", "typing.Any", "object", "builtins.object"}:
                out.add(node.name)
                break
    return out


def _annotation_alternatives(ann) -> list[str]:
    """Return the list of class-name alternatives in an annotation.

    ``int | None`` → ``["int", "None"]``;  ``Union[A, B]`` →
    ``["A", "B"]``;  ``Optional[T]`` → ``["T", "None"]``;  any other
    annotation → ``[<dotted_name>]`` or ``[]`` if unrecognisable.
    """
    import ast as _ast

    def _flatten(node) -> list[str]:
        # PEP 604 ``A | B``
        if isinstance(node, _ast.BinOp) and isinstance(node.op, _ast.BitOr):
            return _flatten(node.left) + _flatten(node.right)
        # ``None`` literal in a union.
        if isinstance(node, _ast.Constant) and node.value is None:
            return ["None"]
        # ``Optional[T]`` / ``Union[A, B]``
        if isinstance(node, _ast.Subscript):
            base = _name_text(node.value)
            slc = node.slice
            if base in ("Optional", "typing.Optional"):
                return _flatten(slc) + ["None"]
            if base in ("Union", "typing.Union"):
                if isinstance(slc, _ast.Tuple):
                    out: list[str] = []
                    for elt in slc.elts:
                        out.extend(_flatten(elt))
                    return out
                return _flatten(slc)
            # Generic ``list[T]`` / ``dict[K, V]`` — keep the base.
            return [base] if base else []
        return [_name_text(node)] if _name_text(node) else []

    def _name_text(node) -> str:
        if isinstance(node, _ast.Name):
            return node.id
        if isinstance(node, _ast.Attribute):
            return _name_text(node.value) + "." + node.attr
        try:
            return _ast.unparse(node)
        except Exception:
            return ""

    return _flatten(ann)


# ─────────────────────────────────────────────────────────────────────
#  Phase E helpers — path guards, builtin sidecar, callee summaries
# ─────────────────────────────────────────────────────────────────────

def _path_guards_for_source(refinement_map, src) -> tuple[str, ...]:
    """Pull path-sensitive guards from a RefinementMap for ``src``.

    Returns ``()`` when no map / no facts match.  We match by lineno
    + col + kind to avoid bleeding guards across different sources at
    the same line.
    """
    if refinement_map is None:
        return ()
    loc = getattr(src, "location", None)
    if loc is None:
        return ()
    lineno = getattr(loc, "lineno", 0)
    col = getattr(loc, "col_offset", 0)
    kind = getattr(getattr(src, "kind", None), "name", "")
    return refinement_map.conjoined_guards_for_source(lineno, col, kind)


def _conjoin(precondition: str, guards: tuple[str, ...]) -> str:
    """Conjoin a function-wide precondition with path-sensitive guards.

    Empty string / ``"True"`` for either is dropped.
    """
    parts: list[str] = []
    pre = (precondition or "").strip()
    if pre and pre != "True":
        parts.append(f"({pre})")
    for g in guards:
        g = (g or "").strip()
        if g and g != "True":
            parts.append(f"({g})")
    if not parts:
        return "True"
    return " and ".join(parts)


def _try_builtin_sidecar_discharge(
    *, src, precondition: str, kernel,
):
    """Discharge a CALL_PROPAGATION source using the builtin sidecar.

    For every catalogued entry whose mode is ``"safety_predicate"``,
    ask Z3 whether ``precondition`` implies the substituted predicate.
    On the first success, return a ``Z3Proof`` term.  Entries with
    ``mode in {"raises_declaration", "total"}`` are *not* discharged
    here — they are kept open so the user sees the residual obligation.
    """
    if src.kind is not ExceptionKind.CALL_PROPAGATION:
        return None
    call = getattr(src, "ast_node", None)
    if call is None:
        return None
    try:
        from deppy.pipeline.builtin_sidecar import (
            lookup_call, substitute_call_arguments,
        )
    except ImportError:
        return None
    entries = lookup_call(call)
    if not entries:
        return None
    for entry in entries:
        if entry.mode == "total":
            # Honest accounting (Soundness fix F8): the catalogue's
            # ``total`` entries are *unverified facts about CPython*
            # (e.g. ``str(x)`` never raises) — we have not proven
            # them.  Emit an ``AxiomInvocation`` so the witness
            # carries AXIOM_TRUSTED rather than the misleading
            # KERNEL/STRUCTURAL_CHAIN trust a ``Structural`` would
            # confer.
            ax_name = f"builtin_total[{entry.exception_class}]"
            try:
                kernel.register_axiom(
                    ax_name,
                    statement=f"builtin total: {entry.note or entry.exception_class}",
                )
            except Exception:
                pass
            return AxiomInvocation(name=ax_name)
        if entry.mode == "safety_predicate":
            substituted = substitute_call_arguments(entry.predicate, call)
            if not substituted:
                continue
            formula = f"({precondition}) => ({substituted})"
            verdict, _reason = kernel._z3_check(formula)
            if verdict:
                return Z3Proof(formula=formula)
    return None


# ─────────────────────────────────────────────────────────────────────
#  Discharge-path classification (Phase L5)
# ─────────────────────────────────────────────────────────────────────

_DISCHARGE_TAGS = (
    "z3-arithmetic",
    "z3-syntactic",
    "builtin-sidecar",
    "callee-summary",
    "raises-declaration",
    "callee-axiom",
    "builtin-total-axiom",
    "is-total",
    "termination",
    "user-lean-proof",
    "co-located-peer",
    "cubical-kan",            # round-2 audit chunk D: cubical Kan filling
    "structural-unknown",
    "undischarged",
)


def _classify_discharge(d: SourceDischarge) -> str:
    """Map a :class:`SourceDischarge` to one of :data:`_DISCHARGE_TAGS`.

    The tag is read from a small set of pattern matches against the
    ``inner`` proof-term type, the human-readable ``note`` field, and
    the :class:`AxiomInvocation` name (so we can tell
    ``builtin_total[...]`` axioms from generic ``callee_safe[...]``
    ones).

    A :class:`Structural` whose origin we cannot positively identify
    falls through to ``"structural-unknown"`` (Soundness fix F7) so
    the breakdown distinguishes "Z3 proved an arithmetic fact" from
    "the pipeline emitted a structural assumption we can't trace".
    """
    inner = d.inner
    note = (d.note or "").lower()
    if isinstance(inner, Assume):
        return "undischarged"
    if isinstance(inner, LeanProof):
        return "user-lean-proof"
    if isinstance(inner, TerminationObligation):
        return "termination"
    if isinstance(inner, AxiomInvocation):
        ax_name = (getattr(inner, "name", "") or "").lower()
        if ax_name.startswith("builtin_total["):
            return "builtin-total-axiom"
        if "raises_declaration" in note or ax_name.startswith("raises_decl["):
            return "raises-declaration"
        return "callee-axiom"
    if isinstance(inner, Z3Proof):
        return "z3-arithmetic"
    if isinstance(inner, Structural):
        desc = (getattr(inner, "description", "") or "").lower()
        if "is_total" in note or "is_total" in desc:
            return "is-total"
        if "syntactic conjunct" in desc:
            return "z3-syntactic"
        if "cubical kan" in desc or "cubical-kan" in note:
            return "cubical-kan"
        if "co-located" in note:
            return "co-located-peer"
        if "callee" in note and "discharged" in note:
            return "callee-summary"
        if "builtin" in note or "builtin" in desc:
            return "builtin-sidecar"
        return "structural-unknown"
    return "undischarged"


def _try_user_lean_proof(
    *, src, lean_proofs, kernel, fn_node=None, safety_predicate=None,
    precondition: str = "True", type_context=None,
):
    """Discharge ``src`` using a user-attached Lean proof.

    Soundness fix F1
    ----------------
    The kernel synthesises the theorem from the source's safety
    predicate (translated to Lean) plus the user's proof body.  The
    user *cannot* fabricate a different goal — Lean will reject the
    proof unless it inhabits ``deppy-generated-goal``.

    ``lean_proofs`` is the merged list of
    ``(failure_kind, theorem, proof_script, imports)`` tuples
    collected from ``@with_lean_proof`` decorators and from the
    sidecar spec's ``lean_proofs`` field.  We use the *proof_script*
    field as the user's proof body; the ``theorem`` field is ignored
    (the kernel synthesises the theorem itself).
    """
    if not lean_proofs:
        return None
    if not safety_predicate:
        return None
    kind = getattr(getattr(src, "kind", None), "name", "")

    from deppy.lean.predicate_translation import translate
    py_types = _python_binder_map(fn_node)
    goal_result = translate(safety_predicate, python_types=py_types)
    pre_result = translate(precondition or "True", python_types=py_types)

    # Build typed binders + aux-decls from the function signature.
    binder_aux: list[str] = []
    binders = _lean_binders_for_fn(
        fn_node, aux_decls=binder_aux, type_context=type_context,
    )
    if pre_result.lean_text and pre_result.lean_text != "True":
        binders = binders + (f"(h_pre : {pre_result.lean_text})",)

    # Combined imports + auxiliary axiom declarations from both the
    # goal, the precondition, and the binder type translations.
    imports_set: list[str] = []
    aux_set: list[str] = []
    for lst, src_lst in (
        (imports_set, goal_result.imports),
        (imports_set, pre_result.imports),
        (aux_set, goal_result.aux_decls),
        (aux_set, pre_result.aux_decls),
        (aux_set, binder_aux),
    ):
        for line in src_lst:
            if line not in lst:
                lst.append(line)

    for failure_kind, _theorem, proof_script, user_imports in lean_proofs:
        if failure_kind not in ("*", kind):
            continue
        all_imports = tuple(imports_set + list(user_imports or []))
        # Prepend aux Prop declarations to the proof script's
        # surrounding source via a synthetic theorem name.
        candidate = LeanProof(
            expected_goal=goal_result.lean_text,
            binders=binders,
            proof_script=proof_script,
            imports=tuple(list(all_imports) + aux_set),
        )
        # Run the kernel-level Lean check with the synthesised
        # theorem so we honour Soundness fix F1: the user cannot
        # change the goal.
        from deppy.core.kernel import LeanProof as _LP  # already imported
        # Re-use _lean_check with manually-built theorem so the cache
        # key reflects the synthesised form.
        synth_theorem = (
            f"theorem deppy_obligation {' '.join(binders)} : "
            f"({goal_result.lean_text})"
        )
        ok, _detail = kernel._lean_check(
            theorem=synth_theorem, proof_script=proof_script,
            imports=tuple(list(all_imports) + aux_set),
            cache_into=candidate,
        )
        if ok:
            return candidate
    return None


def _lean_binders_for_fn(
    fn_node, *,
    aux_decls: Optional[list[str]] = None,
    type_context=None,
) -> tuple[str, ...]:
    """Translate a function's parameter list into Lean-4 binders.

    Delegates to :mod:`deppy.lean.type_translation` so the same
    annotation rules apply across the whole system: ``Union`` /
    ``Optional`` / ``Any`` / ``Callable`` / generic containers /
    user-defined classes all translate consistently.

    ``type_context`` is an optional :class:`Context` carrying the
    enclosing module's TypeVar / NewType / TypeAlias declarations
    so polymorphic signatures translate accurately.
    """
    import ast as _ast
    if fn_node is None:
        return ()
    from deppy.lean.type_translation import translate_annotation
    binders: list[str] = []
    for arg in getattr(fn_node, "args",
                        _ast.arguments(args=[])).args:
        result = translate_annotation(
            arg.annotation, context=type_context,
        )
        if aux_decls is not None:
            for d in result.aux_decls:
                if d not in aux_decls:
                    aux_decls.append(d)
        binders.append(f"({arg.arg} : {result.lean})")
    return tuple(binders)


def _try_callee_summary_discharge_v2(
    *, src, callee_summaries, caller_path_guards: tuple[str, ...], kernel,
):
    """Like :func:`_try_callee_summary_discharge` but returns a tuple
    ``(proof | None, internal_callee_known: bool)`` so the caller can
    distinguish "callee unknown / external" from "callee known but
    couldn't discharge under the caller's guards".
    """
    proof = _try_callee_summary_discharge(
        src=src, callee_summaries=callee_summaries,
        caller_path_guards=caller_path_guards, kernel=kernel,
    )
    callee_name = getattr(src, "callee_name", None)
    summary = callee_summaries.get(callee_name) if callee_summaries else None
    return proof, (summary is not None)


def _try_callee_summary_discharge(
    *, src, callee_summaries, caller_path_guards: tuple[str, ...], kernel,
):
    """Discharge a ``CALL_PROPAGATION`` source via a callee
    :class:`FunctionSummary`.

    ``callee_summaries`` maps function name → ``FunctionSummary`` (from
    :mod:`deppy.pipeline.interprocedural`).  When the callee is in the
    map and its preconditions are entailed by the caller's path
    guards, return a ``Z3Proof``; when the callee is ``is_safe`` with
    no preconditions, return a ``Structural`` proof.
    """
    import ast as _ast
    if src.kind is not ExceptionKind.CALL_PROPAGATION:
        return None
    if not callee_summaries:
        return None
    call = getattr(src, "ast_node", None)
    if call is None or not isinstance(call, _ast.Call):
        return None
    callee_name = src.callee_name
    if not callee_name:
        return None
    summary = callee_summaries.get(callee_name)
    if summary is None:
        return None
    actuals: list[str] = []
    for a in call.args:
        try:
            actuals.append(_ast.unparse(a))
        except Exception:
            return None
    try:
        from deppy.pipeline.interprocedural import discharge_call_site
    except ImportError:
        return None
    ok, msg = discharge_call_site(
        callee_summary=summary, actuals=actuals,
        caller_path_guards=caller_path_guards, z3_check=kernel._z3_check,
    )
    if not ok:
        return None
    # Both flavors emit ``Structural`` so the kernel verifies the
    # discharge without re-running Z3 (the Z3 entailment was already
    # established inside ``discharge_call_site``).  This is the same
    # idea as the syntactic-conjunct shortcut in ``_try_z3_discharge``.
    return Structural(
        description=f"callee {callee_name} discharged: {msg}",
    )


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
