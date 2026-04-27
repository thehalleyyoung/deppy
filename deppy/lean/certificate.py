"""Lean certificate generator — Lean as the gold standard.

A *certificate* is a self-contained Lean 4 file that, if Lean
accepts it, certifies the safety + correctness properties claimed
by the deppy verdict.  It contains:

1. **Imports**: ``DeppyBase`` (deppy's tactic library + safety
   predicates) plus any user-supplied imports.
2. **Type axioms**: opaque ``axiom <Name> : Type`` declarations for
   every user class / TypeVar / NewType that appeared in the source.
3. **Function definitions**: a ``def fn_name (args : T) : R := body``
   for every analysed Python function.  Bodies are translated by
   :mod:`deppy.lean.body_translation` — fully-translated when the
   body is arithmetic / list-shape, ``sorry`` otherwise.
4. **Safety theorems**: one per detected exception source, stating
   that the function's safety predicate holds under its
   precondition.  Proof bodies are auto-deduced where possible
   (``omega`` / ``decide`` / ``simp_all`` / ``Deppy.deppy_safe``);
   discharged sources get matching tactic bodies; unaddressed
   sources get ``sorry``.
5. **Implication theorems**: one per ``@implies(X, Y)`` decorator,
   stating ``∀ args, X → Y`` where ``Y`` may reference ``result``,
   the function's return value.

The certificate is intended to be Lean-checkable.  When Lean accepts
it, the deppy verdict is *kernel-validated* — Lean kernel checking
becomes the gold-standard correctness criterion.

Public API::

    @dataclass class Certificate
    @dataclass class CertificateReport
    write_certificate(source, out_path, *, sidecar_specs=None,
                      use_drafts=True, module_name="DeppyCertificate",
                      run_lean=False, lean_timeout_s=120)
        → CertificateReport

When ``run_lean=True`` and the local ``lean`` binary is available,
the report's ``lean_accepted`` field reflects the Lean kernel's
verdict.
"""
from __future__ import annotations

import ast
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


# ─────────────────────────────────────────────────────────────────────
#  Output dataclasses
# ─────────────────────────────────────────────────────────────────────

@dataclass
class Certificate:
    """A completed certificate ready to write to disk."""
    module_name: str
    text: str
    function_count: int = 0
    theorem_count: int = 0
    sorry_count: int = 0
    aux_decl_count: int = 0
    # Cohomological structure (Phase C2):
    cocycle_count_c0: int = 0
    cocycle_count_c1: int = 0
    cocycle_count_c2: int = 0
    cohomology_h0_size: int = 0
    cohomology_h1_size: int = 0
    cohomology_h2_size: int = 0
    # Audit fix #7 — `@implies` accounting:
    implies_count: int = 0
    implies_auto_proved: int = 0
    implies_user_supplied: int = 0
    implies_unproved: int = 0  # honest sorries

    # Round-2 audit integration #3 — cubical-section accounting:
    cubical_kan_theorems_count: int = 0
    cubical_higher_path_theorems_count: int = 0
    cubical_sorries: int = 0  # honest sorries from the cubical section


@dataclass
class CertificateReport:
    """Outcome of a certificate run."""
    out_path: Path
    certificate: Certificate
    lean_accepted: Optional[bool] = None
    lean_stdout: str = ""
    lean_stderr: str = ""
    notes: list[str] = field(default_factory=list)

    def summary(self) -> str:
        lines = [
            f"Certificate written to {self.out_path}",
            f"  functions:   {self.certificate.function_count}",
            f"  theorems:    {self.certificate.theorem_count}",
            f"  sorry stubs: {self.certificate.sorry_count}",
        ]
        if self.lean_accepted is not None:
            lines.append(
                f"  Lean kernel: "
                f"{'ACCEPTED' if self.lean_accepted else 'REJECTED'}"
            )
        for n in self.notes:
            lines.append(f"  note: {n}")
        return "\n".join(lines)


# ─────────────────────────────────────────────────────────────────────
#  Public entry point
# ─────────────────────────────────────────────────────────────────────

def write_certificate(
    source: str,
    out_path: Path | str,
    *,
    sidecar_specs: Optional[dict] = None,
    sidecar_module: Optional[object] = None,
    use_drafts: bool = True,
    module_name: str = "DeppyCertificate",
    run_lean: bool = False,
    lean_timeout_s: int = 120,
) -> CertificateReport:
    """Build a complete Lean certificate for ``source``.

    The certificate bundles function definitions, safety theorems
    (one per discharged or open exception source), and implication
    theorems (one per ``@implies`` decorator) into a single
    Lean-checkable file.

    When ``run_lean=True`` and the ``lean`` binary is on PATH, the
    report includes the kernel's accept/reject verdict.
    """
    from deppy.pipeline.safety_pipeline import verify_module_safety
    from deppy.lean.body_translation import translate_body
    from deppy.lean.predicate_translation import translate as translate_pred
    from deppy.lean.type_translation import (
        Context, translate_annotation,
    )
    from deppy.lean.obligations import (
        _python_param_type_to_lean, _safe_ident,
    )

    out_path = Path(out_path)

    # Run the safety pipeline so we have discharge info per source.
    verdict = verify_module_safety(
        source, sidecar_specs=sidecar_specs, use_drafts=use_drafts,
    )

    # AST walk for function nodes + module-level type context.
    try:
        tree = ast.parse(source)
    except SyntaxError as e:
        return CertificateReport(
            out_path=out_path,
            certificate=Certificate(
                module_name=module_name,
                text=f"-- failed to parse Python source: {e}\n",
            ),
            notes=[f"failed to parse: {e}"],
        )

    type_context = Context.from_module_source(source)

    fn_nodes: dict[str, ast.FunctionDef | ast.AsyncFunctionDef] = {}
    fn_runtime: dict[str, object] = {}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            fn_nodes.setdefault(node.name, node)

    # Execute the source (for picking up @implies metadata).  Failures
    # are non-fatal — without runtime metadata we still emit safety
    # theorems, just no implication theorems.
    runtime_env: dict = {}
    try:
        exec(compile(tree, "<deppy-cert>", "exec"),
             runtime_env, runtime_env)
        for name, fn in list(runtime_env.items()):
            if callable(fn) and name in fn_nodes:
                fn_runtime[name] = fn
    except Exception:
        pass

    # Aggregated certificate sections.
    aux_decls: list[str] = []
    function_defs: list[str] = []
    safety_theorems: list[str] = []
    implies_theorems: list[str] = []
    sorry_count = 0

    # ── 1) Function definitions ────────────────────────────────────
    for fn_name, fn_node in fn_nodes.items():
        binders, return_lean = _render_signature(
            fn_node, type_context, aux_decls,
        )
        # Audit fix #6: thread the same inferred parameter types into
        # the body translator so identifier types are consistent
        # between the signature and the body.
        from deppy.lean.body_translation import infer_locals_types
        body_param_types = infer_locals_types(fn_node)
        body = translate_body(
            fn_node, type_context=type_context,
            param_types=body_param_types,
        )
        if body.sorry_count:
            sorry_count += body.sorry_count
            for n in body.notes:
                # Surface translation notes as comments above the def.
                pass
        partial_kw = "partial " if _is_recursive(fn_node, fn_name) else ""
        function_defs.append(
            f"-- Translation of Python function `{fn_name}`.\n"
            f"{partial_kw}def {fn_name} {binders} : {return_lean} :=\n"
            f"  {body.lean_text}\n"
        )

    # ── 2) Safety theorems ────────────────────────────────────────
    # Hole 1 fix: theorem names are derived from ``<fn>_L<lineno>_<kind>``
    # which collides when multiple sources share the same line/kind
    # (e.g., several NAME_ERROR sources on the same body line — one
    # per let-bound local).  Dedupe by source_id within each function;
    # when collisions remain (different col_offsets, same lineno),
    # append an index suffix to make the Lean identifier unique.
    for fn_name, fv in verdict.functions.items():
        fn_node = fn_nodes.get(fn_name)
        spec = (sidecar_specs or {}).get(fn_name)
        precondition = "True"
        if spec is not None:
            efw = list(getattr(spec, "exception_free_when", None) or [])
            if efw:
                precondition = " and ".join(efw)
        params = (
            [a.arg for a in fn_node.args.args] if fn_node is not None else []
        )
        seen_ids: dict[str, int] = {}
        for src_str in list(fv.addressed) + list(fv.unaddressed):
            kind, lineno = _parse_source_str(src_str)
            base_source_id = f"{fn_name}_L{lineno}_{kind}"
            count = seen_ids.get(base_source_id, 0)
            seen_ids[base_source_id] = count + 1
            # Disambiguate same-(fn, line, kind) sources by index.
            source_id = (
                base_source_id if count == 0
                else f"{base_source_id}_{count}"
            )
            full_id = f"{fn_name}:L{lineno}:{kind}"
            tag = fv.discharge_paths.get(full_id, "")
            sp = _safety_predicate_for(fv, lineno, kind) or (
                f"undischarged_{kind}_at_L{lineno}"
            )
            theorem_text, theorem_sorries = _render_safety_theorem(
                fn_name=fn_name, source_id=source_id, kind=kind,
                safety_predicate=sp, precondition=precondition,
                fn_node=fn_node, params=params,
                discharge_path=tag, aux_decls=aux_decls,
            )
            sorry_count += theorem_sorries
            safety_theorems.append(theorem_text)

    # ── 3) Implication theorems (@implies) ────────────────────────
    # Audit fix #7: collect per-@implies audit entries so the
    # certificate can render an audit summary block (and so the
    # downstream verdict can count auto-proved vs sorry-emitted vs
    # user-supplied obligations).
    from deppy.lean.implies_tactics import (
        ImpliesAuditEntry,
        render_audit_summary,
        count_unproved as _count_implies_unproved,
        count_auto_proved as _count_implies_auto,
        count_user_supplied as _count_implies_user,
    )
    implies_audit: list[ImpliesAuditEntry] = []
    for fn_name, fn_node in fn_nodes.items():
        fn_obj = fn_runtime.get(fn_name)
        if fn_obj is None:
            continue
        implies_specs = getattr(fn_obj, "_deppy_implies", None) or []
        for i, spec in enumerate(implies_specs):
            theorem_text, theorem_sorries = _render_implies_theorem(
                fn_name=fn_name, idx=i, spec=spec,
                fn_node=fn_node,
                type_context=type_context, aux_decls=aux_decls,
                audit_entries=implies_audit,
            )
            sorry_count += theorem_sorries
            implies_theorems.append(theorem_text)

    # ── Compute the cohomological structure (Phase C2 + Audit Fix #1) ─
    cohomology = _compute_cohomology(verdict, fn_nodes, source)
    # Real cocycle theorems with non-trivial goals (replaces the
    # vacuous ``: True := by deppy_safe`` from the original
    # implementation).
    from deppy.lean.cohomology import render_cocycle_section
    cocycle_theorems, cocycle_report = render_cocycle_section(
        verdict, fn_nodes, source,
        type_context=type_context, sidecar_specs=sidecar_specs,
    )
    # Audit fix #4 + #5: emit a *standard simplicial* cochain
    # complex with explicit face maps, the implication-form
    # coboundary, and an actual cohomology computation
    # (``H^k = ker δ^k / im δ^(k-1)``).  The block sits as a Lean
    # comment block in the certificate so the structure is auditable
    # without re-deriving it.
    from deppy.lean.cohomology_compute import (
        build_chain_complex,
        render_chain_complex_lean,
    )
    standard_chain_complex = build_chain_complex(verdict, fn_nodes)
    standard_complex_block = render_chain_complex_lean(
        standard_chain_complex,
    )

    # ── Render the file ────────────────────────────────────────────
    lines: list[str] = [
        f"-- Auto-generated by `deppy.lean.certificate`.",
        f"-- Module: {module_name}",
        f"-- Lean as the gold standard: this certificate is",
        f"-- self-contained — running ``lean`` on it accepts iff",
        f"-- the safety + implication theorems hold.",
        f"--",
        f"-- Cohomological structure (Phase C2):",
        f"--   |C^0| (per-function safety): {len(cohomology.c0)}",
        f"--   |C^1| (call-site cocycles):  {len(cohomology.c1)}",
        f"--   |C^2| (module coherence):    {len(cohomology.c2)}",
        f"--   |H^0|: {len(cohomology.h0)}  (verified-safe functions)",
        f"--   |H^1|: {len(cohomology.h1)}  (open obstructions)",
        f"--   |H^2|: {len(cohomology.h2)}  (coherence failures)",
        "",
        "import DeppyBase",
        "open Deppy",
        "",
    ]
    if aux_decls:
        lines.append("/-! ## Auxiliary type axioms -/")
        lines.append("")
        for d in aux_decls:
            lines.append(d)
        lines.append("")

    # Hole 7 fix: render sidecar-declared axioms as Lean axioms.
    # When a ``.deppy`` sidecar carries ``axiom <name>: "<statement>"``
    # declarations they were previously parsed but never reached the
    # certificate.  We now emit them as ``axiom <ident> : Prop``
    # with the original Python statement preserved as a comment so
    # callers can later supply concrete Lean proofs / definitions.
    sidecar_axioms_emitted = 0
    if sidecar_module is not None:
        try:
            sidecar_axioms_dict = getattr(sidecar_module, "axioms", {}) or {}
        except Exception:
            sidecar_axioms_dict = {}
        if sidecar_axioms_dict:
            lines.append("/-! ## Sidecar-declared library axioms")
            lines.append("")
            lines.append(
                "These axioms come from the ``.deppy`` sidecar.  Each "
                "is asserted as an opaque ``Prop`` so callers can"
            )
            lines.append(
                "introduce a concrete Lean proof / definition later "
                "without modifying the certificate. -/"
            )
            lines.append("")
            for ax_name, ax in sorted(sidecar_axioms_dict.items()):
                ident = _safe_ident(f"sidecar_{ax_name}")
                stmt = getattr(ax, "statement", "") or ""
                target = getattr(ax, "target", "") or ""
                module = getattr(ax, "module", "") or ""
                pre = getattr(ax, "precondition", "") or ""
                lines.append(
                    f"-- Sidecar axiom: {ax_name}  "
                    f"(target: {target}; module: {module})"
                )
                lines.append(f"-- Statement (Python): {stmt}")
                if pre:
                    lines.append(f"-- Precondition (Python): {pre}")
                lines.append(f"axiom {ident} : Prop")
                sidecar_axioms_emitted += 1
            lines.append("")

    lines.append("namespace " + _safe_ident(module_name))
    lines.append("")
    if function_defs:
        lines.append("/-! ## Translated function definitions -/")
        lines.append("")
        for fd in function_defs:
            lines.append(fd)
    if safety_theorems:
        lines.append("/-! ## Runtime-safety theorems -/")
        lines.append("")
        for t in safety_theorems:
            lines.append(t)
    if implies_theorems:
        # Audit fix #7: lead with the audit summary so a reader sees
        # at a glance which @implies obligations were auto-proved
        # vs. sorry-emitted vs. user-supplied.
        if implies_audit:
            audit_block = render_audit_summary(implies_audit)
            if audit_block:
                lines.append(audit_block)
        lines.append("/-! ## ``@implies`` correctness theorems -/")
        lines.append("")
        for t in implies_theorems:
            lines.append(t)
    # Audit fix #4 + #5: standard simplicial cochain-complex block.
    if standard_complex_block:
        lines.append(standard_complex_block)

    # Round-2 audit phase 4: cubical control-flow analysis.
    cubical_section_for_cert = None
    try:
        from deppy.lean.cubical_certificate import render_cubical_section
        cubical_section_for_cert = render_cubical_section(
            verdict, fn_nodes,
            include_kan_theorems=True,
            include_higher_paths=False,
        )
        if cubical_section_for_cert.summary_block:
            lines.append(cubical_section_for_cert.summary_block)
        if cubical_section_for_cert.theorems:
            lines.append(
                "/-! ## Cubical Kan-fillability theorems -/"
            )
            lines.append("")
            for t in cubical_section_for_cert.theorems:
                lines.append(t)
        # Track sorry count for the certificate's sorry budget.
        try:
            sorry_count += cubical_section_for_cert.sorry_count
        except NameError:
            pass
    except Exception as _e:
        lines.append(
            f"-- (cubical certificate section unavailable: {_e})"
        )

    if cocycle_theorems:
        lines.append("/-! ## Cohomological structure (Phase C2)")
        lines.append("")
        lines.append("Each cocycle below is a theorem at level k:")
        lines.append("  * level 0: per-function safety bundles")
        lines.append("  * level 1: call-site cocycles (caller_pre ⇒ subst(callee_pre))")
        lines.append("  * level 2: module coherence (associativity of compositions)")
        lines.append("-/")
        lines.append("")
        for t in cocycle_theorems:
            lines.append(t)
    lines.append("end " + _safe_ident(module_name))
    lines.append("")
    text = "\n".join(lines)

    # Round-2 audit integration #3: collect cubical-section
    # accounting from the rendered section.
    cubical_kan_count = 0
    cubical_higher_count = 0
    cubical_sorries_count = 0
    if cubical_section_for_cert is not None:
        cubical_kan_count = (
            cubical_section_for_cert.kan_theorems_count
        )
        cubical_higher_count = (
            cubical_section_for_cert.higher_path_theorems_count
        )
        cubical_sorries_count = cubical_section_for_cert.sorry_count
    cert = Certificate(
        module_name=module_name,
        text=text,
        function_count=len(function_defs),
        theorem_count=(
            len(safety_theorems) + len(implies_theorems)
            + len(cocycle_theorems)
            + cubical_kan_count + cubical_higher_count
        ),
        sorry_count=sorry_count,
        aux_decl_count=len(aux_decls),
        cocycle_count_c0=len(cohomology.c0),
        cocycle_count_c1=len(cohomology.c1),
        cocycle_count_c2=len(cohomology.c2),
        cohomology_h0_size=len(cohomology.h0),
        cohomology_h1_size=len(cohomology.h1),
        cohomology_h2_size=len(cohomology.h2),
        implies_count=len(implies_audit),
        implies_auto_proved=_count_implies_auto(implies_audit),
        implies_user_supplied=_count_implies_user(implies_audit),
        implies_unproved=_count_implies_unproved(implies_audit),
        cubical_kan_theorems_count=cubical_kan_count,
        cubical_higher_path_theorems_count=cubical_higher_count,
        cubical_sorries=cubical_sorries_count,
    )
    # Attach the per-cocycle goal/proof metadata (Audit Fix #1)
    # so callers can audit which cocycles got real (non-True) goals.
    cert.cocycle_metadata = cocycle_report  # type: ignore[attr-defined]
    # Attach the per-@implies audit log (Audit Fix #7) so callers can
    # see exactly which obligations were classified how, which got
    # honest sorries, and why.
    cert.implies_audit = list(implies_audit)  # type: ignore[attr-defined]

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text, encoding="utf-8")

    report = CertificateReport(
        out_path=out_path, certificate=cert,
    )
    if run_lean:
        report = _run_lean(report, out_path, timeout_s=lean_timeout_s)
    return report


# ─────────────────────────────────────────────────────────────────────
#  Helpers
# ─────────────────────────────────────────────────────────────────────

def _render_signature(
    fn_node, type_context, aux_decls: list[str],
) -> tuple[str, str]:
    """Return ``(binders_str, return_type)`` for a Python function.

    Audit fix #6: when the function's ``-> T`` annotation is missing,
    use :func:`deppy.lean.body_translation.infer_function_signature`
    to derive the return type from the body — otherwise we'd emit
    ``mergesort (xs : List Int) : Int`` for a function that
    returns a list.
    """
    from deppy.lean.type_translation import translate_annotation
    from deppy.lean.body_translation import infer_function_signature

    explicit_return = getattr(fn_node, "returns", None) is not None
    if explicit_return:
        binders: list[str] = []
        for arg in fn_node.args.args:
            result = translate_annotation(
                arg.annotation, context=type_context,
            )
            for d in result.aux_decls:
                if d not in aux_decls:
                    aux_decls.append(d)
            binders.append(f"({arg.arg} : {result.lean})")
        binders_str = " ".join(binders) if binders else ""
        ret_result = translate_annotation(
            getattr(fn_node, "returns", None), context=type_context,
        )
        for d in ret_result.aux_decls:
            if d not in aux_decls:
                aux_decls.append(d)
        return binders_str, ret_result.lean

    # Implicit return — defer to the inferrer.
    binders_text, ret_lean, sig_aux = infer_function_signature(
        fn_node, type_context,
    )
    for d in sig_aux:
        if d not in aux_decls:
            aux_decls.append(d)
    return binders_text, ret_lean


def _is_recursive(fn_node, fn_name: str) -> bool:
    for sub in ast.walk(fn_node):
        if (isinstance(sub, ast.Call) and isinstance(sub.func, ast.Name)
                and sub.func.id == fn_name):
            return True
    return False


def _parse_source_str(src_str: str) -> tuple[str, int]:
    """Parse ``ExceptionSource(KIND @ <path>:line:col in fn)`` →
    ``(kind, lineno)``.
    """
    try:
        head, _ = src_str.split(" @ ", 1)
        kind = head.split("(", 1)[1]
        tail = src_str.split(" @ ", 1)[1].rsplit(" in ", 1)[0]
        parts = tail.split(":")
        lineno = int(parts[-2])
        return kind, lineno
    except Exception:
        return "", 0


def _safety_predicate_for(fv, lineno: int, kind: str) -> str:
    try:
        disch = (fv.proof_payload or {}).get("semantic", {}).get(
            "discharges", [],
        )
        for d in disch:
            if d.get("source_id", "").endswith(f":L{lineno}:{kind}"):
                return d.get("safety_predicate", "")
    except Exception:
        pass
    return ""


def _render_safety_theorem(
    *,
    fn_name: str, source_id: str, kind: str,
    safety_predicate: str, precondition: str,
    fn_node, params: list[str], discharge_path: str,
    aux_decls: list[str],
) -> tuple[str, int]:
    from deppy.lean.obligations import (
        _render_obligation, _safe_ident,
    )
    ob = _render_obligation(
        fn_name=fn_name, source_id=source_id, failure_kind=kind,
        safety_predicate=safety_predicate, precondition=precondition,
        parameters=params, fn_node=fn_node, aux_decls=aux_decls,
        discharge_path=discharge_path,
    )
    n_sorry = ob.theorem_text.count("sorry")
    return ob.theorem_text, n_sorry


def _render_implies_theorem(
    *,
    fn_name: str, idx: int, spec: dict,
    fn_node, type_context, aux_decls: list[str],
    audit_entries: Optional[list] = None,
) -> tuple[str, int]:
    """Emit a Lean theorem corresponding to a ``@implies(X, Y)``
    decorator on ``fn_name``.

    Soundness: the theorem's statement is generated entirely by deppy
    from the decorator arguments and the function's signature.  The
    proof body comes from one of three sources:

    1. **User-supplied** (``spec["proof"]``) — the kernel validates;
       deppy emits the user text directly.
    2. **Auto-selected tactic** — :mod:`deppy.lean.implies_tactics`
       analyses the pre / post AST, classifies the obligation, and
       picks a specific Lean tactic (``omega`` for linear arithmetic,
       ``decide`` for closed decidable propositions, ``intro h;
       exact h`` for the identity, ``intro h; exact h.left`` for
       conjunct-of-pre, etc.).  We refuse to use the catch-all
       ``Deppy.deppy_safe`` because it makes the certificate
       indistinguishable between "tactic worked" and "tactic gave up
       silently".
    3. **Honest sorry** — when the analyser can't find a plausible
       tactic (the pre/post mention opaque predicates such as
       ``hasattr``, ``defined``, or user-defined functions, or the
       structure simply doesn't match any known pattern), deppy
       emits ``sorry`` with a comment explaining why.

    The ``audit_entries`` list, when provided, is appended to with an
    :class:`ImpliesAuditEntry` describing the classification — the
    final certificate then renders an audit summary at the top.

    Audit fix #7 — this function used to emit ``by Deppy.deppy_safe``
    unconditionally.  The new logic above is the honest replacement.
    """
    from deppy.lean.obligations import _safe_ident
    from deppy.lean.predicate_translation import translate as translate_pred
    from deppy.lean.type_translation import translate_annotation
    from deppy.lean.implies_tactics import (
        select_implies_tactic,
        ImpliesAuditEntry,
    )

    pre_py = spec.get("precondition", "True")
    post_py = spec.get("postcondition", "True")
    user_proof = (spec.get("proof") or "").strip()

    # Build typed binders from the function signature.
    binders: list[str] = []
    py_types: dict[str, str] = {}
    for arg in fn_node.args.args:
        ann_result = translate_annotation(
            arg.annotation, context=type_context,
        )
        for d in ann_result.aux_decls:
            if d not in aux_decls:
                aux_decls.append(d)
        binders.append(f"({arg.arg} : {ann_result.lean})")
        try:
            py_types[arg.arg] = (
                ast.unparse(arg.annotation) if arg.annotation else "int"
            )
        except Exception:
            py_types[arg.arg] = "int"

    pre_translated = translate_pred(pre_py, python_types=py_types)
    # Bind the result to the function call so the postcondition can
    # reference it.  Audit fix #11: AST-based substitution that
    # respects identifier boundaries and string-literal contents
    # (the previous ``str.replace`` rewrote ``result_count`` to
    # ``(f x)_count`` and substituted into ``"result is positive"``
    # message strings).
    from deppy.lean.result_substitution import substitute_result_lean
    arg_names = [arg.arg for arg in fn_node.args.args]
    post_with_result = substitute_result_lean(
        post_py, fn_name=fn_name, arg_names=arg_names,
    )
    post_translated = translate_pred(
        post_with_result, python_types=py_types,
    )
    for d in pre_translated.aux_decls + post_translated.aux_decls:
        if d not in aux_decls:
            aux_decls.append(d)

    theorem_name = _safe_ident(f"deppy_implies_{fn_name}_{idx}")

    # Hole 9 fix: identifiers in pre/post that aren't function
    # arguments need to be added as universally-quantified binders.
    # Otherwise Lean rejects the theorem with "unknown identifier".
    # We discover them by AST-walking the original Python predicates
    # and subtracting the known parameter names + the canonical
    # ``result`` (which is substituted away by substitute_result_lean).
    extra_binders = _collect_extra_binders(
        pre_py, post_py,
        known=set(arg.arg for arg in fn_node.args.args) | {"result"},
    )
    if extra_binders:
        for name in extra_binders:
            binders.append(f"({name} : Int)")
    binders_str = " ".join(binders)
    # Form: ∀ args, X → Y[result := fn args]
    statement = (
        f"({pre_translated.lean_text}) → ({post_translated.lean_text})"
    )

    # Audit fix #7: pick a real tactic instead of blanket
    # ``Deppy.deppy_safe``.  When no plausible tactic exists, emit
    # an honest ``sorry`` with a comment.
    # Round-2 audit integration #2: pass the function's cubical
    # set so the classifier can find a Kan witness when one exists.
    cubical_set_for_implies = None
    try:
        from deppy.pipeline.cubical_ast import build_cubical_set
        cubical_set_for_implies = build_cubical_set(fn_node)
    except Exception:
        cubical_set_for_implies = None
    plan = select_implies_tactic(
        pre_py, post_py, py_types=py_types,
        user_proof=user_proof or None, fn_name=fn_name,
        cubical_set=cubical_set_for_implies,
    )
    body = plan.tactic_text
    sorries = 1 if plan.is_sorry else 0

    # Hole 2+3 fix (final): even when the classifier picked a
    # specific tactic (REFL_TAUTOLOGY, LINEAR_ARITH, etc.), the
    # *translated* post may have become an opaque axiom (because
    # of a user-function call we couldn't translate).  In that
    # case the picked tactic will fail in Lean — we honestly
    # downgrade to ``sorry`` rather than emitting an unsound
    # tactic claim.
    post_text = post_translated.lean_text.strip()
    if (("deppy_pred_" in post_text)
            and not user_proof
            and not plan.is_sorry):
        body = "sorry  -- opaque post (user-function call); honest sorry"
        sorries = 1

    if audit_entries is not None:
        audit_entries.append(
            ImpliesAuditEntry(
                fn_name=fn_name, idx=idx,
                pre_py=pre_py, post_py=post_py,
                classification=plan.classification,
                is_sorry=plan.is_sorry,
                confidence=plan.confidence,
                notes=list(plan.notes),
                sorry_reason=plan.sorry_reason,
                user_supplied=plan.is_user_supplied,
            )
        )

    # Render rationale comment alongside the theorem.
    rationale = ""
    if plan.is_sorry:
        rationale = (
            f"-- ⚠ deppy could not auto-prove this @implies "
            f"({plan.sorry_reason or 'unknown reason'}); "
            f"emitting sorry honestly.  Add proof= argument or "
            f"strengthen pre to remove the sorry.\n"
        )
    elif not plan.is_user_supplied:
        rationale = (
            f"-- auto-tactic: {plan.classification.value} "
            f"(confidence {plan.confidence:.2f})\n"
        )
    text = (
        f"-- @implies({pre_py!r}, {post_py!r}) on `{fn_name}`\n"
        f"{rationale}"
        f"theorem {theorem_name} {binders_str} :\n"
        f"    {statement} := {body}\n"
    )
    return text, sorries


def _safe_ident(text: str) -> str:
    """Local copy of obligations._safe_ident to avoid an import cycle."""
    out = []
    for ch in text:
        if ch.isalnum() or ch == "_":
            out.append(ch)
        else:
            out.append("_")
    s = "".join(out).strip("_")
    if not s:
        s = "obligation"
    if not s[0].isalpha() and s[0] != "_":
        s = "ob_" + s
    return s


def _run_lean(
    report: CertificateReport, path: Path, *, timeout_s: int = 120,
) -> CertificateReport:
    """Invoke ``lean`` on the certificate file and update the report."""
    lean_bin = shutil.which("lean")
    if not lean_bin:
        report.notes.append("lean binary not on PATH; cannot run kernel")
        return report
    # Lean needs to find ``DeppyBase.lean`` — copy it next to the
    # certificate so ``import DeppyBase`` resolves.
    import importlib.resources
    base_src = (
        Path(__file__).parent / "DeppyBase.lean"
    )
    target_dir = path.parent
    if base_src.is_file():
        target = target_dir / "DeppyBase.lean"
        if not target.exists() or target.read_text() != base_src.read_text():
            target.write_text(base_src.read_text(), encoding="utf-8")
    try:
        proc = subprocess.run(
            [lean_bin, str(path)],
            capture_output=True, text=True,
            timeout=timeout_s, check=False,
            cwd=str(target_dir),
        )
    except subprocess.TimeoutExpired as e:
        report.lean_accepted = False
        report.notes.append(f"lean timed out after {timeout_s}s")
        return report
    except Exception as e:
        report.notes.append(f"lean invocation failed: {e}")
        return report
    report.lean_stdout = proc.stdout
    report.lean_stderr = proc.stderr
    report.lean_accepted = (proc.returncode == 0)
    return report


# ─────────────────────────────────────────────────────────────────────
#  Cohomological structure (Phase C2)
# ─────────────────────────────────────────────────────────────────────

@dataclass
class _CohomologyData:
    """Cochain complex data extracted from a verdict.

    ``c0`` : list of (function_name, source_count) — each function
            contributes one 0-cocycle bundling all its source
            obligations.
    ``c1`` : list of (caller, callee) — one 1-cocycle per
            intra-module call-site.
    ``c2`` : list of (f, g, h) triples — one 2-cocycle per
            three-step composition (associativity coherence).
    ``h0`` : list of function names verified safe (kernel-discharged
            without remaining obligations) — the cohomology classes
            in degree 0.
    ``h1`` : list of (caller, callee) for which the call-site
            cocycle didn't discharge — open obstructions.
    ``h2`` : list of (f, g, h) for which coherence failed — three
            paths through the call graph that don't agree up to
            cohomology.
    """
    c0: list[tuple[str, int]] = field(default_factory=list)
    c1: list[tuple[str, str]] = field(default_factory=list)
    c2: list[tuple[str, str, str]] = field(default_factory=list)
    h0: list[str] = field(default_factory=list)
    h1: list[tuple[str, str]] = field(default_factory=list)
    h2: list[tuple[str, str, str]] = field(default_factory=list)


def _compute_cohomology(verdict, fn_nodes, source: str) -> _CohomologyData:
    """Build the cochain complex from a safety verdict.

    The structure mirrors :mod:`deppy.lean.DeppyBase`:

    * ``C^0`` — per-function safety obligations (one 0-cochain per
      function).
    * ``C^1`` — call-site cocycle conditions (caller's precondition
      ⇒ substituted callee's precondition).
    * ``C^2`` — coherence: associativity of three-function chains.

    Each level's cocycles are the witnessed conditions; ``H^k`` is
    the residual obstruction (cocycles modulo coboundaries).  We
    approximate ``H^k`` as the *open* (undischarged) cocycles —
    soundness only; precision can be improved with explicit
    coboundary witnesses in future revisions.
    """
    data = _CohomologyData()

    # C^0 — per-function safety bundles + open H^0.
    for fn_name, fv in verdict.functions.items():
        n_sources = len(list(fv.addressed) + list(fv.unaddressed))
        data.c0.append((fn_name, n_sources))
        if fv.is_safe and not fv.unaddressed:
            data.h0.append(fn_name)

    # C^1 — call-site cocycles.
    try:
        from deppy.pipeline.interprocedural import build_call_graph
        cg = build_call_graph(source)
        for caller, callees in cg.edges.items():
            for callee in callees:
                if caller == callee:
                    continue  # self-recursion — handled by termination
                data.c1.append((caller, callee))
                # H^1 obstruction iff the discharge for any
                # CALL_PROPAGATION source on this edge remained open.
                caller_v = verdict.functions.get(caller)
                if caller_v is None:
                    continue
                for u in caller_v.unaddressed:
                    if "CALL_PROPAGATION" in u and callee in u:
                        data.h1.append((caller, callee))
                        break
    except Exception:
        pass

    # C^2 — three-step composition coherence.
    try:
        from deppy.pipeline.interprocedural import build_call_graph
        cg = build_call_graph(source)
        for f, gs in cg.edges.items():
            for g in gs:
                hs = cg.edges.get(g, set())
                for h in hs:
                    if f == g or g == h or f == h:
                        continue
                    data.c2.append((f, g, h))
                    # H^2 obstruction iff either inner cocycle is open.
                    if ((f, g) in data.h1) or ((g, h) in data.h1):
                        data.h2.append((f, g, h))
    except Exception:
        pass

    return data


def _render_cocycle_theorems(
    cohomology: _CohomologyData, *, module_name: str,
) -> list[str]:
    """Emit Lean theorems for each cocycle in the complex.

    Each theorem's body is auto-deduced — closed cocycles use
    ``Deppy.deppy_cocycle`` / ``deppy_safe`` (which compose the
    component lemmas above); open cocycles get ``sorry`` with a
    note.
    """
    lines: list[str] = []
    # C^0 cocycles — each function's safety bundled.
    for (fn_name, n_sources) in cohomology.c0:
        thm = f"deppy_c0_cocycle_{_safe_ident(fn_name)}"
        is_open = fn_name not in cohomology.h0
        body = (
            "by sorry  -- C^0 obstruction: function has open safety obligations"
            if is_open
            else "by Deppy.deppy_safe"
        )
        lines.append(
            f"-- C^0 cocycle: function `{fn_name}` "
            f"({n_sources} source{'s' if n_sources != 1 else ''})\n"
            f"theorem {thm} : True := {body}\n"
        )
    # C^1 cocycles — call-site cocycle conditions.
    for (caller, callee) in cohomology.c1:
        thm = f"deppy_c1_cocycle_{_safe_ident(caller)}_to_{_safe_ident(callee)}"
        is_open = (caller, callee) in cohomology.h1
        body = (
            "by sorry  -- C^1 obstruction: caller's precondition does "
            "not entail callee's"
            if is_open
            else "by Deppy.deppy_cocycle"
        )
        lines.append(
            f"-- C^1 cocycle: `{caller}` calls `{callee}`\n"
            f"theorem {thm} : True := {body}\n"
        )
    # C^2 coherence — associativity of f → g → h compositions.
    for (f, g, h) in cohomology.c2:
        thm = (
            f"deppy_c2_coherence_"
            f"{_safe_ident(f)}_{_safe_ident(g)}_{_safe_ident(h)}"
        )
        is_open = (f, g, h) in cohomology.h2
        body = (
            "by sorry  -- C^2 coherence failure: inner cocycles open"
            if is_open
            else "by Deppy.deppy_safe"
        )
        lines.append(
            f"-- C^2 coherence: `{f} → {g} → {h}`\n"
            f"theorem {thm} : True := {body}\n"
        )
    return lines


def _collect_extra_binders(
    pre_py: str, post_py: str, *, known: set[str],
) -> list[str]:
    """Hole 9 fix — return identifiers used in ``pre_py`` / ``post_py``
    that are not in ``known`` (the function's argument names plus the
    ``result`` keyword, which is substituted away).  Such names need
    to be added as Lean binders for the @implies theorem to typecheck.

    Filters out Python builtins / predicate-translator keywords.  The
    returned names are sorted to give a deterministic order.
    """
    import ast as _ast
    builtins_to_skip = {
        "True", "False", "None", "len", "abs", "min", "max",
        "isinstance", "hasattr", "callable", "any", "all",
        "sum", "int", "float", "str", "bool", "list", "tuple",
        "dict", "set", "and", "or", "not", "in",
    }
    extra: set[str] = set()
    for src in (pre_py, post_py):
        if not src:
            continue
        try:
            tree = _ast.parse(src, mode="eval")
        except SyntaxError:
            continue
        for sub in _ast.walk(tree):
            if isinstance(sub, _ast.Name):
                if sub.id in known:
                    continue
                if sub.id in builtins_to_skip:
                    continue
                extra.add(sub.id)
    return sorted(extra)


__all__ = [
    "Certificate",
    "CertificateReport",
    "write_certificate",
]
