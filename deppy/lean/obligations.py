"""Lean proof obligation emission.

When the safety pipeline cannot discharge a runtime-safety source via
Z3, the syntactic shortcut, the builtin sidecar, callee summaries, or
a user-attached Lean proof, the source remains *open*.  This module
emits a Lean-4 file with one ``theorem ... := by sorry`` per open
source, which a human or LLM can fill in and feed back through
``deppy check`` (via ``--sidecar`` or ``@with_lean_proof``) to close
the obligation.

Public API::

    emit_obligations(
        source_or_path: str,         # source code or file path
        out_path: Path | str,        # write the .lean file here
    ) -> ObligationReport

The emitted file is intentionally human-readable and stable — names
are deterministic so re-running deppy reuses the same theorem names
and a partially-filled ``.lean`` survives re-emission.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Optional


# ─────────────────────────────────────────────────────────────────────
#  Output dataclasses
# ─────────────────────────────────────────────────────────────────────

@dataclass
class Obligation:
    """One open proof obligation emitted to the .lean file."""
    function_name: str
    source_id: str        # e.g. "f:L4:ZERO_DIVISION"
    failure_kind: str     # "ZERO_DIVISION" / "KEY_ERROR" / ...
    safety_predicate: str # the canonical Python-syntax predicate
    precondition: str     # function-wide precondition (Python syntax)
    parameters: list[str] # formal parameter names (for hypothesis binding)
    theorem_name: str     # stable Lean identifier
    theorem_text: str     # the rendered ``theorem ... := by sorry`` block

    def __repr__(self) -> str:
        return f"Obligation({self.theorem_name})"


@dataclass
class ObligationReport:
    """Result of an obligation-emission run."""
    module_path: str
    out_path: Path
    obligations: list[Obligation] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)

    @property
    def open_count(self) -> int:
        return len(self.obligations)

    def summary(self) -> str:
        if not self.obligations:
            return f"No open obligations in {self.module_path}."
        lines = [
            f"{self.open_count} open obligation(s) in {self.module_path}:",
        ]
        for o in self.obligations:
            lines.append(f"  - {o.function_name}: {o.source_id}")
        lines.append(f"Wrote skeleton to {self.out_path}")
        return "\n".join(lines)


# ─────────────────────────────────────────────────────────────────────
#  Predicate translation: Python syntax → Lean syntax
# ─────────────────────────────────────────────────────────────────────

# Conservative mapping for the predicate kinds the safety pipeline
# emits.  Anything we cannot translate becomes a Lean comment so the
# user retains the original.
_PY_TO_LEAN_REPLACEMENTS: list[tuple[str, str]] = [
    # Comparison operators
    (" != ", " ≠ "),
    (" == ", " = "),
    (" and ", " ∧ "),
    (" or ", " ∨ "),
    (" not ", " ¬ "),
    # Membership reads naturally in Lean (List.mem / dict)
    # but Lean surface syntax differs — leave as a comment for now.
]


def _py_predicate_to_lean(pred: str) -> tuple[str, list[str], list[str]]:
    """Lean translation of a Python-syntax predicate.

    Soundness fix F4: never returns ``True`` as a fallback.  When
    the predicate cannot be cleanly translated, we emit an *opaque
    Lean Prop* (axiomatised via ``axiom deppy_pred_<hash> : Prop``)
    so the user cannot accidentally discharge it with ``trivial``.

    Returns
    -------
    ``(lean_text, aux_decls, notes)``

    * ``lean_text`` — the Lean term to use as the theorem's goal.
    * ``aux_decls`` — auxiliary ``axiom`` declarations the .lean file
      must include (deterministic across runs).
    * ``notes`` — informational comments the emitter inlines into
      the theorem's preamble.
    """
    from deppy.lean.predicate_translation import translate
    result = translate(pred)
    return result.lean_text, list(result.aux_decls), list(result.notes)


def _python_param_type_to_lean(
    ann: Optional[str],
    *,
    aux_decls: Optional[list[str]] = None,
    notes: Optional[list[str]] = None,
    known_classes: Iterable[str] = (),
) -> str:
    """Translate a Python annotation string to a Lean 4 type.

    Delegates to :mod:`deppy.lean.type_translation` so the same rules
    apply across the obligation emitter and the pipeline's
    ``LeanProof`` discharge.  Handles ``Union``, ``Optional``,
    ``Any``, ``Callable``, generic containers, and user-defined
    classes.
    """
    if ann is None or ann == "":
        return "Int"
    from deppy.lean.type_translation import translate_annotation_str
    result = translate_annotation_str(ann, known_classes=known_classes)
    if aux_decls is not None:
        for d in result.aux_decls:
            if d not in aux_decls:
                aux_decls.append(d)
    if notes is not None:
        notes.extend(result.notes)
    return result.lean


# ─────────────────────────────────────────────────────────────────────
#  Theorem rendering
# ─────────────────────────────────────────────────────────────────────

def _safe_ident(text: str) -> str:
    """Sanitize ``text`` to a Lean identifier: alphanumerics + underscore."""
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


def _render_obligation(
    *,
    fn_name: str,
    source_id: str,
    failure_kind: str,
    safety_predicate: str,
    precondition: str,
    parameters: list[str],
    fn_node=None,
    aux_decls: list[str] | None = None,
) -> Obligation:
    pre_lean, pre_aux, pre_notes = _py_predicate_to_lean(precondition)
    goal_lean, goal_aux, goal_notes = _py_predicate_to_lean(safety_predicate)

    # Aggregate auxiliary axiom declarations for the parent emitter.
    if aux_decls is not None:
        for decl in pre_aux + goal_aux:
            if decl not in aux_decls:
                aux_decls.append(decl)

    theorem_name = _safe_ident(f"deppy_{fn_name}_{source_id}")

    # Build the typed parameter list, threading any auxiliary
    # axiom declarations from the type translator into the parent
    # ``aux_decls`` list so the obligations file emits each unique
    # opaque type / class declaration exactly once.
    typed_params: list[str] = []
    if fn_node is not None:
        try:
            import ast as _ast
            for arg in fn_node.args.args:
                ann = None
                if arg.annotation is not None:
                    try:
                        ann = _ast.unparse(arg.annotation)
                    except Exception:
                        ann = None
                ty = _python_param_type_to_lean(
                    ann, aux_decls=aux_decls,
                )
                typed_params.append(f"({arg.arg} : {ty})")
        except Exception:
            typed_params = [f"({p} : Int)" for p in parameters]
    else:
        typed_params = [f"({p} : Int)" for p in parameters]

    binders = " ".join(typed_params)
    pre_hyp = f"(h_pre : {pre_lean})" if pre_lean.strip() != "True" else ""
    full_binders = (binders + " " + pre_hyp).strip() if pre_hyp else binders

    body = "by\n    -- TODO: fill in the proof.\n    sorry"
    theorem_text = (
        f"-- Source: {source_id} ({failure_kind}) in function {fn_name!r}\n"
        f"-- Safety predicate (Python): {safety_predicate}\n"
        f"-- Precondition (Python):     {precondition or 'True'}\n"
    )
    for n in pre_notes + goal_notes:
        theorem_text += f"-- NOTE: {n}\n"

    if pre_hyp:
        theorem_text += (
            f"theorem {theorem_name} {full_binders} :\n"
            f"    ({goal_lean}) := {body}\n"
        )
    else:
        theorem_text += (
            f"theorem {theorem_name} {binders} :\n"
            f"    ({goal_lean}) := {body}\n"
        )

    return Obligation(
        function_name=fn_name,
        source_id=source_id,
        failure_kind=failure_kind,
        safety_predicate=safety_predicate,
        precondition=precondition,
        parameters=parameters,
        theorem_name=theorem_name,
        theorem_text=theorem_text,
    )


# ─────────────────────────────────────────────────────────────────────
#  Public entry point
# ─────────────────────────────────────────────────────────────────────

def emit_obligations(
    source: str,
    out_path: Path | str,
    *,
    sidecar_specs: Optional[dict] = None,
    use_drafts: bool = True,
    module_name: str = "DeppyObligations",
) -> ObligationReport:
    """Run the safety pipeline and emit a Lean file with the open obligations.

    Parameters
    ----------
    source :
        Python source code (string).
    out_path :
        Where to write the rendered ``.lean`` skeleton.
    sidecar_specs :
        Optional ``{name: ExternalSpec}`` to feed the safety pipeline.
    use_drafts :
        Whether to use auto-inferred drafts (default ``True``).

    Returns
    -------
    ObligationReport
        The emitted obligations and the output path.
    """
    import ast
    from deppy.pipeline.safety_pipeline import verify_module_safety

    out_path = Path(out_path)
    verdict = verify_module_safety(
        source, sidecar_specs=sidecar_specs, use_drafts=use_drafts,
    )

    # Re-run a lightweight AST walk so we have parameter names per
    # function for the theorem binders.
    try:
        tree = ast.parse(source)
    except SyntaxError as e:
        return ObligationReport(
            module_path="<unparseable>", out_path=out_path,
            notes=[f"failed to parse: {e}"],
        )
    fn_nodes: dict[str, ast.FunctionDef | ast.AsyncFunctionDef] = {}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            fn_nodes.setdefault(node.name, node)

    obligations: list[Obligation] = []
    notes: list[str] = []
    aux_decls: list[str] = []
    for fn_name, fv in verdict.functions.items():
        if not fv.unaddressed:
            continue
        # Pull function-wide precondition.
        spec = (sidecar_specs or {}).get(fn_name)
        if spec is None:
            precondition = "True"
        else:
            efw = list(getattr(spec, "exception_free_when", None) or [])
            precondition = " and ".join(efw) if efw else "True"
        node = fn_nodes.get(fn_name)
        params = (
            [a.arg for a in node.args.args] if node is not None else []
        )
        for u in fv.unaddressed:
            # Parse the unaddressed string back to a source-id.
            # Format: "ExceptionSource(KIND @ <path>:line:col in fn)"
            kind = ""
            lineno = 0
            col = 0
            try:
                head, _ = u.split(" @ ", 1)
                kind = head.split("(", 1)[1]
                # ``<path>:line:col in fn``
                tail = u.split(" @ ", 1)[1].rsplit(" in ", 1)[0]
                # Splitting on : works because path here is "<string>"
                parts = tail.split(":")
                lineno = int(parts[-2])
                col = int(parts[-1].rstrip(")"))
            except Exception:
                pass

            source_id = f"{fn_name}_L{lineno}_{kind}"
            # The safety_predicate isn't on the verdict directly, but
            # we can reconstruct it from the discharge payload.
            safety_pred = ""
            try:
                disch = (fv.proof_payload or {}).get("semantic", {}).get(
                    "discharges", [],
                )
                for d in disch:
                    if d.get("source_id", "").endswith(f":L{lineno}:{kind}"):
                        safety_pred = d.get("safety_predicate", "")
                        break
            except Exception:
                pass
            # Soundness fix F4: if we can't recover the safety
            # predicate, emit an opaque Prop (NOT ``True``) so the
            # user can't trivially discharge the obligation.
            if not safety_pred:
                safety_pred = f"undischarged_{kind}_at_L{lineno}"

            ob = _render_obligation(
                fn_name=fn_name, source_id=source_id,
                failure_kind=kind, safety_predicate=safety_pred,
                precondition=precondition, parameters=params,
                fn_node=node, aux_decls=aux_decls,
            )
            obligations.append(ob)

    # Render the file.
    out_lines = [
        f"-- Auto-generated by `deppy obligations`.",
        f"-- Module: {module_name}",
        f"-- Open obligations: {len(obligations)}",
        f"-- Edit ``sorry`` to provide a Lean proof, then attach with",
        f"--    @with_lean_proof(proof=..., for_kind=...)",
        f"-- and re-run ``deppy check``.",
        f"--",
        f"-- Soundness note: deppy synthesises the theorem statement",
        f"-- from the safety predicate, so the user supplies *only* the",
        f"-- proof body.  ``trivial`` will not work for predicates that",
        f"-- translate to opaque ``Prop`` axioms — the user must produce",
        f"-- a real witness or refine the axiom.",
        "",
    ]
    if aux_decls:
        out_lines.append(
            "-- Auxiliary opaque-Prop declarations for predicates that")
        out_lines.append(
            "-- could not be cleanly translated to native Lean.")
        out_lines.append(
            "-- The user is expected to either replace them with a")
        out_lines.append(
            "-- concrete definition or provide a proof another way.")
        for decl in aux_decls:
            out_lines.append(decl)
        out_lines.append("")
    out_lines.append("namespace " + _safe_ident(module_name))
    out_lines.append("")
    for ob in obligations:
        out_lines.append(ob.theorem_text)
        out_lines.append("")
    out_lines.append("end " + _safe_ident(module_name))
    out_lines.append("")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(out_lines), encoding="utf-8")

    return ObligationReport(
        module_path=getattr(verdict, "module_path", "<module>"),
        out_path=out_path, obligations=obligations, notes=notes,
    )


__all__ = [
    "Obligation",
    "ObligationReport",
    "emit_obligations",
]
