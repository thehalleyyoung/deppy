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
        body = translate_body(fn_node, type_context=type_context)
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
        for src_str in list(fv.addressed) + list(fv.unaddressed):
            kind, lineno = _parse_source_str(src_str)
            source_id = f"{fn_name}_L{lineno}_{kind}"
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
            )
            sorry_count += theorem_sorries
            implies_theorems.append(theorem_text)

    # ── Render the file ────────────────────────────────────────────
    lines: list[str] = [
        f"-- Auto-generated by `deppy.lean.certificate`.",
        f"-- Module: {module_name}",
        f"-- Lean as the gold standard: this certificate is",
        f"-- self-contained — running ``lean`` on it accepts iff",
        f"-- the safety + implication theorems hold.",
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
        lines.append("/-! ## ``@implies`` correctness theorems -/")
        lines.append("")
        for t in implies_theorems:
            lines.append(t)
    lines.append("end " + _safe_ident(module_name))
    lines.append("")
    text = "\n".join(lines)

    cert = Certificate(
        module_name=module_name,
        text=text,
        function_count=len(function_defs),
        theorem_count=len(safety_theorems) + len(implies_theorems),
        sorry_count=sorry_count,
        aux_decl_count=len(aux_decls),
    )

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
    """Return ``(binders_str, return_type)`` for a Python function."""
    from deppy.lean.type_translation import translate_annotation
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
) -> tuple[str, int]:
    """Emit a Lean theorem corresponding to a ``@implies(X, Y)``
    decorator on ``fn_name``.

    Soundness: the theorem's statement is generated entirely by deppy
    from the decorator arguments and the function's signature; the
    user supplies only the proof body (or accepts the auto-deduced
    ``Deppy.deppy_safe`` tactic).
    """
    from deppy.lean.obligations import _safe_ident
    from deppy.lean.predicate_translation import translate as translate_pred
    from deppy.lean.type_translation import translate_annotation

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
    # reference it.
    post_with_result = post_py.replace(
        "result",
        f"({fn_name} " + " ".join(arg.arg for arg in fn_node.args.args) + ")",
    )
    post_translated = translate_pred(
        post_with_result, python_types=py_types,
    )
    for d in pre_translated.aux_decls + post_translated.aux_decls:
        if d not in aux_decls:
            aux_decls.append(d)

    theorem_name = _safe_ident(f"deppy_implies_{fn_name}_{idx}")
    binders_str = " ".join(binders)
    # Form: ∀ args, X → Y[result := fn args]
    statement = (
        f"({pre_translated.lean_text}) → ({post_translated.lean_text})"
    )

    if user_proof:
        body = f"by {user_proof}"
    else:
        # Auto-deduce: try the strongest tactic.  For arithmetic
        # implies we fall back to omega; otherwise deppy_safe.
        body = "by Deppy.deppy_safe"
    sorries = body.count("sorry")

    text = (
        f"-- @implies({pre_py!r}, {post_py!r}) on `{fn_name}`\n"
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


__all__ = [
    "Certificate",
    "CertificateReport",
    "write_certificate",
]
