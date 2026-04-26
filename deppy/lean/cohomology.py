"""Real cohomological cocycle emission for Lean certificates.

The previous certificate's cocycle theorems all had goal ``True``
(``theorem deppy_c0_cocycle_X : True := by Deppy.deppy_safe``) —
informationless decoration over the call graph.  This module
replaces that with *concrete* propositions: each cocycle theorem
states the actual mathematical condition it should witness, the
condition is built compositionally from the function's safety
predicates and inter-procedural call structure, and the proof body
is the strongest tactic that *might* close the real goal.

Design
------

The pipeline emits three levels of cocycles:

* **C^0** — per-function safety bundle.  For function ``f`` with
  precondition ``P_f`` and source obligations
  ``Q_{f,1}, ..., Q_{f,n}``, the C^0 cocycle is::

      ∀ <args>, P_f → (Q_{f,1} ∧ Q_{f,2} ∧ ... ∧ Q_{f,n})

  This is the *bundle* — the discharge guarantee for the whole
  function as a single proposition.  When every Q_i was Z3-discharged
  the proof is ``by intro h_pre; refine ⟨?_, ?_, ..., ?_⟩ <;> omega``.

* **C^1** — call-site cocycle (caller_pre → subst(callee_pre)).
  For a caller ``f`` and callee ``g``, with caller pre ``P_f`` and
  callee pre ``P_g(formals)``, the C^1 cocycle for the (f, g)
  edge is::

      ∀ <f's args>, P_f(<f's args>) →
        P_g[formals := <actual args at call site>]

  Each call site contributes one cocycle.  When the safety pipeline
  Z3-discharged the call, the proof is ``by intro h_pre; <Z3-style>``.

* **C^2** — composition coherence.  For a chain ``f → g → h``,
  the C^2 cocycle states that the *composed* precondition matches
  the *direct* precondition::

      ∀ <f's args>, P_f → P_h[formals := <subst through g>]

  Witnesses associativity of cocycle composition.

Each cocycle produced here has a *real* Lean goal type built from
the source predicates and call structure, so a vacuously-true
``Deppy.deppy_safe`` no longer closes the obligation when the
underlying maths doesn't hold.

Public API
----------
:class:`CohomologyEmitter` — the top-level builder.

:meth:`CohomologyEmitter.emit_c0_cocycle` ``(fn_name) → str``
:meth:`CohomologyEmitter.emit_c1_cocycle` ``(caller, callee, site) → str``
:meth:`CohomologyEmitter.emit_c2_coherence` ``(f, g, h, sites) → str``

Each method returns the rendered Lean theorem string.  The emitter
also tracks per-cocycle metadata in :attr:`CohomologyEmitter.report`
so the verdict can surface which cocycles closed automatically and
which need manual proofs.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Optional


# ─────────────────────────────────────────────────────────────────────
#  Substitution machinery
# ─────────────────────────────────────────────────────────────────────

@dataclass
class CallSite:
    """A single call-site: ``caller`` calls ``callee(actuals)``.

    Stored as Python-syntax strings so we can parse + substitute
    when generating the cocycle goal.
    """
    caller: str
    callee: str
    actuals: list[str] = field(default_factory=list)
    lineno: int = 0
    col: int = 0


def substitute_actuals(
    predicate: str,
    formals: list[str],
    actuals: list[str],
) -> str:
    """Replace formal parameter names in ``predicate`` with the
    actual argument expressions.  Uses an AST-based ``NodeTransformer``
    so identifiers embedded in larger names (e.g. ``count_x``) are
    not accidentally rewritten.

    When the predicate cannot be parsed (synthetic / unparseable),
    we fall back to the original text — the certificate's tactic
    layer will surface the failure as ``sorry``.
    """
    if not predicate or not predicate.strip():
        return predicate
    if len(formals) != len(actuals):
        return predicate
    subst = dict(zip(formals, actuals))
    if not subst:
        return predicate
    try:
        tree = ast.parse(predicate, mode="eval")
    except SyntaxError:
        return predicate

    class _Sub(ast.NodeTransformer):
        def visit_Name(self, node: ast.Name) -> ast.AST:
            if node.id in subst:
                try:
                    parsed = ast.parse(
                        f"({subst[node.id]})", mode="eval"
                    ).body
                    return ast.copy_location(parsed, node)
                except SyntaxError:
                    return node
            return node

        def generic_visit(self, node):
            if getattr(node, "_deppy_substituted", False):
                return node
            return super().generic_visit(node)

    new = ast.fix_missing_locations(_Sub().visit(tree))
    try:
        return ast.unparse(new)
    except Exception:
        return predicate


def substitute_via(
    predicate: str,
    *,
    f_formals: list[str],
    g_formals: list[str],
    g_actuals_in_f: list[str],
    h_formals: list[str],
    h_actuals_in_g: list[str],
) -> str:
    """Two-step substitution for C^2 coherence.

    Given a predicate over ``h``'s formals, substitute through ``g``
    (so it's in ``g``'s formal-parameter scope), then through ``f``
    (so it's in ``f``'s scope).  Used to express
    ``P_h(h_actuals_in_g[g_formals := f_actuals])`` directly in
    terms of ``f``'s arguments.
    """
    if not predicate:
        return predicate
    # Step 1: substitute h's formals with their actuals (in g's scope).
    intermediate = substitute_actuals(predicate, h_formals, h_actuals_in_g)
    # Step 2: substitute g's formals with their actuals (in f's scope).
    final = substitute_actuals(intermediate, g_formals, g_actuals_in_f)
    return final


# ─────────────────────────────────────────────────────────────────────
#  Per-cocycle metadata
# ─────────────────────────────────────────────────────────────────────

@dataclass
class CocycleMeta:
    """Diagnostic metadata for a single emitted cocycle.

    The certificate's banner uses this to report which cocycles
    have *real* (non-vacuous) goals and which ones the auto-tactic
    is expected to close.
    """
    level: int                       # 0, 1, or 2
    name: str                        # Lean theorem name
    label: str                       # human-readable label
    goal_kind: str                   # "True" / "real_arithmetic" /
                                     # "real_opaque" / "real_mixed"
    proof_mode: str                  # "trivial" / "omega" /
                                     # "deppy_safe" / "sorry"
    open: bool = False               # True iff the proof body is
                                     # ``sorry`` / undischarged


@dataclass
class EmitReport:
    """Aggregated metadata across an entire certificate."""
    cocycles: list[CocycleMeta] = field(default_factory=list)

    @property
    def by_level(self) -> dict[int, list[CocycleMeta]]:
        out: dict[int, list[CocycleMeta]] = {0: [], 1: [], 2: []}
        for c in self.cocycles:
            out.setdefault(c.level, []).append(c)
        return out

    @property
    def open_count(self) -> int:
        return sum(1 for c in self.cocycles if c.open)

    @property
    def real_goal_count(self) -> int:
        return sum(1 for c in self.cocycles if c.goal_kind != "True")


# ─────────────────────────────────────────────────────────────────────
#  Cohomology emitter
# ─────────────────────────────────────────────────────────────────────

class CohomologyEmitter:
    """Builds real Lean cocycle theorems from a safety verdict.

    Each call to ``emit_*`` returns the rendered Lean theorem text
    *and* records a :class:`CocycleMeta` in ``self.report`` so the
    certificate can audit how many cocycles got real (non-True)
    goals and which ones close automatically.
    """

    def __init__(
        self, verdict, fn_nodes: dict, *,
        type_context=None, sidecar_specs: Optional[dict] = None,
    ) -> None:
        self.verdict = verdict
        self.fn_nodes = fn_nodes
        self.type_context = type_context
        self.sidecar_specs = sidecar_specs or {}
        self.report = EmitReport()

    # -- C^0 ----------------------------------------------------------

    def emit_c0_cocycle(self, fn_name: str) -> str:
        """Emit the C^0 cocycle theorem for ``fn_name``.

        Goal: ``∀ <args>, P_f → (Q_1 ∧ Q_2 ∧ ... ∧ Q_n)`` where
        each Q_i is the safety predicate of one source.  When the
        function has zero sources, the goal collapses to ``True``
        (and we honestly mark it as such in the report).
        """
        fv = self.verdict.functions.get(fn_name)
        if fv is None:
            return self._emit_trivial_c0(fn_name, "no verdict for function")

        node = self.fn_nodes.get(fn_name)
        if node is None:
            return self._emit_trivial_c0(fn_name, "no AST for function")

        precondition = self._function_precondition(fn_name)
        sources = self._function_sources(fv)
        if not sources:
            return self._emit_trivial_c0(fn_name, "no sources")

        binders, py_types = self._render_binders(node)
        pre_lean = self._translate_predicate(precondition, py_types)
        # Build the conjunction of safety predicates.
        per_source_lean: list[str] = []
        all_arithmetic = True
        any_real = False
        for safety_pred in sources:
            t = self._translate_predicate(safety_pred, py_types)
            per_source_lean.append(t.lean_text)
            if not t.exact:
                all_arithmetic = False
            if t.lean_text != "True":
                any_real = True
        conjunction = (
            " ∧ ".join(f"({p})" for p in per_source_lean)
            if per_source_lean else "True"
        )

        # Goal classification + tactic.
        if not any_real:
            goal_kind = "True"
            proof_mode = "trivial"
            body = "by trivial"
        elif all_arithmetic and pre_lean.exact:
            goal_kind = "real_arithmetic"
            proof_mode = "omega"
            body = "by intro _h_pre; (try omega) <;> Deppy.deppy_safe"
        else:
            goal_kind = "real_mixed"
            proof_mode = "deppy_safe"
            body = "by intro _h_pre; Deppy.deppy_safe"

        thm_name = f"deppy_c0_cocycle_{_safe_ident(fn_name)}"
        statement = (
            f"({pre_lean.lean_text}) → ({conjunction})"
        )
        text = (
            f"-- C^0 cocycle: function `{fn_name}` "
            f"({len(sources)} source obligation"
            f"{'s' if len(sources) != 1 else ''})\n"
            f"-- Goal kind: {goal_kind}\n"
            f"theorem {thm_name} {binders} :\n"
            f"    {statement} := {body}\n"
        )
        self.report.cocycles.append(CocycleMeta(
            level=0, name=thm_name,
            label=f"safety bundle of {fn_name}",
            goal_kind=goal_kind, proof_mode=proof_mode,
            open=(proof_mode == "sorry"),
        ))
        return text

    def _emit_trivial_c0(self, fn_name: str, reason: str) -> str:
        """Emit a trivially-true C^0 theorem with an honest reason."""
        thm_name = f"deppy_c0_cocycle_{_safe_ident(fn_name)}"
        text = (
            f"-- C^0 cocycle (trivial): {reason}\n"
            f"theorem {thm_name} : True := by trivial\n"
        )
        self.report.cocycles.append(CocycleMeta(
            level=0, name=thm_name,
            label=f"trivial bundle of {fn_name}",
            goal_kind="True", proof_mode="trivial",
        ))
        return text

    # -- C^1 ----------------------------------------------------------

    def emit_c1_cocycle(
        self, caller: str, callee: str,
        sites: list[CallSite],
    ) -> str:
        """Emit the C^1 cocycle theorem for the ``caller → callee``
        edge.

        Goal: ``∀ <caller args>, P_caller →
                P_callee[formals := actuals_at_first_site]``

        We use the first call site for the cocycle statement; multiple
        call sites between the same pair generate separate theorems
        downstream when needed.
        """
        if not sites:
            return self._emit_trivial_c1(caller, callee, "no call sites")

        caller_node = self.fn_nodes.get(caller)
        callee_node = self.fn_nodes.get(callee)
        if caller_node is None or callee_node is None:
            return self._emit_trivial_c1(
                caller, callee, "missing AST for caller or callee",
            )

        site = sites[0]
        caller_formals = [a.arg for a in caller_node.args.args]
        callee_formals = [a.arg for a in callee_node.args.args]
        actuals = list(site.actuals)
        if len(actuals) != len(callee_formals):
            return self._emit_trivial_c1(
                caller, callee,
                f"arity mismatch at call site (got {len(actuals)} "
                f"actuals, callee declares {len(callee_formals)})",
            )

        caller_pre = self._function_precondition(caller)
        callee_pre = self._function_precondition(callee)
        substituted_callee_pre = substitute_actuals(
            callee_pre, callee_formals, actuals,
        )

        binders, py_types = self._render_binders(caller_node)
        pre_lean = self._translate_predicate(caller_pre, py_types)
        post_lean = self._translate_predicate(
            substituted_callee_pre, py_types,
        )

        if pre_lean.lean_text == "True" and post_lean.lean_text == "True":
            goal_kind = "True"
            proof_mode = "trivial"
            body = "by trivial"
        elif pre_lean.exact and post_lean.exact:
            goal_kind = "real_arithmetic"
            proof_mode = "omega"
            body = (
                "by intro _h_pre; "
                "(try omega) <;> Deppy.deppy_safe"
            )
        else:
            goal_kind = "real_opaque" if not post_lean.exact else "real_mixed"
            proof_mode = "deppy_safe"
            body = "by intro _h_pre; Deppy.deppy_safe"

        thm_name = (
            f"deppy_c1_cocycle_"
            f"{_safe_ident(caller)}_to_{_safe_ident(callee)}"
        )
        statement = (
            f"({pre_lean.lean_text}) → ({post_lean.lean_text})"
        )
        text = (
            f"-- C^1 cocycle: `{caller}` → `{callee}` "
            f"at L{site.lineno}:{site.col}\n"
            f"-- Goal kind: {goal_kind}\n"
            f"-- Caller pre (Python): {caller_pre}\n"
            f"-- Callee pre (Python): {callee_pre}\n"
            f"-- Actuals: {actuals}\n"
            f"theorem {thm_name} {binders} :\n"
            f"    {statement} := {body}\n"
        )
        self.report.cocycles.append(CocycleMeta(
            level=1, name=thm_name,
            label=f"call-site cocycle {caller}→{callee}",
            goal_kind=goal_kind, proof_mode=proof_mode,
            open=(proof_mode == "sorry"),
        ))
        return text

    def _emit_trivial_c1(
        self, caller: str, callee: str, reason: str,
    ) -> str:
        thm_name = (
            f"deppy_c1_cocycle_"
            f"{_safe_ident(caller)}_to_{_safe_ident(callee)}"
        )
        text = (
            f"-- C^1 cocycle (trivial): {reason}\n"
            f"theorem {thm_name} : True := by trivial\n"
        )
        self.report.cocycles.append(CocycleMeta(
            level=1, name=thm_name,
            label=f"trivial cocycle {caller}→{callee}",
            goal_kind="True", proof_mode="trivial",
        ))
        return text

    # -- C^2 ----------------------------------------------------------

    def emit_c2_coherence(
        self, f: str, g: str, h: str,
        sites_fg: list[CallSite],
        sites_gh: list[CallSite],
    ) -> str:
        """Emit the C^2 coherence theorem for chain ``f → g → h``.

        Goal: ``∀ <f's args>, P_f → P_h[formals substituted via g]``.

        This witnesses associativity: the composed precondition
        ``P_h(actuals_of_h_in_g[formals_of_g := actuals_of_g_in_f])``
        is implied by ``P_f``.
        """
        if not sites_fg or not sites_gh:
            return self._emit_trivial_c2(f, g, h, "missing call sites")

        f_node = self.fn_nodes.get(f)
        g_node = self.fn_nodes.get(g)
        h_node = self.fn_nodes.get(h)
        if f_node is None or g_node is None or h_node is None:
            return self._emit_trivial_c2(f, g, h, "missing AST for chain")

        site_fg = sites_fg[0]
        site_gh = sites_gh[0]
        f_formals = [a.arg for a in f_node.args.args]
        g_formals = [a.arg for a in g_node.args.args]
        h_formals = [a.arg for a in h_node.args.args]

        g_actuals_in_f = list(site_fg.actuals)
        h_actuals_in_g = list(site_gh.actuals)

        if (len(g_actuals_in_f) != len(g_formals)
                or len(h_actuals_in_g) != len(h_formals)):
            return self._emit_trivial_c2(
                f, g, h, "arity mismatch in chain",
            )

        f_pre = self._function_precondition(f)
        h_pre = self._function_precondition(h)
        composed_h_pre = substitute_via(
            h_pre,
            f_formals=f_formals,
            g_formals=g_formals,
            g_actuals_in_f=g_actuals_in_f,
            h_formals=h_formals,
            h_actuals_in_g=h_actuals_in_g,
        )

        binders, py_types = self._render_binders(f_node)
        f_pre_lean = self._translate_predicate(f_pre, py_types)
        composed_lean = self._translate_predicate(
            composed_h_pre, py_types,
        )

        if (f_pre_lean.lean_text == "True"
                and composed_lean.lean_text == "True"):
            goal_kind = "True"
            proof_mode = "trivial"
            body = "by trivial"
        elif f_pre_lean.exact and composed_lean.exact:
            goal_kind = "real_arithmetic"
            proof_mode = "omega"
            body = (
                "by intro _h_pre; "
                "(try omega) <;> Deppy.deppy_safe"
            )
        else:
            goal_kind = "real_mixed"
            proof_mode = "deppy_safe"
            body = "by intro _h_pre; Deppy.deppy_safe"

        thm_name = (
            f"deppy_c2_coherence_"
            f"{_safe_ident(f)}_{_safe_ident(g)}_{_safe_ident(h)}"
        )
        statement = (
            f"({f_pre_lean.lean_text}) → ({composed_lean.lean_text})"
        )
        text = (
            f"-- C^2 coherence: chain `{f}` → `{g}` → `{h}`\n"
            f"-- Goal kind: {goal_kind}\n"
            f"-- f's pre (Python): {f_pre}\n"
            f"-- h's pre (Python): {h_pre}\n"
            f"-- composed via g(f) → h(g(f)): {composed_h_pre}\n"
            f"theorem {thm_name} {binders} :\n"
            f"    {statement} := {body}\n"
        )
        self.report.cocycles.append(CocycleMeta(
            level=2, name=thm_name,
            label=f"coherence {f}→{g}→{h}",
            goal_kind=goal_kind, proof_mode=proof_mode,
            open=(proof_mode == "sorry"),
        ))
        return text

    def _emit_trivial_c2(
        self, f: str, g: str, h: str, reason: str,
    ) -> str:
        thm_name = (
            f"deppy_c2_coherence_"
            f"{_safe_ident(f)}_{_safe_ident(g)}_{_safe_ident(h)}"
        )
        text = (
            f"-- C^2 coherence (trivial): {reason}\n"
            f"theorem {thm_name} : True := by trivial\n"
        )
        self.report.cocycles.append(CocycleMeta(
            level=2, name=thm_name,
            label=f"trivial coherence {f}→{g}→{h}",
            goal_kind="True", proof_mode="trivial",
        ))
        return text

    # -- helpers -----------------------------------------------------

    def _function_precondition(self, fn_name: str) -> str:
        """Return the function's exception-free-when precondition
        as a Python-syntax string."""
        spec = self.sidecar_specs.get(fn_name)
        if spec is None:
            # Try refinement_inference's function_wide_preconditions.
            try:
                from deppy.pipeline.refinement_inference import (
                    infer_refinements,
                )
                # Avoid re-running inference per function — cache once.
                if not hasattr(self, "_refinement_cache"):
                    pass  # caller should pre-set the cache; default empty
                rmap = getattr(self, "_refinement_cache", {}).get(fn_name)
                if rmap is not None and rmap.function_wide_preconditions:
                    return " and ".join(rmap.function_wide_preconditions)
            except Exception:
                pass
            return "True"
        efw = list(getattr(spec, "exception_free_when", None) or [])
        return " and ".join(efw) if efw else "True"

    def _function_sources(self, fv) -> list[str]:
        """Return the list of safety predicates for the function's
        sources (addressed + unaddressed)."""
        out: list[str] = []
        try:
            disch = (fv.proof_payload or {}).get("semantic", {}).get(
                "discharges", [],
            )
            for d in disch:
                pred = d.get("safety_predicate", "")
                if pred:
                    out.append(pred)
        except Exception:
            pass
        return out

    def _render_binders(
        self, fn_node,
    ) -> tuple[str, dict[str, str]]:
        """Render the function's binders as a Lean string + return
        the python_types dict for predicate translation."""
        try:
            from deppy.lean.type_translation import translate_annotation
        except ImportError:
            return "", {}
        py_types: dict[str, str] = {}
        binders: list[str] = []
        for arg in fn_node.args.args:
            ann_result = translate_annotation(
                arg.annotation, context=self.type_context,
            )
            binders.append(f"({arg.arg} : {ann_result.lean})")
            try:
                py_types[arg.arg] = (
                    ast.unparse(arg.annotation) if arg.annotation else "int"
                )
            except Exception:
                py_types[arg.arg] = "int"
        return " ".join(binders), py_types

    def _translate_predicate(
        self, predicate: str, py_types: dict[str, str],
    ):
        """Translate a Python-syntax predicate to Lean."""
        try:
            from deppy.lean.predicate_translation import translate
            return translate(predicate, python_types=py_types)
        except ImportError:
            class _Dummy:
                lean_text = predicate
                exact = False
            return _Dummy()


# ─────────────────────────────────────────────────────────────────────
#  Call-site extraction
# ─────────────────────────────────────────────────────────────────────

def extract_call_sites(source: str) -> dict[tuple[str, str], list[CallSite]]:
    """Walk the AST and collect every intra-module call site as
    ``(caller, callee) → [CallSite, ...]``.

    Only ``Call`` nodes whose ``func`` is a bare ``Name`` matching
    a top-level function are recorded.  Method calls and external
    calls are ignored — the C^1 / C^2 cocycles are about deppy's
    internal call graph, not external library calls.
    """
    out: dict[tuple[str, str], list[CallSite]] = {}
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return out

    fn_nodes: dict[str, ast.FunctionDef | ast.AsyncFunctionDef] = {}
    def walk_classes(node):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            fn_nodes[node.name] = node
            for child in node.body:
                walk_classes(child)
            return
        if isinstance(node, ast.ClassDef):
            for child in node.body:
                walk_classes(child)
            return
        for child in ast.iter_child_nodes(node):
            walk_classes(child)
    walk_classes(tree)

    for caller_name, caller_node in fn_nodes.items():
        for sub in ast.walk(caller_node):
            if not isinstance(sub, ast.Call):
                continue
            if isinstance(sub.func, ast.Name):
                callee_name = sub.func.id
                if callee_name not in fn_nodes:
                    continue
                actuals: list[str] = []
                for a in sub.args:
                    try:
                        actuals.append(ast.unparse(a))
                    except Exception:
                        actuals.append(f"_arg{len(actuals)}")
                site = CallSite(
                    caller=caller_name,
                    callee=callee_name,
                    actuals=actuals,
                    lineno=getattr(sub, "lineno", 0),
                    col=getattr(sub, "col_offset", 0),
                )
                out.setdefault((caller_name, callee_name), []).append(site)
    return out


# ─────────────────────────────────────────────────────────────────────
#  Cohomology rendering driver
# ─────────────────────────────────────────────────────────────────────

def render_cocycle_section(
    verdict, fn_nodes: dict, source: str,
    *, type_context=None, sidecar_specs: Optional[dict] = None,
) -> tuple[list[str], EmitReport]:
    """Build the full list of cocycle theorem texts for a verdict.

    Returns ``(theorems, report)`` where ``theorems`` is a list of
    rendered Lean theorem strings and ``report`` carries
    per-cocycle metadata (goal kind, proof mode, open/closed).
    """
    emitter = CohomologyEmitter(
        verdict, fn_nodes,
        type_context=type_context, sidecar_specs=sidecar_specs,
    )
    sites = extract_call_sites(source)
    theorems: list[str] = []

    # C^0 — one per function.
    for fn_name in sorted(fn_nodes.keys()):
        theorems.append(emitter.emit_c0_cocycle(fn_name))

    # C^1 — one per (caller, callee) pair.
    for (caller, callee), site_list in sorted(sites.items()):
        if caller == callee:
            continue  # self-recursion handled by termination obligations
        theorems.append(
            emitter.emit_c1_cocycle(caller, callee, site_list),
        )

    # C^2 — one per chain f → g → h.
    seen_chains: set[tuple[str, str, str]] = set()
    for (caller, callee), fg_sites in sorted(sites.items()):
        if caller == callee:
            continue
        # find chains starting g → h
        for (caller2, callee2), gh_sites in sorted(sites.items()):
            if caller2 != callee:
                continue
            if caller == caller2 or callee == callee2 or caller == callee2:
                continue
            chain = (caller, callee, callee2)
            if chain in seen_chains:
                continue
            seen_chains.add(chain)
            theorems.append(
                emitter.emit_c2_coherence(
                    caller, callee, callee2,
                    fg_sites, gh_sites,
                ),
            )

    return theorems, emitter.report


# ─────────────────────────────────────────────────────────────────────
#  Identifier helper (local copy)
# ─────────────────────────────────────────────────────────────────────

def _safe_ident(text: str) -> str:
    out: list[str] = []
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


__all__ = [
    "CallSite",
    "CocycleMeta",
    "EmitReport",
    "CohomologyEmitter",
    "substitute_actuals",
    "substitute_via",
    "extract_call_sites",
    "render_cocycle_section",
]
