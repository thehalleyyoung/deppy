"""Inter-procedural function summaries for the safety pipeline.

This module builds a real call graph for a Python module, computes a
:class:`FunctionSummary` for every function in reverse topological
order (handling recursion via SCC fixpoint), and exposes a
:func:`discharge_call_site` helper the safety pipeline uses to retire
``CALL_PROPAGATION`` sources at internal call sites.

Why this exists
---------------

The previous ``_try_callee_discharge`` registered an *axiom* claiming
the callee is safe whenever its name appears at a call site — that
assumption is unsound: the callee may itself have undischarged
sources, or it may require preconditions the caller does not
establish.  This module replaces the unconditional axiom with a real
Z3 entailment check:

    caller_path_guards(call_site)  ⊢  callee.preconditions(actuals)

When the entailment holds, the call is genuinely safe under the
caller's path; when not, the source remains undischarged and the
pipeline reports it.

Public API
----------
* :func:`build_call_graph`        — caller→callee edges
* :func:`compute_summaries`       — function summaries via SCC fixpoint
* :func:`discharge_call_site`     — Z3 entailment check at a single site
* :class:`FunctionSummary`        — per-function data: preconditions,
  postconditions, declared raises, mutations
* :class:`CallGraph`              — adjacency lists with SCC analysis
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Optional


# ─────────────────────────────────────────────────────────────────────
#  CallGraph
# ─────────────────────────────────────────────────────────────────────

@dataclass
class CallGraph:
    """Caller → callee adjacency lists.

    Only *intra-module* edges are tracked — calls to imported names
    (``math.sqrt``) are out of scope here; they are handled by the
    builtin sidecars in :mod:`deppy.pipeline.builtin_sidecar`.
    """
    nodes: set[str] = field(default_factory=set)
    edges: dict[str, set[str]] = field(default_factory=dict)
    # Per call-site information: ``{(caller, callee): [Call AST nodes]}``.
    call_sites: dict[tuple[str, str], list[ast.Call]] = field(default_factory=dict)

    def add_node(self, name: str) -> None:
        self.nodes.add(name)
        self.edges.setdefault(name, set())

    def add_edge(self, caller: str, callee: str, *,
                 site: Optional[ast.Call] = None) -> None:
        self.add_node(caller)
        self.add_node(callee)
        self.edges[caller].add(callee)
        if site is not None:
            self.call_sites.setdefault((caller, callee), []).append(site)

    # -- SCC analysis -------------------------------------------------

    def sccs(self) -> list[list[str]]:
        """Return strongly-connected components using Tarjan's algorithm.

        The returned list is in *reverse* topological order — leaves
        first, roots last.  This is the natural order for bottom-up
        summary propagation: when we visit ``f``'s SCC every callee
        ``g`` (outside the SCC) has already been summarised.
        """
        index = {0: 0}
        stack: list[str] = []
        on_stack: dict[str, bool] = {}
        indices: dict[str, int] = {}
        lowlinks: dict[str, int] = {}
        result: list[list[str]] = []

        def strongconnect(v: str) -> None:
            indices[v] = index[0]
            lowlinks[v] = index[0]
            index[0] += 1
            stack.append(v)
            on_stack[v] = True
            for w in self.edges.get(v, ()):
                if w not in self.nodes:
                    continue
                if w not in indices:
                    strongconnect(w)
                    lowlinks[v] = min(lowlinks[v], lowlinks[w])
                elif on_stack.get(w, False):
                    lowlinks[v] = min(lowlinks[v], indices[w])
            if lowlinks[v] == indices[v]:
                comp: list[str] = []
                while True:
                    w = stack.pop()
                    on_stack[w] = False
                    comp.append(w)
                    if w == v:
                        break
                result.append(comp)

        for v in sorted(self.nodes):
            if v not in indices:
                strongconnect(v)
        return result  # already reverse topological from Tarjan


def build_call_graph(source: str) -> CallGraph:
    """Parse ``source`` and return its intra-module call graph."""
    cg = CallGraph()
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return cg

    func_names: set[str] = {
        n.name for n in ast.walk(tree)
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
    }

    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        cg.add_node(node.name)
        for sub in ast.walk(node):
            if isinstance(sub, ast.Call):
                callee = _callee_name(sub.func)
                if callee and callee in func_names and callee != node.name:
                    cg.add_edge(node.name, callee, site=sub)
                elif callee == node.name:
                    # self-recursion — still record as edge so SCC
                    # detection picks it up.
                    cg.add_edge(node.name, callee, site=sub)
    return cg


def _callee_name(expr: ast.expr) -> Optional[str]:
    """Best-effort extraction of the called function name."""
    if isinstance(expr, ast.Name):
        return expr.id
    if isinstance(expr, ast.Attribute):
        return expr.attr
    return None


# ─────────────────────────────────────────────────────────────────────
#  FunctionSummary
# ─────────────────────────────────────────────────────────────────────

@dataclass
class FunctionSummary:
    """Per-function summary used by the safety pipeline.

    Attributes
    ----------
    name :
        The function's local name.
    parameters :
        Ordered list of formal parameter names (used for substitution
        at call sites).
    preconditions :
        Predicates the *caller* is required to establish before the
        call.  Sourced from:

        * the function's leading raise-guards (refinement_inference's
          ``function_wide_preconditions``);
        * any user-supplied ``ExternalSpec.preconditions`` /
          ``exception_free_when``.
    postconditions :
        Predicates the function guarantees on return.
    raises :
        Exception classes the function can propagate (a unioning of
        the function's *own* raises plus every callee's ``raises``).
    is_safe :
        ``True`` when every internal source has been discharged.  Used
        to short-circuit ``CALL_PROPAGATION`` discharge: if
        ``is_safe``, a call to this function adds nothing the caller
        must worry about.
    """
    name: str
    parameters: list[str] = field(default_factory=list)
    preconditions: list[str] = field(default_factory=list)
    postconditions: list[str] = field(default_factory=list)
    raises: set[str] = field(default_factory=set)
    is_safe: bool = False
    decreases: list[str] = field(default_factory=list)


# ─────────────────────────────────────────────────────────────────────
#  Summary computation
# ─────────────────────────────────────────────────────────────────────

def compute_summaries(
    source: str,
    *,
    drafts: Optional[dict] = None,
    refinement_maps: Optional[dict] = None,
    user_specs: Optional[dict] = None,
) -> dict[str, FunctionSummary]:
    """Compute a :class:`FunctionSummary` for every function in
    ``source``.

    Bottom-up walk through the SCCs of the call graph.  Inside an SCC
    (recursive group) we run a small fixpoint until ``raises`` and
    ``preconditions`` stop growing.

    The result is consumed by :func:`discharge_call_site`.
    """
    cg = build_call_graph(source)
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return {}

    fn_nodes: dict[str, ast.FunctionDef | ast.AsyncFunctionDef] = {}
    for n in ast.walk(tree):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            fn_nodes[n.name] = n

    drafts = drafts or {}
    user_specs = user_specs or {}
    refinement_maps = refinement_maps or {}

    summaries: dict[str, FunctionSummary] = {}

    def base_summary(name: str) -> FunctionSummary:
        node = fn_nodes.get(name)
        params = [a.arg for a in node.args.args] if node is not None else []
        # Merge spec sources by precedence: user > draft > inferred.
        pre: list[str] = []
        post: list[str] = []
        raises: set[str] = set()
        decreases: list[str] = []
        # Refinement-inference function-wide preconditions.
        rmap = refinement_maps.get(name)
        if rmap is not None:
            for p in rmap.function_wide_preconditions:
                if p not in pre:
                    pre.append(p)
        # Auto-spec drafts (inferred ExternalSpec).
        d = drafts.get(name)
        if d is not None:
            for p in (getattr(d, "preconditions", None) or []):
                if p not in pre:
                    pre.append(p)
            for p in (getattr(d, "postconditions", None) or []):
                if p not in post:
                    post.append(p)
            for cls, _cond in (getattr(d, "raises_declarations", None) or []):
                raises.add(cls)
            for m in (getattr(d, "decreases", None) or []):
                if m not in decreases:
                    decreases.append(m)
        # User-supplied sidecar wins outright.
        u = user_specs.get(name)
        if u is not None:
            for p in (getattr(u, "preconditions", None) or []):
                if p not in pre:
                    pre.append(p)
            for p in (getattr(u, "exception_free_when", None) or []):
                if p not in pre:
                    pre.append(p)
            for p in (getattr(u, "postconditions", None) or []):
                if p not in post:
                    post.append(p)
            for cls, _cond in (getattr(u, "raises_declarations", None) or []):
                raises.add(cls)
            for m in (getattr(u, "decreases", None) or []):
                if m not in decreases:
                    decreases.append(m)
        return FunctionSummary(
            name=name, parameters=params,
            preconditions=pre, postconditions=post,
            raises=raises, decreases=decreases,
            is_safe=False,
        )

    # Process SCCs in reverse topological order (Tarjan returns them
    # this way — leaves first).
    for comp in cg.sccs():
        # Initialise all summaries in the SCC.
        for name in comp:
            if name in fn_nodes and name not in summaries:
                summaries[name] = base_summary(name)
        # Fixpoint within the SCC.
        changed = True
        while changed:
            changed = False
            for name in comp:
                if name not in summaries:
                    continue
                summary = summaries[name]
                node = fn_nodes.get(name)
                if node is None:
                    continue
                # Union raises from each *known* callee.
                for callee in cg.edges.get(name, ()):
                    callee_summary = summaries.get(callee)
                    if callee_summary is None:
                        continue
                    for cls in callee_summary.raises:
                        if cls not in summary.raises:
                            summary.raises.add(cls)
                            changed = True
                # Self-recursion: if no decreases set and self-edge
                # present, mark as potentially non-terminating.
                if name in cg.edges.get(name, ()):
                    if not summary.decreases and "RecursionError" not in summary.raises:
                        summary.raises.add("RecursionError")
                        changed = True
        # After the fixpoint, mark functions safe only when:
        #  (a) their own ``raises`` set is empty (no callee can throw
        #      an undischarged exception up to them), AND
        #  (b) every exception source in the function body is covered
        #      by a path-sensitive guard.
        #
        # Without check (b), an unguarded ``a / b`` in a leaf function
        # would yield ``raises = set()`` (because the function makes
        # no internal calls and has no raises_declarations), which
        # would falsely claim ``is_safe = True``.  The caller would
        # then inherit that false safety via the ``callee.is_safe``
        # shortcut in :func:`discharge_call_site`.
        for name in comp:
            if name not in summaries:
                continue
            summary = summaries[name]
            if summary.raises:
                summary.is_safe = False
                continue
            rmap = refinement_maps.get(name)
            unguarded = False
            if rmap is not None:
                for fact in rmap.per_source:
                    if not fact.guards:
                        # No path-sensitive guard at this source.
                        # Unless the function-wide preconditions cover
                        # it (or a sidecar `is_total`), treat the
                        # function as not-safe.
                        unguarded = True
                        break
            summary.is_safe = (not unguarded
                               and not summary.preconditions
                               and not summary.raises)

    # Add summaries for any function not visited by the SCC walk
    # (defensive — should not happen for well-formed input).
    for name, node in fn_nodes.items():
        if name not in summaries:
            summaries[name] = base_summary(name)

    return summaries


# ─────────────────────────────────────────────────────────────────────
#  Per-call-site discharge
# ─────────────────────────────────────────────────────────────────────

def discharge_call_site(
    *,
    callee_summary: FunctionSummary,
    actuals: list[str],
    caller_path_guards: tuple[str, ...],
    z3_check,
) -> tuple[bool, str]:
    """Z3-entailment check for a single call site.

    Parameters
    ----------
    callee_summary :
        The pre-computed summary for the callee.
    actuals :
        The Python source-form of each actual argument at the call
        site, in formal-parameter order.
    caller_path_guards :
        The path-sensitive guards live at the call site (typically
        produced by ``RefinementInferrer``).
    z3_check :
        ``ProofKernel._z3_check`` — a function that takes a formula
        string and returns ``(verdict, reason)``.

    Returns
    -------
    ``(ok, message)`` — ``ok`` is ``True`` when *every* callee
    precondition is implied by the conjunction of caller guards under
    the actuals→formals substitution.

    When the callee's summary marks it ``is_safe`` *and* its
    preconditions are empty, the call is trivially safe and we return
    ``True`` without invoking Z3.
    """
    if callee_summary.is_safe and not callee_summary.preconditions:
        return True, f"callee {callee_summary.name} is_safe; no preconditions"

    if not callee_summary.preconditions:
        # Callee has no preconditions but is not is_safe — caller is
        # stuck with whatever the callee can raise; we cannot
        # discharge this without proof.
        return False, (
            f"callee {callee_summary.name} not is_safe; "
            f"no preconditions to discharge"
        )

    # Substitute actuals for formals in each precondition.
    if len(actuals) > len(callee_summary.parameters):
        # Variadic / keyword args: bail out — discharge is not safe.
        return False, "actuals/formals arity mismatch"
    subst = dict(zip(callee_summary.parameters, actuals))

    failed: list[str] = []
    for pre in callee_summary.preconditions:
        substituted = _substitute_identifiers(pre, subst)
        if substituted is None:
            failed.append(f"could not substitute in {pre!r}")
            continue
        guards = " and ".join(
            f"({g})" for g in caller_path_guards if g.strip()
        ) or "True"
        formula = f"({guards}) => ({substituted})"
        verdict, reason = z3_check(formula)
        if not verdict:
            failed.append(
                f"{substituted!r} not entailed by guards "
                f"({reason or 'disagrees'})"
            )

    if failed:
        return False, "; ".join(failed)
    return True, f"all {len(callee_summary.preconditions)} preconditions discharged"


# ─────────────────────────────────────────────────────────────────────
#  Internal: AST substitution
# ─────────────────────────────────────────────────────────────────────

def _substitute_identifiers(expr: str, subst: dict[str, str]) -> Optional[str]:
    """Replace formal parameter names with actual-argument source.

    Parses ``expr`` and rewrites every ``Name`` whose ``id`` matches
    a key in ``subst`` with a fresh expression parsed from the
    corresponding value.  Returns the unparsed result, or ``None`` if
    parsing fails.

    We *do not* visit the children of a substituted node — otherwise
    a substitution like ``n → "n - 1"`` would re-trigger on the inner
    ``n`` and loop forever (each pass replaces ``n`` with ``n - 1``).
    """
    try:
        tree = ast.parse(expr, mode="eval")
    except SyntaxError:
        return None

    class _Sub(ast.NodeTransformer):
        def visit_Name(self, node: ast.Name) -> ast.AST:  # type: ignore[override]
            if node.id in subst:
                try:
                    parsed = ast.parse(f"({subst[node.id]})", mode="eval").body
                    # Mark the substituted subtree as "do not recurse"
                    # so a subsequent ``self.visit`` from the parent's
                    # generic walk does not re-substitute the new
                    # name (which would loop ``n → n-1 → n-1-1-1…``).
                    return ast.copy_location(parsed, node)
                except SyntaxError:
                    return node
            return node

        def generic_visit(self, node):  # type: ignore[override]
            # Skip generic_visit of any node we just produced from a
            # substitution — the AST is "fresh" already.  We detect
            # this by attaching a sentinel attribute.
            if getattr(node, "_deppy_substituted", False):
                return node
            return super().generic_visit(node)

    transformer = _Sub()
    new = ast.fix_missing_locations(transformer.visit(tree))
    try:
        return ast.unparse(new)
    except Exception:
        return None


__all__ = [
    "CallGraph",
    "FunctionSummary",
    "build_call_graph",
    "compute_summaries",
    "discharge_call_site",
]
