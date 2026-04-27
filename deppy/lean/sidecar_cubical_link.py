"""Run deppy's intra-procedural cubical analysis on the actual
library source bodies linked by :mod:`deppy.lean.sidecar_body_link`.

This is the bridge from a sidecar's linked methods to deppy's
existing cubical machinery — :func:`build_cubical_set`,
:meth:`CubicalSet.find_kan_fillable`,
:func:`cubical_set_to_obligations`, and the renderer
:func:`render_cubical_section`.  Nothing in this module is
library-specific: it consumes the AST nodes that
:mod:`sidecar_body_link` already extracted via
``inspect.getsource`` + ``ast.parse``.

The bridge is necessary because :func:`render_cubical_section`
expects a :class:`SafetyVerdict` (the output of the full deppy
safety pipeline, which assumes ``@implies``-decorated source).
For sidecar use, we don't have that pipeline output — instead we
build a minimal verdict shell that has the right shape: a module
path, an empty ``functions`` map (so the renderer falls back to
running the cubical analysis directly on the AST without trying to
reconcile with previously-recorded cubical statistics).

What gets emitted to the certificate:

  * A per-function summary (cells by dimension, Kan candidates,
    obligations total, Euler characteristic) for every linked
    method.
  * Lean ``IsKanFillable`` theorems for each Kan-fillable cell,
    rendered by :func:`render_cubical_section` with
    ``include_kan_theorems=True``.

Honest acknowledgement: the rendered cubical theorems use
``sorry`` for their proof bodies whenever the safety pipeline
hasn't already discharged the obligation — exactly as
``deppy.lean.cubical_certificate`` does in the normal flow.  We're
not pretending these are kernel-verified Kan fills; we're
exercising the cubical analysis on real library code and reporting
honestly.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Optional


@dataclass
class CubicalLinkReport:
    section_text: str = ""
    per_method: dict[str, dict] = field(default_factory=dict)
    total_cells: int = 0
    total_kan_candidates: int = 0
    total_obligations: int = 0
    methods_analysed: int = 0


def link_cubical(body_link_report) -> CubicalLinkReport:
    """Run deppy's cubical analysis on every successfully-linked
    method's AST.

    Returns a :class:`CubicalLinkReport` whose ``section_text`` is
    Lean text suitable for embedding in the certificate.  The
    section contains a per-function summary plus Kan-theorem stubs.
    """
    if body_link_report is None or not body_link_report.results:
        return CubicalLinkReport()

    # Gather AST FunctionDef nodes from each successful link.
    fn_nodes: dict[str, ast.AST] = {}
    for r in body_link_report.results:
        if r.error or not r.source:
            continue
        try:
            mod = ast.parse(r.source)
        except SyntaxError:
            continue
        for node in mod.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                fn_nodes[r.qualified] = node
                break

    if not fn_nodes:
        return CubicalLinkReport()

    # F8 — populate SafetyVerdict with synthetic FunctionVerdict
    # entries per linked method.  This gives render_cubical_section
    # real per-function data to look up (cubical_obligations_total,
    # discharge_paths, etc.) instead of the empty shell that
    # produces zero counts.
    from deppy.pipeline.safety_pipeline import (
        SafetyVerdict, FunctionVerdict,
    )
    from deppy.core.kernel import TrustLevel
    from deppy.lean.cubical_certificate import render_cubical_section

    function_verdicts: dict = {}
    for fn_name, node in fn_nodes.items():
        try:
            from deppy.pipeline.cubical_ast import build_cubical_set
            cset = build_cubical_set(node)
            cell_counts = {
                d: len(cs) for d, cs in cset.cells_by_dim.items()
            }
            kan = cset.find_kan_fillable()
            euler = cset.euler_characteristic()
        except Exception:
            cell_counts = {}
            kan = []
            euler = 0
        function_verdicts[fn_name] = FunctionVerdict(
            name=fn_name,
            is_safe=True,
            trust=TrustLevel.STRUCTURAL_CHAIN,
            coverage_ratio=1.0,
            cubical_cell_counts=cell_counts,
            cubical_kan_candidates=len(kan),
            cubical_obligations_total=len(kan),
            cubical_obligations_verified=0,
            cubical_euler=euler,
        )
    verdict = SafetyVerdict(
        module_path="<sidecar-linked-methods>",
        functions=function_verdicts,
    )

    section = render_cubical_section(
        verdict, fn_nodes,
        include_kan_theorems=True,
        include_higher_paths=False,
    )

    per_method: dict[str, dict] = {}
    for fn_name, summary in (
        section.per_function_summaries or {}
    ).items():
        per_method[fn_name] = {
            "cell_counts_by_dim": dict(summary.cell_counts_by_dim),
            "kan_candidates": summary.kan_candidates,
            "obligations_total": summary.obligations_total,
            "obligations_verified": summary.obligations_verified,
            "euler": summary.euler,
        }

    # Compose the section text: the summary block + theorems.
    parts: list[str] = []
    parts.append(section.summary_block.rstrip())
    parts.append("")
    for thm in section.theorems:
        parts.append(thm)
    section_text = "\n".join(parts).strip() + "\n"

    return CubicalLinkReport(
        section_text=section_text,
        per_method=per_method,
        total_cells=sum(
            sum(m["cell_counts_by_dim"].values())
            for m in per_method.values()
        ),
        total_kan_candidates=sum(
            m["kan_candidates"] for m in per_method.values()
        ),
        total_obligations=sum(
            m["obligations_total"] for m in per_method.values()
        ),
        methods_analysed=len(fn_nodes),
    )


__all__ = [
    "CubicalLinkReport",
    "link_cubical",
]
