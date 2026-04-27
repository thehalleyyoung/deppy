"""Build the cubical-simplicial bicomplex over linked sidecar
methods, exercising deppy's full inter-procedural infrastructure.

The bicomplex C^{p,q} combines:

  * **p-axis (cubical / intra-procedural)** — per-function cubical
    sets emitted by ``deppy.pipeline.cubical_ast.build_cubical_set``
    (already used in :mod:`sidecar_cubical_link`).

  * **q-axis (simplicial / inter-procedural)** — the call graph
    of the linked methods, computed by
    ``deppy.lean.cohomology_compute.build_chain_complex``.

The total cohomology is computed by
:meth:`Bicomplex.compute_total_cohomology` — this is the deepest
inter-procedural verification structure deppy has.

For our sidecar use we feed an empty :class:`SafetyVerdict` shell
(the methods come from sympy, not from a verified deppy module);
the bicomplex still composes and exposes:

  * Per-function cubical part (cells by dim).
  * Module simplicial part (call-graph chain).
  * Bicomplex 1-cells (cubical/simplicial mixed) and 2-cells.
  * Total cohomology dimensions and Euler characteristic.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field


@dataclass
class BicomplexLinkReport:
    bicomplex_built: bool = False
    cubical_parts: int = 0
    simplicial_present: bool = False
    bicomplex_edges: int = 0
    bicomplex_faces: int = 0
    total_cohomology: dict[int, int] = field(default_factory=dict)
    euler_total: int = 0
    notes: list[str] = field(default_factory=list)


def link_bicomplex(body_link_report) -> BicomplexLinkReport:
    """Build the cubical-simplicial bicomplex over linked methods."""
    out = BicomplexLinkReport()
    if body_link_report is None or not body_link_report.results:
        return out

    fn_nodes: dict = {}
    for r in body_link_report.results:
        if r.error or not r.source:
            continue
        try:
            mod = ast.parse(r.source)
        except SyntaxError:
            continue
        for node in mod.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                node.name = r.qualified
                fn_nodes[r.qualified] = node
                break

    if not fn_nodes:
        return out

    try:
        from deppy.pipeline.safety_pipeline import SafetyVerdict
        from deppy.lean.cubical_simplicial_bicomplex import (
            build_bicomplex,
        )
        verdict = SafetyVerdict(
            module_path="<sidecar-linked-methods>",
            functions={},
        )
        bicomplex = build_bicomplex(verdict, fn_nodes)
    except Exception as e:
        out.notes.append(f"build_bicomplex failed: {e}")
        return out

    out.bicomplex_built = True
    out.cubical_parts = len(bicomplex.cubical_parts)
    out.simplicial_present = bicomplex.simplicial is not None
    out.bicomplex_edges = len(bicomplex.bicomplex_edges())
    out.bicomplex_faces = len(bicomplex.bicomplex_faces())

    try:
        cohom = bicomplex.compute_total_cohomology()
        # ``cohom`` carries dimension counts; extract them defensively.
        if hasattr(cohom, "h_total"):
            ht = getattr(cohom, "h_total")
            if isinstance(ht, dict):
                out.total_cohomology = dict(ht)
        if hasattr(cohom, "euler_characteristic"):
            out.euler_total = int(cohom.euler_characteristic)
    except Exception as e:
        out.notes.append(f"compute_total_cohomology failed: {e}")

    return out


__all__ = ["BicomplexLinkReport", "link_bicomplex"]
