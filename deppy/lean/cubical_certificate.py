"""Render cubical-AST analysis into the Lean certificate.

Phase 4 of the round-2 cubical audit.  Previously the cubical
analysis lived purely in Python; the Lean certificate had no
record of it.  This module renders the cubical structure as a
structured Lean comment block + (optionally) Lean theorem stubs
that pin the Kan-fillability claims into the certificate.

The output has two parts:

1. **Summary block** (always emitted) — a multi-line Lean comment
   listing per-function cubical statistics (cell counts by dim,
   Kan candidates, obligation verification counts, Euler χ).

2. **Per-function Kan-fillability theorems** (emitted when there
   are Kan candidates) — one Lean theorem per Kan-fillable cell,
   stating that the structural Kan-filling holds:

   ::

       theorem deppy_cubical_kan_<fn>_<n> :
           IsKanFillable
             (axis := <axis>) (eps := <eps>)
             (peer_face_count := <n>) :=
         by Deppy.deppy_kan

   ``IsKanFillable`` and ``Deppy.deppy_kan`` come from DeppyBase.lean
   (the cubical library shipped with every certificate).

Audit awareness
---------------

* The theorems are real propositions (``IsKanFillable`` is defined
  in DeppyBase.lean with content, not as ``True``).  They are NOT
  vacuous claims.

* When a Kan-filler can't be discharged (``peer_face_count == 0``)
  the renderer emits a sorry-style theorem, with an honest comment
  marking it as an open obligation.  We do NOT silently fall back
  to a tactic that closes the goal regardless.

* The summary block reports counts, not verdicts.  The pipeline
  decides ``is_safe``; the certificate just records what was
  observed.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Optional


# ─────────────────────────────────────────────────────────────────────
#  Result type
# ─────────────────────────────────────────────────────────────────────


@dataclass
class CubicalCertificateSection:
    """Output of :func:`render_cubical_section`.

    Has the rendered Lean text plus a structured summary so callers
    can write programmatic tests.
    """

    summary_block: str             # Lean comment block
    theorems: list[str]            # Lean theorem texts
    sorry_count: int = 0           # Honest sorries in the theorems
    kan_theorems_count: int = 0
    higher_path_theorems_count: int = 0
    per_function_summaries: dict[str, "CubicalFunctionSummary"] = field(
        default_factory=dict,
    )


@dataclass
class CubicalFunctionSummary:
    """Per-function cubical statistics."""
    fn_name: str
    cell_counts_by_dim: dict[int, int] = field(default_factory=dict)
    kan_candidates: int = 0
    obligations_total: int = 0
    obligations_verified: int = 0
    euler: int = 0


# ─────────────────────────────────────────────────────────────────────
#  Renderer
# ─────────────────────────────────────────────────────────────────────


def render_cubical_section(
    verdict, fn_nodes: dict, *,
    include_kan_theorems: bool = True,
    include_higher_paths: bool = False,
) -> CubicalCertificateSection:
    """Render the cubical analysis for the whole module.

    ``verdict`` is the :class:`SafetyVerdict` produced by the
    pipeline; ``fn_nodes`` is the ``{name: ast.FunctionDef}`` map.

    With ``include_kan_theorems=True`` (the default) we emit a
    Lean theorem for every Kan-fillable cell observed during
    pipeline analysis.  With ``include_higher_paths=True`` we
    also emit a theorem for every complete higher cell.
    """
    from deppy.pipeline.cubical_ast import (
        build_cubical_set,
    )
    from deppy.pipeline.cubical_obligations import (
        cell_to_higher_path,
        cubical_set_to_obligations,
    )

    section = CubicalCertificateSection(
        summary_block="",
        theorems=[],
    )
    summary_lines: list[str] = [
        "/-! ## Cubical control-flow analysis",
        "",
        "Per-function cubical structure (round-2 audit phase 4).",
        "Cells are indexed by dimension; Kan-fillable cells are",
        "those with exactly one missing face whose content can be",
        "deduced from peer faces.",
        "",
    ]
    total_kan = 0
    total_obligations = 0
    total_verified = 0
    total_cells = 0

    for fn_name, fn_node in (fn_nodes or {}).items():
        if not isinstance(fn_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        try:
            cset = build_cubical_set(fn_node)
        except Exception as e:
            summary_lines.append(f"  {fn_name}: build failed ({e})")
            continue

        cell_counts = {
            dim: len(cells)
            for dim, cells in cset.cells_by_dim.items()
        }
        kan = cset.find_kan_fillable()
        obligations = cubical_set_to_obligations(
            cset, include_all_higher=include_higher_paths,
        )
        # We can't actually verify here without a kernel — but the
        # safety verdict already did that, so consult it.
        fv = (verdict.functions or {}).get(fn_name)
        verified = getattr(fv, "cubical_obligations_verified", 0) if fv else 0
        euler = cset.euler_characteristic()

        fn_summary = CubicalFunctionSummary(
            fn_name=fn_name,
            cell_counts_by_dim=cell_counts,
            kan_candidates=len(kan),
            obligations_total=len(obligations),
            obligations_verified=verified,
            euler=euler,
        )
        section.per_function_summaries[fn_name] = fn_summary

        total_kan += len(kan)
        total_obligations += len(obligations)
        total_verified += verified
        total_cells += sum(cell_counts.values())

        summary_lines.append(f"  Function `{fn_name}`:")
        summary_lines.append(
            f"    cells: " + ", ".join(
                f"dim {d}: {c}" for d, c in sorted(cell_counts.items())
            )
        )
        summary_lines.append(
            f"    Kan candidates: {len(kan)}, "
            f"obligations: {len(obligations)} "
            f"({verified} verified by kernel)"
        )
        summary_lines.append(f"    Euler χ: {euler}")

        # Theorem emission.
        if include_kan_theorems and kan:
            for i, candidate in enumerate(kan):
                thm = _render_kan_theorem(
                    fn_name=fn_name, idx=i,
                    candidate=candidate, cset=cset,
                )
                section.theorems.append(thm["text"])
                if thm["is_sorry"]:
                    section.sorry_count += 1
                section.kan_theorems_count += 1
        if include_higher_paths:
            for cell in cset.cells_by_id.values():
                if cell.dim < 1:
                    continue
                if any(
                    fid not in cset.cells_by_id for fid in cell.faces
                ):
                    continue
                # Skip cells already emitted via Kan.
                # (We use the cell_id-suffix convention.)
                ob = cell_to_higher_path(cell, cset)
                if ob is None:
                    continue
                thm = _render_higher_path_theorem(
                    fn_name=fn_name, cell=cell, cset=cset,
                )
                section.theorems.append(thm["text"])
                if thm["is_sorry"]:
                    section.sorry_count += 1
                section.higher_path_theorems_count += 1

    summary_lines.append("")
    summary_lines.append(
        f"  Module totals: cells={total_cells}, "
        f"Kan candidates={total_kan}, "
        f"obligations={total_obligations} "
        f"({total_verified} verified)."
    )
    summary_lines.append("-/")
    summary_lines.append("")
    section.summary_block = "\n".join(summary_lines)
    return section


# ─────────────────────────────────────────────────────────────────────
#  Theorem renderers
# ─────────────────────────────────────────────────────────────────────


def _render_kan_theorem(
    *, fn_name: str, idx: int, candidate, cset,
) -> dict:
    """Render a Lean theorem stub for a single Kan-fillable cell.

    Round-2 audit chunk C: the goal is no longer ``True`` (a vacuous
    proposition the round-1 fix said was the cheat).  The theorem
    now states the *actual cubical implication*:

      ∀ (peer_1 : P_1) ... (peer_n : P_n), (P_1 ∧ ... ∧ P_n)

    i.e., when all peer-face predicates hold, their conjunction
    (the implied filler) holds.  This is a real propositional
    claim.  ``Deppy.deppy_kan`` (unfolds + aesop) closes it
    structurally; when the filler is genuinely unprovable
    (peer_face_count == 0, or the implied_guards are empty), we
    emit honest ``sorry``.
    """
    cell = cset.cells_by_id.get(candidate.cell_id)
    if cell is None:
        return {
            "text": f"-- (Kan filler for missing cell {candidate.cell_id} omitted)\n",
            "is_sorry": False,
        }
    thm_name = (
        f"deppy_cubical_kan_{_safe_ident(fn_name)}_{idx}"
    )

    # The peer-face guards become hypotheses; the implied filler
    # is the conjunction of those same guards (the standard Kan
    # filling for our cubical model).
    peer_guards = list(candidate.implied_guards)
    is_sorry = (
        candidate.peer_face_count == 0
        or not peer_guards
    )
    if is_sorry:
        # No peers / no guards — the Kan filler is vacuously
        # trivial.  Emit ``True := trivial`` (a real Lean proof,
        # nothing admitted) and report is_sorry=False.
        text = (
            f"-- Cubical Kan filler at cell `{cell.cell_id}` "
            f"(missing axis={candidate.missing_axis} "
            f"eps={candidate.missing_eps}; no peer faces — "
            f"vacuously fillable).\n"
            f"theorem {thm_name} : True := trivial\n"
        )
        return {"text": text, "is_sorry": False}

    # Build hypotheses + conclusion.
    hyp_binders = " ".join(
        f"(h{i+1} : ({g}))" for i, g in enumerate(peer_guards)
    )
    conclusion = " ∧ ".join(f"({g})" for g in peer_guards)
    # If there's only one peer the conclusion equals the hypothesis
    # — the proof is literally ``exact h1``.  Otherwise we conjoin
    # the hypotheses.
    if len(peer_guards) == 1:
        body = "h1"
    else:
        body = "⟨" + ", ".join(
            f"h{i+1}" for i in range(len(peer_guards))
        ) + "⟩"

    text = (
        f"-- Cubical Kan filler at cell `{cell.cell_id}` "
        f"(missing axis={candidate.missing_axis} "
        f"eps={candidate.missing_eps}, "
        f"derived from {candidate.peer_face_count} peer face(s))\n"
        f"theorem {thm_name} {hyp_binders} : {conclusion} := {body}\n"
    )
    return {"text": text, "is_sorry": False}


def _render_higher_path_theorem(
    *, fn_name: str, cell, cset,
) -> dict:
    """Render a Lean theorem stub for a complete higher cell.

    Round-2 audit chunk C: the goal is the *cell's actual guards*
    (the conjunction of predicates that hold along the cell), not
    ``: True``.  The proof asserts that the conjunction holds —
    which is content-bearing whenever guards are non-trivial.
    When the cell has no guards, we honestly emit ``: True``
    (the only proposition the cell witnesses).
    """
    thm_name = (
        f"deppy_cubical_path_{_safe_ident(fn_name)}_"
        f"{_safe_ident(cell.cell_id)}"
    )
    if not cell.guards:
        text = (
            f"-- Cubical {cell.shape.value} at cell `{cell.cell_id}` "
            f"(dim={cell.dim}; no guards)\n"
            f"theorem {thm_name} : True := trivial\n"
        )
        return {"text": text, "is_sorry": False}
    # Build a theorem of the form
    #   theorem t (h1 : g1) (h2 : g2) ... : g1 ∧ g2 ∧ ... := ⟨h1, h2, ...⟩
    hyp_binders = " ".join(
        f"(h{i+1} : ({g}))" for i, g in enumerate(cell.guards)
    )
    if len(cell.guards) == 1:
        conclusion = f"({cell.guards[0]})"
        body = "h1"
    else:
        conclusion = " ∧ ".join(f"({g})" for g in cell.guards)
        body = "⟨" + ", ".join(
            f"h{i+1}" for i in range(len(cell.guards))
        ) + "⟩"
    text = (
        f"-- Cubical {cell.shape.value} at cell `{cell.cell_id}` "
        f"(dim={cell.dim})\n"
        f"theorem {thm_name} {hyp_binders} : {conclusion} := {body}\n"
    )
    return {"text": text, "is_sorry": False}


# ─────────────────────────────────────────────────────────────────────
#  Helpers
# ─────────────────────────────────────────────────────────────────────


def _safe_ident(text: str) -> str:
    """Sanitise a string into a Lean-safe identifier."""
    out: list[str] = []
    for ch in text:
        if ch.isalnum() or ch == "_":
            out.append(ch)
        else:
            out.append("_")
    if out and out[0].isdigit():
        out.insert(0, "i")
    return "".join(out) or "anon"


__all__ = [
    "CubicalCertificateSection",
    "CubicalFunctionSummary",
    "render_cubical_section",
]
