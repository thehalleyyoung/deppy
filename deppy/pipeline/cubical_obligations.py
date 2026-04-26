"""Bridge: cubical AST analysis → kernel proof obligations.

This module converts the *geometric* result of
:mod:`deppy.pipeline.cubical_ast` into kernel-level proof terms
(:class:`KanFill`, :class:`HigherPath`) that
:class:`deppy.core.kernel.ProofKernel` can verify.

The motivation
---------------

The cubical analyser identifies *Kan-fillable* cells — cells in
the AST's cubical realisation with exactly one missing face whose
content can be deduced from peer faces.  But on its own it doesn't
discharge anything; the deduction has to land in the kernel for
the verdict to count.

This module produces the discharge:

::

    obligation = kan_candidate_to_obligation(candidate, cset)
    result = kernel.verify(ctx, goal, obligation.proof_term)

Each :class:`CubicalObligation` carries:

* ``proof_term`` — the kernel-level :class:`KanFill` or
  :class:`HigherPath` whose verification *certifies* the
  Kan-fillability claim.
* ``goal_predicate`` — the proposition the proof term claims.
* ``trust_floor`` — the trust level the kernel will return
  (``STRUCTURAL_CHAIN`` for Kan-filled discharges, since the
  fill itself is a structural inference).
* ``cell_id`` — back-reference to the cubical cell.

API
---

::

    obligations = cubical_set_to_obligations(cset)
    # → list[CubicalObligation]

    for ob in obligations:
        r = kernel.verify(ctx, goal, ob.proof_term)
        if r.success:
            # Kan filling discharged the obligation.
            ...

The kernel's :class:`KanFill` already validates structural
conditions (face endpoints; cube closure).  This module wires the
cubical-side data into the term so the kernel can run those checks.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from deppy.core.kernel import (
    HigherPath,
    KanFill,
    Refl,
    TrustLevel,
)
from deppy.core.types import Var
from deppy.pipeline.cubical_ast import (
    Cell,
    CellShape,
    CubicalSet,
    KanCandidate,
)


# ─────────────────────────────────────────────────────────────────────
#  Result type
# ─────────────────────────────────────────────────────────────────────


@dataclass
class CubicalObligation:
    """A kernel-level obligation derived from a cubical cell.

    ``proof_term`` is what the kernel verifies.  ``goal_predicate``
    is the human-readable proposition this term claims (the union
    of peer-face guards, conjoined).  ``trust_floor`` is the trust
    level the discharge will achieve when the proof term verifies.

    ``cell_id`` and ``kan_candidate`` keep the back-pointers for
    diagnostic / certificate use.
    """

    cell_id: str
    proof_term: object  # ProofTerm — but we don't import the alias to keep this loose
    goal_predicate: str
    trust_floor: TrustLevel
    kan_candidate: Optional[KanCandidate] = None
    notes: list[str] = field(default_factory=list)


# ─────────────────────────────────────────────────────────────────────
#  Translators — cell shape → kernel proof term
# ─────────────────────────────────────────────────────────────────────


def kan_candidate_to_obligation(
    candidate: KanCandidate, cset: CubicalSet,
) -> CubicalObligation:
    """Turn a :class:`KanCandidate` into a kernel
    :class:`KanFill` proof obligation.

    The KanFill term takes:
      * ``dimension``: the cube's geometric dimension
      * ``faces``: the *present* peer faces as proof terms
      * ``face_endpoints``: the (start, end) SynTerm pairs for
        each face — the kernel uses these to verify cube closure
      * ``missing_face_label``: identifies which face is to be
        filled (``"axis_<N>_eps_<E>"``)

    For each present face cell we synthesise a :class:`Refl` proof
    term over a :class:`Var` named after the cell — this is a
    placeholder that the kernel accepts when the cube structure is
    consistent.  Real proof content must come from elsewhere (the
    safety pipeline's per-source discharges); this term *carries
    the structural skeleton* that the kernel will check.
    """
    cell = cset.cells_by_id.get(candidate.cell_id)
    if cell is None:
        raise KeyError(
            f"KanCandidate references missing cell: {candidate.cell_id}"
        )

    # Collect the present faces' proof terms and endpoints.
    face_proofs: list[object] = []
    face_endpoints: list[tuple] = []
    for axis in range(cell.dim):
        for eps in (0, 1):
            if (axis, eps) == (
                candidate.missing_axis, candidate.missing_eps,
            ):
                continue
            face_idx = 2 * axis + eps
            if face_idx >= len(cell.faces):
                continue
            face_id = cell.faces[face_idx]
            face_cell = cset.cells_by_id.get(face_id)
            if face_cell is None:
                continue
            # Make a placeholder Refl proof term keyed by the
            # face cell's id.  The variable name is derived from
            # the cell id (sanitised to a valid SynTerm var name).
            v = Var(name=_safe_var(face_cell.cell_id))
            face_proofs.append(Refl(term=v))
            # Endpoints: vertices of this face.
            if face_cell.vertices:
                start = Var(name=_safe_var(face_cell.vertices[0]))
                end = Var(name=_safe_var(
                    face_cell.vertices[-1] if len(face_cell.vertices) > 1 else face_cell.vertices[0]
                ))
                face_endpoints.append((start, end))

    proof_term = KanFill(
        dimension=cell.dim,
        faces=face_proofs,
        face_endpoints=face_endpoints,
        missing_face_label=(
            f"axis_{candidate.missing_axis}_eps_{candidate.missing_eps}"
        ),
    )
    # Predicate: conjunction of implied guards.
    if candidate.implied_guards:
        goal_pred = " ∧ ".join(
            f"({g})" for g in candidate.implied_guards
        )
    else:
        goal_pred = "True"

    notes = [
        f"Kan-filled at cell {cell.cell_id} "
        f"(missing axis={candidate.missing_axis} "
        f"eps={candidate.missing_eps})",
        f"Implied from {candidate.peer_face_count} peer face(s).",
    ]

    return CubicalObligation(
        cell_id=cell.cell_id,
        proof_term=proof_term,
        goal_predicate=goal_pred,
        trust_floor=TrustLevel.STRUCTURAL_CHAIN,
        kan_candidate=candidate,
        notes=notes,
    )


def cell_to_higher_path(
    cell: Cell, cset: CubicalSet,
) -> Optional[CubicalObligation]:
    """Turn a 1-cell or higher into a :class:`HigherPath` obligation.

    Only emits when:
      * ``cell.dim >= 1``
      * the cell has at least one well-formed boundary

    Returns ``None`` for cells that don't fit the pattern.

    The HigherPath kernel term takes:
      * ``dimension``: cell's dim
      * ``vertices``: list of SynTerms (one per cube vertex)
      * ``boundary_proofs``: list of proof terms (one per boundary
        face, dim-1)
      * ``boundary_endpoints``: list of (start, end) vertex-index
        pairs — the kernel uses these to validate the cube
        structure (no degenerate / out-of-range endpoints)
    """
    if cell.dim < 1:
        return None
    vertices = [
        Var(name=_safe_var(v)) for v in cell.vertices
    ]
    boundary_proofs: list[object] = []
    boundary_endpoints: list[tuple[int, int]] = []
    for axis in range(cell.dim):
        for eps in (0, 1):
            face_idx = 2 * axis + eps
            if face_idx >= len(cell.faces):
                continue
            face_id = cell.faces[face_idx]
            face_cell = cset.cells_by_id.get(face_id)
            if face_cell is None:
                continue
            # Use a placeholder Refl proof.
            v = Var(name=_safe_var(face_cell.cell_id))
            boundary_proofs.append(Refl(term=v))
            # Endpoint indices: which two cell vertices lie on
            # this face?  For axis i, eps j: vertices whose
            # i-th bit equals j.
            face_indices: list[int] = []
            for k, _v in enumerate(cell.vertices):
                if ((k >> axis) & 1) == eps:
                    face_indices.append(k)
            if len(face_indices) >= 2:
                boundary_endpoints.append(
                    (face_indices[0], face_indices[-1])
                )

    if not boundary_proofs:
        return None

    proof_term = HigherPath(
        dimension=cell.dim,
        vertices=vertices,
        boundary_proofs=boundary_proofs,
        boundary_endpoints=boundary_endpoints,
    )
    pred = "True"
    if cell.guards:
        pred = " ∧ ".join(f"({g})" for g in cell.guards)
    return CubicalObligation(
        cell_id=cell.cell_id,
        proof_term=proof_term,
        goal_predicate=pred,
        trust_floor=TrustLevel.STRUCTURAL_CHAIN,
        notes=[
            f"HigherPath of dim {cell.dim} at cell {cell.cell_id} "
            f"({cell.shape.value})",
        ],
    )


def cubical_set_to_obligations(
    cset: CubicalSet, *,
    include_all_higher: bool = False,
) -> list[CubicalObligation]:
    """Generate obligations for the entire cubical set.

    Always:
      * emit a Kan-fill obligation for every Kan-fillable cell.

    When ``include_all_higher=True``:
      * also emit a HigherPath obligation for every cell of dim ≥ 1
        whose boundary is *complete* (no missing faces).  These are
        useful for asserting structural coherence even when there's
        no Kan-fill to do.
    """
    out: list[CubicalObligation] = []

    # Kan-fillable cells.
    for candidate in cset.find_kan_fillable():
        try:
            ob = kan_candidate_to_obligation(candidate, cset)
        except KeyError:
            continue
        out.append(ob)

    if include_all_higher:
        for cell in cset.cells_by_id.values():
            if cell.dim < 1:
                continue
            # Skip if it was already emitted via Kan-fill.
            if any(o.cell_id == cell.cell_id for o in out):
                continue
            # Skip cells with missing faces (HigherPath requires
            # a complete boundary).
            complete = all(
                cset.cells_by_id.get(fid) is not None
                for fid in cell.faces
            )
            if not complete:
                continue
            ob_hp = cell_to_higher_path(cell, cset)
            if ob_hp is not None:
                out.append(ob_hp)

    return out


# ─────────────────────────────────────────────────────────────────────
#  Helpers
# ─────────────────────────────────────────────────────────────────────


def _safe_var(name: str) -> str:
    """Convert a cell-id-style string into a valid Var name.

    Var names must start with a letter / underscore and contain
    only alphanumerics + underscore.  Cubical cell ids contain
    dots and digits at the start.
    """
    if not name:
        return "anon"
    out: list[str] = []
    for ch in name:
        if ch.isalnum() or ch == "_":
            out.append(ch)
        else:
            out.append("_")
    if out and out[0].isdigit():
        out.insert(0, "v")
    return "".join(out)


# ─────────────────────────────────────────────────────────────────────
#  Diagnostic rendering
# ─────────────────────────────────────────────────────────────────────


def render_obligations_summary(
    obligations: list[CubicalObligation],
) -> str:
    """Return a human-readable multi-line summary of obligations."""
    if not obligations:
        return "(no cubical obligations)\n"
    lines = [
        f"Cubical obligations ({len(obligations)} total):",
        "",
    ]
    by_kind: dict[str, list[CubicalObligation]] = {}
    for ob in obligations:
        kind = type(ob.proof_term).__name__
        by_kind.setdefault(kind, []).append(ob)
    for kind, group in sorted(by_kind.items()):
        lines.append(f"  {kind}: {len(group)} obligation(s)")
        for ob in group[:3]:
            lines.append(
                f"    {ob.cell_id} → trust ≥ {ob.trust_floor.name}"
            )
            if len(ob.goal_predicate) > 60:
                pred = ob.goal_predicate[:57] + "..."
            else:
                pred = ob.goal_predicate
            lines.append(f"      goal: {pred}")
        if len(group) > 3:
            lines.append(f"    ... +{len(group) - 3} more")
    return "\n".join(lines) + "\n"


__all__ = [
    "CubicalObligation",
    "kan_candidate_to_obligation",
    "cell_to_higher_path",
    "cubical_set_to_obligations",
    "render_obligations_summary",
]
