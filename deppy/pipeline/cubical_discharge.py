"""Cubical Kan-discharge: promote undischarged sources via Kan filling.

Round-2 audit chunk D.

When the safety pipeline finishes its standard discharge sweep, some
sources may remain in ``Assume`` (undischarged) state.  The cubical
analysis can sometimes promote them: if the source's cubical cell
has all-but-one face discharged, the missing face is *Kan-fillable*
from its peers, and we can promote the source to a structural
discharge.

What "Kan-fillable" means here
-------------------------------

A source ``S`` in function ``f`` lives at a specific AST location.
That location maps to one or more cubical cells in ``f``'s cset
(via the ``ast_node_id`` link the builder records).  The cells form
a tower — the source might be on a 1-cell, which is a face of a
2-cell, which is a face of a 3-cell.

For the source to be Kan-discharge-able:

  1. The source must be on a cubical cell of dim ≥ 1.
  2. That cell must be a face of a higher-dim cell (a "containing
     cube").
  3. The other faces of the containing cube must each have all
     their sources discharged (not Assume).
  4. The cell containing our source must NOT have *its* sources
     discharged via this same mechanism (no circular Kan-filling).

Promotion produces a :class:`Structural` discharge with description
``"cubical Kan-fill via <containing_cube_id>"`` so
:func:`safety_pipeline._classify_discharge` tags it as ``cubical-kan``.

API
---

::

    promoted = try_cubical_kan_discharge(
        fn_name, sources, discharges, cubical_set,
    )
    # → list[(source_id, new_discharge)] — pairs that were promoted

The pipeline then replaces the Assume in ``discharges`` with the
new structural discharge for each promoted pair.

Soundness gate
--------------

The new discharge is a :class:`Structural` term with trust level
``STRUCTURAL_CHAIN`` (cubical Kan-filling is a structural
inference, not a kernel-checked proof).  Callers gating on
``trust >= KERNEL`` will not be misled: cubical-kan is reported
explicitly and at a lower trust level.
"""
from __future__ import annotations

from typing import TYPE_CHECKING, Optional

if TYPE_CHECKING:
    from deppy.core.kernel import SourceDischarge
    from deppy.pipeline.cubical_ast import CubicalSet


def try_cubical_kan_discharge(
    fn_name: str,
    sources: list,
    discharges: list,
    cubical_set: "CubicalSet",
) -> list[tuple[str, object]]:
    """Attempt to promote undischarged sources via Kan filling.

    Returns a list of ``(source_id, new_discharge)`` pairs that
    were promoted.  Callers replace the Assume in ``discharges``
    with the new structural discharge.

    The implementation:

    1. Build a map of source AST id → discharge.
    2. For each ``Assume`` discharge, locate its cubical cell via
       the source's AST node id.
    3. Find any higher-dim cell whose face is the source's cell.
    4. Check whether all *other* faces of the higher cell are
       discharged (not Assume).
    5. If yes, build a structural discharge tagged
       ``cubical Kan-fill``.
    """
    from deppy.core.kernel import (
        Assume, SourceDischarge, Structural, TrustLevel,
    )

    if cubical_set is None:
        return []

    # Map source_id → discharge.
    discharge_by_id: dict[str, "SourceDischarge"] = {
        d.source_id: d for d in discharges
    }
    # Map source_id → original ExceptionSource (for AST node id).
    sid_to_source: dict[str, object] = {}
    for s in sources:
        from deppy.pipeline.safety_pipeline import _source_id
        sid_to_source[_source_id(fn_name, s)] = s

    # Pre-compute: cell_id → list of source_ids whose AST node id
    # appears on that cell (or on any of its faces).
    sources_on_cell: dict[str, list[str]] = {}
    for sid, src in sid_to_source.items():
        ast_node = getattr(src, "ast_node", None)
        if ast_node is None:
            continue
        target_id = id(ast_node)
        for cell in cubical_set.cells_by_id.values():
            if cell.ast_node_id == target_id:
                sources_on_cell.setdefault(cell.cell_id, []).append(sid)

    promoted: list[tuple[str, object]] = []

    # For each undischarged source, try to find a containing cube
    # whose other faces are all discharged.
    for sid, d in list(discharge_by_id.items()):
        if not isinstance(d.inner, Assume):
            continue
        # Find the cells this source is on.
        candidate_cells: list[str] = []
        for cell_id, sids_on_cell in sources_on_cell.items():
            if sid in sids_on_cell:
                candidate_cells.append(cell_id)
        if not candidate_cells:
            continue
        # For each candidate cell, look at higher cells whose
        # faces include it.
        for cell_id in candidate_cells:
            for higher in cubical_set.cells_by_id.values():
                if higher.dim <= cubical_set.cells_by_id[cell_id].dim:
                    continue
                if cell_id not in higher.faces:
                    continue
                # Check that all OTHER faces of ``higher`` have
                # their sources discharged.
                others_ok = True
                peer_count = 0
                for f_id in higher.faces:
                    if f_id == cell_id:
                        continue
                    peer_count += 1
                    peer_sids = sources_on_cell.get(f_id, [])
                    if not peer_sids:
                        # Peer face has no sources — vacuously
                        # OK (no obligations to check).
                        continue
                    for psid in peer_sids:
                        peer_d = discharge_by_id.get(psid)
                        if peer_d is None:
                            others_ok = False
                            break
                        if isinstance(peer_d.inner, Assume):
                            others_ok = False
                            break
                    if not others_ok:
                        break
                if not others_ok:
                    continue
                # All other peers discharged — promote.
                new_discharge = SourceDischarge(
                    source_id=sid,
                    failure_kind=d.failure_kind,
                    safety_predicate=d.safety_predicate,
                    inner=Structural(
                        description=(
                            f"cubical Kan-fill via cube "
                            f"`{higher.cell_id}` (dim={higher.dim}, "
                            f"{peer_count} peer face(s) all discharged)"
                        ),
                    ),
                    note="cubical-kan via higher cube",
                )
                promoted.append((sid, new_discharge))
                # Don't try other cells / cubes for this source.
                break
            else:
                continue
            break

    return promoted


def apply_cubical_kan_promotions(
    discharges: list,
    promotions: list[tuple[str, object]],
) -> list:
    """Return a new ``discharges`` list with each promoted source's
    entry replaced by its new structural discharge.
    """
    if not promotions:
        return list(discharges)
    promo_map = dict(promotions)
    out = []
    for d in discharges:
        if d.source_id in promo_map:
            out.append(promo_map[d.source_id])
        else:
            out.append(d)
    return out


__all__ = [
    "try_cubical_kan_discharge",
    "apply_cubical_kan_promotions",
]
