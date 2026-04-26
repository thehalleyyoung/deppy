"""Tests for round-2 audit integration #2: ``select_implies_tactic``
consults the cubical structure.

When a cubical 1-cell carries both the pre and the post predicate
in its guards, the @implies obligation is structurally provable
via cubical Kan-filling.  The classifier returns CUBICAL_KAN.
"""
from __future__ import annotations

from deppy.lean.implies_tactics import (
    ImpliesClassification,
    select_implies_tactic,
)
from deppy.pipeline.cubical_ast import (
    Cell,
    CellShape,
    CubicalSet,
)


# ─────────────────────────────────────────────────────────────────────
#  CUBICAL_KAN classification
# ─────────────────────────────────────────────────────────────────────


class TestCubicalKanClassification:
    def test_cubical_witness_picked_when_present(self):
        # Build a cubical set with a 1-cell whose guards include
        # both the pre and the post.
        cset = CubicalSet(function_name="t")
        cset.add(Cell(cell_id="a", dim=0, shape=CellShape.POINT,
                      vertices=("a",)))
        cset.add(Cell(cell_id="b", dim=0, shape=CellShape.POINT,
                      vertices=("b",)))
        e = Cell(
            cell_id="e", dim=1, shape=CellShape.EDGE_SEQ,
            vertices=("a", "b"), faces=("a", "b"),
            guards=("x > 0", "x >= 0"),
        )
        cset.add(e)
        plan = select_implies_tactic(
            "x > 0", "x >= 0",
            py_types={"x": "int"},
            cubical_set=cset,
        )
        # Round-2 integration: when a cell has both guards, we
        # classify as CUBICAL_KAN.
        assert plan.classification == ImpliesClassification.CUBICAL_KAN
        assert "Deppy.deppy_kan" in plan.tactic_body

    def test_no_cubical_fallback_to_other_rules(self):
        # When no cubical set is supplied, fall back to the
        # standard classifier.
        plan = select_implies_tactic(
            "x > 0", "x >= 0",
            py_types={"x": "int"},
        )
        # Linear-arith picks omega.
        assert plan.classification != ImpliesClassification.CUBICAL_KAN
        assert plan.classification == ImpliesClassification.LINEAR_ARITH

    def test_cubical_set_without_witness_falls_through(self):
        # Cubical set has cells but no cell carries BOTH the pre
        # and the post.
        cset = CubicalSet(function_name="t")
        cset.add(Cell(cell_id="a", dim=0, shape=CellShape.POINT,
                      vertices=("a",)))
        cset.add(Cell(cell_id="b", dim=0, shape=CellShape.POINT,
                      vertices=("b",)))
        cset.add(Cell(
            cell_id="e", dim=1, shape=CellShape.EDGE_SEQ,
            vertices=("a", "b"), faces=("a", "b"),
            guards=("x > 0",),  # only pre, not post
        ))
        plan = select_implies_tactic(
            "x > 0", "x >= 0",
            py_types={"x": "int"},
            cubical_set=cset,
        )
        # No witness — fall through to LINEAR_ARITH.
        assert plan.classification != ImpliesClassification.CUBICAL_KAN
        assert plan.classification == ImpliesClassification.LINEAR_ARITH

    def test_user_proof_still_wins(self):
        # User proof always wins, regardless of cubical witness.
        cset = CubicalSet(function_name="t")
        plan = select_implies_tactic(
            "x > 0", "x >= 0",
            user_proof="omega",
            cubical_set=cset,
        )
        assert plan.is_user_supplied
        assert plan.tactic_body == "omega"
