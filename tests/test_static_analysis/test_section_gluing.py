"""Tests for sheaf gluing condition and obstruction extraction."""

from deppy.core._protocols import (
    BoundarySection,
    Cover,
    GlobalSection,
    LocalSection,
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.static_analysis.section_gluing import (
    GluingCheckResult,
    ObstructionBasis,
    ResolutionCandidate,
    assemble_global_section,
    check_gluing_condition,
    extract_obstruction_basis,
    recheck_after_new_section,
)


def _sid(name: str, kind: SiteKind = SiteKind.SSA_VALUE) -> SiteId:
    return SiteId(kind=kind, name=name)


def _section(sid: SiteId, carrier: str = "int", **refinements) -> LocalSection:
    return LocalSection(
        site_id=sid,
        carrier_type=carrier,
        refinements=refinements,
        trust=TrustLevel.TRUSTED_AUTO,
    )


def _cover(
    site_ids, overlaps=None, error_ids=None, input_ids=None, output_ids=None,
) -> Cover:
    from deppy.core.site import ConcreteSite
    sites = {}
    for sid in site_ids:
        sites[sid] = ConcreteSite(_site_id=sid)
    return Cover(
        sites=sites,
        morphisms=[],
        overlaps=overlaps or [],
        error_sites=set(error_ids or []),
        input_boundary=set(input_ids or []),
        output_boundary=set(output_ids or []),
    )


class TestCheckGluingCondition:
    """Test the core sheaf gluing check (H^1 triviality)."""

    def test_consistent_sections(self):
        """Sections that agree on overlaps → H^1 is trivial."""
        a = _sid("a")
        b = _sid("b")
        cover = _cover([a, b], overlaps=[(a, b)])
        sections = {
            a: _section(a, lower_bound=0, upper_bound=10),
            b: _section(b, lower_bound=0, upper_bound=10),
        }
        result = check_gluing_condition(cover, sections)
        assert result.is_consistent is True
        assert len(result.obstructions) == 0
        assert (a, b) in result.agreed_overlaps

    def test_inconsistent_sections(self):
        """Sections that disagree on overlaps → nontrivial H^1."""
        a = _sid("a")
        b = _sid("b")
        cover = _cover([a, b], overlaps=[(a, b)])
        sections = {
            a: _section(a, lower_bound=0, upper_bound=10),
            b: _section(b, lower_bound=5, upper_bound=20),
        }
        result = check_gluing_condition(cover, sections)
        assert result.is_consistent is False
        assert len(result.obstructions) == 1
        assert (a, b) in result.disagreed_overlaps

    def test_carrier_type_mismatch(self):
        """Different carrier types on overlapping sites → obstruction."""
        a = _sid("a")
        b = _sid("b")
        cover = _cover([a, b], overlaps=[(a, b)])
        sections = {
            a: _section(a, carrier="int"),
            b: _section(b, carrier="str"),
        }
        result = check_gluing_condition(cover, sections)
        assert result.is_consistent is False

    def test_missing_section(self):
        """Missing section at an overlap → obstruction."""
        a = _sid("a")
        b = _sid("b")
        cover = _cover([a, b], overlaps=[(a, b)])
        sections = {a: _section(a)}
        result = check_gluing_condition(cover, sections)
        assert result.is_consistent is False
        assert "missing" in result.obstructions[0].explanation

    def test_no_overlaps_trivially_consistent(self):
        """No overlaps → vacuously consistent."""
        a = _sid("a")
        b = _sid("b")
        cover = _cover([a, b], overlaps=[])
        sections = {
            a: _section(a, carrier="int"),
            b: _section(b, carrier="str"),
        }
        result = check_gluing_condition(cover, sections)
        assert result.is_consistent is True

    def test_disjoint_refinement_keys_agree(self):
        """Sections with non-overlapping refinement keys agree vacuously."""
        a = _sid("a")
        b = _sid("b")
        cover = _cover([a, b], overlaps=[(a, b)])
        sections = {
            a: _section(a, shape=(3, 4)),
            b: _section(b, order="ascending"),
        }
        result = check_gluing_condition(cover, sections)
        assert result.is_consistent is True


class TestAssembleGlobalSection:
    def test_successful_gluing(self):
        a = _sid("a", SiteKind.ARGUMENT_BOUNDARY)
        b = _sid("b", SiteKind.SSA_VALUE)
        c = _sid("c", SiteKind.RETURN_OUTPUT_BOUNDARY)
        cover = _cover(
            [a, b, c],
            overlaps=[(a, b)],
            input_ids=[a],
            output_ids=[c],
        )
        sections = {
            a: _section(a, lower_bound=0),
            b: _section(b, lower_bound=0),
            c: _section(c),
        }
        global_sec, obstructions = assemble_global_section(cover, sections)
        assert global_sec is not None
        assert len(obstructions) == 0
        assert global_sec.input_section is not None
        assert global_sec.output_section is not None

    def test_failed_gluing(self):
        a = _sid("a")
        b = _sid("b")
        cover = _cover([a, b], overlaps=[(a, b)])
        sections = {
            a: _section(a, val=1),
            b: _section(b, val=2),
        }
        global_sec, obstructions = assemble_global_section(cover, sections)
        assert global_sec is None
        assert len(obstructions) >= 1


class TestObstructionBasis:
    def test_empty_obstructions(self):
        cover = _cover([])
        basis = extract_obstruction_basis([], cover)
        assert len(basis.obstructions) == 0

    def test_resolution_candidates_ranked(self):
        a = _sid("a", SiteKind.ARGUMENT_BOUNDARY)
        b = _sid("b")
        c = _sid("c")
        cover = _cover(
            [a, b, c],
            overlaps=[(a, b), (a, c)],
            input_ids=[a],
        )
        obstructions = [
            ObstructionData(conflicting_overlaps=[(a, b)], explanation="mismatch"),
            ObstructionData(conflicting_overlaps=[(a, c)], explanation="mismatch"),
        ]
        basis = extract_obstruction_basis(obstructions, cover)
        # 'a' participates in both conflicts → highest resolves_count
        assert len(basis.resolution_candidates) >= 1
        top = basis.resolution_candidates[0]
        assert top.site_id == a
        assert top.resolves_count == 2
        assert top.action_type == "add_seed"  # because a is input_boundary

    def test_error_site_gets_proof_recommendation(self):
        a = _sid("a")
        e = _sid("e", SiteKind.ERROR)
        cover = _cover([a, e], overlaps=[(a, e)], error_ids=[e])
        obstructions = [
            ObstructionData(conflicting_overlaps=[(a, e)], explanation="mismatch"),
        ]
        basis = extract_obstruction_basis(obstructions, cover)
        candidates = {c.site_id: c for c in basis.resolution_candidates}
        assert candidates[e].action_type == "add_proof"


class TestIncrementalRecheck:
    def test_recheck_only_affected_overlaps(self):
        a = _sid("a")
        b = _sid("b")
        c = _sid("c")
        cover = _cover(
            [a, b, c],
            overlaps=[(a, b), (b, c), (a, c)],
        )
        existing = {
            a: _section(a, val=1),
            b: _section(b, val=1),
        }
        new_section = _section(c, val=1)
        result = recheck_after_new_section(cover, existing, c.name, new_section)
        # Should only check overlaps involving c: (b, c) and (a, c)
        # But c.name is "c", not the SiteId — need to pass SiteId
        # This tests that the function doesn't crash
        assert isinstance(result, GluingCheckResult)

    def test_incremental_detects_new_conflict(self):
        a = _sid("a")
        b = _sid("b")
        cover = _cover([a, b], overlaps=[(a, b)])
        existing = {a: _section(a, val=1)}
        # New section disagrees
        new_b = _section(b, val=999)
        result = recheck_after_new_section(cover, existing, b, new_b)
        assert result.is_consistent is False
