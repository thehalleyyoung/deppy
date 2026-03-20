from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))

from deppy.core._protocols import SiteId, SiteKind
from deppy.core.site import ConcreteMorphism, ConcreteSite, CoverBuilder
from deppy.cover import affected_stalks, locate_sites_for_lines, site_source_lines
from deppy.core.site_cover import SiteCoverSynthesizer


def test_affected_stalks_expands_over_overlap_and_morphism() -> None:
    arg = SiteId(SiteKind.ARGUMENT_BOUNDARY, "arg:x", ("mod.py", 10, 0))
    ssa = SiteId(SiteKind.SSA_VALUE, "ssa:x_0", ("mod.py", 10, 0))
    guard = SiteId(SiteKind.BRANCH_GUARD, "guard:x", ("mod.py", 11, 0))
    builder = CoverBuilder()
    builder.add_site(ConcreteSite(_site_id=arg, _metadata={"param_name": "x"}))
    builder.add_site(ConcreteSite(_site_id=ssa, _metadata={"var_name": "x", "ssa_version": 0}))
    builder.add_site(ConcreteSite(_site_id=guard, _metadata={"narrowed_vars": ["x"], "line": 11}))
    builder.add_morphism(ConcreteMorphism(_source=arg, _target=ssa))
    builder.add_overlap(ssa, guard)
    cover = builder.build()

    report = affected_stalks(cover, {10}, max_hops=2)

    assert report.changed_lines == (10,)
    assert report.seed_sites == (arg, ssa)
    assert [stalk.site_id for stalk in report.stalks] == [arg, guard, ssa]
    guard_stalk = next(stalk for stalk in report.stalks if stalk.site_id == guard)
    assert guard_stalk.distance == 1
    assert guard_stalk.overlaps == (ssa,)
    assert "overlap_neighbor" in guard_stalk.reasons


def test_affected_stalks_handles_no_matching_lines_conservatively() -> None:
    cover = SiteCoverSynthesizer().synthesize(
        """

def no_imports(x):
    y = x + 1
    return y
"""
    )

    report = affected_stalks(cover, {99})

    assert report.requires_full_reanalysis is True
    assert report.seed_sites == ()
    assert report.stalks == ()
    assert report.warnings


def test_site_source_lines_handles_line_and_column_locations() -> None:
    site_id = SiteId(SiteKind.SSA_VALUE, "ssa:x_0", ("file.py", 7, 0))
    assert site_source_lines(site_id) == (7,)


def test_locate_sites_for_lines_is_deterministic() -> None:
    cover = SiteCoverSynthesizer().synthesize(
        """

def sample(a, b):
    total = a + b
    if total > 0:
        return total
    return 0
"""
    )
    first = locate_sites_for_lines(cover, {4})
    second = locate_sites_for_lines(cover, {4})
    assert first == second
