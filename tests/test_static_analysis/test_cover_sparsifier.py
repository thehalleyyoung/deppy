"""Tests for cover sparsification strategies."""

from deppy.core._protocols import Cover, SiteId, SiteKind
from deppy.core.site import ConcreteMorphism, ConcreteSite
from deppy.static_analysis.cover_sparsifier import (
    CompositeSparsifier,
    CoverStats,
    RemoveDisconnectedSites,
    RemoveRedundantSSASites,
    compute_cover_stats,
    sparsify_cover,
)


def _sid(name: str, kind: SiteKind = SiteKind.SSA_VALUE) -> SiteId:
    return SiteId(kind=kind, name=name)


def _site(sid: SiteId) -> ConcreteSite:
    return ConcreteSite(_site_id=sid)


def _morph(src: SiteId, tgt: SiteId) -> ConcreteMorphism:
    return ConcreteMorphism(_source=src, _target=tgt)


class TestRemoveDisconnectedSites:
    def test_keeps_boundary_sites(self):
        inp = _sid("inp", SiteKind.ARGUMENT_BOUNDARY)
        out = _sid("out", SiteKind.RETURN_OUTPUT_BOUNDARY)
        disconnected = _sid("disc")
        cover = Cover(
            sites={inp: _site(inp), out: _site(out), disconnected: _site(disconnected)},
            morphisms=[],
            overlaps=[],
            input_boundary={inp},
            output_boundary={out},
        )
        strategy = RemoveDisconnectedSites()
        result = strategy.apply(cover)
        assert inp in result.sites
        assert out in result.sites
        assert disconnected not in result.sites

    def test_keeps_connected_sites(self):
        a = _sid("a")
        b = _sid("b")
        cover = Cover(
            sites={a: _site(a), b: _site(b)},
            morphisms=[_morph(a, b)],
        )
        strategy = RemoveDisconnectedSites()
        result = strategy.apply(cover)
        assert a in result.sites
        assert b in result.sites

    def test_keeps_error_sites(self):
        err = _sid("err", SiteKind.ERROR)
        cover = Cover(
            sites={err: _site(err)},
            morphisms=[],
            error_sites={err},
        )
        strategy = RemoveDisconnectedSites()
        result = strategy.apply(cover)
        assert err in result.sites


class TestRemoveRedundantSSASites:
    def test_removes_passthrough(self):
        a = _sid("a", SiteKind.ARGUMENT_BOUNDARY)
        b = _sid("b", SiteKind.SSA_VALUE)
        c = _sid("c", SiteKind.RETURN_OUTPUT_BOUNDARY)
        cover = Cover(
            sites={a: _site(a), b: _site(b), c: _site(c)},
            morphisms=[_morph(a, b), _morph(b, c)],
            overlaps=[],
            input_boundary={a},
            output_boundary={c},
        )
        strategy = RemoveRedundantSSASites()
        result = strategy.apply(cover)
        assert b not in result.sites
        assert a in result.sites
        assert c in result.sites

    def test_keeps_sites_with_overlaps(self):
        a = _sid("a", SiteKind.ARGUMENT_BOUNDARY)
        b = _sid("b", SiteKind.SSA_VALUE)
        c = _sid("c", SiteKind.RETURN_OUTPUT_BOUNDARY)
        cover = Cover(
            sites={a: _site(a), b: _site(b), c: _site(c)},
            morphisms=[_morph(a, b), _morph(b, c)],
            overlaps=[(a, b)],
            input_boundary={a},
            output_boundary={c},
        )
        strategy = RemoveRedundantSSASites()
        result = strategy.apply(cover)
        assert b in result.sites  # Kept because it participates in overlaps


class TestCompositeSparsifier:
    def test_default_strategies(self):
        sparsifier = CompositeSparsifier()
        # Should have at least RemoveDisconnected and RemoveRedundant
        assert len(sparsifier._strategies) >= 2

    def test_sparsify_removes_disconnected(self):
        inp = _sid("inp", SiteKind.ARGUMENT_BOUNDARY)
        disc = _sid("disc")
        cover = Cover(
            sites={inp: _site(inp), disc: _site(disc)},
            morphisms=[],
            input_boundary={inp},
        )
        result = sparsify_cover(cover)
        assert inp in result.sites
        assert disc not in result.sites


class TestCoverStats:
    def test_compute_stats(self):
        a = _sid("a", SiteKind.ARGUMENT_BOUNDARY)
        b = _sid("b", SiteKind.SSA_VALUE)
        c = _sid("c", SiteKind.ERROR)
        cover = Cover(
            sites={a: _site(a), b: _site(b), c: _site(c)},
            morphisms=[_morph(a, b)],
            overlaps=[(a, b)],
            error_sites={c},
            input_boundary={a},
            output_boundary=set(),
        )
        stats = compute_cover_stats(cover)
        assert stats.total_sites == 3
        assert stats.total_morphisms == 1
        assert stats.total_overlaps == 1
        assert stats.error_site_count == 1
        assert stats.input_boundary_count == 1
        assert stats.disconnected_sites == 1  # c is disconnected
        assert SiteKind.ARGUMENT_BOUNDARY in stats.sites_by_kind
        assert SiteKind.SSA_VALUE in stats.sites_by_kind
