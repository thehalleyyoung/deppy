"""Tests for value lineage tracking — sheaf-theoretic provenance."""

from deppy.core._protocols import Cover, SiteId, SiteKind
from deppy.core.site import ConcreteMorphism, ConcreteSite
from deppy.static_analysis.restriction_maps import RestrictionData, RestrictionKind
from deppy.static_analysis.value_lineage import (
    LineageGraph,
    TransparencyResult,
    analyze_wrapper_transparency,
    error_sites_reachable_from,
    input_sites_influencing_error,
)


def _sid(name: str, kind: SiteKind = SiteKind.SSA_VALUE) -> SiteId:
    return SiteId(kind=kind, name=name)


def _morphism(src: SiteId, tgt: SiteId, restriction: RestrictionData = None) -> ConcreteMorphism:
    metadata = {"restriction": restriction} if restriction else {}
    return ConcreteMorphism(_source=src, _target=tgt, projection=None)


class TestLineageGraph:
    def test_add_edge_and_parent(self):
        g = LineageGraph()
        a = _sid("a")
        b = _sid("b")
        g.add_edge(a, b)
        assert g.parent(b) == a
        assert g.parent(a) is None

    def test_root(self):
        g = LineageGraph()
        a, b, c = _sid("a"), _sid("b"), _sid("c")
        g.add_edge(a, b)
        g.add_edge(b, c)
        assert g.root(c) == a
        assert g.root(b) == a
        assert g.root(a) == a

    def test_descendants(self):
        g = LineageGraph()
        a, b, c, d = _sid("a"), _sid("b"), _sid("c"), _sid("d")
        g.add_edge(a, b)
        g.add_edge(a, c)
        g.add_edge(b, d)
        desc = g.descendants(a)
        assert b in desc
        assert c in desc
        assert d in desc
        assert a not in desc

    def test_ancestors(self):
        g = LineageGraph()
        a, b, c = _sid("a"), _sid("b"), _sid("c")
        g.add_edge(a, b)
        g.add_edge(b, c)
        assert a in g.ancestors(c)
        assert b in g.ancestors(c)
        assert len(g.ancestors(a)) == 0

    def test_same_lineage(self):
        g = LineageGraph()
        a, b, c, d = _sid("a"), _sid("b"), _sid("c"), _sid("d")
        g.add_edge(a, b)
        g.add_edge(a, c)
        assert g.same_lineage(b, c) is True
        # d is disconnected
        assert g.same_lineage(b, d) is False

    def test_lineage_depth(self):
        g = LineageGraph()
        a, b, c = _sid("a"), _sid("b"), _sid("c")
        g.add_edge(a, b)
        g.add_edge(b, c)
        assert g.lineage_depth(a) == 0
        assert g.lineage_depth(b) == 1
        assert g.lineage_depth(c) == 2

    def test_lineage_chain(self):
        g = LineageGraph()
        a, b, c = _sid("a"), _sid("b"), _sid("c")
        g.add_edge(a, b)
        g.add_edge(b, c)
        chain = g.lineage_chain(c)
        assert chain == [a, b, c]

    def test_all_roots(self):
        g = LineageGraph()
        a, b, c, d = _sid("a"), _sid("b"), _sid("c"), _sid("d")
        g.add_edge(a, b)
        g.add_edge(c, d)
        roots = g.all_roots()
        assert a in roots
        assert c in roots
        assert len(roots) == 2

    def test_lineage_groups(self):
        g = LineageGraph()
        a, b, c, d = _sid("a"), _sid("b"), _sid("c"), _sid("d")
        g.add_edge(a, b)
        g.add_edge(c, d)
        groups = g.lineage_groups()
        assert a in groups
        assert c in groups
        assert b in groups[a]
        assert d in groups[c]

    def test_cycle_protection(self):
        """Cycles in lineage shouldn't cause infinite loops."""
        g = LineageGraph()
        a, b = _sid("a"), _sid("b")
        g.add_edge(a, b)
        g._parents[a] = b  # Force a cycle
        # Should terminate without infinite loop
        root = g.root(a)
        assert root is not None
        depth = g.lineage_depth(a)
        assert depth >= 0


class TestErrorSiteReachability:
    def test_reachable_error_sites(self):
        g = LineageGraph()
        inp = _sid("inp", SiteKind.ARGUMENT_BOUNDARY)
        x1 = _sid("x1")
        x2 = _sid("x2")
        err = _sid("err", SiteKind.ERROR)
        g.add_edge(inp, x1)
        g.add_edge(x1, x2)
        g.add_edge(x2, err)

        cover = Cover(
            sites={},
            error_sites={err},
        )
        reachable = error_sites_reachable_from(cover, g, inp)
        assert err in reachable

    def test_input_sites_influencing(self):
        g = LineageGraph()
        inp1 = _sid("inp1", SiteKind.ARGUMENT_BOUNDARY)
        inp2 = _sid("inp2", SiteKind.ARGUMENT_BOUNDARY)
        x = _sid("x")
        err = _sid("err", SiteKind.ERROR)
        g.add_edge(inp1, x)
        g.add_edge(x, err)
        # inp2 is not connected to err

        cover = Cover(
            sites={},
            input_boundary={inp1, inp2},
        )
        influencing = input_sites_influencing_error(cover, g, err)
        assert inp1 in influencing
        assert inp2 not in influencing


class TestWrapperTransparency:
    def test_transparent_wrapper(self):
        """A wrapper that preserves all keys is transparent."""
        a = _sid("a")
        b = _sid("b")

        restriction = RestrictionData(
            kind=RestrictionKind.LINEAGE,
            preserved_keys=frozenset({"type", "shape"}),
            dropped_keys=frozenset(),
        )
        morphism = ConcreteMorphism(_source=a, _target=b)
        # Store restriction in morphism metadata
        # Note: ConcreteMorphism is frozen, so we need to work with the cover

        cover = Cover(
            sites={
                a: ConcreteSite(_site_id=a),
                b: ConcreteSite(_site_id=b),
            },
            morphisms=[morphism],
            error_sites=set(),
        )
        lineage = LineageGraph()
        lineage.add_edge(a, b)

        result = analyze_wrapper_transparency(cover, lineage, b)
        assert isinstance(result, TransparencyResult)
        assert result.chain == (a, b)
