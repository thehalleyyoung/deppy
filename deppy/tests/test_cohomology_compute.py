"""Audit fix #4+#5 — standard cohomology with real computation.

Tests the simplicial cochain complex and the cohomology
computation built from a deppy verdict.

Sections:

* ``TestCochain`` — the data structure invariants.
* ``TestChainComplex`` — the level-0/1/2 structure, face maps,
  and coboundary operators.
* ``TestVerifyChainComplex`` — the δ²=0 invariant.
* ``TestCohomologyComputation`` — H^0/H^1/H^2 reflects the actual
  call graph.
* ``TestBuildFromVerdict`` — end-to-end on a synthetic Python
  module.
"""
from __future__ import annotations

import ast
import textwrap
from dataclasses import dataclass, field

from deppy.lean.cohomology_compute import (
    ChainComplex,
    ChainComplexAudit,
    Cochain,
    CohomologyComputation,
    build_chain_complex,
    render_chain_complex_lean,
)


# Lightweight FunctionVerdict / SafetyVerdict mocks.
@dataclass
class _FV:
    is_safe: bool = True


@dataclass
class _SV:
    functions: dict = field(default_factory=dict)


def _parse_module(src: str) -> dict[str, ast.FunctionDef]:
    src = textwrap.dedent(src)
    out = {}
    for node in ast.parse(src).body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            out[node.name] = node
    return out


# ─────────────────────────────────────────────────────────────────────
#  Cochain
# ─────────────────────────────────────────────────────────────────────


class TestCochain:
    def test_empty_cochain(self):
        c = Cochain(level=0)
        assert len(c) == 0
        assert "f" not in c
        assert c.get("f") is None

    def test_add_and_lookup(self):
        c = Cochain(level=0)
        c.add("f", "True")
        assert "f" in c
        assert c.get("f") == "True"
        assert len(c) == 1

    def test_simplices(self):
        c = Cochain(level=1)
        c.add(("f", "g"), "p")
        c.add(("g", "h"), "q")
        assert sorted(c.simplices()) == [("f", "g"), ("g", "h")]


# ─────────────────────────────────────────────────────────────────────
#  ChainComplex face maps + coboundaries
# ─────────────────────────────────────────────────────────────────────


class TestChainComplex:
    def test_empty(self):
        cx = ChainComplex.empty()
        assert len(cx.c0) == 0
        assert len(cx.c1) == 0
        assert len(cx.c2) == 0

    def test_face_d1(self):
        cx = ChainComplex.empty()
        # d^1_0(f, g) = g; d^1_1(f, g) = f.
        assert cx.face_d1(("f", "g"), 0) == "g"
        assert cx.face_d1(("f", "g"), 1) == "f"
        assert cx.face_d1(("f", "g"), 2) is None

    def test_face_d2(self):
        cx = ChainComplex.empty()
        # d^2_0(f, g, h) = (g, h); d^2_1 = (f, h); d^2_2 = (f, g).
        assert cx.face_d2(("f", "g", "h"), 0) == ("g", "h")
        assert cx.face_d2(("f", "g", "h"), 1) == ("f", "h")
        assert cx.face_d2(("f", "g", "h"), 2) == ("f", "g")
        assert cx.face_d2(("f", "g", "h"), 3) is None

    def test_coboundary_0(self):
        cx = ChainComplex.empty()
        cx.c0.add("f", "P")
        cx.c0.add("g", "Q")
        cx.calls["f"] = {"g"}
        delta = cx.coboundary_0(cx.c0)
        # δ^0(P, Q) over edge (f, g) = P → Q.
        assert ("f", "g") in delta
        assert "P" in delta.get(("f", "g"))
        assert "Q" in delta.get(("f", "g"))
        assert "→" in delta.get(("f", "g"))

    def test_coboundary_1(self):
        cx = ChainComplex.empty()
        cx.c1.add(("f", "g"), "Pfg")
        cx.c1.add(("g", "h"), "Pgh")
        cx.c1.add(("f", "h"), "Pfh")
        cx.calls = {"f": {"g"}, "g": {"h"}}
        delta = cx.coboundary_1(cx.c1)
        # The single 2-simplex is (f, g, h).
        assert ("f", "g", "h") in delta
        text = delta.get(("f", "g", "h"))
        # All three predicates appear in the implication.
        assert "Pgh" in text
        assert "Pfh" in text
        assert "Pfg" in text


# ─────────────────────────────────────────────────────────────────────
#  Chain-complex axiom δ² = 0
# ─────────────────────────────────────────────────────────────────────


class TestVerifyChainComplex:
    def test_empty_complex_passes(self):
        cx = ChainComplex.empty()
        audit = cx.verify_chain_complex()
        assert audit.d2_squared_zero
        assert audit.c0_size == 0
        assert audit.image_d0_size == 0

    def test_simple_call_chain_skips_non_transitive(self):
        # δ²=0 verification: a chain f→g→h without a direct f→h
        # edge has no 2-simplex face data for (f, h), so the triple
        # is *skipped* (not a mismatch).  The audit reports skipped
        # but still d2_squared_zero=True (no false claims).
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.c0.add("g", "Pg")
        cx.c0.add("h", "Ph")
        cx.calls = {"f": {"g"}, "g": {"h"}}  # no f→h
        audit = cx.verify_chain_complex()
        assert audit.d2_squared_zero
        assert audit.image_d0_size == 2  # (f,g), (g,h)
        # Skipped because (f, h) isn't a call edge, so δ¹(δ⁰(c0))
        # has nothing to check for the (f, g, h) triple.
        assert audit.triples_skipped >= 1
        assert audit.triples_verified == 0
        assert not audit.mismatch_simplices

    def test_filled_triangle_actually_verifies(self):
        # A "filled" triangle (f calls g, g calls h, AND f calls h)
        # has all three faces in C¹, so δ¹(δ⁰(c0)) emits a value
        # for (f, g, h) and ``verify_chain_complex`` actually
        # exercises the tautology check.
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.c0.add("g", "Pg")
        cx.c0.add("h", "Ph")
        cx.calls = {"f": {"g", "h"}, "g": {"h"}}  # f also calls h
        audit = cx.verify_chain_complex()
        assert audit.d2_squared_zero
        # The triple (f, g, h) is now verifiable.
        assert audit.triples_verified >= 1
        assert not audit.mismatch_simplices


# ─────────────────────────────────────────────────────────────────────
#  Cohomology computation
# ─────────────────────────────────────────────────────────────────────


class TestCohomologyComputation:
    def test_empty_complex(self):
        cx = ChainComplex.empty()
        coh = cx.compute_cohomology()
        assert coh.h0_size == 0
        assert coh.h1_size == 0
        assert coh.h2_size == 0

    def test_function_no_calls_in_h0(self):
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.calls["f"] = set()
        coh = cx.compute_cohomology()
        # f has no outgoing calls → trivially in H^0.
        assert "f" in coh.h0_representatives
        assert coh.h0_size == 1

    def test_function_with_satisfied_callee_in_h0(self):
        # Audit fix (round 2): C¹ predicate must MATCH δ⁰(c0)
        # canonically — not just have the same simplex key.  Build
        # c1 with the same shape δ⁰ would emit.
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.c0.add("g", "Pg")
        cx.calls["f"] = {"g"}
        cx.c1.add(("f", "g"), "(Pf) → (Pg)")
        coh = cx.compute_cohomology()
        assert "f" in coh.h0_representatives

    def test_function_with_mismatched_callee_pred_NOT_in_h0(self):
        # Audit-fix invariant: a C¹ predicate that doesn't match
        # δ⁰(c0) on the edge means f is NOT in ker δ⁰.  Before the
        # fix this would have wrongly placed f in H⁰ because the
        # check only considered simplex membership.
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.c0.add("g", "Pg")
        cx.calls["f"] = {"g"}
        cx.c1.add(("f", "g"), "Pfg")  # ≠ "(Pf) → (Pg)"
        coh = cx.compute_cohomology()
        assert "f" not in coh.h0_representatives

    def test_h1_obstruction_when_edge_not_in_image(self):
        # Edge (f, g) is in C^1 but C^0 is empty so im δ^0 doesn't
        # cover it.
        cx = ChainComplex.empty()
        cx.c1.add(("f", "g"), "Pfg")
        # No c0, no calls — the image of δ^0 is empty.
        coh = cx.compute_cohomology()
        assert ("f", "g") in coh.h1_obstructions

    def test_h1_no_obstruction_when_pred_matches(self):
        # The C¹ predicate matches δ⁰(c0) canonically → trivial class.
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.c0.add("g", "Pg")
        cx.calls["f"] = {"g"}
        cx.c1.add(("f", "g"), "(Pf) → (Pg)")
        coh = cx.compute_cohomology()
        assert ("f", "g") not in coh.h1_obstructions

    def test_h1_obstruction_when_pred_mismatches(self):
        # Audit-fix invariant: a C¹ predicate that's just a fresh
        # name "Pfg" (with no relation to δ⁰(c0)) is correctly
        # classified as an obstruction.  Before the fix this would
        # have been a trivial class because the simplex was present.
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.c0.add("g", "Pg")
        cx.calls["f"] = {"g"}
        cx.c1.add(("f", "g"), "Pfg")
        coh = cx.compute_cohomology()
        assert ("f", "g") in coh.h1_obstructions


# ─────────────────────────────────────────────────────────────────────
#  build_chain_complex from a Python module
# ─────────────────────────────────────────────────────────────────────


class TestBuildFromVerdict:
    def test_simple_function(self):
        fn_nodes = _parse_module("""
            def f():
                return 1
        """)
        verdict = _SV(functions={"f": _FV(is_safe=True)})
        cx = build_chain_complex(verdict, fn_nodes)
        assert "f" in cx.c0
        # No calls → no C^1 / C^2.
        assert len(cx.c1) == 0
        assert len(cx.c2) == 0

    def test_call_chain(self):
        fn_nodes = _parse_module("""
            def f():
                return g()
            def g():
                return h()
            def h():
                return 1
        """)
        verdict = _SV(functions={
            "f": _FV(is_safe=True),
            "g": _FV(is_safe=True),
            "h": _FV(is_safe=True),
        })
        cx = build_chain_complex(verdict, fn_nodes)
        assert ("f", "g") in cx.c1
        assert ("g", "h") in cx.c1
        assert ("f", "g", "h") in cx.c2

    def test_diamond(self):
        fn_nodes = _parse_module("""
            def top():
                return a() + b()
            def a():
                return c()
            def b():
                return c()
            def c():
                return 1
        """)
        verdict = _SV(functions={
            n: _FV(is_safe=True) for n in ("top", "a", "b", "c")
        })
        cx = build_chain_complex(verdict, fn_nodes)
        # 4 call edges: top→a, top→b, a→c, b→c.
        assert len(cx.c1) == 4
        # 2 composition triples: (top, a, c), (top, b, c).
        assert ("top", "a", "c") in cx.c2
        assert ("top", "b", "c") in cx.c2

    def test_unsafe_function_predicate(self):
        fn_nodes = _parse_module("""
            def f():
                return 1
        """)
        verdict = _SV(functions={"f": _FV(is_safe=False)})
        cx = build_chain_complex(verdict, fn_nodes)
        # Predicate is "True" (default) when not safe; we check
        # the structural shape exists, not the predicate's truth.
        assert cx.c0.get("f") == "True"


# ─────────────────────────────────────────────────────────────────────
#  Lean rendering
# ─────────────────────────────────────────────────────────────────────


class TestLeanRender:
    def test_render_includes_levels(self):
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.c1.add(("f", "g"), "Pfg")
        cx.calls = {"f": {"g"}}
        text = render_chain_complex_lean(cx)
        assert "C^0" in text
        assert "C^1" in text
        assert "C^2" in text
        assert "δ^0" in text
        assert "δ^1" in text
        # Header explains the implication-form coboundary.
        assert "implication" in text.lower()

    def test_render_includes_sizes(self):
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.c0.add("g", "Pg")
        text = render_chain_complex_lean(cx)
        # ``|C^0| = 2`` should appear.
        assert "|C^0| = 2" in text

    def test_render_includes_cohomology(self):
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.calls["f"] = set()
        text = render_chain_complex_lean(cx)
        # H^0 size mentioned.
        assert "H^0" in text


# ─────────────────────────────────────────────────────────────────────
#  Audit-fix invariants
# ─────────────────────────────────────────────────────────────────────


class TestAuditInvariants:
    """The audit said the original IsCocycle was a pullback-form, not
    a proper alternating-coboundary.  We verify the new form:

    * δ^0 produces *implications* on call edges (not just pullbacks).
    * δ^1 produces *triple-implications* (g→h ∧ f→h ⟹ f→g) on
      composition triples.
    * H^k computation follows the standard quotient definition
      ``ker δ^k / im δ^(k-1)``.
    """

    def test_d0_produces_implication(self):
        cx = ChainComplex.empty()
        cx.c0.add("f", "Pf")
        cx.c0.add("g", "Pg")
        cx.calls["f"] = {"g"}
        delta = cx.coboundary_0(cx.c0)
        text = delta.get(("f", "g"))
        assert "→" in text  # implication

    def test_d1_produces_triple_implication(self):
        cx = ChainComplex.empty()
        cx.c1.add(("f", "g"), "Pfg")
        cx.c1.add(("g", "h"), "Pgh")
        cx.c1.add(("f", "h"), "Pfh")
        cx.calls = {"f": {"g"}, "g": {"h"}}
        delta = cx.coboundary_1(cx.c1)
        text = delta.get(("f", "g", "h"))
        # Triple-implication structure: (Pgh ∧ Pfh) → Pfg.
        assert "∧" in text
        assert "→" in text

    def test_h_sizes_match_quotient_definition(self):
        cx = ChainComplex.empty()
        # Three functions, no calls.
        for n in ("f", "g", "h"):
            cx.c0.add(n, f"P{n}")
            cx.calls[n] = set()
        coh = cx.compute_cohomology()
        # All three functions have empty outgoing edges, so all
        # three are in ker δ^0; H^0 = ker δ^0 / im δ^(-1) = ker δ^0.
        assert coh.h0_size == 3
        # No C^1, no C^2.
        assert coh.h1_size == 0
        assert coh.h2_size == 0
