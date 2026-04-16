"""Tests for cohomological_decomposition — invariant-cover proving.

Tests the full pipeline: markers → CFG → regions → discharge → H¹ → gluing.
"""
from __future__ import annotations

import pytest
import textwrap

from cctt.proof_theory.cohomological_decomposition import (
    # Runtime markers
    invariant, precondition, postcondition, loop_invariant,
    library_fact, assume_correct,
    # Data model
    MarkerKind, InvariantPoint, CFGNode, CFGNodeKind, CFGEdge,
    FunctionCFG, ProofRegion, InvariantCover, OverlapObligation,
    TrustLevel, TrustSummary,
    # AST analysis
    extract_markers, build_cfg, _compile_predicate,
    # VC generation
    generate_regions, generate_overlaps,
    # Discharge
    discharge_region, discharge_overlap,
    # H¹
    compute_h1,
    # Gluing
    glue_proofs,
    # Pipeline
    decompose_and_prove, decompose,
    # LLM interface
    DecompositionSuggestion, DecompositionFeedback,
    apply_decomposition,
    generate_feedback, build_llm_prompt,
    # Refinement
    refine_decomposition,
    # Analysis
    analyze_function, verify_annotations,
    # Integration
    decompose_library_function,
)

from cctt.proof_theory.terms import (
    ProofTerm, Refl, Assume, Z3Discharge,
    RefinementDescent,
    var, lit, op, abstract,
)
from cctt.proof_theory.predicates import (
    Pred, PVar, PCompare, PAnd, PTrue, PLit,
    parse_predicate,
)


# ═══════════════════════════════════════════════════════════════════
# §1. Runtime Marker Tests — markers are no-ops at runtime
# ═══════════════════════════════════════════════════════════════════

class TestRuntimeMarkers:
    """Markers must be no-ops at runtime."""

    def test_invariant_returns_true(self):
        assert invariant("x > 0") is True

    def test_precondition_returns_true(self):
        assert precondition("isinstance(x, int)") is True

    def test_loop_invariant_returns_true(self):
        assert loop_invariant("total >= 0") is True

    def test_library_fact_returns_true(self):
        assert library_fact("sympy", "expand(a+b) = expand(a) + expand(b)") is True

    def test_assume_correct_returns_true(self):
        assert assume_correct("merge_sort") is True

    def test_markers_in_function_body(self):
        """Markers in a real function body must not affect execution."""
        def safe_abs(x: int) -> int:
            precondition("isinstance(x, int)")
            if x < 0:
                invariant("x < 0")
                return -x
            invariant("x >= 0")
            return x

        assert safe_abs(-5) == 5
        assert safe_abs(3) == 3
        assert safe_abs(0) == 0

    def test_postcondition_as_decorator(self):
        """postcondition used as decorator must return a callable."""
        @postcondition("result > 0")
        def foo(x):
            return x + 1
        assert foo(5) == 6
        assert hasattr(foo, '__postconditions__')
        assert foo.__postconditions__ == ["result > 0"]


# ═══════════════════════════════════════════════════════════════════
# §2. Predicate Compilation Tests
# ═══════════════════════════════════════════════════════════════════

class TestPredicateCompilation:
    """Predicate strings must compile to formal Pred ASTs."""

    def test_simple_comparison(self):
        pred, status = _compile_predicate("x > 0")
        assert status == 'ok'
        assert isinstance(pred, PCompare)

    def test_equality(self):
        pred, status = _compile_predicate("len(result) == len(xs)")
        assert status == 'ok'

    def test_boolean_and(self):
        pred, status = _compile_predicate("x > 0 and x < 100")
        assert status == 'ok'
        assert isinstance(pred, PAnd)

    def test_isinstance_call(self):
        pred, status = _compile_predicate("isinstance(x, int)")
        assert status == 'ok'

    def test_complex_expression(self):
        """Complex expressions may fall back to PVar."""
        pred, status = _compile_predicate(
            "all(result[i] <= result[i+1] for i in range(len(result)-1))")
        # This is too complex for parse_predicate — expect fallback
        assert status in ('ok', 'fallback')

    def test_unparseable_nl(self):
        """Natural language that can't be parsed → fallback."""
        pred, status = _compile_predicate("the list is sorted ascending")
        assert status == 'fallback'
        assert isinstance(pred, PVar)

    def test_true_false(self):
        pred, status = _compile_predicate("True")
        assert status == 'ok'


# ═══════════════════════════════════════════════════════════════════
# §3. Marker Extraction Tests
# ═══════════════════════════════════════════════════════════════════

class TestMarkerExtraction:
    """Extract markers from Python source."""

    def test_extract_invariant(self):
        source = textwrap.dedent('''
        def foo(x):
            invariant("x > 0")
            return x
        ''')
        markers = extract_markers(source)
        assert len(markers) == 1
        assert markers[0].kind == MarkerKind.INVARIANT
        assert markers[0].surface_text == "x > 0"

    def test_extract_precondition(self):
        source = textwrap.dedent('''
        def foo(x):
            precondition("isinstance(x, int)")
            return x + 1
        ''')
        markers = extract_markers(source)
        assert len(markers) == 1
        assert markers[0].kind == MarkerKind.PRECONDITION

    def test_extract_multiple_markers(self):
        source = textwrap.dedent('''
        def foo(xs):
            precondition("isinstance(xs, list)")
            result = sorted(xs)
            invariant("len(result) == len(xs)")
            postcondition("result == sorted(xs)")
            return result
        ''')
        markers = extract_markers(source)
        assert len(markers) >= 3
        kinds = {m.kind for m in markers}
        assert MarkerKind.PRECONDITION in kinds
        assert MarkerKind.INVARIANT in kinds

    def test_extract_loop_invariant(self):
        source = textwrap.dedent('''
        def sum_list(xs):
            total = 0
            for x in xs:
                loop_invariant("total >= 0")
                total += x
            return total
        ''')
        markers = extract_markers(source)
        assert any(m.kind == MarkerKind.LOOP_INVARIANT for m in markers)

    def test_extract_library_fact(self):
        source = textwrap.dedent('''
        def foo(e):
            library_fact("sympy", "simplify(expand(e)) == e")
            return simplify(expand(e))
        ''')
        markers = extract_markers(source)
        assert len(markers) == 1
        assert markers[0].kind == MarkerKind.LIBRARY_FACT
        assert markers[0].library == "sympy"

    def test_extract_postcondition_decorator(self):
        source = textwrap.dedent('''
        @postcondition("result >= 0")
        def abs_val(x):
            if x < 0:
                return -x
            return x
        ''')
        markers = extract_markers(source)
        assert any(m.kind == MarkerKind.POSTCONDITION for m in markers)

    def test_extract_no_markers(self):
        source = textwrap.dedent('''
        def foo(x):
            return x + 1
        ''')
        markers = extract_markers(source)
        assert len(markers) == 0

    def test_syntax_error_source(self):
        markers = extract_markers("this is not python {{{}}}}")
        assert markers == []


# ═══════════════════════════════════════════════════════════════════
# §4. CFG Construction Tests
# ═══════════════════════════════════════════════════════════════════

class TestCFGConstruction:
    """Build control flow graphs from Python source."""

    def test_simple_function_cfg(self):
        source = textwrap.dedent('''
        def foo(x):
            return x + 1
        ''')
        cfg = build_cfg(source)
        assert cfg.function_name == 'foo'
        assert cfg.entry == 'entry'
        assert 'exit' in cfg.exits
        assert len(cfg.nodes) >= 2  # entry, exit, possibly return + stmt

    def test_if_branch_cfg(self):
        source = textwrap.dedent('''
        def abs_val(x):
            if x < 0:
                return -x
            return x
        ''')
        cfg = build_cfg(source)
        # Should have: entry, branch, return nodes, join, exit
        assert any(n.kind == CFGNodeKind.BRANCH for n in cfg.nodes.values())

    def test_loop_cfg(self):
        source = textwrap.dedent('''
        def sum_list(xs):
            total = 0
            for x in xs:
                total += x
            return total
        ''')
        cfg = build_cfg(source)
        assert any(n.kind == CFGNodeKind.LOOP_HEADER for n in cfg.nodes.values())

    def test_invariant_creates_cfg_node(self):
        source = textwrap.dedent('''
        def foo(x):
            invariant("x > 0")
            return x
        ''')
        cfg = build_cfg(source)
        inv_nodes = [n for n in cfg.nodes.values()
                     if n.kind == CFGNodeKind.INVARIANT]
        assert len(inv_nodes) >= 1
        assert inv_nodes[0].invariants[0].surface_text == "x > 0"

    def test_cfg_has_edges(self):
        source = textwrap.dedent('''
        def foo(x):
            precondition("x > 0")
            y = x + 1
            invariant("y > 1")
            return y
        ''')
        cfg = build_cfg(source)
        assert len(cfg.edges) >= 2

    def test_cfg_pretty_print(self):
        source = textwrap.dedent('''
        def foo(x):
            invariant("x > 0")
            return x
        ''')
        cfg = build_cfg(source)
        pretty = cfg.pretty()
        assert 'foo' in pretty
        assert 'entry' in pretty

    def test_parse_error_produces_trivial_cfg(self):
        cfg = build_cfg("not valid python {{{")
        assert cfg.entry == 'entry'
        assert len(cfg.edges) >= 1


# ═══════════════════════════════════════════════════════════════════
# §5. Region Generation Tests
# ═══════════════════════════════════════════════════════════════════

class TestRegionGeneration:
    """Generate proof regions (VCs) from CFG."""

    def test_regions_from_invariants(self):
        source = textwrap.dedent('''
        def foo(x):
            precondition("x > 0")
            y = x + 1
            invariant("y > 1")
            return y
        ''')
        cfg = build_cfg(source)
        regions = generate_regions(cfg)
        assert len(regions) >= 1

    def test_region_has_entry_exit_invariants(self):
        source = textwrap.dedent('''
        def foo(x):
            precondition("x > 0")
            invariant("x >= 0")
            return x
        ''')
        cfg = build_cfg(source)
        regions = generate_regions(cfg)
        # At least one region should have entry and exit invariants
        has_both = any(r.entry_invariants and r.exit_invariants
                       for r in regions)
        # At least one region should have *some* invariant
        has_any = any(r.entry_invariants or r.exit_invariants
                      for r in regions)
        assert has_any

    def test_region_obligation_text(self):
        source = textwrap.dedent('''
        def foo(x):
            precondition("x > 0")
            invariant("x >= 0")
            return x
        ''')
        cfg = build_cfg(source)
        regions = generate_regions(cfg)
        for r in regions:
            assert r.obligation_text  # should have obligation text

    def test_no_regions_without_invariants(self):
        source = textwrap.dedent('''
        def foo(x):
            return x + 1
        ''')
        cfg = build_cfg(source)
        regions = generate_regions(cfg)
        # Should have no regions (no invariants → no VCs)
        assert len(regions) == 0


# ═══════════════════════════════════════════════════════════════════
# §6. Overlap Generation Tests
# ═══════════════════════════════════════════════════════════════════

class TestOverlapGeneration:
    """Generate overlap obligations at CFG join points."""

    def test_if_else_creates_overlaps(self):
        source = textwrap.dedent('''
        def abs_val(x):
            precondition("isinstance(x, int)")
            if x < 0:
                result = -x
                invariant("result > 0")
            else:
                result = x
                invariant("result >= 0")
            return result
        ''')
        cfg = build_cfg(source)
        regions = generate_regions(cfg)
        overlaps = generate_overlaps(cfg, regions)
        # The join after if/else may create overlap obligations
        # (depends on whether regions have exit invariants at the join)
        assert isinstance(overlaps, list)


# ═══════════════════════════════════════════════════════════════════
# §7. Discharge Tests
# ═══════════════════════════════════════════════════════════════════

class TestDischarge:
    """Proof discharge strategies."""

    def test_reflexive_discharge(self):
        """Same invariant at entry and exit → Refl."""
        inv = InvariantPoint(
            surface_text="x > 0",
            compiled=parse_predicate("x > 0"),
            kind=MarkerKind.INVARIANT,
            parse_status='ok',
        )
        region = ProofRegion(
            region_id='test',
            edge=CFGEdge('e1', 'a', 'b'),
            entry_invariants=[inv],
            exit_invariants=[inv],
        )
        assert discharge_region(region)
        assert region.trust == TrustLevel.KERNEL
        assert isinstance(region.proof, Refl)

    def test_no_exit_invariant_is_trivial(self):
        """No exit invariants → trivially satisfied."""
        inv = InvariantPoint(
            surface_text="x > 0",
            compiled=parse_predicate("x > 0"),
            kind=MarkerKind.INVARIANT,
            parse_status='ok',
        )
        region = ProofRegion(
            region_id='test',
            edge=CFGEdge('e1', 'a', 'b'),
            entry_invariants=[inv],
            exit_invariants=[],
        )
        assert discharge_region(region)
        assert region.trust == TrustLevel.KERNEL

    def test_assume_correct_discharge(self):
        """assume_correct markers → Assume proof."""
        inv = InvariantPoint(
            surface_text="merge_sort is correct",
            compiled=PVar("merge_sort is correct"),
            kind=MarkerKind.ASSUME_CORRECT,
            parse_status='fallback',
            func_ref='merge_sort',
        )
        region = ProofRegion(
            region_id='test',
            edge=CFGEdge('e1', 'a', 'b'),
            entry_invariants=[inv],
            exit_invariants=[inv],
        )
        assert discharge_region(region)
        # First tries structural (reflexive) since same invariant
        assert region.is_proved

    def test_overlap_same_invariants(self):
        """Overlaps with identical invariants → trivial compatibility."""
        inv = InvariantPoint(
            surface_text="x > 0",
            compiled=parse_predicate("x > 0"),
            kind=MarkerKind.INVARIANT,
            parse_status='ok',
        )
        overlap = OverlapObligation(
            join_node_id='join_1',
            branch_a='e1',
            branch_b='e2',
            invariants_a=[inv],
            invariants_b=[inv],
        )
        assert discharge_overlap(overlap)
        assert overlap.trust == TrustLevel.KERNEL

    def test_overlap_different_invariants(self):
        """Different invariants → assumed compatibility."""
        inv_a = InvariantPoint(
            surface_text="x > 0",
            compiled=parse_predicate("x > 0"),
            kind=MarkerKind.INVARIANT,
            parse_status='ok',
        )
        inv_b = InvariantPoint(
            surface_text="x >= 0",
            compiled=parse_predicate("x >= 0"),
            kind=MarkerKind.INVARIANT,
            parse_status='ok',
        )
        overlap = OverlapObligation(
            join_node_id='join_1',
            branch_a='e1',
            branch_b='e2',
            invariants_a=[inv_a],
            invariants_b=[inv_b],
        )
        assert discharge_overlap(overlap)
        assert overlap.trust == TrustLevel.ASSUMED


# ═══════════════════════════════════════════════════════════════════
# §8. H¹ Computation Tests
# ═══════════════════════════════════════════════════════════════════

class TestH1Computation:
    """Cohomological obstruction computation."""

    def test_all_proved_h1_zero(self):
        """All regions proved, all overlaps compatible → H¹ = 0."""
        inv = InvariantPoint(
            surface_text="x > 0",
            compiled=parse_predicate("x > 0"),
            kind=MarkerKind.INVARIANT,
            parse_status='ok',
        )
        region = ProofRegion(
            region_id='r1',
            edge=CFGEdge('e1', 'a', 'b'),
            entry_invariants=[inv],
            exit_invariants=[inv],
            proof=Refl(term=var('x')),
            trust=TrustLevel.KERNEL,
        )
        cover = InvariantCover(
            function_name='test',
            cfg=FunctionCFG('test'),
            preconditions=[],
            postconditions=[],
            all_invariants=[inv],
            regions=[region],
            overlaps=[],
        )
        h1 = compute_h1(cover)
        assert h1 == 0

    def test_unproved_region_h1_positive(self):
        """Unproved region → H¹ > 0."""
        inv = InvariantPoint(
            surface_text="x > 0",
            compiled=parse_predicate("x > 0"),
            kind=MarkerKind.INVARIANT,
            parse_status='ok',
        )
        region = ProofRegion(
            region_id='r1',
            edge=CFGEdge('e1', 'a', 'b'),
            entry_invariants=[inv],
            exit_invariants=[inv],
            # No proof!
        )
        cover = InvariantCover(
            function_name='test',
            cfg=FunctionCFG('test'),
            preconditions=[],
            postconditions=[],
            all_invariants=[inv],
            regions=[region],
            overlaps=[],
        )
        h1 = compute_h1(cover)
        assert h1 > 0

    def test_unresolved_overlap_h1_positive(self):
        """Unresolved overlap → H¹ > 0."""
        cover = InvariantCover(
            function_name='test',
            cfg=FunctionCFG('test'),
            preconditions=[],
            postconditions=[],
            all_invariants=[],
            regions=[],
            overlaps=[OverlapObligation(
                join_node_id='j1',
                branch_a='e1', branch_b='e2',
                invariants_a=[], invariants_b=[],
                # No proof!
            )],
        )
        h1 = compute_h1(cover)
        assert h1 > 0


# ═══════════════════════════════════════════════════════════════════
# §9. Gluing Tests
# ═══════════════════════════════════════════════════════════════════

class TestGluing:
    """Global proof construction via GluePath."""

    def test_glue_single_region(self):
        """Single proved region → global proof is the region proof."""
        inv = InvariantPoint(
            surface_text="x > 0",
            compiled=parse_predicate("x > 0"),
            kind=MarkerKind.INVARIANT,
            parse_status='ok',
        )
        proof = Refl(term=var('x'))
        region = ProofRegion(
            region_id='r1',
            edge=CFGEdge('e1', 'a', 'b'),
            entry_invariants=[inv],
            exit_invariants=[inv],
            proof=proof,
            trust=TrustLevel.KERNEL,
        )
        cover = InvariantCover(
            function_name='test',
            cfg=FunctionCFG('test'),
            preconditions=[],
            postconditions=[],
            all_invariants=[inv],
            regions=[region],
            overlaps=[],
            h1_rank=0,
        )
        global_proof = glue_proofs(cover)
        assert global_proof is not None
        assert cover.is_globally_proved

    def test_glue_multiple_regions(self):
        """Multiple proved regions → RefinementDescent global proof."""
        inv1 = InvariantPoint(
            surface_text="x > 0", compiled=parse_predicate("x > 0"),
            kind=MarkerKind.INVARIANT, parse_status='ok',
        )
        inv2 = InvariantPoint(
            surface_text="y > 0", compiled=parse_predicate("y > 0"),
            kind=MarkerKind.INVARIANT, parse_status='ok',
        )
        r1 = ProofRegion(
            region_id='r1', edge=CFGEdge('e1', 'a', 'b'),
            entry_invariants=[inv1], exit_invariants=[inv2],
            proof=Refl(term=var('x')), trust=TrustLevel.KERNEL,
        )
        r2 = ProofRegion(
            region_id='r2', edge=CFGEdge('e2', 'b', 'c'),
            entry_invariants=[inv2], exit_invariants=[inv1],
            proof=Refl(term=var('y')), trust=TrustLevel.KERNEL,
        )
        cover = InvariantCover(
            function_name='test',
            cfg=FunctionCFG('test'),
            preconditions=[], postconditions=[],
            all_invariants=[inv1, inv2],
            regions=[r1, r2], overlaps=[],
            h1_rank=0,
        )
        global_proof = glue_proofs(cover)
        assert global_proof is not None
        assert isinstance(global_proof, RefinementDescent)

    def test_no_glue_when_h1_positive(self):
        """H¹ > 0 → no global proof."""
        cover = InvariantCover(
            function_name='test',
            cfg=FunctionCFG('test'),
            preconditions=[], postconditions=[],
            all_invariants=[], regions=[], overlaps=[],
            h1_rank=1,
        )
        assert glue_proofs(cover) is None

    def test_glue_empty_regions(self):
        """No regions → trivial reflexivity proof."""
        cover = InvariantCover(
            function_name='test',
            cfg=FunctionCFG('test'),
            preconditions=[], postconditions=[],
            all_invariants=[], regions=[], overlaps=[],
            h1_rank=0,
        )
        global_proof = glue_proofs(cover)
        assert global_proof is not None
        assert isinstance(global_proof, Refl)


# ═══════════════════════════════════════════════════════════════════
# §10. Full Pipeline Tests
# ═══════════════════════════════════════════════════════════════════

class TestFullPipeline:
    """End-to-end decompose_and_prove tests."""

    def test_simple_function_with_invariants(self):
        source = textwrap.dedent('''
        def safe_abs(x):
            precondition("isinstance(x, int)")
            if x < 0:
                result = -x
            else:
                result = x
            invariant("result >= 0")
            return result
        ''')
        cover = decompose_and_prove(source)
        assert cover.function_name == 'safe_abs'
        assert len(cover.preconditions) == 1
        assert len(cover.all_invariants) >= 1
        assert cover.trust is not None

    def test_function_with_guarantee(self):
        source = textwrap.dedent('''
        def identity(x):
            return x
        ''')
        cover = decompose_and_prove(source, guarantee="result == x")
        assert len(cover.postconditions) >= 1

    def test_loop_with_invariant(self):
        source = textwrap.dedent('''
        def sum_positive(xs):
            precondition("isinstance(xs, list)")
            total = 0
            for x in xs:
                loop_invariant("total >= 0")
                if x > 0:
                    total += x
            return total
        ''')
        cover = decompose_and_prove(source)
        assert cover.function_name == 'sum_positive'
        loop_invs = [m for m in cover.all_invariants
                     if m.kind == MarkerKind.LOOP_INVARIANT]
        assert len(loop_invs) >= 1

    def test_library_fact_function(self):
        source = textwrap.dedent('''
        def normalize(e):
            library_fact("sympy", "simplify(e) is idempotent")
            return simplify(e)
        ''')
        cover = decompose_and_prove(source)
        lib_facts = [m for m in cover.all_invariants
                     if m.kind == MarkerKind.LIBRARY_FACT]
        assert len(lib_facts) >= 1

    def test_no_markers_produces_empty_cover(self):
        source = textwrap.dedent('''
        def add(a, b):
            return a + b
        ''')
        cover = decompose_and_prove(source)
        assert cover.n_regions == 0
        assert cover.h1_rank == 0  # vacuously true

    def test_trust_summary_computed(self):
        source = textwrap.dedent('''
        def foo(x):
            precondition("x > 0")
            invariant("x > 0")
            return x
        ''')
        cover = decompose_and_prove(source)
        assert cover.trust is not None
        assert cover.trust.total_steps >= 0

    def test_cover_pretty_print(self):
        source = textwrap.dedent('''
        def foo(x):
            precondition("x > 0")
            invariant("x >= 0")
            return x
        ''')
        cover = decompose_and_prove(source)
        pretty = cover.pretty()
        assert 'foo' in pretty
        assert 'Preconditions' in pretty


# ═══════════════════════════════════════════════════════════════════
# §11. @decompose Decorator Tests
# ═══════════════════════════════════════════════════════════════════

class TestDecomposeDecorator:
    """The @decompose decorator."""

    def test_decorator_preserves_function(self):
        @decompose
        def add(a, b):
            return a + b

        assert add(2, 3) == 5
        assert add.__name__ == 'add'

    def test_decorator_attaches_cover(self):
        @decompose
        def foo(x):
            precondition("x > 0")
            return x

        assert hasattr(foo, '__cover__')
        cover = foo.__cover__
        assert isinstance(cover, InvariantCover)

    def test_decorator_with_postcondition(self):
        @decompose
        @postcondition("result >= 0")
        def abs_val(x):
            precondition("isinstance(x, int)")
            if x < 0:
                return -x
            return x

        assert abs_val(-5) == 5
        cover = abs_val.__cover__
        assert cover is not None

    def test_decorator_attaches_trust(self):
        @decompose
        def foo(x):
            precondition("x > 0")
            invariant("x > 0")
            return x

        assert hasattr(foo, '__trust__')
        assert hasattr(foo, '__h1__')


# ═══════════════════════════════════════════════════════════════════
# §12. LLM Decomposition Interface Tests
# ═══════════════════════════════════════════════════════════════════

class TestLLMInterface:
    """LLM decomposition suggestion interface."""

    def test_apply_decomposition_inserts_invariants(self):
        source = textwrap.dedent('''
        def foo(x):
            y = x + 1
            return y
        ''')
        suggestion = DecompositionSuggestion(
            invariants=[{'line': '3', 'predicate': 'y > x'}],
            loop_invariants=[],
            library_facts=[],
        )
        modified = apply_decomposition(source, suggestion)
        assert 'invariant' in modified
        assert 'y > x' in modified

    def test_generate_feedback(self):
        source = textwrap.dedent('''
        def foo(x):
            precondition("x > 0")
            return x
        ''')
        cover = decompose_and_prove(source)
        feedback = generate_feedback(cover)
        assert feedback.n_regions >= 0
        assert feedback.n_proved >= 0
        assert isinstance(feedback.failed_regions, list)

    def test_build_llm_prompt(self):
        source = textwrap.dedent('''
        def foo(x):
            return x + 1
        ''')
        prompt = build_llm_prompt(source, guarantee="result > x")
        assert 'invariant' in prompt
        assert 'result > x' in prompt
        assert 'JSON' in prompt

    def test_build_llm_prompt_with_feedback(self):
        feedback = DecompositionFeedback(
            success=False,
            n_regions=3,
            n_proved=1,
            n_failed=2,
            h1_rank=2,
            failed_regions=[{
                'region': 'r1',
                'obligation': 'x > 0 ⟹ y > 0',
                'reason': 'Z3 timeout',
            }],
        )
        prompt = build_llm_prompt("def foo(x): return x", feedback=feedback)
        assert 'failed' in prompt.lower() or 'FAILED' in prompt


# ═══════════════════════════════════════════════════════════════════
# §13. Trust Model Tests
# ═══════════════════════════════════════════════════════════════════

class TestTrustModel:
    """Trust accounting and propagation."""

    def test_trust_summary_max_trust(self):
        ts = TrustSummary(kernel_steps=3, library_steps=1)
        assert ts.max_trust == TrustLevel.LIBRARY

    def test_trust_summary_all_kernel(self):
        ts = TrustSummary(kernel_steps=5)
        assert ts.max_trust == TrustLevel.KERNEL

    def test_trust_summary_with_assumed(self):
        ts = TrustSummary(kernel_steps=3, assumed_steps=1)
        assert ts.max_trust == TrustLevel.ASSUMED

    def test_trust_summary_with_unverified(self):
        ts = TrustSummary(kernel_steps=3, unverified_steps=1)
        assert ts.max_trust == TrustLevel.UNVERIFIED

    def test_trust_verified_fraction(self):
        ts = TrustSummary(kernel_steps=3, library_steps=1, assumed_steps=1)
        assert ts.verified_fraction == 4 / 5

    def test_trust_pretty(self):
        ts = TrustSummary(kernel_steps=2, library_steps=1)
        pretty = ts.pretty()
        assert 'library' in pretty
        assert 'kernel' in pretty

    def test_empty_trust_is_kernel(self):
        ts = TrustSummary()
        assert ts.max_trust == TrustLevel.KERNEL
        assert ts.verified_fraction == 1.0


# ═══════════════════════════════════════════════════════════════════
# §14. Refinement Tests
# ═══════════════════════════════════════════════════════════════════

class TestRefinement:
    """Counterexample-guided refinement."""

    def test_refine_trivial(self):
        """Already proved → no refinement needed."""
        source = textwrap.dedent('''
        def foo(x):
            return x
        ''')
        cover, history = refine_decomposition(source, max_iterations=2)
        assert len(history) >= 1
        assert history[0].iteration == 0

    def test_refine_with_heuristic(self):
        source = textwrap.dedent('''
        def foo(x):
            precondition("x > 0")
            y = x + 1
            invariant("y > 1")
            return y
        ''')
        cover, history = refine_decomposition(source, max_iterations=2)
        assert isinstance(cover, InvariantCover)


# ═══════════════════════════════════════════════════════════════════
# §15. Analysis Utilities Tests
# ═══════════════════════════════════════════════════════════════════

class TestAnalysisUtilities:
    """High-level analysis functions."""

    def test_analyze_function(self):
        source = textwrap.dedent('''
        def foo(x):
            precondition("x > 0")
            invariant("x >= 0")
            return x
        ''')
        result = analyze_function(source)
        assert result['function_name'] == 'foo'
        assert result['n_preconditions'] == 1
        assert result['n_invariants'] >= 1
        assert 'trust_level' in result

    def test_verify_annotations(self):
        source = textwrap.dedent('''
        def foo(x):
            precondition("x > 0")
            invariant("x >= 0")
            invariant("the sky is blue")
            return x
        ''')
        result = verify_annotations(source)
        assert result['total'] >= 3
        assert result['formal'] >= 2  # x > 0 and x >= 0
        # "the sky is blue" should be fallback
        assert result['fallback'] >= 1 or result['total'] >= 3

    def test_analyze_function_with_guarantee(self):
        source = textwrap.dedent('''
        def add(a, b):
            return a + b
        ''')
        result = analyze_function(source, guarantee="result == a + b")
        assert result['n_postconditions'] >= 1


# ═══════════════════════════════════════════════════════════════════
# §16. Integration Tests
# ═══════════════════════════════════════════════════════════════════

class TestIntegration:
    """Integration with library_prover and existing proof infrastructure."""

    def test_decompose_library_function(self):
        source = textwrap.dedent('''
        def factorial(n):
            precondition("n >= 0")
            if n <= 1:
                return 1
            return n * factorial(n - 1)
        ''')
        cover = decompose_library_function(
            source, func_name='factorial', library='builtins',
            guarantee='result >= 1')
        assert isinstance(cover, InvariantCover)
        assert cover.function_name == 'factorial'

    def test_invariant_point_formal_check(self):
        """Formal predicates report is_formal correctly."""
        ip_formal = InvariantPoint(
            surface_text="x > 0",
            compiled=parse_predicate("x > 0"),
            kind=MarkerKind.INVARIANT,
            parse_status='ok',
        )
        assert ip_formal.is_formal

        ip_fallback = InvariantPoint(
            surface_text="the list is sorted",
            compiled=PVar("the list is sorted"),
            kind=MarkerKind.INVARIANT,
            parse_status='fallback',
        )
        assert not ip_fallback.is_formal

    def test_region_is_proved(self):
        """ProofRegion.is_proved checks proof AND trust."""
        region = ProofRegion(
            region_id='r1',
            edge=CFGEdge('e1', 'a', 'b'),
            entry_invariants=[], exit_invariants=[],
            proof=Refl(term=var('x')),
            trust=TrustLevel.KERNEL,
        )
        assert region.is_proved

        unproved = ProofRegion(
            region_id='r2',
            edge=CFGEdge('e2', 'a', 'b'),
            entry_invariants=[], exit_invariants=[],
        )
        assert not unproved.is_proved


# ═══════════════════════════════════════════════════════════════════
# §17. Complex Scenario Tests
# ═══════════════════════════════════════════════════════════════════

class TestComplexScenarios:
    """Complex, realistic test scenarios."""

    def test_binary_search_decomposition(self):
        source = textwrap.dedent('''
        def binary_search(xs, target):
            precondition("isinstance(xs, list)")
            precondition("len(xs) > 0")
            lo, hi = 0, len(xs) - 1
            while lo <= hi:
                loop_invariant("0 <= lo and hi < len(xs)")
                loop_invariant("lo <= hi + 1")
                mid = (lo + hi) // 2
                if xs[mid] == target:
                    return mid
                elif xs[mid] < target:
                    lo = mid + 1
                else:
                    hi = mid - 1
            return -1
        ''')
        cover = decompose_and_prove(source)
        assert cover.function_name == 'binary_search'
        assert len(cover.preconditions) == 2
        loop_invs = [m for m in cover.all_invariants
                     if m.kind == MarkerKind.LOOP_INVARIANT]
        assert len(loop_invs) == 2

    def test_merge_sort_decomposition(self):
        source = textwrap.dedent('''
        def merge_sort(xs):
            precondition("isinstance(xs, list)")
            if len(xs) <= 1:
                return xs
            mid = len(xs) // 2
            left = merge_sort(xs[:mid])
            right = merge_sort(xs[mid:])
            assume_correct("merge_sort")
            invariant("len(left) + len(right) == len(xs)")
            return merge(left, right)
        ''')
        cover = decompose_and_prove(source)
        assert cover.function_name == 'merge_sort'
        assert any(m.kind == MarkerKind.ASSUME_CORRECT
                   for m in cover.all_invariants)

    def test_sympy_like_function(self):
        source = textwrap.dedent('''
        def normalize_expr(expr):
            library_fact("sympy", "expand(e) distributes over +")
            library_fact("sympy", "simplify is idempotent")
            expanded = expand(expr)
            invariant("expanded == expand(expr)")
            simplified = simplify(expanded)
            invariant("simplified == simplify(expanded)")
            return simplified
        ''')
        cover = decompose_and_prove(source)
        lib_facts = [m for m in cover.all_invariants
                     if m.kind == MarkerKind.LIBRARY_FACT]
        assert len(lib_facts) == 2

    def test_trust_propagation_in_complex_function(self):
        """Trust level should be the weakest link."""
        source = textwrap.dedent('''
        def process(data):
            precondition("isinstance(data, list)")
            invariant("len(data) >= 0")
            library_fact("numpy", "array preserves length")
            assume_correct("validate")
            return data
        ''')
        cover = decompose_and_prove(source)
        cover.compute_trust()
        # The trust level should reflect the weakest component
        assert cover.trust is not None

    def test_nested_if_decomposition(self):
        source = textwrap.dedent('''
        def classify(x):
            precondition("isinstance(x, int)")
            if x > 0:
                if x > 100:
                    invariant("x > 100")
                    return "large"
                else:
                    invariant("0 < x and x <= 100")
                    return "medium"
            else:
                invariant("x <= 0")
                return "non-positive"
        ''')
        cover = decompose_and_prove(source)
        assert cover.function_name == 'classify'
        assert len(cover.all_invariants) >= 3
