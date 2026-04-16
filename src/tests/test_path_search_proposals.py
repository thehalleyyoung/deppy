"""Tests for path_search proposals (g08) wired into CCTT.

Covers all 14 proposals plus the integrated pipeline.
"""
from __future__ import annotations

import pytest
from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)
from cctt.path_search import (
    # Original exports
    PathStep, PathResult, FiberCtx,
    _ROOT_AXIOMS, _ALL_AXIOMS, _all_rewrites, _identify_spec, search_path, hit_path_equiv,
    # Proposal 1
    StructuredPathStep, PathCertificate,
    # Proposal 2
    extract_symbols, AXIOM_SYMBOL_TABLE, relevant_axioms, filtered_rewrites,
    # Proposal 3
    identify_spec_extended,
    # Proposal 4
    _edit_distance_heuristic, astar_search,
    # Proposal 5
    FiberProperty, FIBER_PROPERTY_TABLE, FiberValidator,
    # Proposal 6
    verify_certificate, verify_certificate_deep,
    # Proposal 7
    PathSearchMetrics, instrumented_search,
    # Proposal 8
    AxiomNode, AxiomDependencyGraph, build_default_axiom_graph,
    # Proposal 9
    EnumeratedPath, enumerate_paths_dfs, count_reachable,
    # Proposal 10
    AxiomMorphism, TensorProduct, AxiomCategory,
    # Proposal 11
    spec_gcd, spec_lcm, spec_prime_sieve, spec_matrix_mul,
    spec_tree_traversal, spec_dot_product, spec_power, spec_fibonacci,
    SPEC_REGISTRY, register_spec, identify_spec_registry,
    # Proposal 12
    CongruenceClosure,
    # Proposal 13
    ProofWitness, ProofRelevantStep, ProofRelevantPath, proof_relevant_search,
    # Proposal 14
    FailedPair, SynthesisedAxiom, AxiomSynthesiser,
    # Pipeline
    full_pipeline_search,
)


# ── Shared fixtures ──

@pytest.fixture
def ctx_num():
    return FiberCtx(param_duck_types={'p0': 'int', 'p1': 'int'})


@pytest.fixture
def ctx_str():
    return FiberCtx(param_duck_types={'p0': 'str', 'p1': 'str'})


@pytest.fixture
def add_p0_p1():
    return OOp('add', (OVar('p0'), OVar('p1')))


@pytest.fixture
def add_p1_p0():
    return OOp('add', (OVar('p1'), OVar('p0')))


# ═══════════════════════════════════════════════════════════
# Proposal 1: StructuredPathStep / PathCertificate
# ═══════════════════════════════════════════════════════════

class TestStructuredPathStep:
    def test_to_base(self):
        step = StructuredPathStep(
            axiom='ALG_commute', position=(),
            before=OOp('add', (OVar('p0'), OVar('p1'))),
            after=OOp('add', (OVar('p1'), OVar('p0'))),
        )
        base = step.to_base()
        assert isinstance(base, PathStep)
        assert base.axiom == 'ALG_commute'
        assert base.position == 'root'

    def test_verify(self, ctx_num):
        step = StructuredPathStep(
            axiom='ALG_commute', position=(),
            before=OOp('add', (OVar('p0'), OVar('p1'))),
            after=OOp('add', (OVar('p1'), OVar('p0'))),
        )
        assert step.verify(ctx_num) is True


class TestPathCertificate:
    def test_chain_connected(self):
        src = OOp('add', (OVar('p0'), OVar('p1')))
        tgt = OOp('add', (OVar('p1'), OVar('p0')))
        step = StructuredPathStep(
            axiom='ALG_commute', position=(), before=src, after=tgt,
        )
        cert = PathCertificate(steps=[step], source=src, target=tgt)
        assert cert.is_chain_connected()
        assert len(cert) == 1

    def test_empty_refl(self):
        t = OVar('x')
        cert = PathCertificate(steps=[], source=t, target=t)
        assert cert.is_chain_connected()

    def test_to_path_result(self):
        src = OOp('add', (OVar('p0'), OVar('p1')))
        tgt = OOp('add', (OVar('p1'), OVar('p0')))
        step = StructuredPathStep(
            axiom='ALG_commute', position=(), before=src, after=tgt,
        )
        cert = PathCertificate(steps=[step], source=src, target=tgt)
        pr = cert.to_path_result()
        assert pr.found is True
        assert len(pr.path) == 1

    def test_from_path_result(self):
        ps = PathStep('ALG_commute', 'root', 'add($p0,$p1)', 'add($p1,$p0)')
        pr = PathResult(found=True, path=[ps])
        cert = PathCertificate.from_path_result(
            pr,
            OOp('add', (OVar('p0'), OVar('p1'))),
            OOp('add', (OVar('p1'), OVar('p0'))),
        )
        assert len(cert) == 1


# ═══════════════════════════════════════════════════════════
# Proposal 2: Axiom Relevance Filtering
# ═══════════════════════════════════════════════════════════

class TestAxiomRelevanceFiltering:
    def test_extract_symbols_basic(self):
        t = OOp('add', (OVar('p0'), OLit(1)))
        syms = extract_symbols(t)
        assert 'add' in syms

    def test_extract_symbols_fold(self):
        t = OFold('.mul', OLit(1), OOp('range', (OVar('n'),)))
        syms = extract_symbols(t)
        assert '.mul' in syms
        assert 'OFold' in syms
        assert 'range' in syms

    def test_extract_symbols_var_lit(self):
        assert extract_symbols(OVar('x')) == set()
        assert extract_symbols(OLit(42)) == set()

    def test_relevant_axioms_returns_subset(self, ctx_num, add_p0_p1):
        rel = relevant_axioms(add_p0_p1, ctx_num)
        assert len(rel) <= len(_ALL_AXIOMS)
        assert len(rel) > 0

    def test_filtered_rewrites_produces_results(self, ctx_num, add_p0_p1):
        results = filtered_rewrites(add_p0_p1, ctx_num)
        assert len(results) > 0


# ═══════════════════════════════════════════════════════════
# Proposal 3: Extended Spec Identification
# ═══════════════════════════════════════════════════════════

class TestExtendedSpecId:
    def test_max_op(self):
        t = OOp('max', (OVar('xs'),))
        spec = identify_spec_extended(t)
        assert spec is not None
        assert spec[0] == 'max'

    def test_min_fold(self):
        t = OFold('min', OLit(float('inf')), OVar('xs'))
        spec = identify_spec_extended(t)
        assert spec is not None
        assert spec[0] == 'min'

    def test_reversed(self):
        t = OOp('reversed', (OVar('xs'),))
        spec = identify_spec_extended(t)
        assert spec is not None
        assert spec[0] == 'reverse'

    def test_flatten(self):
        t = OFold('concat', OSeq(()), OVar('nested'))
        spec = identify_spec_extended(t)
        assert spec is not None
        assert spec[0] == 'flatten'

    def test_all_op(self):
        t = OOp('all', (OVar('xs'),))
        spec = identify_spec_extended(t)
        assert spec is not None
        assert spec[0] == 'all'

    def test_any_fold(self):
        t = OFold('or', OLit(False), OVar('xs'))
        spec = identify_spec_extended(t)
        assert spec is not None
        assert spec[0] == 'any'

    def test_len_op(self):
        t = OOp('len', (OVar('xs'),))
        spec = identify_spec_extended(t)
        assert spec is not None
        assert spec[0] == 'len'

    def test_product_fold(self):
        t = OFold('.mul', OLit(1), OVar('xs'))
        spec = identify_spec_extended(t)
        assert spec is not None
        assert spec[0] == 'product'

    def test_delegates_to_base(self):
        # factorial — already handled by _identify_spec
        t = OFold('.mul', OLit(1), OOp('range', (OVar('n'),)))
        spec = identify_spec_extended(t)
        assert spec is not None
        assert spec[0] == 'factorial'


# ═══════════════════════════════════════════════════════════
# Proposal 4: A* Search
# ═══════════════════════════════════════════════════════════

class TestAStarSearch:
    def test_finds_commutative_path(self, ctx_num, add_p0_p1, add_p1_p0):
        r = astar_search(add_p0_p1, add_p1_p0, ctx_num, max_depth=3)
        assert r.found is True

    def test_refl(self, ctx_num, add_p0_p1):
        r = astar_search(add_p0_p1, add_p0_p1, ctx_num)
        assert r.found is True
        assert r.reason == 'refl'
        assert len(r.path) == 0

    def test_edit_distance_identical(self):
        assert _edit_distance_heuristic('abc', 'abc') == 0

    def test_edit_distance_different(self):
        assert _edit_distance_heuristic('abc', 'xyz') >= 0


# ═══════════════════════════════════════════════════════════
# Proposal 5: Fiber Validation
# ═══════════════════════════════════════════════════════════

class TestFiberValidation:
    def test_add_commutative_on_int(self, ctx_num, add_p0_p1):
        v = FiberValidator(ctx_num)
        assert v.has_property(add_p0_p1, 'add', FiberProperty.COMMUTATIVE)

    def test_add_not_commutative_on_str(self, ctx_str):
        t = OOp('add', (OVar('p0'), OVar('p1')))
        v = FiberValidator(ctx_str)
        assert not v.has_property(t, 'add', FiberProperty.COMMUTATIVE)

    def test_mul_always_commutative(self, ctx_num, add_p0_p1):
        v = FiberValidator(ctx_num)
        assert v.has_property(add_p0_p1, 'mul', FiberProperty.COMMUTATIVE)

    def test_audit_step(self, ctx_num):
        v = FiberValidator(ctx_num)
        step = PathStep('ALG_commute', 'root', 'add($p0,$p1)', 'add($p1,$p0)')
        warnings = v.audit_step(step)
        assert isinstance(warnings, list)


# ═══════════════════════════════════════════════════════════
# Proposal 6: Certificate Verification
# ═══════════════════════════════════════════════════════════

class TestCertificateVerification:
    def test_valid_certificate(self):
        steps = [PathStep('ALG_commute', 'root', 'add($p0,$p1)', 'add($p1,$p0)')]
        ok, errs = verify_certificate(steps)
        assert ok
        assert len(errs) == 0

    def test_broken_chain(self):
        steps = [
            PathStep('ALG_commute', 'root', 'add($p0,$p1)', 'add($p1,$p0)'),
            PathStep('ALG_commute', 'root', 'WRONG_CANON', 'add($p0,$p1)'),
        ]
        ok, errs = verify_certificate(steps)
        assert not ok
        assert len(errs) > 0

    def test_deep_verification(self, add_p0_p1, add_p1_p0):
        steps = [PathStep('ALG_commute', 'root',
                          add_p0_p1.canon(), add_p1_p0.canon())]
        ok, errs = verify_certificate_deep(steps, add_p0_p1, add_p1_p0)
        assert ok


# ═══════════════════════════════════════════════════════════
# Proposal 7: Metrics
# ═══════════════════════════════════════════════════════════

class TestPathSearchMetrics:
    def test_record_axiom_use(self):
        m = PathSearchMetrics()
        m.record_axiom_use('ALG_commute')
        assert m.axiom_histogram == {'ALG_commute': 1}

    def test_record_congruence(self):
        m = PathSearchMetrics()
        m.record_axiom_use('ALG_commute@arg0')
        assert 'ALG_commute' in m.axiom_histogram
        assert 'ALG_commute@arg0' in m.congruences_used

    def test_instrumented_search(self, add_p0_p1, add_p1_p0):
        r, m = instrumented_search(
            add_p0_p1, add_p1_p0,
            param_duck_types={'p0': 'int', 'p1': 'int'},
        )
        assert r.found is True
        assert m.strategy_used != ''
        assert m.time_ms >= 0
        assert len(m.summary()) > 0

    def test_to_dict(self):
        m = PathSearchMetrics(strategy_used='C_bfs', time_ms=1.5)
        d = m.to_dict()
        assert d['strategy'] == 'C_bfs'
        assert d['time_ms'] == 1.5


# ═══════════════════════════════════════════════════════════
# Proposal 8: Axiom Dependency Graph
# ═══════════════════════════════════════════════════════════

class TestAxiomDependencyGraph:
    def test_default_graph_has_16_nodes(self):
        g = build_default_axiom_graph()
        assert len(g.nodes) == 16

    def test_d1_enables_some_axioms(self):
        g = build_default_axiom_graph()
        deps = g.get_dependents('D1_fold_unfold')
        assert len(deps) > 0

    def test_topological_order(self):
        g = build_default_axiom_graph()
        order = g.topological_order()
        assert len(order) == 16

    def test_custom_graph(self):
        g = AxiomDependencyGraph()
        g.add_axiom('A', creates={'x'}, requires={'y'})
        g.add_axiom('B', creates={'y'}, requires={'z'})
        assert g.get_dependents('B') == ['A']
        assert g.get_dependencies('A') == ['B']


# ═══════════════════════════════════════════════════════════
# Proposal 9: DFS Path Enumeration
# ═══════════════════════════════════════════════════════════

class TestDFSEnumeration:
    def test_enumerate_finds_paths(self):
        t = OOp('add', (OOp('add', (OVar('a'), OVar('b'))), OVar('c')))
        ctx = FiberCtx(param_duck_types={'a': 'int', 'b': 'int', 'c': 'int'})
        paths = enumerate_paths_dfs(t, None, ctx, max_depth=1, max_paths=50)
        assert len(paths) >= 1

    def test_count_reachable(self):
        t = OOp('add', (OOp('add', (OVar('a'), OVar('b'))), OVar('c')))
        ctx = FiberCtx(param_duck_types={'a': 'int', 'b': 'int', 'c': 'int'})
        counts = count_reachable(t, ctx, max_depth=1)
        assert counts[0] == 1
        assert 1 in counts


# ═══════════════════════════════════════════════════════════
# Proposal 10: Axiom Category
# ═══════════════════════════════════════════════════════════

class TestAxiomCategory:
    def test_identity(self):
        cat = AxiomCategory()
        m = cat.identity('add($p0,$p1)')
        assert m.source == m.target

    def test_compose_involution(self):
        cat = AxiomCategory()
        m1 = AxiomMorphism('ALG_commute', 'add($p0,$p1)', 'add($p1,$p0)')
        m2 = AxiomMorphism('ALG_commute', 'add($p1,$p0)', 'add($p0,$p1)')
        composed = cat.compose(m1, m2)
        assert composed is not None
        assert composed.source == composed.target

    def test_tensor_product(self):
        m1 = AxiomMorphism('ALG_commute', 'add($p0,$p1)', 'add($p1,$p0)')
        m2 = AxiomMorphism('ALG_commute', 'add($p1,$p0)', 'add($p0,$p1)')
        cat = AxiomCategory()
        tp = cat.tensor(m1, m2)
        assert '\u2297' in tp.source

    def test_symmetry(self):
        m1 = AxiomMorphism('A', 'x', 'y')
        m2 = AxiomMorphism('B', 'u', 'v')
        cat = AxiomCategory()
        tp = cat.tensor(m1, m2)
        sym = cat.symmetry(tp)
        assert sym.left == tp.right
        assert sym.right == tp.left


# ═══════════════════════════════════════════════════════════
# Proposal 11: Extended Spec Library
# ═══════════════════════════════════════════════════════════

class TestExtendedSpecLibrary:
    def test_spec_gcd(self):
        t = spec_gcd(OVar('a'), OVar('b'))
        assert isinstance(t, OAbstract)
        assert t.spec == 'gcd'

    def test_spec_lcm_canon(self):
        assert spec_lcm(OVar('a'), OVar('b')).canon() == '@lcm($a,$b)'

    def test_spec_fibonacci_canon(self):
        assert spec_fibonacci(OVar('n')).canon() == '@fibonacci($n)'

    def test_spec_power(self):
        t = spec_power(OVar('b'), OVar('e'))
        assert t.spec == 'power'

    def test_spec_prime_sieve(self):
        t = spec_prime_sieve(OVar('n'))
        assert t.spec == 'prime_sieve'

    def test_spec_matrix_mul(self):
        t = spec_matrix_mul(OVar('A'), OVar('B'))
        assert t.canon() == '@matmul($A,$B)'

    def test_spec_dot_product(self):
        t = spec_dot_product(OVar('a'), OVar('b'))
        assert t.spec == 'dot_product'

    def test_spec_tree_traversal(self):
        t = spec_tree_traversal(OVar('root'), 'preorder')
        assert t.spec == 'tree_preorder'

    def test_registry_recognises_gcd(self):
        t = OOp('gcd', (OVar('a'), OVar('b')))
        spec = identify_spec_registry(t)
        assert spec is not None
        assert spec[0] == 'gcd'

    def test_registry_recognises_power(self):
        t = OOp('pow', (OVar('b'), OVar('e')))
        spec = identify_spec_registry(t)
        assert spec is not None
        assert spec[0] == 'power'


# ═══════════════════════════════════════════════════════════
# Proposal 12: Congruence Closure
# ═══════════════════════════════════════════════════════════

class TestCongruenceClosure:
    def test_commutative_terms(self, ctx_num, add_p0_p1, add_p1_p0):
        cc = CongruenceClosure(ctx_num)
        cc.add_term(add_p0_p1, depth=1)
        cc.add_term(add_p1_p0, depth=1)
        assert cc.are_equal(add_p0_p1, add_p1_p0)

    def test_class_count(self, ctx_num, add_p0_p1):
        cc = CongruenceClosure(ctx_num)
        cc.add_term(add_p0_p1, depth=1)
        assert cc.class_count() >= 1

    def test_equivalence_class(self, ctx_num, add_p0_p1):
        cc = CongruenceClosure(ctx_num)
        cc.add_term(add_p0_p1, depth=1)
        eq_class = cc.equivalence_class(add_p0_p1)
        assert len(eq_class) >= 1


# ═══════════════════════════════════════════════════════════
# Proposal 13: Proof-Relevant Search
# ═══════════════════════════════════════════════════════════

class TestProofRelevantSearch:
    def test_finds_path(self, ctx_num, add_p0_p1, add_p1_p0):
        pr = proof_relevant_search(add_p0_p1, add_p1_p0, ctx_num)
        assert pr is not None

    def test_path_is_valid(self, ctx_num, add_p0_p1, add_p1_p0):
        pr = proof_relevant_search(add_p0_p1, add_p1_p0, ctx_num)
        assert pr is not None
        assert pr.is_valid

    def test_to_latex(self, ctx_num, add_p0_p1, add_p1_p0):
        pr = proof_relevant_search(add_p0_p1, add_p1_p0, ctx_num)
        assert pr is not None
        latex = pr.to_latex()
        assert 'align*' in latex

    def test_step_justify(self):
        step = ProofRelevantStep(
            axiom='ALG_commute',
            witness=ProofWitness.AXIOM_APPLICATION,
            before=OUnknown('add($p0,$p1)'),
            after=OUnknown('add($p1,$p0)'),
            position=(),
        )
        j = step.justify()
        assert 'AXIOM_APPLICATION' in j


# ═══════════════════════════════════════════════════════════
# Proposal 14: Axiom Synthesis
# ═══════════════════════════════════════════════════════════

class TestAxiomSynthesis:
    def test_record_failure(self):
        synth = AxiomSynthesiser()
        synth.record_failure(
            OOp('custom_op', (OVar('x'),)),
            OOp('other_op', (OVar('x'),)),
            'no path',
        )
        assert len(synth.failures) == 1

    def test_cluster_by_structure(self):
        synth = AxiomSynthesiser()
        synth.record_failure(
            OOp('a', (OVar('x'),)),
            OOp('b', (OVar('x'),)),
            'no path',
        )
        clusters = synth.cluster_by_structure()
        assert len(clusters) == 1

    def test_synthesise(self):
        synth = AxiomSynthesiser()
        synth.record_failure(
            OOp('custom', (OVar('x'),)),
            OOp('other', (OVar('x'),)),
            'no path',
        )
        candidates = synth.synthesise()
        assert len(candidates) >= 1

    def test_report(self):
        synth = AxiomSynthesiser()
        synth.record_failure(
            OOp('a', (OVar('x'),)),
            OOp('b', (OVar('x'),)),
            'fail',
        )
        report = synth.report()
        assert 'failure' in report.lower()


# ═══════════════════════════════════════════════════════════
# Integration: Full Pipeline
# ═══════════════════════════════════════════════════════════

class TestFullPipeline:
    def test_pipeline_with_astar(self, add_p0_p1, add_p1_p0):
        r, m = full_pipeline_search(
            add_p0_p1, add_p1_p0,
            param_duck_types={'p0': 'int', 'p1': 'int'},
            use_astar=True,
            collect_metrics=True,
        )
        assert r.found is True
        assert m is not None
        assert m.time_ms >= 0

    def test_pipeline_with_congruence_closure(self, add_p0_p1, add_p1_p0):
        r, m = full_pipeline_search(
            add_p0_p1, add_p1_p0,
            param_duck_types={'p0': 'int', 'p1': 'int'},
            use_congruence_closure=True,
            collect_metrics=True,
        )
        assert r.found is True

    def test_pipeline_refl(self, add_p0_p1):
        r, m = full_pipeline_search(add_p0_p1, add_p0_p1)
        assert r.found is True
        assert r.reason == 'refl'

    def test_pipeline_extended_spec(self):
        t1 = OOp('gcd', (OVar('a'), OVar('b')))
        t2 = OOp('math.gcd', (OVar('a'), OVar('b')))
        r, m = full_pipeline_search(t1, t2)
        assert r.found is True
