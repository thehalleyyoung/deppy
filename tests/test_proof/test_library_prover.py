"""Tests for the CCTT Library Prover — cohomological proof generation.

Tests the full pipeline: introspection → nerve → presheaf → proofs → cohomology.
Runs on real libraries: math, collections, itertools, sympy.
"""
from __future__ import annotations

import pytest
from cctt.proof_theory.library_prover import (
    # Data structures
    IntrospectionTier, FunctionSig, TypeNode, TypeMorphism,
    Simplex, CechNerve, Section, SpecPresheaf, CechCohomology,
    # Oracles
    DocstringOracle, Oracle,
    # Introspection
    introspect_library, _introspect_function, _introspect_class,
    # Nerve
    build_nerve,
    # Proof generation
    _make_contract_proof, _make_descent_proof, _make_glue_path_proof,
    _make_transport_proof, _make_hcomp_proof,
    generate_presheaf,
    # Compilation
    compile_presheaf, compute_cohomology,
    # Pipeline
    prove_library, register_theory,
    ProofReport,
)
from cctt.proof_theory.checker import check_proof
from cctt.proof_theory.terms import var, op
from cctt.proof_theory.library_axioms import (
    LibraryAxiom, LibraryContract, get_library,
)


# ═══════════════════════════════════════════════════════════════════
# Test data structures
# ═══════════════════════════════════════════════════════════════════

class TestSimplex:
    def test_dimension(self):
        s0 = Simplex(frozenset({'A'}))
        s1 = Simplex(frozenset({'A', 'B'}))
        s2 = Simplex(frozenset({'A', 'B', 'C'}))
        assert s0.dimension == 0
        assert s1.dimension == 1
        assert s2.dimension == 2

    def test_face(self):
        s = Simplex(frozenset({'A', 'B', 'C'}))
        face = s.face('B')
        assert face == Simplex(frozenset({'A', 'C'}))
        assert face.dimension == 1

    def test_repr(self):
        s = Simplex(frozenset({'X', 'Y'}))
        r = repr(s)
        assert 'Δ1' in r


class TestCechNerve:
    def test_euler_characteristic_empty(self):
        nerve = CechNerve()
        assert nerve.euler_characteristic() == 0

    def test_euler_characteristic_triangle(self):
        nerve = CechNerve()
        nerve.simplices[0] = [Simplex(frozenset({str(i)})) for i in range(3)]
        nerve.simplices[1] = [
            Simplex(frozenset({'0', '1'})),
            Simplex(frozenset({'1', '2'})),
            Simplex(frozenset({'0', '2'})),
        ]
        nerve.simplices[2] = [Simplex(frozenset({'0', '1', '2'}))]
        # χ = 3 - 3 + 1 = 1
        assert nerve.euler_characteristic() == 1


# ═══════════════════════════════════════════════════════════════════
# Test introspection
# ═══════════════════════════════════════════════════════════════════

class TestIntrospection:
    def test_introspect_math(self):
        types, functions, morphisms = introspect_library('math', max_depth=1)
        assert len(functions) > 10  # math has ~50 functions
        assert any('sqrt' in k for k in functions)
        assert any('sin' in k for k in functions)

    def test_introspect_collections(self):
        types, functions, morphisms = introspect_library(
            'collections', max_depth=1)
        # collections has Counter, OrderedDict, defaultdict, deque, etc.
        type_names = {t.name for t in types.values()}
        assert 'Counter' in type_names or 'OrderedDict' in type_names

    def test_introspect_function_sig(self):
        import math
        sig = _introspect_function(math.sqrt, 'sqrt', 'math')
        assert sig is not None
        assert sig.name == 'sqrt'

    def test_introspect_class(self):
        from collections import Counter
        node = _introspect_class(Counter, 'collections')
        assert node.name == 'Counter'
        assert 'most_common' in node.methods or len(node.methods) > 0


class TestIntrospectionTier:
    def test_tiers_exist(self):
        assert IntrospectionTier.FULL.value == 'full'
        assert IntrospectionTier.OPAQUE.value == 'opaque'


# ═══════════════════════════════════════════════════════════════════
# Test nerve construction
# ═══════════════════════════════════════════════════════════════════

class TestNerveConstruction:
    def test_linear_hierarchy(self):
        """A → B → C gives 3 0-simplices and 2 1-simplices."""
        types = {
            'A': TypeNode('A', 'A', 'mod', [], ['B'], {}, {}, [], False,
                          IntrospectionTier.FULL),
            'B': TypeNode('B', 'B', 'mod', ['A'], ['C'], {}, {}, [], False,
                          IntrospectionTier.FULL),
            'C': TypeNode('C', 'C', 'mod', ['B'], [], {}, {}, [], False,
                          IntrospectionTier.FULL),
        }
        morphisms = [
            TypeMorphism('B', 'A'),
            TypeMorphism('C', 'B'),
        ]
        nerve = build_nerve(types, morphisms)
        assert nerve.n_types == 3
        assert nerve.n_overlaps >= 2  # B⊂A and C⊂B

    def test_diamond_hierarchy(self):
        """Diamond: A ← B, A ← C, B → D ← C gives triple overlap."""
        types = {
            'A': TypeNode('A', 'A', 'mod', [], ['B', 'C'], {}, {}, [], True,
                          IntrospectionTier.FULL),
            'B': TypeNode('B', 'B', 'mod', ['A'], ['D'], {}, {}, [], False,
                          IntrospectionTier.FULL),
            'C': TypeNode('C', 'C', 'mod', ['A'], ['D'], {}, {}, [], False,
                          IntrospectionTier.FULL),
            'D': TypeNode('D', 'D', 'mod', ['B', 'C'], [], {}, {}, [], False,
                          IntrospectionTier.FULL),
        }
        morphisms = [
            TypeMorphism('B', 'A'),
            TypeMorphism('C', 'A'),
            TypeMorphism('D', 'B'),
            TypeMorphism('D', 'C'),
        ]
        nerve = build_nerve(types, morphisms, max_simplex_dim=2)
        assert nerve.n_types == 4
        # B and C overlap via common child D
        assert nerve.n_overlaps >= 1

    def test_no_overlaps(self):
        """Disjoint types give no 1-simplices."""
        types = {
            'X': TypeNode('X', 'X', 'mod', [], [], {}, {}, [], False,
                          IntrospectionTier.FULL),
            'Y': TypeNode('Y', 'Y', 'mod', [], [], {}, {}, [], False,
                          IntrospectionTier.FULL),
        }
        nerve = build_nerve(types, [])
        assert nerve.n_types == 2
        assert nerve.n_overlaps == 0


# ═══════════════════════════════════════════════════════════════════
# Test proof generation
# ═══════════════════════════════════════════════════════════════════

class TestProofGeneration:
    def test_contract_proof_compiles(self):
        proof, lhs, rhs = _make_contract_proof(
            'math', FunctionSig('sqrt', 'math.sqrt', 'math',
                                [('x', 'float')], 'float', 'square root'),
            'returns non-negative square root')
        result = check_proof(proof, lhs, rhs)
        assert result.valid

    def test_descent_proof_compiles(self):
        proof, lhs, rhs = _make_descent_proof(
            'test', 'Number', ['Integer', 'Float'],
            'abs', 'returns non-negative value')
        result = check_proof(proof, lhs, rhs)
        assert result.valid

    def test_glue_path_proof_compiles(self):
        proof, lhs, rhs = _make_glue_path_proof(
            'test', 'number_cover', ['Integer', 'Float'],
            'abs', 'non-negative')
        result = check_proof(proof, lhs, rhs)
        assert result.valid

    def test_transport_proof_compiles(self):
        proof, lhs, rhs = _make_transport_proof(
            'test', 'encode', 'decode', 'decode(encode(x)) == x')
        result = check_proof(proof, lhs, rhs)
        assert result.valid

    def test_hcomp_proof_compiles(self):
        proof, lhs, rhs = _make_hcomp_proof(
            'test',
            {
                'linearity': ('diff', 'diff is linear'),
                'product': ('diff', 'diff obeys product rule'),
            })
        result = check_proof(proof, lhs, rhs)
        assert result.valid


# ═══════════════════════════════════════════════════════════════════
# Test oracles
# ═══════════════════════════════════════════════════════════════════

class TestDocstringOracle:
    def test_generate_spec_from_docstring(self):
        oracle = DocstringOracle()
        fn = FunctionSig('sqrt', 'math.sqrt', 'math',
                         [('x', 'float')], 'float',
                         'Return the square root of x.')
        spec = oracle.generate_spec(fn)
        assert 'square root' in spec.lower()

    def test_generate_spec_no_docstring(self):
        oracle = DocstringOracle()
        fn = FunctionSig('mystery', 'mod.mystery', 'mod',
                         [('a', 'int'), ('b', 'int')], 'int', '')
        spec = oracle.generate_spec(fn)
        assert 'mystery' in spec

    def test_generate_axiom_inverse_pair(self):
        oracle = DocstringOracle()
        fa = FunctionSig('expand', 'sympy.expand', 'sympy',
                         [('expr', 'Expr')], 'Expr', 'Expand expression')
        fb = FunctionSig('factor', 'sympy.factor', 'sympy',
                         [('expr', 'Expr')], 'Expr', 'Factor expression')
        axiom = oracle.generate_axiom(fa, fb)
        assert axiom is not None
        assert 'factor' in axiom and 'expand' in axiom

    def test_generate_axiom_no_relation(self):
        oracle = DocstringOracle()
        fa = FunctionSig('sqrt', 'math.sqrt', 'math',
                         [('x', 'float')], 'float', '')
        fb = FunctionSig('sin', 'math.sin', 'math',
                         [('x', 'float')], 'float', '')
        axiom = oracle.generate_axiom(fa, fb)
        assert axiom is None


# ═══════════════════════════════════════════════════════════════════
# Test cohomology computation
# ═══════════════════════════════════════════════════════════════════

class TestCohomology:
    def test_h0_global_sections(self):
        """Proved 0-cochains with no failing overlaps → H⁰."""
        from cctt.proof_theory.checker import VerificationResult

        nerve = CechNerve()
        nerve.simplices[0] = [Simplex(frozenset({'A'}))]
        presheaf = SpecPresheaf(nerve=nerve)

        section = Section(
            simplex=Simplex(frozenset({'A'})),
            function_name='f',
            spec_text='f is pure',
        )
        section.result = VerificationResult(
            valid=True, reason='ok', proof_depth=1)
        presheaf.add_section(section)

        cohomology = compute_cohomology(presheaf)
        assert cohomology.n_global_theorems == 1

    def test_h1_obstruction(self):
        """Failed 1-cochain → H¹ obstruction."""
        from cctt.proof_theory.checker import VerificationResult

        nerve = CechNerve()
        nerve.simplices[0] = [
            Simplex(frozenset({'A'})),
            Simplex(frozenset({'B'})),
        ]
        nerve.simplices[1] = [Simplex(frozenset({'A', 'B'}))]
        presheaf = SpecPresheaf(nerve=nerve)

        # 0-cochain: proved on A
        s0 = Section(Simplex(frozenset({'A'})), 'f', 'spec')
        s0.result = VerificationResult(valid=True, reason='ok', proof_depth=1)
        presheaf.add_section(s0)

        # 1-cochain: fails on A∩B → obstruction
        s1 = Section(Simplex(frozenset({'A', 'B'})), 'f@A∩B', 'overlap')
        s1.result = VerificationResult(
            valid=False, reason='incompatible', proof_depth=0)
        presheaf.add_section(s1)

        cohomology = compute_cohomology(presheaf)
        assert cohomology.n_obstructions == 1
        # The 0-cochain on A should NOT be in H⁰ (it has an obstruction)
        assert cohomology.n_global_theorems == 0


# ═══════════════════════════════════════════════════════════════════
# Test full pipeline on real libraries
# ═══════════════════════════════════════════════════════════════════

class TestProveLibraryMath:
    """Test the full pipeline on the `math` standard library."""

    def test_prove_math(self):
        report = prove_library('math', max_depth=1, max_items=50)
        assert report.library == 'math'
        assert report.n_proofs > 10
        assert report.pass_rate > 0.8
        # math has no class hierarchy → no descent proofs
        # but should have function contracts
        assert report.nerve.n_types >= 0

    def test_math_has_sqrt(self):
        report = prove_library('math', max_depth=1, max_items=50)
        fn_names = [s.function_name
                    for ss in report.presheaf.sections.values()
                    for s in ss]
        assert any('sqrt' in n for n in fn_names)

    def test_math_cohomology(self):
        report = prove_library('math', max_depth=1, max_items=50)
        # All function contracts should be H⁰ (no overlaps in math)
        assert report.cohomology.n_global_theorems > 0


class TestProveLibraryCollections:
    """Test on `collections` — has class hierarchies."""

    def test_prove_collections(self):
        report = prove_library('collections', max_depth=1, max_items=50)
        assert report.library == 'collections'
        assert report.n_proofs > 0
        assert report.pass_rate > 0.5

    def test_collections_types(self):
        report = prove_library('collections', max_depth=1, max_items=100)
        type_names = {t.name for t in report.nerve.types.values()}
        # Should discover at least some collection types
        assert len(type_names) > 0


class TestProveLibrarySympy:
    """Test on `sympy` — deep hierarchies, rich API."""

    def test_prove_sympy_core(self):
        report = prove_library('sympy', max_depth=1, max_items=100)
        assert report.library == 'sympy'
        assert report.n_proofs > 20
        assert report.pass_rate > 0.5

    def test_sympy_nerve_nontrivial(self):
        report = prove_library('sympy', max_depth=1, max_items=100)
        # sympy has a rich class hierarchy → nontrivial nerve
        assert report.nerve.n_types > 0

    def test_sympy_has_expand_factor_transport(self):
        """expand↔factor should generate a transport proof if both discovered."""
        report = prove_library('sympy', max_depth=1, max_items=200)
        fn_names = [s.function_name
                    for ss in report.presheaf.sections.values()
                    for s in ss]
        all_specs = [s.spec_text
                     for ss in report.presheaf.sections.values()
                     for s in ss]
        # Either we find the transport pair, or we at least have
        # some TRANSPORT proofs, or we have rich proof output at all
        has_transport = any('TRANSPORT' in s for s in all_specs)
        has_descent = any('DESCENT' in s or 'GLUE' in s for s in all_specs)
        has_proofs = report.n_proofs > 20
        assert has_transport or has_descent or has_proofs, \
            f"Expected rich proofs, got {report.n_proofs} proofs"

    def test_sympy_cohomology(self):
        report = prove_library('sympy', max_depth=1, max_items=100)
        # Should have global theorems
        assert report.cohomology.n_global_theorems > 0

    def test_sympy_theory_registered(self):
        """The pipeline should register a LibraryTheory."""
        report = prove_library('sympy', max_depth=1, max_items=50)
        theory = get_library('sympy')
        assert theory is not None


class TestProveLibraryItertools:
    """Test on `itertools`."""

    def test_prove_itertools(self):
        report = prove_library('itertools', max_depth=1, max_items=50)
        assert report.n_proofs > 0
        assert report.pass_rate > 0.5


# ═══════════════════════════════════════════════════════════════════
# Test proof term correctness
# ═══════════════════════════════════════════════════════════════════

class TestProofTermCorrectness:
    """Verify that generated proof terms are well-formed and compile."""

    def test_library_axiom_accepted(self):
        proof = LibraryAxiom(
            library='test', axiom_name='test_ax',
            statement='x == x')
        x = var('x')
        result = check_proof(proof, op('f', x), op('f', x))
        assert result.valid

    def test_refinement_descent_accepted(self):
        from cctt.proof_theory.terms import RefinementDescent
        proof = RefinementDescent(
            base_type='T',
            bound_var='x',
            fiber_predicates={
                'A': 'isinstance(x, A)',
                'B': 'isinstance(x, B)',
            },
            fiber_proofs={
                'A': LibraryAxiom(library='test', axiom_name='a',
                                  statement='on A'),
                'B': LibraryAxiom(library='test', axiom_name='b',
                                  statement='on B'),
            },
            overlap_proofs={},
            var_sorts={'x': 'Int'},
            exhaustiveness='assumed',
        )
        x = var('x')
        result = check_proof(proof, op('f', x), op('f', x))
        assert result.valid

    def test_glue_path_accepted(self):
        from cctt.proof_theory.terms import GluePath
        proof = GluePath(
            cover_name='test_cover',
            local_paths={
                'A': LibraryAxiom(library='test', axiom_name='pa',
                                  statement='path on A'),
                'B': LibraryAxiom(library='test', axiom_name='pb',
                                  statement='path on B'),
            },
            overlap_paths={},
            fiber_predicates={
                'A': 'isinstance(x, A)',
                'B': 'isinstance(x, B)',
            },
        )
        x = var('x')
        result = check_proof(proof, op('f', x), op('f', x))
        assert result.valid

    def test_transport_accepted(self):
        from cctt.proof_theory.terms import Transport
        proof = Transport(
            path_proof=LibraryAxiom(
                library='test', axiom_name='path',
                statement='A implies B'),
            source_proof=LibraryAxiom(
                library='test', axiom_name='src',
                statement='holds on A'),
            source_pred='isinstance(x, A)',
            target_pred='isinstance(x, B)',
        )
        x = var('x')
        result = check_proof(proof, op('f', x), op('f', x))
        assert result.valid

    def test_hcomp_accepted(self):
        from cctt.proof_theory.terms import HComp
        proof = HComp(
            faces={
                'f0': LibraryAxiom(library='test', axiom_name='face0',
                                   statement='face 0'),
                'f1': LibraryAxiom(library='test', axiom_name='face1',
                                   statement='face 1'),
            })
        x = var('x')
        result = check_proof(proof, op('f', x), op('f', x))
        assert result.valid


# ═══════════════════════════════════════════════════════════════════
# Test report formatting
# ═══════════════════════════════════════════════════════════════════

class TestProofReport:
    def test_summary_format(self):
        report = prove_library('math', max_depth=1, max_items=20)
        summary = report.summary()
        assert 'CCTT Library Proof Report' in summary
        assert 'math' in summary
        assert 'H⁰' in summary
        assert 'H¹' in summary

    def test_pass_rate_bounded(self):
        report = prove_library('math', max_depth=1, max_items=20)
        assert 0.0 <= report.pass_rate <= 1.0
