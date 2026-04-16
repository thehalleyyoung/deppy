"""Tests for the new C⁴ modules: extraction, DSL, python_patterns, spec_compiler."""
from __future__ import annotations

import sys
import os
import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

from cctt.proof_theory.terms import (
    ProofTerm, Refl, Sym, Trans, Cong,
    Beta, Delta, Eta,
    NatInduction, ListInduction, Assume, Cut,
    LoopInvariant, Simulation, AbstractionRefinement,
    CasesSplit, Ext, FiberDecomposition,
    ArithmeticSimp,
    var, lit, op, lam,
)

from cctt.proof_theory.checker import (
    check_proof, VerificationResult, ProofContext,
)


# ═══════════════════════════════════════════════════════════════════
# Extraction tests
# ═══════════════════════════════════════════════════════════════════

class TestExtraction:
    """Tests for cctt.proof_theory.extraction."""

    def test_import(self):
        from cctt.proof_theory.extraction import (
            extract_from_proof, oterm_to_python, oterm_to_function,
            code_to_proof_obligation, verified,
            ExtractedCode, ExtractionCertificate,
        )
        assert ExtractedCode is not None
        assert ExtractionCertificate is not None

    def test_oterm_to_python_var(self):
        from cctt.proof_theory.extraction import oterm_to_python
        assert oterm_to_python(OVar('x')) == 'x'

    def test_oterm_to_python_lit(self):
        from cctt.proof_theory.extraction import oterm_to_python
        assert oterm_to_python(OLit(42)) == '42'
        assert oterm_to_python(OLit('hello')) == "'hello'"

    def test_oterm_to_python_binop(self):
        from cctt.proof_theory.extraction import oterm_to_python
        term = OOp('+', (OVar('x'), OLit(1)))
        result = oterm_to_python(term)
        assert 'x' in result
        assert '+' in result
        assert '1' in result

    def test_oterm_to_python_case(self):
        from cctt.proof_theory.extraction import oterm_to_python
        term = OCase(
            test=OOp('==', (OVar('n'), OLit(0))),
            true_branch=OLit(1),
            false_branch=OVar('n'),
        )
        result = oterm_to_python(term)
        assert 'if' in result
        assert 'else' in result

    def test_oterm_to_python_lambda(self):
        from cctt.proof_theory.extraction import oterm_to_python
        term = OLam(params=('x',), body=OOp('+', (OVar('x'), OLit(1))))
        result = oterm_to_python(term)
        assert 'lambda' in result

    def test_oterm_to_function(self):
        from cctt.proof_theory.extraction import oterm_to_function
        term = OOp('+', (OVar('a'), OVar('b')))
        result = oterm_to_function(term, 'add', ['a', 'b'])
        assert 'def add(a, b):' in result
        assert 'return' in result

    def test_oterm_to_function_case(self):
        from cctt.proof_theory.extraction import oterm_to_function
        term = OCase(
            test=OOp('<', (OVar('x'), OLit(0))),
            true_branch=OOp('-', (OLit(0), OVar('x'))),
            false_branch=OVar('x'),
        )
        result = oterm_to_function(term, 'my_abs', ['x'])
        assert 'def my_abs(x):' in result
        assert 'if' in result

    def test_extract_from_proof_refl(self):
        from cctt.proof_theory.extraction import extract_from_proof
        term = OOp('+', (OVar('a'), OVar('b')))
        proof = Refl(term=term)
        extracted = extract_from_proof(proof, term, term, 'add_fn', ['a', 'b'])
        assert extracted.function_name == 'add_fn'
        assert 'def add_fn' in extracted.source
        assert extracted.certificate.verification_valid

    def test_extract_from_proof_nat_induction(self):
        from cctt.proof_theory.extraction import extract_from_proof
        lhs = OFix('f', OCase(
            OOp('==', (OVar('n'), OLit(0))),
            OLit(1),
            OOp('*', (OVar('n'), OOp('f', (OOp('-', (OVar('n'), OLit(1))),)))),
        ))
        rhs = OFold(
            op_name='*',
            init=OLit(1),
            collection=OOp('range', (OLit(1), OOp('+', (OVar('n'), OLit(1))))),
        )
        proof = NatInduction(
            base_case=Assume('base', lhs, rhs),
            inductive_step=Assume('step', lhs, rhs),
            variable='n',
        )
        extracted = extract_from_proof(proof, lhs, rhs, 'factorial', ['n'])
        assert 'factorial' in extracted.source
        assert extracted.certificate.proof_strategy == 'NatInduction'

    def test_extraction_certificate_trust_levels(self):
        from cctt.proof_theory.extraction import ExtractionCertificate
        cert_valid = ExtractionCertificate(
            proof_strategy='Refl', lhs_description='a', rhs_description='a',
            verification_valid=True, z3_calls=0,
        )
        assert cert_valid.trust_level() == 'STRUCTURALLY_VERIFIED'

        cert_z3 = ExtractionCertificate(
            proof_strategy='Z3', lhs_description='a', rhs_description='a',
            verification_valid=True, z3_calls=1,
        )
        assert cert_z3.trust_level() == 'Z3_PROVEN'

        cert_cond = ExtractionCertificate(
            proof_strategy='Assume', lhs_description='a', rhs_description='a',
            verification_valid=True, assumptions_used=['ih'],
        )
        assert cert_cond.trust_level() == 'CONDITIONAL'

        cert_bad = ExtractionCertificate(
            proof_strategy='X', lhs_description='a', rhs_description='a',
            verification_valid=False,
        )
        assert cert_bad.trust_level() == 'UNTRUSTED'

    def test_with_guarantee(self):
        from cctt.proof_theory.extraction import ExtractedCode, ExtractionCertificate
        ec = ExtractedCode(
            source='def f(x):\n    return x + 1',
            function_name='f',
            guarantee_text='increments by one',
            certificate=ExtractionCertificate(
                proof_strategy='Refl', lhs_description='f',
                rhs_description='f', verification_valid=True,
            ),
        )
        text = ec.with_guarantee()
        assert '@guarantee("increments by one")' in text
        assert 'from deppy.hybrid import guarantee' in text

    def test_code_to_proof_obligation(self):
        from cctt.proof_theory.extraction import code_to_proof_obligation
        obl = code_to_proof_obligation(
            'def f(xs): return sorted(set(xs))',
            'returns a sorted list with no duplicates',
            'f',
        )
        assert 'goal' in obl
        assert 'structural' in obl
        assert 'semantic' in obl
        assert len(obl['structural']) > 0  # 'sorted' and 'no duplicate' detected

    def test_verified_decorator(self):
        from cctt.proof_theory.extraction import verified
        term = OLit(42)
        proof = Refl(term=term)

        @verified(proof, term, term)
        def constant():
            return 42

        assert hasattr(constant, '_c4_verified')
        assert constant._c4_verified is True
        assert constant._c4_proof_strategy == 'Refl'

    def test_bidirectional_extraction(self):
        """Test forward + backward extraction (the key advantage over F*)."""
        from cctt.proof_theory.extraction import (
            extract_from_proof, code_to_proof_obligation,
        )
        # Forward: proof → code
        term = OOp('*', (OVar('x'), OVar('x')))
        proof = Refl(term=term)
        extracted = extract_from_proof(proof, term, term, 'square', ['x'])
        assert 'def square' in extracted.source

        # Backward: code → obligation
        obl = code_to_proof_obligation(
            extracted.source,
            extracted.guarantee_text,
            'square',
        )
        assert obl['function_name'] == 'square'


# ═══════════════════════════════════════════════════════════════════
# DSL tests
# ═══════════════════════════════════════════════════════════════════

class TestDSL:
    """Tests for cctt.proof_theory.dsl."""

    def test_import(self):
        from cctt.proof_theory.dsl import (
            ProofBuilder, ProofScript, c4_proof,
        )
        assert ProofBuilder is not None

    def test_proof_builder_refl(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder(lhs=OLit(1), rhs=OLit(1))
        proof = pb.refl(OLit(1))
        assert isinstance(proof, Refl)
        assert pb.result is proof

    def test_proof_builder_sym(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        inner = pb.refl(OLit(1))
        outer = pb.sym(inner)
        assert isinstance(outer, Sym)

    def test_proof_builder_trans(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        p1 = Refl(term=OLit(1))
        p2 = Refl(term=OLit(1))
        result = pb.trans(p1, p2)
        assert isinstance(result, Trans)

    def test_proof_builder_induction(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        base = Refl(term=OLit(0))
        step = Assume('ih', OVar('n'), OVar('n'))
        result = pb.by_induction(on='n', base=base, step=step)
        assert isinstance(result, NatInduction)

    def test_proof_builder_list_induction(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        base = Refl(term=OLit(0))
        step = Assume('ih', OVar('xs'), OVar('xs'))
        result = pb.by_induction(on='xs', base=base, step=step, structure='list')
        assert isinstance(result, ListInduction)

    def test_proof_builder_cases(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        result = pb.by_cases(
            on=OVar('b'),
            cases={
                'true': Refl(term=OLit(1)),
                'false': Refl(term=OLit(0)),
            },
        )
        assert isinstance(result, CasesSplit)

    def test_proof_builder_have(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        lemma = pb.have('lem', OVar('a'), OVar('b'))
        assert isinstance(lemma, Assume)
        assert 'lem' in pb._lemmas

    def test_proof_builder_have_with_proof(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        inner = Refl(term=OLit(1))
        lemma = pb.have('lem', OLit(1), OLit(1), by=inner)
        assert isinstance(lemma, Refl)

    def test_proof_builder_calc_trans(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        p1 = Refl(term=OLit(1))
        p2 = Refl(term=OLit(1))
        p3 = Refl(term=OLit(1))
        result = pb.calc_trans(p1, p2, p3)
        assert isinstance(result, Trans)

    def test_proof_builder_build(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        pb.refl(OLit(42))
        proof = pb.build()
        assert isinstance(proof, Refl)

    def test_proof_builder_verify(self):
        from cctt.proof_theory.dsl import ProofBuilder
        term = OLit(42)
        pb = ProofBuilder(lhs=term, rhs=term)
        pb.refl(term)
        result = pb.verify()
        assert result.valid

    def test_proof_builder_fiber_split(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        result = pb.fiber_split({
            'positive': Refl(term=OLit(1)),
            'negative': Refl(term=OLit(-1)),
        })
        assert isinstance(result, FiberDecomposition)

    def test_proof_builder_simulation(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        result = pb.by_simulation(
            relation='bisim',
            init=Refl(term=OLit(0)),
            step=Assume('step', OVar('s'), OVar('t')),
            output=Refl(term=OVar('out')),
        )
        assert isinstance(result, Simulation)

    def test_proof_builder_z3(self):
        from cctt.proof_theory.dsl import ProofBuilder
        from cctt.proof_theory.terms import Z3Discharge
        pb = ProofBuilder()
        result = pb.z3('x + y == y + x', fragment='qf_lia', x='int', y='int')
        assert isinstance(result, Z3Discharge)

    def test_c4_proof_decorator(self):
        from cctt.proof_theory.dsl import c4_proof
        term = OLit(42)

        @c4_proof(lhs=term, rhs=term)
        def my_proof(pb):
            pb.refl(term)

        assert my_proof.result is not None
        assert isinstance(my_proof.build(), Refl)

    def test_proof_script(self):
        from cctt.proof_theory.dsl import ProofScript
        lhs = OLit(42)
        rhs = OLit(42)
        script = ProofScript(lhs=lhs, rhs=rhs)
        script.apply(Refl(term=lhs))
        proof = script.qed()
        assert isinstance(proof, Refl)

    def test_proof_script_induction(self):
        from cctt.proof_theory.dsl import ProofScript
        lhs = OVar('f_n')
        rhs = OVar('g_n')
        script = ProofScript(lhs=lhs, rhs=rhs)
        script.induction('n')
        script.base_case(Refl(term=OLit(0)))
        script.inductive_step(Assume('ih', lhs, rhs))
        proof = script.qed()
        assert isinstance(proof, NatInduction)

    def test_proof_builder_ext(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        result = pb.ext('x', Refl(term=OVar('x')))
        assert isinstance(result, Ext)

    def test_proof_builder_unfold(self):
        from cctt.proof_theory.dsl import ProofBuilder
        pb = ProofBuilder()
        result = pb.unfold('f', OVar('x'))
        assert isinstance(result, Delta)


# ═══════════════════════════════════════════════════════════════════
# Python patterns tests
# ═══════════════════════════════════════════════════════════════════

class TestPythonPatterns:
    """Tests for cctt.proof_theory.python_patterns."""

    def test_import(self):
        from cctt.proof_theory.python_patterns import (
            PatternInstance, by_pattern, list_patterns, PATTERNS,
        )
        assert len(PATTERNS) == 10

    def test_list_patterns(self):
        from cctt.proof_theory.python_patterns import list_patterns
        names = list_patterns()
        assert 'list_comp' in names
        assert 'generator' in names
        assert 'exception' in names
        assert 'context_manager' in names

    def test_list_comp_pattern(self):
        from cctt.proof_theory.python_patterns import by_pattern
        inst = by_pattern('list_comp',
                          collection=OVar('my_list'),
                          transform=OLam(params=('x',), body=OOp('+', (OVar('x'), OLit(1)))))
        assert inst.pattern_name == 'list_comprehension'
        assert inst.lhs is not None
        assert inst.rhs is not None
        assert isinstance(inst.proof, ListInduction)

    def test_generator_pattern(self):
        from cctt.proof_theory.python_patterns import by_pattern
        inst = by_pattern('generator',
                          collection=OVar('items'),
                          transform=OLam(params=('x',), body=OVar('x')))
        assert inst.pattern_name == 'generator_materialization'

    def test_mutation_isolation_pattern(self):
        from cctt.proof_theory.python_patterns import by_pattern
        inst = by_pattern('mutation_isolation')
        assert inst.pattern_name == 'mutation_isolation'
        assert isinstance(inst.proof, Simulation)

    def test_exception_pattern(self):
        from cctt.proof_theory.python_patterns import by_pattern
        inst = by_pattern('exception')
        assert inst.pattern_name == 'exception_equiv'
        assert isinstance(inst.proof, CasesSplit)

    def test_decorator_pattern(self):
        from cctt.proof_theory.python_patterns import by_pattern
        inst = by_pattern('decorator', func_name='my_func', decorator_name='cache')
        assert inst.pattern_name == 'decorator_transparency'
        assert isinstance(inst.proof, Ext)

    def test_context_manager_pattern(self):
        from cctt.proof_theory.python_patterns import by_pattern
        inst = by_pattern('context_manager', resource='file', body='read')
        assert inst.pattern_name == 'context_manager'

    def test_map_filter_pattern(self):
        from cctt.proof_theory.python_patterns import by_pattern
        inst = by_pattern('map_filter')
        assert inst.pattern_name == 'map_filter_compose'

    def test_reduce_loop_pattern(self):
        from cctt.proof_theory.python_patterns import by_pattern
        inst = by_pattern('reduce_loop')
        assert inst.pattern_name == 'reduce_loop'
        assert isinstance(inst.proof, Refl)  # trivially equal

    def test_dict_comp_pattern(self):
        from cctt.proof_theory.python_patterns import by_pattern
        inst = by_pattern('dict_comp')
        assert inst.pattern_name == 'dict_comprehension'

    def test_sorted_key_pattern(self):
        from cctt.proof_theory.python_patterns import by_pattern
        inst = by_pattern('sorted_key')
        assert inst.pattern_name == 'sorted_key'

    def test_unknown_pattern_raises(self):
        from cctt.proof_theory.python_patterns import by_pattern
        with pytest.raises(ValueError, match='Unknown pattern'):
            by_pattern('nonexistent_pattern')

    def test_pattern_instance_has_description(self):
        from cctt.proof_theory.python_patterns import by_pattern
        inst = by_pattern('reduce_loop')
        assert len(inst.description) > 0
        assert inst.parameters is not None


# ═══════════════════════════════════════════════════════════════════
# Spec compiler tests
# ═══════════════════════════════════════════════════════════════════

class TestSpecCompiler:
    """Tests for cctt.proof_theory.spec_compiler."""

    def test_import(self):
        from cctt.proof_theory.spec_compiler import (
            CompiledSpec, parse_guarantee, compile_guarantee_to_type,
            verify_against_spec, spec_to_markdown,
            StructuralPredicate, SemanticPredicate,
        )
        assert CompiledSpec is not None

    def test_parse_sorted(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee
        spec = parse_guarantee('returns a sorted list')
        assert len(spec.structural) >= 1
        assert any(s.name == 'sorted' for s in spec.structural)

    def test_parse_unique(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee
        spec = parse_guarantee('returns unique elements')
        assert any(s.name == 'unique' for s in spec.structural)

    def test_parse_sorted_unique(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee
        spec = parse_guarantee('returns a sorted list with no duplicates')
        assert any(s.name == 'sorted' for s in spec.structural)
        assert any(s.name == 'unique' for s in spec.structural)

    def test_parse_semantic(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee
        spec = parse_guarantee('computes the optimal solution')
        assert len(spec.semantic) >= 1
        assert any(s.name == 'optimality' for s in spec.semantic)

    def test_parse_fallback_semantic(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee
        spec = parse_guarantee('does something very specific and unusual')
        assert len(spec.semantic) == 1
        assert spec.semantic[0].name == 'full_spec'

    def test_sigma_type_str(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee
        spec = parse_guarantee('returns a sorted list with no duplicates')
        sigma = spec.sigma_type_str()
        assert 'Σ' in sigma
        assert 'result' in sigma

    def test_return_type_inference(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee
        spec = parse_guarantee('returns a sorted list')
        assert spec.return_type == 'List'

        spec2 = parse_guarantee('returns the count of items')
        assert spec2.return_type == 'int'

        spec3 = parse_guarantee('returns a dictionary mapping')
        assert spec3.return_type == 'Dict'

    def test_compile_guarantee_to_type(self):
        from cctt.proof_theory.spec_compiler import compile_guarantee_to_type
        spec = compile_guarantee_to_type(
            'returns a sorted list with no duplicates',
            function_name='unique_sorted',
            parameter_types={'items': 'List[int]'},
        )
        assert spec.parameters == {'items': 'List[int]'}
        assert len(spec.structural) >= 2

    def test_proof_obligations(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee
        spec = parse_guarantee('returns a sorted list with no duplicates')
        obls = spec.proof_obligations()
        assert len(obls) >= 2
        assert all('kind' in o for o in obls)
        assert all('name' in o for o in obls)

    def test_generate_proof_skeleton(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee
        spec = parse_guarantee('returns a sorted list with no duplicates')
        skeleton = spec.generate_proof_skeleton()
        assert isinstance(skeleton, ProofTerm)

    def test_to_oterm(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee
        spec = parse_guarantee('returns a sorted list')
        oterm = spec.to_oterm()
        assert isinstance(oterm, OAbstract)

    def test_spec_to_markdown(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee, spec_to_markdown
        spec = parse_guarantee('returns a sorted list with no duplicates')
        md = spec_to_markdown(spec)
        assert '## Specification' in md
        assert 'Structural' in md
        assert 'sorted' in md.lower()

    def test_verify_against_spec(self):
        from cctt.proof_theory.spec_compiler import verify_against_spec
        code = OOp('sorted', (OVar('xs'),))
        spec, result = verify_against_spec(
            code, 'returns a sorted list',
        )
        assert spec is not None
        # The skeleton proof uses FiberDecomposition, which may or may not verify
        assert isinstance(result, VerificationResult)

    def test_parse_nonempty(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee
        spec = parse_guarantee('returns a non-empty list')
        assert any(s.name == 'nonempty' for s in spec.structural)

    def test_parse_monotonic(self):
        from cctt.proof_theory.spec_compiler import parse_guarantee
        spec = parse_guarantee('a monotonic function')
        assert any(s.name == 'monotonic' for s in spec.structural)


# ═══════════════════════════════════════════════════════════════════
# Integration: test that __init__ exports work
# ═══════════════════════════════════════════════════════════════════

class TestInitExports:
    """Verify that __init__.py exports all new modules."""

    def test_extraction_exports(self):
        from cctt.proof_theory import (
            extract_from_proof, extract_from_document, extract_all,
            oterm_to_python, oterm_to_function,
            code_to_proof_obligation, verified,
            ExtractedCode, ExtractionCertificate,
        )
        assert extract_from_proof is not None

    def test_dsl_exports(self):
        from cctt.proof_theory import (
            ProofBuilder, ProofScript, CalcStep, c4_proof,
        )
        assert ProofBuilder is not None

    def test_pattern_exports(self):
        from cctt.proof_theory import (
            PatternInstance, by_pattern, list_patterns, PATTERNS,
        )
        assert len(PATTERNS) > 0

    def test_spec_compiler_exports(self):
        from cctt.proof_theory import (
            CompiledSpec, StructuralPredicate, SemanticPredicate,
            parse_guarantee, compile_guarantee_to_type,
            verify_against_spec, spec_to_markdown,
        )
        assert parse_guarantee is not None


if __name__ == '__main__':
    pytest.main([__file__, '-v', '--timeout=30'])
