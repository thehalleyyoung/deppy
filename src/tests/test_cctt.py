"""Tests for the CCTT codebase."""
from __future__ import annotations
import pytest
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cctt.checker import check_equivalence, check_spec, find_bugs


class TestCoreEquivalence:
    def test_factorial_rec_iter(self):
        r = check_equivalence(
            'def f(n):\n if n<=1: return 1\n return n*f(n-1)',
            'def f(n):\n r=1\n for i in range(1,n+1): r*=i\n return r')
        assert r.equivalent is True

    def test_abs_branches(self):
        r = check_equivalence(
            'def f(x):\n if x>0: return x\n return -x',
            'def f(x): return x if x>=0 else -x')
        assert r.equivalent is True

    def test_different_functions(self):
        r = check_equivalence('def f(n): return n*2', 'def g(n): return n+1')
        assert r.equivalent is False

    def test_sign_reorder(self):
        r = check_equivalence(
            'def f(x):\n if x<0: return -1\n if x==0: return 0\n return 1',
            'def f(x):\n if x>0: return 1\n if x<0: return -1\n return 0')
        assert r.equivalent is True

    def test_sum_rec_iter(self):
        r = check_equivalence(
            'def f(n):\n if n<=0: return 0\n return n+f(n-1)',
            'def f(n):\n s=0\n for i in range(0,n+1): s+=i\n return s')
        assert r.equivalent is True

    def test_double_arith(self):
        r = check_equivalence('def f(n): return n+n', 'def f(n): return 2*n')
        assert r.equivalent is True

    def test_arity_mismatch(self):
        r = check_equivalence('def f(a): return a', 'def f(a, b): return a')
        assert r.equivalent is False


class TestSpecChecking:
    def test_sort_correct(self):
        r = check_spec('def f(xs): return sorted(xs)', 'def f(xs): return sorted(xs)')
        assert r.equivalent is True

    def test_abs_spec(self):
        r = check_spec(
            'def f(x):\n if x < 0: return -x\n return x',
            'def f(x): return abs(x)')
        assert r.equivalent is True


class TestBugFinding:
    def test_off_by_one(self):
        r = find_bugs(
            'def f(n):\n s=0\n for i in range(n): s+=i\n return s',
            'def f(n):\n s=0\n for i in range(n+1): s+=i\n return s')
        assert r.equivalent is False

    def test_wrong_init(self):
        r = find_bugs(
            'def f(n):\n r=0\n for i in range(1,n+1): r*=i\n return r',
            'def f(n):\n r=1\n for i in range(1,n+1): r*=i\n return r')
        assert r.equivalent is False


class TestTheory:
    def test_pyobj_constructors(self):
        from cctt.theory import Theory
        T = Theory()
        assert T.mkint(42) is not None
        assert T.mkbool(True) is not None
        assert T.mkstr("hello") is not None
        assert T.mknone() is not None

    def test_shared_fn_identity(self):
        from cctt.theory import Theory
        T = Theory()
        assert T.shared_fn('sorted', 1) is T.shared_fn('sorted', 1)

    def test_tag_fibration(self):
        from cctt.theory import Theory, _z3
        T = Theory()
        s = _z3.Solver()
        s.add(T.tag(T.mkint(5)) != T.TInt)
        assert s.check() == _z3.unsat


class TestCechCohomology:
    """Tests for genuine Čech cohomology over the input-space guard cover."""

    def test_piecewise_flatten_linear_chain(self):
        """Flatten a linear OCase chain to piecewise form."""
        from cctt.denotation import OCase, OOp, OVar, OLit
        from cctt.compositional_cohomology import _flatten_to_piecewise

        # case(x > 0, 1, case(x < 0, -1, 0))
        term = OCase(
            test=OOp('gt', (OVar('x'), OLit(0))),
            true_branch=OLit(1),
            false_branch=OCase(
                test=OOp('lt', (OVar('x'), OLit(0))),
                true_branch=OLit(-1),
                false_branch=OLit(0)))
        pieces = _flatten_to_piecewise(term)
        assert len(pieces) == 3
        assert pieces[0].value.canon() == '1'
        assert pieces[1].value.canon() == '-1'
        assert pieces[2].value.canon() == '0'

    def test_piecewise_single_piece(self):
        """Non-case term yields single piece with guard=True."""
        from cctt.denotation import OOp, OVar, OLit
        from cctt.compositional_cohomology import _flatten_to_piecewise

        term = OOp('add', (OVar('x'), OLit(1)))
        pieces = _flatten_to_piecewise(term)
        assert len(pieces) == 1
        assert pieces[0].guard.canon() == 'True'
        assert pieces[0].value.canon() == 'add($x,1)'

    def test_cech_same_guards_same_values(self):
        """Same guard + same values → H¹=0."""
        from cctt.denotation import OCase, OOp, OVar, OLit
        from cctt.compositional_cohomology import cech_input_cohomology

        t1 = OCase(OOp('gt', (OVar('x'), OLit(0))), OLit(1), OLit(0))
        t2 = OCase(OOp('gt', (OVar('x'), OLit(0))), OLit(1), OLit(0))
        result = cech_input_cohomology(t1, t2, params=['x'])
        assert result.equivalent is True

    def test_cech_equivalent_guards_integer(self):
        """x > 0 ≡ x >= 1 for integers → H¹=0."""
        from cctt.denotation import OCase, OOp, OVar, OLit
        from cctt.compositional_cohomology import cech_input_cohomology

        t1 = OCase(OOp('gt', (OVar('x'), OLit(0))), OLit(1), OLit(0))
        t2 = OCase(OOp('ge', (OVar('x'), OLit(1))), OLit(1), OLit(0))
        result = cech_input_cohomology(t1, t2, params=['x'])
        assert result.equivalent is True
        assert result.h1_rank == 0

    def test_cech_different_guard_order(self):
        """sign: case(x>0,1,case(x<0,-1,0)) ≡ case(x<0,-1,case(x>0,1,0))."""
        from cctt.denotation import OCase, OOp, OVar, OLit
        from cctt.compositional_cohomology import cech_input_cohomology

        t1 = OCase(OOp('gt', (OVar('x'), OLit(0))), OLit(1),
                    OCase(OOp('lt', (OVar('x'), OLit(0))), OLit(-1), OLit(0)))
        t2 = OCase(OOp('lt', (OVar('x'), OLit(0))), OLit(-1),
                    OCase(OOp('gt', (OVar('x'), OLit(0))), OLit(1), OLit(0)))
        result = cech_input_cohomology(t1, t2, params=['x'])
        assert result.equivalent is True
        assert result.h1_rank == 0
        assert result.empty_regions >= 6  # most cross-product regions are empty

    def test_cech_complementary_guards(self):
        """and(a,b) vs or(eq(a,0),eq(b,0)) — complementary boolean guards."""
        from cctt.denotation import OCase, OOp, OVar, OLit
        from cctt.compositional_cohomology import cech_input_cohomology

        formula = OOp('add', (OVar('a'), OVar('b')))
        t1 = OCase(OOp('and', (OVar('a'), OVar('b'))), formula, OLit(0))
        t2 = OCase(OOp('or', (OOp('eq', (OVar('a'), OLit(0))),
                               OOp('eq', (OVar('b'), OLit(0))))),
                   OLit(0), formula)
        result = cech_input_cohomology(t1, t2, params=['a', 'b'])
        assert result.equivalent is True
        assert result.h1_rank == 0

    def test_cech_structural_emptiness(self):
        """Cross-product regions with contradictory guards are structurally empty."""
        from cctt.compositional_cohomology import _is_structurally_contradictory
        from cctt.denotation import OOp, OVar, OLit

        guard = OOp('gt', (OVar('x'), OLit(0)))
        neg_guard = OOp('u_not', (guard,))

        # and(guard, u_not(guard)) is contradictory
        contradictory = OOp('and', (guard, neg_guard))
        assert _is_structurally_contradictory(contradictory, set()) is True

        # and(guard, guard) is NOT contradictory
        consistent = OOp('and', (guard, guard))
        assert _is_structurally_contradictory(consistent, set()) is False

    def test_cech_no_false_positive_opaque_vars(self):
        """Opaque Z3 variables must not produce spurious counterexamples."""
        from cctt.denotation import OCase, OOp, OVar, OLit, OFold
        from cctt.compositional_cohomology import cech_input_cohomology

        # Two folds with different hash keys — structurally different
        # but Čech must NOT report False (counterexample) — only None (unknown)
        t1 = OCase(OOp('gt', (OVar('x'), OLit(0))),
                   OFold('hash1', OLit(0), OVar('x')),
                   OLit(0))
        t2 = OCase(OOp('gt', (OVar('x'), OLit(0))),
                   OFold('hash2', OLit(0), OVar('x')),
                   OLit(0))
        result = cech_input_cohomology(t1, t2, params=['x'])
        # Must not report False (would be false positive)
        assert result.equivalent is not False
        assert result.disagreed_regions == 0

    def test_cech_genuine_disagreement(self):
        """Genuine disagreement on a region → H¹ > 0 (no opaque vars)."""
        from cctt.denotation import OCase, OOp, OVar, OLit
        from cctt.compositional_cohomology import cech_input_cohomology

        # case(x > 0, 1, 0) vs case(x > 0, 2, 0)
        # Value 1 ≠ 2 on the x>0 region — genuine disagreement
        t1 = OCase(OOp('gt', (OVar('x'), OLit(0))), OLit(1), OLit(0))
        t2 = OCase(OOp('gt', (OVar('x'), OLit(0))), OLit(2), OLit(0))
        result = cech_input_cohomology(t1, t2, params=['x'])
        assert result.equivalent is False
        assert result.h1_rank >= 1


if __name__ == '__main__':
    pytest.main([__file__, '-v', '--timeout=30'])
