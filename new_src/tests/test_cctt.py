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


if __name__ == '__main__':
    pytest.main([__file__, '-v', '--timeout=30'])
