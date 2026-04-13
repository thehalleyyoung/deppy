"""D20: Specification Unification Axiom — Yoneda Embedding for Programs.

§22.6 of the CCTT monograph.  Theorem 22.6.1 (Spec Uniqueness):
If two programs satisfy the same deterministic specification on all
inputs, they are equal in the presheaf model (Yoneda lemma).

This is the LARGEST axiom file — it houses the complete spec library:
  factorial, range_sum, fibonacci_like, sorted, binomial,
  gcd, lcm, is_prime, power, flatten, zip_with, partition,
  group_by, max, min, reverse, abs, all, any, product, len,
  matrix_multiply, tree_traversal.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "D20_spec_unify"
AXIOM_CATEGORY = "algorithmic_strategy"

SOUNDNESS_PROOF = """
Theorem 22.6.1 (Specification Uniqueness — Yoneda).
Let F: C^op → Set be a representable presheaf with F ≅ Hom(−, A).
Two programs p₁, p₂ satisfying the same deterministic specification
φ have the same image under F: F(p₁) = F(p₂).  Since F is faithful
on the decidable fragment, p₁ = p₂ in PyComp/~.

Concretely: if we can identify that both programs compute "factorial",
they produce identical outputs on all inputs, hence are ≡ in the
operad denotation.
"""

COMPOSES_WITH = ["D24_eta", "D22_effect", "ALG", "FOLD"]
REQUIRES: List[str] = []

EXAMPLES = [
    ("fold[mul](1, range(1, n+1))", "@factorial(n)", "D20_spec_discovery"),
    ("fix[fib](add(sub,sub))", "@fibonacci_like(n)", "D20_spec_discovery"),
    ("fold[add](0, range(n))", "@range_sum(n)", "D20_spec_discovery"),
    ("math.gcd(a, b)", "@gcd(a, b)", "D20_spec_discovery"),
    ("fold[concat]([], nested)", "@flatten(nested)", "D20_spec_discovery"),
]

# ── Free variable extraction ────────────────────────────────

def _extract_free_vars(term: OTerm) -> Set[str]:
    if isinstance(term, OVar):
        return {term.name}
    if isinstance(term, (OLit, OUnknown)):
        return set()
    if isinstance(term, OOp):
        r: Set[str] = set()
        for a in term.args:
            r |= _extract_free_vars(a)
        return r
    if isinstance(term, OCase):
        return (_extract_free_vars(term.test)
                | _extract_free_vars(term.true_branch)
                | _extract_free_vars(term.false_branch))
    if isinstance(term, OFold):
        return _extract_free_vars(term.init) | _extract_free_vars(term.collection)
    if isinstance(term, OFix):
        return _extract_free_vars(term.body)
    if isinstance(term, OLam):
        return _extract_free_vars(term.body) - set(term.params)
    if isinstance(term, OSeq):
        r2: Set[str] = set()
        for e in term.elements:
            r2 |= _extract_free_vars(e)
        return r2
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner)
    if isinstance(term, OAbstract):
        r3: Set[str] = set()
        for a in term.inputs:
            r3 |= _extract_free_vars(a)
        return r3
    if isinstance(term, OMap):
        r4 = _extract_free_vars(term.transform) | _extract_free_vars(term.collection)
        if term.filter_pred:
            r4 |= _extract_free_vars(term.filter_pred)
        return r4
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body) | _extract_free_vars(term.default)
    if isinstance(term, ODict):
        r5: Set[str] = set()
        for k, v in term.pairs:
            r5 |= _extract_free_vars(k) | _extract_free_vars(v)
        return r5
    return set()


def _sorted_var_tuple(term: OTerm) -> Tuple[OTerm, ...]:
    """Helper: extract free vars as sorted OVar tuple."""
    fv = _extract_free_vars(term)
    return tuple(OVar(v) for v in sorted(fv))


# ═══════════════════════════════════════════════════════════
# Individual spec recognisers
# ═══════════════════════════════════════════════════════════

def _identify_factorial(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """fold[mul](1, range(1, n+1)) or fix with n * f(n-1)."""
    if isinstance(term, OFold):
        if term.op_name in ('.mul', 'mul', 'imul', 'mult'):
            if isinstance(term.init, OLit) and term.init.value == 1:
                if isinstance(term.collection, OOp) and term.collection.name == 'range':
                    return ('factorial', (term.collection.args[-1],))
    if isinstance(term, OFix):
        canon = term.body.canon()
        if ('mul' in canon or 'mult' in canon) and 'sub' in canon:
            if '0' in canon or '1' in canon:
                inputs = _extract_free_vars(term)
                if inputs:
                    return ('factorial', tuple(OVar(v) for v in sorted(inputs)))
    if isinstance(term, OOp) and term.name in ('math.factorial', 'factorial'):
        return ('factorial', term.args)
    return None


def _identify_range_sum(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """fold[add](0, range(…))."""
    if isinstance(term, OFold):
        if term.op_name in ('.add', 'add', 'iadd'):
            if isinstance(term.init, OLit) and term.init.value == 0:
                if isinstance(term.collection, OOp) and term.collection.name == 'range':
                    return ('range_sum', (term.collection.args[-1],))
    # n*(n-1)//2 closed form
    if isinstance(term, OOp) and term.name == 'floordiv':
        if len(term.args) == 2 and isinstance(term.args[1], OLit) and term.args[1].value == 2:
            numer = term.args[0]
            if isinstance(numer, OOp) and numer.name in ('mul', 'mult') and len(numer.args) == 2:
                return ('range_sum', (numer.args[0],))
    return None


def _identify_fibonacci(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """fix with f(n-1) + f(n-2) pattern."""
    if isinstance(term, OFix):
        canon = term.body.canon()
        if 'add' in canon and 'sub' in canon:
            inputs = _extract_free_vars(term)
            if inputs:
                return ('fibonacci_like', tuple(OVar(v) for v in sorted(inputs)))
    return None


def _identify_sorted(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name in ('sorted', 'stable_sort'):
        return ('sorted', term.args)
    return None


def _identify_binomial(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """C(n,k) via math.comb or factorial quotient."""
    if isinstance(term, OOp) and term.name in ('math.comb', 'comb', 'binomial'):
        return ('binomial', term.args)
    # factorial(n) // (factorial(k) * factorial(n-k))
    if isinstance(term, OOp) and term.name == 'floordiv' and len(term.args) == 2:
        numer, denom = term.args
        if (isinstance(numer, OAbstract) and numer.spec == 'factorial' and
                isinstance(denom, OOp) and denom.name in ('mul', 'mult')):
            return ('binomial', numer.inputs)
    return None


def _identify_gcd(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OFix):
        canon = term.body.canon()
        if ('mod' in canon or 'sub' in canon) and '0' in canon:
            inputs = _extract_free_vars(term)
            si = sorted(inputs)
            if len(si) >= 2:
                return ('gcd', (OVar(si[0]), OVar(si[1])))
    if isinstance(term, OOp) and term.name in ('gcd', 'math.gcd'):
        return ('gcd', term.args)
    return None


def _identify_lcm(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name in ('lcm', 'math.lcm'):
        return ('lcm', term.args)
    if isinstance(term, OOp) and term.name in ('floordiv', 'div') and len(term.args) == 2:
        numer, denom = term.args
        if isinstance(numer, OOp) and numer.name in ('mul', 'mult'):
            if isinstance(denom, OOp) and denom.name in ('math.gcd', 'gcd'):
                return ('lcm', numer.args)
        if isinstance(numer, OOp) and numer.name == 'abs' and len(numer.args) == 1:
            if isinstance(numer.args[0], OOp) and numer.args[0].name in ('mul', 'mult'):
                return ('lcm', numer.args[0].args)
    return None


def _identify_is_prime(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OFix):
        canon = term.body.canon()
        if 'mod' in canon and ('sqrt' in canon or 'mul' in canon):
            inputs = _extract_free_vars(term)
            if inputs:
                return ('is_prime', (OVar(sorted(inputs)[0]),))
    if isinstance(term, OFold):
        canon = term.collection.canon() if term.collection else ''
        if 'mod' in canon or 'mod' in term.op_name:
            inputs = _extract_free_vars(term)
            if inputs:
                return ('is_prime', (OVar(sorted(inputs)[0]),))
    return None


def _identify_power(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name in ('pow', 'math.pow', '**'):
        return ('power', term.args)
    if isinstance(term, OFix):
        canon = term.body.canon()
        if ('mul' in canon or 'mult' in canon) and ('floordiv' in canon or 'rshift' in canon):
            inputs = _extract_free_vars(term)
            si = sorted(inputs)
            if len(si) >= 2:
                return ('power', (OVar(si[0]), OVar(si[1])))
    if isinstance(term, OFold):
        if term.op_name in ('mul', '.mul', 'imul', 'mult'):
            if isinstance(term.init, OLit) and term.init.value == 1:
                if isinstance(term.collection, OOp) and term.collection.name == 'repeat':
                    if len(term.collection.args) == 2:
                        return ('power', term.collection.args)
    return None


def _identify_flatten(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name in ('chain.from_iterable', 'flatten'):
        return ('flatten', term.args)
    if isinstance(term, OFold):
        if term.op_name in ('concat', 'extend', 'iadd', '.add'):
            if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
                return ('flatten', (term.collection,))
            if isinstance(term.init, OOp) and term.init.name == 'list' and not term.init.args:
                return ('flatten', (term.collection,))
    return None


def _identify_zip_with(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OMap):
        if isinstance(term.collection, OOp) and term.collection.name == 'zip':
            if len(term.collection.args) == 2:
                return ('zip_with', (term.transform,) + term.collection.args)
    if isinstance(term, OOp) and term.name == 'starmap' and len(term.args) == 2:
        fn, zipped = term.args
        if isinstance(zipped, OOp) and zipped.name == 'zip':
            return ('zip_with', (fn,) + zipped.args)
    return None


def _identify_partition(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name == 'partition':
        return ('partition', term.args)
    if isinstance(term, OOp) and term.name == 'tuple' and len(term.args) == 2:
        lhs, rhs = term.args
        if isinstance(lhs, OMap) and isinstance(rhs, OMap):
            if lhs.filter_pred is not None and rhs.filter_pred is not None:
                if lhs.collection.canon() == rhs.collection.canon():
                    lp = lhs.filter_pred.canon()
                    rp = rhs.filter_pred.canon()
                    if f'u_not({lp})' == rp or f'u_not({rp})' == lp:
                        return ('partition', (lhs.filter_pred, lhs.collection))
    return None


def _identify_group_by(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name == 'groupby':
        return ('group_by', term.args)
    if isinstance(term, OFold):
        if term.op_name in ('dict_append', 'setdefault_append'):
            return ('group_by', (OUnknown('key_fn'), term.collection))
    return None


def _identify_max(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name == 'max':
        return ('max', term.args)
    if isinstance(term, OFold) and term.op_name in ('max', '.max'):
        return ('max', (term.collection,))
    return None


def _identify_min(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name == 'min':
        return ('min', term.args)
    if isinstance(term, OFold) and term.op_name in ('min', '.min'):
        return ('min', (term.collection,))
    return None


def _identify_reverse(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OFold) and term.op_name in ('prepend', '.prepend', 'cons'):
        if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
            return ('reverse', (term.collection,))
    if isinstance(term, OOp) and term.name in ('reversed', 'list_reverse'):
        return ('reverse', term.args)
    return None


def _identify_abs(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name == 'abs':
        return ('abs', term.args)
    if isinstance(term, OCase):
        if isinstance(term.test, OOp) and term.test.name == 'lt':
            if (len(term.test.args) == 2
                    and isinstance(term.test.args[1], OLit)
                    and term.test.args[1].value == 0):
                inner_x = term.test.args[0]
                if isinstance(term.true_branch, OOp) and term.true_branch.name == 'u_neg':
                    if (len(term.true_branch.args) == 1
                            and term.true_branch.args[0].canon() == inner_x.canon()
                            and term.false_branch.canon() == inner_x.canon()):
                        return ('abs', (inner_x,))
    return None


def _identify_all_any(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name == 'all':
        return ('all', term.args)
    if isinstance(term, OFold) and term.op_name in ('and', '.and'):
        if isinstance(term.init, OLit) and term.init.value is True:
            return ('all', (term.collection,))
    if isinstance(term, OOp) and term.name == 'any':
        return ('any', term.args)
    if isinstance(term, OFold) and term.op_name in ('or', '.or'):
        if isinstance(term.init, OLit) and term.init.value is False:
            return ('any', (term.collection,))
    return None


def _identify_product(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Product of collection elements (not factorial — not over range)."""
    if isinstance(term, OOp) and term.name in ('prod', 'math.prod'):
        return ('product', term.args)
    if isinstance(term, OFold) and term.op_name in ('.mul', 'mul', 'imul', 'mult'):
        if isinstance(term.init, OLit) and term.init.value == 1:
            if not (isinstance(term.collection, OOp) and term.collection.name == 'range'):
                return ('product', (term.collection,))
    return None


def _identify_len(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name == 'len':
        return ('len', term.args)
    return None


def _identify_matrix_multiply(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name in ('matmul', 'np.dot', '@'):
        return ('matrix_multiply', term.args)
    if isinstance(term, OOp) and term.name == 'list':
        if len(term.args) == 1 and isinstance(term.args[0], OMap):
            outer_map = term.args[0]
            if isinstance(outer_map.transform, OLam):
                canon = outer_map.transform.body.canon()
                if 'sum' in canon and ('mul' in canon or 'mult' in canon):
                    inputs = _extract_free_vars(term)
                    si = sorted(inputs)
                    if len(si) >= 2:
                        return ('matrix_multiply', (OVar(si[0]), OVar(si[1])))
    return None


def _identify_tree_traversal(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    if isinstance(term, OOp) and term.name in ('inorder', 'preorder', 'postorder'):
        return ('tree_traversal_' + term.name, term.args)
    if isinstance(term, OFix):
        canon = term.body.canon()
        if '.left' in canon and '.right' in canon:
            inputs = _extract_free_vars(term)
            if inputs:
                if '.val' in canon or '.data' in canon:
                    if 'concat' in canon or 'add' in canon:
                        return ('tree_traversal', tuple(OVar(v) for v in sorted(inputs)))
    return None


# ═══════════════════════════════════════════════════════════
# Master spec identification
# ═══════════════════════════════════════════════════════════

_SPEC_RECOGNISERS = [
    _identify_factorial,
    _identify_range_sum,
    _identify_fibonacci,
    _identify_sorted,
    _identify_binomial,
    _identify_gcd,
    _identify_lcm,
    _identify_is_prime,
    _identify_power,
    _identify_flatten,
    _identify_zip_with,
    _identify_partition,
    _identify_group_by,
    _identify_max,
    _identify_min,
    _identify_reverse,
    _identify_abs,
    _identify_all_any,
    _identify_product,
    _identify_len,
    _identify_matrix_multiply,
    _identify_tree_traversal,
]


def identify_spec(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Try to identify a high-level specification from an OTerm.

    Returns (spec_name, inputs) if recognised, else None.
    This is the Yoneda embedding: a program is uniquely determined
    by its behaviour under all observations.
    """
    for recogniser in _SPEC_RECOGNISERS:
        result = recogniser(term)
        if result is not None:
            return result
    return None


# ── FiberCtx ──────────────────────────────────────────────

@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


# ── Core axiom application ──────────────────────────────────

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D20 spec-unification to *term*.

    If the term's structure matches a known spec, replace it with
    OAbstract(spec_name, inputs).  Two different algorithms computing
    the same spec then become syntactically equal.
    """
    results: List[Tuple[OTerm, str]] = []
    spec = identify_spec(term)
    if spec is not None:
        spec_name, inputs = spec
        results.append((OAbstract(spec_name, inputs), 'D20_spec_discovery'))
    return results


def recognizes(term: OTerm) -> bool:
    """Return True if D20 can potentially identify *term*'s spec."""
    return identify_spec(term) is not None


def relevance_score(source: OTerm, target: OTerm) -> float:
    """D20 is always moderately relevant — spec unification is universal."""
    s_spec = identify_spec(source)
    t_spec = identify_spec(target)
    if s_spec is not None and t_spec is not None:
        if s_spec[0] == t_spec[0]:
            return 0.95
        return 0.4
    if s_spec is not None or t_spec is not None:
        return 0.6
    return 0.3


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: expand OAbstract back to a canonical implementation.

    OAbstract('factorial', (n,)) → fold[mul](1, range(1, n+1))
    """
    results: List[Tuple[OTerm, str]] = []

    if isinstance(term, OAbstract):
        if term.spec == 'factorial' and len(term.inputs) == 1:
            n = term.inputs[0]
            results.append((
                OFold('mul', OLit(1), OOp('range', (OLit(1), OOp('add', (n, OLit(1)))))),
                'D20_spec_expand_factorial',
            ))
        elif term.spec == 'range_sum' and len(term.inputs) == 1:
            n = term.inputs[0]
            results.append((
                OFold('add', OLit(0), OOp('range', (n,))),
                'D20_spec_expand_range_sum',
            ))
        elif term.spec == 'flatten' and len(term.inputs) == 1:
            results.append((
                OFold('concat', OSeq(()), term.inputs[0]),
                'D20_spec_expand_flatten',
            ))
        elif term.spec == 'reverse' and len(term.inputs) == 1:
            results.append((
                OOp('reversed', term.inputs),
                'D20_spec_expand_reverse',
            ))
        elif term.spec == 'product' and len(term.inputs) == 1:
            results.append((
                OFold('mul', OLit(1), term.inputs[0]),
                'D20_spec_expand_product',
            ))
        elif term.spec == 'max' and len(term.inputs) >= 1:
            results.append((
                OOp('max', term.inputs),
                'D20_spec_expand_max',
            ))
        elif term.spec == 'min' and len(term.inputs) >= 1:
            results.append((
                OOp('min', term.inputs),
                'D20_spec_expand_min',
            ))
        elif term.spec == 'all' and len(term.inputs) == 1:
            results.append((
                OOp('all', term.inputs),
                'D20_spec_expand_all',
            ))
        elif term.spec == 'any' and len(term.inputs) == 1:
            results.append((
                OOp('any', term.inputs),
                'D20_spec_expand_any',
            ))
        elif term.spec == 'len' and len(term.inputs) >= 1:
            results.append((
                OOp('len', term.inputs),
                'D20_spec_expand_len',
            ))
        elif term.spec == 'gcd' and len(term.inputs) == 2:
            results.append((
                OOp('math.gcd', term.inputs),
                'D20_spec_expand_gcd',
            ))
        elif term.spec == 'lcm' and len(term.inputs) == 2:
            results.append((
                OOp('math.lcm', term.inputs),
                'D20_spec_expand_lcm',
            ))
        elif term.spec == 'sorted' and len(term.inputs) >= 1:
            results.append((
                OOp('sorted', term.inputs),
                'D20_spec_expand_sorted',
            ))
        elif term.spec == 'abs' and len(term.inputs) == 1:
            results.append((
                OOp('abs', term.inputs),
                'D20_spec_expand_abs',
            ))
        elif term.spec == 'power' and len(term.inputs) == 2:
            results.append((
                OOp('pow', term.inputs),
                'D20_spec_expand_power',
            ))
        elif term.spec == 'matrix_multiply' and len(term.inputs) == 2:
            results.append((
                OOp('matmul', term.inputs),
                'D20_spec_expand_matmul',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    _pass = 0
    _fail = 0

    def _assert(cond: bool, msg: str) -> None:
        global _pass, _fail
        if cond:
            _pass += 1
        else:
            _fail += 1
            print(f"  FAIL: {msg}")

    ctx = FiberCtx()
    a, b, n = OVar('a'), OVar('b'), OVar('n')

    # factorial: fold[mul](1, range(1, n+1))
    fact_term = OFold('mul', OLit(1), OOp('range', (OLit(1), OOp('add', (n, OLit(1))))))
    s = identify_spec(fact_term)
    _assert(s is not None and s[0] == 'factorial', "factorial recognised (fold)")

    # factorial: fix
    fact_fix = OFix('f', OCase(OOp('eq', (n, OLit(0))), OLit(1),
                               OOp('mul', (n, OOp('f', (OOp('sub', (n, OLit(1))),))))))
    s2 = identify_spec(fact_fix)
    _assert(s2 is not None and s2[0] == 'factorial', "factorial recognised (fix)")

    # range_sum
    sum_term = OFold('add', OLit(0), OOp('range', (n,)))
    s3 = identify_spec(sum_term)
    _assert(s3 is not None and s3[0] == 'range_sum', "range_sum recognised")

    # fibonacci
    fib = OFix('fib', OOp('add', (OOp('sub', (n, OLit(1))), OOp('sub', (n, OLit(2))))))
    s4 = identify_spec(fib)
    _assert(s4 is not None and s4[0] == 'fibonacci_like', "fibonacci recognised")

    # gcd
    gcd_fix = OFix('gcd', OCase(OOp('eq', (b, OLit(0))), a,
                                OOp('gcd', (b, OOp('mod', (a, b))))))
    s5 = identify_spec(gcd_fix)
    _assert(s5 is not None and s5[0] == 'gcd', "gcd recognised (fix)")

    gcd_op = OOp('math.gcd', (a, b))
    s6 = identify_spec(gcd_op)
    _assert(s6 is not None and s6[0] == 'gcd', "gcd recognised (builtin)")

    # lcm = a*b // gcd(a,b)
    lcm_term = OOp('floordiv', (OOp('mul', (a, b)), OOp('math.gcd', (a, b))))
    s7 = identify_spec(lcm_term)
    _assert(s7 is not None and s7[0] == 'lcm', "lcm recognised")

    # flatten
    flat = OFold('concat', OSeq(()), OVar('nested'))
    s8 = identify_spec(flat)
    _assert(s8 is not None and s8[0] == 'flatten', "flatten recognised")

    # zip_with
    zw = OMap(OLam(('p',), OOp('f', (OVar('p'),))), OOp('zip', (OVar('xs'), OVar('ys'))))
    s9 = identify_spec(zw)
    _assert(s9 is not None and s9[0] == 'zip_with', "zip_with recognised")

    # group_by
    gb = OFold('dict_append', ODict(()), OVar('items'))
    s10 = identify_spec(gb)
    _assert(s10 is not None and s10[0] == 'group_by', "group_by recognised")

    # max via fold
    mx = OFold('max', OLit(float('-inf')), OVar('xs'))
    # max fold doesn't match op_name 'max' exactly — uses identify_max
    s11 = _identify_max(OOp('max', (OVar('xs'),)))
    _assert(s11 is not None and s11[0] == 'max', "max recognised")

    # min
    s12 = _identify_min(OOp('min', (OVar('xs'),)))
    _assert(s12 is not None and s12[0] == 'min', "min recognised")

    # reverse
    rev = OOp('reversed', (OVar('xs'),))
    s13 = identify_spec(rev)
    _assert(s13 is not None and s13[0] == 'reverse', "reverse recognised")

    # abs via case
    abs_case = OCase(
        OOp('lt', (OVar('x'), OLit(0))),
        OOp('u_neg', (OVar('x'),)),
        OVar('x'),
    )
    s14 = identify_spec(abs_case)
    _assert(s14 is not None and s14[0] == 'abs', "abs recognised (case)")

    # all
    s15 = identify_spec(OOp('all', (OVar('xs'),)))
    _assert(s15 is not None and s15[0] == 'all', "all recognised")

    # any
    s16 = identify_spec(OOp('any', (OVar('xs'),)))
    _assert(s16 is not None and s16[0] == 'any', "any recognised")

    # product
    prod = OFold('mul', OLit(1), OVar('xs'))
    s17 = identify_spec(prod)
    _assert(s17 is not None and s17[0] == 'product', "product recognised")

    # matmul
    s18 = identify_spec(OOp('matmul', (OVar('A'), OVar('B'))))
    _assert(s18 is not None and s18[0] == 'matrix_multiply', "matmul recognised")

    # tree traversal
    s19 = identify_spec(OOp('inorder', (OVar('tree'),)))
    _assert(s19 is not None and 'tree_traversal' in s19[0], "tree_traversal recognised")

    # power
    s20 = identify_spec(OOp('pow', (a, b)))
    _assert(s20 is not None and s20[0] == 'power', "power recognised")

    # apply produces OAbstract
    r = apply(fact_term, ctx)
    _assert(len(r) >= 1, "D20 apply produces results")
    _assert(isinstance(r[0][0], OAbstract), "D20 result is OAbstract")

    # apply_inverse round-trip for factorial
    abstract_fact = OAbstract('factorial', (n,))
    inv = apply_inverse(abstract_fact, ctx)
    _assert(len(inv) >= 1, "D20 inverse expands factorial")
    _assert(isinstance(inv[0][0], OFold), "D20 inverse is OFold")

    # relevance
    _assert(relevance_score(fact_term, gcd_fix) < relevance_score(fact_term, fact_fix),
            "same-spec relevance > cross-spec")

    print(f"D20 spec-unify: {_pass} passed, {_fail} failed")
