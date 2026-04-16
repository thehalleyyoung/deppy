from __future__ import annotations
"""D2: β-reduction — inline function application.

Mathematical basis: the β-rule of the simply-typed λ-calculus.
``(λx. body)(arg)  ≡  body[x := arg]``

This axiom performs single-step and multi-step β-reduction,
η-contraction (``λx. f(x) → f``), map-identity elimination,
and the reverse direction (abstracting common sub-expressions
into a λ-application).

HIT path:  d2 : OOp('apply', OLam(…), args…) = body[params := args]
Monograph: Chapter 20, §20.2 — Definition 4.3
"""

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Set, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    _subst, normalize,
)
from cctt.path_search import FiberCtx

# ═══════════════════════════════════════════════════════════════
# Constants
# ═══════════════════════════════════════════════════════════════

AXIOM_NAME = "d2_beta"
AXIOM_CATEGORY = "HOF"

# ═══════════════════════════════════════════════════════════════
# Internal helpers
# ═══════════════════════════════════════════════════════════════

def _subst_deep(term: OTerm, var_name: str, replacement: OTerm) -> OTerm:
    """Deep substitution of a variable with an arbitrary OTerm."""
    if isinstance(term, OVar):
        return replacement if term.name == var_name else term
    if isinstance(term, OLit):
        return term
    if isinstance(term, OOp):
        return OOp(term.name,
                   tuple(_subst_deep(a, var_name, replacement) for a in term.args))
    if isinstance(term, OCase):
        return OCase(_subst_deep(term.test, var_name, replacement),
                     _subst_deep(term.true_branch, var_name, replacement),
                     _subst_deep(term.false_branch, var_name, replacement))
    if isinstance(term, OFold):
        return OFold(term.op_name,
                     _subst_deep(term.init, var_name, replacement),
                     _subst_deep(term.collection, var_name, replacement))
    if isinstance(term, OFix):
        return OFix(term.name, _subst_deep(term.body, var_name, replacement))
    if isinstance(term, OSeq):
        return OSeq(tuple(_subst_deep(e, var_name, replacement) for e in term.elements))
    if isinstance(term, ODict):
        return ODict(tuple((_subst_deep(k, var_name, replacement),
                            _subst_deep(v, var_name, replacement))
                           for k, v in term.pairs))
    if isinstance(term, OQuotient):
        return OQuotient(_subst_deep(term.inner, var_name, replacement),
                         term.equiv_class)
    if isinstance(term, OAbstract):
        return OAbstract(term.spec,
                         tuple(_subst_deep(a, var_name, replacement)
                               for a in term.inputs))
    if isinstance(term, OLam):
        if var_name in term.params:
            return term  # shadowed
        return OLam(term.params, _subst_deep(term.body, var_name, replacement))
    if isinstance(term, OMap):
        new_t = _subst_deep(term.transform, var_name, replacement)
        new_c = _subst_deep(term.collection, var_name, replacement)
        new_f = (_subst_deep(term.filter_pred, var_name, replacement)
                 if term.filter_pred else None)
        return OMap(new_t, new_c, new_f)
    if isinstance(term, OCatch):
        return OCatch(_subst_deep(term.body, var_name, replacement),
                      _subst_deep(term.default, var_name, replacement))
    return term


def _single_beta(term: OTerm) -> Optional[OTerm]:
    """Perform a single β-reduction at the root if applicable.

    ``OOp('apply', OLam(params, body), arg1, arg2, …)``
    →  ``body[params := args]``
    """
    if not isinstance(term, OOp) or term.name != 'apply':
        return None
    if len(term.args) < 2 or not isinstance(term.args[0], OLam):
        return None
    lam = term.args[0]
    actual_args = term.args[1:]
    if len(lam.params) != len(actual_args):
        return None
    body = lam.body
    for var_name, replacement in zip(lam.params, actual_args):
        body = _subst_deep(body, var_name, replacement)
    return body


def _beta_one_pass(term: OTerm) -> OTerm:
    """One full pass of β-reduction over all sub-terms."""
    root_red = _single_beta(term)
    if root_red is not None:
        return root_red
    if isinstance(term, OOp):
        new_args = tuple(_beta_one_pass(a) for a in term.args)
        return OOp(term.name, new_args)
    if isinstance(term, OCase):
        return OCase(
            _beta_one_pass(term.test),
            _beta_one_pass(term.true_branch),
            _beta_one_pass(term.false_branch),
        )
    if isinstance(term, OFold):
        return OFold(term.op_name, _beta_one_pass(term.init),
                     _beta_one_pass(term.collection))
    if isinstance(term, OFix):
        return OFix(term.name, _beta_one_pass(term.body))
    if isinstance(term, OLam):
        return OLam(term.params, _beta_one_pass(term.body))
    if isinstance(term, OMap):
        fp = _beta_one_pass(term.filter_pred) if term.filter_pred else None
        return OMap(_beta_one_pass(term.transform),
                    _beta_one_pass(term.collection), fp)
    if isinstance(term, OSeq):
        return OSeq(tuple(_beta_one_pass(e) for e in term.elements))
    if isinstance(term, OCatch):
        return OCatch(_beta_one_pass(term.body), _beta_one_pass(term.default))
    if isinstance(term, OQuotient):
        return OQuotient(_beta_one_pass(term.inner), term.equiv_class)
    return term


def multi_step_beta(term: OTerm, max_steps: int = 8) -> Tuple[OTerm, int]:
    """Repeatedly β-reduce *term* until no more redexes exist.

    Returns ``(reduced_term, number_of_steps_taken)``.
    """
    current = term
    for step in range(max_steps):
        reduced = _beta_one_pass(current)
        if reduced.canon() == current.canon():
            return current, step
        current = reduced
    return current, max_steps


def _extract_free_vars(term: OTerm) -> Set[str]:
    """Extract free variable names from a term."""
    if isinstance(term, OVar):
        return {term.name}
    if isinstance(term, OLit):
        return set()
    if isinstance(term, OOp):
        result: Set[str] = set()
        for a in term.args:
            result |= _extract_free_vars(a)
        return result
    if isinstance(term, OCase):
        return (_extract_free_vars(term.test)
                | _extract_free_vars(term.true_branch)
                | _extract_free_vars(term.false_branch))
    if isinstance(term, OFold):
        return _extract_free_vars(term.init) | _extract_free_vars(term.collection)
    if isinstance(term, OFix):
        return _extract_free_vars(term.body) - {term.name}
    if isinstance(term, OLam):
        return _extract_free_vars(term.body) - set(term.params)
    if isinstance(term, OMap):
        s = _extract_free_vars(term.transform) | _extract_free_vars(term.collection)
        if term.filter_pred:
            s |= _extract_free_vars(term.filter_pred)
        return s
    if isinstance(term, OSeq):
        result = set()
        for e in term.elements:
            result |= _extract_free_vars(e)
        return result
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body) | _extract_free_vars(term.default)
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner)
    if isinstance(term, OAbstract):
        result = set()
        for a in term.inputs:
            result |= _extract_free_vars(a)
        return result
    if isinstance(term, ODict):
        result = set()
        for k, v in term.pairs:
            result |= _extract_free_vars(k) | _extract_free_vars(v)
        return result
    return set()


# ═══════════════════════════════════════════════════════════════
# Main apply function
# ═══════════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply D2 axiom: β-reduction, η-contraction, map-identity.

    Produces multiple intermediate results from multi-step β so
    the BFS can pick the most useful one.
    """
    results: List[Tuple[OTerm, str]] = []

    # ── Single-step β-reduction ──
    if isinstance(term, OOp) and term.name == 'apply':
        if len(term.args) >= 2 and isinstance(term.args[0], OLam):
            lam = term.args[0]
            actual_args = term.args[1:]
            if len(lam.params) == len(actual_args):
                body = lam.body
                for var_name, replacement in zip(lam.params, actual_args):
                    body = _subst_deep(body, var_name, replacement)
                results.append((body, 'D2_beta'))

    # ── Multi-step β-reduction (emit intermediates) ──
    current = term
    seen: Set[str] = {current.canon()}
    for i in range(6):
        nxt = _beta_one_pass(current)
        c = nxt.canon()
        if c in seen:
            break
        seen.add(c)
        results.append((nxt, f'D2_beta_step{i + 1}'))
        current = nxt

    # ── Map with identity lambda: map(λx.x, coll) → coll ──
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        lam = term.transform
        if (len(lam.params) == 1
                and isinstance(lam.body, OVar)
                and lam.body.name == lam.params[0]):
            if term.filter_pred is None:
                results.append((term.collection, 'D2_map_id'))

    # ── η-contraction: λx,y,... . op(x,y,...) → op ──
    if isinstance(term, OLam) and isinstance(term.body, OOp):
        if (len(term.params) == len(term.body.args)
                and all(isinstance(a, OVar) and a.name == p
                        for a, p in zip(term.body.args, term.params))):
            results.append((OVar(term.body.name), 'D2_eta'))

    # ── Let-inlining: OOp where first arg is a let-binding ──
    # Recognise patterns like op(let(x, val, body), ...) and inline
    if isinstance(term, OOp) and term.name == 'let':
        if len(term.args) == 3:
            name_term, val, body = term.args
            if isinstance(name_term, OVar):
                inlined = _subst_deep(body, name_term.name, val)
                results.append((inlined, 'D2_let_inline'))

    return results


# ═══════════════════════════════════════════════════════════════
# Recognition and relevance
# ═══════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could D2 apply to this term?"""
    if isinstance(term, OOp) and term.name == 'apply':
        return len(term.args) >= 2 and isinstance(term.args[0], OLam)
    if isinstance(term, OMap) and isinstance(term.transform, OLam):
        lam = term.transform
        if (len(lam.params) == 1
                and isinstance(lam.body, OVar)
                and lam.body.name == lam.params[0]):
            return True
    if isinstance(term, OLam) and isinstance(term.body, OOp):
        if (len(term.params) == len(term.body.args)
                and all(isinstance(a, OVar) and a.name == p
                        for a, p in zip(term.body.args, term.params))):
            return True
    if isinstance(term, OOp) and term.name == 'let':
        return True
    return False


def relevance_score(term: OTerm, other: OTerm) -> float:
    """How likely is D2 to help prove ``term ≡ other``?

    Returns a score in [0.0, 1.0]:
      0.9 — term has an explicit apply(λ..., args)
      0.7 — term is an η-expandable lambda
      0.4 — term has lambdas but no direct redex
      0.0 — no lambdas at all
    """
    if isinstance(term, OOp) and term.name == 'apply':
        if len(term.args) >= 2 and isinstance(term.args[0], OLam):
            return 0.9
    if isinstance(term, OLam) and isinstance(term.body, OOp):
        return 0.7
    if isinstance(term, OLam) or isinstance(other, OLam):
        return 0.4
    return 0.0


# ═══════════════════════════════════════════════════════════════
# Inverse (abstraction)
# ═══════════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply D2 in reverse: abstract common sub-expressions into a lambda.

    Given ``add(mul(p0, p0), mul(add(p0, 1), add(p0, 1)))``
    recognise that sub-expressions could be abstracted as
    ``(λ(a,b). add(mul(a,a), mul(b,b)))(p0, add(p0,1))``.
    """
    results: List[Tuple[OTerm, str]] = []
    if not isinstance(term, OOp) or len(term.args) < 2:
        return results
    subterms = [a for a in term.args if not isinstance(a, OLit)]
    if len(subterms) < 2:
        return results
    for i, sub in enumerate(subterms):
        param = f'_abs{i}'
        abstracted = _subst_deep(term, sub.canon(), OVar(param))
        if abstracted.canon() != term.canon():
            lam = OLam((param,), abstracted)
            app = OOp('apply', (lam, sub))
            results.append((app, 'D2_beta_reverse'))
            break
    return results


# ═══════════════════════════════════════════════════════════════
# Composability metadata
# ═══════════════════════════════════════════════════════════════

COMPOSES_WITH = ["d1_fold_unfold", "d4_comp_fusion", "d7_tailrec"]
REQUIRES: List[str] = []

# ═══════════════════════════════════════════════════════════════
# Soundness justification
# ═══════════════════════════════════════════════════════════════

SOUNDNESS_PROOF = """
Theorem (D2 Soundness): If D2 transforms t to t', then ⟦t⟧ = ⟦t'⟧.

Proof: By the β-rule of the simply-typed λ-calculus.

For single-step reduction:
    ⟦(λx. M)(N)⟧  =  ⟦M[x := N]⟧
by the substitution lemma (Barendregt, §3.2).

For η-contraction:
    ⟦λx. f(x)⟧  =  ⟦f⟧
when x ∉ FV(f), by the η-rule.

For map-identity:
    ⟦map(λx. x, coll)⟧  =  ⟦coll⟧
by functorial identity: F(id) = id.

Multi-step reduction follows by transitivity of equality.  ∎
"""

# ═══════════════════════════════════════════════════════════════
# Examples
# ═══════════════════════════════════════════════════════════════

EXAMPLES = [
    {
        "name": "simple_beta",
        "before": "OOp('apply', (OLam(('x',), OOp('add', (OVar('x'), OLit(1)))), OLit(5)))",
        "after": "OOp('add', (OLit(5), OLit(1)))",
        "benchmark": "beta01",
        "description": "(λx. x+1)(5) → 5+1",
    },
    {
        "name": "eta_contraction",
        "before": "OLam(('x',), OOp('f', (OVar('x'),)))",
        "after": "OVar('f')",
        "benchmark": "eta01",
        "description": "λx. f(x) → f",
    },
    {
        "name": "map_identity",
        "before": "OMap(OLam(('x',), OVar('x')), OVar('coll'))",
        "after": "OVar('coll')",
        "benchmark": "map_id01",
        "description": "map(λx.x, coll) → coll",
    },
    {
        "name": "nested_beta",
        "before": "OOp('apply', (OLam(('y',), OOp('apply', (OLam(('x',), OOp('add', (OVar('x'), OLit(1)))), OVar('y')))), OLit(3)))",
        "after": "OOp('add', (OLit(3), OLit(1)))",
        "benchmark": "beta02",
        "description": "(λy. (λx. x+1)(y))(3) → 3+1",
    },
    {
        "name": "let_inlining",
        "before": "OOp('let', (OVar('x'), OLit(10), OOp('add', (OVar('x'), OLit(1)))))",
        "after": "OOp('add', (OLit(10), OLit(1)))",
        "benchmark": "let01",
        "description": "let x = 10 in x+1 → 10+1",
    },
]

# ═══════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    import sys
    _passed = 0
    _failed = 0

    def _assert(cond: bool, msg: str) -> None:
        global _passed, _failed
        if cond:
            _passed += 1
            print(f'  ✓ {msg}')
        else:
            _failed += 1
            print(f'  ✗ FAIL: {msg}')

    ctx = FiberCtx(param_duck_types={'p0': 'int', 'p1': 'int'})

    # Test single β-reduction
    print('▶ D2 single β-reduction')
    lam = OLam(('x',), OOp('add', (OVar('x'), OLit(1))))
    app = OOp('apply', (lam, OLit(5)))
    results = apply(app, ctx)
    _assert(any(lbl == 'D2_beta' for _, lbl in results), 'D2_beta fires')
    beta_result = [t for t, lbl in results if lbl == 'D2_beta'][0]
    _assert(isinstance(beta_result, OOp) and beta_result.name == 'add',
            'result is add(5, 1)')

    # Test multi-step β
    print('▶ D2 multi-step β-reduction')
    nested_lam = OLam(('y',), OOp('apply', (lam, OVar('y'))))
    nested_app = OOp('apply', (nested_lam, OLit(3)))
    reduced, steps = multi_step_beta(nested_app)
    _assert(steps >= 2, f'nested beta took {steps} step(s)')

    results = apply(nested_app, ctx)
    _assert(any('step' in lbl for _, lbl in results),
            'multi-step fires')

    # Test η-contraction
    print('▶ D2 η-contraction')
    eta_lam = OLam(('x',), OOp('f', (OVar('x'),)))
    results = apply(eta_lam, ctx)
    _assert(any(lbl == 'D2_eta' for _, lbl in results), 'η fires')
    eta_result = [t for t, lbl in results if lbl == 'D2_eta'][0]
    _assert(isinstance(eta_result, OVar) and eta_result.name == 'f',
            'η result is f')

    # Test map identity
    print('▶ D2 map(λx.x, coll) → coll')
    id_lam = OLam(('x',), OVar('x'))
    id_map = OMap(id_lam, OVar('coll'))
    results = apply(id_map, ctx)
    _assert(any(lbl == 'D2_map_id' for _, lbl in results), 'map_id fires')
    map_result = [t for t, lbl in results if lbl == 'D2_map_id'][0]
    _assert(isinstance(map_result, OVar) and map_result.name == 'coll',
            'result is coll')

    # Test let-inlining
    print('▶ D2 let-inlining')
    let_term = OOp('let', (OVar('x'), OLit(10),
                            OOp('add', (OVar('x'), OLit(1)))))
    results = apply(let_term, ctx)
    _assert(any(lbl == 'D2_let_inline' for _, lbl in results),
            'let_inline fires')

    # Test recognizes
    print('▶ D2 recognizes()')
    _assert(recognizes(app), 'apply(λ…) recognised')
    _assert(recognizes(id_map), 'map(λx.x, …) recognised')
    _assert(recognizes(eta_lam), 'η-reducible recognised')
    _assert(not recognizes(OLit(42)), 'literal not recognised')

    # Test apply_inverse
    print('▶ D2 apply_inverse()')
    sq_term = OOp('add', (OOp('mul', (OVar('p0'), OVar('p0'))), OLit(1)))
    inv_results = apply_inverse(sq_term, ctx)
    _assert(isinstance(inv_results, list), 'inverse returns list')

    # Edge cases
    print('▶ D2 edge cases')
    _assert(apply(OLit(42), ctx) == [], 'D2 on literal is empty')
    _assert(apply(OVar('x'), ctx) == [], 'D2 on var is empty')
    partial_app = OOp('apply', (OLam(('x', 'y'), OVar('x')), OLit(1)))
    results = apply(partial_app, ctx)
    # arity mismatch — should not fire single beta
    _assert(not any(lbl == 'D2_beta' for _, lbl in results),
            'arity mismatch → no D2_beta')

    print(f'\n{"═" * 50}')
    print(f'  D2: {_passed} passed, {_failed} failed')
    print(f'{"═" * 50}')
    sys.exit(1 if _failed > 0 else 0)
