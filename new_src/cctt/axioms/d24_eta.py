"""D24: η-Reduction Axiom — Lambda ↔ Named Function.

§23.4 of the CCTT monograph.  Theorem 23.4.1:
η-expansion/contraction: λx.f(x) ≡ f when f does not capture x.

Key rewrites:
  • λx. f(x) → f                        [single-arg η-contraction]
  • λ(x,y,...). f(x,y,...) → f          [multi-arg η-contraction]
  • λ(x,y). f(x, y, CONST) → partial(f, CONST)  [partial application]
  • λx. g(f(x)) → compose(g, f)         [composition detection]
  • f → λx. f(x)                        [η-expansion, inverse]
  • λx. x → id                          [identity function]
  • λx. CONST → const(CONST)            [constant function]
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "D24_eta"
AXIOM_CATEGORY = "language_feature"

SOUNDNESS_PROOF = r"""
Theorem 23.4.1 (η-Reduction).
In any cartesian closed category (CCC):
    λx. f(x) = f   when x ∉ FV(f)
This is the η-law for function types.

Multi-argument: λ(x₁,...,xₙ). f(x₁,...,xₙ) = f by iterated η.

Composition: λx. g(f(x)) = g ∘ f by the universal property of
composition in a CCC.

Partial application: λ(x₁,...,xₖ). f(x₁,...,xₖ, c₁,...,cₘ)
= partial(f, c₁,...,cₘ) is the currying isomorphism
Hom(A×B, C) ≅ Hom(A, C^B) applied to the constants.
"""

COMPOSES_WITH = ["ALG", "D20_spec", "FOLD"]
REQUIRES: List[str] = []

EXAMPLES = [
    ("λ(x).f(x)", "f()", "D24_eta_contract"),
    ("λ(x,y).f(x,y)", "f()", "D24_eta_contract_multi"),
    ("λ(x).g(f(x))", "compose(g(), f())", "D24_eta_compose"),
    ("λ(x).x", "id()", "D24_eta_identity"),
    ("λ(x).42", "const(42)", "D24_eta_constant"),
]


def _extract_free_vars(term: OTerm, bound: Optional[Set[str]] = None) -> Set[str]:
    """Extract free variables from a term, excluding bound variables."""
    if bound is None:
        bound = set()
    if isinstance(term, OVar):
        return {term.name} - bound
    if isinstance(term, (OLit, OUnknown)):
        return set()
    if isinstance(term, OOp):
        r: Set[str] = set()
        for a in term.args:
            r |= _extract_free_vars(a, bound)
        return r
    if isinstance(term, OLam):
        return _extract_free_vars(term.body, bound | set(term.params))
    if isinstance(term, OCase):
        return (_extract_free_vars(term.test, bound)
                | _extract_free_vars(term.true_branch, bound)
                | _extract_free_vars(term.false_branch, bound))
    if isinstance(term, OFold):
        return _extract_free_vars(term.init, bound) | _extract_free_vars(term.collection, bound)
    if isinstance(term, OFix):
        return _extract_free_vars(term.body, bound)
    if isinstance(term, OSeq):
        r2: Set[str] = set()
        for e in term.elements:
            r2 |= _extract_free_vars(e, bound)
        return r2
    if isinstance(term, OMap):
        r3 = _extract_free_vars(term.transform, bound) | _extract_free_vars(term.collection, bound)
        if term.filter_pred:
            r3 |= _extract_free_vars(term.filter_pred, bound)
        return r3
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner, bound)
    if isinstance(term, OAbstract):
        r4: Set[str] = set()
        for a in term.inputs:
            r4 |= _extract_free_vars(a, bound)
        return r4
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body, bound) | _extract_free_vars(term.default, bound)
    if isinstance(term, ODict):
        r5: Set[str] = set()
        for k, v in term.pairs:
            r5 |= _extract_free_vars(k, bound) | _extract_free_vars(v, bound)
        return r5
    return set()


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D24 η-reduction rewrites to *term*."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OLam):
        # η-expansion for non-lambda named ops
        if isinstance(term, OOp) and len(term.args) == 0:
            results.append((
                OLam(('_x',), OOp(term.name, (OVar('_x'),))),
                'D24_eta_expand',
            ))
        return results

    # ── 1. Identity: λx. x → id ──
    if len(term.params) == 1:
        if isinstance(term.body, OVar) and term.body.name == term.params[0]:
            results.append((
                OOp('id', ()),
                'D24_eta_identity',
            ))

    # ── 2. Constant function: λx. CONST → const(CONST) ──
    if len(term.params) >= 1:
        body_fv = _extract_free_vars(term.body, set(term.params))
        param_set = set(term.params)
        # Body uses none of the params → constant function
        body_uses_params = bool(_extract_free_vars(term.body) & param_set)
        if not body_uses_params:
            results.append((
                OOp('const', (term.body,)),
                'D24_eta_constant',
            ))

    # ── 3. Single/multi-arg η-contraction: λ(x,...). f(x,...) → f ──
    if isinstance(term.body, OOp):
        body_op = term.body
        if len(body_op.args) == len(term.params):
            all_match = all(
                isinstance(a, OVar) and a.name == p
                for a, p in zip(body_op.args, term.params)
            )
            if all_match:
                label = 'D24_eta_contract' if len(term.params) == 1 else 'D24_eta_contract_multi'
                results.append((
                    OOp(body_op.name, ()),
                    label,
                ))

    # ── 4. Partial application: λ(x,...). f(x,..., CONST,...) ──
    if isinstance(term.body, OOp) and len(term.body.args) > len(term.params):
        body_op = term.body
        param_set = set(term.params)
        forwarded: List[int] = []
        constants: List[Tuple[int, OTerm]] = []
        param_idx = 0
        valid = True
        for i, arg in enumerate(body_op.args):
            if isinstance(arg, OVar) and arg.name in param_set:
                if param_idx < len(term.params) and arg.name == term.params[param_idx]:
                    forwarded.append(i)
                    param_idx += 1
                else:
                    valid = False
                    break
            else:
                constants.append((i, arg))

        if valid and param_idx == len(term.params) and constants:
            const_terms = tuple(c[1] for c in constants)
            results.append((
                OOp('partial', (OOp(body_op.name, ()), *const_terms)),
                'D24_eta_partial',
            ))

    # ── 5. Composition: λx. g(f(x)) → compose(g, f) ──
    if len(term.params) == 1:
        x = term.params[0]
        if isinstance(term.body, OOp) and len(term.body.args) == 1:
            inner = term.body.args[0]
            if isinstance(inner, OOp) and len(inner.args) == 1:
                if isinstance(inner.args[0], OVar) and inner.args[0].name == x:
                    results.append((
                        OOp('compose', (OOp(term.body.name, ()), OOp(inner.name, ()))),
                        'D24_eta_compose',
                    ))

    # ── 6. Map-lambda fusion: λx. f(g(x)) where both are known ──
    if len(term.params) == 1:
        x = term.params[0]
        if isinstance(term.body, OOp) and len(term.body.args) == 1:
            inner = term.body.args[0]
            # λx. f(x+1) is NOT η-reducible but IS recognisable
            if isinstance(inner, OOp) and len(inner.args) == 2:
                if (isinstance(inner.args[0], OVar) and inner.args[0].name == x
                        and isinstance(inner.args[1], OLit)):
                    # λx. f(op(x, c)) → compose(f, partial(op, c))
                    results.append((
                        OOp('compose', (
                            OOp(term.body.name, ()),
                            OOp('partial', (OOp(inner.name, ()), inner.args[1])),
                        )),
                        'D24_eta_compose_partial',
                    ))

    # ── 7. Double lambda collapse: λx. (λy. body)(x) → λy. body ──
    if len(term.params) == 1:
        x = term.params[0]
        if isinstance(term.body, OOp) and term.body.name == '__call__':
            if len(term.body.args) == 2:
                fn, arg = term.body.args
                if isinstance(fn, OLam) and isinstance(arg, OVar) and arg.name == x:
                    results.append((fn, 'D24_beta_reduce'))

    return results


def recognizes(term: OTerm) -> bool:
    """Return True if D24 can potentially rewrite *term*."""
    if isinstance(term, OLam):
        return True
    if isinstance(term, OOp) and len(term.args) == 0:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D24's relevance for bridging *source* → *target*."""
    sc = source.canon()
    tc = target.canon()
    s_lam = 'λ(' in sc
    t_lam = 'λ(' in tc
    if s_lam != t_lam:
        return 0.8
    if s_lam and t_lam:
        return 0.4
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse: η-expand or decompose compositions."""
    results: List[Tuple[OTerm, str]] = []

    # f → λx. f(x)
    if isinstance(term, OOp) and len(term.args) == 0:
        results.append((
            OLam(('_x',), OOp(term.name, (OVar('_x'),))),
            'D24_eta_expand_inv',
        ))

    # compose(g, f) → λx. g(f(x))
    if isinstance(term, OOp) and term.name == 'compose' and len(term.args) == 2:
        g, f = term.args
        if isinstance(g, OOp) and isinstance(f, OOp):
            results.append((
                OLam(('_x',), OOp(g.name, (OOp(f.name, (OVar('_x'),)),))),
                'D24_compose_to_lambda',
            ))

    # id → λx. x
    if isinstance(term, OOp) and term.name == 'id' and len(term.args) == 0:
        results.append((
            OLam(('_x',), OVar('_x')),
            'D24_id_to_lambda',
        ))

    # const(v) → λx. v
    if isinstance(term, OOp) and term.name == 'const' and len(term.args) == 1:
        results.append((
            OLam(('_x',), term.args[0]),
            'D24_const_to_lambda',
        ))

    # partial(f, c) → λx. f(x, c)
    if isinstance(term, OOp) and term.name == 'partial' and len(term.args) >= 2:
        fn = term.args[0]
        consts = term.args[1:]
        if isinstance(fn, OOp):
            results.append((
                OLam(('_x',), OOp(fn.name, (OVar('_x'),) + consts)),
                'D24_partial_to_lambda',
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

    # Single-arg η-contraction
    t1 = OLam(('x',), OOp('f', (OVar('x'),)))
    r1 = apply(t1, ctx)
    _assert(any(a == 'D24_eta_contract' for _, a in r1), "single-arg η-contract")

    # Multi-arg η-contraction
    t2 = OLam(('x', 'y'), OOp('f', (OVar('x'), OVar('y'))))
    r2 = apply(t2, ctx)
    _assert(any(a == 'D24_eta_contract_multi' for _, a in r2), "multi-arg η-contract")

    # Composition detection: λx. g(f(x)) → compose(g, f)
    t3 = OLam(('x',), OOp('g', (OOp('f', (OVar('x'),)),)))
    r3 = apply(t3, ctx)
    _assert(any(a == 'D24_eta_compose' for _, a in r3), "composition detection")

    # Non-η case: λx. f(x, 1) should NOT η-contract
    t4 = OLam(('x',), OOp('add', (OVar('x'), OLit(1))))
    r4 = apply(t4, ctx)
    _assert(not any(a == 'D24_eta_contract' for _, a in r4), "non-η not contracted")

    # Identity: λx. x → id
    t5 = OLam(('x',), OVar('x'))
    r5 = apply(t5, ctx)
    _assert(any(a == 'D24_eta_identity' for _, a in r5), "identity detection")

    # Constant: λx. 42 → const(42)
    t6 = OLam(('x',), OLit(42))
    r6 = apply(t6, ctx)
    _assert(any(a == 'D24_eta_constant' for _, a in r6), "constant detection")

    # Partial application: λx. f(x, 1, 2)
    t7 = OLam(('x',), OOp('f', (OVar('x'), OLit(1), OLit(2))))
    r7 = apply(t7, ctx)
    _assert(any(a == 'D24_eta_partial' for _, a in r7), "partial application")

    # η-expansion inverse
    t8 = OOp('f', ())
    r8 = apply_inverse(t8, ctx)
    _assert(any(a == 'D24_eta_expand_inv' for _, a in r8), "η-expansion inverse")

    # compose → lambda inverse
    t9 = OOp('compose', (OOp('g', ()), OOp('f', ())))
    r9 = apply_inverse(t9, ctx)
    _assert(any(a == 'D24_compose_to_lambda' for _, a in r9), "compose → lambda")

    # id → lambda inverse
    t10 = OOp('id', ())
    r10 = apply_inverse(t10, ctx)
    _assert(any(a == 'D24_id_to_lambda' for _, a in r10), "id → lambda")

    # const → lambda inverse
    t11 = OOp('const', (OLit(42),))
    r11 = apply_inverse(t11, ctx)
    _assert(any(a == 'D24_const_to_lambda' for _, a in r11), "const → lambda")

    # partial → lambda inverse
    t12 = OOp('partial', (OOp('f', ()), OLit(1)))
    r12 = apply_inverse(t12, ctx)
    _assert(any(a == 'D24_partial_to_lambda' for _, a in r12), "partial → lambda")

    # recognizes
    _assert(recognizes(t1), "recognizes lambda")
    _assert(recognizes(t8), "recognizes zero-arg op")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # relevance
    _assert(relevance_score(t1, t8) > 0.5, "lambda vs op relevance high")

    # compose-partial: λx. f(add(x, 1))
    t13 = OLam(('x',), OOp('f', (OOp('add', (OVar('x'), OLit(1))),)))
    r13 = apply(t13, ctx)
    _assert(any(a == 'D24_eta_compose_partial' for _, a in r13), "compose-partial detection")

    print(f"D24 eta: {_pass} passed, {_fail} failed")
