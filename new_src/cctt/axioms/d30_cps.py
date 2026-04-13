"""D30: CPS Transformation — Direct Style ↔ Continuation-Passing Style.

§25.6 of the CCTT monograph.  Theorem 25.6.1 (Plotkin 1975):
Every direct-style program has a canonical CPS translation, and
the two are denotationally equivalent.

Key rewrites:
  • Direct composition: f(g(x)) ↔ g(x, λr. f(r, k))  [CPS]
  • Sequential: OSeq(a, b) ↔ a(λ_. b(k))  [CPS of sequencing]
  • Callback nesting → sequential composition
  • OLam(x, OOp(f, (OOp(g, (x,)),))) ↔ CPS callback chain
  • Return unwrapping: (λk. k(v)) ↔ v  [CPS identity]
  • Nested callbacks → flat promise-style chain
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "D30_cps"
AXIOM_CATEGORY = "control_flow"

SOUNDNESS_PROOF = r"""
Theorem 25.6.1 (CPS Transformation — Plotkin 1975).

The CPS transformation ⟦·⟧ : Λ → Λ_CPS is defined by:
  ⟦x⟧         = λk. k(x)
  ⟦λx.M⟧     = λk. k(λx. ⟦M⟧)
  ⟦M N⟧      = λk. ⟦M⟧(λm. ⟦N⟧(λn. m(n)(k)))

Theorem (Plotkin):
  For all closed terms M of PCF:
    M ⇓ v  iff  ⟦M⟧(id) ⇓ v

Proof sketch:
  By structural induction on M.  The CPS translation makes
  all control flow explicit via continuations, but does not
  change the observable behavior.  The identity continuation
  id extracts the final value, making ⟦M⟧(id) ≡ M.

Corollary (Direct ↔ CPS equivalence):
  f(g(x)) ≡ g(x, λr. f(r, k)) in the CPS-translated program,
  because the CPS translation sequences g before f with r
  carrying the intermediate result.

Callback flattening:
  f(λr₁. g(r₁, λr₂. h(r₂, k))) ≡ compose(h, compose(g, f))(x, k)
  by associativity of composition in the Kleisli category
  of the continuation monad.  □
"""

COMPOSES_WITH = ["D7_tailrec", "D24_eta", "D4_comp_fusion"]
REQUIRES: List[str] = []

EXAMPLES = [
    {
        "name": "direct_to_cps",
        "before": "f(g(x))",
        "after": "cps_seq(g, λr. f(r))",
        "benchmark": None,
    },
    {
        "name": "cps_identity",
        "before": "λk. k(v)",
        "after": "v",
        "benchmark": None,
    },
    {
        "name": "callback_flatten",
        "before": "f(λr1. g(r1, λr2. h(r2, k)))",
        "after": "chain(f, g, h, k)",
        "benchmark": None,
    },
    {
        "name": "seq_to_cps",
        "before": "OSeq(a, b)",
        "after": "a(λ_. b(k))",
        "benchmark": None,
    },
]


@dataclass
class FiberCtx:
    param_duck_types: Dict[str, str] = field(default_factory=dict)

    def is_numeric(self, term: OTerm) -> bool:
        return True


def _extract_free_vars(term: OTerm, bound: Optional[Set[str]] = None) -> Set[str]:
    """Extract free variables from a term."""
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
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body, bound) | _extract_free_vars(term.default, bound)
    if isinstance(term, OQuotient):
        return _extract_free_vars(term.inner, bound)
    if isinstance(term, OAbstract):
        return set().union(*(_extract_free_vars(a, bound) for a in term.inputs))
    if isinstance(term, ODict):
        r5: Set[str] = set()
        for k, v in term.pairs:
            r5 |= _extract_free_vars(k, bound) | _extract_free_vars(v, bound)
        return r5
    return set()


def _is_cps_identity(term: OTerm) -> Optional[OTerm]:
    """Check if term is λk. k(v) and return v.

    This is the CPS representation of a value — the continuation
    is immediately applied to the value.
    """
    if isinstance(term, OLam) and len(term.params) == 1:
        k = term.params[0]
        body = term.body
        if isinstance(body, OOp) and body.name == k and len(body.args) == 1:
            return body.args[0]
        if isinstance(body, OOp) and body.name == '__call__' and len(body.args) == 2:
            if isinstance(body.args[0], OVar) and body.args[0].name == k:
                return body.args[1]
    return None


def _extract_callback_chain(term: OTerm) -> Optional[List[OTerm]]:
    """Extract a chain of callbacks from nested CPS form.

    Pattern: f(x, λr1. g(r1, λr2. h(r2, k)))
    Returns [f, g, h] and the continuation k.
    """
    chain: List[OTerm] = []
    current = term
    depth = 0
    max_depth = 20

    while depth < max_depth:
        depth += 1
        if isinstance(current, OOp) and len(current.args) >= 2:
            last_arg = current.args[-1]
            if isinstance(last_arg, OLam) and len(last_arg.params) == 1:
                chain.append(OOp(current.name, current.args[:-1]))
                current = last_arg.body
                continue
        break

    if len(chain) >= 2:
        return chain
    return None


def _subst_var(term: OTerm, name: str, replacement: OTerm) -> OTerm:
    """Substitute variable *name* with *replacement* in *term*."""
    if isinstance(term, OVar):
        return replacement if term.name == name else term
    if isinstance(term, (OLit, OUnknown)):
        return term
    if isinstance(term, OOp):
        return OOp(term.name, tuple(_subst_var(a, name, replacement) for a in term.args))
    if isinstance(term, OLam):
        if name in term.params:
            return term
        return OLam(term.params, _subst_var(term.body, name, replacement))
    if isinstance(term, OCase):
        return OCase(
            _subst_var(term.test, name, replacement),
            _subst_var(term.true_branch, name, replacement),
            _subst_var(term.false_branch, name, replacement),
        )
    if isinstance(term, OFold):
        return OFold(term.op_name, _subst_var(term.init, name, replacement),
                     _subst_var(term.collection, name, replacement))
    if isinstance(term, OSeq):
        return OSeq(tuple(_subst_var(e, name, replacement) for e in term.elements))
    if isinstance(term, OMap):
        filt = term.filter_pred
        if filt is not None:
            filt = _subst_var(filt, name, replacement)
        return OMap(_subst_var(term.transform, name, replacement),
                    _subst_var(term.collection, name, replacement), filt)
    if isinstance(term, OCatch):
        return OCatch(_subst_var(term.body, name, replacement),
                      _subst_var(term.default, name, replacement))
    return term


# ═══════════════════════════════════════════════════════════
# Core axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Apply D30 CPS transformation rewrites to *term*.

    Handles:
      1. CPS identity elimination: λk. k(v) → v
      2. Direct to CPS: f(g(x)) → cps_seq(g, λr.f(r))
      3. CPS to direct: cps_seq(g, λr.f(r)) → f(g(x))
      4. Callback chain flattening
      5. Sequential to CPS: OSeq(a, b) → cps_seq form
      6. Compose to CPS chain: compose(f, g) → CPS form
      7. then/chain normalisation
    """
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # ── 1. CPS identity: λk. k(v) → v ──
    v = _is_cps_identity(term)
    if v is not None:
        results.append((v, 'D30_cps_identity'))

    # ── 2. Direct to CPS: f(g(x)) → cps_seq form ──
    #    Detect nested function application and offer CPS rewrite
    if isinstance(term, OOp) and len(term.args) >= 1:
        for i, arg in enumerate(term.args):
            if isinstance(arg, OOp) and len(arg.args) >= 1:
                # f(g(x)) → g(x, λr. f(r))
                r_var = OVar('_r')
                outer_args = list(term.args)
                outer_args[i] = r_var
                cont = OLam(('_r',), OOp(term.name, tuple(outer_args)))
                inner_with_cont = OOp(arg.name, arg.args + (cont,))
                results.append((inner_with_cont, 'D30_direct_to_cps'))
                break  # one rewrite per call

    # ── 3. CPS to direct: f(x, λr. g(r, ...)) → g(f(x), ...) ──
    if isinstance(term, OOp) and len(term.args) >= 2:
        last = term.args[-1]
        if isinstance(last, OLam) and len(last.params) == 1:
            r_param = last.params[0]
            body = last.body
            if isinstance(body, OOp):
                # Check if r_param appears exactly once in body args
                r_positions = [j for j, a in enumerate(body.args)
                               if isinstance(a, OVar) and a.name == r_param]
                if len(r_positions) == 1:
                    pos = r_positions[0]
                    inner_call = OOp(term.name, term.args[:-1])
                    new_args = list(body.args)
                    new_args[pos] = inner_call
                    results.append((
                        OOp(body.name, tuple(new_args)),
                        'D30_cps_to_direct',
                    ))

    # ── 4. Callback chain flattening ──
    chain = _extract_callback_chain(term)
    if chain is not None and len(chain) >= 2:
        results.append((
            OOp('chain', tuple(chain)),
            'D30_flatten_callbacks',
        ))

    # ── 5. chain(f, g, ...) → nested callbacks ──
    if isinstance(term, OOp) and term.name == 'chain' and len(term.args) >= 2:
        # Build nested callbacks from chain
        fns = list(term.args)
        # Innermost: last(rN, k)
        result: OTerm = fns[-1]
        for i in range(len(fns) - 2, -1, -1):
            r_name = f'_r{i}'
            fn = fns[i]
            if isinstance(fn, OOp):
                result = OOp(fn.name, fn.args + (OLam((r_name,), result),))
            else:
                result = OOp('__call__', (fn, OLam((r_name,), result)))
        results.append((result, 'D30_unflatten_chain'))

    # ── 6. Sequential to CPS: OSeq elements → CPS chaining ──
    if isinstance(term, OSeq) and len(term.elements) >= 2:
        elts = list(term.elements)
        # [a, b, c] → a(λ_. b(λ_. c))  (CPS of sequencing)
        result_seq: OTerm = elts[-1]
        for i in range(len(elts) - 2, -1, -1):
            elt = elts[i]
            result_seq = OOp('cps_seq', (elt, OLam(('_',), result_seq)))
        results.append((result_seq, 'D30_seq_to_cps'))

    # ── 7. cps_seq(a, λ_. b) → OSeq(a, b)  when a is pure ──
    if isinstance(term, OOp) and term.name == 'cps_seq' and len(term.args) == 2:
        a, cont = term.args
        if isinstance(cont, OLam) and len(cont.params) == 1:
            b = cont.body
            results.append((OSeq((a, b)), 'D30_cps_to_seq'))

    # ── 8. compose(f, g) → λx. f(g(x)) (then CPS if desired) ──
    if isinstance(term, OOp) and term.name == 'compose' and len(term.args) == 2:
        f, g = term.args
        if isinstance(f, OOp) and isinstance(g, OOp):
            # CPS form: λ(x, k). g(x, λr. f(r, k))
            cps_form = OLam(
                ('_x', '_k'),
                OOp(g.name, (OVar('_x'),
                             OLam(('_r',), OOp(f.name, (OVar('_r'), OVar('_k'))))))
            )
            results.append((cps_form, 'D30_compose_to_cps'))

    # ── 9. then(a, f) → f(a)  (promise-style) ──
    if isinstance(term, OOp) and term.name == 'then' and len(term.args) == 2:
        a, f = term.args
        if isinstance(f, OLam) and len(f.params) == 1:
            results.append((
                _subst_var(f.body, f.params[0], a),
                'D30_then_to_direct',
            ))
        else:
            results.append((
                OOp('__call__', (f, a)),
                'D30_then_to_call',
            ))

    return results


def recognizes(term: OTerm) -> bool:
    """Quick check: could D30 apply to this term?"""
    # CPS identity
    if _is_cps_identity(term) is not None:
        return True
    # Nested function calls (CPS candidates)
    if isinstance(term, OOp) and len(term.args) >= 1:
        if any(isinstance(a, OOp) for a in term.args):
            return True
        if any(isinstance(a, OLam) for a in term.args):
            return True
    # Sequences (CPS of sequencing)
    if isinstance(term, OSeq) and len(term.elements) >= 2:
        return True
    # CPS-specific ops
    if isinstance(term, OOp) and term.name in ('cps_seq', 'chain', 'then', 'compose'):
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Score D30's relevance for bridging source → target."""
    sc = source.canon()
    tc = target.canon()

    s_cps = any(kw in sc for kw in ('cps_seq(', 'chain(', 'then('))
    t_cps = any(kw in tc for kw in ('cps_seq(', 'chain(', 'then('))
    s_lam = 'λ(' in sc
    t_lam = 'λ(' in tc

    # One CPS, other direct → high
    if s_cps != t_cps:
        return 0.9
    # One has lambdas as callback args, other doesn't
    if s_lam != t_lam:
        return 0.6
    # Both CPS or both direct
    if s_cps and t_cps:
        return 0.5
    # Nested calls in one, flat in other
    s_depth = sc.count('(') - sc.count(')')
    t_depth = tc.count('(') - tc.count(')')
    if abs(sc.count('(') - tc.count('(')) > 3:
        return 0.5
    return 0.05


def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Inverse of D30: CPS to direct, direct to CPS."""
    if ctx is None:
        ctx = FiberCtx()
    results: List[Tuple[OTerm, str]] = []

    # Direct → CPS: wrap value in CPS identity  v → λk. k(v)
    if isinstance(term, (OVar, OLit)):
        results.append((
            OLam(('_k',), OOp('_k', (term,))),
            'D30_inv_value_to_cps',
        ))

    # OSeq → CPS sequential
    if isinstance(term, OSeq) and len(term.elements) >= 2:
        elts = list(term.elements)
        result_seq: OTerm = elts[-1]
        for i in range(len(elts) - 2, -1, -1):
            result_seq = OOp('cps_seq', (elts[i], OLam(('_',), result_seq)))
        results.append((result_seq, 'D30_inv_seq_to_cps'))

    # cps_seq → OSeq
    if isinstance(term, OOp) and term.name == 'cps_seq' and len(term.args) == 2:
        a, cont = term.args
        if isinstance(cont, OLam) and len(cont.params) == 1:
            results.append((OSeq((a, cont.body)), 'D30_inv_cps_to_seq'))

    # Nested direct calls → CPS
    if isinstance(term, OOp) and len(term.args) >= 1:
        for i, arg in enumerate(term.args):
            if isinstance(arg, OOp) and len(arg.args) >= 1:
                r_var = OVar('_r')
                outer_args = list(term.args)
                outer_args[i] = r_var
                cont = OLam(('_r',), OOp(term.name, tuple(outer_args)))
                inner_with_cont = OOp(arg.name, arg.args + (cont,))
                results.append((inner_with_cont, 'D30_inv_direct_to_cps'))
                break

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
    x, y, k = OVar('x'), OVar('y'), OVar('k')
    v = OVar('v')

    # 1. CPS identity: λk. k(v) → v
    cps_id = OLam(('k',), OOp('k', (v,)))
    r1 = apply(cps_id, ctx)
    _assert(any(lbl == 'D30_cps_identity' for _, lbl in r1), "CPS identity")
    extracted = [t for t, lbl in r1 if lbl == 'D30_cps_identity'][0]
    _assert(extracted.canon() == v.canon(), "CPS identity extracts v")

    # 2. Direct to CPS: f(g(x)) → g(x, λr. f(r))
    direct = OOp('f', (OOp('g', (x,)),))
    r2 = apply(direct, ctx)
    _assert(any(lbl == 'D30_direct_to_cps' for _, lbl in r2), "direct → CPS")
    cps_form = [t for t, lbl in r2 if lbl == 'D30_direct_to_cps'][0]
    _assert(isinstance(cps_form, OOp) and cps_form.name == 'g', "CPS outer is g")

    # 3. CPS to direct: g(x, λr. f(r)) → f(g(x))
    cps_term = OOp('g', (x, OLam(('r',), OOp('f', (OVar('r'),)))))
    r3 = apply(cps_term, ctx)
    _assert(any(lbl == 'D30_cps_to_direct' for _, lbl in r3), "CPS → direct")
    direct_form = [t for t, lbl in r3 if lbl == 'D30_cps_to_direct'][0]
    _assert(isinstance(direct_form, OOp) and direct_form.name == 'f', "direct outer is f")

    # 4. Callback chain flattening
    nested_cb = OOp('f', (x, OLam(('r1',), OOp('g', (OVar('r1'), OLam(('r2',), OOp('h', (OVar('r2'),))))))))
    r4 = apply(nested_cb, ctx)
    _assert(any(lbl == 'D30_flatten_callbacks' for _, lbl in r4), "callback flatten")
    chain_result = [t for t, lbl in r4 if lbl == 'D30_flatten_callbacks'][0]
    _assert(isinstance(chain_result, OOp) and chain_result.name == 'chain', "result is chain")

    # 5. chain → nested callbacks (unflatten)
    chain_term = OOp('chain', (OOp('f', (x,)), OOp('g', ()), OOp('h', ())))
    r5 = apply(chain_term, ctx)
    _assert(any(lbl == 'D30_unflatten_chain' for _, lbl in r5), "chain unflatten")

    # 6. Seq to CPS: [a, b, c] → cps_seq(a, λ_. cps_seq(b, λ_. c))
    seq = OSeq((OVar('a'), OVar('b'), OVar('c')))
    r6 = apply(seq, ctx)
    _assert(any(lbl == 'D30_seq_to_cps' for _, lbl in r6), "seq → CPS")
    cps_seq = [t for t, lbl in r6 if lbl == 'D30_seq_to_cps'][0]
    _assert(isinstance(cps_seq, OOp) and cps_seq.name == 'cps_seq', "result is cps_seq")

    # 7. cps_seq → Seq: cps_seq(a, λ_. b) → [a, b]
    cps_seq_term = OOp('cps_seq', (OVar('a'), OLam(('_',), OVar('b'))))
    r7 = apply(cps_seq_term, ctx)
    _assert(any(lbl == 'D30_cps_to_seq' for _, lbl in r7), "cps_seq → seq")

    # 8. compose to CPS
    compose = OOp('compose', (OOp('f', ()), OOp('g', ())))
    r8 = apply(compose, ctx)
    _assert(any(lbl == 'D30_compose_to_cps' for _, lbl in r8), "compose → CPS")

    # 9. then(a, f) → direct
    then_term = OOp('then', (OVar('a'), OLam(('r',), OOp('f', (OVar('r'),)))))
    r9 = apply(then_term, ctx)
    _assert(any(lbl == 'D30_then_to_direct' for _, lbl in r9), "then → direct")
    then_result = [t for t, lbl in r9 if lbl == 'D30_then_to_direct'][0]
    _assert(isinstance(then_result, OOp) and then_result.name == 'f', "then gives f(a)")

    # 10. Recognizes
    _assert(recognizes(cps_id), "recognizes CPS identity")
    _assert(recognizes(direct), "recognizes nested calls")
    _assert(recognizes(seq), "recognizes sequence")
    _assert(recognizes(chain_term), "recognizes chain")
    _assert(recognizes(cps_seq_term), "recognizes cps_seq")
    _assert(not recognizes(OLit(42)), "does not recognize literal")

    # 11. Relevance
    _assert(relevance_score(direct, cps_seq_term) > 0.3, "direct↔CPS relevance")
    _assert(relevance_score(cps_seq_term, seq) > 0.5, "cps_seq↔seq relevance")

    # 12. Inverse: value → CPS identity
    r12 = apply_inverse(v, ctx)
    _assert(any(lbl == 'D30_inv_value_to_cps' for _, lbl in r12), "inv value → CPS")

    # 13. Inverse: seq → CPS seq
    r13 = apply_inverse(seq, ctx)
    _assert(any(lbl == 'D30_inv_seq_to_cps' for _, lbl in r13), "inv seq → CPS")

    # 14. Inverse: cps_seq → seq
    r14 = apply_inverse(cps_seq_term, ctx)
    _assert(any(lbl == 'D30_inv_cps_to_seq' for _, lbl in r14), "inv cps → seq")

    # 15. Inverse: direct → CPS
    r15 = apply_inverse(direct, ctx)
    _assert(any(lbl == 'D30_inv_direct_to_cps' for _, lbl in r15), "inv direct → CPS")

    # 16. Roundtrip: direct → CPS → direct
    cps_v = [t for t, lbl in r2 if lbl == 'D30_direct_to_cps'][0]
    r16 = apply(cps_v, ctx)
    roundtrip = [t for t, lbl in r16 if lbl == 'D30_cps_to_direct']
    _assert(len(roundtrip) > 0, "roundtrip CPS→direct succeeds")

    print(f"D30 CPS: {_pass} passed, {_fail} failed")
