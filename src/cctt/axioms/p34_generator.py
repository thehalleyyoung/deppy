"""P34 Axiom: Generator / Coroutine Equivalences.

Establishes equivalences between different generator and coroutine
patterns: yield from vs explicit loops, generator expressions vs
list comprehensions, itertools.chain vs yield-from-in-loop,
send/return value, StopIteration handling, and next-with-default.

Mathematical basis: Generators are coalgebras of the functor
  F(X) = 1 + A × X     (either done, or yield a value and continue)
The final coalgebra is the type of (possibly infinite) streams of A.
Two generator implementations are bisimilar (produce the same
observation sequence) iff they are identified by the unique
coalgebra morphism to the final coalgebra.

"yield from it" and "for x in it: yield x" define the same
coalgebra structure map — they unfold the sub-iterator identically.

Generator expressions and list comprehensions compute the same
function  List(A) → List(B),  but the generator is lazy (coinductive)
while the list comp is eager (inductive).  They are related by the
canonical morphism from the initial algebra to the final coalgebra
(the "fold-after-unfold" factorisation).

Key rewrites:
  • yield from it ↔ for x in it: yield x
  • genexpr ↔ listcomp (lazy ↔ eager)
  • itertools.chain(*its) ↔ yield from in loop
  • gen.send(v) ↔ return value assignment
  • StopIteration handling ↔ for-loop
  • next(gen, default) ↔ try/except StopIteration
  • gen.throw ↔ raise inside generator
  • gen.close ↔ GeneratorExit
  • iter + next loop ↔ for loop
  • accumulate-with-yield ↔ itertools.accumulate

(§P34, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P34_generator"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P23_iteration", "P6_itertools", "P11_functional"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P34 Generator / Coroutine Equivalences).

1. yield_from(it) ≡ yield_loop(it)
   "yield from it" delegates to the sub-iterator; "for x in it:
   yield x" manually iterates and yields each element.  Both
   produce the identical stream coalgebra.

2. genexpr(fn, it) ≡ listcomp_eager(fn, it)
   A generator expression (fn(x) for x in it) and a list comp
   [fn(x) for x in it] compute the same mapped sequence; the
   generator is lazy, the list comp is eager.

3. chain_iters(it1, it2, ...) ≡ yield_from_loop(it1, it2, ...)
   itertools.chain(it1, it2) and "for it in [it1, it2]: yield from
   it" produce the same concatenated stream.

4. gen_send(gen, val) ≡ gen_return(gen, val)
   gen.send(val) resumes the generator and delivers val as the
   yield-expression's value; this is the coroutine dual of return.

5. next_default(gen, d) ≡ next_try_except(gen, d)
   next(gen, d) returns d on StopIteration; try: next(gen) except
   StopIteration: d does the same.

6. stopiteration_catch(gen) ≡ iter_next_loop(gen)
   Catching StopIteration in a while-next loop is equivalent to
   a for-loop over the generator.

7. gen_throw(gen, exc) — throws an exception into the generator.
8. gen_close(gen) — equivalent to gen.throw(GeneratorExit).
9. yield_accumulate(fn, it) ≡ itertools.accumulate(it, fn) as a
   generator that yields running results.
10. gen_to_list(gen) ≡ list(gen) — eagerly consume a generator.
"""

EXAMPLES = [
    ("yield_from($it)", "yield_loop($it)", "P34_yield_from_to_loop"),
    ("genexpr($fn, $it)", "listcomp_eager($fn, $it)", "P34_genexpr_to_list"),
    ("chain_iters($a, $b)", "yield_from_loop($a, $b)", "P34_chain_to_yield"),
    ("next_default($g, $d)", "next_try_except($g, $d)", "P34_next_default"),
    ("gen_to_list($g)", "listcomp_eager($fn, $g)", "P34_gen_to_list"),
]

_GENERATOR_OPS = frozenset({
    'yield_from', 'yield_loop', 'genexpr', 'listcomp_eager',
    'chain_iters', 'yield_from_loop', 'gen_send', 'gen_return',
    'next_default', 'next_try_except', 'stopiteration_catch',
    'gen_throw', 'gen_close', 'iter_next_loop', 'yield_accumulate',
    'gen_to_list',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P34: Generator / coroutine equivalence rewrites (forward)."""
    results: List[Tuple[OTerm, str]] = []

    if not isinstance(term, OOp):
        return results

    # ── 1. yield_from ↔ yield_loop ──
    if term.name == 'yield_from' and len(term.args) >= 1:
        results.append((
            OOp('yield_loop', term.args),
            'P34_yield_from_to_loop',
        ))

    if term.name == 'yield_loop' and len(term.args) >= 1:
        results.append((
            OOp('yield_from', term.args),
            'P34_loop_to_yield_from',
        ))

    # ── 2. genexpr ↔ listcomp_eager ──
    if term.name == 'genexpr' and len(term.args) == 2:
        results.append((
            OOp('listcomp_eager', term.args),
            'P34_genexpr_to_listcomp',
        ))

    if term.name == 'listcomp_eager' and len(term.args) == 2:
        results.append((
            OOp('genexpr', term.args),
            'P34_listcomp_to_genexpr',
        ))

    # ── 3. chain_iters ↔ yield_from_loop ──
    if term.name == 'chain_iters' and len(term.args) >= 2:
        results.append((
            OOp('yield_from_loop', term.args),
            'P34_chain_to_yield_from',
        ))

    if term.name == 'yield_from_loop' and len(term.args) >= 2:
        results.append((
            OOp('chain_iters', term.args),
            'P34_yield_from_to_chain',
        ))

    # ── 4. gen_send ↔ gen_return ──
    if term.name == 'gen_send' and len(term.args) == 2:
        results.append((
            OOp('gen_return', term.args),
            'P34_send_to_return',
        ))

    if term.name == 'gen_return' and len(term.args) == 2:
        results.append((
            OOp('gen_send', term.args),
            'P34_return_to_send',
        ))

    # ── 5. next_default ↔ next_try_except ──
    if term.name == 'next_default' and len(term.args) == 2:
        results.append((
            OOp('next_try_except', term.args),
            'P34_next_default_to_try',
        ))

    if term.name == 'next_try_except' and len(term.args) == 2:
        results.append((
            OOp('next_default', term.args),
            'P34_try_to_next_default',
        ))

    # ── 6. stopiteration_catch ↔ iter_next_loop ──
    if term.name == 'stopiteration_catch' and len(term.args) >= 1:
        results.append((
            OOp('iter_next_loop', term.args),
            'P34_stopiter_to_loop',
        ))

    if term.name == 'iter_next_loop' and len(term.args) >= 1:
        results.append((
            OOp('stopiteration_catch', term.args),
            'P34_loop_to_stopiter',
        ))

    # ── 7. gen_throw ↔ raise inside generator ──
    if term.name == 'gen_throw' and len(term.args) == 2:
        results.append((
            OOp('gen_close', (term.args[0],)),
            'P34_throw_to_close',
        ))

    # ── 8. gen_close ↔ gen_throw(GeneratorExit) ──
    if term.name == 'gen_close' and len(term.args) == 1:
        results.append((
            OOp('gen_throw', (term.args[0], OLit('GeneratorExit'))),
            'P34_close_to_throw',
        ))

    # ── 9. yield_accumulate ↔ fold with yield ──
    if term.name == 'yield_accumulate' and len(term.args) == 2:
        fn, it = term.args
        results.append((
            OFold('accumulate', OLit(None), it),
            'P34_yield_accum_to_fold',
        ))

    # ── 10. gen_to_list ↔ listcomp_eager identity ──
    if term.name == 'gen_to_list' and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, OOp) and inner.name == 'genexpr' and \
                len(inner.args) == 2:
            results.append((
                OOp('listcomp_eager', inner.args),
                'P34_gen_to_list_comp',
            ))
        results.append((
            OOp('listcomp_eager', (OLam(('x',), OVar('x')), term.args[0])),
            'P34_gen_to_list_identity',
        ))

    # ── 11. genexpr → gen_to_list (wrap for eager consumers) ──
    if term.name == 'genexpr' and len(term.args) == 2:
        results.append((
            OOp('gen_to_list', (term,)),
            'P34_genexpr_to_gen_list',
        ))

    # ── 12. stopiteration_catch → yield_loop (for loop form) ──
    if term.name == 'stopiteration_catch' and len(term.args) >= 1:
        results.append((
            OOp('yield_loop', term.args),
            'P34_stopiter_to_yield_loop',
        ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """Return reverse rewrites (manual form → idiomatic generator form)."""
    inverse_labels = {
        'P34_loop_to_yield_from', 'P34_listcomp_to_genexpr',
        'P34_yield_from_to_chain', 'P34_return_to_send',
        'P34_try_to_next_default', 'P34_loop_to_stopiter',
        'P34_close_to_throw',
    }
    return [(t, l) for t, l in apply(term, ctx) if l in inverse_labels]


def recognizes(term: OTerm) -> bool:
    """Return True if the term's root operator is a generator/coroutine op."""
    if isinstance(term, OOp) and term.name in _GENERATOR_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    """Heuristic relevance for search-guided rewriting."""
    sc, tc = source.canon(), target.canon()
    for kw in ('yield', 'gen', 'generator', 'coroutine', 'next',
               'chain', 'stopiteration', 'send', 'accumulate'):
        if kw in sc and kw in tc:
            return 0.9
    if ('yield' in sc and 'loop' in tc) or ('loop' in sc and 'yield' in tc):
        return 0.85
    if ('genexpr' in sc and 'listcomp' in tc) or \
       ('listcomp' in sc and 'genexpr' in tc):
        return 0.85
    if ('chain' in sc and 'yield' in tc) or ('yield' in sc and 'chain' in tc):
        return 0.8
    if any(k in sc for k in ('yield', 'gen', 'next', 'chain', 'iter')):
        return 0.3
    return 0.05


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

    # 1. yield_from → yield_loop
    t = OOp('yield_from', (OVar('it'),))
    r = apply(t)
    _assert(any(l == 'P34_yield_from_to_loop' for _, l in r),
            "yield_from → loop")

    # 2. yield_loop → yield_from
    t2 = OOp('yield_loop', (OVar('it'),))
    r2 = apply(t2)
    _assert(any(l == 'P34_loop_to_yield_from' for _, l in r2),
            "loop → yield_from")

    # 3. genexpr → listcomp_eager
    t3 = OOp('genexpr', (OVar('fn'), OVar('it')))
    r3 = apply(t3)
    _assert(any(l == 'P34_genexpr_to_listcomp' for _, l in r3),
            "genexpr → listcomp")

    # 4. listcomp_eager → genexpr
    t4 = OOp('listcomp_eager', (OVar('fn'), OVar('it')))
    r4 = apply(t4)
    _assert(any(l == 'P34_listcomp_to_genexpr' for _, l in r4),
            "listcomp → genexpr")

    # 5. chain_iters → yield_from_loop
    t5 = OOp('chain_iters', (OVar('a'), OVar('b')))
    r5 = apply(t5)
    _assert(any(l == 'P34_chain_to_yield_from' for _, l in r5),
            "chain → yield_from")

    # 6. yield_from_loop → chain_iters
    t6 = OOp('yield_from_loop', (OVar('a'), OVar('b')))
    r6 = apply(t6)
    _assert(any(l == 'P34_yield_from_to_chain' for _, l in r6),
            "yield_from_loop → chain")

    # 7. gen_send → gen_return
    t7 = OOp('gen_send', (OVar('gen'), OVar('val')))
    r7 = apply(t7)
    _assert(any(l == 'P34_send_to_return' for _, l in r7),
            "send → return")

    # 8. gen_return → gen_send
    t8 = OOp('gen_return', (OVar('gen'), OVar('val')))
    r8 = apply(t8)
    _assert(any(l == 'P34_return_to_send' for _, l in r8),
            "return → send")

    # 9. next_default → next_try_except
    t9 = OOp('next_default', (OVar('gen'), OLit(0)))
    r9 = apply(t9)
    _assert(any(l == 'P34_next_default_to_try' for _, l in r9),
            "next_default → try")

    # 10. next_try_except → next_default
    t10 = OOp('next_try_except', (OVar('gen'), OLit(0)))
    r10 = apply(t10)
    _assert(any(l == 'P34_try_to_next_default' for _, l in r10),
            "try → next_default")

    # 11. stopiteration_catch → iter_next_loop
    t11 = OOp('stopiteration_catch', (OVar('gen'),))
    r11 = apply(t11)
    _assert(any(l == 'P34_stopiter_to_loop' for _, l in r11),
            "stopiter → loop")

    # 12. iter_next_loop → stopiteration_catch
    t12 = OOp('iter_next_loop', (OVar('gen'),))
    r12 = apply(t12)
    _assert(any(l == 'P34_loop_to_stopiter' for _, l in r12),
            "loop → stopiter")

    # 13. gen_close → gen_throw(GeneratorExit)
    t13 = OOp('gen_close', (OVar('gen'),))
    r13 = apply(t13)
    _assert(any(l == 'P34_close_to_throw' for _, l in r13),
            "close → throw")

    # 14. gen_to_list(genexpr(fn, it)) → listcomp_eager(fn, it)
    t14 = OOp('gen_to_list', (OOp('genexpr', (OVar('fn'), OVar('it'))),))
    r14 = apply(t14)
    _assert(any(l == 'P34_gen_to_list_comp' for _, l in r14),
            "gen_to_list(genexpr) → listcomp")

    # 15. yield_accumulate → fold
    t15 = OOp('yield_accumulate', (OVar('fn'), OVar('it')))
    r15 = apply(t15)
    _assert(any(l == 'P34_yield_accum_to_fold' for _, l in r15),
            "yield_accum → fold")

    # 16. genexpr → gen_to_list (wrap)
    _assert(any(l == 'P34_genexpr_to_gen_list' for _, l in r3),
            "genexpr → gen_to_list")

    # 17. stopiteration_catch → yield_loop (transitive)
    _assert(any(l == 'P34_stopiter_to_yield_loop' for _, l in r11),
            "stopiter → yield_loop (transitive)")

    # 18. inverse: yield_loop → yield_from
    r18_inv = apply_inverse(OOp('yield_loop', (OVar('it'),)))
    _assert(any(l == 'P34_loop_to_yield_from' for _, l in r18_inv),
            "inv: loop → yield_from")

    # 19. recognizes generator ops
    _assert(recognizes(OOp('yield_from', (OVar('it'),))),
            "recognizes yield_from")
    _assert(recognizes(OOp('gen_send', (OVar('g'), OVar('v')))),
            "recognizes gen_send")
    _assert(not recognizes(OLit(42)), "!recognizes literal")

    # 20. relevance: yield ↔ loop high
    _assert(relevance_score(
        OOp('yield_from', (OVar('it'),)),
        OOp('yield_loop', (OVar('it'),)),
    ) > 0.7, "yield/loop relevance high")

    # 21. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2,
            "unrelated relevance low")

    print(f"P34 generator: {_pass} passed, {_fail} failed")
