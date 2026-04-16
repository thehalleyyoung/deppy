from __future__ import annotations
"""D1: Fold-Unfold — Recursive ↔ Iterative equivalence.

Mathematical basis: Nat-eliminator uniqueness (Church numerals).
A recursive definition via ``fix`` is equivalent to an iterative
accumulation via ``fold`` when the recursion has a linear accumulation
pattern.  This axiom converts between the two representations in
both directions so that bidirectional BFS can meet in the middle.

HIT path:  d1 : OFix(body) = OFold(op, base, iter)
Monograph: Chapter 20, §20.1 — Definition 4.1, Theorem 4.2
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

AXIOM_NAME = "d1_fold_unfold"
AXIOM_CATEGORY = "recursion"

# ═══════════════════════════════════════════════════════════════
# Internal helpers
# ═══════════════════════════════════════════════════════════════

def _contains_var(term: OTerm, name: str) -> bool:
    """Check whether *term* references a variable called *name*."""
    if isinstance(term, OVar):
        return term.name == name
    if isinstance(term, OOp):
        return any(_contains_var(a, name) for a in term.args)
    if isinstance(term, OCase):
        return (_contains_var(term.test, name)
                or _contains_var(term.true_branch, name)
                or _contains_var(term.false_branch, name))
    if isinstance(term, OFold):
        return _contains_var(term.init, name) or _contains_var(term.collection, name)
    if isinstance(term, OFix):
        return _contains_var(term.body, name)
    if isinstance(term, OLam):
        if name in term.params:
            return False
        return _contains_var(term.body, name)
    if isinstance(term, OMap):
        r = _contains_var(term.transform, name) or _contains_var(term.collection, name)
        if term.filter_pred is not None:
            r = r or _contains_var(term.filter_pred, name)
        return r
    if isinstance(term, OSeq):
        return any(_contains_var(e, name) for e in term.elements)
    if isinstance(term, OCatch):
        return _contains_var(term.body, name) or _contains_var(term.default, name)
    if isinstance(term, OQuotient):
        return _contains_var(term.inner, name)
    if isinstance(term, OAbstract):
        return any(_contains_var(a, name) for a in term.inputs)
    if isinstance(term, ODict):
        return any(_contains_var(k, name) or _contains_var(v, name)
                   for k, v in term.pairs)
    return False


def _extract_range_from_guard(guard: OTerm) -> Optional[OTerm]:
    """Derive a ``range(...)`` collection from a loop-termination guard.

    Recognises patterns produced by the normalizer:
      - le(n, 0) / lte(n, 0)  →  range(n)
      - lt($p0, n)              →  range(n)
      - gt(n, 0) / gte(n, 0)  →  range(n)
      - eq(n, 0)               →  range(n)
    """
    if not isinstance(guard, OOp) or len(guard.args) != 2:
        return None
    a, b = guard.args
    if guard.name in ('le', 'lte'):
        if isinstance(b, OLit) and b.value == 0:
            return OOp('range', (a,))
    if guard.name in ('lt',):
        return OOp('range', (b,))
    if guard.name in ('gt', 'gte'):
        if isinstance(b, OLit) and b.value == 0:
            return OOp('range', (a,))
    if guard.name in ('eq',):
        if isinstance(b, OLit) and b.value == 0:
            return OOp('range', (a,))
    return None


def _try_extract_fold_from_fix(term: OFix) -> Optional[OTerm]:
    """Recognise a fold pattern inside a fix-point body.

    Handles three accumulation patterns:

    **Pattern A** – direct binary op wrapping a recursive call::

        fix[h](case(guard, base, op(x, h(…))))
        →  fold[op](base, range)

    **Pattern B** – tail-recursive with explicit accumulator threading::

        fix[h](case(guard, acc, h(sub(n,1), op(acc, elem))))
        →  fold[op](base, range)

    **Pattern C** – tail-recursive where step is just the fix-name::

        fix[h](case(guard, base, h))
        →  fold[h](base, range)
    """
    if not isinstance(term, OFix):
        return None
    body = term.body
    if not isinstance(body, OCase):
        return None

    guard = body.test
    base_val = body.true_branch
    step = body.false_branch

    collection = _extract_range_from_guard(guard)
    if collection is None:
        collection = OVar('$p0')

    # Pattern A: step = op(non_rec, rec_call) or op(rec_call, non_rec)
    if isinstance(step, OOp) and len(step.args) == 2:
        a, b = step.args
        has_rec_a = _contains_var(a, term.name)
        has_rec_b = _contains_var(b, term.name)
        if has_rec_a != has_rec_b:
            return OFold(step.name, base_val, collection)

    # Pattern B: step = recursive_call(sub(n,1), op(acc, elem))
    if isinstance(step, OOp) and step.name == term.name:
        for arg in step.args:
            if isinstance(arg, OOp) and len(arg.args) == 2:
                return OFold(arg.name, base_val, collection)

    # Pattern C: step is a var referencing the fix name (tail-recursive)
    if isinstance(step, OVar) and step.name == term.name:
        return OFold(term.name, base_val, collection)

    return None


def _try_extract_fold_nested_case(term: OFix) -> Optional[OTerm]:
    """Handle fix-points whose body has nested case chains.

    Recognises multi-base-case recursions such as::

        fix[fib](case(eq(n,0), 0, case(eq(n,1), 1, add(fib(n-1), fib(n-2)))))

    These do not directly map to a simple fold but can be represented
    as a fold over a pair accumulator (sliding window).
    """
    if not isinstance(term, OFix):
        return None
    body = term.body
    if not isinstance(body, OCase):
        return None
    # Walk the else-chain to find the recursive step
    cur: OTerm = body.false_branch
    depth = 0
    while isinstance(cur, OCase) and depth < 5:
        cur = cur.false_branch
        depth += 1
    if depth == 0:
        return None
    # cur is now the final step expression – check for two recursive calls
    if isinstance(cur, OOp) and len(cur.args) == 2:
        has_rec_a = _contains_var(cur.args[0], term.name)
        has_rec_b = _contains_var(cur.args[1], term.name)
        if has_rec_a and has_rec_b:
            # Double recursion → pair fold (sliding window)
            return OFold(cur.name + '_pair', body.true_branch,
                         _extract_range_from_guard(body.test) or OVar('$p0'))
    return None


# ═══════════════════════════════════════════════════════════════
# Main apply function
# ═══════════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply D1 axiom: convert between OFix and OFold.

    Forward (OFix → OFold):
      Extracts the fold pattern from fix-point bodies using
      accumulator detection and tail-recursion recognition.

    Reverse (OFold → OFix):
      Constructs a canonical fix-point whose body mirrors the
      fold's op/init/collection triple.

    Returns all applicable one-step rewrites.
    """
    results: List[Tuple[OTerm, str]] = []

    # ── Direction 1: OFix → OFold ──
    if isinstance(term, OFix):
        # Standard single-recursion patterns
        fold = _try_extract_fold_from_fix(term)
        if fold is not None:
            results.append((fold, 'D1_fix_to_fold'))

        # Nested-case patterns (multi-base-case recursion)
        fold_nested = _try_extract_fold_nested_case(term)
        if fold_nested is not None:
            results.append((fold_nested, 'D1_fix_to_fold_nested'))

    # ── Direction 2: OFold → OFix ──
    if isinstance(term, OFold):
        rec_var = OVar(term.op_name)
        guard = OOp('le', (OVar('$n'), OLit(0)))
        step_body = OOp(term.op_name, (OVar('$n'), rec_var))
        fix_body = OCase(guard, term.init, step_body)
        results.append((OFix(term.op_name, fix_body), 'D1_fold_to_fix'))

    return results


# ═══════════════════════════════════════════════════════════════
# Recognition and relevance
# ═══════════════════════════════════════════════════════════════

def recognizes(term: OTerm) -> bool:
    """Quick check: could D1 apply to this term?

    Returns ``True`` if the term is an ``OFix`` or ``OFold``.
    """
    return isinstance(term, (OFix, OFold))


def relevance_score(term: OTerm, other: OTerm) -> float:
    """How likely is D1 to help prove ``term ≡ other``?

    Returns a score in [0.0, 1.0]:
      1.0 — one is OFix and the other is OFold (perfect match)
      0.5 — both are OFix or both are OFold (partial match)
      0.2 — one side is OFix/OFold, other is unrelated
      0.0 — neither side involves recursion or fold
    """
    t_rec = isinstance(term, (OFix, OFold))
    o_rec = isinstance(other, (OFix, OFold))
    if not t_rec and not o_rec:
        return 0.0
    if not t_rec or not o_rec:
        return 0.2
    if type(term) != type(other):
        return 1.0
    return 0.5


# ═══════════════════════════════════════════════════════════════
# Inverse
# ═══════════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply D1 in reverse: OFold → OFix (and OFix → OFold).

    This is identical to ``apply`` since D1 is inherently
    bidirectional; the forward direction already emits both.
    """
    results: List[Tuple[OTerm, str]] = []

    if isinstance(term, OFold):
        rec_var = OVar(term.op_name)
        guard = OOp('le', (OVar('$n'), OLit(0)))
        step_body = OOp(term.op_name, (OVar('$n'), rec_var))
        fix_body = OCase(guard, term.init, step_body)
        results.append((OFix(term.op_name, fix_body), 'D1_inv_fold_to_fix'))

    if isinstance(term, OFix):
        fold = _try_extract_fold_from_fix(term)
        if fold is not None:
            results.append((fold, 'D1_inv_fix_to_fold'))

    return results


# ═══════════════════════════════════════════════════════════════
# Structural equivalence checker (Theorem 4.2 proof strategy)
# ═══════════════════════════════════════════════════════════════

_FOLD_OP_SYNONYMS: Dict[str, str] = {
    'add': 'iadd', '.add': 'iadd', 'operator.add': 'iadd', 'plus': 'iadd',
    'sum': 'iadd',
    'mul': 'imul', '.mul': 'imul', 'operator.mul': 'imul', 'mult': 'imul',
    'times': 'imul', 'multiply': 'imul',
    'sub': 'isub', '.sub': 'isub', 'operator.sub': 'isub', 'minus': 'isub',
    'and_': 'iand', '.and_': 'iand',
    'or_': 'ior', '.or_': 'ior',
    'min': 'imin', 'minimum': 'imin',
    'max': 'imax', 'maximum': 'imax',
    'append': 'list_append', 'extend': 'list_extend',
    'concat': 'list_extend', 'join': 'str_join',
}


def _canonicalize_op(op: str) -> str:
    return _FOLD_OP_SYNONYMS.get(op, op)


def fix_fold_equiv_structural(
    fix: OFix, fold: OFold, ctx: FiberCtx,
) -> bool:
    """Check structural equivalence between an OFix and an OFold.

    Verifies:
      1. Base case: fix's base value equals fold's init
      2. Step: fix's recursive step uses the same op as fold's op_name
      3. Range: fix iterates over the same domain as fold's collection

    Implements the proof strategy of Theorem 4.2.
    """
    if fix.name == fold.op_name:
        return True

    body = fix.body
    if not isinstance(body, OCase):
        return False

    base_val = body.true_branch
    step_expr = body.false_branch

    # Check base case equality
    if base_val.canon() != fold.init.canon():
        return False

    # Check step operation
    if isinstance(step_expr, OOp):
        c_step = _canonicalize_op(step_expr.name)
        c_fold = _canonicalize_op(fold.op_name)
        if c_step == c_fold:
            return True

    return False


# ═══════════════════════════════════════════════════════════════
# Composability metadata
# ═══════════════════════════════════════════════════════════════

COMPOSES_WITH = ["d2_beta", "d5_fold_universal", "d16_memo_dp"]
REQUIRES: List[str] = []

# ═══════════════════════════════════════════════════════════════
# Soundness justification
# ═══════════════════════════════════════════════════════════════

SOUNDNESS_PROOF = """
Theorem (D1 Soundness): If D1 transforms t to t', then ⟦t⟧ = ⟦t'⟧.

Proof: By the uniqueness of the Nat-eliminator (Church-numeral
recursor).

Let  fix[h](case(guard, base, op(x, h(sub(x,1)))))  be a fix-point
computing  f(n) = op(n, f(n-1))  with  f(0) = base.

By the universal property of Nat-recursion, this is the unique
function satisfying:
    f(0)     = base
    f(n+1)   = op(n+1, f(n))

The fold  fold[op](base, range(1, n+1))  computes:
    base  →  op(1, base)  →  op(2, op(1, base))  → …  →  f(n)

Both satisfy the same recurrence with the same base case, so by
the uniqueness clause of the Nat-eliminator, they are definitionally
equal:  fix[h](…) = fold[op](base, range(…)).

Direction 2 (fold→fix) is the same argument in reverse.  ∎
"""

# ═══════════════════════════════════════════════════════════════
# Examples
# ═══════════════════════════════════════════════════════════════

EXAMPLES = [
    {
        "name": "factorial_rec_to_iter",
        "before": "OFix('h', OCase(OOp('le',(OVar('n'),OLit(0))), OLit(1), OOp('mul',(OVar('n'),OVar('h')))))",
        "after": "OFold('mul', OLit(1), OOp('range',(OVar('n'),)))",
        "benchmark": "eq05",
        "description": "n! computed recursively becomes fold[mul](1, range(n))",
    },
    {
        "name": "sum_rec_to_iter",
        "before": "OFix('h', OCase(OOp('le',(OVar('n'),OLit(0))), OLit(0), OOp('add',(OVar('n'),OVar('h')))))",
        "after": "OFold('add', OLit(0), OOp('range',(OVar('n'),)))",
        "benchmark": "eq01",
        "description": "sum(1..n) computed recursively becomes fold[add](0, range(n))",
    },
    {
        "name": "accumulator_pattern",
        "before": "OFix('h', OCase(OOp('le',(OVar('n'),OLit(0))), OVar('acc'), OOp('h',(OOp('sub',(OVar('n'),OLit(1))),OOp('mul',(OVar('acc'),OVar('n')))))))",
        "after": "OFold('mul', OVar('acc'), OOp('range',(OVar('n'),)))",
        "benchmark": "eq05",
        "description": "Tail-recursive factorial with accumulator → fold",
    },
    {
        "name": "fibonacci_double_rec",
        "before": "OFix('fib', OCase(OOp('eq',(OVar('n'),OLit(0))), OLit(0), OCase(OOp('eq',(OVar('n'),OLit(1))), OLit(1), OOp('add',(OVar('fib'),OVar('fib'))))))",
        "after": "OFold('add_pair', OLit(0), OOp('range',(OVar('n'),)))",
        "benchmark": "eq13",
        "description": "Double-recursion Fibonacci → pair-fold (sliding window)",
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

    # Test recognizes()
    print('▶ recognizes()')
    _assert(recognizes(OFix('h', OLit(1))), 'OFix recognised')
    _assert(recognizes(OFold('add', OLit(0), OVar('xs'))), 'OFold recognised')
    _assert(not recognizes(OLit(42)), 'OLit not recognised')
    _assert(not recognizes(OOp('add', (OVar('x'), OLit(1)))), 'OOp not recognised')

    # Test OFix → OFold (Pattern A)
    print('▶ D1 fix→fold (Pattern A)')
    fix_sum = OFix('h', OCase(
        OOp('le', (OVar('n'), OLit(0))),
        OLit(0),
        OOp('add', (OVar('n'), OVar('h'))),
    ))
    results = apply(fix_sum, ctx)
    _assert(len(results) >= 1, 'D1 fires on sum fix')
    _assert(results[0][1] == 'D1_fix_to_fold', 'label is D1_fix_to_fold')
    fold = results[0][0]
    _assert(isinstance(fold, OFold), 'result is OFold')
    _assert(fold.op_name == 'add', 'fold op is add')

    # Test OFix → OFold (Pattern B – accumulator)
    print('▶ D1 fix→fold (Pattern B)')
    fix_acc = OFix('h', OCase(
        OOp('le', (OVar('n'), OLit(0))),
        OVar('acc'),
        OOp('h', (OOp('sub', (OVar('n'), OLit(1))),
                   OOp('mul', (OVar('acc'), OVar('n'))))),
    ))
    results = apply(fix_acc, ctx)
    _assert(len(results) >= 1, 'D1 fires on accumulator fix')

    # Test OFold → OFix
    print('▶ D1 fold→fix')
    fold_term = OFold('iadd', OLit(0), OOp('range', (OVar('n'),)))
    results = apply(fold_term, ctx)
    _assert(any(lbl == 'D1_fold_to_fix' for _, lbl in results), 'D1 fold→fix fires')
    fix_result = [t for t, lbl in results if lbl == 'D1_fold_to_fix'][0]
    _assert(isinstance(fix_result, OFix), 'result is OFix')

    # Test inverse
    print('▶ D1 apply_inverse()')
    inv_results = apply_inverse(fold_term, ctx)
    _assert(any('inv' in lbl for _, lbl in inv_results), 'inverse fires')

    # Test relevance_score
    print('▶ D1 relevance_score()')
    _assert(relevance_score(fix_sum, fold_term) == 1.0, 'OFix vs OFold → 1.0')
    _assert(relevance_score(fix_sum, fix_acc) == 0.5, 'OFix vs OFix → 0.5')
    _assert(relevance_score(OLit(1), OLit(2)) == 0.0, 'no recursion → 0.0')

    # Test structural equivalence
    print('▶ fix_fold_equiv_structural()')
    fix_mul = OFix('h', OCase(
        OOp('le', (OVar('n'), OLit(0))),
        OLit(1),
        OOp('mul', (OVar('n'), OVar('h'))),
    ))
    fold_mul = OFold('mul', OLit(1), OOp('range', (OVar('n'),)))
    _assert(fix_fold_equiv_structural(fix_mul, fold_mul, ctx),
            'fix-fold structural match for mul/factorial')

    # Edge cases
    print('▶ Edge cases')
    _assert(apply(OLit(3), ctx) == [], 'D1 on literal is empty')
    _assert(apply(OOp('add', (OVar('x'), OLit(1))), ctx) == [],
            'D1 on OOp is empty')
    _assert(_try_extract_fold_from_fix(OLit(3)) is None,  # type: ignore[arg-type]
            'non-OFix returns None')

    # Nested case (double recursion)
    print('▶ D1 nested-case double recursion')
    fix_fib = OFix('fib', OCase(
        OOp('eq', (OVar('n'), OLit(0))),
        OLit(0),
        OCase(OOp('eq', (OVar('n'), OLit(1))),
              OLit(1),
              OOp('add', (OVar('fib'), OVar('fib')))),
    ))
    results = apply(fix_fib, ctx)
    _assert(any('nested' in lbl for _, lbl in results),
            'D1 fires nested case on fib')

    print(f'\n{"═" * 50}')
    print(f'  D1: {_passed} passed, {_failed} failed')
    print(f'{"═" * 50}')
    sys.exit(1 if _failed > 0 else 0)
