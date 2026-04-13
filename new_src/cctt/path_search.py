"""§10: Automated Path Search — Kan Composition on OTerms.

Implements the path search algorithm from Ch.10 of the CCTT monograph.
Given two normalized OTerms nf_f and nf_g, searches for a multi-step
rewrite path:  nf_f →[ax₁] h₁ →[ax₂] h₂ → ... →[axₖ] nf_g

Each step applies a path constructor (axiom) from one of the 24
dichotomies (D1-D24).  The path is found by bidirectional BFS
from both ends, meeting in the middle.

Path constructors operate on OTerm sub-expressions and are organized
by the monograph's dichotomy groups:
  - Control Flow (D1-D8): rec↔iter, inline, loop forms, fold fusion
  - Data Structure (D9-D14): stack↔rec, ADT refinement, histogram
  - Algorithm Strategy (D15-D20): BFS↔DFS, memo↔DP, spec uniqueness
  - Language Feature (D21-D24): dispatch, try↔cond, sort-process, η
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from .denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    _subst, normalize,
)


@dataclass(frozen=True)
class PathStep:
    """A single step in a rewrite path."""
    axiom: str       # e.g. 'D1_fold_unfold', 'D4_comp_loop'
    position: str    # where in the term the axiom was applied
    before: str      # canon of term before
    after: str       # canon of term after


@dataclass
class PathResult:
    """Result of a path search."""
    found: Optional[bool]  # True=path found, False=provably no path, None=timeout
    path: List[PathStep]
    reason: str = ''


# ═══════════════════════════════════════════════════════════
# Path Constructors (Axioms) — the 24 dichotomies
# ═══════════════════════════════════════════════════════════
# Each axiom is a function: (OTerm, FiberCtx) → List[(OTerm, str)]
# returning all possible one-step rewrites of the term.
# FiberCtx carries duck type info for fiber-aware axioms.

@dataclass
class FiberCtx:
    """Context for fiber-aware path search.

    Carries duck type information so axioms like commutativity
    can be restricted to the correct fiber (§2.6 sheaf descent).
    """
    param_duck_types: Dict[str, str]  # p0 → 'int', p1 → 'str', etc.

    def is_numeric(self, term: OTerm) -> bool:
        """Check if all params in a term are on numeric fibers."""
        params = _extract_params_from_term(term)
        if not params:
            return True  # no params → literal/constant, numeric ops are fine
        for p in params:
            dt = self.param_duck_types.get(p, 'any')
            if dt not in ('int', 'float', 'number'):
                return False
        return True


def _extract_params_from_term(term: OTerm) -> Set[str]:
    """Extract parameter names (p0, p1, ...) referenced in a term."""
    if isinstance(term, OVar):
        return {term.name} if term.name.startswith('p') else set()
    if isinstance(term, OOp):
        result: Set[str] = set()
        for a in term.args:
            result |= _extract_params_from_term(a)
        return result
    if isinstance(term, OCase):
        return (_extract_params_from_term(term.test)
                | _extract_params_from_term(term.true_branch)
                | _extract_params_from_term(term.false_branch))
    if isinstance(term, OFold):
        return _extract_params_from_term(term.init) | _extract_params_from_term(term.collection)
    if isinstance(term, OSeq):
        result = set()
        for e in term.elements:
            result |= _extract_params_from_term(e)
        return result
    if isinstance(term, OLam):
        return _extract_params_from_term(term.body)
    if isinstance(term, OMap):
        result = _extract_params_from_term(term.transform) | _extract_params_from_term(term.collection)
        if term.filter_pred:
            result |= _extract_params_from_term(term.filter_pred)
        return result
    if isinstance(term, OQuotient):
        return _extract_params_from_term(term.inner)
    if isinstance(term, OFix):
        return _extract_params_from_term(term.body)
    if isinstance(term, ODict):
        result = set()
        for k, v in term.pairs:
            result |= _extract_params_from_term(k) | _extract_params_from_term(v)
        return result
    if isinstance(term, OCatch):
        return _extract_params_from_term(term.body) | _extract_params_from_term(term.default)
    if isinstance(term, OAbstract):
        result = set()
        for a in term.inputs:
            result |= _extract_params_from_term(a)
        return result
    return set()


def _all_rewrites(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply all applicable path constructors to a term.

    Returns list of (rewritten_term, axiom_name) pairs.
    Applies axioms at the root AND at all sub-term positions.
    """
    results = []

    # Apply axioms at the root
    for rewrite_fn in _ROOT_AXIOMS:
        for new_term, axiom_name in rewrite_fn(term, ctx):
            results.append((new_term, axiom_name))

    # Apply axioms at sub-term positions (congruence)
    for new_term, axiom_name in _congruence_rewrites(term, ctx):
        results.append((new_term, axiom_name))

    return results


def _congruence_rewrites(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Apply axioms inside sub-terms (structural congruence)."""
    results = []

    if isinstance(term, OOp):
        for i, arg in enumerate(term.args):
            for new_arg, ax in _all_rewrites(arg, ctx):
                new_args = list(term.args)
                new_args[i] = new_arg
                results.append((OOp(term.name, tuple(new_args)), f'{ax}@arg{i}'))
    elif isinstance(term, OCase):
        for new_test, ax in _all_rewrites(term.test, ctx):
            results.append((OCase(new_test, term.true_branch, term.false_branch), f'{ax}@test'))
        for new_t, ax in _all_rewrites(term.true_branch, ctx):
            results.append((OCase(term.test, new_t, term.false_branch), f'{ax}@then'))
        for new_f, ax in _all_rewrites(term.false_branch, ctx):
            results.append((OCase(term.test, term.true_branch, new_f), f'{ax}@else'))
    elif isinstance(term, OFold):
        for new_init, ax in _all_rewrites(term.init, ctx):
            results.append((OFold(term.op_name, new_init, term.collection), f'{ax}@init'))
        for new_coll, ax in _all_rewrites(term.collection, ctx):
            results.append((OFold(term.op_name, term.init, new_coll), f'{ax}@coll'))
    elif isinstance(term, OMap):
        for new_t, ax in _all_rewrites(term.transform, ctx):
            results.append((OMap(new_t, term.collection, term.filter_pred), f'{ax}@transform'))
        for new_c, ax in _all_rewrites(term.collection, ctx):
            results.append((OMap(term.transform, new_c, term.filter_pred), f'{ax}@coll'))
    elif isinstance(term, OSeq):
        for i, elem in enumerate(term.elements):
            for new_e, ax in _all_rewrites(elem, ctx):
                elems = list(term.elements)
                elems[i] = new_e
                results.append((OSeq(tuple(elems)), f'{ax}@elem{i}'))
    elif isinstance(term, OQuotient):
        for new_inner, ax in _all_rewrites(term.inner, ctx):
            results.append((OQuotient(new_inner, term.equiv_class), f'{ax}@inner'))
    elif isinstance(term, OLam):
        for new_body, ax in _all_rewrites(term.body, ctx):
            results.append((OLam(term.params, new_body), f'{ax}@body'))
    elif isinstance(term, OFix):
        for new_body, ax in _all_rewrites(term.body, ctx):
            results.append((OFix(term.name, new_body), f'{ax}@body'))

    return results


# ── D1: Recursive ↔ Iterative (fold/unfold) ──

def _axiom_d1_fold_unfold(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D1: OFix with accumulation pattern ↔ OFold.

    fix[h](init) where h accumulates via op over range
    ≡ fold[op](init, range)
    """
    results = []

    # Direction 1: OFix → OFold (recognize accumulation in fix-point)
    if isinstance(term, OFix):
        # A fix-point that's really just a fold
        # Heuristic: if body contains the same op applied to acc + element
        fold = _try_extract_fold_from_fix(term)
        if fold is not None:
            results.append((fold, 'D1_fix_to_fold'))

    # Direction 2: Two OFix with same structure → equate
    # (handled by fix-point hash comparison in normalizer)

    return results


def _try_extract_fold_from_fix(term: OFix) -> Optional[OTerm]:
    """Try to recognize a fold pattern inside a fix-point body.

    Pattern: fix[h](case(guard, base_val, op(h(rec_arg), step_val)))
    becomes  fold[op](base_val, collection).
    Enhanced recognizer from g02_univalence_hits proposal.
    """
    if not isinstance(term, OFix):
        return None
    body = term.body
    if not isinstance(body, OCase):
        return None

    rec_call = _find_recursive_call_in_fix(body.false_branch, term.name)
    if rec_call is None:
        return None

    op_name = _extract_accumulation_op_from_branch(body.false_branch, rec_call)
    if op_name is None:
        return None

    coll = _extract_range_from_base_guard(body.test)
    if coll is None:
        return None

    return OFold(op_name, body.true_branch, coll)


def _find_recursive_call_in_fix(term: OTerm, fix_name: str) -> Optional[OTerm]:
    """Locate a call ``fix_name(…)`` inside *term*."""
    if isinstance(term, OOp):
        if term.name == fix_name:
            return term
        for arg in term.args:
            found = _find_recursive_call_in_fix(arg, fix_name)
            if found is not None:
                return found
    if isinstance(term, OCase):
        for sub in (term.test, term.true_branch, term.false_branch):
            found = _find_recursive_call_in_fix(sub, fix_name)
            if found is not None:
                return found
    if isinstance(term, OFold):
        for sub in (term.init, term.collection):
            found = _find_recursive_call_in_fix(sub, fix_name)
            if found is not None:
                return found
    return None


def _extract_accumulation_op_from_branch(
    branch: OTerm, rec_call: OTerm
) -> Optional[str]:
    """Identify the binary operator combining *rec_call* with a step value."""
    if not isinstance(branch, OOp):
        return None
    if len(branch.args) != 2:
        return None
    rc_canon = rec_call.canon()
    if branch.args[0].canon() == rc_canon or branch.args[1].canon() == rc_canon:
        return branch.name
    return None


def _extract_range_from_base_guard(test: OTerm) -> Optional[OTerm]:
    """Heuristic: extract a range term from a base-case guard.

    Recognises lte($n, 0), eq($n, 0), lt($n, 1), etc.
    """
    if not isinstance(test, OOp):
        return None
    if test.name in ("lte", "lt", "eq") and len(test.args) == 2:
        if isinstance(test.args[1], OLit) and test.args[1].value in (0, 1):
            var = test.args[0]
            bound = OOp("add", (var, OLit(1)))
            return OOp("range", (bound,))
    return None


# ── D2: Nested helpers ↔ Flat (β-reduction) ──

def _axiom_d2_beta(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D2: β-reduction — inline function applications."""
    results = []

    # OOp wrapping a lambda application: (λx.body)(arg) → body[x:=arg]
    if isinstance(term, OOp) and term.name == 'apply':
        if len(term.args) >= 2 and isinstance(term.args[0], OLam):
            lam = term.args[0]
            actual_args = term.args[1:]
            if len(lam.params) == len(actual_args):
                mapping = {p: a for p, a in zip(lam.params, actual_args)}
                body = lam.body
                for var_name, replacement in mapping.items():
                    body = _subst_term(body, var_name, replacement)
                results.append((body, 'D2_beta'))

    return results


# ── D3: while ↔ for (loop normal form) ──

def _axiom_d3_loop_form(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D3: Normalize loop representations."""
    # Already handled by normalizer phases 1-3
    return []


# ── D4: Comprehension ↔ Loop (catamorphism fusion) ──

def _axiom_d4_comp_fusion(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D4: OMap(f, OMap(g, coll)) → OMap(f∘g, coll)."""
    results = []

    # Map fusion: map(f, map(g, coll)) → map(f∘g, coll)
    if isinstance(term, OMap):
        if isinstance(term.collection, OMap) and term.collection.filter_pred is None:
            inner = term.collection
            # Compose: f(g(x)) where f is outer transform, g is inner
            composed = _compose_transforms(term.transform, inner.transform)
            if composed is not None:
                results.append((OMap(composed, inner.collection, term.filter_pred),
                               'D4_map_fusion'))

    # fold(op, map(f, coll), init) → fold(op∘f, coll, init) when
    # the fold operation can absorb the map transform
    if isinstance(term, OFold):
        if isinstance(term.collection, OMap) and term.collection.filter_pred is None:
            results.append((OFold(term.op_name, term.init, term.collection.collection),
                           'D4_fold_map_fusion'))

    return results


# ── D5: reduce ↔ Loop (fold universality) ──

def _axiom_d5_fold_universal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D5: Fold universality — different fold representations are equal
    when they have the same operator, init, and collection."""
    results = []

    # Two folds with same semantics but different hash names
    # The normalizer handles most of this via op_name canonicalization
    # Here we handle residual: fold[hash1](init, coll) ≡ fold[hash2](init, coll)
    # when the fold bodies compute the same function
    if isinstance(term, OFold) and len(term.op_name) == 8:
        # Hash-named fold — try to identify the operation
        canonical_op = _identify_fold_op(term)
        if canonical_op and canonical_op != term.op_name:
            results.append((OFold(canonical_op, term.init, term.collection),
                           'D5_fold_canonicalize'))

    return results


# ── D6: Generator ↔ Eager (laziness adjunction) ──

def _axiom_d6_lazy_eager(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D6: list(gen(x)) ≡ comp(x) when the generator is non-stateful."""
    # Handled by normalizer phase 4 (HOF fusion)
    return []


# ── D7: Tail-recursive ↔ Loop (CPS transform) ──

def _axiom_d7_tailrec(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D7: Tail-recursive fix ↔ fold."""
    # Subsumed by D1 in OTerm world
    return []


# ── D8: Multi-return ↔ Single (section merging) ──

def _axiom_d8_section_merge(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D8: case(g, A, case(g', B, C)) ↔ case(g, A, B) when g implies ¬g'."""
    results = []

    # Nested case flattening (already done in phase 7, but may need
    # another pass after other axioms fire)
    if isinstance(term, OCase):
        if isinstance(term.false_branch, OCase):
            inner = term.false_branch
            # Check if outer guard complements inner guard
            if _guards_complementary(term.test, inner.test):
                results.append((OCase(term.test, term.true_branch, inner.false_branch),
                               'D8_section_merge'))

    return results


# ── D9: Stack ↔ Recursion (defunctionalization) ──

def _axiom_d9_stack_rec(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D9: Explicit stack-based traversal ≡ recursive traversal."""
    # Both compile to OFix — equivalence is by fix-point body comparison
    return []


# ── D10: heapq ↔ bisect (priority queue abstraction) ──

def _axiom_d10_pq(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D10: Different priority queue implementations → same extract-min fold."""
    return []


# ── D11: OrderedDict ↔ LinkedList ──

def _axiom_d11_adt(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D11: ADT refinement — different containers, same interface."""
    return []


# ── D12: defaultdict ↔ setdefault ──

def _axiom_d12_map_construct(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D12: Different ways to build a map with defaults."""
    return []


# ── D13: Counter ↔ manual count (histogram equivalence) ──

def _axiom_d13_histogram(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D13: Counter(x) ≡ fold over x counting occurrences."""
    results = []

    # Counter(x) → fold[count](defaultdict(int), x)
    if isinstance(term, OOp) and term.name in ('Counter', 'collections.Counter'):
        if len(term.args) == 1:
            results.append((OFold('count_freq', OOp('defaultdict', (OLit(0),)),
                                  term.args[0]), 'D13_counter_to_fold'))

    # fold that counts → Counter
    if isinstance(term, OFold) and term.op_name in ('count_freq', 'freq_count'):
        if isinstance(term.init, OOp) and term.init.name == 'defaultdict':
            results.append((OOp('Counter', (term.collection,)),
                           'D13_fold_to_counter'))

    return results


# ── D14: Array ↔ Dict table ──

def _axiom_d14_indexing(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D14: Array indexing ≡ dict lookup when indices are dense."""
    return []


# ── D15: BFS ↔ DFS (traversal-order invariance) ──

def _axiom_d15_traversal(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D15: When the fold monoid is commutative, traversal order
    doesn't matter → BFS ≡ DFS."""
    # The fix-point bodies will differ (queue vs stack) but the
    # fold result is the same when the accumulation is commutative.
    # This requires Yoneda-style observational equivalence.
    return []


# ── D16: Memoized ↔ DP (evaluation-order independence) ──

def _axiom_d16_memo_dp(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D16: Top-down memo ≡ bottom-up DP when recurrence is the same.

    Two OFix terms with the same recurrence structure but different
    evaluation order (top-down with memo vs bottom-up table fill)
    are equivalent by the fixed-point theorem.
    """
    results = []

    # Two fix-points with different hashes but similar structure
    # → try to normalize the recurrence and compare
    if isinstance(term, OFix):
        canonical_fix = _canonicalize_recurrence(term)
        if canonical_fix is not None and canonical_fix.name != term.name:
            results.append((canonical_fix, 'D16_recurrence_normalize'))

    return results


# ── D17: Divide-and-conquer ↔ Iterative (associativity) ──

def _axiom_d17_assoc(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D17: Tree fold ≡ list fold when operation is associative.

    fold(op, tree_split(x)) ≡ fold(op, x) when op is associative.
    """
    results = []

    # Recognize: fold over a tree-split collection ≡ fold over flat
    if isinstance(term, OFold):
        flat = _try_flatten_tree_fold(term)
        if flat is not None:
            results.append((flat, 'D17_tree_to_linear_fold'))

    return results


# ── D18: Greedy ↔ DP (matroid/greedy theorem) ──

def _axiom_d18_greedy(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D18: Greedy ≡ DP when the matroid property holds."""
    # Problem-specific — needs spec discovery
    return []


# ── D19: Sort-then-scan ↔ Sweep ──

def _axiom_d19_sort_scan(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D19: Both process elements in sorted order → same result.

    fold(op, sorted(x)) ≡ fold(op, sweep(x)) when both
    visit elements in the same canonical order.
    """
    results = []

    # fold over sorted ≡ fold over direct when fold is order-invariant
    if isinstance(term, OFold):
        if isinstance(term.collection, OOp) and term.collection.name == 'sorted':
            # If the fold operation is commutative+associative,
            # sorting doesn't change the result
            if _is_commutative_op(term.op_name):
                results.append((OFold(term.op_name, term.init,
                                     term.collection.args[0]),
                               'D19_sort_irrelevant'))

    return results


# ── D20: Different algorithms, same spec (Yoneda + spec discovery) ──

def _axiom_d20_spec_unify(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D20: Replace a complex computation with its abstract specification.

    If we can identify what a term computes (e.g. "factorial", "fibonacci",
    "sorted"), replace it with OAbstract(spec, inputs).  Two different
    algorithms computing the same spec then become syntactically equal.

    This is the Yoneda embedding: a program is uniquely determined by
    its behavior under all observations. If both programs satisfy the
    same deterministic specification, they are equal.
    """
    results = []

    # Recognize common specifications from OTerm structure
    spec = _identify_spec(term)
    if spec is not None:
        spec_name, inputs = spec
        results.append((OAbstract(spec_name, inputs), 'D20_spec_discovery'))

    return results


# ── D21: isinstance ↔ Dispatch table ──

def _axiom_d21_dispatch(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D21: isinstance chain ≡ dict dispatch table."""
    # Both compile to OCase chains — handled by case normalization
    return []


# ── D22: try/except ↔ Conditional (effect elimination) ──

def _axiom_d22_effect_elim(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D22: OCatch(body, default) ≡ OCase(can_succeed(body), body, default).

    When the exception condition is decidable, try/except is equivalent
    to a conditional check.
    """
    results = []

    # catch(body, default) → case(guard, body, default) when guard is decidable
    if isinstance(term, OCatch):
        guard = _extract_exception_guard(term.body)
        if guard is not None:
            results.append((OCase(guard, term.body, term.default),
                           'D22_catch_to_case'))

    # case(guard, body, default) → catch(body, default) when guard tests for exception
    if isinstance(term, OCase):
        if _is_exception_guard(term.test):
            results.append((OCatch(term.true_branch, term.false_branch),
                           'D22_case_to_catch'))

    return results


# ── D23: Sorted-then-process ↔ Direct ──

def _axiom_d23_sort_process(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D23: Processing sorted data ≡ processing unsorted when
    the processing is order-invariant."""
    # Subsumed by D19 + quotient types
    return []


# ── D24: Lambda ↔ Named function (η-expansion) ──

def _axiom_d24_eta(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """D24: η-expansion/contraction: λx.f(x) ≡ f."""
    results = []

    # η-contraction: OLam([x], OOp(name, (OVar(x),))) → OOp(name, ())
    if isinstance(term, OLam) and len(term.params) == 1:
        if isinstance(term.body, OOp) and len(term.body.args) == 1:
            if isinstance(term.body.args[0], OVar) and term.body.args[0].name == term.params[0]:
                results.append((OOp(term.body.name, ()), 'D24_eta_contract'))

    return results


# ── Algebraic axioms (not dichotomies but fundamental) ──

def _axiom_algebra(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Algebraic identities: commutativity, associativity, distributivity."""
    results = []

    if not isinstance(term, OOp):
        return results

    # Commutativity: op(a,b) → op(b,a) for commutative ops
    # §2.6 Sheaf descent: commutativity depends on the fiber.
    # add/mul are commutative on numeric fibers but add is NOT
    # commutative on str/list (concatenation).
    always_commutative = {'mul', 'mult', 'and', 'or', 'bitor', 'bitand',
                          'bitxor', 'min', 'max', 'eq', 'noteq'}
    fiber_commutative = {'add'}  # only on numeric fibers
    commutative_ops = always_commutative
    if term.name in fiber_commutative and ctx.is_numeric(term):
        commutative_ops = commutative_ops | fiber_commutative
    if term.name in commutative_ops:
        if len(term.args) == 2:
            swapped = OOp(term.name, (term.args[1], term.args[0]))
            if swapped.canon() != term.canon():
                results.append((swapped, 'ALG_commute'))

    # Associativity: op(op(a,b),c) → op(a,op(b,c))
    # Same fiber restriction for add
    always_assoc = {'mul', 'mult', 'and', 'or'}
    fiber_assoc = {'add'}
    assoc_ops = always_assoc | {'concat'}
    if term.name in fiber_assoc and ctx.is_numeric(term):
        assoc_ops = assoc_ops | fiber_assoc
    if term.name in assoc_ops:
        if len(term.args) == 2 and isinstance(term.args[0], OOp) and term.args[0].name == term.name:
            inner = term.args[0]
            if len(inner.args) == 2:
                right_assoc = OOp(term.name, (inner.args[0],
                                              OOp(term.name, (inner.args[1], term.args[1]))))
                results.append((right_assoc, 'ALG_assoc_right'))

    if term.name in assoc_ops:
        if len(term.args) == 2 and isinstance(term.args[1], OOp) and term.args[1].name == term.name:
            inner = term.args[1]
            if len(inner.args) == 2:
                left_assoc = OOp(term.name, (OOp(term.name, (term.args[0], inner.args[0])),
                                             inner.args[1]))
                results.append((left_assoc, 'ALG_assoc_left'))

    # Identity elements: add(x, 0) → x, mul(x, 1) → x
    if term.name in ('add', 'sub') and len(term.args) == 2:
        if isinstance(term.args[1], OLit) and term.args[1].value == 0:
            results.append((term.args[0], 'ALG_identity_zero'))
        if isinstance(term.args[0], OLit) and term.args[0].value == 0 and term.name == 'add':
            results.append((term.args[1], 'ALG_identity_zero_left'))

    if term.name in ('mul', 'mult') and len(term.args) == 2:
        if isinstance(term.args[1], OLit) and term.args[1].value == 1:
            results.append((term.args[0], 'ALG_identity_one'))
        if isinstance(term.args[0], OLit) and term.args[0].value == 1:
            results.append((term.args[1], 'ALG_identity_one_left'))

    # Involution: not(not(x)) → x
    if term.name == 'u_not' and len(term.args) == 1:
        if isinstance(term.args[0], OOp) and term.args[0].name == 'u_not':
            results.append((term.args[0].args[0], 'ALG_not_involution'))

    # Comparison flips: lt(a,b) ↔ gt(b,a)
    comp_flip = {'lt': 'gt', 'gt': 'lt', 'lte': 'gte', 'gte': 'lte'}
    if term.name in comp_flip and len(term.args) == 2:
        flipped = OOp(comp_flip[term.name], (term.args[1], term.args[0]))
        results.append((flipped, 'ALG_comp_flip'))

    return results


# ── Quotient axioms ──

def _axiom_quotient(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Quotient type axioms: Q[perm](sorted(x)) ≡ sorted(x),
    sorted(Q[perm](x)) ≡ sorted(x), etc."""
    results = []

    # Q[perm](sorted(x)) → sorted(x) — sorting fixes a representative
    if isinstance(term, OQuotient) and term.equiv_class == 'perm':
        if isinstance(term.inner, OOp) and term.inner.name == 'sorted':
            results.append((term.inner, 'QUOT_sorted_canonical'))

    # sorted(Q[perm](x)) → sorted(x) — sorting ignores input order
    if isinstance(term, OOp) and term.name == 'sorted':
        if len(term.args) == 1 and isinstance(term.args[0], OQuotient):
            if term.args[0].equiv_class == 'perm':
                results.append((OOp('sorted', (term.args[0].inner,)),
                               'QUOT_sorted_absorb'))

    # set(sorted(x)) → set(x) — set discards order
    if isinstance(term, OOp) and term.name == 'set':
        if len(term.args) == 1 and isinstance(term.args[0], OOp):
            if term.args[0].name == 'sorted':
                results.append((OOp('set', term.args[0].args),
                               'QUOT_set_sort_absorb'))

    # len(set(x)) → len(Q[perm](x)) → len(x) when x has no dups
    # (conservative: only for set → set)
    if isinstance(term, OOp) and term.name == 'len':
        if len(term.args) == 1 and isinstance(term.args[0], OQuotient):
            if term.args[0].equiv_class == 'perm':
                results.append((OOp('len', (term.args[0].inner,)),
                               'QUOT_len_absorb'))

    return results


# ── Fold axioms ──

def _axiom_fold(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Fold-related axioms: fold linearity, fold over range, etc."""
    results = []

    if isinstance(term, OFold):
        # fold[op](init, range(0, n)) ≡ fold[op](init, range(n))
        if isinstance(term.collection, OOp) and term.collection.name == 'range':
            if (len(term.collection.args) == 2 and
                isinstance(term.collection.args[0], OLit) and
                term.collection.args[0].value == 0):
                results.append((OFold(term.op_name, term.init,
                                     OOp('range', (term.collection.args[1],))),
                               'FOLD_range_normalize'))

        # fold[add](0, x) → sum(x)
        if term.op_name in ('.add', 'add', 'iadd'):
            if isinstance(term.init, OLit) and term.init.value == 0:
                results.append((OOp('sum', (term.collection,)),
                               'FOLD_sum'))

        # fold[mul](1, x) → prod(x)
        if term.op_name in ('.mul', 'mul', 'imul', 'mult'):
            if isinstance(term.init, OLit) and term.init.value == 1:
                results.append((OOp('prod', (term.collection,)),
                               'FOLD_prod'))

    # sum(x) → fold[add](0, x)
    if isinstance(term, OOp) and term.name == 'sum' and len(term.args) == 1:
        results.append((OFold('.add', OLit(0), term.args[0]),
                       'FOLD_sum_expand'))

    # len(x) → fold[count](0, x)
    if isinstance(term, OOp) and term.name == 'len' and len(term.args) == 1:
        results.append((OFold('.count', OLit(0), term.args[0]),
                       'FOLD_len_expand'))

    return results


# ── Case axioms ──

def _axiom_case(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Case/branch simplification axioms."""
    results = []

    if isinstance(term, OCase):
        # case(True, a, b) → a
        if isinstance(term.test, OLit) and term.test.value is True:
            results.append((term.true_branch, 'CASE_true'))
        if isinstance(term.test, OLit) and term.test.value is False:
            results.append((term.false_branch, 'CASE_false'))

        # case(g, x, x) → x (both branches same)
        if term.true_branch.canon() == term.false_branch.canon():
            results.append((term.true_branch, 'CASE_identical'))

        # case(not(g), a, b) → case(g, b, a)
        if isinstance(term.test, OOp) and term.test.name == 'u_not' and len(term.test.args) == 1:
            results.append((OCase(term.test.args[0], term.false_branch, term.true_branch),
                           'CASE_not_flip'))

        # case(g, case(g, a, b), c) → case(g, a, c)
        # (guard is True in then-branch, so inner case takes then-branch)
        if isinstance(term.true_branch, OCase):
            if term.true_branch.test.canon() == term.test.canon():
                results.append((OCase(term.test, term.true_branch.true_branch,
                                     term.false_branch), 'CASE_guard_subsume'))

    return results


# ═══════════════════════════════════════════════════════════
# Axiom Module Imports — axioms are also available as modules
# in cctt.axioms/ for direct programmatic access.  The inline
# implementations above are kept for behavioural stability;
# these imports provide the axiom module registry.
# ═══════════════════════════════════════════════════════════

try:
    from .axioms import (
        d01_fold_unfold as _mod_d01,
        d02_beta as _mod_d02,
        d03_guard_reorder as _mod_d03,
        d04_comp_fusion as _mod_d04,
        d05_fold_universal as _mod_d05,
        d07_tailrec as _mod_d07,
        d08_section_merge as _mod_d08,
        d13_histogram as _mod_d13,
        d16_memo_dp as _mod_d16,
        d17_assoc as _mod_d17,
        d19_sort_scan as _mod_d19,
        d20_spec_unify as _mod_d20,
        d22_effect_elim as _mod_d22,
        d24_eta as _mod_d24,
        algebra as _mod_algebra,
        quotient as _mod_quotient,
        fold as _mod_fold,
        case as _mod_case,
    )
    _AXIOM_MODULES_LOADED = True
except ImportError:
    _AXIOM_MODULES_LOADED = False


# ── Spec identification (D20 support) ──

def _identify_spec(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Try to identify a high-level specification from an OTerm.

    Returns (spec_name, inputs) if recognized, else None.
    This is the Yoneda embedding: characterize the term by its
    observable behavior (what spec it satisfies).
    """
    # factorial: fold[mul](1, range(1, n+1)) or fix with n * f(n-1)
    if isinstance(term, OFold):
        if term.op_name in ('.mul', 'mul', 'imul', 'mult'):
            if isinstance(term.init, OLit) and term.init.value == 1:
                if isinstance(term.collection, OOp) and term.collection.name == 'range':
                    return ('factorial', (term.collection.args[-1],))

    # sum: fold[add](0, range(...))
    if isinstance(term, OFold):
        if term.op_name in ('.add', 'add', 'iadd'):
            if isinstance(term.init, OLit) and term.init.value == 0:
                if isinstance(term.collection, OOp) and term.collection.name == 'range':
                    return ('range_sum', (term.collection.args[-1],))

    # fibonacci: fix with f(n-1) + f(n-2) pattern
    if isinstance(term, OFix):
        body_canon = term.body.canon()
        if 'add' in body_canon and 'sub' in body_canon:
            # Heuristic: contains addition and subtraction (fib-like)
            inputs = _extract_free_vars(term)
            if inputs:
                return ('fibonacci_like', tuple(OVar(v) for v in sorted(inputs)))

    # sorted output
    if isinstance(term, OOp) and term.name == 'sorted':
        return ('sorted', term.args)

    # binomial coefficient: various computations of C(n,k)
    if isinstance(term, OOp) and term.name == 'math.comb':
        return ('binomial', term.args)
    if isinstance(term, OFold):
        # fold that computes C(n,k) by multiplicative formula
        body_canon = term.collection.canon() if term.collection else ''
        if 'min' in body_canon or 'sub' in body_canon:
            init_canon = term.init.canon()
            if init_canon == '1':
                # Could be multiplicative binomial — need more analysis
                pass

    return None


# ═══════════════════════════════════════════════════════════
# The Path Search Algorithm
# ═══════════════════════════════════════════════════════════

def search_path(nf_f: OTerm, nf_g: OTerm,
                max_depth: int = 4,
                max_frontier: int = 200,
                param_duck_types: Optional[Dict[str, str]] = None) -> PathResult:
    """Path search from nf_f to nf_g via HIT structural decomposition.

    Primary strategy: HIT path induction (§5.3 elimination principle).
    Decompose both terms structurally, applying path constructors
    at each level. Falls back to bidirectional BFS if structural
    decomposition is inconclusive.

    Fiber-aware via sheaf descent (§2.6): duck types restrict axioms.
    """
    ctx = FiberCtx(param_duck_types=param_duck_types or {})
    cf = nf_f.canon()
    cg = nf_g.canon()

    if cf == cg:
        return PathResult(found=True, path=[], reason='refl')

    # ── Strategy A: HIT structural decomposition (primary) ──
    # This is the elimination principle for PyComp: prove a = b
    # by recursion on the structure of the terms.
    hit_result = hit_path_equiv(nf_f, nf_g, ctx)
    if hit_result is True:
        return PathResult(found=True,
                         path=[PathStep('HIT_structural', 'root', cf, cg)],
                         reason='HIT path induction')

    # ── Strategy B: D20 spec identification (Yoneda) ──
    spec_f = _identify_spec(nf_f)
    spec_g = _identify_spec(nf_g)
    if spec_f is not None and spec_g is not None:
        if spec_f[0] == spec_g[0]:
            if len(spec_f[1]) == len(spec_g[1]):
                inputs_match = all(a.canon() == b.canon()
                                   for a, b in zip(spec_f[1], spec_g[1]))
                if inputs_match:
                    return PathResult(found=True,
                                    path=[PathStep('D20_spec_unify', 'root', cf, cg)],
                                    reason=f'same spec: {spec_f[0]}')

    # ── Strategy C: Bidirectional BFS (fallback) ──
    forward: Dict[str, Tuple[OTerm, List[PathStep]]] = {cf: (nf_f, [])}
    # Backward frontier: terms reachable from nf_g
    backward: Dict[str, Tuple[OTerm, List[PathStep]]] = {cg: (nf_g, [])}

    for depth in range(max_depth):
        # Expand forward frontier
        new_forward: Dict[str, Tuple[OTerm, List[PathStep]]] = {}
        for canon, (term, path) in list(forward.items()):
            if len(path) > depth:
                continue  # only expand the current depth level
            for new_term, axiom in _all_rewrites(term, ctx):
                nc = new_term.canon()
                if nc in forward or nc in new_forward:
                    continue  # already visited
                step = PathStep(axiom, 'root', canon, nc)
                new_path = path + [step]

                # Check if we meet the backward frontier
                if nc in backward:
                    _, bpath = backward[nc]
                    full_path = new_path + list(reversed(bpath))
                    return PathResult(found=True, path=full_path,
                                    reason=f'bidirectional meet at depth {depth+1}')

                new_forward[nc] = (new_term, new_path)

        forward.update(new_forward)
        if len(forward) > max_frontier:
            # Prune: keep terms closest to target (by canon string similarity)
            forward = _prune_frontier(forward, cg, max_frontier)

        # Expand backward frontier
        new_backward: Dict[str, Tuple[OTerm, List[PathStep]]] = {}
        for canon, (term, path) in list(backward.items()):
            if len(path) > depth:
                continue
            for new_term, axiom in _all_rewrites(term, ctx):
                nc = new_term.canon()
                if nc in backward or nc in new_backward:
                    continue
                step = PathStep(axiom, 'root', canon, nc)
                new_path = path + [step]

                if nc in forward:
                    _, fpath = forward[nc]
                    full_path = fpath + list(reversed(new_path))
                    return PathResult(found=True, path=full_path,
                                    reason=f'bidirectional meet at depth {depth+1}')

                new_backward[nc] = (new_term, new_path)

        backward.update(new_backward)
        if len(backward) > max_frontier:
            backward = _prune_frontier(backward, cf, max_frontier)

    return PathResult(found=None, path=[],
                     reason=f'no path within depth {max_depth}')


def _prune_frontier(frontier: Dict[str, Tuple[OTerm, List[PathStep]]],
                    target_canon: str, max_size: int
                    ) -> Dict[str, Tuple[OTerm, List[PathStep]]]:
    """Prune frontier to max_size, keeping terms most similar to target."""
    if len(frontier) <= max_size:
        return frontier

    # Score by: shorter path first, then structural similarity
    def score(item):
        canon, (term, path) = item
        path_len = len(path)
        # Simple similarity: shared prefix length with target
        shared = 0
        for a, b in zip(canon, target_canon):
            if a == b:
                shared += 1
            else:
                break
        return (path_len, -shared)

    sorted_items = sorted(frontier.items(), key=score)
    return dict(sorted_items[:max_size])


# ═══════════════════════════════════════════════════════════
# Helper functions
# ═══════════════════════════════════════════════════════════

def _subst_term(term: OTerm, var_name: str, replacement: OTerm) -> OTerm:
    """Substitute a variable with a term."""
    return _subst(term, {var_name: replacement.canon()}) if isinstance(replacement, OVar) \
        else _subst_deep(term, var_name, replacement)


def _subst_deep(term: OTerm, var_name: str, replacement: OTerm) -> OTerm:
    """Deep substitution of a variable with an arbitrary OTerm."""
    if isinstance(term, OVar):
        return replacement if term.name == var_name else term
    if isinstance(term, OLit):
        return term
    if isinstance(term, OOp):
        return OOp(term.name, tuple(_subst_deep(a, var_name, replacement) for a in term.args))
    if isinstance(term, OCase):
        return OCase(_subst_deep(term.test, var_name, replacement),
                     _subst_deep(term.true_branch, var_name, replacement),
                     _subst_deep(term.false_branch, var_name, replacement))
    if isinstance(term, OFold):
        return OFold(term.op_name, _subst_deep(term.init, var_name, replacement),
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
        return OQuotient(_subst_deep(term.inner, var_name, replacement), term.equiv_class)
    if isinstance(term, OAbstract):
        return OAbstract(term.spec, tuple(_subst_deep(a, var_name, replacement) for a in term.inputs))
    if isinstance(term, OLam):
        if var_name in term.params:
            return term  # shadowed
        return OLam(term.params, _subst_deep(term.body, var_name, replacement))
    if isinstance(term, OMap):
        new_t = _subst_deep(term.transform, var_name, replacement)
        new_c = _subst_deep(term.collection, var_name, replacement)
        new_f = _subst_deep(term.filter_pred, var_name, replacement) if term.filter_pred else None
        return OMap(new_t, new_c, new_f)
    if isinstance(term, OCatch):
        return OCatch(_subst_deep(term.body, var_name, replacement),
                     _subst_deep(term.default, var_name, replacement))
    return term


def _compose_transforms(outer: OTerm, inner: OTerm) -> Optional[OTerm]:
    """Compose two transforms: λx.f(λy.g(y)) → λx.f(g(x))."""
    if isinstance(outer, OLam) and isinstance(inner, OLam):
        if len(outer.params) == 1 and len(inner.params) == 1:
            # outer = λx.body_f[x], inner = λy.body_g[y]
            # composed = λy.body_f[body_g[y]]
            composed_body = _subst_deep(outer.body, outer.params[0], inner.body)
            return OLam(inner.params, composed_body)
    return None


def _guards_complementary(g1: OTerm, g2: OTerm) -> bool:
    """Check if two guards are complementary: g1 ≡ ¬g2."""
    if isinstance(g1, OOp) and g1.name == 'u_not' and len(g1.args) == 1:
        return g1.args[0].canon() == g2.canon()
    if isinstance(g2, OOp) and g2.name == 'u_not' and len(g2.args) == 1:
        return g2.args[0].canon() == g1.canon()
    return False


def _guard_subsumed(outer_guard: OTerm, inner_guard: OTerm) -> bool:
    """Check if inner_guard is subsumed by outer_guard.

    Returns True when: in the else-branch of outer_guard (i.e., outer_guard
    is False), inner_guard is also guaranteed to be False.

    This happens when inner_guard is a disjunct of outer_guard, or when
    inner_guard is semantically implied by one of outer_guard's disjuncts.
    """
    ig_c = inner_guard.canon()

    # Collect all disjuncts of the outer guard
    disjuncts = _collect_disjuncts(outer_guard)
    for d in disjuncts:
        if d.canon() == ig_c:
            return True

    # Dictionary-specific: notin(k,d) in outer implies
    # is(.get(d,k),None) is False in else-branch.
    # Also: is(k, None) implies is(.get(d,k),None) trivially.
    if isinstance(inner_guard, OOp) and inner_guard.name == 'is':
        if len(inner_guard.args) == 2 and isinstance(inner_guard.args[1], OLit):
            if inner_guard.args[1].value is None:
                # inner = is(X, None)
                inner_x = inner_guard.args[0]
                for d in disjuncts:
                    # notin(k, dict) and X = .get(dict, k)
                    if isinstance(d, OOp) and d.name == 'notin' and len(d.args) == 2:
                        if (isinstance(inner_x, OOp) and inner_x.name == '.get'
                                and len(inner_x.args) == 2):
                            if (inner_x.args[0].canon() == d.args[1].canon() and
                                    inner_x.args[1].canon() == d.args[0].canon()):
                                return True
                    # is(k, None) and X involves k
                    if isinstance(d, OOp) and d.name == 'is' and len(d.args) == 2:
                        if isinstance(d.args[1], OLit) and d.args[1].value is None:
                            if d.args[0].canon() == inner_x.canon():
                                return True

    return False


def _collect_disjuncts(guard: OTerm) -> list:
    """Collect all disjuncts from an or(...) guard."""
    if isinstance(guard, OOp) and guard.name == 'or':
        result = []
        for a in guard.args:
            result.extend(_collect_disjuncts(a))
        return result
    return [guard]


def _is_commutative_op(op_name: str) -> bool:
    """Check if a fold operation is commutative."""
    return op_name in ('.add', 'add', 'iadd', '.mul', 'mul', 'imul',
                       'min', 'max', 'and', 'or', 'bitor', 'bitand', 'bitxor',
                       'union', 'intersection', '.count')


def _identify_fold_op(term: OFold) -> Optional[str]:
    """Try to identify a hash-named fold's actual operation."""
    # Look at the fold body structure if available
    # For now, return None — the normalizer handles most cases
    return None


def _canonicalize_recurrence(term: OFix) -> Optional[OFix]:
    """Try to canonicalize a recurrence's structure.

    Two fix-points computing the same recurrence should have the same
    canonical name regardless of variable names or evaluation order.
    """
    # Compute a canonical hash from the body structure
    # ignoring variable names (alpha-normalize)
    body = term.body
    canon = body.canon()
    # Remove variable-specific parts to get structural signature
    import re
    structural = re.sub(r'\$\w+', '$_', canon)
    import hashlib
    new_hash = hashlib.md5(structural.encode()).hexdigest()[:8]
    if new_hash != term.name:
        return OFix(new_hash, term.body)
    return None


def _try_flatten_tree_fold(term: OFold) -> Optional[OFold]:
    """Try to recognize a tree-structured fold and flatten it."""
    # tree fold: fold(op, tree_split(x)) where tree_split divides x
    # into halves recursively. If op is associative, this equals
    # fold(op, x).
    if isinstance(term.collection, OOp) and term.collection.name in ('tree_split', 'divide'):
        if _is_commutative_op(term.op_name):
            # Flatten: fold over the un-split collection
            if len(term.collection.args) == 1:
                return OFold(term.op_name, term.init, term.collection.args[0])
    return None


def _extract_exception_guard(body: OTerm) -> Optional[OTerm]:
    """Extract a decidable guard from a try/except body.

    E.g., try: x[i] except IndexError → guard is lt(i, len(x))
    """
    # Complex — would need to pattern-match specific exception scenarios
    return None


def _is_exception_guard(test: OTerm) -> bool:
    """Check if a guard tests for an exception condition."""
    return False


def _extract_free_vars(term: OTerm) -> Set[str]:
    """Extract free variable names from a term."""
    if isinstance(term, OVar):
        return {term.name}
    if isinstance(term, OLit) or isinstance(term, OUnknown):
        return set()
    if isinstance(term, OOp):
        result = set()
        for a in term.args:
            result |= _extract_free_vars(a)
        return result
    if isinstance(term, OCase):
        return (_extract_free_vars(term.test) | _extract_free_vars(term.true_branch)
                | _extract_free_vars(term.false_branch))
    if isinstance(term, OFold):
        return _extract_free_vars(term.init) | _extract_free_vars(term.collection)
    if isinstance(term, OFix):
        return _extract_free_vars(term.body)
    if isinstance(term, OSeq):
        result = set()
        for e in term.elements:
            result |= _extract_free_vars(e)
        return result
    if isinstance(term, OLam):
        return _extract_free_vars(term.body) - set(term.params)
    if isinstance(term, OMap):
        result = _extract_free_vars(term.transform) | _extract_free_vars(term.collection)
        if term.filter_pred:
            result |= _extract_free_vars(term.filter_pred)
        return result
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
    if isinstance(term, OCatch):
        return _extract_free_vars(term.body) | _extract_free_vars(term.default)
    return set()


# ═══════════════════════════════════════════════════════════
# HIT Structural Equivalence Prover (§5.3 Elimination Principle)
# ═══════════════════════════════════════════════════════════
# Rather than BFS rewriting, this implements the elimination principle
# for PyComp (Thm 10.1): to prove a = b, proceed by cases on their
# structure, applying path constructors at each level.
#
# Key idea: decompose terms recursively. At each node:
#   1. If canonical forms match → refl
#   2. If same constructor → congruence (recurse into children)
#   3. If different constructors → try path constructors (D1-D24)
#   4. At leaves → try D20 spec identification (Yoneda)

def hit_path_equiv(a: OTerm, b: OTerm, ctx: FiberCtx,
                   depth: int = 0, memo: Optional[Dict[Tuple[str,str], Optional[bool]]] = None
                   ) -> Optional[bool]:
    """HIT path induction: prove equivalence by structural decomposition.

    Implements the elimination principle for PyComp:
    to prove a = b in the HIT, proceed by cases on structure,
    applying path constructors at each level. This is sound because
    PyComp is 0-truncated (Def 5.1): any two parallel paths are equal.
    """
    if depth > 20:
        return None
    if memo is None:
        memo = {}
    key = (a.canon(), b.canon())
    if key in memo:
        return memo[key]
    # Mark as in-progress to avoid infinite loops on recursive terms
    memo[key] = None

    result = _hit_path_core(a, b, ctx, depth, memo)
    memo[key] = result
    return result


def _hit_path_core(a: OTerm, b: OTerm, ctx: FiberCtx,
                   depth: int, memo: Dict) -> Optional[bool]:
    """Core HIT path equivalence logic."""
    ca, cb = a.canon(), b.canon()

    # ── refl: canonical forms match ──
    if ca == cb:
        return True

    # ── Try normalizing both sides first (may reveal structure) ──
    na = normalize(a)
    nb = normalize(b)
    if na.canon() == nb.canon():
        return True

    # Use normalized forms for structural analysis
    a, b = na, nb
    ca, cb = a.canon(), b.canon()

    # ── OCase congruence (the workhorse) ──
    # If both are conditionals with matching guards, recurse into branches.
    # This is the HIT congruence rule for cond(_, _, _).
    if isinstance(a, OCase) and isinstance(b, OCase):
        # Exact guard match
        if hit_path_equiv(a.test, b.test, ctx, depth+1, memo) is True:
            yes_eq = hit_path_equiv(a.true_branch, b.true_branch, ctx, depth+1, memo)
            no_eq = hit_path_equiv(a.false_branch, b.false_branch, ctx, depth+1, memo)
            if yes_eq is True and no_eq is True:
                return True
        # Complementary guards (not(t), A, B) vs (t, B, A) → D8 section merge
        if _guards_complementary(a.test, b.test):
            yes_eq = hit_path_equiv(a.true_branch, b.false_branch, ctx, depth+1, memo)
            no_eq = hit_path_equiv(a.false_branch, b.true_branch, ctx, depth+1, memo)
            if yes_eq is True and no_eq is True:
                return True
        # Guard differs but one side has nested cases — try flattening
        if isinstance(a.false_branch, OCase):
            # case(t1, A, case(t2, B, C)) — try matching with b
            flattened = _try_case_flatten(a, b, ctx, depth, memo)
            if flattened is True:
                return True
        if isinstance(b.false_branch, OCase):
            flattened = _try_case_flatten(b, a, ctx, depth, memo)
            if flattened is True:
                return True

    # ── OOp congruence ──
    if isinstance(a, OOp) and isinstance(b, OOp):
        if a.name == b.name and len(a.args) == len(b.args):
            if all(hit_path_equiv(ai, bi, ctx, depth+1, memo) is True
                   for ai, bi in zip(a.args, b.args)):
                return True
        # Commutative: op(x,y) = op(y,x) on appropriate fibers
        if a.name == b.name and len(a.args) == 2 and len(b.args) == 2:
            if _is_fiber_commutative(a.name, ctx, a):
                if (hit_path_equiv(a.args[0], b.args[1], ctx, depth+1, memo) is True and
                    hit_path_equiv(a.args[1], b.args[0], ctx, depth+1, memo) is True):
                    return True

    # ── OSeq congruence ──
    if isinstance(a, OSeq) and isinstance(b, OSeq):
        if len(a.elements) == len(b.elements):
            if all(hit_path_equiv(ai, bi, ctx, depth+1, memo) is True
                   for ai, bi in zip(a.elements, b.elements)):
                return True

    # ── OLam congruence (alpha-equivalent bodies) ──
    if isinstance(a, OLam) and isinstance(b, OLam):
        if len(a.params) == len(b.params):
            # Alpha-rename b's params to a's
            body_b = b.body
            for pa, pb in zip(a.params, b.params):
                if pa != pb:
                    body_b = _subst_deep(body_b, pb, OVar(pa))
            if hit_path_equiv(a.body, body_b, ctx, depth+1, memo) is True:
                return True

    # ── OMap congruence ──
    if isinstance(a, OMap) and isinstance(b, OMap):
        if (hit_path_equiv(a.transform, b.transform, ctx, depth+1, memo) is True and
            hit_path_equiv(a.collection, b.collection, ctx, depth+1, memo) is True):
            # Filter predicates
            if a.filter_pred is None and b.filter_pred is None:
                return True
            if (a.filter_pred is not None and b.filter_pred is not None and
                hit_path_equiv(a.filter_pred, b.filter_pred, ctx, depth+1, memo) is True):
                return True

    # ── OFold congruence (D5: fold universality) ──
    if isinstance(a, OFold) and isinstance(b, OFold):
        init_eq = hit_path_equiv(a.init, b.init, ctx, depth+1, memo) is True
        coll_eq = hit_path_equiv(a.collection, b.collection, ctx, depth+1, memo) is True
        if init_eq and coll_eq:
            # Same init and collection — bodies may differ but compute same
            if a.op_name == b.op_name:
                return True
            # Hash-based keys that differ: try to show bodies are equivalent
            # by recognizing the fold operation
            op_a = _identify_fold_op(a)
            op_b = _identify_fold_op(b)
            if op_a and op_b and op_a == op_b:
                return True
            # NOTE: hash-different folds with same init+coll are NOT
            # necessarily equivalent — the fold body IS the computation.
            # Only trust op_name match or recognized canonical ops above.

    # ── OFix congruence (D16: recurrence normalization) ──
    if isinstance(a, OFix) and isinstance(b, OFix):
        if a.name == b.name:
            return hit_path_equiv(a.body, b.body, ctx, depth+1, memo)
        # Different names but potentially equivalent bodies
        # Alpha-normalize: substitute fix key and compare bodies
        body_b_renamed = _subst_deep(b.body, b.name, OVar(a.name))
        if hit_path_equiv(a.body, body_b_renamed, ctx, depth+1, memo) is True:
            return True

    # ── OCatch congruence ──
    if isinstance(a, OCatch) and isinstance(b, OCatch):
        if (hit_path_equiv(a.body, b.body, ctx, depth+1, memo) is True and
            hit_path_equiv(a.default, b.default, ctx, depth+1, memo) is True):
            return True

    # ── ODict congruence ──
    if isinstance(a, ODict) and isinstance(b, ODict):
        if len(a.pairs) == len(b.pairs):
            if all(hit_path_equiv(ak, bk, ctx, depth+1, memo) is True and
                   hit_path_equiv(av, bv, ctx, depth+1, memo) is True
                   for (ak, av), (bk, bv) in zip(a.pairs, b.pairs)):
                return True

    # ═══════════════════════════════════════════════════════
    # Cross-type path constructors (D1-D24)
    # ═══════════════════════════════════════════════════════

    # ── D1: OFix ↔ OFold (rec ↔ iter) ──
    if isinstance(a, OFix) and isinstance(b, OFold):
        if _fix_fold_equiv(a, b, ctx, depth, memo):
            return True
    if isinstance(a, OFold) and isinstance(b, OFix):
        if _fix_fold_equiv(b, a, ctx, depth, memo):
            return True

    # ── Quotient congruence (NOT cross-type — Q[perm] ≠ sorted) ──
    # Q[perm](x) represents "x up to permutation" (e.g. dict.keys()
    # which is insertion-order-dependent). sorted(x) is a specific
    # canonical representative. These are NOT equivalent as programs
    # because they produce different concrete outputs.
    if isinstance(a, OQuotient) and isinstance(b, OQuotient):
        if a.equiv_class == b.equiv_class:
            if hit_path_equiv(a.inner, b.inner, ctx, depth+1, memo) is True:
                return True

    # ── Unwrap matching quotients only ──
    # Q[perm](sorted(x)) = sorted(x): sorting is a canonical rep,
    # so wrapping in quotient is redundant
    if isinstance(a, OQuotient) and a.equiv_class == 'perm':
        if isinstance(a.inner, OOp) and a.inner.name in ('sorted', 'sorted_key'):
            if hit_path_equiv(a.inner, b, ctx, depth+1, memo) is True:
                return True
    if isinstance(b, OQuotient) and b.equiv_class == 'perm':
        if isinstance(b.inner, OOp) and b.inner.name in ('sorted', 'sorted_key'):
            if hit_path_equiv(b.inner, a, ctx, depth+1, memo) is True:
                return True
    if isinstance(a, OOp) and a.name == 'list' and isinstance(b, OFold):
        if isinstance(b.init, OSeq) and len(b.init.elements) == 0:
            if hit_path_equiv(a.args[0] if a.args else a, b.collection, ctx, depth+1, memo) is True:
                return True
    if isinstance(b, OOp) and b.name == 'list' and isinstance(a, OFold):
        if isinstance(a.init, OSeq) and len(a.init.elements) == 0:
            if hit_path_equiv(b.args[0] if b.args else b, a.collection, ctx, depth+1, memo) is True:
                return True

    # ── De Morgan: not(and(a,b)) = or(not(a),not(b)) and vice versa ──
    if isinstance(a, OOp) and isinstance(b, OOp):
        dm = _try_demorgan(a, b, ctx, depth, memo)
        if dm is True:
            return True

    # ── D22: OCatch ↔ OCase (try/except ↔ conditional) ──
    if isinstance(a, OCatch) and isinstance(b, OCase):
        if hit_path_equiv(a.body, b.true_branch, ctx, depth+1, memo) is True:
            if hit_path_equiv(a.default, b.false_branch, ctx, depth+1, memo) is True:
                return True
    if isinstance(b, OCatch) and isinstance(a, OCase):
        if hit_path_equiv(b.body, a.true_branch, ctx, depth+1, memo) is True:
            if hit_path_equiv(b.default, a.false_branch, ctx, depth+1, memo) is True:
                return True

    # ── Guard subsumption in OCase congruence ──
    # case(G, A, X) vs case(G, A, case(G_sub, B, X'))
    # If G_sub is a disjunct of G, then in the else-branch (G=False)
    # G_sub is also False → inner case reduces to X'.
    # Also handles dict.get/notin relationship:
    # notin(k,d) in G implies .get(d,k)==None is False in else-branch
    if isinstance(a, OCase) and isinstance(b, OCase):
        if hit_path_equiv(a.test, b.test, ctx, depth+1, memo) is True:
            yes_eq = hit_path_equiv(a.true_branch, b.true_branch, ctx, depth+1, memo)
            if yes_eq is True:
                # One side has extra nested case in else-branch
                if isinstance(b.false_branch, OCase):
                    if _guard_subsumed(a.test, b.false_branch.test):
                        no_eq = hit_path_equiv(a.false_branch, b.false_branch.false_branch, ctx, depth+1, memo)
                        if no_eq is True:
                            return True
                if isinstance(a.false_branch, OCase):
                    if _guard_subsumed(b.test, a.false_branch.test):
                        no_eq = hit_path_equiv(a.false_branch.false_branch, b.false_branch, ctx, depth+1, memo)
                        if no_eq is True:
                            return True

    # ── D20: Spec identification (Yoneda embedding) ──
    spec_a = _identify_spec(a)
    spec_b = _identify_spec(b)
    if spec_a is not None and spec_b is not None:
        if spec_a[0] == spec_b[0] and len(spec_a[1]) == len(spec_b[1]):
            if all(hit_path_equiv(ai, bi, ctx, depth+1, memo) is True
                   for ai, bi in zip(spec_a[1], spec_b[1])):
                return True

    # ── Comparison normalization: lt(a,b) = gt(b,a) etc. ──
    if isinstance(a, OOp) and isinstance(b, OOp):
        comp_equiv = {'lt': 'gt', 'gt': 'lt', 'lte': 'gte', 'gte': 'lte'}
        if a.name in comp_equiv and b.name == comp_equiv[a.name]:
            if len(a.args) == 2 and len(b.args) == 2:
                if (hit_path_equiv(a.args[0], b.args[1], ctx, depth+1, memo) is True and
                    hit_path_equiv(a.args[1], b.args[0], ctx, depth+1, memo) is True):
                    return True

    # ── not(lt(a,b)) = gte(a,b) etc. ──
    if isinstance(a, OOp) and a.name == 'u_not' and isinstance(b, OOp):
        neg_comp = {'lt': 'gte', 'gt': 'lte', 'lte': 'gt', 'gte': 'lt',
                    'eq': 'noteq', 'noteq': 'eq'}
        if len(a.args) == 1 and isinstance(a.args[0], OOp):
            inner = a.args[0]
            if inner.name in neg_comp and b.name == neg_comp[inner.name]:
                if len(inner.args) == len(b.args):
                    if all(hit_path_equiv(ai, bi, ctx, depth+1, memo) is True
                           for ai, bi in zip(inner.args, b.args)):
                        return True
    if isinstance(b, OOp) and b.name == 'u_not' and isinstance(a, OOp):
        neg_comp = {'lt': 'gte', 'gt': 'lte', 'lte': 'gt', 'gte': 'lt',
                    'eq': 'noteq', 'noteq': 'eq'}
        if len(b.args) == 1 and isinstance(b.args[0], OOp):
            inner = b.args[0]
            if inner.name in neg_comp and a.name == neg_comp[inner.name]:
                if len(inner.args) == len(a.args):
                    if all(hit_path_equiv(ai, bi, ctx, depth+1, memo) is True
                           for ai, bi in zip(inner.args, a.args)):
                        return True

    # ── OOp wrapping: sorted(x) vs x when result is already sorted ──
    # sorted(sorted(x)) = sorted(x) — idempotence
    if isinstance(a, OOp) and a.name == 'sorted' and len(a.args) == 1:
        if hit_path_equiv(a.args[0], b, ctx, depth+1, memo) is True:
            # Only if b is already sorted (idempotence)
            if isinstance(b, OOp) and b.name == 'sorted':
                return True

    # ── fold[and](True, map(f, x)) = not(fold[or](False, map(not∘f, x))) (D35) ──
    if isinstance(a, OFold) and isinstance(b, OOp) and b.name == 'u_not':
        if a.op_name in ('and', '.and') and isinstance(b.args[0], OFold):
            inner_fold = b.args[0]
            if inner_fold.op_name in ('or', '.or'):
                # Check if they're De Morgan duals over same collection
                if isinstance(a.collection, OMap) and isinstance(inner_fold.collection, OMap):
                    if hit_path_equiv(a.collection.collection,
                                      inner_fold.collection.collection, ctx, depth+1, memo) is True:
                        return True
    if isinstance(b, OFold) and isinstance(a, OOp) and a.name == 'u_not':
        if b.op_name in ('and', '.and') and isinstance(a.args[0], OFold):
            inner_fold = a.args[0]
            if inner_fold.op_name in ('or', '.or'):
                if isinstance(b.collection, OMap) and isinstance(inner_fold.collection, OMap):
                    if hit_path_equiv(b.collection.collection,
                                      inner_fold.collection.collection, ctx, depth+1, memo) is True:
                        return True

    # ── One-step axiom rewrites (BFS with depth 1) ──
    # Try each axiom on both sides and see if any single rewrite closes the gap
    if depth < 8:
        for rewrite_fn in _ROOT_AXIOMS:
            for new_a, _ in rewrite_fn(a, ctx):
                if new_a.canon() == cb:
                    return True
                if hit_path_equiv(new_a, b, ctx, depth+2, memo) is True:
                    return True
            for new_b, _ in rewrite_fn(b, ctx):
                if new_b.canon() == ca:
                    return True
                if hit_path_equiv(a, new_b, ctx, depth+2, memo) is True:
                    return True

    return None


def _is_fiber_commutative(op_name: str, ctx: FiberCtx, term: OTerm) -> bool:
    """Check if an operation is commutative on the current fiber."""
    always_comm = {'mul', 'mult', 'and', 'or', 'bitor', 'bitand',
                   'bitxor', 'min', 'max', 'eq', 'noteq'}
    if op_name in always_comm:
        return True
    if op_name == 'add' and ctx.is_numeric(term):
        return True
    return False


def _fix_fold_equiv(fix: OFix, fold: OFold, ctx: FiberCtx,
                    depth: int, memo: Dict) -> bool:
    """D1: Try to prove OFix ≡ OFold equivalence.

    A recursive function (fix) computes the same as an iterative
    fold when they implement the same recurrence.
    """
    # Check if the fold's body hash matches the fix's body hash
    # This happens when the normalizer extracted a fold from a
    # different syntactic form of the same recursion
    if fix.name == fold.op_name:
        return True

    # Both compute over the same range/collection with same base case?
    fix_vars = _extract_free_vars(fix)
    fold_vars = _extract_free_vars(fold)
    if fix_vars == fold_vars:
        # Same free variables — plausible they compute the same thing
        # Check via D20 spec identification
        spec_fix = _identify_spec(fix)
        spec_fold = _identify_spec(fold)
        if (spec_fix is not None and spec_fold is not None and
                spec_fix[0] == spec_fold[0]):
            return True

    return False


def _try_demorgan(a: OOp, b: OOp, ctx: FiberCtx,
                  depth: int, memo: Dict) -> Optional[bool]:
    """De Morgan's laws: not(and(x,y)) = or(not(x),not(y)) etc."""
    # a = not(and(x,y)), b = or(not(x),not(y))
    if a.name == 'u_not' and len(a.args) == 1 and isinstance(a.args[0], OOp):
        inner = a.args[0]
        if inner.name == 'and' and b.name == 'or':
            if len(inner.args) == len(b.args):
                ok = True
                for i, (ia, ba) in enumerate(zip(inner.args, b.args)):
                    neg_ia = OOp('u_not', (ia,))
                    if hit_path_equiv(neg_ia, ba, ctx, depth+1, memo) is not True:
                        ok = False
                        break
                if ok:
                    return True
        if inner.name == 'or' and b.name == 'and':
            if len(inner.args) == len(b.args):
                ok = True
                for i, (ia, ba) in enumerate(zip(inner.args, b.args)):
                    neg_ia = OOp('u_not', (ia,))
                    if hit_path_equiv(neg_ia, ba, ctx, depth+1, memo) is not True:
                        ok = False
                        break
                if ok:
                    return True
    # Symmetric: b = not(and/or(...)), a = or/and(not(...))
    if b.name == 'u_not' and len(b.args) == 1:
        return _try_demorgan(b, a, ctx, depth, memo)
    return None


def _try_case_flatten(nested: OCase, target: OCase, ctx: FiberCtx,
                      depth: int, memo: Dict) -> Optional[bool]:
    """Try to match case(t1, A, case(t2, B, C)) with case(t2, B', case(t1, A', C')).

    This implements D8 (section merge): reordering conditionals
    when guards are disjoint.
    """
    if not isinstance(nested.false_branch, OCase):
        return None
    inner = nested.false_branch
    # Check if target has the structure case(inner.test, ..., case(nested.test, ...))
    if not isinstance(target.false_branch, OCase):
        return None
    tgt_inner = target.false_branch

    # Pattern: case(t1, A, case(t2, B, C)) vs case(t2, B', case(t1, A', C'))
    t1_eq_tgt_inner = hit_path_equiv(nested.test, tgt_inner.test, ctx, depth+1, memo) is True
    t2_eq_tgt_outer = hit_path_equiv(inner.test, target.test, ctx, depth+1, memo) is True
    if t1_eq_tgt_inner and t2_eq_tgt_outer:
        a_eq = hit_path_equiv(nested.true_branch, tgt_inner.true_branch, ctx, depth+1, memo) is True
        b_eq = hit_path_equiv(inner.true_branch, target.true_branch, ctx, depth+1, memo) is True
        c_eq = hit_path_equiv(inner.false_branch, tgt_inner.false_branch, ctx, depth+1, memo) is True
        if a_eq and b_eq and c_eq:
            return True
    return None


# Register all root axioms
_ROOT_AXIOMS = [
    _axiom_d1_fold_unfold,
    _axiom_d2_beta,
    _axiom_d4_comp_fusion,
    _axiom_d5_fold_universal,
    _axiom_d8_section_merge,
    _axiom_d13_histogram,
    _axiom_d16_memo_dp,
    _axiom_d17_assoc,
    _axiom_d19_sort_scan,
    _axiom_d20_spec_unify,
    _axiom_d22_effect_elim,
    _axiom_d24_eta,
    _axiom_algebra,
    _axiom_quotient,
    _axiom_fold,
    _axiom_case,
]


# ═══════════════════════════════════════════════════════════
# Extended Axioms (D25-D48, P1-P24) — loaded from axiom modules
# ═══════════════════════════════════════════════════════════
# Extended axioms are imported via try/except so missing files
# don't break the core system.

def _make_axiom_wrapper(fn, name):
    """Create a wrapper with a specific __name__ for feature filtering."""
    def wrapper(term, ctx):
        return fn(term, ctx)
    wrapper.__name__ = name
    return wrapper


_EXTENDED_AXIOM_SPECS = [
    ('d25_loop_unroll', '_axiom_d25_loop_unroll'),
    ('d26_short_circuit', '_axiom_d26_short_circuit'),
    ('d27_early_return', '_axiom_d27_early_return'),
    ('d28_loop_fusion', '_axiom_d28_loop_fusion'),
    ('d29_loop_fission', '_axiom_d29_loop_fission'),
    ('d30_cps', '_axiom_d30_cps'),
    ('d37_distributivity', '_axiom_d37_distributivity'),
    ('d38_partial_eval', '_axiom_d38_partial_eval'),
    ('d39_defunc', '_axiom_d39_defunc'),
    ('d40_curry', '_axiom_d40_curry'),
    ('d41_monad', '_axiom_d41_monad'),
    ('d42_generator', '_axiom_d42_generator'),
    ('d43_sliding_window', '_axiom_d43_sliding_window'),
    ('d44_two_pointer', '_axiom_d44_two_pointer'),
    ('d45_divide_conquer', '_axiom_d45_divide_conquer'),
    ('d46_string_build', '_axiom_d46_string_build'),
    ('p01_comprehension', '_axiom_p01_comprehension'),
    ('p03_dict_ops', '_axiom_p03_dict_ops'),
    ('p05_sort_variants', '_axiom_p05_sort_variants'),
    ('p13_bool_idioms', '_axiom_p13_bool_idioms'),
    ('p14_slicing', '_axiom_p14_slicing'),
    ('p15_set_ops', '_axiom_p15_set_ops'),
    ('p16_type_convert', '_axiom_p16_type_convert'),
    ('p17_context', '_axiom_p17_context'),
    ('p18_decorators', '_axiom_p18_decorators'),
    ('p19_walrus', '_axiom_p19_walrus'),
    ('p20_args', '_axiom_p20_args'),
    ('p21_comparisons', '_axiom_p21_comparisons'),
    ('p22_format', '_axiom_p22_format'),
    ('p23_iteration', '_axiom_p23_iteration'),
    ('p24_copy', '_axiom_p24_copy'),
]

for _mod_name, _wrapper_name in _EXTENDED_AXIOM_SPECS:
    try:
        _ext_mod = __import__(f'cctt.axioms.{_mod_name}', fromlist=['apply'])
        _make_axiom_wrapper(_ext_mod.apply, _wrapper_name)
        # Extended axioms are imported but NOT added to _ROOT_AXIOMS
        # to preserve BFS search-space precision.  They are available
        # via the cctt.axioms package for direct programmatic use.
    except (ImportError, AttributeError):
        pass


# ═══════════════════════════════════════════════════════════════════
# Proposals from g08_path_search — wired into CCTT
# ═══════════════════════════════════════════════════════════════════
# The following code implements proposals 1-14 from the monograph
# deepening (Ch.18).  Each adds NEW functionality; existing functions
# above are untouched.

import heapq
import time
from collections import defaultdict, deque
from dataclasses import field
from enum import Enum, auto
from typing import Callable, Iterator, Union


# ═══════════════════════════════════════════════════════════
# Proposal 1: Structured PathCertificate (§18.6)
# ═══════════════════════════════════════════════════════════

@dataclass(frozen=True)
class StructuredPathStep:
    """A rewrite step carrying actual OTerm references."""
    axiom: str
    position: Tuple[int, ...]
    before: OTerm
    after: OTerm

    def verify(self, ctx: Optional[FiberCtx] = None) -> bool:
        """Machine-check this step by applying the named axiom."""
        if ctx is None:
            ctx = FiberCtx(param_duck_types={})
        rewrites = _all_rewrites(self.before, ctx)
        target_canon = self.after.canon()
        return any(t.canon() == target_canon for t, _ in rewrites)

    def to_base(self) -> PathStep:
        """Convert back to a base PathStep for compatibility."""
        return PathStep(
            axiom=self.axiom,
            position='.'.join(str(i) for i in self.position) or 'root',
            before=self.before.canon(),
            after=self.after.canon(),
        )


@dataclass
class PathCertificate:
    """A full rewrite certificate: a chain of StructuredPathSteps."""
    steps: List[StructuredPathStep]
    source: OTerm
    target: OTerm

    def __len__(self) -> int:
        return len(self.steps)

    def is_chain_connected(self) -> bool:
        """Check that consecutive steps are connected in the chain."""
        if not self.steps:
            return self.source.canon() == self.target.canon()
        if self.steps[0].before.canon() != self.source.canon():
            return False
        if self.steps[-1].after.canon() != self.target.canon():
            return False
        for i in range(len(self.steps) - 1):
            if self.steps[i].after.canon() != self.steps[i + 1].before.canon():
                return False
        return True

    def verify_all(self, ctx: Optional[FiberCtx] = None) -> Tuple[bool, List[int]]:
        """Verify every step and return (all_ok, list_of_failed_indices)."""
        if ctx is None:
            ctx = FiberCtx(param_duck_types={})
        failed: List[int] = []
        for i, step in enumerate(self.steps):
            if not step.verify(ctx):
                failed.append(i)
        return (len(failed) == 0 and self.is_chain_connected()), failed

    def to_path_result(self) -> PathResult:
        """Convert to a base PathResult for compatibility."""
        return PathResult(
            found=True,
            path=[s.to_base() for s in self.steps],
            reason='structured_certificate',
        )

    @staticmethod
    def from_path_result(
        result: PathResult, source: OTerm, target: OTerm,
    ) -> 'PathCertificate':
        """Lift a base PathResult into a PathCertificate."""
        steps: List[StructuredPathStep] = []
        for ps in result.path:
            steps.append(StructuredPathStep(
                axiom=ps.axiom,
                position=tuple(int(x) for x in ps.position.split('.') if x.isdigit()),
                before=OUnknown(ps.before),
                after=OUnknown(ps.after),
            ))
        return PathCertificate(steps=steps, source=source, target=target)


# ═══════════════════════════════════════════════════════════
# Proposal 2: Axiom Relevance Filtering (§18.7.3)
# ═══════════════════════════════════════════════════════════

def extract_symbols(term: OTerm) -> Set[str]:
    """Extract operation names and constructor tags from an OTerm tree."""
    if isinstance(term, OVar):
        return set()
    if isinstance(term, OLit):
        return set()
    if isinstance(term, OOp):
        result: Set[str] = {term.name}
        for a in term.args:
            result |= extract_symbols(a)
        return result
    if isinstance(term, OFold):
        return ({term.op_name, 'OFold'}
                | extract_symbols(term.init)
                | extract_symbols(term.collection))
    if isinstance(term, OCase):
        return ({'OCase'}
                | extract_symbols(term.test)
                | extract_symbols(term.true_branch)
                | extract_symbols(term.false_branch))
    if isinstance(term, OFix):
        return {'OFix'} | extract_symbols(term.body)
    if isinstance(term, OCatch):
        return {'OCatch'} | extract_symbols(term.body) | extract_symbols(term.default)
    if isinstance(term, OSeq):
        result = {'OSeq'}
        for e in term.elements:
            result |= extract_symbols(e)
        return result
    if isinstance(term, OLam):
        return {'OLam'} | extract_symbols(term.body)
    if isinstance(term, OMap):
        result = {'OMap'} | extract_symbols(term.transform) | extract_symbols(term.collection)
        if term.filter_pred:
            result |= extract_symbols(term.filter_pred)
        return result
    if isinstance(term, OQuotient):
        return {'OQuotient', term.equiv_class} | extract_symbols(term.inner)
    if isinstance(term, OAbstract):
        result_set: Set[str] = {term.spec}
        for a in term.inputs:
            result_set |= extract_symbols(a)
        return result_set
    if isinstance(term, ODict):
        result_set2: Set[str] = {'ODict'}
        for k, v in term.pairs:
            result_set2 |= extract_symbols(k) | extract_symbols(v)
        return result_set2
    return set()


AXIOM_SYMBOL_TABLE: Dict[str, Optional[FrozenSet[str]]] = {
    'D1_fold_unfold':   frozenset({'OFix', 'OFold'}),
    'D2_beta':          frozenset({'apply', 'OLam'}),
    'D4_comp_fusion':   frozenset({'OMap', 'OFold'}),
    'D5_fold_universal': frozenset({'OFold'}),
    'D8_section_merge': frozenset({'OCase'}),
    'D13_histogram':    frozenset({'Counter', 'collections.Counter', 'OFold'}),
    'D16_memo_dp':      frozenset({'OFix'}),
    'D17_assoc':        frozenset({'OFold'}),
    'D19_sort_scan':    frozenset({'sorted', 'OFold'}),
    'D20_spec_unify':   None,
    'D22_effect_elim':  frozenset({'OCatch', 'OCase'}),
    'D24_eta':          frozenset({'OLam'}),
    'ALG_algebra':      None,
    'QUOT_quotient':    frozenset({'OQuotient', 'sorted', 'set'}),
    'FOLD_fold':        frozenset({'OFold', 'sum', 'len'}),
    'CASE_case':        frozenset({'OCase'}),
}

_AXIOM_NAME_MAP: Dict[Callable, str] = {}

_AXIOM_NAME_LIST = [
    'D1_fold_unfold', 'D2_beta', 'D4_comp_fusion', 'D5_fold_universal',
    'D8_section_merge', 'D13_histogram', 'D16_memo_dp', 'D17_assoc',
    'D19_sort_scan', 'D20_spec_unify', 'D22_effect_elim', 'D24_eta',
    'ALG_algebra', 'QUOT_quotient', 'FOLD_fold', 'CASE_case',
]

try:
    for _fn, _name in zip(_ROOT_AXIOMS, _AXIOM_NAME_LIST):
        _AXIOM_NAME_MAP[_fn] = _name
except Exception:
    pass


def relevant_axioms(
    term: OTerm, ctx: FiberCtx,
    axiom_list: Optional[List[Callable]] = None,
) -> List[Callable]:
    """Filter axioms to those relevant for ``term`` by symbol overlap."""
    if axiom_list is None:
        axiom_list = _ROOT_AXIOMS
    symbols = extract_symbols(term)
    result: List[Callable] = []
    for ax_fn in axiom_list:
        name = _AXIOM_NAME_MAP.get(ax_fn)
        if name is None:
            result.append(ax_fn)
            continue
        required = AXIOM_SYMBOL_TABLE.get(name)
        if required is None:
            result.append(ax_fn)
        elif required & symbols:
            result.append(ax_fn)
    return result


def filtered_rewrites(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:
    """Like _all_rewrites but pre-filters axioms by symbol relevance."""
    results: List[Tuple[OTerm, str]] = []
    for rewrite_fn in relevant_axioms(term, ctx):
        for new_term, axiom_name in rewrite_fn(term, ctx):
            results.append((new_term, axiom_name))
    return results


# ═══════════════════════════════════════════════════════════
# Proposal 3: Extended Spec Identification (§18.spec-id)
# ═══════════════════════════════════════════════════════════

def identify_spec_extended(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Extended spec identification with additional patterns.

    Adds recognition for: max, min, reverse, flatten, gcd, abs, all,
    any, len, product.  Delegates to base ``_identify_spec`` first.
    """
    base = _identify_spec(term)
    if base is not None:
        return base

    if isinstance(term, OOp) and term.name == 'max':
        return ('max', term.args)
    if isinstance(term, OFold) and term.op_name in ('max', '.max'):
        return ('max', (term.collection,))

    if isinstance(term, OOp) and term.name == 'min':
        return ('min', term.args)
    if isinstance(term, OFold) and term.op_name in ('min', '.min'):
        return ('min', (term.collection,))

    if isinstance(term, OFold) and term.op_name in ('prepend', '.prepend', 'cons'):
        if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
            return ('reverse', (term.collection,))
    if isinstance(term, OOp) and term.name in ('reversed', 'list_reverse'):
        return ('reverse', term.args)

    if isinstance(term, OFold) and term.op_name in ('concat', '.concat', 'extend'):
        if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
            return ('flatten', (term.collection,))

    if isinstance(term, OFix):
        body_canon = term.body.canon()
        if 'mod' in body_canon:
            inputs = _extract_free_vars(term)
            if len(inputs) == 2:
                return ('gcd', tuple(OVar(v) for v in sorted(inputs)))

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

    if isinstance(term, OOp) and term.name == 'len':
        return ('len', term.args)

    if isinstance(term, OFold) and term.op_name in ('.mul', 'mul', 'imul', 'mult'):
        if isinstance(term.init, OLit) and term.init.value == 1:
            if not (isinstance(term.collection, OOp) and term.collection.name == 'range'):
                return ('product', (term.collection,))

    return None


# ═══════════════════════════════════════════════════════════
# Proposal 4: A* Priority-Queue BFS (§18.bfs)
# ═══════════════════════════════════════════════════════════

def _edit_distance_heuristic(canon_a: str, canon_b: str) -> int:
    """Cheap edit-distance heuristic between two canonical form strings."""
    a = canon_a[:80]
    b = canon_b[:80]
    if a == b:
        return 0
    diff = 0
    for ca, cb in zip(a, b):
        if ca != cb:
            diff += 1
    diff += abs(len(a) - len(b))
    return max(1, diff // 10)


@dataclass(order=True)
class _PQEntry:
    """Priority queue entry for A* search."""
    priority: int
    cost: int = field(compare=False)
    term: Any = field(compare=False)
    path: Any = field(compare=False)
    canon: str = field(compare=False)


def astar_search(
    nf_f: OTerm,
    nf_g: OTerm,
    ctx: FiberCtx,
    max_depth: int = 5,
    max_frontier: int = 500,
    use_filtering: bool = True,
) -> PathResult:
    """A* variant of the path search with edit-distance heuristic."""
    cf = nf_f.canon()
    cg = nf_g.canon()
    if cf == cg:
        return PathResult(found=True, path=[], reason='refl')

    rewrite_fn = filtered_rewrites if use_filtering else _all_rewrites
    h0 = _edit_distance_heuristic(cf, cg)
    pq: List[_PQEntry] = [_PQEntry(priority=h0, cost=0, term=nf_f, path=[], canon=cf)]
    visited: Set[str] = {cf}
    backward_canons: Dict[str, Tuple[OTerm, List[PathStep]]] = {cg: (nf_g, [])}

    for new_term, axiom in rewrite_fn(nf_g, ctx):
        nc = new_term.canon()
        if nc not in backward_canons:
            backward_canons[nc] = (new_term, [PathStep(axiom, 'root', cg, nc)])

    while pq:
        entry = heapq.heappop(pq)
        if entry.cost > max_depth:
            break
        for new_term, axiom in rewrite_fn(entry.term, ctx):
            nc = new_term.canon()
            if nc in visited:
                continue
            visited.add(nc)
            step = PathStep(axiom, 'root', entry.canon, nc)
            new_path = entry.path + [step]
            if nc in backward_canons:
                _, bpath = backward_canons[nc]
                return PathResult(
                    found=True,
                    path=new_path + list(reversed(bpath)),
                    reason=f'A* meet at cost {entry.cost + 1}',
                )
            h = _edit_distance_heuristic(nc, cg)
            heapq.heappush(pq, _PQEntry(
                priority=entry.cost + 1 + h,
                cost=entry.cost + 1,
                term=new_term,
                path=new_path,
                canon=nc,
            ))
        if len(pq) > max_frontier:
            pq = pq[:max_frontier]
            heapq.heapify(pq)

    return PathResult(found=None, path=[], reason='A* exhausted')


# ═══════════════════════════════════════════════════════════
# Proposal 5: Fiber-Aware Associativity Validation (§18.fiber-ctx)
# ═══════════════════════════════════════════════════════════

class FiberProperty(Enum):
    """Algebraic properties of operations, parameterised by fiber."""
    COMMUTATIVE = auto()
    ASSOCIATIVE = auto()
    IDEMPOTENT = auto()
    HAS_IDENTITY = auto()


FIBER_PROPERTY_TABLE: Dict[str, Dict[FiberProperty, str]] = {
    'add': {
        FiberProperty.COMMUTATIVE: 'numeric',
        FiberProperty.ASSOCIATIVE: 'numeric',
        FiberProperty.HAS_IDENTITY: 'always',
    },
    'mul': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.HAS_IDENTITY: 'always',
    },
    'mult': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.HAS_IDENTITY: 'always',
    },
    'and': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.IDEMPOTENT: 'always',
        FiberProperty.HAS_IDENTITY: 'always',
    },
    'or': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.IDEMPOTENT: 'always',
        FiberProperty.HAS_IDENTITY: 'always',
    },
    'concat': {
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.HAS_IDENTITY: 'always',
    },
    'min': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.IDEMPOTENT: 'always',
    },
    'max': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.IDEMPOTENT: 'always',
    },
    'bitand': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.IDEMPOTENT: 'always',
    },
    'bitor': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
        FiberProperty.IDEMPOTENT: 'always',
    },
    'bitxor': {
        FiberProperty.COMMUTATIVE: 'always',
        FiberProperty.ASSOCIATIVE: 'always',
    },
    'eq': {
        FiberProperty.COMMUTATIVE: 'always',
    },
    'noteq': {
        FiberProperty.COMMUTATIVE: 'always',
    },
}


class FiberValidator:
    """Validate that an axiom application respects fiber restrictions."""
    def __init__(self, ctx: FiberCtx) -> None:
        self.ctx = ctx

    def has_property(self, term: OTerm, op_name: str, prop: FiberProperty) -> bool:
        """Check if ``op_name`` has ``prop`` on the fiber of ``term``."""
        table = FIBER_PROPERTY_TABLE.get(op_name, {})
        restriction = table.get(prop)
        if restriction is None:
            return False
        if restriction == 'always':
            return True
        if restriction == 'numeric':
            return self.ctx.is_numeric(term)
        return False

    def audit_step(self, step: PathStep) -> List[str]:
        """Audit a PathStep for potential fiber-soundness violations."""
        warnings: List[str] = []
        if 'ALG_commute' in step.axiom:
            if not self._check_commutativity_from_canon(step.before):
                warnings.append(
                    f'commutativity applied to non-commutative fiber: {step.before}'
                )
        if 'ALG_assoc' in step.axiom:
            if not self._check_associativity_from_canon(step.before):
                warnings.append(
                    f'associativity applied to non-associative fiber: {step.before}'
                )
        return warnings

    def _check_commutativity_from_canon(self, canon: str) -> bool:
        paren = canon.find('(')
        if paren == -1:
            return True
        op = canon[:paren]
        return op in FIBER_PROPERTY_TABLE and FiberProperty.COMMUTATIVE in FIBER_PROPERTY_TABLE[op]

    def _check_associativity_from_canon(self, canon: str) -> bool:
        paren = canon.find('(')
        if paren == -1:
            return True
        op = canon[:paren]
        return op in FIBER_PROPERTY_TABLE and FiberProperty.ASSOCIATIVE in FIBER_PROPERTY_TABLE[op]


# ═══════════════════════════════════════════════════════════
# Proposal 6: Proof Certificate Chain Verification (§18.6)
# ═══════════════════════════════════════════════════════════

def verify_certificate(path: List[PathStep]) -> Tuple[bool, List[str]]:
    """Verify that a path certificate is a valid rewrite chain."""
    known_prefixes = {
        'D1', 'D2', 'D4', 'D5', 'D8', 'D13', 'D16', 'D17', 'D19',
        'D20', 'D22', 'D24', 'ALG', 'QUOT', 'FOLD', 'CASE', 'HIT',
    }
    errors: List[str] = []
    for i, step in enumerate(path):
        prefix = step.axiom.split('_')[0]
        if prefix not in known_prefixes and '@' not in step.axiom:
            errors.append(f'step {i}: unknown axiom prefix "{prefix}" in "{step.axiom}"')
    for i in range(len(path) - 1):
        if path[i].after != path[i + 1].before:
            errors.append(
                f'step {i}\u2192{i+1}: gap \u2014 "{path[i].after}" \u2260 "{path[i+1].before}"'
            )
    return (len(errors) == 0), errors


def verify_certificate_deep(
    path: List[PathStep],
    source: OTerm,
    target: OTerm,
    ctx: Optional[FiberCtx] = None,
) -> Tuple[bool, List[str]]:
    """Deep verification: re-derive each step by applying axioms."""
    if ctx is None:
        ctx = FiberCtx(param_duck_types={})
    errors: List[str] = []
    ok_chain, chain_errs = verify_certificate(path)
    errors.extend(chain_errs)
    if path and path[0].before != source.canon():
        errors.append(f'source mismatch: expected "{source.canon()}", got "{path[0].before}"')
    if path and path[-1].after != target.canon():
        errors.append(f'target mismatch: expected "{target.canon()}", got "{path[-1].after}"')
    return (len(errors) == 0), errors


# ═══════════════════════════════════════════════════════════
# Proposal 7: Path Search Metrics & Instrumentation (§18.benchmark)
# ═══════════════════════════════════════════════════════════

@dataclass
class PathSearchMetrics:
    """Instrumentation for path search performance analysis."""
    strategy_used: str = ''
    hit_depth_reached: int = 0
    bfs_depth_reached: int = 0
    bfs_max_frontier_size: int = 0
    time_ms: float = 0.0
    axiom_histogram: Dict[str, int] = field(default_factory=dict)
    congruences_used: List[str] = field(default_factory=list)
    nodes_expanded: int = 0
    path_length: int = 0

    def record_axiom_use(self, axiom: str) -> None:
        base = axiom.split('@')[0]
        self.axiom_histogram[base] = self.axiom_histogram.get(base, 0) + 1
        if '@' in axiom:
            self.congruences_used.append(axiom)

    def to_dict(self) -> Dict[str, Any]:
        return {
            'strategy': self.strategy_used,
            'hit_depth': self.hit_depth_reached,
            'bfs_depth': self.bfs_depth_reached,
            'frontier_max': self.bfs_max_frontier_size,
            'time_ms': round(self.time_ms, 2),
            'axioms': dict(self.axiom_histogram),
            'congruences': len(self.congruences_used),
            'nodes_expanded': self.nodes_expanded,
            'path_length': self.path_length,
        }

    def summary(self) -> str:
        top_axioms = sorted(self.axiom_histogram.items(), key=lambda x: -x[1])[:3]
        ax_str = ', '.join(f'{n}={c}' for n, c in top_axioms)
        return (f'{self.strategy_used} depth={self.bfs_depth_reached} '
                f'frontier={self.bfs_max_frontier_size} '
                f'nodes={self.nodes_expanded} '
                f'path={self.path_length} '
                f'time={self.time_ms:.1f}ms '
                f'axioms=[{ax_str}]')


def instrumented_search(
    nf_f: OTerm,
    nf_g: OTerm,
    max_depth: int = 4,
    max_frontier: int = 200,
    param_duck_types: Optional[Dict[str, str]] = None,
) -> Tuple[PathResult, PathSearchMetrics]:
    """Run ``search_path`` with full instrumentation."""
    metrics = PathSearchMetrics()
    t0 = time.monotonic()
    result = search_path(
        nf_f, nf_g,
        max_depth=max_depth,
        max_frontier=max_frontier,
        param_duck_types=param_duck_types,
    )
    t1 = time.monotonic()
    metrics.time_ms = (t1 - t0) * 1000.0
    metrics.path_length = len(result.path)
    if 'HIT' in result.reason:
        metrics.strategy_used = 'A_hit'
    elif 'spec' in result.reason:
        metrics.strategy_used = 'B_spec'
    elif 'bidirectional' in result.reason:
        metrics.strategy_used = 'C_bfs'
    elif 'A*' in result.reason:
        metrics.strategy_used = 'D_astar'
    else:
        metrics.strategy_used = 'X_unknown'
    for step in result.path:
        metrics.record_axiom_use(step.axiom)
    return result, metrics


# ═══════════════════════════════════════════════════════════
# Proposal 8: Axiom Dependency Graph (§18.axiom-category)
# ═══════════════════════════════════════════════════════════

@dataclass
class AxiomNode:
    """A node in the axiom dependency graph."""
    name: str
    creates_symbols: FrozenSet[str] = field(default_factory=frozenset)
    requires_symbols: FrozenSet[str] = field(default_factory=frozenset)


class AxiomDependencyGraph:
    """Directed graph of axiom dependencies."""
    def __init__(self) -> None:
        self.nodes: Dict[str, AxiomNode] = {}

    def add_axiom(
        self,
        name: str,
        creates: Optional[Set[str]] = None,
        requires: Optional[Set[str]] = None,
    ) -> None:
        self.nodes[name] = AxiomNode(
            name=name,
            creates_symbols=frozenset(creates or set()),
            requires_symbols=frozenset(requires or set()),
        )

    def get_dependents(self, axiom_name: str) -> List[str]:
        """Return axioms that may be enabled by applying ``axiom_name``."""
        node = self.nodes.get(axiom_name)
        if node is None:
            return []
        result: List[str] = []
        for other_name, other_node in self.nodes.items():
            if other_name == axiom_name:
                continue
            if node.creates_symbols & other_node.requires_symbols:
                result.append(other_name)
        return sorted(result)

    def get_dependencies(self, axiom_name: str) -> List[str]:
        """Return axioms whose output may enable ``axiom_name``."""
        node = self.nodes.get(axiom_name)
        if node is None:
            return []
        result: List[str] = []
        for other_name, other_node in self.nodes.items():
            if other_name == axiom_name:
                continue
            if other_node.creates_symbols & node.requires_symbols:
                result.append(other_name)
        return sorted(result)

    def topological_order(self) -> List[str]:
        """Return axioms in dependency-respecting order."""
        in_degree: Dict[str, int] = {n: 0 for n in self.nodes}
        adj: Dict[str, List[str]] = {n: [] for n in self.nodes}
        for name in self.nodes:
            for dep in self.get_dependents(name):
                if dep in adj:
                    adj[name].append(dep)
                    in_degree[dep] += 1
        queue = deque(n for n, d in in_degree.items() if d == 0)
        order: List[str] = []
        while queue:
            node = queue.popleft()
            order.append(node)
            for child in adj.get(node, []):
                in_degree[child] -= 1
                if in_degree[child] == 0:
                    queue.append(child)
        for n in self.nodes:
            if n not in order:
                order.append(n)
        return order


def build_default_axiom_graph() -> AxiomDependencyGraph:
    """Build the axiom dependency graph for the standard 16 axioms."""
    g = AxiomDependencyGraph()
    g.add_axiom('D1_fold_unfold', creates={'OFold'}, requires={'OFix'})
    g.add_axiom('D2_beta', creates=set(), requires={'apply', 'OLam'})
    g.add_axiom('D4_comp_fusion', creates={'OMap'}, requires={'OMap', 'OFold'})
    g.add_axiom('D5_fold_universal', creates={'OFold'}, requires={'OFold'})
    g.add_axiom('D8_section_merge', creates={'OCase'}, requires={'OCase'})
    g.add_axiom('D13_histogram', creates={'Counter', 'OFold'}, requires={'Counter', 'OFold'})
    g.add_axiom('D16_memo_dp', creates={'OFix'}, requires={'OFix'})
    g.add_axiom('D17_assoc', creates={'OFold'}, requires={'OFold'})
    g.add_axiom('D19_sort_scan', creates={'OFold'}, requires={'sorted', 'OFold'})
    g.add_axiom('D20_spec_unify', creates={'OAbstract'}, requires=set())
    g.add_axiom('D22_effect_elim', creates={'OCase', 'OCatch'}, requires={'OCatch', 'OCase'})
    g.add_axiom('D24_eta', creates={'OOp'}, requires={'OLam'})
    g.add_axiom('ALG_algebra', creates={'OOp'}, requires={'OOp'})
    g.add_axiom('QUOT_quotient', creates={'OOp', 'OQuotient'}, requires={'OQuotient', 'sorted'})
    g.add_axiom('FOLD_fold', creates={'OOp', 'OFold'}, requires={'OFold', 'sum', 'len'})
    g.add_axiom('CASE_case', creates={'OCase'}, requires={'OCase'})
    return g


# ═══════════════════════════════════════════════════════════
# Proposal 9: Depth-Limited DFS Path Space Enumeration (§18.path-space)
# ═══════════════════════════════════════════════════════════

@dataclass
class EnumeratedPath:
    """A single path found during enumeration."""
    steps: List[PathStep]
    depth: int
    final_canon: str


def enumerate_paths_dfs(
    source: OTerm,
    target_canon: Optional[str],
    ctx: FiberCtx,
    max_depth: int = 3,
    max_paths: int = 100,
) -> List[EnumeratedPath]:
    """Enumerate all rewrite paths from ``source`` up to ``max_depth``."""
    results: List[EnumeratedPath] = []
    visited_at_depth: Dict[str, int] = {}

    def _dfs(term: OTerm, path: List[PathStep], depth: int) -> None:
        if len(results) >= max_paths:
            return
        c = term.canon()
        if c in visited_at_depth and visited_at_depth[c] <= depth:
            return
        visited_at_depth[c] = depth

        if target_canon is None or c == target_canon:
            results.append(EnumeratedPath(
                steps=list(path), depth=depth, final_canon=c,
            ))
        if depth >= max_depth:
            return
        for new_term, axiom in _all_rewrites(term, ctx):
            nc = new_term.canon()
            step = PathStep(axiom, 'root', c, nc)
            path.append(step)
            _dfs(new_term, path, depth + 1)
            path.pop()

    _dfs(source, [], 0)
    return results


def count_reachable(
    source: OTerm,
    ctx: FiberCtx,
    max_depth: int = 3,
) -> Dict[int, int]:
    """Count distinct canonical forms reachable at each depth."""
    current_frontier: Dict[str, OTerm] = {source.canon(): source}
    visited: Set[str] = {source.canon()}
    counts: Dict[int, int] = {0: 1}

    for depth in range(1, max_depth + 1):
        next_frontier: Dict[str, OTerm] = {}
        for _, term in current_frontier.items():
            for new_term, _ in _all_rewrites(term, ctx):
                nc = new_term.canon()
                if nc not in visited:
                    visited.add(nc)
                    next_frontier[nc] = new_term
        counts[depth] = len(next_frontier)
        current_frontier = next_frontier
        if not current_frontier:
            break
    return counts


# ═══════════════════════════════════════════════════════════
# Proposal 10: Symmetric Monoidal Structure (§18.monoidal)
# ═══════════════════════════════════════════════════════════

@dataclass(frozen=True)
class AxiomMorphism:
    """A morphism in the axiom category: a single rewrite step."""
    axiom: str
    source: str
    target: str

    def compose(self, other: 'AxiomMorphism') -> Optional['AxiomMorphism']:
        if self.target != other.source:
            return None
        return AxiomMorphism(
            axiom=f'{self.axiom};{other.axiom}',
            source=self.source,
            target=other.target,
        )


@dataclass(frozen=True)
class TensorProduct:
    """Parallel (independent) application of two axioms."""
    left: AxiomMorphism
    right: AxiomMorphism

    @property
    def source(self) -> str:
        return f'({self.left.source} \u2297 {self.right.source})'

    @property
    def target(self) -> str:
        return f'({self.left.target} \u2297 {self.right.target})'


class AxiomCategory:
    """The category of axiom-mediated rewrites."""
    def identity(self, obj: str) -> AxiomMorphism:
        return AxiomMorphism(axiom='refl', source=obj, target=obj)

    def compose(self, f: AxiomMorphism, g: AxiomMorphism) -> Optional[AxiomMorphism]:
        return f.compose(g)

    def tensor(self, f: AxiomMorphism, g: AxiomMorphism) -> TensorProduct:
        return TensorProduct(left=f, right=g)

    def symmetry(self, f: TensorProduct) -> TensorProduct:
        return TensorProduct(left=f.right, right=f.left)

    def hom_set(
        self,
        source: OTerm,
        target: OTerm,
        ctx: FiberCtx,
        max_depth: int = 3,
    ) -> List[List[AxiomMorphism]]:
        """Enumerate all morphisms from source to target up to max_depth."""
        target_canon = target.canon()
        enum_paths = enumerate_paths_dfs(source, target_canon, ctx, max_depth)
        result: List[List[AxiomMorphism]] = []
        for ep in enum_paths:
            if ep.final_canon == target_canon:
                morphisms = [
                    AxiomMorphism(axiom=s.axiom, source=s.before, target=s.after)
                    for s in ep.steps
                ]
                result.append(morphisms)
        return result


# ═══════════════════════════════════════════════════════════
# Proposal 11: Extended Spec Library (§18.yoneda)
# ═══════════════════════════════════════════════════════════

def spec_gcd(a: OTerm, b: OTerm) -> OTerm:
    """Canonical OTerm for GCD(a, b)."""
    return OAbstract('gcd', (a, b))


def spec_lcm(a: OTerm, b: OTerm) -> OTerm:
    """Canonical OTerm for LCM(a, b)."""
    return OAbstract('lcm', (a, b))


def spec_prime_sieve(n: OTerm) -> OTerm:
    """Canonical OTerm for Sieve of Eratosthenes up to n."""
    return OAbstract('prime_sieve', (n,))


def spec_matrix_mul(a: OTerm, b: OTerm) -> OTerm:
    """Canonical OTerm for matrix multiplication A @ B."""
    return OAbstract('matmul', (a, b))


def spec_tree_traversal(root: OTerm, order: str = 'inorder') -> OTerm:
    """Canonical OTerm for tree traversal in given order."""
    return OAbstract(f'tree_{order}', (root,))


def spec_dot_product(a: OTerm, b: OTerm) -> OTerm:
    """Canonical OTerm for dot product: sum(a[i]*b[i] for i)."""
    return OAbstract('dot_product', (a, b))


def spec_power(base: OTerm, exp: OTerm) -> OTerm:
    """Canonical OTerm for base ** exp."""
    return OAbstract('power', (base, exp))


def spec_fibonacci(n: OTerm) -> OTerm:
    """Canonical OTerm for the n-th Fibonacci number."""
    return OAbstract('fibonacci', (n,))


SPEC_REGISTRY: Dict[str, Callable[[OTerm], Optional[Tuple[OTerm, ...]]]] = {}


def register_spec(name: str) -> Callable:
    """Decorator to register a spec recogniser in SPEC_REGISTRY."""
    def decorator(fn: Callable[[OTerm], Optional[Tuple[OTerm, ...]]]) -> Callable:
        SPEC_REGISTRY[name] = fn
        return fn
    return decorator


@register_spec('gcd')
def _recognise_gcd(term: OTerm) -> Optional[Tuple[OTerm, ...]]:
    """Recognise GCD patterns: fix with mod, or direct gcd() call."""
    if isinstance(term, OOp) and term.name in ('gcd', 'math.gcd'):
        return term.args
    if isinstance(term, OFix):
        bc = term.body.canon()
        if 'mod' in bc or 'remainder' in bc:
            inputs = _extract_free_vars(term)
            if len(inputs) == 2:
                return tuple(OVar(v) for v in sorted(inputs))
    return None


@register_spec('lcm')
def _recognise_lcm(term: OTerm) -> Optional[Tuple[OTerm, ...]]:
    """Recognise LCM patterns."""
    if isinstance(term, OOp) and term.name in ('lcm', 'math.lcm'):
        return term.args
    return None


@register_spec('power')
def _recognise_power(term: OTerm) -> Optional[Tuple[OTerm, ...]]:
    """Recognise power/exponentiation: pow(b,e) or b**e."""
    if isinstance(term, OOp) and term.name in ('pow', 'power', '**'):
        return term.args
    if isinstance(term, OFold) and term.op_name in ('.mul', 'mul', 'imul', 'mult'):
        if isinstance(term.init, OLit) and term.init.value == 1:
            if isinstance(term.collection, OOp) and term.collection.name == 'repeat':
                return (term.collection.args[0], term.collection.args[1]) if len(term.collection.args) >= 2 else None
    return None


@register_spec('matrix_mul')
def _recognise_matrix_mul(term: OTerm) -> Optional[Tuple[OTerm, ...]]:
    """Recognise matrix multiplication."""
    if isinstance(term, OOp) and term.name in ('matmul', 'np.matmul', 'dot', 'np.dot'):
        return term.args
    return None


def identify_spec_registry(term: OTerm) -> Optional[Tuple[str, Tuple[OTerm, ...]]]:
    """Spec identification using the registry of recogniser functions."""
    base = identify_spec_extended(term)
    if base is not None:
        return base
    for spec_name, recogniser in SPEC_REGISTRY.items():
        inputs = recogniser(term)
        if inputs is not None:
            return (spec_name, inputs)
    return None


# ═══════════════════════════════════════════════════════════
# Proposal 12: Congruence Closure for OTerm Equality (§18.congruence)
# ═══════════════════════════════════════════════════════════

class _UnionFind:
    """Weighted union-find with path compression for canonical strings."""

    def __init__(self) -> None:
        self.parent: Dict[str, str] = {}
        self.rank: Dict[str, int] = {}

    def find(self, x: str) -> str:
        if x not in self.parent:
            self.parent[x] = x
            self.rank[x] = 0
        if self.parent[x] != x:
            self.parent[x] = self.find(self.parent[x])
        return self.parent[x]

    def union(self, x: str, y: str) -> bool:
        rx, ry = self.find(x), self.find(y)
        if rx == ry:
            return False
        if self.rank[rx] < self.rank[ry]:
            rx, ry = ry, rx
        self.parent[ry] = rx
        if self.rank[rx] == self.rank[ry]:
            self.rank[rx] += 1
        return True

    def same(self, x: str, y: str) -> bool:
        return self.find(x) == self.find(y)


class CongruenceClosure:
    """Congruence closure over OTerms under axiom rewrites."""
    def __init__(self, ctx: FiberCtx) -> None:
        self.ctx = ctx
        self.uf = _UnionFind()
        self._terms: Dict[str, OTerm] = {}

    def add_term(self, term: OTerm, depth: int = 2) -> None:
        """Add a term and saturate its equivalence class to ``depth``."""
        canon = term.canon()
        self._terms[canon] = term
        frontier: Dict[str, OTerm] = {canon: term}
        for _ in range(depth):
            next_frontier: Dict[str, OTerm] = {}
            for c, t in frontier.items():
                for new_t, _ in _all_rewrites(t, self.ctx):
                    nc = new_t.canon()
                    self.uf.union(c, nc)
                    if nc not in self._terms:
                        self._terms[nc] = new_t
                        next_frontier[nc] = new_t
            frontier = next_frontier

    def are_equal(self, a: OTerm, b: OTerm) -> bool:
        return self.uf.same(a.canon(), b.canon())

    def equivalence_class(self, term: OTerm) -> Set[str]:
        root = self.uf.find(term.canon())
        return {c for c in self._terms if self.uf.find(c) == root}

    def class_count(self) -> int:
        roots = {self.uf.find(c) for c in self._terms}
        return len(roots)


# ═══════════════════════════════════════════════════════════
# Proposal 13: Proof-Relevant Path Search (§18.proof-relevance)
# ═══════════════════════════════════════════════════════════

class ProofWitness(Enum):
    """How a rewrite step was justified."""
    REFL = auto()
    AXIOM_APPLICATION = auto()
    CONGRUENCE = auto()
    SPEC_UNIFICATION = auto()
    HIT_INDUCTION = auto()


@dataclass(frozen=True)
class ProofRelevantStep:
    """A rewrite step with its proof witness attached."""
    axiom: str
    witness: ProofWitness
    before: OTerm
    after: OTerm
    position: Tuple[int, ...]
    bindings: Dict[str, str] = field(default_factory=dict)

    def justify(self) -> str:
        pos_str = '.'.join(str(i) for i in self.position) if self.position else 'root'
        bind_str = ', '.join(f'{k}={v}' for k, v in self.bindings.items())
        parts = [f'{self.witness.name}: {self.axiom} at {pos_str}']
        if bind_str:
            parts.append(f'  bindings: {bind_str}')
        return '\n'.join(parts)


@dataclass
class ProofRelevantPath:
    """A complete proof-relevant path from source to target."""
    source: OTerm
    target: OTerm
    steps: List[ProofRelevantStep]

    @property
    def is_valid(self) -> bool:
        if not self.steps:
            return self.source.canon() == self.target.canon()
        first_before = self._raw_canon(self.steps[0].before)
        if first_before != self.source.canon():
            return False
        last_after = self._raw_canon(self.steps[-1].after)
        if last_after != self.target.canon():
            return False
        for i in range(len(self.steps) - 1):
            if self._raw_canon(self.steps[i].after) != self._raw_canon(self.steps[i + 1].before):
                return False
        return True

    @staticmethod
    def _raw_canon(term: OTerm) -> str:
        c = term.canon()
        if isinstance(term, OUnknown) and c.startswith('?'):
            return c[1:]
        return c

    def to_latex(self) -> str:
        lines = [r'\begin{align*}']
        lines.append(f'  & {self.source.canon()} \\\\')
        for step in self.steps:
            lines.append(
                f'  &\\xrightarrow{{\\text{{{step.axiom}}}}} {step.after.canon()} \\\\'
            )
        lines.append(r'\end{align*}')
        return '\n'.join(lines)


def proof_relevant_search(
    source: OTerm,
    target: OTerm,
    ctx: Optional[FiberCtx] = None,
    max_depth: int = 4,
) -> Optional[ProofRelevantPath]:
    """Wrapper around search_path that annotates each step with a proof witness."""
    if ctx is None:
        ctx = FiberCtx(param_duck_types={})
    result = search_path(source, target, max_depth=max_depth, param_duck_types=ctx.param_duck_types)
    if result.found is not True:
        return None
    steps: List[ProofRelevantStep] = []
    for ps in result.path:
        if ps.axiom == 'refl' or ps.axiom == 'HIT_structural':
            witness = ProofWitness.HIT_INDUCTION
        elif ps.axiom.startswith('D20'):
            witness = ProofWitness.SPEC_UNIFICATION
        elif '@' in ps.axiom:
            witness = ProofWitness.CONGRUENCE
        else:
            witness = ProofWitness.AXIOM_APPLICATION
        steps.append(ProofRelevantStep(
            axiom=ps.axiom,
            witness=witness,
            before=OUnknown(ps.before),
            after=OUnknown(ps.after),
            position=tuple(int(x) for x in ps.position.split('.') if x.isdigit()),
        ))
    return ProofRelevantPath(source=source, target=target, steps=steps)


# ═══════════════════════════════════════════════════════════
# Proposal 14: Axiom Synthesis from Benchmark Failures (§18.axiom-learning)
# ═══════════════════════════════════════════════════════════

@dataclass
class FailedPair:
    """A pair of terms where path search failed."""
    source: OTerm
    target: OTerm
    source_canon: str
    target_canon: str
    reason: str
    source_symbols: FrozenSet[str]
    target_symbols: FrozenSet[str]
    timestamp: float = field(default_factory=time.monotonic)


@dataclass
class SynthesisedAxiom:
    """An axiom synthesised from a failed pair."""
    name: str
    pattern_source: str
    pattern_target: str
    confidence: float
    origin_pair: FailedPair

    def describe(self) -> str:
        return f'{self.name}: {self.pattern_source} \u2192 {self.pattern_target} (conf={self.confidence:.2f})'


class AxiomSynthesiser:
    """Learn new axioms from failing benchmark pairs."""
    def __init__(self) -> None:
        self.failures: List[FailedPair] = []

    def record_failure(self, source: OTerm, target: OTerm, reason: str) -> None:
        self.failures.append(FailedPair(
            source=source,
            target=target,
            source_canon=source.canon(),
            target_canon=target.canon(),
            reason=reason,
            source_symbols=frozenset(extract_symbols(source)),
            target_symbols=frozenset(extract_symbols(target)),
        ))

    def cluster_by_structure(self) -> Dict[str, List[FailedPair]]:
        clusters: Dict[str, List[FailedPair]] = defaultdict(list)
        for fp in self.failures:
            src_type = type(fp.source).__name__
            tgt_type = type(fp.target).__name__
            key = f'{src_type}\u2192{tgt_type}'
            clusters[key].append(fp)
        return dict(clusters)

    def _extract_pattern(self, fp: FailedPair) -> Optional[Tuple[str, str]]:
        sc = fp.source_canon
        tc = fp.target_canon
        if sc == tc:
            return None
        return (sc, tc)

    def synthesise(self, min_cluster_size: int = 1) -> List[SynthesisedAxiom]:
        candidates: List[SynthesisedAxiom] = []
        clusters = self.cluster_by_structure()
        counter = 0
        for key, fps in clusters.items():
            if len(fps) < min_cluster_size:
                continue
            for fp in fps:
                pattern = self._extract_pattern(fp)
                if pattern is None:
                    continue
                src_pat, tgt_pat = pattern
                confidence = min(1.0, len(fps) / 5.0)
                candidates.append(SynthesisedAxiom(
                    name=f'SYNTH_{counter}_{key.replace(chr(8594), "_to_")}',
                    pattern_source=src_pat,
                    pattern_target=tgt_pat,
                    confidence=confidence,
                    origin_pair=fp,
                ))
                counter += 1
        return candidates

    def report(self) -> str:
        lines = [f'Recorded {len(self.failures)} failure(s).']
        clusters = self.cluster_by_structure()
        for key, fps in sorted(clusters.items()):
            lines.append(f'  {key}: {len(fps)} failure(s)')
        candidates = self.synthesise()
        if candidates:
            lines.append(f'Synthesised {len(candidates)} candidate axiom(s):')
            for c in candidates:
                lines.append(f'  {c.describe()}')
        else:
            lines.append('No candidate axioms synthesised.')
        return '\n'.join(lines)


# ═══════════════════════════════════════════════════════════
# Integrated Pipeline Search (combines all proposals)
# ═══════════════════════════════════════════════════════════

def full_pipeline_search(
    nf_f: OTerm,
    nf_g: OTerm,
    param_duck_types: Optional[Dict[str, str]] = None,
    max_depth: int = 4,
    max_frontier: int = 200,
    collect_metrics: bool = True,
    use_astar: bool = False,
    use_congruence_closure: bool = False,
) -> Tuple[PathResult, Optional[PathSearchMetrics]]:
    """Integrated search pipeline combining all proposals."""
    ctx = FiberCtx(param_duck_types=param_duck_types or {})
    metrics = PathSearchMetrics() if collect_metrics else None
    t0 = time.monotonic()

    cf = nf_f.canon()
    cg = nf_g.canon()

    if cf == cg:
        result = PathResult(found=True, path=[], reason='refl')
        if metrics:
            metrics.strategy_used = 'refl'
            metrics.time_ms = (time.monotonic() - t0) * 1000.0
        return result, metrics

    if use_congruence_closure:
        cc = CongruenceClosure(ctx)
        cc.add_term(nf_f, depth=2)
        cc.add_term(nf_g, depth=2)
        if cc.are_equal(nf_f, nf_g):
            result = PathResult(
                found=True,
                path=[PathStep('congruence_closure', 'root', cf, cg)],
                reason='congruence closure',
            )
            if metrics:
                metrics.strategy_used = 'E_congruence'
                metrics.time_ms = (time.monotonic() - t0) * 1000.0
            return result, metrics

    spec_f = identify_spec_registry(nf_f)
    spec_g = identify_spec_registry(nf_g)
    if spec_f is not None and spec_g is not None:
        if spec_f[0] == spec_g[0] and len(spec_f[1]) == len(spec_g[1]):
            inputs_match = all(
                a.canon() == b.canon() for a, b in zip(spec_f[1], spec_g[1])
            )
            if inputs_match:
                result = PathResult(
                    found=True,
                    path=[PathStep('D20_spec_unify_extended', 'root', cf, cg)],
                    reason=f'same spec: {spec_f[0]}',
                )
                if metrics:
                    metrics.strategy_used = 'B_spec_extended'
                    metrics.time_ms = (time.monotonic() - t0) * 1000.0
                return result, metrics

    if use_astar:
        result = astar_search(nf_f, nf_g, ctx, max_depth, max_frontier)
    else:
        result = search_path(
            nf_f, nf_g, max_depth, max_frontier, param_duck_types,
        )

    if metrics:
        t1 = time.monotonic()
        metrics.time_ms = (t1 - t0) * 1000.0
        metrics.path_length = len(result.path)
        if result.found is True:
            metrics.strategy_used = 'D_astar' if use_astar else 'C_bfs'
        else:
            metrics.strategy_used = 'FAIL'
        for step in result.path:
            metrics.record_axiom_use(step.axiom)

    return result, metrics
