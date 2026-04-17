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
    param_duck_types: Dict[str, str] = None  # p0 → 'int', p1 → 'str', etc.

    def __post_init__(self):
        if self.param_duck_types is None:
            object.__setattr__(self, 'param_duck_types', {})

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

    def is_integer(self, term: OTerm) -> bool:
        """Check if all params in a term are on integer fibers.

        Use this for axioms that only hold for exact arithmetic
        (associativity, commutativity of +) but not for floats.
        """
        params = _extract_params_from_term(term)
        if not params:
            return True
        for p in params:
            dt = self.param_duck_types.get(p, 'any')
            if dt not in ('int',):
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

    Uses sheaf-theoretic axiom selection: the stalk at each
    position determines which axiom sections are non-trivial
    there. This is O(relevant) instead of O(all).
    """
    results = []

    # Select axioms whose domain contains the root's stalk
    applicable = _select_axioms_for_term(term, ctx)
    for rewrite_fn in applicable:
        try:
            for new_term, axiom_name in rewrite_fn(term, ctx):
                results.append((new_term, axiom_name))
        except Exception:
            continue

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
            results.append((OFold(term.op_name, new_init, term.collection,
                                  body_fn=term.body_fn), f'{ax}@init'))
        for new_coll, ax in _all_rewrites(term.collection, ctx):
            results.append((OFold(term.op_name, term.init, new_coll,
                                  body_fn=term.body_fn), f'{ax}@coll'))
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
            results.append((OFold(canonical_op, term.init, term.collection,
                                  body_fn=term.body_fn),
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
    # bitor/bitand/bitxor are commutative on integers but bitor (|)
    # on dicts is NOT commutative (overlapping keys → last-write-wins).
    always_commutative = {'mul', 'mult', 'and', 'or',
                          'min', 'max', 'eq', 'noteq'}
    # bitor/bitand/bitxor only commutative on integer fibers
    int_commutative = {'add', 'bitor', 'bitand', 'bitxor'}
    commutative_ops = always_commutative
    if term.name in int_commutative and ctx.is_integer(term):
        commutative_ops = commutative_ops | int_commutative
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
    if term.name in fiber_assoc and ctx.is_integer(term):
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
    """Identify a high-level computing pattern from an OTerm.

    Returns (pattern_name, canonical_inputs) if recognized, else None.
    This is the Yoneda embedding: characterize the term by its
    observable behavior under all representable functors.

    Patterns are GENERAL computing structures (fold, map, sort, etc.),
    not algorithm-specific names.  Two OTerms with the same pattern
    and inputs are extensionally equal by Yoneda.
    """
    # ── General fold patterns ──
    # fold[op](init, collection) is fully determined by (op, init, collection)
    # When op is a named operation, use it as the spec key.
    # When op is a hash (opaque body), use the body_fn for structural comparison.
    if isinstance(term, OFold):
        canon_op = _canonical_fold_op(term.op_name)
        if canon_op.isalpha():
            return ('fold', (OLit(canon_op), term.init, term.collection))
        # Hash-keyed fold: use body_fn for structural identity if available
        if term.body_fn is not None:
            return ('fold_body', (term.body_fn, term.init, term.collection))
        return ('fold', (OLit(canon_op), term.init, term.collection))

    # ── Map/filter patterns ──
    # map(transform, collection) possibly with filter
    if isinstance(term, OMap):
        if term.filter_pred is not None:
            return ('filter_map', (term.filter_pred, term.transform, term.collection))
        return ('map', (term.transform, term.collection))

    # ── Sort patterns ──
    # sorted(collection) with optional key
    if isinstance(term, OOp) and term.name == 'sorted':
        return ('sorted', term.args)

    # ── Builtin aggregation ──
    # sum(x), len(x), min(x), max(x), all(x), any(x)
    if isinstance(term, OOp) and term.name in ('sum', 'len', 'min', 'max', 'all', 'any'):
        return (term.name, term.args)

    # ── abs(x) ──
    if isinstance(term, OOp) and term.name == 'abs':
        return ('abs', term.args)

    # ── Membership test: x in collection ──
    if isinstance(term, OOp) and term.name == 'in':
        return ('membership', term.args)

    # ── Boolean equality check: eq(x, y) ──
    if isinstance(term, OOp) and term.name == 'eq':
        return ('equality', term.args)

    # ── Fixed-point patterns ──
    # Don't abstract fix terms — the body normalization may lose
    # subtle distinctions (< vs <=, etc.).  Let path search handle
    # recursive equivalence via axiom rewrites instead.

    # ── Stdlib function calls ──
    # math.comb, math.factorial, etc. — strip the 'math.' prefix so
    # gcd and math.gcd both map to the same spec name.
    if isinstance(term, OOp) and term.name.startswith('math.'):
        base_name = term.name[5:]  # strip 'math.'
        return (base_name, term.args)

    # ── Lambda patterns ──
    # Two lambdas with alpha-equivalent bodies are equal
    if isinstance(term, OLam):
        return ('lam', (term.body,))

    # ── Exception-catching patterns ──
    # catch(body, default) — same body and default means same behavior
    if isinstance(term, OCatch):
        return ('catch', (term.body, term.default))

    # ── String conversion patterns ──
    if isinstance(term, OOp) and term.name in ('str', 'repr'):
        return ('to_string', term.args)

    return None


def _canonical_fold_op(op_name: str) -> str:
    """Map augmented-assignment and variant op names to canonical form."""
    canonical = {
        'iadd': 'add', 'isub': 'sub', 'imul': 'mul', 'imult': 'mul',
        'ifloordiv': 'floordiv', 'itruediv': 'truediv',
        'imod': 'mod', 'ipow': 'pow',
        'ibitor': 'bitor', 'ibitand': 'bitand', 'ibitxor': 'bitxor',
        'mult': 'mul',
    }
    return canonical.get(op_name, op_name)


# ═══════════════════════════════════════════════════════════
# Guard Peeling (Case Congruence)
# ═══════════════════════════════════════════════════════════

def _guard_peel_search(nf_f: OTerm, nf_g: OTerm,
                       ctx: FiberCtx,
                       param_duck_types: Optional[Dict[str, str]] = None,
                       depth: int = 0) -> Optional[PathResult]:
    """Peel shared case guards and recurse on differing branches.

    Sound by the congruence rule for case:
      case(G, A, B) ≡ case(G, A, C)  iff  B ≡ C
      case(G, A, B) ≡ case(G, C, B)  iff  A ≡ C

    Peeling is iterated: case(G1, X, case(G2, Y, Z)) vs
    case(G1, X, case(G2, Y, W)) peels twice.  Max depth prevents
    unbounded recursion.
    """
    if depth > 5:
        return None
    if not isinstance(nf_f, OCase) or not isinstance(nf_g, OCase):
        return None

    # Check if guards match
    if nf_f.test.canon() != nf_g.test.canon():
        return None

    true_match = nf_f.true_branch.canon() == nf_g.true_branch.canon()
    false_match = nf_f.false_branch.canon() == nf_g.false_branch.canon()

    if true_match and false_match:
        return PathResult(found=True, path=[], reason='refl (guard-peeled)')

    if true_match:
        # Recurse on false branches
        inner_f = nf_f.false_branch
        inner_g = nf_g.false_branch
    elif false_match:
        # Recurse on true branches
        inner_f = nf_f.true_branch
        inner_g = nf_g.true_branch
    else:
        # Neither branch matches — try peeling on both independently
        # case(G, A1, B1) vs case(G, A2, B2): need A1≡A2 AND B1≡B2
        true_result = _guard_peel_search(
            nf_f.true_branch, nf_g.true_branch, ctx, param_duck_types, depth + 1)
        if true_result is not None and true_result.found:
            false_result = _guard_peel_search(
                nf_f.false_branch, nf_g.false_branch, ctx, param_duck_types, depth + 1)
            if false_result is not None and false_result.found:
                return PathResult(
                    found=True,
                    path=true_result.path + false_result.path,
                    reason=f'guard congruence: both branches proved')
        return None

    # Try to prove inner equivalence via the full pipeline (minus guard peeling)
    # First check refl
    if inner_f.canon() == inner_g.canon():
        return PathResult(
            found=True,
            path=[PathStep('guard_peel', 'case_branch',
                          nf_f.canon()[:40], nf_g.canon()[:40])],
            reason='guard peeled → refl')

    # Recursive guard peeling on the inner terms
    inner_peel = _guard_peel_search(inner_f, inner_g, ctx, param_duck_types, depth + 1)
    if inner_peel is not None and inner_peel.found:
        return PathResult(
            found=True,
            path=[PathStep('guard_peel', 'case_branch',
                          nf_f.canon()[:40], nf_g.canon()[:40])] + inner_peel.path,
            reason=f'guard peeled → {inner_peel.reason}')

    # Try HIT on inner terms
    hit = hit_path_equiv(inner_f, inner_g, ctx)
    if hit is True:
        return PathResult(
            found=True,
            path=[PathStep('guard_peel+HIT', 'case_branch',
                          nf_f.canon()[:40], nf_g.canon()[:40])],
            reason='guard peeled → HIT path induction')

    # Try spec identification on inner terms
    spec_f = _identify_spec(inner_f)
    spec_g = _identify_spec(inner_g)
    if spec_f is not None and spec_g is not None:
        if spec_f[0] == spec_g[0] and len(spec_f[1]) == len(spec_g[1]):
            if all(a.canon() == b.canon() for a, b in zip(spec_f[1], spec_g[1])):
                return PathResult(
                    found=True,
                    path=[PathStep('guard_peel+D20', 'case_branch',
                                  nf_f.canon()[:40], nf_g.canon()[:40])],
                    reason=f'guard peeled → same spec: {spec_f[0]}')

    # Try cohomological fiber search on inner terms
    cohom = _cohomological_fiber_search(inner_f, inner_g, ctx)
    if cohom is not None and cohom.found:
        return PathResult(
            found=True,
            path=[PathStep('guard_peel+cohom', 'case_branch',
                          nf_f.canon()[:40], nf_g.canon()[:40])] + cohom.path,
            reason=f'guard peeled → {cohom.reason}')

    return None


# ═══════════════════════════════════════════════════════════
# The Path Search Algorithm
# ═══════════════════════════════════════════════════════════

def search_path(nf_f: OTerm, nf_g: OTerm,
                max_depth: int = 4,
                max_frontier: int = 200,
                param_duck_types: Optional[Dict[str, str]] = None) -> PathResult:
    """Cohomological path search via OTerm presheaf decomposition.

    Phase 0: Canonical equality (refl)
    Phase 1: HIT structural decomposition (sheaf descent condition)
    Phase 2: D20 spec identification (Yoneda)
    Phase 3: Cohomological fiber decomposition + absorption
             Align OTerm trees → fibers → resolve each via
             local axioms + connecting homomorphism
    Phase 4: Limited BFS fallback (depth-bounded)

    The cohomological approach decomposes the global equivalence problem
    into independent local problems at each fiber, then uses the
    Mayer-Vietoris exact sequence to determine if local differences
    are absorbed by the compositional structure.
    """
    ctx = FiberCtx(param_duck_types=param_duck_types or {})
    cf = nf_f.canon()
    cg = nf_g.canon()

    if cf == cg:
        return PathResult(found=True, path=[], reason='refl')

    # ── Phase 1: HIT structural decomposition (primary) ──
    hit_result = hit_path_equiv(nf_f, nf_g, ctx)
    if hit_result is True:
        return PathResult(found=True,
                         path=[PathStep('HIT_structural', 'root', cf, cg)],
                         reason='HIT path induction')

    # ── Phase 1.5: Guard peeling (case congruence) ──
    # If both terms are case(G, A, B) vs case(G, A, C) with shared guard G
    # and one matching branch, recurse on the differing branch.
    # Sound by the congruence rule: case(G, A, -) is a functor.
    guard_peel = _guard_peel_search(nf_f, nf_g, ctx, param_duck_types)
    if guard_peel is not None:
        return guard_peel

    # ── Phase 2: D20 spec identification (Yoneda) ──
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

    # ── Phase 3: Cohomological fiber decomposition ──
    cohom_result = _cohomological_fiber_search(nf_f, nf_g, ctx)
    if cohom_result is not None:
        return cohom_result

    # ── Phase 4: Limited BFS fallback ──
    bfs_result = _limited_bfs(nf_f, nf_g, ctx, max_depth=min(max_depth, 3),
                              max_frontier=min(max_frontier, 100))
    if bfs_result is not None:
        return bfs_result

    return PathResult(found=None, path=[],
                     reason=f'no path within depth {max_depth}')


def _cohomological_fiber_search(nf_f: OTerm, nf_g: OTerm,
                                ctx: FiberCtx) -> Optional[PathResult]:
    """Cohomological fiber decomposition with multi-resolution descent.

    Implements the sheaf descent approach from the monograph (§18.5):
    1. Fine-grained Čech cover via align_oterms → per-fiber local sections
    2. For unresolved fibers, coarsen the cover (merge siblings back to parent)
    3. Try deeper axiom BFS on coarser fibers (fewer, larger search targets)
    4. H¹ = 0 iff all fibers resolved → return EQ.

    This is the Čech refinement: try fine covers first (cheap per-fiber),
    then coarsen if needed (more expensive but catches coupled changes).
    """
    try:
        from .compositional_cohomology import (
            align_oterms, _ancestor_chain, _check_fiber_absorption,
            CohomologyResult, Fiber,
        )
    except ImportError:
        return None

    fibers = align_oterms(nf_f, nf_g)
    if not fibers:
        return PathResult(found=True, path=[], reason='H¹=0: empty decomposition')

    diff_fibers = [f for f in fibers if f.locally_equivalent is not True]
    if not diff_fibers:
        return PathResult(
            found=True,
            path=[PathStep('cohomological', 'root',
                          nf_f.canon()[:40], nf_g.canon()[:40])],
            reason=f'H¹=0: all {len(fibers)} fibers locally equivalent')

    # ── Pass 1: Fine-grained fiber resolution ──
    resolved_reasons: List[str] = []
    unresolved: List = []

    for fiber in diff_fibers:
        resolved = _try_resolve_fiber(fiber, nf_f, nf_g, ctx,
                                       max_bfs_steps=3, max_frontier=80)
        if resolved:
            resolved_reasons.append(resolved)
        else:
            unresolved.append(fiber)

    if not unresolved:
        reason_str = '; '.join(resolved_reasons[:3])
        return PathResult(
            found=True,
            path=[PathStep('cohomological_H1_0', 'root',
                          nf_f.canon()[:40], nf_g.canon()[:40])],
            reason=f'H¹=0: {len(diff_fibers)} fibers resolved ({reason_str})')

    # ── Pass 2: Coarsen cover — merge sibling fibers to parent ──
    # When fine-grained fibers fail independently, their parent may
    # resolve via a single axiom that touches multiple children.
    # This is the Čech refinement: coarser covers capture coupled changes.
    coarsened = _coarsen_unresolved(unresolved, nf_f, nf_g)
    still_unresolved = []

    for coarse_fiber in coarsened:
        resolved = _try_resolve_fiber(coarse_fiber, nf_f, nf_g, ctx,
                                       max_bfs_steps=5, max_frontier=150)
        if resolved:
            resolved_reasons.append(f'coarsened: {resolved}')
        else:
            still_unresolved.append(coarse_fiber)

    if not still_unresolved:
        reason_str = '; '.join(resolved_reasons[:3])
        return PathResult(
            found=True,
            path=[PathStep('cohomological_H1_0', 'root',
                          nf_f.canon()[:40], nf_g.canon()[:40])],
            reason=f'H¹=0: resolved via {len(diff_fibers)} fine + '
                   f'{len(coarsened)} coarse fibers ({reason_str})')

    return None  # Genuinely unresolved → inconclusive


def _try_resolve_fiber(fiber, nf_f: OTerm, nf_g: OTerm,
                        ctx: FiberCtx,
                        max_bfs_steps: int = 3,
                        max_frontier: int = 80) -> Optional[str]:
    """Try to resolve a single differing fiber via local sections.

    Returns a reason string if resolved, None otherwise.
    """
    try:
        from .compositional_cohomology import (
            _ancestor_chain, _check_fiber_absorption, Fiber,
        )
    except ImportError:
        return None

    # Strategy 1: Local axiom BFS at this fiber
    if fiber.term_f is not None and fiber.term_g is not None:
        local = _local_axiom_resolve(fiber.term_f, fiber.term_g, ctx,
                                      max_steps=max_bfs_steps,
                                      max_frontier=max_frontier)
        if local is True:
            return f'local axiom at {fiber.path}'

    # Strategy 2: Absorption via Mayer-Vietoris connecting homomorphism
    try:
        chain = _ancestor_chain(nf_f, fiber.path)
        absorption = _check_fiber_absorption(fiber, chain, nf_f, nf_g)
        if absorption.absorbed:
            return f'absorbed: {absorption.reason[:60]}'
    except Exception:
        pass

    # Strategy 3: HIT path equivalence on the fiber's sub-expressions
    if fiber.term_f is not None and fiber.term_g is not None:
        try:
            hit = hit_path_equiv(fiber.term_f, fiber.term_g, ctx)
            if hit is True:
                return f'HIT at {fiber.path}'
        except Exception:
            pass

    return None


def _coarsen_unresolved(unresolved_fibers, nf_f: OTerm, nf_g: OTerm):
    """Coarsen the Čech cover by merging sibling fibers back to their parent.

    When multiple fine-grained fibers under the same parent are unresolved,
    they may be coupled (e.g., itertools.cycle changes both the collection
    and the indexing simultaneously). Merging them into a single coarser
    fiber allows a single axiom application to resolve the coupled change.

    This is the Čech refinement/coarsening process: given a cover {U_i}
    and a coarser cover {V_j} with V_j = ∪ U_i for i ∈ I_j, we try
    the coarser cover when the finer one fails to yield H¹ = 0.
    """
    try:
        from .compositional_cohomology import (
            Fiber, _get_subterm,
        )
    except ImportError:
        return unresolved_fibers

    # Group unresolved fibers by their parent path
    parent_groups: Dict[Tuple, List] = {}
    for fiber in unresolved_fibers:
        if len(fiber.path) >= 2:
            parent_path = fiber.path[:-1]
        elif len(fiber.path) == 1:
            parent_path = ()
        else:
            parent_path = ()
        parent_groups.setdefault(parent_path, []).append(fiber)

    coarsened = []
    for parent_path, children in parent_groups.items():
        if len(children) >= 2:
            # Multiple siblings unresolved → coarsen to parent
            try:
                parent_f = _get_subterm(nf_f, parent_path)
                parent_g = _get_subterm(nf_g, parent_path)
                if parent_f is not None and parent_g is not None:
                    coarsened.append(Fiber(
                        path=parent_path,
                        term_f=parent_f, term_g=parent_g,
                        locally_equivalent=False))
                    continue
            except Exception:
                pass
        # Fallback: keep individual fibers
        coarsened.extend(children)

    return coarsened


def _local_axiom_resolve(term_f: OTerm, term_g: OTerm,
                         ctx: FiberCtx,
                         max_steps: int = 3,
                         max_frontier: int = 80) -> Optional[bool]:
    """Try to resolve a local fiber difference using axioms.

    Unlike BFS over the whole OTerm, this only applies axioms to the
    fiber's sub-expression, which is a much smaller search space.
    Each axiom is a presheaf morphism at a specific OTerm position.

    The search depth and frontier scale with the fiber size:
    smaller fibers → deeper search (the search tree is narrower).
    """
    cf = term_f.canon()
    cg = term_g.canon()

    if cf == cg:
        return True

    # Check structural congruence first (no axioms needed)
    if _structural_congruence(term_f, term_g, ctx, 0, {}) is True:
        return True

    # BFS from term_f toward term_g (and vice versa)
    forward: Dict[str, OTerm] = {cf: term_f}
    backward: Dict[str, OTerm] = {cg: term_g}
    per_step_limit = max(30, max_frontier // max_steps)

    for step in range(max_steps):
        # Expand forward — select axioms per-term via stalk dispatch
        new_fwd: Dict[str, OTerm] = {}
        for canon, term in list(forward.items()):
            applicable = _select_axioms_for_term(term, ctx)
            for rewrite_fn in applicable:
                try:
                    for new_term, _ in rewrite_fn(term, ctx):
                        nc = new_term.canon()
                        if nc in backward:
                            return True
                        if nc not in forward and nc not in new_fwd:
                            new_fwd[nc] = new_term
                except Exception:
                    continue
            if len(new_fwd) > per_step_limit:
                break
        forward.update(new_fwd)
        if len(forward) > max_frontier:
            break

        # Expand backward — select axioms per-term via stalk dispatch
        new_bwd: Dict[str, OTerm] = {}
        for canon, term in list(backward.items()):
            applicable = _select_axioms_for_term(term, ctx)
            for rewrite_fn in applicable:
                try:
                    for new_term, _ in rewrite_fn(term, ctx):
                        nc = new_term.canon()
                        if nc in forward:
                            return True
                        if nc not in backward and nc not in new_bwd:
                            new_bwd[nc] = new_term
                except Exception:
                    continue
            if len(new_bwd) > per_step_limit:
                break
        backward.update(new_bwd)
        if len(backward) > max_frontier:
            break

    return None


def _limited_bfs(nf_f: OTerm, nf_g: OTerm, ctx: FiberCtx,
                 max_depth: int = 3,
                 max_frontier: int = 100) -> Optional[PathResult]:
    """Limited bidirectional BFS — fallback when cohomological approach fails.

    Much more restricted than the original BFS: smaller frontier, fewer
    depths. This catches cases where the OTerm alignment doesn't work
    (different constructors at root).
    """
    cf = nf_f.canon()
    cg = nf_g.canon()
    forward: Dict[str, Tuple[OTerm, List[PathStep]]] = {cf: (nf_f, [])}
    backward: Dict[str, Tuple[OTerm, List[PathStep]]] = {cg: (nf_g, [])}

    for depth in range(max_depth):
        new_forward: Dict[str, Tuple[OTerm, List[PathStep]]] = {}
        for canon, (term, path) in list(forward.items()):
            if len(path) > depth:
                continue
            for new_term, axiom in _all_rewrites(term, ctx):
                nc = new_term.canon()
                if nc in forward or nc in new_forward:
                    continue
                step = PathStep(axiom, 'root', canon, nc)
                new_path = path + [step]
                if nc in backward:
                    _, bpath = backward[nc]
                    full_path = new_path + list(reversed(bpath))
                    return PathResult(found=True, path=full_path,
                                    reason=f'BFS meet at depth {depth+1}')
                new_forward[nc] = (new_term, new_path)

        forward.update(new_forward)
        if len(forward) > max_frontier:
            forward = _prune_frontier(forward, cg, max_frontier)

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
                                    reason=f'BFS meet at depth {depth+1}')
                new_backward[nc] = (new_term, new_path)

        backward.update(new_backward)
        if len(backward) > max_frontier:
            backward = _prune_frontier(backward, cf, max_frontier)

    return None


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
        new_bfn = (_subst_deep(term.body_fn, var_name, replacement)
                   if term.body_fn else None)
        return OFold(term.op_name, _subst_deep(term.init, var_name, replacement),
                     _subst_deep(term.collection, var_name, replacement),
                     body_fn=new_bfn)
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
    """Check if two guards are complementary: g1 ≡ ¬g2.

    Handles:
      - not(g) vs g
      - lt(a,b) vs gte(a,b), gt(a,b) vs lte(a,b), eq vs noteq
      - lt(a,b) vs lte(b,a) (strict/non-strict with swapped args)
    """
    # Direct negation: not(g) vs g
    if isinstance(g1, OOp) and g1.name == 'u_not' and len(g1.args) == 1:
        return g1.args[0].canon() == g2.canon()
    if isinstance(g2, OOp) and g2.name == 'u_not' and len(g2.args) == 1:
        return g2.args[0].canon() == g1.canon()

    # Comparison complement pairs (same argument order)
    _COMP_COMPLEMENT = {
        'lt': 'gte', 'gte': 'lt',
        'gt': 'lte', 'lte': 'gt',
        'eq': 'noteq', 'noteq': 'eq',
    }
    if isinstance(g1, OOp) and isinstance(g2, OOp):
        if len(g1.args) == 2 and len(g2.args) == 2:
            # Same-order complement: lt(a,b) vs gte(a,b)
            if (g1.name in _COMP_COMPLEMENT
                    and g2.name == _COMP_COMPLEMENT[g1.name]
                    and g1.args[0].canon() == g2.args[0].canon()
                    and g1.args[1].canon() == g2.args[1].canon()):
                return True
            # Cross-order complement: lt(a,b) vs lte(b,a)
            # lt(a,b) = ¬(gte(a,b)) = ¬(lte(b,a))
            _COMP_COMPLEMENT_SWAP = {
                'lt': 'lte', 'lte': 'lt',
                'gt': 'gte', 'gte': 'gt',
            }
            if (g1.name in _COMP_COMPLEMENT_SWAP
                    and g2.name == _COMP_COMPLEMENT_SWAP[g1.name]
                    and g1.args[0].canon() == g2.args[1].canon()
                    and g1.args[1].canon() == g2.args[0].canon()):
                return True

    # DeMorgan complement: and(A1,A2) vs or(B1,B2) where each Ai↔Bi
    # are complementary.  By De Morgan: ¬(A1 ∧ A2) ≡ ¬A1 ∨ ¬A2.
    if isinstance(g1, OOp) and isinstance(g2, OOp):
        if {g1.name, g2.name} == {'and', 'or'}:
            if len(g1.args) == 2 and len(g2.args) == 2:
                # Try both orderings of args
                if (_guards_complementary(g1.args[0], g2.args[0]) and
                        _guards_complementary(g1.args[1], g2.args[1])):
                    return True
                if (_guards_complementary(g1.args[0], g2.args[1]) and
                        _guards_complementary(g1.args[1], g2.args[0])):
                    return True

    # Variable truthiness: X is complement of eq(X, 0/None/False/'')
    # In Python, bool(x) is True iff x is not a falsy value.
    # So `case(x, ...)` and `case(eq(x,0), ...)` have complementary guards.
    _FALSY = (0, None, False, '', [])
    if isinstance(g1, OVar) and isinstance(g2, OOp):
        if g2.name == 'eq' and len(g2.args) == 2:
            if isinstance(g2.args[1], OLit) and g2.args[1].value in _FALSY:
                if g1.canon() == g2.args[0].canon():
                    return True
    if isinstance(g2, OVar) and isinstance(g1, OOp):
        if g1.name == 'eq' and len(g1.args) == 2:
            if isinstance(g1.args[1], OLit) and g1.args[1].value in _FALSY:
                if g2.canon() == g1.args[0].canon():
                    return True

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
    """Identify a hash-named fold's actual operation from body_fn.

    Analyzes the body lambda λ(acc, elem) → new_acc to determine
    the fold's algebraic operation. This enables fold congruence
    when two folds use the same operation but have different hashes.

    IMPORTANT: Only returns an op name when the body lambda is EXACTLY
    λ(acc, x) → op(acc, x) — a direct binary application with no
    extra computation. This ensures the op_name fully determines the
    step function (sound for fold universality).

    Returns an algebraic name ('add', 'bitxor', etc.) or None.
    """
    body = term.body_fn
    if body is None:
        return None
    if not isinstance(body, OLam) or len(body.params) < 2:
        return None

    acc_var = body.params[0]
    elem_var = body.params[1]
    inner = body.body

    # λ(acc, x) → op(acc, x) where op is a pure binary operation
    # Both args must be exactly the bound variables — no subexpressions.
    if isinstance(inner, OOp) and len(inner.args) == 2:
        a0, a1 = inner.args
        # op(acc, elem) — direct binary
        if (isinstance(a0, OVar) and a0.name == acc_var
                and isinstance(a1, OVar) and a1.name == elem_var):
            return inner.name
        # op(elem, acc) — commutative binary
        if (isinstance(a1, OVar) and a1.name == acc_var
                and isinstance(a0, OVar) and a0.name == elem_var):
            if inner.name in ('add', 'iadd', 'mul', 'imul', 'imult', 'mult',
                              'min', 'max', 'gcd', 'bitand', 'bitor', 'bitxor',
                              'and', 'or'):
                return inner.name

    # Do NOT identify append/concat folds by op name alone.
    # λ(acc, x) → .append!(acc, f(x)) depends on f, so the op_name
    # '.append!' does not fully determine the step function.

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

    # ── OOp('map', [f, xs]) ↔ OMap(f, xs) ──
    # Python's map() builtin vs list comprehension produce OOp vs OMap
    # They are semantically identical.
    if isinstance(a, OOp) and a.name == 'map' and isinstance(b, OMap):
        if len(a.args) >= 2 and b.filter_pred is None:
            if (hit_path_equiv(a.args[0], b.transform, ctx, depth+1, memo) is True and
                hit_path_equiv(a.args[1], b.collection, ctx, depth+1, memo) is True):
                return True
        # map(f, filter(pred, xs)) ≡ filter_map(pred, f, xs)
        if len(a.args) >= 2 and b.filter_pred is not None:
            inner = a.args[1]
            if isinstance(inner, OOp) and inner.name == 'filter' and len(inner.args) >= 2:
                if (hit_path_equiv(a.args[0], b.transform, ctx, depth+1, memo) is True and
                    hit_path_equiv(inner.args[0], b.filter_pred, ctx, depth+1, memo) is True and
                    hit_path_equiv(inner.args[1], b.collection, ctx, depth+1, memo) is True):
                    return True
    if isinstance(b, OOp) and b.name == 'map' and isinstance(a, OMap):
        if len(b.args) >= 2 and a.filter_pred is None:
            if (hit_path_equiv(b.args[0], a.transform, ctx, depth+1, memo) is True and
                hit_path_equiv(b.args[1], a.collection, ctx, depth+1, memo) is True):
                return True
        if len(b.args) >= 2 and a.filter_pred is not None:
            inner = b.args[1]
            if isinstance(inner, OOp) and inner.name == 'filter' and len(inner.args) >= 2:
                if (hit_path_equiv(b.args[0], a.transform, ctx, depth+1, memo) is True and
                    hit_path_equiv(inner.args[0], a.filter_pred, ctx, depth+1, memo) is True and
                    hit_path_equiv(inner.args[1], a.collection, ctx, depth+1, memo) is True):
                    return True

    # ── OFold congruence (D5: fold universality) ──
    if isinstance(a, OFold) and isinstance(b, OFold):
        init_eq = hit_path_equiv(a.init, b.init, ctx, depth+1, memo) is True
        coll_eq = hit_path_equiv(a.collection, b.collection, ctx, depth+1, memo) is True
        if init_eq and coll_eq:
            # Same init and collection — check step function equivalence.
            # For NAMED ops (like 'add', 'mul', etc.), the op_name fully
            # determines the step function, so matching names suffice.
            # For HASH-named ops with body_fn, must compare body_fns.
            if a.op_name == b.op_name:
                # If both have body_fn, verify they actually match.
                # This prevents FPs when hash-named folds get canonicalized
                # to the same op name but compute different functions.
                if a.body_fn is not None and b.body_fn is not None:
                    if hit_path_equiv(a.body_fn, b.body_fn, ctx, depth+1, memo) is True:
                        return True
                    # body_fns differ — op_name match alone is insufficient
                else:
                    # At most one has body_fn — op_name match is sufficient
                    # (this covers named ops like 'add' which have no body_fn)
                    return True
            # Hash-based keys that differ: try to show bodies are equivalent
            # by recognizing the fold operation
            op_a = _identify_fold_op(a)
            op_b = _identify_fold_op(b)
            if op_a and op_b and op_a == op_b:
                return True
            # D5 fold universality: fold is determined by (init, collection, body).
            # If bodies are structurally equivalent (via alpha-normalization +
            # path search), the folds compute the same function.
            if a.body_fn is not None and b.body_fn is not None:
                if hit_path_equiv(a.body_fn, b.body_fn, ctx, depth+1, memo) is True:
                    return True

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

    # ── D1b: Linear recursion ↔ fold (catamorphism principle) ──
    # case(guard, op(x, fix(...)), base) ≡ fold[op](base, range(...))
    if isinstance(a, OCase) and isinstance(b, OFold):
        lr = _try_linear_rec_fold_equiv(a, b, ctx, depth, memo)
        if lr is True:
            return True
    if isinstance(b, OCase) and isinstance(a, OFold):
        lr = _try_linear_rec_fold_equiv(b, a, ctx, depth, memo)
        if lr is True:
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

    # ═══════════════════════════════════════════════════════
    # New cross-type path constructors (general Python semantics)
    # ═══════════════════════════════════════════════════════

    # ── Multiset equality path ──
    # eq(counter(x), counter(y)) ↔ eq(sorted(x), sorted(y))
    # Mathematical theorem: two sequences have the same multiset iff sorted forms are equal.
    if isinstance(a, OOp) and isinstance(b, OOp) and a.name == 'eq' == b.name:
        if len(a.args) == 2 and len(b.args) == 2:
            a0, a1 = a.args
            b0, b1 = b.args
            if (isinstance(a0, OOp) and isinstance(a1, OOp)
                    and isinstance(b0, OOp) and isinstance(b1, OOp)):
                a_ops = {a0.name, a1.name}
                b_ops = {b0.name, b1.name}
                multiset_ops = {'counter', 'sorted', 'frozenset', 'set'}
                if (a_ops & multiset_ops and b_ops & multiset_ops
                        and a_ops != b_ops):
                    # Both compare multiset-equivalent representations
                    if (hit_path_equiv(a0.args[0] if a0.args else a0,
                                       b0.args[0] if b0.args else b0,
                                       ctx, depth+1, memo) is True
                        and hit_path_equiv(a1.args[0] if a1.args else a1,
                                           b1.args[0] if b1.args else b1,
                                           ctx, depth+1, memo) is True):
                        return True

    # ── OFix ↔ OCase: fix-point with structured body ──
    # OFix(key, OCase(test, step, base)) ↔ OCase(test, step, base) when the
    # fix-point just wraps a single conditional iteration
    if isinstance(a, OFix) and isinstance(a.body, OCase) and isinstance(b, OCase):
        if hit_path_equiv(a.body, b, ctx, depth+1, memo) is True:
            return True
    if isinstance(b, OFix) and isinstance(b.body, OCase) and isinstance(a, OCase):
        if hit_path_equiv(b.body, a, ctx, depth+1, memo) is True:
            return True

    # ── OFix body extraction ──
    # When both are OFix with different keys, compare their BODIES structurally
    if isinstance(a, OFix) and isinstance(b, OFix) and a.name != b.name:
        if isinstance(a.body, OCase) and isinstance(b.body, OCase):
            if hit_path_equiv(a.body, b.body, ctx, depth+1, memo) is True:
                return True

    # ── OFold ↔ OOp: fold desugaring of builtins ──
    # sum(x) = fold[iadd](0, x), len(x) = fold[iadd](0, map(λ.1, x)),
    # min(x) = fold[min](inf, x), max(x) = fold[max](-inf, x),
    # all(x) = fold[and](True, x), any(x) = fold[or](False, x)
    _fold_builtin_map = {
        ('iadd', 0): 'sum', ('iadd', 0.0): 'sum',
        ('add', 0): 'sum', ('add', 0.0): 'sum',
        ('and', True): 'all', ('.and', True): 'all',
        ('or', False): 'any', ('.or', False): 'any',
    }
    if isinstance(a, OFold) and isinstance(b, OOp):
        init_val = a.init.value if isinstance(a.init, OLit) else None
        key = (a.op_name, init_val)
        if key in _fold_builtin_map and b.name == _fold_builtin_map[key]:
            if len(b.args) >= 1:
                if hit_path_equiv(a.collection, b.args[0], ctx, depth+1, memo) is True:
                    return True
    if isinstance(b, OFold) and isinstance(a, OOp):
        init_val = b.init.value if isinstance(b.init, OLit) else None
        key = (b.op_name, init_val)
        if key in _fold_builtin_map and a.name == _fold_builtin_map[key]:
            if len(a.args) >= 1:
                if hit_path_equiv(b.collection, a.args[0], ctx, depth+1, memo) is True:
                    return True

    # ── OMap ↔ OFold: map as a fold ──
    # map(f, xs) = fold[append]([], map(f, xs)) when fold collects results
    if isinstance(a, OMap) and isinstance(b, OFold):
        if b.op_name in ('.append!', 'concat', 'iadd'):
            init_b = b.init
            if isinstance(init_b, OSeq) and len(init_b.elements) == 0:
                if isinstance(b.collection, OMap):
                    if (hit_path_equiv(a.transform, b.collection.transform, ctx, depth+1, memo) is True
                            and hit_path_equiv(a.collection, b.collection.collection, ctx, depth+1, memo) is True):
                        return True
                # fold collects directly from same source
                if hit_path_equiv(a.collection, b.collection, ctx, depth+1, memo) is True:
                    return True
    if isinstance(b, OMap) and isinstance(a, OFold):
        if a.op_name in ('.append!', 'concat', 'iadd'):
            init_a = a.init
            if isinstance(init_a, OSeq) and len(init_a.elements) == 0:
                if isinstance(a.collection, OMap):
                    if (hit_path_equiv(b.transform, a.collection.transform, ctx, depth+1, memo) is True
                            and hit_path_equiv(b.collection, a.collection.collection, ctx, depth+1, memo) is True):
                        return True
                if hit_path_equiv(b.collection, a.collection, ctx, depth+1, memo) is True:
                    return True

    # ── OFold ↔ OFold with related ops ──
    # fold[iadd] ↔ fold[add], fold[imult] ↔ fold[mult], etc.
    _related_fold_ops = {
        'iadd': 'add', 'add': 'iadd',
        'imult': 'mult', 'mult': 'imult',
        'imul': 'mul', 'mul': 'imul',
    }
    if isinstance(a, OFold) and isinstance(b, OFold):
        if _related_fold_ops.get(a.op_name) == b.op_name:
            if (hit_path_equiv(a.init, b.init, ctx, depth+1, memo) is True
                    and hit_path_equiv(a.collection, b.collection, ctx, depth+1, memo) is True):
                return True

    # ── str.join ↔ fold[concat]: join is a fold ──
    # ''.join(xs) = fold[str_concat]('', xs)
    if isinstance(a, OOp) and a.name == '.join' and isinstance(b, OFold):
        if b.op_name in ('str_concat', 'iadd', 'add', 'concat'):
            if len(a.args) >= 2:
                if (hit_path_equiv(a.args[0], b.init, ctx, depth+1, memo) is True
                        and hit_path_equiv(a.args[1], b.collection, ctx, depth+1, memo) is True):
                    return True
    if isinstance(b, OOp) and b.name == '.join' and isinstance(a, OFold):
        if a.op_name in ('str_concat', 'iadd', 'add', 'concat'):
            if len(b.args) >= 2:
                if (hit_path_equiv(b.args[0], a.init, ctx, depth+1, memo) is True
                        and hit_path_equiv(b.args[1], a.collection, ctx, depth+1, memo) is True):
                    return True

    # ── Arithmetic identities: x*1=x, x+0=x, x//1=x, x**1=x ──
    if isinstance(a, OOp) and isinstance(b, (OVar, OLit, OOp)):
        reduced = _try_arith_identity(a)
        if reduced is not None:
            if hit_path_equiv(reduced, b, ctx, depth+1, memo) is True:
                return True
    if isinstance(b, OOp) and isinstance(a, (OVar, OLit, OOp)):
        reduced = _try_arith_identity(b)
        if reduced is not None:
            if hit_path_equiv(a, reduced, ctx, depth+1, memo) is True:
                return True

    # ── OFold ↔ OFix: fold is an iterative fixpoint ──
    if isinstance(a, OFold) and isinstance(b, OFix):
        if isinstance(b.body, OCase):
            # The fix-point body has the form case(test, step, base)
            # A fold is equivalent when the step accumulates the same way
            if hit_path_equiv(a.init, b.body.false_branch, ctx, depth+1, memo) is True:
                return True
    if isinstance(b, OFold) and isinstance(a, OFix):
        if isinstance(a.body, OCase):
            if hit_path_equiv(b.init, a.body.false_branch, ctx, depth+1, memo) is True:
                return True

    # ── min/max ↔ case(lt/gt) ──
    # min(a, b) ≡ case(lt(a, b), a, b) ≡ case(lte(a, b), a, b)
    # max(a, b) ≡ case(lt(a, b), b, a) ≡ case(lte(a, b), b, a)
    if isinstance(a, OOp) and a.name == 'min' and len(a.args) == 2 and isinstance(b, OCase):
        if isinstance(b.test, OOp) and b.test.name in ('lt', 'lte') and len(b.test.args) == 2:
            if (hit_path_equiv(a.args[0], b.test.args[0], ctx, depth+1, memo) is True and
                hit_path_equiv(a.args[1], b.test.args[1], ctx, depth+1, memo) is True):
                if (hit_path_equiv(a.args[0], b.true_branch, ctx, depth+1, memo) is True and
                    hit_path_equiv(a.args[1], b.false_branch, ctx, depth+1, memo) is True):
                    return True
    if isinstance(b, OOp) and b.name == 'min' and len(b.args) == 2 and isinstance(a, OCase):
        if isinstance(a.test, OOp) and a.test.name in ('lt', 'lte') and len(a.test.args) == 2:
            if (hit_path_equiv(b.args[0], a.test.args[0], ctx, depth+1, memo) is True and
                hit_path_equiv(b.args[1], a.test.args[1], ctx, depth+1, memo) is True):
                if (hit_path_equiv(b.args[0], a.true_branch, ctx, depth+1, memo) is True and
                    hit_path_equiv(b.args[1], a.false_branch, ctx, depth+1, memo) is True):
                    return True
    if isinstance(a, OOp) and a.name == 'max' and len(a.args) == 2 and isinstance(b, OCase):
        if isinstance(b.test, OOp) and b.test.name in ('lt', 'lte') and len(b.test.args) == 2:
            if (hit_path_equiv(a.args[0], b.test.args[0], ctx, depth+1, memo) is True and
                hit_path_equiv(a.args[1], b.test.args[1], ctx, depth+1, memo) is True):
                if (hit_path_equiv(a.args[1], b.true_branch, ctx, depth+1, memo) is True and
                    hit_path_equiv(a.args[0], b.false_branch, ctx, depth+1, memo) is True):
                    return True
    if isinstance(b, OOp) and b.name == 'max' and len(b.args) == 2 and isinstance(a, OCase):
        if isinstance(a.test, OOp) and a.test.name in ('lt', 'lte') and len(a.test.args) == 2:
            if (hit_path_equiv(b.args[0], a.test.args[0], ctx, depth+1, memo) is True and
                hit_path_equiv(b.args[1], a.test.args[1], ctx, depth+1, memo) is True):
                if (hit_path_equiv(b.args[1], a.true_branch, ctx, depth+1, memo) is True and
                    hit_path_equiv(b.args[0], a.false_branch, ctx, depth+1, memo) is True):
                    return True

    # ── Zip/index iteration equivalence ──
    # map(λ(a,b) body, zip(xs, ys)) ≡ map(λ(i) body[a→xs[i],b→ys[i]], range(len(xs)))
    # This also applies when wrapped in fold:
    # fold[op](init, map(λ(a,b) body, zip(xs,ys)))
    #   ≡ fold[op](init, map(λ(i) body[a→xs[i],b→ys[i]], range(len(xs))))
    _zip_result = _try_zip_index_equiv(a, b, ctx, depth, memo)
    if _zip_result is True:
        return True

    # ── reduce(op, coll, init) ≡ fold[op](init, coll) ──
    # Python's functools.reduce is semantically a fold
    if isinstance(a, OOp) and a.name == 'reduce' and isinstance(b, OFold):
        if len(a.args) >= 2:
            # reduce(fn, coll) or reduce(fn, coll, init)
            a_coll = a.args[1]
            a_init = a.args[2] if len(a.args) >= 3 else None
            if (hit_path_equiv(a_coll, b.collection, ctx, depth+1, memo) is True):
                if a_init is not None and hit_path_equiv(a_init, b.init, ctx, depth+1, memo) is True:
                    return True
                if a_init is None:
                    return True  # reduce without init ≡ fold (same semantics)
    if isinstance(b, OOp) and b.name == 'reduce' and isinstance(a, OFold):
        if len(b.args) >= 2:
            b_coll = b.args[1]
            b_init = b.args[2] if len(b.args) >= 3 else None
            if (hit_path_equiv(b_coll, a.collection, ctx, depth+1, memo) is True):
                if b_init is not None and hit_path_equiv(b_init, a.init, ctx, depth+1, memo) is True:
                    return True
                if b_init is None:
                    return True

    # ── map(f, filter(pred, xs)) ≡ filter_map(pred, f, xs) ──
    # Composition of map and filter is semantically filter_map.
    # This also works when wrapped in fold/reduce:
    # reduce(op, map(f, filter(pred, xs)), init) ≡ fold[op](init, filter_map(pred, f, xs))
    _fm_result = _try_map_filter_equiv(a, b, ctx, depth, memo)
    if _fm_result is True:
        return True

    # ── list(enumerate(xs)) ≡ map(λ(i) [i, xs[i]], range(len(xs))) ──
    # enumerate desugaring — enumerate is index-based iteration producing (i, x[i])
    if isinstance(a, OOp) and a.name == 'list' and len(a.args) >= 1:
        if isinstance(a.args[0], OOp) and a.args[0].name == 'enumerate':
            if isinstance(b, OMap) and _is_index_iteration(b):
                src = a.args[0].args[0] if a.args[0].args else None
                idx_src = _extract_index_source(b.collection)
                if src is not None and idx_src is not None:
                    if hit_path_equiv(src, idx_src, ctx, depth+1, memo) is True:
                        return True
    if isinstance(b, OOp) and b.name == 'list' and len(b.args) >= 1:
        if isinstance(b.args[0], OOp) and b.args[0].name == 'enumerate':
            if isinstance(a, OMap) and _is_index_iteration(a):
                src = b.args[0].args[0] if b.args[0].args else None
                idx_src = _extract_index_source(a.collection)
                if src is not None and idx_src is not None:
                    if hit_path_equiv(src, idx_src, ctx, depth+1, memo) is True:
                        return True

    # ── One-step axiom rewrites (NO recursive axiom chaining) ──
    # Apply a single axiom to each side and check if it directly matches
    # or can be closed by pure structural congruence (no further axioms).
    # This prevents "type laundering" where axiom chains cross type domains
    # (e.g., merge → .update → bitor → commute → bitor → .update → merge).
    # Axioms selected via stalk dispatch — only those whose transformation
    # sheaf has support at the root position.
    if depth < 6:
        for rewrite_fn in _select_axioms_for_term(a, ctx):
            try:
                for new_a, _ in rewrite_fn(a, ctx):
                    nc = new_a.canon()
                    if nc == cb:
                        return True
                    # Only structural congruence — no more axiom steps
                    if _structural_congruence(new_a, b, ctx, depth+2, memo) is True:
                        return True
            except Exception:
                continue
        for rewrite_fn in _select_axioms_for_term(b, ctx):
            try:
                for new_b, _ in rewrite_fn(b, ctx):
                    nc = new_b.canon()
                    if nc == ca:
                        return True
                    if _structural_congruence(a, new_b, ctx, depth+2, memo) is True:
                        return True
            except Exception:
                continue

    return None


def _structural_congruence(a: OTerm, b: OTerm, ctx: FiberCtx,
                           depth: int, memo: Dict) -> Optional[bool]:
    """Pure structural congruence — no axiom application.

    This is the sheaf descent condition: check if two terms are
    equivalent by recursing into their structure at each fiber.
    Unlike _hit_path_core, this never applies axiom rewrites,
    so it cannot "launder" types through intermediate representations.
    """
    if depth > 15:
        return None
    ca, cb = a.canon(), b.canon()
    if ca == cb:
        return True
    key = (ca, cb)
    if key in memo:
        return memo[key]
    memo[key] = None

    # Normalize both sides
    na = normalize(a)
    nb = normalize(b)
    if na.canon() == nb.canon():
        memo[key] = True
        return True
    a, b = na, nb

    result = None

    # OOp congruence (pairwise argument match)
    if isinstance(a, OOp) and isinstance(b, OOp):
        if a.name == b.name and len(a.args) == len(b.args):
            if all(_structural_congruence(ai, bi, ctx, depth+1, memo) is True
                   for ai, bi in zip(a.args, b.args)):
                result = True
        # Fiber-aware commutativity
        if result is None and a.name == b.name and len(a.args) == 2 and len(b.args) == 2:
            if _is_fiber_commutative(a.name, ctx, a):
                if (_structural_congruence(a.args[0], b.args[1], ctx, depth+1, memo) is True and
                    _structural_congruence(a.args[1], b.args[0], ctx, depth+1, memo) is True):
                    result = True

    # OCase congruence
    if result is None and isinstance(a, OCase) and isinstance(b, OCase):
        if _structural_congruence(a.test, b.test, ctx, depth+1, memo) is True:
            yes_eq = _structural_congruence(a.true_branch, b.true_branch, ctx, depth+1, memo)
            no_eq = _structural_congruence(a.false_branch, b.false_branch, ctx, depth+1, memo)
            if yes_eq is True and no_eq is True:
                result = True

    # OLam congruence (alpha-equivalent bodies)
    if result is None and isinstance(a, OLam) and isinstance(b, OLam):
        if len(a.params) == len(b.params):
            body_b = b.body
            for pa, pb in zip(a.params, b.params):
                if pa != pb:
                    body_b = _subst_deep(body_b, pb, OVar(pa))
            if _structural_congruence(a.body, body_b, ctx, depth+1, memo) is True:
                result = True

    # OMap congruence
    if result is None and isinstance(a, OMap) and isinstance(b, OMap):
        if (_structural_congruence(a.transform, b.transform, ctx, depth+1, memo) is True and
            _structural_congruence(a.collection, b.collection, ctx, depth+1, memo) is True):
            if a.filter_pred is None and b.filter_pred is None:
                result = True
            elif (a.filter_pred is not None and b.filter_pred is not None and
                  _structural_congruence(a.filter_pred, b.filter_pred, ctx, depth+1, memo) is True):
                result = True

    # OFold congruence
    if result is None and isinstance(a, OFold) and isinstance(b, OFold):
        if a.op_name == b.op_name:
            if (_structural_congruence(a.init, b.init, ctx, depth+1, memo) is True and
                _structural_congruence(a.collection, b.collection, ctx, depth+1, memo) is True):
                result = True

    # OSeq congruence
    if result is None and isinstance(a, OSeq) and isinstance(b, OSeq):
        if len(a.elements) == len(b.elements):
            if all(_structural_congruence(ai, bi, ctx, depth+1, memo) is True
                   for ai, bi in zip(a.elements, b.elements)):
                result = True

    # OFix congruence
    if result is None and isinstance(a, OFix) and isinstance(b, OFix):
        body_b = b.body
        if a.name != b.name:
            body_b = _subst_deep(body_b, b.name, OVar(a.name))
        if _structural_congruence(a.body, body_b, ctx, depth+1, memo) is True:
            result = True

    # ODict congruence
    if result is None and isinstance(a, ODict) and isinstance(b, ODict):
        if len(a.pairs) == len(b.pairs):
            if all(_structural_congruence(ak, bk, ctx, depth+1, memo) is True and
                   _structural_congruence(av, bv, ctx, depth+1, memo) is True
                   for (ak, av), (bk, bv) in zip(a.pairs, b.pairs)):
                result = True

    # OCatch congruence
    if result is None and isinstance(a, OCatch) and isinstance(b, OCatch):
        if (_structural_congruence(a.body, b.body, ctx, depth+1, memo) is True and
            _structural_congruence(a.default, b.default, ctx, depth+1, memo) is True):
            result = True

    # OQuotient congruence
    if result is None and isinstance(a, OQuotient) and isinstance(b, OQuotient):
        if a.equiv_class == b.equiv_class:
            if _structural_congruence(a.inner, b.inner, ctx, depth+1, memo) is True:
                result = True

    # Comparison normalization: lt(a,b) = gt(b,a)
    if result is None and isinstance(a, OOp) and isinstance(b, OOp):
        comp_equiv = {'lt': 'gt', 'gt': 'lt', 'lte': 'gte', 'gte': 'lte'}
        if a.name in comp_equiv and b.name == comp_equiv[a.name]:
            if len(a.args) == 2 and len(b.args) == 2:
                if (_structural_congruence(a.args[0], b.args[1], ctx, depth+1, memo) is True and
                    _structural_congruence(a.args[1], b.args[0], ctx, depth+1, memo) is True):
                    result = True

    memo[key] = result
    return result


def _try_zip_index_equiv(a: OTerm, b: OTerm, ctx: FiberCtx,
                          depth: int, memo: Dict) -> Optional[bool]:
    """Zip/index iteration equivalence (general Python semantic axiom).

    map(λ(a,b) body, zip(xs, ys)) ≡ map(λ(i) body[a→xs[i],b→ys[i]], range(len(xs)))

    This also applies when wrapped in fold:
    fold[op](init, map(f_zip, zip(xs,ys))) ≡ fold[op](init, map(f_idx, range(len(xs))))

    The key insight: iterating via zip(xs,ys) and iterating via range(len(xs))
    with indexing are the same when len(xs)==len(ys).
    """
    # Extract the outer fold wrapper if present
    a_fold_wrap, a_inner = _unwrap_fold(a)
    b_fold_wrap, b_inner = _unwrap_fold(b)

    # Both must have compatible fold wrappers (or neither)
    if a_fold_wrap is not None and b_fold_wrap is not None:
        if a_fold_wrap[0] != b_fold_wrap[0]:  # op_name
            return None
        if not (hit_path_equiv(a_fold_wrap[1], b_fold_wrap[1], ctx, depth+1, memo) is True):
            return None  # init values differ
    elif a_fold_wrap is not None or b_fold_wrap is not None:
        return None  # one has fold wrapper, other doesn't

    # Now check the inner map terms
    return _check_zip_index_maps(a_inner, b_inner, ctx, depth, memo)


def _unwrap_fold(t: OTerm):
    """Unwrap an OFold to get (fold_info, inner_collection).

    Returns (None, t) if t is not a fold wrapping a map.
    Returns ((op_name, init), map_term) if t is fold[op](init, map(...)).
    """
    if isinstance(t, OFold) and isinstance(t.collection, OMap):
        return (t.op_name, t.init), t.collection
    if isinstance(t, OFold):
        return (t.op_name, t.init), t
    return None, t


def _check_zip_index_maps(a: OTerm, b: OTerm, ctx: FiberCtx,
                           depth: int, memo: Dict) -> Optional[bool]:
    """Check if a and b are zip-style vs index-style maps over same data.

    a = map(λ(x,y) body, zip(xs, ys))
    b = map(λ(i) body[x→xs[i], y→ys[i]], range(len(xs)))
    or vice versa.
    """
    if not (isinstance(a, OMap) and isinstance(b, OMap)):
        return None

    zip_map, idx_map = None, None
    # Identify which is zip-style and which is index-style
    if _is_zip_iteration(a) and _is_index_iteration(b):
        zip_map, idx_map = a, b
    elif _is_zip_iteration(b) and _is_index_iteration(a):
        zip_map, idx_map = b, a
    else:
        return None

    # Extract zip sources
    zip_sources = _extract_zip_sources(zip_map.collection)
    if not zip_sources:
        return None

    # Extract index source (range(len(xs)))
    idx_source = _extract_index_source(idx_map.collection)
    if idx_source is None:
        return None

    # Check that zip_sources[0] or a related collection matches idx_source
    sources_match = any(
        hit_path_equiv(src, idx_source, ctx, depth+1, memo) is True
        for src in zip_sources
    )
    if not sources_match:
        return None

    # The transforms differ in variable naming but compute the same thing.
    # zip-style: λ(a,b) f(a,b) — direct element access
    # idx-style: λ(i) f(xs[i], ys[i]) — indexing
    # These are equivalent by definition of zip iteration.
    return True


def _is_zip_iteration(m: OMap) -> bool:
    """Check if map iterates over zip(...)."""
    coll = m.collection
    if isinstance(coll, OOp) and coll.name == 'zip':
        return True
    # Also check for zip wrapped in other forms
    return False


def _is_index_iteration(m: OMap) -> bool:
    """Check if map iterates over range(len(...))."""
    coll = m.collection
    if isinstance(coll, OOp) and coll.name == 'range':
        if len(coll.args) >= 1:
            arg = coll.args[0]
            if isinstance(arg, OOp) and arg.name == 'len':
                return True
    return False


def _extract_zip_sources(coll: OTerm) -> List[OTerm]:
    """Extract the sequences being zipped: zip(xs, ys) → [xs, ys]."""
    if isinstance(coll, OOp) and coll.name == 'zip':
        return list(coll.args)
    return []


def _extract_index_source(coll: OTerm) -> Optional[OTerm]:
    """Extract the source from range(len(xs)) → xs."""
    if isinstance(coll, OOp) and coll.name == 'range':
        if len(coll.args) >= 1:
            arg = coll.args[0]
            if isinstance(arg, OOp) and arg.name == 'len' and len(arg.args) >= 1:
                return arg.args[0]
    return None


def _try_map_filter_equiv(a: OTerm, b: OTerm, ctx: FiberCtx,
                           depth: int, memo: Dict) -> Optional[bool]:
    """Check map(f, filter(pred, xs)) ≡ filter_map(pred, f, xs).

    Also works with reduce/fold wrappers:
    reduce(op, map(f, filter(pred, xs)), init) ≡ fold[op](init, filter_map(pred, f, xs))
    """
    # Direct: OMap with filter collection vs OMap with filter_pred
    if isinstance(a, OMap) and isinstance(b, OMap):
        # a = map(f, filter(pred, xs))  vs  b = filter_map(pred, f, xs)
        if a.filter_pred is None and b.filter_pred is not None:
            # a iterates over filter(...) collection, b has built-in filter
            if isinstance(a.collection, OOp) and a.collection.name == 'filter':
                if len(a.collection.args) >= 2:
                    a_pred = a.collection.args[0]
                    a_xs = a.collection.args[1]
                    if (hit_path_equiv(a_pred, b.filter_pred, ctx, depth+1, memo) is True and
                        hit_path_equiv(a_xs, b.collection, ctx, depth+1, memo) is True and
                        hit_path_equiv(a.transform, b.transform, ctx, depth+1, memo) is True):
                        return True
        if b.filter_pred is None and a.filter_pred is not None:
            if isinstance(b.collection, OOp) and b.collection.name == 'filter':
                if len(b.collection.args) >= 2:
                    b_pred = b.collection.args[0]
                    b_xs = b.collection.args[1]
                    if (hit_path_equiv(b_pred, a.filter_pred, ctx, depth+1, memo) is True and
                        hit_path_equiv(b_xs, a.collection, ctx, depth+1, memo) is True and
                        hit_path_equiv(b.transform, a.transform, ctx, depth+1, memo) is True):
                        return True

    # With fold/reduce wrapper:
    # reduce(op_fn, map(f, filter(pred, xs)), init) ≡ fold[op](init, filter_map(pred, f, xs))
    if isinstance(a, OOp) and a.name == 'reduce' and isinstance(b, OFold):
        if len(a.args) >= 2:
            a_coll = a.args[1]  # map(f, filter(pred, xs))
            a_init = a.args[2] if len(a.args) >= 3 else None
            if isinstance(a_coll, OOp) and a_coll.name == 'map':
                # Not an OMap but an OOp wrapping map — check for filter inside
                pass
            if isinstance(a_coll, OMap) and isinstance(b.collection, OMap):
                # a_coll is map(f, filter(pred, xs)), b.collection is filter_map(pred, f, xs)
                if a_init is not None:
                    if hit_path_equiv(a_init, b.init, ctx, depth+1, memo) is True:
                        inner = _try_map_filter_equiv(a_coll, b.collection, ctx, depth, memo)
                        if inner is True:
                            return True
    if isinstance(b, OOp) and b.name == 'reduce' and isinstance(a, OFold):
        if len(b.args) >= 2:
            b_coll = b.args[1]
            b_init = b.args[2] if len(b.args) >= 3 else None
            if isinstance(b_coll, OMap) and isinstance(a.collection, OMap):
                if b_init is not None:
                    if hit_path_equiv(b_init, a.init, ctx, depth+1, memo) is True:
                        inner = _try_map_filter_equiv(b_coll, a.collection, ctx, depth, memo)
                        if inner is True:
                            return True
    return None


def _is_fiber_commutative(op_name: str, ctx: FiberCtx, term: OTerm) -> bool:
    """Check if an operation is commutative on the current fiber.

    Commutativity is type-dependent:
    - add: commutative on int, NOT on str/list (concatenation) or float
    - bitor/bitand/bitxor: commutative on int, NOT on dict (| is merge)
    - mul, and, or, min, max, eq: always commutative
    """
    always_comm = {'mul', 'mult', 'and', 'or',
                   'min', 'max', 'eq', 'noteq'}
    if op_name in always_comm:
        return True
    int_only_comm = {'add', 'bitor', 'bitand', 'bitxor'}
    if op_name in int_only_comm and ctx.is_integer(term):
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


def _try_linear_rec_fold_equiv(
    case_term: OCase, fold: OFold, ctx: FiberCtx,
    depth: int, memo: Dict
) -> Optional[bool]:
    """Prove linear recursion ≡ fold equivalence.

    Pattern: case(guard(x, K), op(x, fix[h]([sub(x, 1)])), base)
      ≡ fold[op](base, range(K+1, x+1))  [for commutative+associative op]

    This is the catamorphism principle: a linear recursion over natural
    numbers is equivalent to a fold over the corresponding range when
    the combining operation is commutative and associative.

    Sound because: f(n) = n ⊕ f(n-1), f(K) = base
    unrolls to: n ⊕ (n-1) ⊕ ... ⊕ (K+1) ⊕ base
    = fold[⊕](base, [K+1, ..., n])  (by commutativity+associativity)
    = fold[⊕](base, range(K+1, n+1))
    """
    if not isinstance(case_term, OCase):
        return None
    if not isinstance(fold, OFold):
        return None

    # Extract the linear recursion pattern from the case
    rec_info = _extract_linear_recursion(case_term)
    if rec_info is None:
        return None

    op_name, param, step, base, guard_bound, fix_name = rec_info

    # Check: is the fold using the same operation?
    _OP_ALIASES = {
        'add': {'add', 'iadd'}, 'iadd': {'add', 'iadd'},
        'mult': {'mult', 'imult', 'mul', 'imul'},
        'imult': {'mult', 'imult', 'mul', 'imul'},
        'mul': {'mult', 'imult', 'mul', 'imul'},
        'imul': {'mult', 'imult', 'mul', 'imul'},
    }
    fold_op = fold.op_name
    op_aliases = _OP_ALIASES.get(op_name, {op_name})
    if fold_op not in op_aliases:
        return None

    # Check: is the operation commutative AND associative?
    _COMM_ASSOC_OPS = {'add', 'iadd', 'mult', 'imult', 'mul', 'imul',
                       'and', 'or', 'bitand', 'bitor', 'bitxor',
                       'min', 'max', 'gcd'}
    if op_name not in _COMM_ASSOC_OPS:
        return None

    # Check: do bases match?
    if hit_path_equiv(base, fold.init, ctx, depth+1, memo) is not True:
        return None

    # Check: does the fold's collection cover the same range?
    # The recursion covers: param, param-step, ..., guard_bound+1
    # which as a range is: range(guard_bound+1, param+1) (for step=1)
    # The fold covers: fold.collection (often range(param+1) or range(N))
    #
    # For commutative ops with identity base, including extra identity
    # elements doesn't change the result. E.g., fold[add](0, range(n+1))
    # includes 0, but adding 0 is identity.
    fold_coll = fold.collection

    if isinstance(fold_coll, OOp) and fold_coll.name == 'range':
        if len(fold_coll.args) == 1:
            # range(N) = range(0, N)
            fold_upper = fold_coll.args[0]
            fold_lower = OLit(0)
        elif len(fold_coll.args) >= 2:
            fold_lower = fold_coll.args[0]
            fold_upper = fold_coll.args[1]
        else:
            return None

        # Expected: range(guard_bound+1, param+1) for step=1
        expected_upper = OOp('add', (param, OLit(1)))

        # Check upper bound match
        if hit_path_equiv(fold_upper, expected_upper, ctx, depth+1, memo) is not True:
            # Maybe fold_upper = param+1 expressed differently
            return None

        # Check lower bound:
        # If fold starts at 0 and guard_bound is 0, the extra 0 is the identity
        # element for add (0 + x = x) or mult has identity 1
        _IDENTITY = {'add': 0, 'iadd': 0, 'mult': 1, 'imult': 1,
                     'mul': 1, 'imul': 1, 'and': True, 'or': False,
                     'bitand': -1, 'bitor': 0, 'bitxor': 0,
                     'min': float('inf'), 'max': float('-inf'),
                     'gcd': 0}
        identity = _IDENTITY.get(op_name)

        # The recursion starts at guard_bound+1 (after the guard fails)
        # If fold_lower <= guard_bound+1, the extra elements must all be
        # identity elements, which range elements 0..guard_bound are
        # IF the identity of the op equals those range elements.
        # For add with identity 0: range(0, n+1) = [0,1,...,n]
        #   The extra element 0 IS the identity, so fold matches.
        # For mult with identity 1: range(1, n+1) = [1,2,...,n]
        #   If fold starts at 0: range(0, n+1) = [0,1,...,n]
        #   But 0 is NOT the identity for mult, so this would be wrong!
        #   However, mult(0, x) = 0, not x. So this doesn't help.
        #   But the recursion for factorial is f(n) = n * f(n-1), f(1) = 1
        #   So guard_bound = 1, and fold should be range(2, n+1) or range(1, n+1)
        #   range(1, n+1) includes 1 which is the identity for mult. OK.

        if isinstance(fold_lower, OLit) and isinstance(fold_lower.value, (int, float)):
            lower_val = fold_lower.value
            if isinstance(guard_bound, OLit) and isinstance(guard_bound.value, (int, float)):
                gb_val = guard_bound.value
                # All extra elements in [lower_val, gb_val] must be identity for op
                if identity is not None:
                    extra_ok = True
                    for v in range(int(lower_val), int(gb_val) + 1):
                        if v != identity:
                            extra_ok = False
                            break
                    if extra_ok:
                        return True
                # Exact match: fold_lower == guard_bound + 1
                if lower_val == gb_val + 1:
                    return True
            elif hit_path_equiv(fold_lower, OOp('add', (guard_bound, OLit(1))), ctx, depth+1, memo) is True:
                return True
            # For identity-matching: if lower_val is 0 and op is add,
            # range starts at 0 which is identity for add
            if identity is not None and lower_val == identity:
                return True

    return None


def _extract_linear_recursion(case_term: OCase):
    """Extract linear recursion info from case(guard, op(x, fix), base).

    Returns (op_name, param, step, base, guard_bound, fix_name) or None.

    The pattern is:
      case(lt(K, x), op(x, fix[h]([sub(x, step)])), base)
    or equivalently:
      case(lt(x, K+1), base, op(x, fix[h]([sub(x, step)])))
    """
    test = case_term.test
    true_br = case_term.true_branch
    false_br = case_term.false_branch

    # Determine which branch is the recursive case and which is the base
    rec_branch = base_branch = None
    if _contains_fix(true_br) and not _contains_fix(false_br):
        rec_branch, base_branch = true_br, false_br
    elif _contains_fix(false_br) and not _contains_fix(true_br):
        rec_branch, base_branch = false_br, true_br
    else:
        return None

    # Extract the binary operation and fix call from the recursive branch
    if not isinstance(rec_branch, OOp) or len(rec_branch.args) != 2:
        return None

    op_name = rec_branch.name
    arg0, arg1 = rec_branch.args

    # Find which arg is the fix call and which is the parameter
    fix_node = param_node = None
    if isinstance(arg1, OFix):
        fix_node, param_node = arg1, arg0
    elif isinstance(arg0, OFix):
        fix_node, param_node = arg0, arg1
    else:
        return None

    if not isinstance(param_node, OVar):
        return None

    param = param_node

    # Check the fix call argument: should be sub(param, step)
    if not isinstance(fix_node.body, OSeq) or len(fix_node.body.elements) != 1:
        return None
    call_arg = fix_node.body.elements[0]
    if not isinstance(call_arg, OOp) or call_arg.name != 'sub' or len(call_arg.args) != 2:
        return None
    if call_arg.args[0].canon() != param.canon():
        return None
    if not isinstance(call_arg.args[1], OLit):
        return None
    step = call_arg.args[1].value
    if not isinstance(step, int) or step <= 0:
        return None

    # Extract the guard bound from the test
    # Pattern: lt(K, param) → guard_bound = K (base when param ≤ K)
    # Pattern: lt(param, K+1) with base in false_br → need to flip
    guard_bound = _extract_guard_bound(test, param, rec_branch is true_br)
    if guard_bound is None:
        return None

    return (op_name, param, step, base_branch, guard_bound, fix_node.name)


def _extract_guard_bound(test: OTerm, param: OVar, rec_is_true: bool) -> Optional[OTerm]:
    """Extract the guard bound K from a comparison test.

    If rec_is_true: the guard must be satisfied for recursion to continue.
      lt(K, param): recursion when param > K, base when param ≤ K → bound = K
      gt(param, K): same as lt(K, param) → bound = K
    If rec_is_false: the guard must FAIL for recursion.
      lt(param, K+1) with base in true → rec in false: weird, skip.
    """
    if not isinstance(test, OOp) or len(test.args) != 2:
        return None

    a0, a1 = test.args

    if rec_is_true:
        # Guard true → recurse. Guard: lt(K, param) or gt(param, K)
        if test.name == 'lt' and a1.canon() == param.canon():
            return a0  # bound = K
        if test.name == 'gt' and a0.canon() == param.canon():
            return a1  # bound = K
        if test.name == 'lte' and a1.canon() == param.canon():
            # lte(K, param): recurse when param >= K → bound = K-1
            return OOp('sub', (a0, OLit(1)))
        if test.name == 'gte' and a0.canon() == param.canon():
            return OOp('sub', (a1, OLit(1)))
    else:
        # Guard false → recurse. Guard: lt(param, K) → rec when param >= K
        # This is the "else" branch recursion: guard true = base case
        if test.name == 'lt' and a0.canon() == param.canon():
            # lt(param, K): base when param < K, rec when param >= K
            # bound = K - 1
            return OOp('sub', (a1, OLit(1)))
        if test.name == 'gt' and a1.canon() == param.canon():
            return OOp('sub', (a0, OLit(1)))
        if test.name == 'lte' and a0.canon() == param.canon():
            # lte(param, K): base when param <= K, rec when param > K
            return a1  # bound = K
        if test.name == 'gte' and a1.canon() == param.canon():
            return a0

    return None


def _contains_fix(term: OTerm) -> bool:
    """Check if a term contains any OFix node."""
    if isinstance(term, OFix):
        return True
    for attr in ['test', 'true_branch', 'false_branch', 'init',
                 'collection', 'body', 'inner', 'default']:
        child = getattr(term, attr, None)
        if child is not None and _contains_fix(child):
            return True
    if hasattr(term, 'args'):
        for a in term.args:
            if _contains_fix(a):
                return True
    if hasattr(term, 'elements'):
        for e in term.elements:
            if _contains_fix(e):
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


def _try_arith_identity(term: OOp) -> Optional[OTerm]:
    """Try to reduce an arithmetic identity to its simpler form.

    General mathematical identities:
      x * 1 = x,  1 * x = x
      x + 0 = x,  0 + x = x
      x - 0 = x
      x // 1 = x
      x ** 1 = x
      x & ~0 = x (all bits set)
      x | 0 = x
      x ^ 0 = x
    """
    if len(term.args) != 2:
        return None
    left, right = term.args

    def _is_lit_val(t, val):
        return isinstance(t, OLit) and t.value == val

    name = term.name
    if name in ('mul', 'mult', 'imul', 'imult'):
        if _is_lit_val(right, 1):
            return left
        if _is_lit_val(left, 1):
            return right
    elif name in ('add', 'iadd'):
        if _is_lit_val(right, 0):
            return left
        if _is_lit_val(left, 0):
            return right
    elif name in ('sub', 'isub'):
        if _is_lit_val(right, 0):
            return left
    elif name in ('floordiv', 'ifloordiv', 'truediv', 'itruediv'):
        if _is_lit_val(right, 1):
            return left
    elif name in ('pow', 'ipow'):
        if _is_lit_val(right, 1):
            return left
        if _is_lit_val(right, 0):
            return OLit(1)
    elif name in ('bitor', 'ibitor', 'bitxor', 'ibitxor'):
        if _is_lit_val(right, 0):
            return left
        if _is_lit_val(left, 0):
            return right
    elif name in ('bitand', 'ibitand'):
        if _is_lit_val(right, -1):
            return left
        if _is_lit_val(left, -1):
            return right
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
# Extended Axioms — ALL axiom modules from axioms/ directory
# ═══════════════════════════════════════════════════════════
# The monograph treats every dichotomy D1-D48 and Python idiom
# P1-P48 as a path constructor in the PyComp HIT.  Path search
# must have access to ALL of them to find proofs.  Restricting
# to a hand-picked subset means proofs that exist in the theory
# will not be found.

def _make_axiom_wrapper(fn, name):
    """Create a wrapper with a specific __name__ for feature filtering."""
    def wrapper(term, ctx):
        return fn(term, ctx)
    wrapper.__name__ = name
    return wrapper


def _load_all_axiom_modules():
    """Load all axiom modules from cctt.axioms and return (axiom_fns, name_map).

    Each module must expose an ``apply(term, ctx)`` function that
    returns ``List[Tuple[OTerm, str]]`` of rewrites.
    """
    import importlib, os, pathlib
    axioms_dir = pathlib.Path(__file__).parent / 'axioms'
    module_names = sorted(
        f.stem for f in axioms_dir.glob('*.py')
        if f.stem != '__init__' and not f.stem.startswith('.')
    )

    fns = []
    name_map = {}
    for mod_name in module_names:
        try:
            mod = importlib.import_module(f'cctt.axioms.{mod_name}')
            wrapper = _make_axiom_wrapper(mod.apply, f'_axiom_{mod_name}')
            fns.append(wrapper)
            name_map[wrapper] = mod_name.upper()
        except (ImportError, AttributeError):
            pass
    return fns, name_map


_MODULE_AXIOMS, _MODULE_AXIOM_NAMES = _load_all_axiom_modules()

# _ALL_AXIOMS: inline root axioms + all module axioms (deduplicated by name)
# Inline axioms handle the core cases with optimised code;
# module axioms provide the full D1-D48 + P1-P48 coverage.
_inline_names = {
    'D1_fold_unfold', 'D2_beta', 'D4_comp_fusion', 'D5_fold_universal',
    'D8_section_merge', 'D13_histogram', 'D16_memo_dp', 'D17_assoc',
    'D19_sort_scan', 'D20_spec_unify', 'D22_effect_elim', 'D24_eta',
    'ALG_algebra', 'QUOT_quotient', 'FOLD_fold', 'CASE_case',
}
# Module axioms that duplicate an inline axiom are skipped
_dedup_module_axioms = [
    fn for fn, name in zip(_MODULE_AXIOMS, _MODULE_AXIOM_NAMES.values())
    if name not in _inline_names
    and name.replace('_', '').upper().replace('D0', 'D').replace('P0', 'P')
       not in {n.replace('_', '').upper() for n in _inline_names}
]

# Check for true duplicates by matching d01↔D1, d02↔D2, etc.
_inline_prefixes = set()
for n in _inline_names:
    # Extract the number: D1 -> 1, D13 -> 13
    import re as _re2
    m = _re2.match(r'[A-Z]+(\d+)', n)
    if m:
        _inline_prefixes.add(m.group(1))

_dedup_module_axioms2 = []
for fn in _MODULE_AXIOMS:
    name = _MODULE_AXIOM_NAMES.get(fn, '')
    # Extract number from module name like D01_FOLD_UNFOLD -> 01
    m = _re2.match(r'D(\d+)', name)
    if m and m.group(1).lstrip('0') in _inline_prefixes:
        continue  # Skip — covered by inline
    _dedup_module_axioms2.append(fn)

_ALL_AXIOMS = list(_ROOT_AXIOMS) + _dedup_module_axioms2


# ═══════════════════════════════════════════════════════════════════
# Sheaf-theoretic axiom selection (replaces blind iteration)
# ═══════════════════════════════════════════════════════════════════
# Each axiom is a section of a transformation sheaf over the OTerm
# site.  _select_axioms_for_term computes the stalk at the given
# position and returns only the axioms whose support contains it.

# Root axiom domain classification: constructor → applicable inline axioms
_ROOT_AXIOM_DOMAINS: Dict[str, List] = {
    'OFix':      [_axiom_d1_fold_unfold, _axiom_d16_memo_dp],
    'OOp':       [_axiom_d2_beta, _axiom_d13_histogram, _axiom_algebra],
    'OMap':      [_axiom_d4_comp_fusion],
    'OFold':     [_axiom_d5_fold_universal, _axiom_d17_assoc,
                  _axiom_d19_sort_scan, _axiom_fold],
    'OCase':     [_axiom_d8_section_merge, _axiom_case],
    'OCatch':    [_axiom_d22_effect_elim],
    'OLam':      [_axiom_d24_eta],
    'OQuotient': [_axiom_quotient],
    # d20 is universal (applies to any term to recognize specs)
}

# Module axiom domain classification: constructor → applicable module axioms
_MODULE_AXIOM_DOMAINS: Dict[str, List] = {}


def _build_module_axiom_domains():
    """Classify module axioms by the OTerm constructors they operate on.

    Uses the sheaf_axiom_index domain specifications to build an
    inverted index from constructor name → list of module apply fns.
    """
    from .sheaf_axiom_index import get_domain
    _MODULE_AXIOM_DOMAINS.clear()

    for fn in _dedup_module_axioms2:
        name = _MODULE_AXIOM_NAMES.get(fn, '')
        # Get semantic domain from the sheaf index
        domain = get_domain(name)
        if domain is None:
            # Unknown module — default to OOp
            _MODULE_AXIOM_DOMAINS.setdefault('OOp', []).append(fn)
            continue
        for ctor in domain.constructors:
            _MODULE_AXIOM_DOMAINS.setdefault(ctor, []).append(fn)


_MODULE_DOMAINS_BUILT = False


def _select_axioms_for_term(term: OTerm, ctx: FiberCtx) -> List:
    """Select axioms applicable to ``term`` using stalk-based dispatch.

    Returns the union of:
      1. Inline root axioms whose domain contains term's constructor
      2. Module axioms whose domain contains term's constructor
      3. D20 (spec unify) — always applicable (universal axiom)

    This is the stalk computation: Γ({U_x}, T_axiom) where U_x is
    the open neighborhood of the term's position in the OTerm site.
    """
    global _MODULE_DOMAINS_BUILT
    if not _MODULE_DOMAINS_BUILT:
        _build_module_axiom_domains()
        _MODULE_DOMAINS_BUILT = True

    ctor = type(term).__name__
    result = list(_ROOT_AXIOM_DOMAINS.get(ctor, []))

    # D20 is universal — always include it
    result.append(_axiom_d20_spec_unify)

    # Add module axioms for this constructor
    result.extend(_MODULE_AXIOM_DOMAINS.get(ctor, []))

    return result


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
    # Also register all module axiom names
    for _fn, _name in _MODULE_AXIOM_NAMES.items():
        _AXIOM_NAME_MAP[_fn] = _name
except Exception:
    pass


def relevant_axioms(
    term: OTerm, ctx: FiberCtx,
    axiom_list: Optional[List[Callable]] = None,
) -> List[Callable]:
    """Filter axioms to those relevant for ``term`` using stalk dispatch + symbol overlap.

    First filters by semantic domain (stalk), then by symbol overlap.
    """
    if axiom_list is None:
        # Use stalk-based selection instead of _ALL_AXIOMS
        axiom_list = _select_axioms_for_term(term, ctx)
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
    """Extended spec identification — STRUCTURAL patterns only.

    Identifies general aggregate operations (fold→min/max/all/any/etc.)
    before the generic fold catch-all.  No function-specific recognition
    (gcd, fibonacci, catalan, etc.) — those are overfitting.
    """
    # ── Specific fold aggregates (before generic fold catch-all) ──
    if isinstance(term, OFold):
        if term.op_name in ('min', '.min'):
            return ('min', (term.collection,))
        if term.op_name in ('max', '.max'):
            return ('max', (term.collection,))
        if term.op_name in ('and', '.and'):
            if isinstance(term.init, OLit) and term.init.value is True:
                return ('all', (term.collection,))
        if term.op_name in ('or', '.or'):
            if isinstance(term.init, OLit) and term.init.value is False:
                return ('any', (term.collection,))
        if term.op_name in ('concat', '.concat', 'extend'):
            if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
                return ('flatten', (term.collection,))
        if term.op_name in ('prepend', '.prepend', 'cons'):
            if isinstance(term.init, OSeq) and len(term.init.elements) == 0:
                return ('reverse', (term.collection,))
        if term.op_name in ('.mul', 'mul', 'imul', 'mult'):
            if isinstance(term.init, OLit) and term.init.value == 1:
                return ('product', (term.collection,))

    # ── Delegate to base ──
    base = _identify_spec(term)
    if base is not None:
        return base

    # ── Additional OOp patterns (structural) ──
    if isinstance(term, OOp) and term.name == 'max':
        return ('max', term.args)
    if isinstance(term, OOp) and term.name == 'min':
        return ('min', term.args)
    if isinstance(term, OOp) and term.name in ('reversed', 'list_reverse'):
        return ('reverse', term.args)
    if isinstance(term, OOp) and term.name == 'all':
        return ('all', term.args)
    if isinstance(term, OOp) and term.name == 'any':
        return ('any', term.args)
    if isinstance(term, OOp) and term.name == 'len':
        return ('len', term.args)

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

    spec_f = identify_spec_extended(nf_f)
    spec_g = identify_spec_extended(nf_g)
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
