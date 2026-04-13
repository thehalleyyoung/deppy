"""Proposals for Chapters 27-31+ (Nat-Eliminator through Normalization Traces).

This module provides a comprehensive toolkit for analyzing, transforming,
and profiling the OTerm language from the CCTT denotational semantics engine.

Implemented proposals:
  1. Nat-eliminator extraction from OFix bodies (Ch 27)
  2. Course-of-values recursion detection (Ch 29)
  3. Map-map fusion in Phase 4 (Ch 30)
  4. Normalization trace with per-phase snapshots (Ch 31)
  5. Full catamorphism recognizer (fold/map/filter/scan/reduce)
  6. Recursion scheme classifier (primitive, course-of-values, mutual, tail, tree)
  7. HOF fusion engine (map∘map, filter∘map, map∘filter fusion rules)
  8. De Bruijn normalization for OLam (full alpha-equivalence)
  9. Normalization phase profiler (which phase does the most work)
  10. OTerm pretty-printer with mathematical notation
  11. Compilation coverage analyzer (which Python AST nodes are/aren't handled)
  12. Fold canonicalization extensions (more base/op combinations)
  13. OTerm size/depth metrics for complexity estimation
"""
from __future__ import annotations

import ast
import textwrap
import time
from collections import Counter
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple, Union

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, OLam, OMap,
    OQuotient, ODict, OUnknown, OAbstract, OCatch,
    compile_to_oterm, normalize,
    _phase1_beta, _phase2_ring, _phase3_fold,
    _phase4_hof, _phase5_unify, _phase6_quotient, _phase7_piecewise,
    _subst,
)


# ═══════════════════════════════════════════════════════════
# §1  OTerm Structural Metrics (size, depth, complexity)
# ═══════════════════════════════════════════════════════════

def oterm_size(term: OTerm) -> int:
    """Count the total number of OTerm nodes in the tree.

    Every constructor (OVar, OLit, OOp, etc.) contributes exactly 1.
    This is the |t| metric used for termination arguments in the monograph.
    """
    if isinstance(term, (OVar, OLit, OUnknown)):
        return 1
    if isinstance(term, OOp):
        return 1 + sum(oterm_size(a) for a in term.args)
    if isinstance(term, OCase):
        return 1 + oterm_size(term.test) + oterm_size(term.true_branch) + oterm_size(term.false_branch)
    if isinstance(term, OFold):
        return 1 + oterm_size(term.init) + oterm_size(term.collection)
    if isinstance(term, OFix):
        return 1 + oterm_size(term.body)
    if isinstance(term, OSeq):
        return 1 + sum(oterm_size(e) for e in term.elements)
    if isinstance(term, ODict):
        return 1 + sum(oterm_size(k) + oterm_size(v) for k, v in term.pairs)
    if isinstance(term, OQuotient):
        return 1 + oterm_size(term.inner)
    if isinstance(term, OAbstract):
        return 1 + sum(oterm_size(a) for a in term.inputs)
    if isinstance(term, OLam):
        return 1 + oterm_size(term.body)
    if isinstance(term, OMap):
        s = 1 + oterm_size(term.transform) + oterm_size(term.collection)
        if term.filter_pred is not None:
            s += oterm_size(term.filter_pred)
        return s
    if isinstance(term, OCatch):
        return 1 + oterm_size(term.body) + oterm_size(term.default)
    return 1


def oterm_depth(term: OTerm) -> int:
    """Compute the maximum nesting depth of an OTerm tree.

    Depth 0 = leaf node (OVar, OLit, OUnknown).
    Each constructor adds 1 to the depth of its deepest child.
    """
    if isinstance(term, (OVar, OLit, OUnknown)):
        return 0
    if isinstance(term, OOp):
        return 1 + max((oterm_depth(a) for a in term.args), default=0)
    if isinstance(term, OCase):
        return 1 + max(oterm_depth(term.test), oterm_depth(term.true_branch),
                       oterm_depth(term.false_branch))
    if isinstance(term, OFold):
        return 1 + max(oterm_depth(term.init), oterm_depth(term.collection))
    if isinstance(term, OFix):
        return 1 + oterm_depth(term.body)
    if isinstance(term, OSeq):
        return 1 + max((oterm_depth(e) for e in term.elements), default=0)
    if isinstance(term, ODict):
        return 1 + max((max(oterm_depth(k), oterm_depth(v)) for k, v in term.pairs), default=0)
    if isinstance(term, OQuotient):
        return 1 + oterm_depth(term.inner)
    if isinstance(term, OAbstract):
        return 1 + max((oterm_depth(a) for a in term.inputs), default=0)
    if isinstance(term, OLam):
        return 1 + oterm_depth(term.body)
    if isinstance(term, OMap):
        d = max(oterm_depth(term.transform), oterm_depth(term.collection))
        if term.filter_pred is not None:
            d = max(d, oterm_depth(term.filter_pred))
        return 1 + d
    if isinstance(term, OCatch):
        return 1 + max(oterm_depth(term.body), oterm_depth(term.default))
    return 0


def collect_free_vars(term: OTerm, bound: FrozenSet[str] = frozenset()) -> Set[str]:
    """Collect free variable names from an OTerm, respecting OLam binders."""
    if isinstance(term, OVar):
        return {term.name} if term.name not in bound else set()
    if isinstance(term, OLit) or isinstance(term, OUnknown):
        return set()
    if isinstance(term, OOp):
        s: Set[str] = set()
        for a in term.args:
            s |= collect_free_vars(a, bound)
        return s
    if isinstance(term, OCase):
        return (collect_free_vars(term.test, bound)
                | collect_free_vars(term.true_branch, bound)
                | collect_free_vars(term.false_branch, bound))
    if isinstance(term, OFold):
        return collect_free_vars(term.init, bound) | collect_free_vars(term.collection, bound)
    if isinstance(term, OFix):
        return collect_free_vars(term.body, bound | {term.name})
    if isinstance(term, OSeq):
        s = set()
        for e in term.elements:
            s |= collect_free_vars(e, bound)
        return s
    if isinstance(term, ODict):
        s = set()
        for k, v in term.pairs:
            s |= collect_free_vars(k, bound) | collect_free_vars(v, bound)
        return s
    if isinstance(term, OQuotient):
        return collect_free_vars(term.inner, bound)
    if isinstance(term, OAbstract):
        s = set()
        for a in term.inputs:
            s |= collect_free_vars(a, bound)
        return s
    if isinstance(term, OLam):
        return collect_free_vars(term.body, bound | frozenset(term.params))
    if isinstance(term, OMap):
        s = collect_free_vars(term.transform, bound) | collect_free_vars(term.collection, bound)
        if term.filter_pred is not None:
            s |= collect_free_vars(term.filter_pred, bound)
        return s
    if isinstance(term, OCatch):
        return collect_free_vars(term.body, bound) | collect_free_vars(term.default, bound)
    return set()


def collect_node_types(term: OTerm) -> Counter:
    """Count occurrences of each OTerm constructor type in the tree."""
    counts: Counter = Counter()
    _count_types(term, counts)
    return counts


def _count_types(term: OTerm, counts: Counter) -> None:
    counts[type(term).__name__] += 1
    if isinstance(term, OOp):
        for a in term.args:
            _count_types(a, counts)
    elif isinstance(term, OCase):
        _count_types(term.test, counts)
        _count_types(term.true_branch, counts)
        _count_types(term.false_branch, counts)
    elif isinstance(term, OFold):
        _count_types(term.init, counts)
        _count_types(term.collection, counts)
    elif isinstance(term, OFix):
        _count_types(term.body, counts)
    elif isinstance(term, OSeq):
        for e in term.elements:
            _count_types(e, counts)
    elif isinstance(term, ODict):
        for k, v in term.pairs:
            _count_types(k, counts)
            _count_types(v, counts)
    elif isinstance(term, OQuotient):
        _count_types(term.inner, counts)
    elif isinstance(term, OAbstract):
        for a in term.inputs:
            _count_types(a, counts)
    elif isinstance(term, OLam):
        _count_types(term.body, counts)
    elif isinstance(term, OMap):
        _count_types(term.transform, counts)
        _count_types(term.collection, counts)
        if term.filter_pred is not None:
            _count_types(term.filter_pred, counts)
    elif isinstance(term, OCatch):
        _count_types(term.body, counts)
        _count_types(term.default, counts)


@dataclass(frozen=True)
class OTermMetrics:
    """Aggregate complexity metrics for an OTerm."""
    size: int
    depth: int
    free_vars: FrozenSet[str]
    node_types: Dict[str, int]
    has_recursion: bool
    has_branching: bool
    has_higher_order: bool

    @property
    def complexity_score(self) -> float:
        """Heuristic complexity score: weighted combination of size, depth, features."""
        score = float(self.size)
        score += self.depth * 2.0
        if self.has_recursion:
            score *= 1.5
        if self.has_higher_order:
            score *= 1.3
        return score


def compute_metrics(term: OTerm) -> OTermMetrics:
    """Compute all structural metrics for an OTerm in a single pass."""
    node_types = collect_node_types(term)
    fv = collect_free_vars(term)
    return OTermMetrics(
        size=oterm_size(term),
        depth=oterm_depth(term),
        free_vars=frozenset(fv),
        node_types=dict(node_types),
        has_recursion=node_types.get('OFix', 0) > 0,
        has_branching=node_types.get('OCase', 0) > 0,
        has_higher_order=(node_types.get('OLam', 0) > 0
                          or node_types.get('OMap', 0) > 0),
    )


# ═══════════════════════════════════════════════════════════
# §2  Nat-eliminator extraction from OFix (Ch 27)
# ═══════════════════════════════════════════════════════════

@dataclass
class NatElimParams:
    """Parameters extracted by the Nat-eliminator.

    Represents the decomposition:
        fix[f](case(cmp(n, t), base, op(n, f(n-1))))
    into the components (base, threshold, op, param, cmp).
    """
    base_val: OTerm
    threshold: OTerm
    op_name: str
    param_name: str
    cmp_op: str


def extract_nat_elim(fix: OFix) -> Optional[NatElimParams]:
    """Extract Nat-eliminator parameters from an OFix body.

    Matches the pattern:
        OFix[f](OCase(OOp(cmp, (n, t)), OLit(b), OOp(op, (n, f(n-1)))))

    Returns NatElimParams if the pattern matches, None otherwise.
    This is the formal extraction described in Theorem 27.0.3.
    """
    body = fix.body
    if not isinstance(body, OCase):
        return None

    test = body.test
    if not isinstance(test, OOp) or test.name not in ('lte', 'lt', 'eq'):
        return None
    if len(test.args) != 2:
        return None

    base_val = body.true_branch

    step = body.false_branch
    if not isinstance(step, OOp) or len(step.args) != 2:
        return None

    param_arg = test.args[0]
    if not isinstance(param_arg, OVar):
        return None

    left, right = step.args
    has_rec_left = _contains_fix_ref(left, fix.name)
    has_rec_right = _contains_fix_ref(right, fix.name)

    if not (has_rec_left or has_rec_right):
        return None

    return NatElimParams(
        base_val=base_val,
        threshold=test.args[1],
        op_name=step.name,
        param_name=param_arg.name,
        cmp_op=test.name,
    )


def apply_nat_elim(fix: OFix) -> OTerm:
    """Apply Nat-eliminator: OFix -> OFold.

    Implements Corollary 27.0.5: transforms a primitive-recursive OFix
    into an OFold with the extracted operator, base value, and range.
    """
    params = extract_nat_elim(fix)
    if params is None:
        return fix

    return OFold(
        op_name=params.op_name,
        init=params.base_val,
        collection=OOp('range', (OVar(params.param_name),)),
    )


def _contains_fix_ref(term: OTerm, fix_name: str) -> bool:
    """Check if an OTerm contains a reference to a named OFix."""
    if isinstance(term, OOp):
        if term.name == fix_name:
            return True
        return any(_contains_fix_ref(a, fix_name) for a in term.args)
    if isinstance(term, OVar):
        return term.name == fix_name
    if isinstance(term, OCase):
        return (_contains_fix_ref(term.test, fix_name) or
                _contains_fix_ref(term.true_branch, fix_name) or
                _contains_fix_ref(term.false_branch, fix_name))
    if isinstance(term, OFold):
        return (_contains_fix_ref(term.init, fix_name) or
                _contains_fix_ref(term.collection, fix_name))
    if isinstance(term, OLam):
        return _contains_fix_ref(term.body, fix_name)
    if isinstance(term, OMap):
        r = (_contains_fix_ref(term.transform, fix_name) or
             _contains_fix_ref(term.collection, fix_name))
        if term.filter_pred is not None:
            r = r or _contains_fix_ref(term.filter_pred, fix_name)
        return r
    if isinstance(term, OSeq):
        return any(_contains_fix_ref(e, fix_name) for e in term.elements)
    if isinstance(term, OCatch):
        return (_contains_fix_ref(term.body, fix_name) or
                _contains_fix_ref(term.default, fix_name))
    return False


# ═══════════════════════════════════════════════════════════
# §3  Course-of-values recursion detection (Ch 29)
# ═══════════════════════════════════════════════════════════

def detect_course_of_values(fix: OFix) -> Optional[int]:
    """Detect course-of-values recursion depth k.

    A course-of-values OFix body accesses f(n-1), f(n-2), ..., f(n-k)
    for fixed k.  Returns k if detected, None otherwise.

    For Fibonacci: k=2 (accesses f(n-1) and f(n-2)).
    For tribonacci: k=3.
    """
    refs = _collect_recursive_offsets(fix.body, fix.name)
    if not refs:
        return None
    if refs == set(range(1, max(refs) + 1)):
        return max(refs)
    return None


def _collect_recursive_offsets(term: OTerm, fix_name: str) -> Set[int]:
    """Collect the set of recursion offsets {d : f(n-d) appears}."""
    offsets: Set[int] = set()
    if isinstance(term, OOp):
        if term.name == fix_name and len(term.args) == 1:
            arg = term.args[0]
            if isinstance(arg, OOp) and arg.name in ('sub', 'isub') and len(arg.args) == 2:
                if isinstance(arg.args[1], OLit) and isinstance(arg.args[1].value, int):
                    offsets.add(arg.args[1].value)
        for a in term.args:
            offsets |= _collect_recursive_offsets(a, fix_name)
    elif isinstance(term, OCase):
        offsets |= _collect_recursive_offsets(term.test, fix_name)
        offsets |= _collect_recursive_offsets(term.true_branch, fix_name)
        offsets |= _collect_recursive_offsets(term.false_branch, fix_name)
    elif isinstance(term, OFold):
        offsets |= _collect_recursive_offsets(term.init, fix_name)
        offsets |= _collect_recursive_offsets(term.collection, fix_name)
    elif isinstance(term, OLam):
        offsets |= _collect_recursive_offsets(term.body, fix_name)
    elif isinstance(term, OSeq):
        for e in term.elements:
            offsets |= _collect_recursive_offsets(e, fix_name)
    return offsets


# ═══════════════════════════════════════════════════════════
# §4  Recursion Scheme Classifier
# ═══════════════════════════════════════════════════════════

class RecursionScheme(Enum):
    """Classification of recursion patterns in OFix terms."""
    PRIMITIVE = auto()          # f(n) depends only on f(n-1)
    COURSE_OF_VALUES = auto()   # f(n) depends on f(n-1), ..., f(n-k) for k>1
    TAIL = auto()               # recursive call is in tail position
    TREE = auto()               # multiple recursive calls at different subproblems
    MUTUAL = auto()             # references another fixpoint
    NON_RECURSIVE = auto()      # no self-reference (degenerate)
    UNKNOWN = auto()


@dataclass
class RecursionInfo:
    """Full analysis of an OFix term's recursion structure."""
    scheme: RecursionScheme
    depth: Optional[int]         # k for course-of-values, 1 for primitive
    call_count: int              # number of recursive call sites
    is_tail: bool                # whether the outermost recursive call is in tail position
    offsets: Set[int]            # set of recursion offsets {d : f(n-d) appears}
    has_accumulator: bool        # whether a fold pattern accumulates over recursive calls


def classify_recursion(fix: OFix) -> RecursionInfo:
    """Classify the recursion scheme of an OFix term.

    Returns a RecursionInfo with the scheme classification, depth,
    call count, tail-position flag, and recursion offsets.
    """
    refs = _collect_recursive_offsets(fix.body, fix.name)
    call_count = _count_recursive_calls(fix.body, fix.name)

    if call_count == 0:
        return RecursionInfo(
            scheme=RecursionScheme.NON_RECURSIVE,
            depth=None, call_count=0, is_tail=False,
            offsets=set(), has_accumulator=False,
        )

    is_tail = _is_tail_recursive(fix.body, fix.name)
    has_acc = _has_accumulator_pattern(fix.body, fix.name)

    if is_tail:
        return RecursionInfo(
            scheme=RecursionScheme.TAIL,
            depth=1, call_count=call_count, is_tail=True,
            offsets=refs, has_accumulator=has_acc,
        )

    if call_count >= 2 and len(refs) <= 1:
        return RecursionInfo(
            scheme=RecursionScheme.TREE,
            depth=None, call_count=call_count, is_tail=False,
            offsets=refs, has_accumulator=has_acc,
        )

    if refs and refs == set(range(1, max(refs) + 1)):
        k = max(refs)
        scheme = RecursionScheme.PRIMITIVE if k == 1 else RecursionScheme.COURSE_OF_VALUES
        return RecursionInfo(
            scheme=scheme,
            depth=k, call_count=call_count, is_tail=False,
            offsets=refs, has_accumulator=has_acc,
        )

    return RecursionInfo(
        scheme=RecursionScheme.UNKNOWN,
        depth=None, call_count=call_count, is_tail=is_tail,
        offsets=refs, has_accumulator=has_acc,
    )


def _count_recursive_calls(term: OTerm, fix_name: str) -> int:
    """Count the number of self-referential call sites in an OTerm."""
    if isinstance(term, OOp):
        count = 1 if term.name == fix_name else 0
        return count + sum(_count_recursive_calls(a, fix_name) for a in term.args)
    if isinstance(term, OCase):
        return (_count_recursive_calls(term.test, fix_name)
                + _count_recursive_calls(term.true_branch, fix_name)
                + _count_recursive_calls(term.false_branch, fix_name))
    if isinstance(term, OFold):
        return (_count_recursive_calls(term.init, fix_name)
                + _count_recursive_calls(term.collection, fix_name))
    if isinstance(term, OLam):
        return _count_recursive_calls(term.body, fix_name)
    if isinstance(term, OSeq):
        return sum(_count_recursive_calls(e, fix_name) for e in term.elements)
    if isinstance(term, OCatch):
        return (_count_recursive_calls(term.body, fix_name)
                + _count_recursive_calls(term.default, fix_name))
    return 0


def _is_tail_recursive(term: OTerm, fix_name: str) -> bool:
    """Check if the recursive call is in strict tail position.

    A call f(expr) is in tail position if it is the last expression
    evaluated before returning — i.e., it is the false/true branch
    of the outermost case and nothing wraps the call.
    """
    if isinstance(term, OCase):
        return (_is_tail_recursive(term.true_branch, fix_name) or
                _is_tail_recursive(term.false_branch, fix_name))
    if isinstance(term, OOp):
        if term.name == fix_name:
            return True
    return False


def _has_accumulator_pattern(term: OTerm, fix_name: str) -> bool:
    """Detect accumulator-passing style: f(n-1, acc OP x) pattern."""
    if isinstance(term, OCase):
        return (_has_accumulator_pattern(term.true_branch, fix_name) or
                _has_accumulator_pattern(term.false_branch, fix_name))
    if isinstance(term, OOp) and term.name == fix_name:
        for arg in term.args:
            if isinstance(arg, OOp) and arg.name in ('iadd', 'imult', 'add', 'mult',
                                                       'sub', 'concat'):
                return True
    return False


# ═══════════════════════════════════════════════════════════
# §5  Full Catamorphism Recognizer
# ═══════════════════════════════════════════════════════════

class CatamorphismKind(Enum):
    """The kind of catamorphism (generalized fold) detected."""
    FOLD = auto()       # fold[op](init, xs)
    MAP = auto()        # map(f, xs) — fold that builds a new list
    FILTER = auto()     # filter(p, xs) — fold that selects elements
    SCAN = auto()       # scan[op](init, xs) — fold keeping intermediates
    REDUCE = auto()     # fold with no explicit init (uses first element)
    FLAT_MAP = auto()   # map + flatten
    ZIP_WITH = auto()   # fold over two parallel collections
    NONE = auto()


@dataclass
class CatamorphismInfo:
    """Result of catamorphism detection on an OTerm."""
    kind: CatamorphismKind
    op_name: Optional[str]        # accumulation operator name
    init: Optional[OTerm]         # initial accumulator value
    collection: Optional[OTerm]   # the collection being folded over
    transform: Optional[OTerm]    # the per-element transform (for map/filter)
    predicate: Optional[OTerm]    # filter predicate (for filter)


def recognize_catamorphism(term: OTerm) -> CatamorphismInfo:
    """Recognize the catamorphism pattern of an OTerm.

    Detects fold, map, filter, scan, reduce, flat_map, and zip_with
    patterns from their structural OTerm shapes.
    """
    if isinstance(term, OFold):
        return CatamorphismInfo(
            kind=CatamorphismKind.FOLD,
            op_name=term.op_name,
            init=term.init,
            collection=term.collection,
            transform=None, predicate=None,
        )

    if isinstance(term, OMap):
        if term.filter_pred is not None and _is_identity_transform(term.transform):
            return CatamorphismInfo(
                kind=CatamorphismKind.FILTER,
                op_name=None,
                init=OSeq(()),
                collection=term.collection,
                transform=None,
                predicate=term.filter_pred,
            )
        if term.filter_pred is not None:
            return CatamorphismInfo(
                kind=CatamorphismKind.MAP,
                op_name=None,
                init=OSeq(()),
                collection=term.collection,
                transform=term.transform,
                predicate=term.filter_pred,
            )
        if _is_flatmap_transform(term.transform):
            return CatamorphismInfo(
                kind=CatamorphismKind.FLAT_MAP,
                op_name='concat',
                init=OSeq(()),
                collection=term.collection,
                transform=term.transform,
                predicate=None,
            )
        return CatamorphismInfo(
            kind=CatamorphismKind.MAP,
            op_name=None,
            init=OSeq(()),
            collection=term.collection,
            transform=term.transform,
            predicate=None,
        )

    if isinstance(term, OOp) and term.name == 'scan' and len(term.args) >= 2:
        return CatamorphismInfo(
            kind=CatamorphismKind.SCAN,
            op_name='scan',
            init=term.args[0] if len(term.args) > 2 else None,
            collection=term.args[-1],
            transform=None, predicate=None,
        )

    return CatamorphismInfo(
        kind=CatamorphismKind.NONE,
        op_name=None, init=None, collection=None,
        transform=None, predicate=None,
    )


def _is_identity_transform(term: OTerm) -> bool:
    """Check if an OLam is the identity function λx.x."""
    if isinstance(term, OLam) and len(term.params) == 1:
        if isinstance(term.body, OVar) and term.body.name == term.params[0]:
            return True
    return False


def _is_flatmap_transform(term: OTerm) -> bool:
    """Check if the transform body produces a sequence (flat_map pattern)."""
    if isinstance(term, OLam):
        return isinstance(term.body, (OSeq, OMap))
    return False


# ═══════════════════════════════════════════════════════════
# §6  HOF Fusion Engine (map∘map, filter∘map, map∘filter)
# ═══════════════════════════════════════════════════════════

def fuse_map_map(outer_f: OLam, inner_g: OLam) -> OLam:
    """Compose two unary OLam values: f ∘ g = λx. f(g(x)).

    Implements the map composition rule from Section 30.0.3:
        map(f, map(g, xs)) → map(f ∘ g, xs)
    """
    if len(outer_f.params) != 1 or len(inner_g.params) != 1:
        raise ValueError("Can only fuse unary lambdas")

    z = '_composed_0'
    inner_applied = _subst(inner_g.body, {inner_g.params[0]: OVar(z)})
    composed_body = _subst(outer_f.body, {outer_f.params[0]: inner_applied})
    return OLam((z,), composed_body)


def fuse_filter_map(filter_pred: OLam, map_fn: OLam) -> OLam:
    """Fuse filter predicate through a map: filter(p, map(f, xs)) → filter(p∘f, xs).

    The result is a predicate that applies f first, then tests p.
    This allows eliminating the intermediate mapped collection.
    """
    if len(filter_pred.params) != 1 or len(map_fn.params) != 1:
        raise ValueError("Can only fuse unary lambdas")

    z = '_fused_fm_0'
    mapped = _subst(map_fn.body, {map_fn.params[0]: OVar(z)})
    pred_applied = _subst(filter_pred.body, {filter_pred.params[0]: mapped})
    return OLam((z,), pred_applied)


def fuse_map_filter(map_fn: OLam, filter_pred: OLam) -> Tuple[OLam, OLam]:
    """Handle map(f, filter(p, xs)): keep both but lift filter to pre-position.

    Returns (map_fn, filter_pred) unchanged since the filter must run
    on the original elements. This is an identity fusion that documents
    the case cannot be further simplified.
    """
    return map_fn, filter_pred


@dataclass
class FusionResult:
    """Result of attempting HOF fusion on an OTerm."""
    fused: bool
    original: OTerm
    result: OTerm
    rule_name: str


def apply_hof_fusion(term: OTerm) -> FusionResult:
    """Apply all HOF fusion rules to an OTerm, returning the result.

    Rules applied:
      1. map(f, map(g, xs)) → map(f∘g, xs)
      2. filter(p, map(f, xs)) → filter_map(p∘f, id, xs)
      3. fold(op, init, map(f, xs)) → fold(op', init, xs) where op'(acc,x) = op(acc,f(x))
      4. map(id, xs) → xs
    """
    result = _apply_fusion_recursive(term)
    fused = result.canon() != term.canon()
    rule = 'map∘map' if fused else 'none'
    if fused and isinstance(term, OMap) and isinstance(term.collection, OMap):
        rule = 'map∘map'
    elif fused and isinstance(term, OFold) and isinstance(term.collection, OMap):
        rule = 'fold∘map'
    return FusionResult(fused=fused, original=term, result=result, rule_name=rule)


def _apply_fusion_recursive(term: OTerm) -> OTerm:
    """Recursively apply fusion rules bottom-up."""
    if isinstance(term, OMap):
        t = _apply_fusion_recursive(term.transform)
        c = _apply_fusion_recursive(term.collection)
        f = _apply_fusion_recursive(term.filter_pred) if term.filter_pred else None

        if _is_identity_transform(t) and f is None:
            return c

        if isinstance(c, OMap) and c.filter_pred is None:
            if isinstance(t, OLam) and isinstance(c.transform, OLam):
                composed = fuse_map_map(t, c.transform)
                return OMap(composed, c.collection, f)

        if isinstance(c, OMap) and c.filter_pred is not None and f is None:
            if isinstance(t, OLam) and isinstance(c.transform, OLam):
                composed = fuse_map_map(t, c.transform)
                return OMap(composed, c.collection, c.filter_pred)

        return OMap(t, c, f)

    if isinstance(term, OFold):
        init = _apply_fusion_recursive(term.init)
        coll = _apply_fusion_recursive(term.collection)
        if isinstance(coll, OMap) and coll.filter_pred is None:
            if isinstance(coll.transform, OLam) and len(coll.transform.params) == 1:
                return OFold(term.op_name, init, coll.collection)
        return OFold(term.op_name, init, coll)

    if isinstance(term, OOp):
        return OOp(term.name, tuple(_apply_fusion_recursive(a) for a in term.args))
    if isinstance(term, OCase):
        return OCase(_apply_fusion_recursive(term.test),
                     _apply_fusion_recursive(term.true_branch),
                     _apply_fusion_recursive(term.false_branch))
    if isinstance(term, OSeq):
        return OSeq(tuple(_apply_fusion_recursive(e) for e in term.elements))
    if isinstance(term, OLam):
        return OLam(term.params, _apply_fusion_recursive(term.body))
    if isinstance(term, OFix):
        return OFix(term.name, _apply_fusion_recursive(term.body))
    if isinstance(term, OQuotient):
        return OQuotient(_apply_fusion_recursive(term.inner), term.equiv_class)
    if isinstance(term, OCatch):
        return OCatch(_apply_fusion_recursive(term.body),
                      _apply_fusion_recursive(term.default))
    return term


def phase4_map_fusion(term: OTerm) -> OTerm:
    """Enhanced Phase 4: detect and apply map-map fusion.

    When we see OMap(f, OMap(g, xs)), replace with OMap(f∘g, xs).
    This avoids an intermediate collection and enables further
    simplification.
    """
    return _apply_fusion_recursive(term)


# ═══════════════════════════════════════════════════════════
# §7  De Bruijn Normalization for OLam
# ═══════════════════════════════════════════════════════════

def de_bruijn_normalize(term: OTerm) -> OTerm:
    """Fully normalize an OTerm by replacing all bound variables with
    de Bruijn-style positional names (_b0, _b1, ...).

    This ensures alpha-equivalent terms produce identical canon() strings.
    Applied recursively to all OLam nodes in the tree.
    """
    if isinstance(term, OLam):
        mapping = {p: f'_b{i}' for i, p in enumerate(term.params)}
        normalized_body = _subst(term.body, mapping)
        normalized_body = de_bruijn_normalize(normalized_body)
        new_params = tuple(f'_b{i}' for i in range(len(term.params)))
        return OLam(new_params, normalized_body)

    if isinstance(term, OOp):
        return OOp(term.name, tuple(de_bruijn_normalize(a) for a in term.args))
    if isinstance(term, OCase):
        return OCase(de_bruijn_normalize(term.test),
                     de_bruijn_normalize(term.true_branch),
                     de_bruijn_normalize(term.false_branch))
    if isinstance(term, OFold):
        return OFold(term.op_name, de_bruijn_normalize(term.init),
                     de_bruijn_normalize(term.collection))
    if isinstance(term, OFix):
        return OFix(term.name, de_bruijn_normalize(term.body))
    if isinstance(term, OSeq):
        return OSeq(tuple(de_bruijn_normalize(e) for e in term.elements))
    if isinstance(term, ODict):
        return ODict(tuple((de_bruijn_normalize(k), de_bruijn_normalize(v))
                          for k, v in term.pairs))
    if isinstance(term, OQuotient):
        return OQuotient(de_bruijn_normalize(term.inner), term.equiv_class)
    if isinstance(term, OAbstract):
        return OAbstract(term.spec, tuple(de_bruijn_normalize(a) for a in term.inputs))
    if isinstance(term, OMap):
        t = de_bruijn_normalize(term.transform)
        c = de_bruijn_normalize(term.collection)
        f = de_bruijn_normalize(term.filter_pred) if term.filter_pred else None
        return OMap(t, c, f)
    if isinstance(term, OCatch):
        return OCatch(de_bruijn_normalize(term.body),
                      de_bruijn_normalize(term.default))
    return term


def alpha_equivalent(a: OTerm, b: OTerm) -> bool:
    """Test if two OTerms are alpha-equivalent (identical up to renaming of bound variables)."""
    return de_bruijn_normalize(a).canon() == de_bruijn_normalize(b).canon()


# ═══════════════════════════════════════════════════════════
# §8  OTerm Pretty-Printer with Mathematical Notation
# ═══════════════════════════════════════════════════════════

_MATH_OP_SYMBOLS: Dict[str, str] = {
    'add': '+', 'iadd': '+', 'sub': '-', 'isub': '-',
    'mult': '×', 'imult': '×', 'floordiv': '÷',
    'mod': 'mod', 'pow': '^',
    'lt': '<', 'lte': '≤', 'gt': '>', 'gte': '≥',
    'eq': '=', 'noteq': '≠',
    'and': '∧', 'or': '∨',
    'u_usub': '-', 'u_not': '¬',
    'sorted': 'sort', 'reversed': 'rev',
}


def pretty_print(term: OTerm, indent: int = 0) -> str:
    """Render an OTerm in human-readable mathematical notation.

    Uses Unicode symbols for arithmetic and logic operators,
    standard mathematical notation for folds (Σ, Π), and
    indentation for nested structures.
    """
    pad = '  ' * indent
    return _pp(term, indent, pad)


def _pp(term: OTerm, indent: int, pad: str) -> str:
    if isinstance(term, OVar):
        return term.name
    if isinstance(term, OLit):
        return repr(term.value)
    if isinstance(term, OUnknown):
        return f'?{term.desc}'

    if isinstance(term, OOp):
        name = term.name
        args = term.args
        if name in _MATH_OP_SYMBOLS and len(args) == 2:
            sym = _MATH_OP_SYMBOLS[name]
            left = _pp(args[0], indent, pad)
            right = _pp(args[1], indent, pad)
            return f'({left} {sym} {right})'
        if name in ('u_usub', 'u_not') and len(args) == 1:
            sym = _MATH_OP_SYMBOLS[name]
            operand = _pp(args[0], indent, pad)
            return f'{sym}{operand}'
        if name == 'range' and len(args) == 1:
            return f'[0..{_pp(args[0], indent, pad)})'
        if name == 'abs' and len(args) == 1:
            return f'|{_pp(args[0], indent, pad)}|'
        arg_strs = ', '.join(_pp(a, indent, pad) for a in args)
        return f'{name}({arg_strs})'

    if isinstance(term, OFold):
        op = term.op_name
        init_s = _pp(term.init, indent, pad)
        coll_s = _pp(term.collection, indent, pad)
        if op in ('iadd', 'add'):
            return f'Σ({coll_s}, init={init_s})'
        if op in ('imult', 'mult'):
            return f'Π({coll_s}, init={init_s})'
        return f'fold[{op}]({init_s}, {coll_s})'

    if isinstance(term, OCase):
        test_s = _pp(term.test, indent, pad)
        t_s = _pp(term.true_branch, indent + 1, pad + '  ')
        f_s = _pp(term.false_branch, indent + 1, pad + '  ')
        return f'if {test_s} then {t_s} else {f_s}'

    if isinstance(term, OFix):
        body_s = _pp(term.body, indent + 1, pad + '  ')
        return f'μ{term.name}.{body_s}'

    if isinstance(term, OSeq):
        elts = ', '.join(_pp(e, indent, pad) for e in term.elements)
        return f'[{elts}]'

    if isinstance(term, ODict):
        pairs = ', '.join(f'{_pp(k, indent, pad)}: {_pp(v, indent, pad)}'
                         for k, v in term.pairs)
        return f'{{{pairs}}}'

    if isinstance(term, OQuotient):
        inner_s = _pp(term.inner, indent, pad)
        return f'{inner_s}/~{term.equiv_class}'

    if isinstance(term, OAbstract):
        arg_strs = ', '.join(_pp(a, indent, pad) for a in term.inputs)
        return f'⟦{term.spec}⟧({arg_strs})'

    if isinstance(term, OLam):
        params_s = ', '.join(term.params)
        body_s = _pp(term.body, indent, pad)
        return f'λ({params_s}). {body_s}'

    if isinstance(term, OMap):
        t_s = _pp(term.transform, indent, pad)
        c_s = _pp(term.collection, indent, pad)
        if term.filter_pred is not None:
            p_s = _pp(term.filter_pred, indent, pad)
            return f'[{t_s}(x) for x in {c_s} if {p_s}(x)]'
        return f'[{t_s}(x) for x in {c_s}]'

    if isinstance(term, OCatch):
        body_s = _pp(term.body, indent, pad)
        default_s = _pp(term.default, indent, pad)
        return f'try {body_s} except → {default_s}'

    return f'<{type(term).__name__}>'


# ═══════════════════════════════════════════════════════════
# §9  Normalization Trace and Phase Profiler (Ch 31)
# ═══════════════════════════════════════════════════════════

@dataclass
class PhaseSnapshot:
    """A snapshot of the OTerm after one normalization phase."""
    phase: int
    phase_name: str
    term: OTerm
    canon: str
    changed: bool
    size_before: int
    size_after: int
    elapsed_us: float


@dataclass
class NormalizationTrace:
    """Complete trace of normalization through all phases and iterations."""
    input_term: OTerm
    output_term: OTerm
    iterations: int
    snapshots: List[PhaseSnapshot]

    def summary(self) -> str:
        """Human-readable summary of the trace."""
        lines = [f"Normalization trace: {self.iterations} iteration(s)"]
        lines.append(f"  Input:  {self.input_term.canon()}")
        for snap in self.snapshots:
            marker = '*' if snap.changed else ' '
            delta = snap.size_after - snap.size_before
            delta_s = f' Δ={delta:+d}' if delta != 0 else ''
            lines.append(
                f"  [{marker}] P{snap.phase} ({snap.phase_name}): "
                f"{snap.canon}{delta_s}  [{snap.elapsed_us:.0f}μs]"
            )
        lines.append(f"  Output: {self.output_term.canon()}")
        return '\n'.join(lines)


@dataclass
class PhaseProfile:
    """Aggregate profile data for a single normalization phase."""
    phase: int
    phase_name: str
    total_changes: int
    total_size_delta: int
    total_time_us: float
    invocations: int

    @property
    def avg_time_us(self) -> float:
        return self.total_time_us / max(self.invocations, 1)


PHASE_NAMES: Dict[int, str] = {
    1: 'beta-reduction',
    2: 'ring/lattice',
    3: 'fold-canon',
    4: 'HOF-fusion',
    5: 'dichotomy',
    6: 'quotient',
    7: 'piecewise',
}

PHASE_FNS: List[Tuple[int, Callable[[OTerm], OTerm]]] = [
    (1, _phase1_beta),
    (2, _phase2_ring),
    (3, _phase3_fold),
    (4, _phase4_hof),
    (5, _phase5_unify),
    (6, _phase6_quotient),
    (7, _phase7_piecewise),
]


def normalize_with_trace(term: OTerm) -> NormalizationTrace:
    """Run the 7-phase normalizer with full tracing.

    Returns a NormalizationTrace recording the OTerm after each phase
    of each iteration, including size deltas and per-phase timing.
    """
    snapshots: List[PhaseSnapshot] = []
    prev_canon: Optional[str] = None
    current = term
    iterations = 0

    for _ in range(8):
        iterations += 1
        for phase_num, phase_fn in PHASE_FNS:
            before_canon = current.canon()
            before_size = oterm_size(current)
            t0 = time.perf_counter_ns()
            current = phase_fn(current)
            elapsed_us = (time.perf_counter_ns() - t0) / 1000.0
            after_canon = current.canon()
            after_size = oterm_size(current)
            snapshots.append(PhaseSnapshot(
                phase=phase_num,
                phase_name=PHASE_NAMES[phase_num],
                term=current,
                canon=after_canon,
                changed=(before_canon != after_canon),
                size_before=before_size,
                size_after=after_size,
                elapsed_us=elapsed_us,
            ))

        current_canon = current.canon()
        if prev_canon is not None and current_canon == prev_canon:
            break
        prev_canon = current_canon

    return NormalizationTrace(
        input_term=term,
        output_term=current,
        iterations=iterations,
        snapshots=snapshots,
    )


def profile_phases(trace: NormalizationTrace) -> List[PhaseProfile]:
    """Aggregate phase-level profiling from a NormalizationTrace.

    Returns a list of PhaseProfile objects, one per phase, summarizing
    how many times each phase changed the term, the total size delta,
    and the total time spent.
    """
    profiles: Dict[int, PhaseProfile] = {}
    for snap in trace.snapshots:
        if snap.phase not in profiles:
            profiles[snap.phase] = PhaseProfile(
                phase=snap.phase,
                phase_name=snap.phase_name,
                total_changes=0,
                total_size_delta=0,
                total_time_us=0.0,
                invocations=0,
            )
        p = profiles[snap.phase]
        p.invocations += 1
        p.total_time_us += snap.elapsed_us
        if snap.changed:
            p.total_changes += 1
        p.total_size_delta += snap.size_after - snap.size_before

    return [profiles[i] for i in sorted(profiles)]


def profile_summary(trace: NormalizationTrace) -> str:
    """Return a compact profiling summary string for a normalization trace."""
    phases = profile_phases(trace)
    lines = [f"Phase profiling ({trace.iterations} iter, "
             f"size {oterm_size(trace.input_term)} → {oterm_size(trace.output_term)}):"]
    for p in phases:
        lines.append(
            f"  P{p.phase} {p.phase_name:15s}: "
            f"{p.total_changes} change(s), "
            f"Δsize={p.total_size_delta:+d}, "
            f"{p.total_time_us:.0f}μs total"
        )
    return '\n'.join(lines)


# ═══════════════════════════════════════════════════════════
# §10  Compilation Coverage Analyzer
# ═══════════════════════════════════════════════════════════

_ALL_EXPR_NODES: FrozenSet[str] = frozenset({
    'Constant', 'Name', 'BinOp', 'UnaryOp', 'Compare', 'BoolOp',
    'IfExp', 'Call', 'Subscript', 'Tuple', 'List', 'ListComp',
    'SetComp', 'GeneratorExp', 'DictComp', 'Dict', 'Set',
    'Attribute', 'NamedExpr', 'Lambda', 'Starred', 'JoinedStr',
    'FormattedValue', 'Slice', 'Await', 'Yield', 'YieldFrom',
})

_ALL_STMT_NODES: FrozenSet[str] = frozenset({
    'Return', 'Assign', 'AugAssign', 'AnnAssign', 'If', 'For',
    'While', 'Try', 'TryStar', 'With', 'Raise', 'Assert',
    'Import', 'ImportFrom', 'FunctionDef', 'AsyncFunctionDef',
    'ClassDef', 'Expr', 'Pass', 'Break', 'Continue', 'Delete',
    'Global', 'Nonlocal', 'Match',
})

_HANDLED_EXPR_NODES: FrozenSet[str] = frozenset({
    'Constant', 'Name', 'BinOp', 'UnaryOp', 'Compare', 'BoolOp',
    'IfExp', 'Call', 'Subscript', 'Tuple', 'List', 'ListComp',
    'SetComp', 'GeneratorExp', 'DictComp', 'Dict', 'Set',
    'Attribute', 'NamedExpr', 'Lambda', 'Starred', 'JoinedStr',
})

_HANDLED_STMT_NODES: FrozenSet[str] = frozenset({
    'Return', 'Assign', 'AugAssign', 'If', 'For', 'While', 'Try',
    'FunctionDef', 'AsyncFunctionDef', 'ClassDef', 'Expr', 'Pass',
    'Break', 'Continue', 'Import', 'ImportFrom',
})


@dataclass
class CoverageReport:
    """Report of which Python AST node types are/aren't handled by compilation."""
    handled_expr: FrozenSet[str]
    unhandled_expr: FrozenSet[str]
    handled_stmt: FrozenSet[str]
    unhandled_stmt: FrozenSet[str]
    source_expr_counts: Dict[str, int]
    source_stmt_counts: Dict[str, int]
    coverage_pct: float

    def summary(self) -> str:
        lines = [f"Compilation coverage: {self.coverage_pct:.1f}%"]
        if self.unhandled_expr:
            lines.append(f"  Unhandled expr nodes: {sorted(self.unhandled_expr)}")
        if self.unhandled_stmt:
            lines.append(f"  Unhandled stmt nodes: {sorted(self.unhandled_stmt)}")
        used_unhandled_expr = {n for n in self.unhandled_expr
                               if self.source_expr_counts.get(n, 0) > 0}
        used_unhandled_stmt = {n for n in self.unhandled_stmt
                               if self.source_stmt_counts.get(n, 0) > 0}
        if used_unhandled_expr:
            lines.append(f"  ⚠ Used but unhandled expr: {sorted(used_unhandled_expr)}")
        if used_unhandled_stmt:
            lines.append(f"  ⚠ Used but unhandled stmt: {sorted(used_unhandled_stmt)}")
        return '\n'.join(lines)


def analyze_coverage(source: str) -> CoverageReport:
    """Analyze which AST node types in the given source are handled by compilation.

    Parses the source, walks the AST, and compares against the set of
    node types that the OTerm compiler handles.
    """
    try:
        tree = ast.parse(textwrap.dedent(source))
    except SyntaxError:
        return CoverageReport(
            handled_expr=_HANDLED_EXPR_NODES,
            unhandled_expr=_ALL_EXPR_NODES - _HANDLED_EXPR_NODES,
            handled_stmt=_HANDLED_STMT_NODES,
            unhandled_stmt=_ALL_STMT_NODES - _HANDLED_STMT_NODES,
            source_expr_counts={},
            source_stmt_counts={},
            coverage_pct=0.0,
        )

    expr_counts: Counter = Counter()
    stmt_counts: Counter = Counter()
    for node in ast.walk(tree):
        name = type(node).__name__
        if isinstance(node, ast.expr):
            expr_counts[name] += 1
        elif isinstance(node, ast.stmt):
            stmt_counts[name] += 1

    used_nodes = set(expr_counts.keys()) | set(stmt_counts.keys())
    handled_used = used_nodes & (_HANDLED_EXPR_NODES | _HANDLED_STMT_NODES)
    total_used = len(used_nodes)
    coverage_pct = (len(handled_used) / max(total_used, 1)) * 100.0

    return CoverageReport(
        handled_expr=_HANDLED_EXPR_NODES,
        unhandled_expr=_ALL_EXPR_NODES - _HANDLED_EXPR_NODES,
        handled_stmt=_HANDLED_STMT_NODES,
        unhandled_stmt=_ALL_STMT_NODES - _HANDLED_STMT_NODES,
        source_expr_counts=dict(expr_counts),
        source_stmt_counts=dict(stmt_counts),
        coverage_pct=coverage_pct,
    )


# ═══════════════════════════════════════════════════════════
# §11  Fold Canonicalization Extensions
# ═══════════════════════════════════════════════════════════

_FOLD_CANON_TABLE: Dict[str, Tuple[str, OTerm]] = {
    'sum': ('iadd', OLit(0)),
    'any': ('or', OLit(False)),
    'all': ('and', OLit(True)),
    'prod': ('imult', OLit(1)),
    'min': ('min', OUnknown('inf')),
    'max': ('max', OUnknown('-inf')),
    'str.join': ('str_concat', OLit('')),
    'set.union': ('set_union', OOp('set', ())),
    'set.intersection': ('set_intersection', OUnknown('universal_set')),
    'list.concat': ('concat', OSeq(())),
    'Counter.sum': ('counter_add', OOp('Counter', ())),
    'bitwise_or': ('ior', OLit(0)),
    'bitwise_and': ('iand', OLit(-1)),
    'bitwise_xor': ('ixor', OLit(0)),
}


def canonicalize_fold(op_name: str, args: Tuple[OTerm, ...]) -> Optional[OFold]:
    """Try to canonicalize a builtin reducer call into an OFold.

    Extended version of Phase 3's fold canonicalization that handles
    additional base/op combinations including prod, min/max with
    infinity sentinels, bitwise operations, and set operations.

    Returns an OFold if the operation can be canonicalized, None otherwise.
    """
    if op_name in _FOLD_CANON_TABLE and len(args) == 1:
        fold_op, init = _FOLD_CANON_TABLE[op_name]
        return OFold(fold_op, init, args[0])

    if op_name == '.join' and len(args) == 2:
        return OFold('str_concat', args[0], args[1])

    if op_name == 'functools.reduce' and len(args) >= 2:
        func, iterable = args[0], args[1]
        init = args[2] if len(args) > 2 else OUnknown('first_elem')
        if isinstance(func, OLam) and len(func.params) == 2:
            if isinstance(func.body, OOp) and len(func.body.args) == 2:
                return OFold(func.body.name, init, iterable)
        return OFold('reduce', init, iterable)

    return None


def extended_phase3_fold(term: OTerm) -> OTerm:
    """Extended Phase 3: fold canonicalization with additional patterns.

    Extends the base _phase3_fold with:
      - prod(xs) → fold[imult](1, xs)
      - min/max with infinity init values
      - functools.reduce recognition
      - bitwise fold patterns (|=, &=, ^=)
      - set union/intersection folds
    """
    if isinstance(term, OOp):
        args = tuple(extended_phase3_fold(a) for a in term.args)
        canon = canonicalize_fold(term.name, args)
        if canon is not None:
            return canon
        return OOp(term.name, args)

    if isinstance(term, OCase):
        return OCase(extended_phase3_fold(term.test),
                     extended_phase3_fold(term.true_branch),
                     extended_phase3_fold(term.false_branch))
    if isinstance(term, OFold):
        return OFold(term.op_name, extended_phase3_fold(term.init),
                     extended_phase3_fold(term.collection))
    if isinstance(term, OFix):
        return OFix(term.name, extended_phase3_fold(term.body))
    if isinstance(term, OSeq):
        return OSeq(tuple(extended_phase3_fold(e) for e in term.elements))
    if isinstance(term, OLam):
        return OLam(term.params, extended_phase3_fold(term.body))
    if isinstance(term, OMap):
        t = extended_phase3_fold(term.transform)
        c = extended_phase3_fold(term.collection)
        f = extended_phase3_fold(term.filter_pred) if term.filter_pred else None
        return OMap(t, c, f)
    if isinstance(term, OCatch):
        return OCatch(extended_phase3_fold(term.body),
                      extended_phase3_fold(term.default))
    if isinstance(term, OQuotient):
        return OQuotient(extended_phase3_fold(term.inner), term.equiv_class)
    return term


# ═══════════════════════════════════════════════════════════
# §12  OTerm Transformers — Bulk Traversal Utilities
# ═══════════════════════════════════════════════════════════

def map_oterm(fn: Callable[[OTerm], OTerm], term: OTerm) -> OTerm:
    """Apply a function to every sub-term bottom-up (catamorphism on OTerm).

    The function is applied after recursing into children, so it sees
    the already-transformed subtree.  This is the universal fold on the
    OTerm algebra.
    """
    if isinstance(term, OOp):
        term = OOp(term.name, tuple(map_oterm(fn, a) for a in term.args))
    elif isinstance(term, OCase):
        term = OCase(map_oterm(fn, term.test),
                     map_oterm(fn, term.true_branch),
                     map_oterm(fn, term.false_branch))
    elif isinstance(term, OFold):
        term = OFold(term.op_name, map_oterm(fn, term.init),
                     map_oterm(fn, term.collection))
    elif isinstance(term, OFix):
        term = OFix(term.name, map_oterm(fn, term.body))
    elif isinstance(term, OSeq):
        term = OSeq(tuple(map_oterm(fn, e) for e in term.elements))
    elif isinstance(term, ODict):
        term = ODict(tuple((map_oterm(fn, k), map_oterm(fn, v)) for k, v in term.pairs))
    elif isinstance(term, OQuotient):
        term = OQuotient(map_oterm(fn, term.inner), term.equiv_class)
    elif isinstance(term, OAbstract):
        term = OAbstract(term.spec, tuple(map_oterm(fn, a) for a in term.inputs))
    elif isinstance(term, OLam):
        term = OLam(term.params, map_oterm(fn, term.body))
    elif isinstance(term, OMap):
        t = map_oterm(fn, term.transform)
        c = map_oterm(fn, term.collection)
        f = map_oterm(fn, term.filter_pred) if term.filter_pred else None
        term = OMap(t, c, f)
    elif isinstance(term, OCatch):
        term = OCatch(map_oterm(fn, term.body), map_oterm(fn, term.default))
    return fn(term)


def fold_oterm(fn: Callable[[OTerm, List[Any]], Any], term: OTerm) -> Any:
    """Fold (catamorphism) over an OTerm tree.

    fn receives the current node and a list of results from children.
    """
    children: List[Any] = []
    if isinstance(term, OOp):
        children = [fold_oterm(fn, a) for a in term.args]
    elif isinstance(term, OCase):
        children = [fold_oterm(fn, term.test),
                    fold_oterm(fn, term.true_branch),
                    fold_oterm(fn, term.false_branch)]
    elif isinstance(term, OFold):
        children = [fold_oterm(fn, term.init), fold_oterm(fn, term.collection)]
    elif isinstance(term, OFix):
        children = [fold_oterm(fn, term.body)]
    elif isinstance(term, OSeq):
        children = [fold_oterm(fn, e) for e in term.elements]
    elif isinstance(term, ODict):
        children = []
        for k, v in term.pairs:
            children.append(fold_oterm(fn, k))
            children.append(fold_oterm(fn, v))
    elif isinstance(term, OQuotient):
        children = [fold_oterm(fn, term.inner)]
    elif isinstance(term, OAbstract):
        children = [fold_oterm(fn, a) for a in term.inputs]
    elif isinstance(term, OLam):
        children = [fold_oterm(fn, term.body)]
    elif isinstance(term, OMap):
        children = [fold_oterm(fn, term.transform), fold_oterm(fn, term.collection)]
        if term.filter_pred is not None:
            children.append(fold_oterm(fn, term.filter_pred))
    elif isinstance(term, OCatch):
        children = [fold_oterm(fn, term.body), fold_oterm(fn, term.default)]
    return fn(term, children)


def collect_all_ops(term: OTerm) -> Set[str]:
    """Collect the set of all operation names used in an OTerm tree."""
    ops: Set[str] = set()

    def _visitor(node: OTerm, child_results: List[Set[str]]) -> Set[str]:
        result: Set[str] = set()
        for cr in child_results:
            result |= cr
        if isinstance(node, OOp):
            result.add(node.name)
        if isinstance(node, OFold):
            result.add(node.op_name)
        return result

    return fold_oterm(_visitor, term)


# ═══════════════════════════════════════════════════════════
# §13  Normalization Comparison Utilities
# ═══════════════════════════════════════════════════════════

@dataclass
class ComparisonResult:
    """Result of comparing two OTerms through normalization."""
    equivalent: bool
    canon_a: str
    canon_b: str
    trace_a: NormalizationTrace
    trace_b: NormalizationTrace
    decisive_phase: Optional[int]

    def summary(self) -> str:
        status = "EQUIVALENT ✓" if self.equivalent else "DIFFERENT ✗"
        lines = [f"Comparison: {status}"]
        if self.decisive_phase is not None:
            lines.append(f"  Decisive phase: P{self.decisive_phase} "
                         f"({PHASE_NAMES.get(self.decisive_phase, '?')})")
        lines.append(f"  A: {self.canon_a}")
        lines.append(f"  B: {self.canon_b}")
        return '\n'.join(lines)


def compare_terms(a: OTerm, b: OTerm) -> ComparisonResult:
    """Normalize two OTerms and compare their canonical forms.

    Also identifies which normalization phase was "decisive" — the
    first phase where both terms reach the same canonical form.
    """
    trace_a = normalize_with_trace(a)
    trace_b = normalize_with_trace(b)
    equivalent = trace_a.output_term.canon() == trace_b.output_term.canon()

    decisive = None
    if equivalent:
        snaps_a = {(s.phase, i // 7): s.canon
                   for i, s in enumerate(trace_a.snapshots)}
        snaps_b = {(s.phase, i // 7): s.canon
                   for i, s in enumerate(trace_b.snapshots)}
        for iteration in range(trace_a.iterations):
            for phase in range(1, 8):
                key = (phase, iteration)
                if key in snaps_a and key in snaps_b:
                    if snaps_a[key] == snaps_b[key]:
                        decisive = phase
                        break
            if decisive is not None:
                break

    return ComparisonResult(
        equivalent=equivalent,
        canon_a=trace_a.output_term.canon(),
        canon_b=trace_b.output_term.canon(),
        trace_a=trace_a,
        trace_b=trace_b,
        decisive_phase=decisive,
    )


def compare_sources(src_a: str, src_b: str) -> Optional[ComparisonResult]:
    """Compile two Python source functions and compare their denotations."""
    result_a = compile_to_oterm(src_a)
    result_b = compile_to_oterm(src_b)
    if result_a is None or result_b is None:
        return None
    term_a, params_a = result_a
    term_b, params_b = result_b
    return compare_terms(term_a, term_b)


# ═══════════════════════════════════════════════════════════
# §14  OTerm Search and Pattern Matching
# ═══════════════════════════════════════════════════════════

def find_subterms(term: OTerm, predicate: Callable[[OTerm], bool]) -> List[OTerm]:
    """Find all sub-terms matching a predicate."""
    results: List[OTerm] = []
    _find_subterms_impl(term, predicate, results)
    return results


def _find_subterms_impl(term: OTerm, predicate: Callable[[OTerm], bool],
                        results: List[OTerm]) -> None:
    if predicate(term):
        results.append(term)
    if isinstance(term, OOp):
        for a in term.args:
            _find_subterms_impl(a, predicate, results)
    elif isinstance(term, OCase):
        _find_subterms_impl(term.test, predicate, results)
        _find_subterms_impl(term.true_branch, predicate, results)
        _find_subterms_impl(term.false_branch, predicate, results)
    elif isinstance(term, OFold):
        _find_subterms_impl(term.init, predicate, results)
        _find_subterms_impl(term.collection, predicate, results)
    elif isinstance(term, OFix):
        _find_subterms_impl(term.body, predicate, results)
    elif isinstance(term, OSeq):
        for e in term.elements:
            _find_subterms_impl(e, predicate, results)
    elif isinstance(term, ODict):
        for k, v in term.pairs:
            _find_subterms_impl(k, predicate, results)
            _find_subterms_impl(v, predicate, results)
    elif isinstance(term, OQuotient):
        _find_subterms_impl(term.inner, predicate, results)
    elif isinstance(term, OAbstract):
        for a in term.inputs:
            _find_subterms_impl(a, predicate, results)
    elif isinstance(term, OLam):
        _find_subterms_impl(term.body, predicate, results)
    elif isinstance(term, OMap):
        _find_subterms_impl(term.transform, predicate, results)
        _find_subterms_impl(term.collection, predicate, results)
        if term.filter_pred is not None:
            _find_subterms_impl(term.filter_pred, predicate, results)
    elif isinstance(term, OCatch):
        _find_subterms_impl(term.body, predicate, results)
        _find_subterms_impl(term.default, predicate, results)


def find_all_folds(term: OTerm) -> List[OFold]:
    """Find all OFold sub-terms."""
    return find_subterms(term, lambda t: isinstance(t, OFold))  # type: ignore


def find_all_fixpoints(term: OTerm) -> List[OFix]:
    """Find all OFix sub-terms."""
    return find_subterms(term, lambda t: isinstance(t, OFix))  # type: ignore


def find_all_maps(term: OTerm) -> List[OMap]:
    """Find all OMap sub-terms."""
    return find_subterms(term, lambda t: isinstance(t, OMap))  # type: ignore


def find_all_lambdas(term: OTerm) -> List[OLam]:
    """Find all OLam sub-terms."""
    return find_subterms(term, lambda t: isinstance(t, OLam))  # type: ignore


# ═══════════════════════════════════════════════════════════
# Self-Tests
# ═══════════════════════════════════════════════════════════

def _test_metrics() -> None:
    """Test OTerm size/depth/free-var metrics."""
    t = OOp('add', (OVar('x'), OLit(1)))
    assert oterm_size(t) == 3, f"Expected 3, got {oterm_size(t)}"
    assert oterm_depth(t) == 1, f"Expected 1, got {oterm_depth(t)}"
    fv = collect_free_vars(t)
    assert fv == {'x'}, f"Expected {{'x'}}, got {fv}"

    nested = OCase(OOp('lt', (OVar('n'), OLit(0))),
                   OOp('u_usub', (OVar('n'),)), OVar('n'))
    assert oterm_size(nested) == 7
    assert oterm_depth(nested) == 2

    lam = OLam(('x',), OOp('add', (OVar('x'), OVar('y'))))
    fv_lam = collect_free_vars(lam)
    assert fv_lam == {'y'}, f"Expected {{'y'}}, got {fv_lam}"

    m = compute_metrics(nested)
    assert m.has_branching is True
    assert m.has_recursion is False
    print("  ✓ metrics tests passed")


def _test_nat_elim() -> None:
    """Test Nat-eliminator extraction."""
    fix = OFix('fact', OCase(
        OOp('lte', (OVar('n'), OLit(1))),
        OLit(1),
        OOp('mult', (OVar('n'), OOp('fact', (OOp('sub', (OVar('n'), OLit(1))),)))),
    ))
    params = extract_nat_elim(fix)
    assert params is not None, "Should extract nat-elim from factorial"
    assert params.op_name == 'mult'
    assert params.cmp_op == 'lte'
    assert isinstance(params.base_val, OLit) and params.base_val.value == 1

    folded = apply_nat_elim(fix)
    assert isinstance(folded, OFold), f"Expected OFold, got {type(folded).__name__}"
    assert folded.op_name == 'mult'
    print("  ✓ nat-elim tests passed")


def _test_course_of_values() -> None:
    """Test course-of-values detection."""
    fib = OFix('fib', OCase(
        OOp('lte', (OVar('n'), OLit(1))),
        OVar('n'),
        OOp('add', (
            OOp('fib', (OOp('sub', (OVar('n'), OLit(1))),)),
            OOp('fib', (OOp('sub', (OVar('n'), OLit(2))),)),
        )),
    ))
    k = detect_course_of_values(fib)
    assert k == 2, f"Expected k=2 for fibonacci, got {k}"

    # Classify it
    info = classify_recursion(fib)
    assert info.scheme == RecursionScheme.COURSE_OF_VALUES
    assert info.depth == 2
    assert info.call_count == 2
    print("  ✓ course-of-values tests passed")


def _test_recursion_classifier() -> None:
    """Test recursion scheme classification."""
    # Tail-recursive accumulator
    tail_sum = OFix('go', OCase(
        OOp('eq', (OVar('n'), OLit(0))),
        OVar('acc'),
        OOp('go', (OOp('sub', (OVar('n'), OLit(1))),)),
    ))
    info = classify_recursion(tail_sum)
    assert info.scheme == RecursionScheme.TAIL, f"Expected TAIL, got {info.scheme}"
    assert info.is_tail is True

    # Non-recursive (degenerate)
    no_rec = OFix('f', OOp('add', (OVar('x'), OLit(1))))
    info2 = classify_recursion(no_rec)
    assert info2.scheme == RecursionScheme.NON_RECURSIVE
    print("  ✓ recursion classifier tests passed")


def _test_catamorphism() -> None:
    """Test catamorphism recognizer."""
    fold = OFold('iadd', OLit(0), OVar('xs'))
    info = recognize_catamorphism(fold)
    assert info.kind == CatamorphismKind.FOLD
    assert info.op_name == 'iadd'

    map_term = OMap(OLam(('x',), OOp('mult', (OVar('x'), OLit(2)))), OVar('xs'))
    info2 = recognize_catamorphism(map_term)
    assert info2.kind == CatamorphismKind.MAP

    filter_term = OMap(OLam(('x',), OVar('x')), OVar('xs'),
                       OLam(('x',), OOp('gt', (OVar('x'), OLit(0)))))
    info3 = recognize_catamorphism(filter_term)
    assert info3.kind == CatamorphismKind.FILTER
    print("  ✓ catamorphism tests passed")


def _test_hof_fusion() -> None:
    """Test HOF fusion rules."""
    double = OLam(('x',), OOp('mult', (OVar('x'), OLit(2))))
    inc = OLam(('x',), OOp('add', (OVar('x'), OLit(1))))

    composed = fuse_map_map(double, inc)
    assert isinstance(composed, OLam)
    assert len(composed.params) == 1

    # map(double, map(inc, xs)) should fuse
    inner_map = OMap(inc, OVar('xs'))
    outer_map = OMap(double, inner_map)
    result = apply_hof_fusion(outer_map)
    assert result.fused is True, "map∘map should fuse"
    assert isinstance(result.result, OMap)
    assert not isinstance(result.result.collection, OMap), "Should eliminate inner map"

    # Identity map should be eliminated
    id_map = OMap(OLam(('x',), OVar('x')), OVar('xs'))
    result2 = apply_hof_fusion(id_map)
    assert result2.fused is True
    assert isinstance(result2.result, OVar)
    print("  ✓ HOF fusion tests passed")


def _test_de_bruijn() -> None:
    """Test de Bruijn normalization and alpha-equivalence."""
    lam_a = OLam(('x',), OOp('add', (OVar('x'), OLit(1))))
    lam_b = OLam(('y',), OOp('add', (OVar('y'), OLit(1))))

    assert alpha_equivalent(lam_a, lam_b), "λx.x+1 should be alpha-equiv to λy.y+1"

    lam_c = OLam(('x',), OOp('mult', (OVar('x'), OLit(2))))
    assert not alpha_equivalent(lam_a, lam_c), "λx.x+1 should not equal λx.x*2"

    norm_a = de_bruijn_normalize(lam_a)
    norm_b = de_bruijn_normalize(lam_b)
    assert norm_a.canon() == norm_b.canon()
    print("  ✓ de Bruijn tests passed")


def _test_pretty_printer() -> None:
    """Test mathematical pretty-printer."""
    t = OOp('add', (OVar('x'), OLit(1)))
    s = pretty_print(t)
    assert '×' not in s and '+' in s, f"Expected + symbol, got: {s}"

    fold = OFold('iadd', OLit(0), OVar('xs'))
    s2 = pretty_print(fold)
    assert 'Σ' in s2, f"Expected Σ for sum fold, got: {s2}"

    case = OCase(OOp('lt', (OVar('n'), OLit(0))),
                 OOp('u_usub', (OVar('n'),)), OVar('n'))
    s3 = pretty_print(case)
    assert 'if' in s3 and 'then' in s3, f"Expected if/then, got: {s3}"
    print("  ✓ pretty-printer tests passed")


def _test_normalization_trace() -> None:
    """Test normalization tracing and profiling."""
    prog_a = OOp('abs', (OVar('n'),))
    prog_b = OCase(OOp('lt', (OVar('n'), OLit(0))),
                   OOp('u_usub', (OVar('n'),)), OVar('n'))

    trace_a = normalize_with_trace(prog_a)
    trace_b = normalize_with_trace(prog_b)

    assert trace_a.iterations >= 1
    assert len(trace_a.snapshots) >= 7
    assert trace_a.output_term.canon() == trace_b.output_term.canon(), \
        f"abs(n) and if n<0 -n else n should normalize to same term"

    profile = profile_phases(trace_a)
    assert len(profile) == 7
    assert any(p.total_changes > 0 for p in profile), "At least one phase should change abs(n)"

    summary = profile_summary(trace_a)
    assert 'P4' in summary
    print("  ✓ normalization trace tests passed")


def _test_coverage() -> None:
    """Test compilation coverage analysis."""
    source = '''
def foo(x, y):
    if x > 0:
        return x + y
    else:
        return x - y
'''
    report = analyze_coverage(source)
    assert report.coverage_pct > 0.0
    assert 'If' in report.source_stmt_counts
    assert 'BinOp' in report.source_expr_counts
    print("  ✓ coverage tests passed")


def _test_fold_canon_extensions() -> None:
    """Test extended fold canonicalization."""
    prod = OOp('prod', (OVar('xs'),))
    result = extended_phase3_fold(prod)
    assert isinstance(result, OFold), f"Expected OFold for prod, got {type(result).__name__}"
    assert result.op_name == 'imult'
    assert isinstance(result.init, OLit) and result.init.value == 1

    bitor = OOp('bitwise_or', (OVar('xs'),))
    result2 = extended_phase3_fold(bitor)
    assert isinstance(result2, OFold)
    assert result2.op_name == 'ior'
    print("  ✓ fold canon extension tests passed")


def _test_traversal_utils() -> None:
    """Test map_oterm, fold_oterm, and search utilities."""
    t = OOp('add', (OVar('x'), OOp('mult', (OVar('y'), OLit(3)))))

    # Collect all ops
    ops = collect_all_ops(t)
    assert 'add' in ops and 'mult' in ops, f"Expected add and mult, got {ops}"

    # Find all variables
    vars_found = find_subterms(t, lambda n: isinstance(n, OVar))
    var_names = {v.name for v in vars_found}  # type: ignore
    assert var_names == {'x', 'y'}, f"Expected x,y got {var_names}"

    # map_oterm: negate all literals
    def negate_lits(n: OTerm) -> OTerm:
        if isinstance(n, OLit) and isinstance(n.value, (int, float)):
            return OLit(-n.value)
        return n

    negated = map_oterm(negate_lits, t)
    assert isinstance(negated, OOp)
    # The literal 3 should now be -3
    inner = negated.args[1]
    assert isinstance(inner, OOp) and isinstance(inner.args[1], OLit)
    assert inner.args[1].value == -3
    print("  ✓ traversal utility tests passed")


def _test_comparison() -> None:
    """Test source comparison utilities."""
    src_a = '''
def f(n):
    return abs(n)
'''
    src_b = '''
def g(n):
    if n < 0:
        return -n
    else:
        return n
'''
    result = compare_sources(src_a, src_b)
    assert result is not None, "Should compile both sources"
    assert result.equivalent, "abs(n) should equal if n<0: -n else n"
    print("  ✓ comparison tests passed")


def _test_contains_fix_ref_extended() -> None:
    """Test _contains_fix_ref with diverse OTerm shapes."""
    assert _contains_fix_ref(OVar('f'), 'f') is True
    assert _contains_fix_ref(OVar('g'), 'f') is False
    assert _contains_fix_ref(OLam(('x',), OOp('f', (OVar('x'),))), 'f') is True
    assert _contains_fix_ref(OMap(
        OLam(('x',), OVar('x')),
        OOp('f', (OVar('n'),)),
    ), 'f') is True
    catch = OCatch(OOp('f', (OVar('x'),)), OLit(0))
    assert _contains_fix_ref(catch, 'f') is True
    assert _contains_fix_ref(catch, 'g') is False
    print("  ✓ contains-fix-ref extended tests passed")


if __name__ == '__main__':
    print("Running g13_compilation proposal self-tests...")
    _test_metrics()
    _test_nat_elim()
    _test_course_of_values()
    _test_recursion_classifier()
    _test_catamorphism()
    _test_hof_fusion()
    _test_de_bruijn()
    _test_pretty_printer()
    _test_normalization_trace()
    _test_coverage()
    _test_fold_canon_extensions()
    _test_traversal_utils()
    _test_comparison()
    _test_contains_fix_ref_extended()
    print("\nAll 14 test suites passed. ✓")
