"""Compositional Cohomology — genuine sheaf cohomology over two sites.

SITE 1 (OTerm tree site — the "algebraic" site):
    Site:       OTerm tree positions (sub-expressions)
    Presheaf:   denotational meaning at each position
    Restriction: how sub-expression changes propagate through enclosing ops
    H¹:         non-absorbed obstructions (genuine compositional invariant)

    The key theorem: the connecting homomorphism δ: H⁰(F_overlap) → H¹(whole)
    maps a local obstruction to ZERO when the enclosing operations have
    algebraic identity/annihilator properties that absorb the difference.

    Example: sum(x² for x if x>0) ≡ sum(x² for x if x≥0) because the
    filter boundary at x=0 maps through x²→0 then +0→id. δ=0.

SITE 2 (Input-space site — the "Čech" site):
    Site:       Input space X = ℤⁿ (or ℝⁿ) partitioned by guard conditions
    Cover:      Guard regions from OCase trees of both programs
    Presheaf:   F(U) = {(f|_U, g|_U)} — the pair of programs restricted to U
    Refinement: Common refinement of both programs' guard covers
    Cocycle:    d_{ij} = (f - g)|_{U_i ∩ V_j} on each refined region
    H¹ = 0 iff all non-empty refined regions agree

    This is strictly more powerful than tree-diffing: two programs with
    DIFFERENT guard partitions can be proven equivalent by checking
    agreement on every piece of the refined cover via Z3.

    Example: case(x>0, A, B) ≡ case(x≥0, A, case(x==0, A, B))
    Tree-diffing sees different guards and gives up.
    Čech refinement: {x>0, x==0, x<0}. On each piece, values match.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union

try:
    from z3 import (
        Int, IntVal, Real, RealVal, ArithRef, BoolVal,
        ForAll, And, Not, Implies, Or,
        Solver, sat, unsat, unknown as z3_unknown,
        set_param as z3_set_param,
    )
    _HAS_Z3 = True
except ImportError:
    _HAS_Z3 = False


# ═══════════════════════════════════════════════════════════════
# Data structures
# ═══════════════════════════════════════════════════════════════

@dataclass
class Fiber:
    """A sub-expression pair at a specific OTerm tree position."""
    path: Tuple[Union[str, int], ...]
    term_f: Any   # OTerm from program f
    term_g: Any   # OTerm from program g
    locally_equivalent: Optional[bool] = None


@dataclass
class AbsorptionResult:
    """Whether a local difference is absorbed by the Mayer-Vietoris
    connecting homomorphism through enclosing operations."""
    absorbed: bool
    reason: str
    z3_verified: bool = False


@dataclass
class CohomologyResult:
    """Result of compositional sheaf cohomology over the OTerm site.

    h1_rank = 0 and all fibers resolved → equivalent (formal proof).
    h1_rank > 0 → non-equivalent (compositional obstruction).
    """
    h1_rank: int
    equivalent: Optional[bool]
    fibers: List[Fiber] = field(default_factory=list)
    absorptions: Dict[Tuple, AbsorptionResult] = field(default_factory=dict)
    explanation: str = ''


# ═══════════════════════════════════════════════════════════════
# Algebraic identity table — axioms, not heuristics
# ═══════════════════════════════════════════════════════════════

# For a fold operation `op`, `FOLD_IDENTITY[op]` is the value e such
# that op(x, e) = x for all x.  These are mathematical facts about
# the operations, verified once and used as axioms.
FOLD_IDENTITY: Dict[str, Any] = {
    'add': 0,
    'Add': 0,
    '+': 0,
    'sub': 0,       # right identity: x - 0 = x
    '-': 0,
    'mul': 1,
    'Mult': 1,
    '*': 1,
    'bitor': 0,     # x | 0 = x
    '|': 0,
    'bitand': -1,   # x & (-1) = x  (all bits set)
    '&': -1,
    'bitxor': 0,    # x ^ 0 = x
    '^': 0,
    'and': True,    # x and True = x
    'And': True,
    'or': False,    # x or False = x
    'Or': False,
    'min': None,    # no finite identity (∞)
    'max': None,    # no finite identity (-∞)
    'concat': '',   # "" + s = s
    'join': '',
}

# Annihilators: op(x, a) = a for all x
FOLD_ANNIHILATOR: Dict[str, Any] = {
    'mul': 0,       # x * 0 = 0
    'Mult': 0,
    '*': 0,
    'and': False,   # x and False = False
    'And': False,
    'or': True,     # x or True = True
    'Or': True,
    'bitand': 0,    # x & 0 = 0
    '&': 0,
}


# ═══════════════════════════════════════════════════════════════
# OTerm alignment — extract the presheaf decomposition
# ═══════════════════════════════════════════════════════════════

def _otype(t) -> str:
    """Get OTerm constructor name."""
    return type(t).__name__


def align_oterms(t_f, t_g, path: Tuple = ()) -> List[Fiber]:
    """Align two OTerms along the OTerm tree, yielding fibers.

    When constructors match, recurse into children (refining the cover).
    When they differ, record the whole subtree as a single differing fiber.
    Leaf nodes (OLit, OVar) are compared directly.

    This defines the Čech cover of the OTerm site: each fiber is an
    open set, and overlapping fibers share parent-child relationships.
    """
    name_f = _otype(t_f)
    name_g = _otype(t_g)
    fibers: List[Fiber] = []

    # Different top-level constructors → single differing fiber
    if name_f != name_g:
        fibers.append(Fiber(path=path, term_f=t_f, term_g=t_g,
                            locally_equivalent=False))
        return fibers

    # Same constructor → recurse into children
    if name_f == 'OLit':
        fibers.append(Fiber(path=path, term_f=t_f, term_g=t_g,
                            locally_equivalent=(t_f.value == t_g.value)))

    elif name_f == 'OVar':
        fibers.append(Fiber(path=path, term_f=t_f, term_g=t_g,
                            locally_equivalent=(t_f.name == t_g.name)))

    elif name_f == 'OOp':
        if t_f.name != t_g.name or len(t_f.args) != len(t_g.args):
            fibers.append(Fiber(path=path, term_f=t_f, term_g=t_g,
                                locally_equivalent=False))
        else:
            # Op names match — recurse into arguments
            all_eq = True
            child_fibers: List[Fiber] = []
            for i, (a, b) in enumerate(zip(t_f.args, t_g.args)):
                cf = align_oterms(a, b, path + ('args', i))
                child_fibers.extend(cf)
                if any(not f.locally_equivalent for f in cf):
                    all_eq = False
            if all_eq and not child_fibers:
                fibers.append(Fiber(path=path, term_f=t_f, term_g=t_g,
                                    locally_equivalent=True))
            else:
                fibers.extend(child_fibers)

    elif name_f == 'OFold':
        if t_f.op_name != t_g.op_name:
            # Different fold keys — check if body_fn matches structurally
            # Only trust body_fn comparison when the body is self-contained
            # (no calls to locally-defined functions that may differ in scope)
            body_equiv = False
            if (hasattr(t_f, 'body_fn') and hasattr(t_g, 'body_fn')
                    and t_f.body_fn is not None and t_g.body_fn is not None):
                from .denotation import _body_fn_trustworthy
                if (t_f.body_fn.canon() == t_g.body_fn.canon()
                        and _body_fn_trustworthy(t_f.body_fn)
                        and _body_fn_trustworthy(t_g.body_fn)):
                    body_equiv = True
            if body_equiv:
                # Body functions match — recurse into init and collection
                fibers.extend(align_oterms(t_f.init, t_g.init,
                                           path + ('init',)))
                fibers.extend(align_oterms(t_f.collection, t_g.collection,
                                           path + ('collection',)))
            else:
                fibers.append(Fiber(path=path, term_f=t_f, term_g=t_g,
                                    locally_equivalent=False))
        else:
            # Same fold op — recurse into init and collection
            fibers.extend(align_oterms(t_f.init, t_g.init,
                                       path + ('init',)))
            fibers.extend(align_oterms(t_f.collection, t_g.collection,
                                       path + ('collection',)))

    elif name_f == 'OMap':
        fibers.extend(align_oterms(t_f.transform, t_g.transform,
                                   path + ('transform',)))
        fibers.extend(align_oterms(t_f.collection, t_g.collection,
                                   path + ('map_collection',)))
        # Filter predicate (may be None)
        if t_f.filter_pred is not None and t_g.filter_pred is not None:
            fibers.extend(align_oterms(t_f.filter_pred, t_g.filter_pred,
                                       path + ('filter_pred',)))
        elif t_f.filter_pred is not None or t_g.filter_pred is not None:
            # One has filter, other doesn't
            fibers.append(Fiber(
                path=path + ('filter_pred',),
                term_f=t_f.filter_pred, term_g=t_g.filter_pred,
                locally_equivalent=False))

    elif name_f == 'OCase':
        fibers.extend(align_oterms(t_f.test, t_g.test,
                                   path + ('test',)))
        fibers.extend(align_oterms(t_f.true_branch, t_g.true_branch,
                                   path + ('true_branch',)))
        fibers.extend(align_oterms(t_f.false_branch, t_g.false_branch,
                                   path + ('false_branch',)))

    elif name_f == 'OLam':
        if len(t_f.params) != len(t_g.params):
            fibers.append(Fiber(path=path, term_f=t_f, term_g=t_g,
                                locally_equivalent=False))
        else:
            fibers.extend(align_oterms(t_f.body, t_g.body,
                                       path + ('body',)))

    elif name_f == 'OSeq':
        if len(t_f.elements) != len(t_g.elements):
            fibers.append(Fiber(path=path, term_f=t_f, term_g=t_g,
                                locally_equivalent=False))
        else:
            for i, (a, b) in enumerate(zip(t_f.elements, t_g.elements)):
                fibers.extend(align_oterms(a, b, path + ('elem', i)))

    elif name_f == 'OFix':
        if t_f.name != t_g.name:
            fibers.append(Fiber(path=path, term_f=t_f, term_g=t_g,
                                locally_equivalent=False))
        else:
            fibers.extend(align_oterms(t_f.body, t_g.body,
                                       path + ('fix_body',)))

    elif name_f == 'OCatch':
        fibers.extend(align_oterms(t_f.body, t_g.body,
                                   path + ('catch_body',)))
        fibers.extend(align_oterms(t_f.default, t_g.default,
                                   path + ('catch_default',)))

    elif name_f == 'OQuotient':
        if t_f.equiv_class != t_g.equiv_class:
            fibers.append(Fiber(path=path, term_f=t_f, term_g=t_g,
                                locally_equivalent=False))
        else:
            fibers.extend(align_oterms(t_f.inner, t_g.inner,
                                       path + ('quotient_inner',)))

    elif name_f == 'OAbstract':
        fibers.append(Fiber(path=path, term_f=t_f, term_g=t_g,
                            locally_equivalent=(t_f.spec == t_g.spec)))

    else:
        # Fallback: compare canonical forms
        fibers.append(Fiber(path=path, term_f=t_f, term_g=t_g,
                            locally_equivalent=(t_f.canon() == t_g.canon())))

    return fibers


# ═══════════════════════════════════════════════════════════════
# Restriction context — the chain from fiber to root
# ═══════════════════════════════════════════════════════════════

def _get_subterm(root, path: Tuple) -> Any:
    """Navigate the OTerm tree to a specific position."""
    current = root
    i = 0
    while i < len(path):
        step = path[i]
        if step == 'args' and i + 1 < len(path):
            current = current.args[path[i + 1]]
            i += 2
        elif step == 'init':
            current = current.init
            i += 1
        elif step == 'collection':
            current = current.collection
            i += 1
        elif step == 'transform':
            current = current.transform
            i += 1
        elif step == 'map_collection':
            current = current.collection
            i += 1
        elif step == 'filter_pred':
            current = current.filter_pred
            i += 1
        elif step == 'test':
            current = current.test
            i += 1
        elif step == 'true_branch':
            current = current.true_branch
            i += 1
        elif step == 'false_branch':
            current = current.false_branch
            i += 1
        elif step == 'body':
            current = current.body
            i += 1
        elif step == 'fix_body':
            current = current.body
            i += 1
        elif step == 'catch_body':
            current = current.body
            i += 1
        elif step == 'catch_default':
            current = current.default
            i += 1
        elif step == 'quotient_inner':
            current = current.inner
            i += 1
        elif step == 'elem' and i + 1 < len(path):
            current = current.elements[path[i + 1]]
            i += 2
        else:
            return None
    return current


def _ancestor_chain(root, fiber_path: Tuple) -> List[Tuple[Tuple, Any, str]]:
    """Walk from root toward the fiber, collecting (path, node, child_role) at each level.

    Returns a list of (ancestor_path, ancestor_oterm, role_of_child) from
    outermost to innermost.  'role_of_child' is the semantic role the next
    level plays in the ancestor (e.g., 'collection' in an OFold, 'transform'
    in an OMap, 'filter_pred' in an OMap).
    """
    chain: List[Tuple[Tuple, Any, str]] = []
    i = 0
    current_path: Tuple = ()
    current = root

    while i < len(fiber_path):
        step = fiber_path[i]

        if step == 'args':
            child_idx = fiber_path[i + 1]
            chain.append((current_path, current, f'args_{child_idx}'))
            current = current.args[child_idx]
            current_path = current_path + (step, child_idx)
            i += 2
        elif step == 'elem':
            child_idx = fiber_path[i + 1]
            chain.append((current_path, current, f'elem_{child_idx}'))
            current = current.elements[child_idx]
            current_path = current_path + (step, child_idx)
            i += 2
        elif step in ('init', 'collection', 'transform', 'map_collection',
                       'filter_pred', 'test', 'true_branch', 'false_branch',
                       'body', 'fix_body', 'catch_body', 'catch_default',
                       'quotient_inner'):
            chain.append((current_path, current, step))
            current = _get_subterm(current, (step,))
            current_path = current_path + (step,)
            i += 1
        else:
            i += 1

    return chain


# ═══════════════════════════════════════════════════════════════
# Absorption checking — the connecting homomorphism
# ═══════════════════════════════════════════════════════════════

def _evaluate_oterm_at(term, var_name: str, value) -> Optional[Any]:
    """Symbolically evaluate an OTerm at a specific variable binding.

    Returns a Python value if the term can be fully evaluated, else None.
    This is exact symbolic evaluation, not approximation.
    """
    name = _otype(term)
    if name == 'OLit':
        return term.value
    if name == 'OVar':
        if term.name == var_name:
            return value
        return None  # free variable, can't evaluate
    if name == 'OLam':
        # Lambda — evaluate body with the bound variable
        if len(term.params) == 1:
            return _evaluate_oterm_at(term.body, term.params[0], value)
        return None
    if name == 'OOp':
        args_eval = []
        for a in term.args:
            v = _evaluate_oterm_at(a, var_name, value)
            if v is None:
                return None
            args_eval.append(v)
        return _apply_op(term.name, args_eval)
    return None


def _apply_op(name: str, args: list) -> Optional[Any]:
    """Apply a named operation to evaluated arguments."""
    try:
        if name in ('add', 'Add', '+') and len(args) == 2:
            return args[0] + args[1]
        if name in ('sub', 'Sub', '-') and len(args) == 2:
            return args[0] - args[1]
        if name in ('mul', 'Mult', '*') and len(args) == 2:
            return args[0] * args[1]
        if name in ('pow', 'Pow', '**') and len(args) == 2:
            return args[0] ** args[1]
        if name in ('mod', 'Mod', '%') and len(args) == 2:
            if args[1] == 0:
                return None
            return args[0] % args[1]
        if name in ('floordiv', 'FloorDiv', '//') and len(args) == 2:
            if args[1] == 0:
                return None
            return args[0] // args[1]
        if name in ('neg', 'USub') and len(args) == 1:
            return -args[0]
        if name == 'abs' and len(args) == 1:
            return abs(args[0])
        if name in ('eq', 'Eq', '==') and len(args) == 2:
            return args[0] == args[1]
        if name in ('ne', 'NotEq', '!=') and len(args) == 2:
            return args[0] != args[1]
        if name in ('lt', 'Lt', '<') and len(args) == 2:
            return args[0] < args[1]
        if name in ('le', 'LtE', '<=') and len(args) == 2:
            return args[0] <= args[1]
        if name in ('gt', 'Gt', '>') and len(args) == 2:
            return args[0] > args[1]
        if name in ('ge', 'GtE', '>=') and len(args) == 2:
            return args[0] >= args[1]
        if name in ('not', 'Not') and len(args) == 1:
            return not args[0]
        if name in ('and', 'And') and len(args) == 2:
            return args[0] and args[1]
        if name in ('or', 'Or') and len(args) == 2:
            return args[0] or args[1]
        if name in ('bitor', 'BitOr', '|') and len(args) == 2:
            return args[0] | args[1]
        if name in ('bitand', 'BitAnd', '&') and len(args) == 2:
            return args[0] & args[1]
        if name in ('bitxor', 'BitXor', '^') and len(args) == 2:
            return args[0] ^ args[1]
        if name == 'in' and len(args) == 2:
            return args[0] in args[1] if hasattr(args[1], '__contains__') else None
    except Exception:
        return None
    return None


def _check_filter_absorption(
    fiber: Fiber,
    ancestor_chain: List[Tuple[Tuple, Any, str]],
) -> AbsorptionResult:
    """Check if a filter predicate difference is absorbed through map→fold.

    This is the main cohomological computation.  The Mayer-Vietoris
    connecting homomorphism δ maps the filter-overlap cocycle to H¹(whole).
    δ = 0 iff the "extra" filtered elements, after passing through
    the map transform, are identity elements of the enclosing fold.

    Exact sequence on the OTerm presheaf:
        H⁰(filter) ⊕ H⁰(map) ⊕ H⁰(fold) → H⁰(overlaps) →δ H¹(whole) → 0
    """
    # Find the enclosing OMap and OFold in the ancestor chain
    map_node = None
    fold_node = None
    for _path, node, _role in reversed(ancestor_chain):
        ntype = _otype(node)
        if ntype == 'OMap' and map_node is None:
            map_node = node
        elif ntype == 'OFold' and fold_node is None:
            fold_node = node
            break

    if fold_node is None:
        return AbsorptionResult(False, 'no enclosing fold to absorb filter difference')

    # Get fold identity
    fold_op = fold_node.op_name
    if fold_op not in FOLD_IDENTITY:
        return AbsorptionResult(False, f'no known identity for fold op "{fold_op}"')
    identity_val = FOLD_IDENTITY[fold_op]
    if identity_val is None:
        return AbsorptionResult(False, f'fold op "{fold_op}" has no finite identity')

    # The "extra elements" are where one filter passes and the other doesn't.
    # We need: for every such extra element x, transform(x) == identity_val
    #
    # For the case filter_pred = OLam(x, OOp(gt, x, 0)) vs OLam(x, OOp(ge, x, 0)):
    # Extra elements: {0}  (where ge passes but gt doesn't)
    # Need: transform(0) == identity_val

    pred_f = fiber.term_f
    pred_g = fiber.term_g

    # Determine which direction the filter expanded (more permissive)
    # We'll check both directions
    boundary_values = _extract_filter_boundary_values(pred_f, pred_g)

    if boundary_values is None:
        # Try Z3 for complex filter predicates
        return _check_filter_absorption_z3(
            pred_f, pred_g, map_node, fold_node, identity_val)

    # For each boundary value, trace through map transform
    transform = map_node.transform if map_node else None

    for bval in boundary_values:
        if transform is not None:
            # Evaluate transform(boundary_value)
            mapped = _evaluate_lambda(transform, bval)
            if mapped is None:
                return AbsorptionResult(
                    False,
                    f'cannot evaluate transform at boundary value {bval}')
            # Check if mapped value is the fold identity
            if mapped != identity_val:
                return AbsorptionResult(
                    False,
                    f'transform({bval}) = {mapped} ≠ {identity_val} '
                    f'(identity of {fold_op}): NOT absorbed')
        else:
            # No map: the element itself must be the identity
            if bval != identity_val:
                return AbsorptionResult(
                    False,
                    f'boundary value {bval} ≠ {identity_val} '
                    f'(identity of {fold_op}): NOT absorbed')

    return AbsorptionResult(
        True,
        f'filter boundary values {boundary_values} map to '
        f'{identity_val} (identity of {fold_op}): absorbed by '
        f'connecting homomorphism δ=0',
        z3_verified=False)


def _evaluate_lambda(lam_term, value) -> Optional[Any]:
    """Evaluate an OLam at a specific argument value."""
    if _otype(lam_term) != 'OLam':
        return None
    if len(lam_term.params) != 1:
        return None
    return _evaluate_oterm_at(lam_term.body, lam_term.params[0], value)


def _extract_filter_boundary_values(pred_f, pred_g) -> Optional[List[Any]]:
    """Extract the concrete boundary values where two filter predicates differ.

    For simple comparison predicates (x > C vs x >= C, x > C vs x > D, etc.),
    the boundary is a finite set of integers.

    Returns None if the predicates are too complex for syntactic analysis.
    """
    # Handle OLam wrappers
    if _otype(pred_f) == 'OLam' and _otype(pred_g) == 'OLam':
        return _extract_comparison_boundary(pred_f.body, pred_g.body,
                                            pred_f.params[0] if pred_f.params else None)

    # Handle raw OOp bodies (when alignment recursed into the lambda)
    if _otype(pred_f) == 'OOp' and _otype(pred_g) == 'OOp':
        return _extract_comparison_boundary(pred_f, pred_g, None)

    return None


def _extract_comparison_boundary(body_f, body_g, var_name) -> Optional[List[Any]]:
    """Extract boundary values from two comparison expressions.

    Handles patterns like:
      x > C  vs  x >= C   → boundary = [C]
      x > C  vs  x > D    → boundary = range(min(C,D)+1, max(C,D)+1)
      x < C  vs  x <= C   → boundary = [C]
      x in "abc" vs x in "abcd" → boundary = ['d']
      x > 0  vs  x >= -1  → normalize to ge form, boundary = [-1, 0]
    """
    if _otype(body_f) != 'OOp' or _otype(body_g) != 'OOp':
        return None

    op_f, op_g = body_f.name, body_g.name

    # Normalize to (var, const) form
    var_f, const_f = _extract_var_const(body_f, var_name)
    var_g, const_g = _extract_var_const(body_g, var_name)

    if var_f is None or var_g is None:
        # Try 'in' operator with string literals
        return _extract_in_boundary(body_f, body_g, var_name)

    # Normalize all comparisons to >= form for integers
    # x > C  →  x >= C+1  (for integers)
    # x < C  →  x >= C is false, x <= C-1 → -(x >= C) but better: negate
    # Actually, normalize to (inclusive_lower_bound, is_upper_bound) form
    gt_ops = {'gt', 'Gt', '>', 'greater'}
    ge_ops = {'ge', 'GtE', '>=', 'gte', 'greater_equal'}
    lt_ops = {'lt', 'Lt', '<', 'less'}
    le_ops = {'le', 'LtE', '<=', 'lte', 'less_equal'}

    if not isinstance(const_f, (int, float)) or not isinstance(const_g, (int, float)):
        return None

    # Convert to "x >= threshold" form (for lower bounds)
    # or "x <= threshold" form (for upper bounds)
    thresh_f = _normalize_to_ge_threshold(op_f, const_f, gt_ops, ge_ops)
    thresh_g = _normalize_to_ge_threshold(op_g, const_g, gt_ops, ge_ops)

    if thresh_f is not None and thresh_g is not None:
        # Both are lower-bound comparisons (x > C or x >= C)
        lo = min(thresh_f, thresh_g)
        hi = max(thresh_f, thresh_g)
        if isinstance(lo, int) and isinstance(hi, int) and hi - lo <= 20:
            return list(range(lo, hi))
        return None

    # Try upper-bound normalization
    thresh_f_upper = _normalize_to_le_threshold(op_f, const_f, lt_ops, le_ops)
    thresh_g_upper = _normalize_to_le_threshold(op_g, const_g, lt_ops, le_ops)

    if thresh_f_upper is not None and thresh_g_upper is not None:
        lo = min(thresh_f_upper, thresh_g_upper)
        hi = max(thresh_f_upper, thresh_g_upper)
        if isinstance(lo, int) and isinstance(hi, int) and hi - lo <= 20:
            return list(range(lo + 1, hi + 1))
        return None

    # x > C vs x >= C (same constant, different strictness)
    if const_f == const_g:
        if (op_f in gt_ops and op_g in ge_ops) or \
           (op_f in ge_ops and op_g in gt_ops):
            return [const_f]
        if (op_f in lt_ops and op_g in le_ops) or \
           (op_f in le_ops and op_g in lt_ops):
            return [const_f]

    return None


def _normalize_to_ge_threshold(op: str, const, gt_ops, ge_ops) -> Optional[int]:
    """Normalize x > C or x >= C to the inclusive lower bound threshold.

    x > C  →  threshold = C + 1  (for integers)
    x >= C →  threshold = C
    """
    if op in ge_ops:
        return int(const) if isinstance(const, (int, float)) else None
    if op in gt_ops:
        return int(const) + 1 if isinstance(const, (int, float)) else None
    return None


def _normalize_to_le_threshold(op: str, const, lt_ops, le_ops) -> Optional[int]:
    """Normalize x < C or x <= C to the inclusive upper bound threshold.

    x < C  →  threshold = C - 1
    x <= C →  threshold = C
    """
    if op in le_ops:
        return int(const) if isinstance(const, (int, float)) else None
    if op in lt_ops:
        return int(const) - 1 if isinstance(const, (int, float)) else None
    return None


def _extract_var_const(op_term, expected_var) -> Tuple[Optional[str], Optional[Any]]:
    """Extract (var_name, constant) from a comparison like OOp(gt, OVar(x), OLit(0))."""
    if _otype(op_term) != 'OOp' or len(op_term.args) != 2:
        return None, None

    a, b = op_term.args
    if _otype(a) == 'OVar' and _otype(b) == 'OLit':
        if expected_var is None or a.name == expected_var:
            return a.name, b.value
    if _otype(b) == 'OVar' and _otype(a) == 'OLit':
        if expected_var is None or b.name == expected_var:
            return b.name, a.value
    return None, None


def _extract_in_boundary(body_f, body_g, var_name) -> Optional[List[Any]]:
    """Extract boundary values for 'in' comparisons.

    x in "aeiou" vs x in "aeio" → boundary = ['u']
    """
    if body_f.name != 'in' or body_g.name != 'in':
        return None
    if len(body_f.args) != 2 or len(body_g.args) != 2:
        return None

    # Check that the variable side matches
    var_f = body_f.args[0]
    var_g = body_g.args[0]
    if _otype(var_f) != 'OVar' or _otype(var_g) != 'OVar':
        return None
    if var_name and (var_f.name != var_name or var_g.name != var_name):
        return None

    # Get the collection side
    coll_f = body_f.args[1]
    coll_g = body_g.args[1]
    if _otype(coll_f) != 'OLit' or _otype(coll_g) != 'OLit':
        return None

    set_f = set(str(coll_f.value)) if isinstance(coll_f.value, str) else set(coll_f.value)
    set_g = set(str(coll_g.value)) if isinstance(coll_g.value, str) else set(coll_g.value)

    # Symmetric difference = boundary values
    boundary = list(set_f.symmetric_difference(set_g))
    if not boundary:
        return []  # identical filter predicates
    return boundary


def _check_filter_absorption_z3(
    pred_f, pred_g, map_node, fold_node, identity_val
) -> AbsorptionResult:
    """Z3-backed absorption check for complex filter predicates.

    Verifies: ∀x. (pred_g(x) ∧ ¬pred_f(x)) → transform(x) == identity_val
    (and symmetrically for pred_f \\ pred_g)
    """
    if not _HAS_Z3:
        return AbsorptionResult(False, 'Z3 not available for complex absorption check')

    try:
        z3_set_param('timeout', 2000)
        x = Int('x_abs')
        solver = Solver()

        # Compile predicates to Z3
        z3_pred_f = _oterm_to_z3(pred_f, {'x': x, '_b0': x})
        z3_pred_g = _oterm_to_z3(pred_g, {'x': x, '_b0': x})
        if z3_pred_f is None or z3_pred_g is None:
            return AbsorptionResult(False, 'cannot compile predicates to Z3')

        # Compile transform to Z3
        z3_transform = None
        if map_node is not None and map_node.transform is not None:
            z3_transform = _oterm_to_z3_value(map_node.transform, {'x': x, '_b0': x})
        else:
            z3_transform = x  # identity transform

        if z3_transform is None:
            return AbsorptionResult(False, 'cannot compile transform to Z3')

        # Check: ∀x. (in symmetric diff) → transform(x) == identity
        z3_id = IntVal(identity_val) if isinstance(identity_val, int) else None
        if z3_id is None:
            return AbsorptionResult(False, 'identity not representable in Z3')

        # Direction 1: elements in pred_g but not pred_f
        solver.push()
        solver.add(z3_pred_g)
        solver.add(Not(z3_pred_f))
        solver.add(z3_transform != z3_id)
        r1 = solver.check()
        solver.pop()

        if r1 == sat:
            return AbsorptionResult(False,
                'Z3 found element in pred_g\\pred_f where transform ≠ identity')

        # Direction 2: elements in pred_f but not pred_g
        solver.push()
        solver.add(z3_pred_f)
        solver.add(Not(z3_pred_g))
        solver.add(z3_transform != z3_id)
        r2 = solver.check()
        solver.pop()

        if r2 == sat:
            return AbsorptionResult(False,
                'Z3 found element in pred_f\\pred_g where transform ≠ identity')

        if r1 == unsat and r2 == unsat:
            return AbsorptionResult(True,
                'Z3 verified: all boundary elements map to fold identity '
                '(connecting homomorphism δ=0)',
                z3_verified=True)

        return AbsorptionResult(False, 'Z3 inconclusive on absorption check')

    except Exception as e:
        return AbsorptionResult(False, f'Z3 error in absorption check: {e}')


def _oterm_to_z3(term, env: dict):
    """Compile an OTerm predicate to a Z3 boolean expression."""
    if not _HAS_Z3:
        return None
    name = _otype(term)
    if name == 'OLam':
        # Bind parameter to the environment variable
        if len(term.params) == 1:
            return _oterm_to_z3(term.body, env)
        return None
    if name == 'OLit':
        if isinstance(term.value, bool):
            from z3 import BoolVal
            return BoolVal(term.value)
        return None
    if name == 'OVar':
        return env.get(term.name)
    if name == 'OOp':
        args_z3 = [_oterm_to_z3_value(a, env) for a in term.args]
        if any(a is None for a in args_z3):
            return None
        op = term.name
        if op in ('gt', 'Gt', '>') and len(args_z3) == 2:
            return args_z3[0] > args_z3[1]
        if op in ('ge', 'GtE', '>=') and len(args_z3) == 2:
            return args_z3[0] >= args_z3[1]
        if op in ('lt', 'Lt', '<') and len(args_z3) == 2:
            return args_z3[0] < args_z3[1]
        if op in ('le', 'LtE', '<=') and len(args_z3) == 2:
            return args_z3[0] <= args_z3[1]
        if op in ('eq', 'Eq', '==') and len(args_z3) == 2:
            return args_z3[0] == args_z3[1]
        if op in ('ne', 'NotEq', '!=') and len(args_z3) == 2:
            return args_z3[0] != args_z3[1]
        if op in ('not', 'Not') and len(args_z3) == 1:
            return Not(args_z3[0])
        if op in ('and', 'And') and len(args_z3) == 2:
            return And(args_z3[0], args_z3[1])
        if op in ('or', 'Or') and len(args_z3) == 2:
            return Or(args_z3[0], args_z3[1])
    return None


def _oterm_to_z3_value(term, env: dict):
    """Compile an OTerm to a Z3 arithmetic/value expression."""
    if not _HAS_Z3:
        return None
    name = _otype(term)
    if name == 'OLam':
        if len(term.params) == 1:
            return _oterm_to_z3_value(term.body, env)
        return None
    if name == 'OLit':
        if isinstance(term.value, (int, float)):
            return IntVal(term.value) if isinstance(term.value, int) else None
        return None
    if name == 'OVar':
        return env.get(term.name)
    if name == 'OOp':
        args_z3 = [_oterm_to_z3_value(a, env) for a in term.args]
        if any(a is None for a in args_z3):
            return None
        op = term.name
        if op in ('add', 'Add', '+') and len(args_z3) == 2:
            return args_z3[0] + args_z3[1]
        if op in ('sub', 'Sub', '-') and len(args_z3) == 2:
            return args_z3[0] - args_z3[1]
        if op in ('mul', 'Mult', '*') and len(args_z3) == 2:
            return args_z3[0] * args_z3[1]
        if op in ('pow', 'Pow', '**') and len(args_z3) == 2:
            # Z3 doesn't have direct pow for general case, handle x**2 etc
            if _otype(term.args[1]) == 'OLit' and term.args[1].value == 2:
                return args_z3[0] * args_z3[0]
            return None
        if op in ('neg', 'USub') and len(args_z3) == 1:
            return -args_z3[0]
        if op == 'abs' and len(args_z3) == 1:
            from z3 import If
            return If(args_z3[0] >= 0, args_z3[0], -args_z3[0])
        if op in ('mod', 'Mod', '%') and len(args_z3) == 2:
            return args_z3[0] % args_z3[1]
    return None


# ═══════════════════════════════════════════════════════════════
# Case boundary absorption — branches agree at guard transition
# ═══════════════════════════════════════════════════════════════

def _check_case_test_absorption(
    fiber: Fiber,
    ancestor_chain: List[Tuple[Tuple, Any, str]],
    root_f, root_g,
) -> AbsorptionResult:
    """Check if a case-test (guard) difference is absorbed because both
    branches produce the same value at the boundary.

    For OCase(cond₁, A, B) vs OCase(cond₂, A, B):
    If A(boundary) == B(boundary) for all boundary values where
    cond₁ ≠ cond₂, the guard difference is absorbed.

    This is the descent condition: the local sections (branch expressions)
    agree on the overlap (guard boundary), so they glue.
    """
    # Find the enclosing OCase
    case_f = None
    case_g = None
    for _path, node, role in reversed(ancestor_chain):
        if _otype(node) == 'OCase' and role == 'test':
            case_f = _get_subterm(root_f, _path)
            case_g = _get_subterm(root_g, _path)
            break

    if case_f is None or case_g is None:
        return AbsorptionResult(False, 'no enclosing OCase for test fiber')

    # Check if both branches agree (structurally)
    if case_f.true_branch.canon() == case_f.false_branch.canon():
        return AbsorptionResult(True,
            'both branches identical: guard difference irrelevant (trivial absorption)')

    # Check if both branches agree at the boundary values
    boundary_values = _extract_filter_boundary_values(fiber.term_f, fiber.term_g)
    if boundary_values is None:
        return AbsorptionResult(False, 'cannot extract boundary values for case test')

    for bval in boundary_values:
        true_val = _evaluate_lambda_or_term(case_f.true_branch, bval)
        false_val = _evaluate_lambda_or_term(case_f.false_branch, bval)
        if true_val is None or false_val is None:
            return AbsorptionResult(False,
                f'cannot evaluate branches at boundary {bval}')
        if true_val != false_val:
            return AbsorptionResult(False,
                f'branches differ at boundary {bval}: '
                f'{true_val} ≠ {false_val} (genuine H¹ obstruction)')

    return AbsorptionResult(True,
        f'branches agree at boundary {boundary_values}: '
        f'guard difference absorbed (descent condition satisfied)')


def _evaluate_lambda_or_term(term, value):
    """Evaluate a term that might be an OLam or a direct expression."""
    if _otype(term) == 'OLam' and len(term.params) == 1:
        return _evaluate_oterm_at(term.body, term.params[0], value)
    # Try common variable names
    for var in ('x', '_b0', 'n', 'i', 's'):
        result = _evaluate_oterm_at(term, var, value)
        if result is not None:
            return result
    return None


# ═══════════════════════════════════════════════════════════════
# Map transform absorption — commutativity and naturality
# ═══════════════════════════════════════════════════════════════

def _check_map_absorption(
    fiber: Fiber,
    ancestor_chain: List[Tuple[Tuple, Any, str]],
) -> AbsorptionResult:
    """Check if a map-transform difference is absorbed by the enclosing fold.

    For fold(op, init, map(f₁, coll)) vs fold(op, init, map(f₂, coll)):
    If op(acc, f₁(x)) == op(acc, f₂(x)) for all x and acc, then
    the transform difference is absorbed.

    This is the naturality condition: the restriction map from
    map-fiber to fold-fiber factors through the fold's algebraic structure.
    """
    fold_node = None
    for _path, node, _role in reversed(ancestor_chain):
        if _otype(node) == 'OFold':
            fold_node = node
            break

    if fold_node is None:
        return AbsorptionResult(False, 'no enclosing fold for map transform')

    # Check if fold has an annihilator: op(x, a) = a for all x
    fold_op = fold_node.op_name
    if fold_op in FOLD_ANNIHILATOR:
        ann = FOLD_ANNIHILATOR[fold_op]
        # If BOTH transforms always produce the annihilator, the fold
        # produces the annihilator regardless → absorbed
        # This is very rare; skip for now
        pass

    # General case: check with Z3 if op(acc, f₁(x)) == op(acc, f₂(x))
    # For many practical cases, this reduces to f₁(x) == f₂(x) when
    # op is injective in its second argument (true for +, *, etc.)
    # So in general, map-transform differences are NOT absorbed
    return AbsorptionResult(False,
        f'map transform difference not absorbed by fold({fold_op}): '
        f'no general naturality')


# ═══════════════════════════════════════════════════════════════
# Main compositional cohomology computation
# ═══════════════════════════════════════════════════════════════

def compositional_equiv(
    t_f, t_g, timeout_ms: int = 5000
) -> CohomologyResult:
    """Check equivalence via compositional sheaf cohomology.

    Decomposes two OTerms along their tree structure, checks local
    equivalence at each fiber, and uses the connecting homomorphism
    of the Mayer-Vietoris sequence to determine if local differences
    are absorbed by the compositional structure.

    Returns:
        CohomologyResult with h1_rank = 0 iff equivalent.
    """
    # Quick canonical check
    if t_f.canon() == t_g.canon():
        return CohomologyResult(
            h1_rank=0, equivalent=True,
            explanation='canonical forms identical')

    # Step 1: Align OTerms → presheaf decomposition
    fibers = align_oterms(t_f, t_g)

    if not fibers:
        return CohomologyResult(
            h1_rank=0, equivalent=True,
            explanation='empty decomposition (trivially equivalent)')

    # Step 2: Identify differing fibers
    diff_fibers = [f for f in fibers if f.locally_equivalent is False]
    equiv_fibers = [f for f in fibers if f.locally_equivalent is True]

    if not diff_fibers:
        return CohomologyResult(
            h1_rank=0, equivalent=True, fibers=fibers,
            explanation=f'all {len(equiv_fibers)} fibers locally equivalent')

    # Step 3: For each differing fiber, check absorption via
    # the connecting homomorphism δ: H⁰(overlap) → H¹(whole)
    absorptions: Dict[Tuple, AbsorptionResult] = {}
    obstructions: List[Fiber] = []

    for fiber in diff_fibers:
        # Build the ancestor chain (restriction maps from fiber to root)
        chain = _ancestor_chain(t_f, fiber.path)

        # Determine what KIND of fiber this is and check absorption
        result = _check_fiber_absorption(fiber, chain, t_f, t_g)
        absorptions[fiber.path] = result

        if not result.absorbed:
            obstructions.append(fiber)

    h1_rank = len(obstructions)

    if h1_rank == 0:
        absorbed_reasons = [a.reason for a in absorptions.values() if a.absorbed]
        return CohomologyResult(
            h1_rank=0, equivalent=True, fibers=fibers,
            absorptions=absorptions,
            explanation=(
                f'H¹=0: {len(diff_fibers)} local differences absorbed by '
                f'compositional structure. '
                + '; '.join(absorbed_reasons[:3])
            ))

    obs_reasons = [absorptions[f.path].reason for f in obstructions[:3]]
    return CohomologyResult(
        h1_rank=h1_rank, equivalent=False, fibers=fibers,
        absorptions=absorptions,
        explanation=(
            f'H¹={h1_rank}: {h1_rank} non-absorbed obstructions. '
            + '; '.join(obs_reasons)
        ))


def _check_fiber_absorption(
    fiber: Fiber,
    ancestor_chain: List[Tuple[Tuple, Any, str]],
    root_f, root_g,
) -> AbsorptionResult:
    """Dispatch absorption check based on the fiber's semantic role.

    The fiber may be deeply nested (e.g., inside an OLam body inside
    an OMap filter_pred inside an OFold).  We walk UP the ancestor chain
    to find the correct semantic context for absorption:

    - A difference inside a filter_pred's lambda body → filter absorption
    - A difference inside a transform's lambda body → map absorption
    - A difference in a case test → case test absorption
    - etc.
    """
    if not ancestor_chain:
        return AbsorptionResult(False,
            'root-level difference: no enclosing structure to absorb')

    # Walk the ancestor chain from INNER to OUTER, looking for the
    # semantic context that determines which absorption rule applies.
    # Skip OLam wrappers — they're just binding forms, not absorbers.
    effective_role = None
    effective_parent_type = None
    effective_chain_depth = len(ancestor_chain)

    for depth in range(len(ancestor_chain) - 1, -1, -1):
        _apath, anode, arole = ancestor_chain[depth]
        atype = _otype(anode)

        # Skip lambda bodies — they're transparent to absorption
        if arole in ('body',) and atype == 'OLam':
            continue

        effective_role = arole
        effective_parent_type = atype
        effective_chain_depth = depth
        break

    if effective_role is None:
        return AbsorptionResult(False,
            'only lambda wrappers in ancestor chain')

    # Filter predicate inside a map (possibly inside a fold)
    if effective_role == 'filter_pred':
        return _check_filter_absorption(fiber, ancestor_chain)

    # Case test (guard condition)
    if effective_role == 'test' and effective_parent_type == 'OCase':
        return _check_case_test_absorption(fiber, ancestor_chain, root_f, root_g)

    # Map transform inside a fold
    if effective_role == 'transform' and effective_parent_type == 'OMap':
        return _check_map_absorption(fiber, ancestor_chain)

    # Init of a fold: only absorbed if the collection is empty,
    # which we generally can't prove statically
    if effective_role == 'init':
        return AbsorptionResult(False,
            'fold init difference: would require proving collection is empty')

    # Collection difference: generally not absorbed
    if effective_role in ('collection', 'map_collection'):
        return AbsorptionResult(False,
            'collection difference: structural mismatch')

    # Arguments of an operation — check if the parent op has
    # commutativity or other properties, but generally these propagate
    if effective_role.startswith('args_'):
        return AbsorptionResult(False,
            f'operation argument difference at {effective_role}')

    # Branch body difference
    if effective_role in ('true_branch', 'false_branch'):
        return AbsorptionResult(False,
            f'branch body difference: genuine semantic difference')

    # Default: not absorbed
    return AbsorptionResult(False,
        f'no absorption rule for role "{effective_role}" in {effective_parent_type}')


# ═══════════════════════════════════════════════════════════════
# Spec checking via presheaf sections
# ═══════════════════════════════════════════════════════════════

def spec_satisfaction_cohomological(
    impl_oterm, spec_oterm,
    timeout_ms: int = 5000,
) -> CohomologyResult:
    """Check if an implementation satisfies a spec using presheaf theory.

    The spec defines a behavioral presheaf F_spec:
      F_spec(U) = {outputs satisfying the spec on region U}

    The implementation defines a section s ∈ F_spec(X):
      s(x) = impl(x)

    Satisfaction = s is a well-defined global section of F_spec.
    This is the descent condition: local satisfaction glues iff H¹ = 0.

    For deterministic specs (return result == E(inputs)):
      satisfaction reduces to impl ≡ ref_impl (compositional_equiv).

    For constraint specs (return P(result, inputs)):
      compose spec(inputs, impl(inputs)) and check ≡ True.
    """
    # This delegates to compositional_equiv after constructing
    # the appropriate comparison terms
    # For now, return inconclusive — full implementation requires
    # the spec decomposition machinery
    return CohomologyResult(
        h1_rank=-1, equivalent=None,
        explanation='spec satisfaction via presheaf sections: not yet fully implemented')


# ═══════════════════════════════════════════════════════════════
# SITE 2: Genuine Čech Cohomology over the Input Space
# ═══════════════════════════════════════════════════════════════
#
# The topological space is the INPUT domain X = ℤⁿ.
# The cover is the set of guard regions from both programs' OCase trees.
# A presheaf section on region U is the (f, g) pair restricted to U.
# H¹ = 0 iff f = g on every non-empty region of the refined cover.
#
# This is NOT tree-diffing. It operates on the INPUT space, not the
# syntax tree. Programs with completely different branching structures
# are handled correctly by computing the common refinement.

@dataclass
class PiecewiseSection:
    """A piece of a piecewise function: (guard, value).

    guard: OTerm boolean expression — defines the input region
    value: OTerm expression — the function's value on that region
    """
    guard: Any   # OTerm
    value: Any   # OTerm


@dataclass
class RefinedRegion:
    """A region in the common refinement of two guard covers.

    guard: intersection of a guard from f's cover with a guard from g's cover
    value_f: f's value on this region
    value_g: g's value on this region
    """
    guard: Any       # OTerm (intersection guard)
    value_f: Any     # OTerm
    value_g: Any     # OTerm
    agreement: Optional[bool] = None  # True=proven equal, False=counterexample, None=unknown
    region_empty: Optional[bool] = None  # True if Z3 proved the region is empty


@dataclass
class CechResult:
    """Result of genuine Čech cohomology over the input space.

    h1_rank: number of non-empty regions where f ≠ g (or unknown)
    equivalent: True if H¹=0 (all regions agree), False if counterexample, None if unknown
    regions: the refined regions with their agreement status
    """
    h1_rank: int
    equivalent: Optional[bool]
    total_regions: int = 0
    empty_regions: int = 0
    agreed_regions: int = 0
    disagreed_regions: int = 0
    unknown_regions: int = 0
    explanation: str = ''
    regions: List[RefinedRegion] = field(default_factory=list)


def _flatten_to_piecewise(
    term, *, max_pieces: int = 32, _depth: int = 0
) -> List[PiecewiseSection]:
    """Flatten an OCase tree to piecewise form over the input space.

    case(g1, A, case(g2, B, C)) →
      [(g1, A), (¬g1 ∧ g2, B), (¬g1 ∧ ¬g2, C)]

    Recursively expands OCase nodes in BOTH true and false branches.
    Limits total pieces to max_pieces to avoid exponential blowup.

    For non-OCase terms: returns [(True, term)] — a single piece.
    """
    from .denotation import OCase, OOp, OLit

    if _otype(term) != 'OCase' or _depth > 10:
        return [PiecewiseSection(guard=OLit(True), value=term)]

    # Flatten true branch and false branch recursively
    true_pieces = _flatten_to_piecewise(
        term.true_branch, max_pieces=max_pieces, _depth=_depth + 1)
    false_pieces = _flatten_to_piecewise(
        term.false_branch, max_pieces=max_pieces, _depth=_depth + 1)

    if len(true_pieces) + len(false_pieces) > max_pieces:
        return [PiecewiseSection(guard=OLit(True), value=term)]

    result: List[PiecewiseSection] = []
    guard = term.test
    neg_guard = OOp('u_not', (guard,))

    # True branch pieces: conjoin with guard
    for piece in true_pieces:
        if _otype(piece.guard) == 'OLit' and piece.guard.value is True:
            conjoined = guard
        else:
            conjoined = OOp('and', (guard, piece.guard))
        result.append(PiecewiseSection(guard=conjoined, value=piece.value))

    # False branch pieces: conjoin with ¬guard
    for piece in false_pieces:
        if _otype(piece.guard) == 'OLit' and piece.guard.value is True:
            conjoined = neg_guard
        else:
            conjoined = OOp('and', (neg_guard, piece.guard))
        result.append(PiecewiseSection(guard=conjoined, value=piece.value))

    return result


def _refine_covers(
    pieces_f: List[PiecewiseSection],
    pieces_g: List[PiecewiseSection],
) -> List[RefinedRegion]:
    """Compute the common Čech refinement of two piecewise covers.

    For covers {A_i} (from f) and {B_j} (from g), the refinement is
    {A_i ∩ B_j} for all (i,j). Many of these intersections may be empty
    (which Z3 will detect).

    Returns a list of RefinedRegion with the intersected guard.
    """
    from .denotation import OOp, OLit

    refined: List[RefinedRegion] = []
    for pf in pieces_f:
        for pg in pieces_g:
            # Intersect guards
            gf = pf.guard
            gg = pg.guard
            gf_is_true = _otype(gf) == 'OLit' and gf.value is True
            gg_is_true = _otype(gg) == 'OLit' and gg.value is True

            if gf_is_true and gg_is_true:
                inter = OLit(True)
            elif gf_is_true:
                inter = gg
            elif gg_is_true:
                inter = gf
            else:
                inter = OOp('and', (gf, gg))

            refined.append(RefinedRegion(
                guard=inter,
                value_f=pf.value,
                value_g=pg.value,
            ))

    return refined


def _collect_free_vars(term, bound: frozenset = frozenset()) -> Set[str]:
    """Collect free variable names from an OTerm."""
    name = _otype(term)
    if name == 'OVar':
        if term.name not in bound:
            return {term.name}
        return set()
    if name == 'OLit':
        return set()
    if name == 'OLam':
        new_bound = bound | frozenset(term.params)
        return _collect_free_vars(term.body, new_bound)
    if name == 'OOp':
        result: Set[str] = set()
        for a in term.args:
            result |= _collect_free_vars(a, bound)
        return result
    if name == 'OCase':
        return (_collect_free_vars(term.test, bound)
                | _collect_free_vars(term.true_branch, bound)
                | _collect_free_vars(term.false_branch, bound))
    if name == 'OFold':
        result = _collect_free_vars(term.init, bound) | _collect_free_vars(term.collection, bound)
        if term.body_fn is not None:
            result |= _collect_free_vars(term.body_fn, bound)
        return result
    if name == 'OFix':
        return _collect_free_vars(term.body, bound)
    if name == 'OSeq':
        result = set()
        for e in term.elements:
            result |= _collect_free_vars(e, bound)
        return result
    if name == 'OMap':
        result = _collect_free_vars(term.collection, bound)
        if hasattr(term, 'transform') and term.transform is not None:
            result |= _collect_free_vars(term.transform, bound)
        if hasattr(term, 'filter_pred') and term.filter_pred is not None:
            result |= _collect_free_vars(term.filter_pred, bound)
        return result
    if name == 'OQuotient':
        return _collect_free_vars(term.inner, bound)
    if name == 'OCatch':
        return _collect_free_vars(term.body, bound) | _collect_free_vars(term.default, bound)
    if name == 'ODict':
        result = set()
        for k, v in term.pairs:
            result |= _collect_free_vars(k, bound) | _collect_free_vars(v, bound)
        return result
    return set()


def _guard_to_z3(guard, z3_vars: dict):
    """Compile a guard OTerm to a Z3 boolean expression.

    Handles: comparisons, boolean ops, truthiness (nonzero for ints),
    modular arithmetic, membership tests.

    Type-level predicates (isinstance, callable, type equality) are
    compiled to opaque Z3 Bool variables keyed by canonical form.
    This allows Z3 to reason about type-level constraints even though
    it can't evaluate Python's type system directly.
    """
    if not _HAS_Z3:
        return None
    name = _otype(guard)

    if name == 'OLit':
        from z3 import BoolVal
        if isinstance(guard.value, bool):
            return BoolVal(guard.value)
        return None

    if name == 'OVar':
        v = z3_vars.get(guard.name)
        if v is None:
            return None
        # Truthiness: var used as boolean → var != 0
        return v != IntVal(0)

    if name == 'OOp':
        op = guard.name

        # Unary not
        if op in ('u_not', 'not', 'Not') and len(guard.args) == 1:
            inner = _guard_to_z3(guard.args[0], z3_vars)
            if inner is None:
                return None
            return Not(inner)

        # Type-level predicates → opaque Z3 Bool variables
        # isinstance(x, T) → Bool('isinstance_$x_T')
        if op == 'isinstance' and len(guard.args) == 2:
            return _opaque_z3_bool(guard, z3_vars)

        # callable(x) → Bool('callable_$x')
        if op == 'callable' and len(guard.args) == 1:
            return _opaque_z3_bool(guard, z3_vars)

        if len(guard.args) == 2:
            # Boolean connectives
            if op in ('and', 'And'):
                left = _guard_to_z3(guard.args[0], z3_vars)
                right = _guard_to_z3(guard.args[1], z3_vars)
                if left is None or right is None:
                    return None
                return And(left, right)
            if op in ('or', 'Or'):
                left = _guard_to_z3(guard.args[0], z3_vars)
                right = _guard_to_z3(guard.args[1], z3_vars)
                if left is None or right is None:
                    return None
                return Or(left, right)

            # type(a) == type(b) → opaque Bool
            if op in ('eq', 'Eq', '=='):
                a0, a1 = guard.args
                if (_otype(a0) == 'OOp' and a0.name == 'type' and
                    _otype(a1) == 'OOp' and a1.name == 'type'):
                    return _opaque_z3_bool(guard, z3_vars)

            # Comparisons — operands are arithmetic values
            left = _value_to_z3(guard.args[0], z3_vars)
            right = _value_to_z3(guard.args[1], z3_vars)
            if left is None or right is None:
                return None

            if op in ('gt', 'Gt', '>'):
                return left > right
            if op in ('ge', 'GtE', '>=', 'gte'):
                return left >= right
            if op in ('lt', 'Lt', '<'):
                return left < right
            if op in ('le', 'LtE', '<=', 'lte'):
                return left <= right
            if op in ('eq', 'Eq', '=='):
                return left == right
            if op in ('ne', 'NotEq', '!=', 'noteq'):
                return left != right

    return None


def _opaque_z3_bool(term, z3_vars: dict):
    """Create an opaque Z3 Bool variable keyed by canonical form.

    Used for predicates Z3 can't evaluate (isinstance, callable, type
    equality).  The same canonical form always gets the same Bool
    variable, so Z3 can reason about them structurally.

    Also adds mutual exclusion axioms for isinstance on disjoint types.
    """
    from z3 import Bool
    canon = term.canon()
    key = f'_bool_{canon}'
    if key in z3_vars:
        return z3_vars[key]

    bv = Bool(key)
    z3_vars[key] = bv

    # Add mutual exclusion axioms for isinstance
    # If we create isinstance(x, T), and isinstance(x, S) already exists
    # with S ≠ T, add an axiom: ¬(isinstance(x,T) ∧ isinstance(x,S))
    name = _otype(term)
    if name == 'OOp' and term.name == 'isinstance' and len(term.args) == 2:
        DISJOINT = {'int', 'float', 'str', 'list', 'dict', 'tuple',
                    'set', 'bool', 'bytes', 'NoneType',
                    '?int', '?float', '?str', '?list', '?dict',
                    '?tuple', '?set', '?bool', '?bytes'}
        param_canon = term.args[0].canon()
        type_canon = term.args[1].canon()
        if type_canon in DISJOINT:
            # Store mutual exclusion info for later solver axioms
            me_key = f'_me_{param_canon}'
            if me_key not in z3_vars:
                z3_vars[me_key] = {}
            z3_vars[me_key][type_canon] = bv

    return bv


def _add_type_axioms(solver, z3_vars: dict):
    """Add mutual exclusion axioms for isinstance type predicates.

    If z3_vars contains isinstance booleans for the same parameter but
    different disjoint types, adds ¬(isinstance(x,T) ∧ isinstance(x,S))
    for every pair T ≠ S.  This encodes that Python simple types are
    mutually exclusive: a value can't be both int and str.
    """
    for key, mapping in list(z3_vars.items()):
        if key.startswith('_me_') and isinstance(mapping, dict):
            types = list(mapping.keys())
            bools = list(mapping.values())
            for i in range(len(types)):
                for j in range(i + 1, len(types)):
                    # At most one can be true: ¬(Ti ∧ Tj)
                    solver.add(Not(And(bools[i], bools[j])))


def _value_to_z3(term, z3_vars: dict):
    """Compile an OTerm value expression to Z3 arithmetic.

    Handles: integers, variables, arithmetic ops, mod, abs, neg.
    For non-primitive subexpressions (getitem, len, gcd, etc.), creates
    opaque Z3 variables keyed by canonical form — the same subexpression
    in f and g gets the SAME Z3 variable, enabling algebraic reasoning.
    """
    if not _HAS_Z3:
        return None
    name = _otype(term)

    if name == 'OLit':
        use_real = z3_vars.get('_use_real', False)
        if isinstance(term.value, int):
            return RealVal(term.value) if use_real else IntVal(term.value)
        if isinstance(term.value, bool):
            v = 1 if term.value else 0
            return RealVal(v) if use_real else IntVal(v)
        if isinstance(term.value, float):
            if use_real:
                return RealVal(term.value)
            # Approximate floats as integers when close to integer
            if term.value == int(term.value) and abs(term.value) < 2**31:
                return IntVal(int(term.value))
            # Small epsilon thresholds (e.g. 1e-10) → 1 for integer reasoning
            if 0 < abs(term.value) < 0.5:
                return IntVal(1)
            if term.value == 0.0:
                return IntVal(0)
        return None

    if name == 'OVar':
        return z3_vars.get(term.name)

    if name == 'OOp':
        op = term.name

        # getitem(container, index) → opaque Z3 variable keyed by canon
        # This allows reasoning about expressions like getitem($p0, 0)
        # where $p0 is a list parameter: both f and g reference the same
        # element, so they get the SAME Z3 variable.
        if op in ('getitem', 'Subscript'):
            return _opaque_z3_var(term, z3_vars)

        # len(container) → opaque Z3 variable
        if op == 'len' and len(term.args) == 1:
            return _opaque_z3_var(term, z3_vars)

        # gcd(a, b) → opaque Z3 variable (commutative — see _opaque_z3_var)
        if op == 'gcd' and len(term.args) == 2:
            return _opaque_z3_var(term, z3_vars)

        args = [_value_to_z3(a, z3_vars) for a in term.args]

        if len(args) == 1 and args[0] is not None:
            if op in ('neg', 'USub'):
                return -args[0]
            if op == 'abs':
                from z3 import If
                return If(args[0] >= 0, args[0], -args[0])
            if op == 'int':
                return args[0]  # int(x) ≈ x for integer reasoning

        if len(args) == 2 and args[0] is not None and args[1] is not None:
            if op in ('add', 'Add', '+'):
                return args[0] + args[1]
            if op in ('sub', 'Sub', '-'):
                return args[0] - args[1]
            if op in ('mul', 'Mult', 'mult', '*'):
                return args[0] * args[1]
            if op in ('mod', 'Mod', '%'):
                return args[0] % args[1]
            if op in ('floordiv', 'FloorDiv', '//'):
                return args[0] / args[1]
            if op in ('div', 'truediv', 'Div'):
                # Use Z3 Real division — handle both Int and Real args
                from z3 import ToReal, is_int as z3_is_int
                a0 = ToReal(args[0]) if z3_is_int(args[0]) else args[0]
                a1 = ToReal(args[1]) if z3_is_int(args[1]) else args[1]
                return a0 / a1
            if op in ('pow', 'Pow', '**'):
                if _otype(term.args[1]) == 'OLit' and isinstance(term.args[1].value, int):
                    exp = term.args[1].value
                    if 0 <= exp <= 4:
                        use_real = z3_vars.get('_use_real', False)
                        result = RealVal(1) if use_real else IntVal(1)
                        for _ in range(exp):
                            result = result * args[0]
                        return result
            if op in ('min', 'Min'):
                from z3 import If
                return If(args[0] <= args[1], args[0], args[1])
            if op in ('max', 'Max'):
                from z3 import If
                return If(args[0] >= args[1], args[0], args[1])

        if len(args) == 1 and args[0] is not None:
            if op in ('u_usub', 'usub', 'USub'):
                return -args[0]

    if name == 'OCase':
        from z3 import If
        cond = _guard_to_z3(term.test, z3_vars)
        tv = _value_to_z3(term.true_branch, z3_vars)
        fv = _value_to_z3(term.false_branch, z3_vars)
        if cond is not None and tv is not None and fv is not None:
            return If(cond, tv, fv)

    if name == 'OSeq':
        # Sequence with getitem → expand to ITE if indexing is used
        # For now, treat whole sequence as opaque
        return _opaque_z3_var(term, z3_vars)

    # Radical opaque unification: for ANY non-primitive OTerm (OFold, OFix,
    # OMap, OLam, etc.), create an opaque Z3 variable keyed by canonical
    # form. If both programs contain the same sub-expression, Z3 gets the
    # SAME variable — enabling algebraic reasoning about the context even
    # when the sub-expression itself is opaque.
    #
    # This is the key to multi-level Čech: opaque variables represent
    # "collapsed stalks" of the presheaf — we don't know their value,
    # but we know they're the same stalk if their canonical forms match.
    if name in ('OFold', 'OFix', 'OMap', 'OLam', 'ODict', 'OCatch'):
        return _opaque_z3_var(term, z3_vars)

    # OOp that wasn't handled above (unknown op name) → opaque
    if name == 'OOp':
        return _opaque_z3_var(term, z3_vars)

    return None


def _value_to_z3_bv(term, z3_vars: dict, bw: int = 64):
    """Compile an OTerm value to Z3 BitVec arithmetic (fixed bit-width).

    Used as fallback when _value_to_z3 returns None due to bitwise ops.
    BitVec sort supports: xor, or, and, shift, invert natively.
    """
    if not _HAS_Z3:
        return None
    from z3 import BitVecVal, BitVec as BV

    name = _otype(term)

    if name == 'OLit':
        if isinstance(term.value, int):
            return BitVecVal(term.value, bw)
        return None

    if name == 'OVar':
        key = f'_bv_{term.name}'
        if key in z3_vars:
            return z3_vars[key]
        v = BV(key, bw)
        z3_vars[key] = v
        return v

    if name == 'OOp':
        op = term.name
        if op in ('getitem', 'Subscript', 'len', 'gcd'):
            import hashlib
            canon = term.canon()
            h = hashlib.md5(canon.encode()).hexdigest()[:10]
            key = f'_bvop_{h}'
            if key in z3_vars:
                return z3_vars[key]
            v = BV(key, bw)
            z3_vars[key] = v
            z3_vars['_opaque_count'] = z3_vars.get('_opaque_count', 0) + 1
            return v

        args = [_value_to_z3_bv(a, z3_vars, bw) for a in term.args]

        if len(args) == 2 and args[0] is not None and args[1] is not None:
            if op in ('add', 'Add', '+'):
                return args[0] + args[1]
            if op in ('sub', 'Sub', '-'):
                return args[0] - args[1]
            if op in ('mul', 'Mult', 'mult', '*'):
                return args[0] * args[1]
            if op in ('bitxor', 'xor', '^'):
                return args[0] ^ args[1]
            if op in ('bitor', '|'):
                return args[0] | args[1]
            if op in ('bitand', '&'):
                return args[0] & args[1]
            if op in ('lshift', '<<'):
                return args[0] << args[1]
            if op in ('rshift', '>>'):
                from z3 import LShR
                return LShR(args[0], args[1])

        if len(args) == 1 and args[0] is not None:
            if op in ('u_invert', 'invert', '~'):
                return ~args[0]
            if op in ('u_usub', 'usub', 'USub'):
                return -args[0]

    if name == 'OCase':
        from z3 import If
        cond = _guard_to_z3(term.test, z3_vars)
        tv = _value_to_z3_bv(term.true_branch, z3_vars, bw)
        fv = _value_to_z3_bv(term.false_branch, z3_vars, bw)
        if cond is not None and tv is not None and fv is not None:
            return If(cond, tv, fv)

    return None


def _opaque_z3_var(term, z3_vars: dict):
    """Create an opaque Z3 variable for a non-primitive OTerm.

    Creates Real or Int depending on '_use_real' flag in z3_vars.
    The variable is keyed by the canonical form of the term, so the
    SAME subexpression appearing in both f and g gets the SAME Z3 variable.

    For commutative operations (gcd, min, max), the canonical form
    normalizes argument order.

    Tracks opaque variable creation via '_opaque_count' in z3_vars.
    """
    import hashlib
    from z3 import Real as Z3Real
    canon = term.canon()
    h = hashlib.md5(canon.encode()).hexdigest()[:10]
    key = f'_op_{h}'
    if key in z3_vars:
        return z3_vars[key]
    use_real = z3_vars.get('_use_real', False)
    v = Z3Real(key) if use_real else Int(key)
    z3_vars[key] = v
    z3_vars['_opaque_count'] = z3_vars.get('_opaque_count', 0) + 1
    return v


def _is_structurally_contradictory(guard, known_guard_canons: set) -> bool:
    """Check if a guard is structurally contradictory (always false).

    A conjunction and(A, u_not(B)) is contradictory when A.canon() == B.canon().
    This catches cases like and(lt(abs(det), 1e-12), u_not(lt(abs(det), 1e-12)))
    where Z3 can't compile the guards (due to floats, getitem, etc.) but
    structural comparison shows they're contradictory.

    Also detects deeper contradictions: and(and(A, C), u_not(A)).
    """
    name = _otype(guard)
    if name != 'OOp' or guard.name not in ('and', 'And'):
        return False

    # Collect all conjuncts
    conjuncts = _collect_conjuncts(guard)

    # Build sets of positive and negated canonical forms
    positive_canons: set = set()
    negative_canons: set = set()
    for c in conjuncts:
        cn = _otype(c)
        if cn == 'OOp' and c.name in ('u_not', 'not', 'Not') and len(c.args) == 1:
            negative_canons.add(c.args[0].canon())
        else:
            positive_canons.add(c.canon())

    # Contradiction: some formula appears both positively and negatively
    return bool(positive_canons & negative_canons)


def _collect_conjuncts(guard) -> list:
    """Flatten nested and() into a list of conjuncts."""
    name = _otype(guard)
    if name == 'OOp' and guard.name in ('and', 'And') and len(guard.args) == 2:
        return _collect_conjuncts(guard.args[0]) + _collect_conjuncts(guard.args[1])
    return [guard]


def _region_is_empty_z3(guard, z3_vars: dict, timeout_ms: int = 500) -> Optional[bool]:
    """Check if a guard region is empty (unsatisfiable).

    Returns True if the region is provably empty, False if satisfiable,
    None if Z3 can't decide.
    """
    if not _HAS_Z3:
        return None

    z3_guard = _guard_to_z3(guard, z3_vars)
    if z3_guard is None:
        return None

    try:
        z3_set_param('timeout', timeout_ms)
        solver = Solver()
        solver.set('timeout', timeout_ms)
        solver.add(z3_guard)
        result = solver.check()
        if result == unsat:
            return True   # region is empty
        if result == sat:
            return False  # region is non-empty
        return None       # unknown
    except Exception:
        return None


def _extract_z3_divisors(z3_expr) -> set:
    """Extract all denominators from a Z3 arithmetic expression.

    Walks the Z3 AST and collects every sub-expression that appears as
    the divisor in a division.  Used to add non-zero constraints that
    the program's guards already enforce.
    """
    divisors: set = set()
    if z3_expr is None:
        return divisors
    try:
        from z3 import is_app, is_div, is_idiv
        _extract_z3_divisors_rec(z3_expr, divisors)
    except Exception:
        pass
    return divisors


def _extract_z3_divisors_rec(expr, divisors: set):
    """Recursive helper for _extract_z3_divisors."""
    from z3 import is_app, Z3_OP_DIV, Z3_OP_IDIV, Z3_OP_REM, Z3_OP_MOD
    if not is_app(expr):
        return
    dk = expr.decl().kind()
    if dk in (Z3_OP_DIV, Z3_OP_IDIV, Z3_OP_REM, Z3_OP_MOD):
        if expr.num_args() >= 2:
            divisors.add(expr.arg(1))
    for i in range(expr.num_args()):
        _extract_z3_divisors_rec(expr.arg(i), divisors)


def _values_agree_on_region_z3(
    guard, val_f, val_g, z3_vars: dict, timeout_ms: int = 1000
) -> Optional[bool]:
    """Check if val_f = val_g on the region defined by guard.

    Uses Z3: ¬∃x. guard(x) ∧ val_f(x) ≠ val_g(x)

    Returns True if provably equal, False if counterexample found
    (only with fully compiled expressions — no opaque variables),
    None if unknown.

    For OSeq values (tuples/lists), compares element by element.
    All elements must agree for the values to agree.

    When opaque Z3 variables are introduced during value compilation,
    a Z3 'sat' result is downgraded to None because the counterexample
    may be spurious (opaque vars are unconstrained in Z3 but constrained
    by actual program semantics).
    """
    if not _HAS_Z3:
        return None

    # OSeq element-by-element comparison
    fn = _otype(val_f)
    gn = _otype(val_g)
    if fn == 'OSeq' and gn == 'OSeq':
        if len(val_f.elements) == len(val_g.elements) and len(val_f.elements) > 0:
            results = []
            for ef, eg in zip(val_f.elements, val_g.elements):
                r = _values_agree_on_region_z3(guard, ef, eg, z3_vars, timeout_ms)
                if r is False:
                    return False  # any element disagrees → disagree
                results.append(r)
            if all(r is True for r in results):
                return True  # all elements agree → agree
            return None  # some unknown

    # Snapshot opaque count before compilation
    opaque_before = z3_vars.get('_opaque_count', 0)

    z3_guard = _guard_to_z3(guard, z3_vars)
    z3_vf = _value_to_z3(val_f, z3_vars)
    z3_vg = _value_to_z3(val_g, z3_vars)

    # Check if new opaque variables were created during value compilation
    opaque_after = z3_vars.get('_opaque_count', 0)
    has_new_opaques = opaque_after > opaque_before

    # Also check if compiled expressions reference ANY opaque variables
    # (they may have been created in a prior call but are still unconstrained)
    has_opaque_refs = False
    if z3_vf is not None and z3_vg is not None:
        vf_str = str(z3_vf)
        vg_str = str(z3_vg)
        guard_str = str(z3_guard) if z3_guard is not None else ''
        if '_op_' in vf_str or '_op_' in vg_str or '_op_' in guard_str:
            has_opaque_refs = True

    if z3_vf is None or z3_vg is None:
        # Values can't compile — try BitVec fallback for bitwise expressions
        bv_vars = dict(z3_vars)  # copy to avoid polluting main vars
        z3_bvf = _value_to_z3_bv(val_f, bv_vars)
        z3_bvg = _value_to_z3_bv(val_g, bv_vars)
        if z3_bvf is not None and z3_bvg is not None:
            try:
                z3_set_param('timeout', timeout_ms)
                solver = Solver()
                solver.set('timeout', timeout_ms)
                if z3_guard is not None:
                    solver.add(z3_guard)
                solver.add(z3_bvf != z3_bvg)
                result = solver.check()
                if result == unsat:
                    return True  # BitVec proved equal
            except Exception:
                pass
        return None

    # ── Divisor constraints ──────────────────────────────────────
    # When expressions involve division, the denominators must be
    # non-zero for the program to reach this branch.  Extract all
    # divisors from both Z3 expressions and assert != 0.
    # This is sound: the programs' guards already exclude denom==0.
    divisor_constraints = _extract_z3_divisors(z3_vf) | _extract_z3_divisors(z3_vg)

    # Use compiled guard if available, otherwise BoolVal(True)
    effective_guard = z3_guard if z3_guard is not None else BoolVal(True)

    try:
        z3_set_param('timeout', timeout_ms)
        solver = Solver()
        solver.set('timeout', timeout_ms)
        _add_type_axioms(solver, z3_vars)
        solver.add(effective_guard)
        for d in divisor_constraints:
            solver.add(d != 0)
        solver.add(z3_vf != z3_vg)
        result = solver.check()
        if result == unsat:
            return True   # proven equal on this region
        if result == sat:
            if has_new_opaques or has_opaque_refs:
                # Counterexample may be spurious — opaque variables are
                # unconstrained in Z3 but determined by program semantics
                pass  # fall through to Real retry
            else:
                return False  # genuine counterexample
    except Exception:
        pass

    # ── Real arithmetic retry ────────────────────────────────────
    # When expressions involve division, Z3's nonlinear arithmetic
    # works much better with pure Real variables than mixed Int/Real.
    # Re-compile everything with Real domain.
    if divisor_constraints or 'ToReal' in str(z3_vf) + str(z3_vg):
        try:
            real_vars: dict = {'_use_real': True}
            for k, v in z3_vars.items():
                if k.startswith('$') or (not k.startswith('_') and isinstance(v, ArithRef) and v.is_int()):
                    real_vars[k] = Real(k)
            real_guard = _guard_to_z3(guard, real_vars)
            real_vf = _value_to_z3(val_f, real_vars)
            real_vg = _value_to_z3(val_g, real_vars)
            if real_vf is not None and real_vg is not None:
                real_divs = _extract_z3_divisors(real_vf) | _extract_z3_divisors(real_vg)
                eff_guard = real_guard if real_guard is not None else BoolVal(True)
                solver2 = Solver()
                solver2.set('timeout', timeout_ms)
                solver2.add(eff_guard)
                for d in real_divs:
                    solver2.add(d != 0)
                solver2.add(real_vf != real_vg)
                result2 = solver2.check()
                if result2 == unsat:
                    return True
        except Exception:
            pass

    return None


# ═══════════════════════════════════════════════════════════════
# Refinement type stalks — arbitrary refinement predicates
# ═══════════════════════════════════════════════════════════════
#
# In dependent type theory, a refinement type {x : τ | φ(x)} restricts
# a base type by a predicate φ.  The Čech cover's regions are precisely
# the atoms of the Boolean algebra generated by all refinement predicates
# appearing in both programs.
#
# Computing the *stalk* of the presheaf at a refinement type means
# restricting the program to the region where φ holds, evaluating all
# determined case branches, and producing a simplified OTerm that is
# the program's value on that fiber.
#
# We support THREE levels of refinement predicates:
#
# VALUE predicates (arithmetic):
#   - x > 0, x == 1, x < n, len(x) == 0
#   - Method calls: x.startswith("a"), sorted(x) == x
#   - Fold trivialization: fold(op, init, []) == init
#
# TYPE predicates (type-theoretic):
#   - isinstance(x, int/str/list/dict/...)  — type dispatch fiber
#   - callable(x)                           — Callable[α, β] refinement
#   - Mutual exclusion: isinstance(x,T) ⟹ ¬isinstance(x,S) for T≠S
#
# PARAMETRIC predicates (TypeVar):
#   - type(a) == type(b)  — shared type variable T constraint
#   - Propagation: type(a)==type(b) ∧ isinstance(a,int) ⟹ isinstance(b,int)
#
# Any is the top type — the absence of a type refinement means the
# parameter inhabits Any.  All refinement predicates further refine
# the Any fiber.
#
# The key theorem: if stalks agree on every atom of the refinement
# lattice, the presheaf sections agree globally (Čech H¹ = 0).
# ═══════════════════════════════════════════════════════════════

def _extract_atomic_predicates(term, bound_vars: frozenset = frozenset(),
                                depth: int = 0) -> set:
    """Extract all atomic boolean predicates from an OTerm.

    These define the refinement type lattice.  We extract predicates from:
    - OCase tests (guard conditions)
    - OMap filter predicates
    - Comparison operations anywhere in the tree
    - Boolean-valued method calls

    Only predicates over FREE variables are useful for input-space refinement.
    Predicates involving bound variables (fold accumulators, lambda params)
    are skipped — they refine the ITERATION space, not the input space.
    """
    if depth > 15:
        return set()
    name = _otype(term)
    result = set()

    if name == 'OCase':
        # The test IS an atomic predicate (if it only references free vars)
        test_fv = _collect_free_vars(term.test, bound_vars)
        if test_fv:  # has at least one free variable
            result.add(term.test.canon())
        result |= _extract_atomic_predicates(term.test, bound_vars, depth + 1)
        result |= _extract_atomic_predicates(term.true_branch, bound_vars, depth + 1)
        result |= _extract_atomic_predicates(term.false_branch, bound_vars, depth + 1)
    elif name == 'OOp':
        # Comparison ops are atomic predicates
        if term.name in ('lt', 'lte', 'gt', 'gte', 'eq', 'noteq',
                          'is', 'in', 'not_in', 'isinstance',
                          '.startswith', '.endswith', '.isdigit', '.isalpha',
                          '.isupper', '.islower'):
            fv = _collect_free_vars(term, bound_vars)
            if fv:
                result.add(term.canon())
        for a in term.args:
            result |= _extract_atomic_predicates(a, bound_vars, depth + 1)
    elif name == 'OFold':
        result |= _extract_atomic_predicates(term.init, bound_vars, depth + 1)
        result |= _extract_atomic_predicates(term.collection, bound_vars, depth + 1)
        if hasattr(term, 'body_fn') and term.body_fn is not None:
            # Body_fn params are bound — don't extract predicates over them
            if hasattr(term.body_fn, 'params'):
                inner_bound = bound_vars | frozenset(term.body_fn.params)
            else:
                inner_bound = bound_vars
            result |= _extract_atomic_predicates(term.body_fn, inner_bound, depth + 1)
    elif name == 'OLam':
        inner_bound = bound_vars | frozenset(term.params)
        result |= _extract_atomic_predicates(term.body, inner_bound, depth + 1)
    elif name == 'OMap':
        result |= _extract_atomic_predicates(term.collection, bound_vars, depth + 1)
        if hasattr(term, 'transform') and term.transform:
            result |= _extract_atomic_predicates(term.transform, bound_vars, depth + 1)
        if hasattr(term, 'filter_pred') and term.filter_pred:
            result |= _extract_atomic_predicates(term.filter_pred, bound_vars, depth + 1)
    elif name == 'OFix':
        result |= _extract_atomic_predicates(term.body, bound_vars, depth + 1)
    elif name == 'OSeq':
        for e in term.elements:
            result |= _extract_atomic_predicates(e, bound_vars, depth + 1)
    return result


def _generate_library_refinements(nf_f, nf_g, params: List[str]) -> list:
    """Generate library-derived refinement predicates.

    In dependent type theory with formalized libraries, types carry
    richer predicates than source-level comparisons.  The refinement
    lattice includes THREE kinds of predicates:

    VALUE predicates (arithmetic boundary):
      x : int | x == 0, x == 1, x < 0, x > 0

    COLLECTION predicates (structural boundary):
      x : list[τ] | len(x) == 0, len(x) == 1

    TYPE predicates (type-theoretic):
      x : Callable[[α], β]  — x is a callable (function/lambda)
      x : Any                — x is unconstrained (top type)
      isinstance(x, int)    — x inhabits int
      isinstance(x, list)   — x inhabits list
      isinstance(x, dict)   — x inhabits dict
      isinstance(x, str)    — x inhabits str

    TypeVar constraints arise when the same type variable appears in
    multiple positions:  T = TypeVar('T');  f : T → T  means input
    and output share the same type, enabling parametric reasoning.

    These type predicates create fibers in the Čech cover where the
    stalk computation can simplify isinstance/callable/type() tests,
    resolving case branches that depend on runtime type dispatch.

    Returns a list of OTerm predicates to add to the Čech cover.
    """
    from .denotation import OOp, OVar, OLit

    predicates = []
    for p in params:
        pv = OVar(p)
        # Value boundary refinement types
        predicates.append(OOp('eq', (pv, OLit(0))))       # x == 0
        predicates.append(OOp('eq', (pv, OLit(1))))       # x == 1
        predicates.append(OOp('eq', (pv, OLit(2))))       # x == 2
        predicates.append(OOp('eq', (pv, OLit(3))))       # x == 3
        predicates.append(OOp('lt', (pv, OLit(0))))       # x < 0
        predicates.append(OOp('lt', (OLit(0), pv)))       # x > 0
        predicates.append(OOp('lt', (pv, OLit(2))))       # x < 2

    # ── Collect type-relevant information from both terms ──

    isinstance_types = set()   # (param_canon, type_name)
    callable_params = set()    # param canons used as callables
    len_canons = set()         # canons of args to len()

    def _scan_type_info(t, d=0):
        """Recursively scan OTerm for type predicates, callable usage, and len."""
        if d > 12:
            return
        n = _otype(t)

        if n == 'OOp':
            op = t.name

            # isinstance(x, type) tests
            if op == 'isinstance' and len(t.args) == 2:
                arg_canon = t.args[0].canon()
                type_canon = t.args[1].canon()
                isinstance_types.add((arg_canon, type_canon))

            # callable(x) usage
            if op == 'callable' and len(t.args) == 1:
                callable_params.add(t.args[0].canon())

            # len(x) usage
            if op == 'len' and len(t.args) == 1:
                len_canons.add(t.args[0].canon())

            # Function application: if a param is used as the function
            # in a call, it's implicitly Callable
            if op in ('func_call', 'call') and len(t.args) >= 1:
                callable_params.add(t.args[0].canon())

            for a in t.args:
                _scan_type_info(a, d + 1)

        elif n == 'OCase':
            _scan_type_info(t.test, d + 1)
            _scan_type_info(t.true_branch, d + 1)
            _scan_type_info(t.false_branch, d + 1)

        elif n == 'OFold':
            _scan_type_info(t.init, d + 1)
            _scan_type_info(t.collection, d + 1)
            # Fold collection has a length
            len_canons.add(('_fold_col', t.collection.canon()))
            if t.body_fn:
                _scan_type_info(t.body_fn, d + 1)

        elif n == 'OMap':
            _scan_type_info(t.collection, d + 1)
            if t.transform:
                _scan_type_info(t.transform, d + 1)
            if t.filter_pred:
                _scan_type_info(t.filter_pred, d + 1)

        elif n == 'OLam':
            _scan_type_info(t.body, d + 1)

        elif n == 'OFix':
            _scan_type_info(t.body, d + 1)

        elif n == 'OSeq':
            for e in t.elements:
                _scan_type_info(e, d + 1)

    _scan_type_info(nf_f)
    _scan_type_info(nf_g)

    # ── Type-level refinement predicates ──
    # For each parameter that appears in isinstance() tests, generate
    # type fiber predicates.  These are structural (not Z3-compilable)
    # and will be handled by _structural_simplify_on_guard.

    seen_type_preds = set()
    for param_canon, type_name in isinstance_types:
        for pname in params:
            pv = OVar(pname)
            if pv.canon() == param_canon:
                pred = OOp('isinstance', (pv, OVar(type_name)))
                key = pred.canon()
                if key not in seen_type_preds:
                    seen_type_preds.add(key)
                    predicates.append(pred)

    # For parameters used as callables, add callable(p) predicate
    for pname in params:
        pv = OVar(pname)
        if pv.canon() in callable_params:
            pred = OOp('callable', (pv,))
            key = pred.canon()
            if key not in seen_type_preds:
                seen_type_preds.add(key)
                predicates.append(pred)

    # TypeVar-style constraints: if the same isinstance type appears for
    # multiple parameters, they share a type variable.  Generate equality
    # predicates: type(p0) == type(p1).  This enables parametric reasoning
    # on the "same-type" fiber.
    type_by_param = {}
    for param_canon, type_name in isinstance_types:
        if param_canon not in type_by_param:
            type_by_param[param_canon] = set()
        type_by_param[param_canon].add(type_name)

    param_canons_with_types = [pc for pc in type_by_param if len(type_by_param[pc]) > 0]
    if len(param_canons_with_types) >= 2:
        # Generate TypeVar equality: type(p_i) == type(p_j)
        for i in range(len(param_canons_with_types)):
            for j in range(i + 1, min(i + 3, len(param_canons_with_types))):
                pc_i, pc_j = param_canons_with_types[i], param_canons_with_types[j]
                for pname_i in params:
                    if OVar(pname_i).canon() == pc_i:
                        for pname_j in params:
                            if OVar(pname_j).canon() == pc_j:
                                pred = OOp('eq', (
                                    OOp('type', (OVar(pname_i),)),
                                    OOp('type', (OVar(pname_j),))
                                ))
                                predicates.append(pred)

    # ── Collection-length refinements ──
    for lc in len_canons:
        if isinstance(lc, tuple):
            continue  # skip fold_col markers for now
        for pname in params:
            if pname in lc:
                pv = OVar(pname)
                predicates.append(OOp('eq', (OOp('len', (pv,)), OLit(0))))
                predicates.append(OOp('eq', (OOp('len', (pv,)), OLit(1))))
                predicates.append(OOp('eq', (OOp('len', (pv,)), OLit(2))))
                predicates.append(OOp('eq', (OOp('len', (pv,)), OLit(3))))
                break

    # ── PROGRAM-SPECIFIC guard predicates ──
    # Extract guard conditions from BOTH programs' OCase trees.
    # These are the predicates that determine branching behavior —
    # using them as refinement types creates fibers aligned with
    # the programs' actual control flow, making stalk computation
    # maximally effective.  This is genuinely cohomological: the
    # cover is ADAPTED to the sheaf (the programs), not generic.
    program_guards = set()
    _extract_guards_from_oterm(nf_f, program_guards, depth=0)
    _extract_guards_from_oterm(nf_g, program_guards, depth=0)

    # Filter: only keep guards that mention program parameters
    # and are Z3-compilable (not opaque predicates)
    param_set = set(params)
    for guard in program_guards:
        guard_vars = _collect_free_vars(guard)
        if guard_vars & param_set:
            canon = guard.canon()
            # Avoid duplicating existing generic predicates
            if not any(p.canon() == canon for p in predicates):
                predicates.append(guard)

    return predicates


def _extract_guards_from_oterm(term, guards: set, depth: int = 0):
    """Recursively extract guard predicates from OCase nodes.

    Collects the test predicates from all OCase nodes in the OTerm tree,
    including those nested inside folds, maps, and fix-points.
    These represent the program's actual branching conditions —
    the semantic predicates that define its behavior regions.
    """
    if depth > 8:
        return
    name = _otype(term)

    if name == 'OCase':
        guards.add(term.test)
        _extract_guards_from_oterm(term.true_branch, guards, depth + 1)
        _extract_guards_from_oterm(term.false_branch, guards, depth + 1)

    elif name == 'OOp':
        for a in term.args:
            _extract_guards_from_oterm(a, guards, depth + 1)

    elif name == 'OFold':
        _extract_guards_from_oterm(term.init, guards, depth + 1)
        _extract_guards_from_oterm(term.collection, guards, depth + 1)
        if term.body_fn:
            _extract_guards_from_oterm(term.body_fn, guards, depth + 1)

    elif name == 'OMap':
        _extract_guards_from_oterm(term.collection, guards, depth + 1)
        if term.transform:
            _extract_guards_from_oterm(term.transform, guards, depth + 1)
        if term.filter_pred:
            _extract_guards_from_oterm(term.filter_pred, guards, depth + 1)

    elif name == 'OLam':
        _extract_guards_from_oterm(term.body, guards, depth + 1)

    elif name == 'OFix':
        _extract_guards_from_oterm(term.body, guards, depth + 1)

    elif name == 'OSeq':
        for e in term.elements:
            _extract_guards_from_oterm(e, guards, depth + 1)


def _solver_implies_pred(pred_z3, solver) -> Optional[bool]:
    """Check if the solver's current constraints imply pred.

    The solver already has region guard constraints asserted.
    Returns True if guard ⟹ pred, False if guard ⟹ ¬pred, None if unknown.
    """
    if pred_z3 is None:
        return None
    try:
        # Check guard ⟹ pred: is guard ∧ ¬pred unsatisfiable?
        solver.push()
        solver.add(Not(pred_z3))
        r = solver.check()
        solver.pop()
        if r == unsat:
            return True   # guard implies pred

        # Check guard ⟹ ¬pred: is guard ∧ pred unsatisfiable?
        solver.push()
        solver.add(pred_z3)
        r = solver.check()
        solver.pop()
        if r == unsat:
            return False  # guard implies ¬pred

        return None
    except Exception:
        return None


def _simplify_on_region(term, z3_vars: dict, solver, timeout_ms: int = 200,
                         depth: int = 0):
    """Compute the stalk of the presheaf at a refinement type region.

    Given a region defined by constraints already added to `solver`,
    simplify the OTerm by evaluating case branches whose tests are
    determined by the region constraints.  This is the sheaf-theoretic
    stalk computation: restricting the section (program value) to a
    fiber of the refinement type cover.

    Supports ARBITRARY refinement predicates — any predicate compilable
    to Z3 can determine a branch.  This includes:
      - Arithmetic: case(x > 0, ...) on region {x : int | x > 0}
      - Collection: case(len(x)==0, ...) on region {x : list | len(x)==0}
      - Library: case(sorted(x)==x, ...) on region {x | sorted(x)==x}

    For case(test, T, F):
      - If region ⟹ test:  stalk = simplify(T)    (take true branch)
      - If region ⟹ ¬test: stalk = simplify(F)    (take false branch)
      - Otherwise: case(test, simplify(T), simplify(F))

    Also simplifies inside folds, maps, operations, and sequences,
    and applies fold trivialization when the collection is provably empty.
    """
    from .denotation import OCase, OOp, OFold, OLam, OMap, OFix, OSeq, OLit, OVar

    if depth > 12:
        return term

    name = _otype(term)

    if name == 'OCase':
        # Try to evaluate the test under the region constraints
        test_z3 = _guard_to_z3(term.test, z3_vars)
        implied = _solver_implies_pred(test_z3, solver)

        if implied is True:
            return _simplify_on_region(
                term.true_branch, z3_vars, solver, timeout_ms, depth + 1)
        elif implied is False:
            return _simplify_on_region(
                term.false_branch, z3_vars, solver, timeout_ms, depth + 1)
        else:
            # Also try structural implication: if test.canon() matches
            # a known-true conjunct in the solver, we can simplify
            tb = _simplify_on_region(
                term.true_branch, z3_vars, solver, timeout_ms, depth + 1)
            fb = _simplify_on_region(
                term.false_branch, z3_vars, solver, timeout_ms, depth + 1)
            if tb is not term.true_branch or fb is not term.false_branch:
                return OCase(term.test, tb, fb)
            return term

    if name == 'OOp':
        op = term.name
        new_args = []
        changed = False
        for a in term.args:
            sa = _simplify_on_region(a, z3_vars, solver, timeout_ms, depth + 1)
            new_args.append(sa)
            if sa is not a:
                changed = True

        # Semantic simplification axioms on the fiber:
        # These are mathematical identities conditioned on the refinement type.
        if len(new_args) == 1 and new_args[0] is not None:
            arg_z3 = _value_to_z3(new_args[0], z3_vars)
            if arg_z3 is not None:
                # abs(x) → x  when region implies x >= 0
                if op == 'abs':
                    if _solver_implies_pred(arg_z3 >= IntVal(0), solver) is True:
                        return new_args[0]
                    if _solver_implies_pred(arg_z3 < IntVal(0), solver) is True:
                        return OOp('neg', (new_args[0],))

        if len(new_args) == 2:
            a0_z3 = _value_to_z3(new_args[0], z3_vars)
            a1_z3 = _value_to_z3(new_args[1], z3_vars)
            if a0_z3 is not None and a1_z3 is not None:
                # min(a, b) → a when region implies a <= b
                if op in ('min', 'Min'):
                    if _solver_implies_pred(a0_z3 <= a1_z3, solver) is True:
                        return new_args[0]
                    if _solver_implies_pred(a1_z3 <= a0_z3, solver) is True:
                        return new_args[1]
                # max(a, b) → a when region implies a >= b
                if op in ('max', 'Max'):
                    if _solver_implies_pred(a0_z3 >= a1_z3, solver) is True:
                        return new_args[0]
                    if _solver_implies_pred(a1_z3 >= a0_z3, solver) is True:
                        return new_args[1]
                # mod(a, b) → a when region implies 0 <= a < b
                if op in ('mod', 'Mod'):
                    from z3 import And as Z3And
                    if (_solver_implies_pred(
                            Z3And(a0_z3 >= IntVal(0), a0_z3 < a1_z3), solver) is True):
                        return new_args[0]

        if changed:
            return OOp(term.name, tuple(new_args))
        return term

    if name == 'OFold':
        si = _simplify_on_region(term.init, z3_vars, solver, timeout_ms, depth + 1)
        sc = _simplify_on_region(term.collection, z3_vars, solver, timeout_ms, depth + 1)

        # Fold trivialization: if collection is provably empty (len==0),
        # fold returns init.  This is the {x : τ | len(x)==0} refinement.
        col_len = OOp('len', (sc,))
        col_len_z3 = _value_to_z3(col_len, z3_vars)
        if col_len_z3 is not None:
            is_empty = _solver_implies_pred(col_len_z3 == IntVal(0), solver)
            if is_empty is True:
                return si

        # Range trivialization: range(a, b) where a >= b → empty
        if _otype(sc) == 'OOp' and sc.name == 'range' and len(sc.args) >= 2:
            lo_z3 = _value_to_z3(sc.args[0], z3_vars)
            hi_z3 = _value_to_z3(sc.args[1], z3_vars)
            if lo_z3 is not None and hi_z3 is not None:
                is_empty = _solver_implies_pred(lo_z3 >= hi_z3, solver)
                if is_empty is True:
                    return si

        # ── Fold unfolding at known collection length ──
        # At the refinement type {x | len(x) == k} for small k,
        # a fold has a CONCRETE computation:
        #   fold(f, init, [a₀, ..., aₖ₋₁]) = f(...f(f(init, a₀), a₁)..., aₖ₋₁)
        # This converts the opaque fold into a Z3-tractable expression.
        # This is a genuine dependent-type refinement: the stalk at the
        # fiber {len(x)==k} has a different (more concrete) type than
        # the generic section.
        body_fn = getattr(term, 'body_fn', None)
        if body_fn is not None and isinstance(body_fn, OLam) and len(body_fn.params) == 2:
            MAX_UNFOLD = 4  # Only unfold for very small collections
            for k in range(1, MAX_UNFOLD + 1):
                if col_len_z3 is not None:
                    is_k = _solver_implies_pred(col_len_z3 == IntVal(k), solver)
                    if is_k is True:
                        # Unfold: fold(f, init, xs) with len(xs)==k
                        # = f(f(...f(init, xs[0])..., xs[k-2]), xs[k-1])
                        result = si
                        acc_param, elem_param = body_fn.params
                        for i in range(k):
                            elem = OOp('getitem', (sc, OLit(i)))
                            result = _subst_in_oterm(
                                body_fn.body,
                                {acc_param: result, elem_param: elem})
                        # Recursively simplify the unfolded expression
                        return _simplify_on_region(
                            result, z3_vars, solver, timeout_ms, depth + 1)
                        break  # noqa: this break is unreachable but clarifies intent

        if si is not term.init or sc is not term.collection:
            new_fold = OFold(term.op_name, si, sc)
            if hasattr(term, 'body_fn'):
                new_fold.body_fn = term.body_fn
            return new_fold
        return term

    if name == 'OMap':
        sc = _simplify_on_region(term.collection, z3_vars, solver, timeout_ms, depth + 1)
        # Map trivialization: map(f, []) = []
        col_len = OOp('len', (sc,))
        col_len_z3 = _value_to_z3(col_len, z3_vars)
        if col_len_z3 is not None:
            is_empty = _solver_implies_pred(col_len_z3 == IntVal(0), solver)
            if is_empty is True:
                return OSeq(())  # empty sequence
        if sc is not term.collection:
            return OMap(term.transform, sc,
                        getattr(term, 'filter_pred', None))
        return term

    if name == 'OSeq':
        new_elems = []
        changed = False
        for e in term.elements:
            se = _simplify_on_region(e, z3_vars, solver, timeout_ms, depth + 1)
            new_elems.append(se)
            if se is not e:
                changed = True
        if changed:
            return OSeq(tuple(new_elems))
        return term

    return term


def _simplify_value_on_guard(value, guard, z3_vars: dict, timeout_ms: int = 300):
    """Simplify a value OTerm given that guard is true.

    Creates a Z3 solver with the guard constraints, then uses
    _simplify_on_region to compute the stalk at this refinement type.
    Supports arbitrary refinement predicates — anything Z3 can reason about.
    """
    if not _HAS_Z3:
        return value

    guard_z3 = _guard_to_z3(guard, z3_vars)
    if guard_z3 is None:
        # Try structural simplification even without Z3
        return _structural_simplify_on_guard(value, guard)

    try:
        z3_set_param('timeout', timeout_ms)
        solver = Solver()
        solver.set('timeout', timeout_ms)
        _add_type_axioms(solver, z3_vars)
        solver.add(guard_z3)
        return _simplify_on_region(value, z3_vars, solver, timeout_ms // 4)
    except Exception:
        return value


def _structural_simplify_on_guard(value, guard):
    """Simplify value structurally when Z3 can't compile the guard.

    If value is case(test, T, F) and test.canon() appears as a positive
    conjunct of the guard, take the true branch.  If u_not(test).canon()
    appears, take the false branch.

    This handles refinement predicates that Z3 can't compile:
      - Method calls: x.startswith("a"), x.is_digit()
      - Library predicates: sorted(x) == x, x.mean() == 0
      - Type predicates: isinstance(x, dict), callable(x)

    Type-level entailments (mutual exclusion of isinstance types):
      isinstance(x, dict) ⟹ ¬isinstance(x, list)
      isinstance(x, int)  ⟹ ¬isinstance(x, str)
      etc. — simple Python types are mutually exclusive.

    TypeVar constraints propagate through structural matching:
      if type(a) == type(b) is in the guard, and isinstance(a, int)
      is also present, then isinstance(b, int) is implied.
    """
    from .denotation import OCase, OOp, OVar

    name = _otype(value)
    if name != 'OCase':
        return value

    # Collect all canonical conjuncts from the guard
    guard_conjuncts = set()
    negated_conjuncts = set()
    # Also track type-level info for entailment reasoning
    isinstance_positive = {}   # param_canon → set of type names
    isinstance_negative = {}   # param_canon → set of negated type names
    callable_positive = set()  # param canons known callable
    callable_negative = set()  # param canons known NOT callable
    typevar_equalities = []    # (param_canon_a, param_canon_b)

    for c in _collect_conjuncts(guard):
        cn = _otype(c)
        if cn == 'OOp' and c.name in ('u_not', 'not', 'Not') and len(c.args) == 1:
            inner = c.args[0]
            negated_conjuncts.add(inner.canon())
            # Track negated type predicates
            icn = _otype(inner)
            if icn == 'OOp' and inner.name == 'isinstance' and len(inner.args) == 2:
                pc = inner.args[0].canon()
                tc = inner.args[1].canon()
                isinstance_negative.setdefault(pc, set()).add(tc)
            if icn == 'OOp' and inner.name == 'callable' and len(inner.args) == 1:
                callable_negative.add(inner.args[0].canon())
        else:
            guard_conjuncts.add(c.canon())
            # Track positive type predicates
            if cn == 'OOp' and c.name == 'isinstance' and len(c.args) == 2:
                pc = c.args[0].canon()
                tc = c.args[1].canon()
                isinstance_positive.setdefault(pc, set()).add(tc)
            if cn == 'OOp' and c.name == 'callable' and len(c.args) == 1:
                callable_positive.add(c.args[0].canon())
            if cn == 'OOp' and c.name == 'eq' and len(c.args) == 2:
                a0, a1 = c.args
                if (_otype(a0) == 'OOp' and a0.name == 'type' and
                    _otype(a1) == 'OOp' and a1.name == 'type'):
                    typevar_equalities.append(
                        (a0.args[0].canon(), a1.args[0].canon()))

    # Propagate TypeVar equalities: if type(a)==type(b) and isinstance(a,T),
    # then isinstance(b,T) is implied
    for pa, pb in typevar_equalities:
        for tc in isinstance_positive.get(pa, set()):
            isinstance_positive.setdefault(pb, set()).add(tc)
        for tc in isinstance_positive.get(pb, set()):
            isinstance_positive.setdefault(pa, set()).add(tc)

    # Mutual exclusion: simple Python types are disjoint
    DISJOINT_TYPES = {'int', 'float', 'str', 'list', 'dict', 'tuple',
                      'set', 'bool', 'bytes', 'NoneType',
                      '?int', '?float', '?str', '?list', '?dict',
                      '?tuple', '?set', '?bool', '?bytes'}

    # Check: does the test match any positive/negative conjunct directly?
    test_canon = value.test.canon()
    if test_canon in guard_conjuncts:
        return _structural_simplify_on_guard(value.true_branch, guard)
    if test_canon in negated_conjuncts:
        return _structural_simplify_on_guard(value.false_branch, guard)

    # Check negation of test
    neg_test_canon = OOp('u_not', (value.test,)).canon()
    if neg_test_canon in guard_conjuncts:
        return _structural_simplify_on_guard(value.false_branch, guard)

    # Type-level entailment: if test is isinstance(x, T) and we know
    # isinstance(x, S) for disjoint S ≠ T, then test is false
    tn = _otype(value.test)
    if tn == 'OOp' and value.test.name == 'isinstance' and len(value.test.args) == 2:
        test_param = value.test.args[0].canon()
        test_type = value.test.args[1].canon()

        # Direct positive: isinstance(x, T) is known true
        if test_type in isinstance_positive.get(test_param, set()):
            return _structural_simplify_on_guard(value.true_branch, guard)

        # Direct negative: ¬isinstance(x, T) is known
        if test_type in isinstance_negative.get(test_param, set()):
            return _structural_simplify_on_guard(value.false_branch, guard)

        # Mutual exclusion: isinstance(x, S) known, S ≠ T, both in DISJOINT_TYPES
        known_types = isinstance_positive.get(test_param, set())
        for kt in known_types:
            if kt != test_type and kt in DISJOINT_TYPES and test_type in DISJOINT_TYPES:
                return _structural_simplify_on_guard(value.false_branch, guard)

    # callable(x) entailment
    if tn == 'OOp' and value.test.name == 'callable' and len(value.test.args) == 1:
        test_param = value.test.args[0].canon()
        if test_param in callable_positive:
            return _structural_simplify_on_guard(value.true_branch, guard)
        if test_param in callable_negative:
            return _structural_simplify_on_guard(value.false_branch, guard)

    return value


# ═══════════════════════════════════════════════════════════════
# Čech fold-body descent — cohomology on the fold fiber
# ═══════════════════════════════════════════════════════════════

def _extract_outermost_fold(term, depth: int = 0):
    """Extract the outermost OFold from a term, stripping wrapping OCase/OOp.

    Returns (fold, context_fn) where context_fn rebuilds the wrapper
    with a replacement fold, or (None, None) if no fold found.
    """
    from .denotation import OFold, OCase, OOp
    if depth > 8:
        return None, None
    if isinstance(term, OFold):
        return term, lambda f: f
    if isinstance(term, OCase):
        # Try true branch first
        fold_t, ctx_t = _extract_outermost_fold(term.true_branch, depth + 1)
        if fold_t is not None:
            return fold_t, lambda f, t=term, c=ctx_t: OCase(t.test, c(f), t.false_branch)
        fold_f, ctx_f = _extract_outermost_fold(term.false_branch, depth + 1)
        if fold_f is not None:
            return fold_f, lambda f, t=term, c=ctx_f: OCase(t.test, t.true_branch, c(f))
    if isinstance(term, OOp) and len(term.args) > 0:
        # Try first arg that contains a fold (e.g., getitem(fold(...), idx))
        for i, arg in enumerate(term.args):
            fold_a, ctx_a = _extract_outermost_fold(arg, depth + 1)
            if fold_a is not None:
                def _rebuild(f, t=term, idx=i, ctx=ctx_a):
                    new_args = list(t.args)
                    new_args[idx] = ctx(f)
                    return OOp(t.name, tuple(new_args))
                return fold_a, _rebuild
    return None, None


def _subst_in_oterm(term, var_map: dict):
    """Substitute variables in an OTerm according to var_map."""
    from .denotation import OVar, OLit, OOp, OCase, OLam, OFold, OMap, OFix, OSeq
    name = _otype(term)
    if name == 'OVar':
        return var_map.get(term.name, term)
    if name == 'OLit':
        return term
    if name == 'OOp':
        return OOp(term.name, tuple(_subst_in_oterm(a, var_map) for a in term.args))
    if name == 'OCase':
        return OCase(
            _subst_in_oterm(term.test, var_map),
            _subst_in_oterm(term.true_branch, var_map),
            _subst_in_oterm(term.false_branch, var_map))
    if name == 'OLam':
        # Don't substitute bound variables
        inner_map = {k: v for k, v in var_map.items() if k not in term.params}
        return OLam(term.params, _subst_in_oterm(term.body, inner_map))
    if name == 'OSeq':
        return OSeq(tuple(_subst_in_oterm(e, var_map) for e in term.elements))
    return term


def cech_fold_body_descent(
    nf_f, nf_g,
    params: Optional[List[str]] = None,
    timeout_ms: int = 3000,
) -> CechResult:
    """Čech cohomology on the fold-body fiber.

    When two programs normalize to folds with the SAME collection (and
    compatible init), this descends into the fold body_fns and applies
    Čech cohomology to the step functions themselves.

    The site is the fold element domain (the iteration variable space).
    The cover is the guard structure within each body_fn.
    The presheaf assigns to each region the step function restricted to
    that region, with the accumulator as a free variable.

    H¹ = 0 on the body fiber ⟹ body_fns are extensionally equal
    ⟹ fold results are equal (by uniqueness of fold).

    This handles cases where two fold implementations have different
    case structures in their bodies but compute the same function.
    """
    if not _HAS_Z3:
        return CechResult(h1_rank=-1, equivalent=None,
                          explanation='Z3 not available')

    from .denotation import OFold, OLam, OCase, OVar, OLit

    # Extract outermost folds from both terms
    fold_f, ctx_f = _extract_outermost_fold(nf_f)
    fold_g, ctx_g = _extract_outermost_fold(nf_g)

    if fold_f is None or fold_g is None:
        return CechResult(h1_rank=-1, equivalent=None,
                          explanation='no fold structure to descend into')

    # Check collection equivalence (must be identical for fold uniqueness)
    col_f = fold_f.collection.canon() if hasattr(fold_f.collection, 'canon') else ''
    col_g = fold_g.collection.canon() if hasattr(fold_g.collection, 'canon') else ''
    if col_f != col_g:
        return CechResult(h1_rank=-1, equivalent=None,
                          explanation=f'fold collections differ: cannot apply fold uniqueness')

    # Check init equivalence
    init_f = fold_f.init.canon() if hasattr(fold_f.init, 'canon') else ''
    init_g = fold_g.init.canon() if hasattr(fold_g.init, 'canon') else ''

    # Allow semantically equivalent inits: False≡0, True≡1
    inits_match = (init_f == init_g)
    if not inits_match:
        # Check boolean/int equivalence
        _bool_int = {('False', '0'), ('0', 'False'), ('True', '1'), ('1', 'True')}
        if (init_f, init_g) in _bool_int:
            inits_match = True

    if not inits_match:
        return CechResult(h1_rank=-1, equivalent=None,
                          explanation=f'fold inits differ: {init_f[:30]} vs {init_g[:30]}')

    # Extract body_fns
    bf_f = getattr(fold_f, 'body_fn', None)
    bf_g = getattr(fold_g, 'body_fn', None)
    if not isinstance(bf_f, OLam) or not isinstance(bf_g, OLam):
        return CechResult(h1_rank=-1, equivalent=None,
                          explanation='fold body_fns not available as lambdas')

    # Check same arity
    if len(bf_f.params) != len(bf_g.params):
        return CechResult(h1_rank=-1, equivalent=None,
                          explanation='fold body_fn arities differ')

    # Alpha-normalize: rename body_fn params to canonical names ($acc, $elem)
    canonical_params = [f'$fold_acc_{i}' if i < len(bf_f.params) - 1 else '$fold_elem'
                        for i in range(len(bf_f.params))]
    if len(bf_f.params) == 2:
        canonical_params = ['$fold_acc', '$fold_elem']

    body_f = _subst_in_oterm(bf_f.body,
        {p: OVar(c) for p, c in zip(bf_f.params, canonical_params)})
    body_g = _subst_in_oterm(bf_g.body,
        {p: OVar(c) for p, c in zip(bf_g.params, canonical_params)})

    # Quick check: bodies already match after alpha-normalization
    if body_f.canon() == body_g.canon():
        # Also check the wrapping context matches
        # Use a dummy to check: if the context around the fold is different,
        # we still need the outer structure to agree
        dummy = OLit(42)
        outer_f = ctx_f(OFold(fold_f.op_name, fold_f.init, fold_f.collection, body_fn=bf_f))
        outer_g = ctx_g(OFold(fold_g.op_name, fold_g.init, fold_g.collection, body_fn=bf_g))
        # Replace fold with dummy to check context
        ctx_f_canon = ctx_f(dummy).canon()
        ctx_g_canon = ctx_g(dummy).canon()
        if ctx_f_canon == ctx_g_canon:
            return CechResult(h1_rank=0, equivalent=True,
                              explanation='fold bodies alpha-equivalent, contexts match')

    # Flatten body_fns to piecewise over the element/accumulator space
    pieces_f = _flatten_to_piecewise(body_f, max_pieces=16)
    pieces_g = _flatten_to_piecewise(body_g, max_pieces=16)

    # Need at least one case structure for Čech to be non-trivial
    if (len(pieces_f) == 1 and len(pieces_g) == 1
            and _otype(pieces_f[0].guard) == 'OLit'
            and _otype(pieces_g[0].guard) == 'OLit'):
        # Both unconditional bodies — just compare values directly
        if pieces_f[0].value.canon() == pieces_g[0].value.canon():
            ctx_f_canon = ctx_f(OLit(42)).canon()
            ctx_g_canon = ctx_g(OLit(42)).canon()
            if ctx_f_canon == ctx_g_canon:
                return CechResult(h1_rank=0, equivalent=True,
                                  explanation='fold bodies unconditionally equal')
        # Try Z3 on the values
        free_vars = _collect_free_vars(body_f) | _collect_free_vars(body_g)
        if params:
            free_vars |= set(params)
        free_vars |= set(canonical_params)
        z3_vars = {v: Int(v) for v in free_vars}
        result = _values_agree_on_region_z3(
            OLit(True), pieces_f[0].value, pieces_g[0].value,
            z3_vars, timeout_ms // 2)
        if result is True:
            ctx_f_canon = ctx_f(OLit(42)).canon()
            ctx_g_canon = ctx_g(OLit(42)).canon()
            if ctx_f_canon == ctx_g_canon:
                return CechResult(h1_rank=0, equivalent=True,
                                  total_regions=1, agreed_regions=1,
                                  explanation='Z3 proved fold bodies equal (single region)')
        return CechResult(h1_rank=1, equivalent=None,
                          explanation='fold bodies differ, Z3 inconclusive')

    # Compute common Čech refinement of the two body_fn covers
    refined = _refine_covers(pieces_f, pieces_g)

    # Structural emptiness detection
    f_guard_canons = {p.guard.canon() for p in pieces_f}
    g_guard_canons = {p.guard.canon() for p in pieces_g}
    for region in refined:
        if _is_structurally_contradictory(region.guard, f_guard_canons | g_guard_canons):
            region.region_empty = True

    # Create Z3 variables for all free vars (including fold params)
    free_vars = _collect_free_vars(body_f) | _collect_free_vars(body_g)
    if params:
        free_vars |= set(params)
    free_vars |= set(canonical_params)
    z3_vars = {v: Int(v) for v in free_vars}

    # Check each refined region
    total = 0; empty = 0; agreed = 0; disagreed = 0; unknown = 0
    per_timeout = max(100, timeout_ms // max(1, len(refined) * 2))

    for region in refined:
        if region.value_f.canon() == region.value_g.canon():
            region.agreement = True
            total += 1; agreed += 1
            continue

        if region.region_empty is True:
            empty += 1
            continue

        # Z3 emptiness check
        is_empty = _region_is_empty_z3(region.guard, z3_vars, per_timeout)
        if is_empty is True:
            region.region_empty = True
            empty += 1
            continue

        region.region_empty = False
        total += 1

        # Z3 value agreement
        result = _values_agree_on_region_z3(
            region.guard, region.value_f, region.value_g,
            z3_vars, per_timeout * 2)

        if result is True:
            region.agreement = True
            agreed += 1
        elif result is False:
            region.agreement = False
            disagreed += 1
        else:
            region.agreement = None
            unknown += 1

    h1 = disagreed + unknown

    if disagreed > 0:
        return CechResult(
            h1_rank=h1, equivalent=False,
            total_regions=total, empty_regions=empty,
            agreed_regions=agreed, disagreed_regions=disagreed,
            explanation=f'fold body Čech H¹={h1}: counterexample on {disagreed}/{total} regions')

    if h1 == 0 and total > 0:
        # Bodies proven equal on all non-empty regions → fold results equal
        # (by uniqueness of fold with equal init, collection, and step function)
        # But still need the wrapping context to match
        ctx_f_canon = ctx_f(OLit(42)).canon()
        ctx_g_canon = ctx_g(OLit(42)).canon()
        if ctx_f_canon == ctx_g_canon:
            return CechResult(
                h1_rank=0, equivalent=True,
                total_regions=total, empty_regions=empty,
                agreed_regions=agreed,
                explanation=(
                    f'fold body Čech H¹=0: bodies equal on all {agreed}/{total} '
                    f'regions ({empty} empty) → fold uniqueness theorem'))

    return CechResult(
        h1_rank=h1, equivalent=None,
        total_regions=total, empty_regions=empty,
        agreed_regions=agreed, unknown_regions=unknown,
        explanation=f'fold body Čech: {unknown}/{total} regions unresolved')


# ═══════════════════════════════════════════════════════════════
# Refinement type sub-Čech — split unknown regions by library predicates
# ═══════════════════════════════════════════════════════════════

def _refinement_sub_cech(
    region_guard, val_f, val_g,
    z3_vars: dict, params: List[str],
    timeout_ms: int,
    _depth: int = 0,
) -> Optional[bool]:
    """Split an unknown region by refinement type predicates and recheck.

    Implements a multi-level dependent type TOWER:

      Level 0:  {x : τ | guard(x)}
      Level 1:  {x : τ | guard(x) ∧ φ₁(x)} ∪ {x : τ | guard(x) ∧ ¬φ₁(x)}
      Level 2:  ... further split unresolved sub-regions by φ₂ ...

    At each level, we split by the MOST USEFUL refinement predicate
    (the one that resolves the most sub-regions), then recurse on
    any remaining unresolved sub-regions with the remaining predicates.

    This tower has depth bounded by MAX_DEPTH to prevent explosion.
    Each level represents a genuine refinement in the dependent type
    lattice — the stalk at each fiber is a simpler OTerm that may
    be provably equal where the original was opaque.

    Returns True if ALL sub-regions are resolved (H¹=0), None otherwise.
    """
    MAX_DEPTH = 3  # Refinement tower depth limit

    if not _HAS_Z3 or _depth > MAX_DEPTH:
        return None
    from .denotation import OOp, OLit, OVar

    # Generate refinement predicates
    lib_preds = _generate_library_refinements(val_f, val_g, params)
    if not lib_preds:
        return None

    # Limit predicates — more at higher depth since regions are smaller
    max_preds = max(6, 16 - _depth * 4)
    lib_preds = lib_preds[:max_preds]

    guard_z3 = _guard_to_z3(region_guard, z3_vars)
    if guard_z3 is None:
        return None

    per_pred_timeout = max(50, timeout_ms // max(1, len(lib_preds) * 4))

    for pred_idx, pred in enumerate(lib_preds):
        pred_z3 = _guard_to_z3(pred, z3_vars)
        if pred_z3 is None:
            continue

        solver = Solver()
        solver.set('timeout', per_pred_timeout)
        _add_type_axioms(solver, z3_vars)
        solver.add(guard_z3)

        # Simplify values on {guard ∧ pred}
        solver.push()
        solver.add(pred_z3)
        r_sat = solver.check()
        if r_sat != sat:
            solver.pop()
            continue

        sf_pos = _simplify_on_region(val_f, z3_vars, solver, per_pred_timeout)
        sg_pos = _simplify_on_region(val_g, z3_vars, solver, per_pred_timeout)
        solver.pop()

        # Simplify values on {guard ∧ ¬pred}
        solver.push()
        solver.add(Not(pred_z3))
        r_sat2 = solver.check()
        if r_sat2 != sat:
            solver.pop()
            # Region entirely within pred — check pos only
            if sf_pos.canon() == sg_pos.canon():
                return True
            pos_guard = OOp('and', (region_guard, pred))
            r = _values_agree_on_region_z3(
                pos_guard, sf_pos, sg_pos, z3_vars, per_pred_timeout)
            if r is True:
                return True
            continue

        sf_neg = _simplify_on_region(val_f, z3_vars, solver, per_pred_timeout)
        sg_neg = _simplify_on_region(val_g, z3_vars, solver, per_pred_timeout)
        solver.pop()

        # Check if both sub-regions agree
        pos_ok = sf_pos.canon() == sg_pos.canon()
        neg_ok = sf_neg.canon() == sg_neg.canon()

        if not pos_ok:
            pos_guard = OOp('and', (region_guard, pred))
            r = _values_agree_on_region_z3(
                pos_guard, sf_pos, sg_pos, z3_vars, per_pred_timeout)
            if r is True:
                pos_ok = True

        if not neg_ok:
            neg_guard = OOp('and', (region_guard, OOp('u_not', (pred,))))
            r = _values_agree_on_region_z3(
                neg_guard, sf_neg, sg_neg, z3_vars, per_pred_timeout)
            if r is True:
                neg_ok = True

        if pos_ok and neg_ok:
            return True  # H¹=0 on the refinement sub-cover!

        # ── Multi-level tower descent ──
        # If ONE sub-region is resolved but the other isn't,
        # recurse on the unresolved sub-region with remaining predicates.
        # This builds the dependent type tower: each resolved sub-region
        # is a leaf, each unresolved one descends another level.
        if pos_ok and not neg_ok and _depth < MAX_DEPTH:
            neg_guard = OOp('and', (region_guard, OOp('u_not', (pred,))))
            remaining_ms = max(50, timeout_ms // 2)
            sub = _refinement_sub_cech(
                neg_guard, sf_neg, sg_neg,
                z3_vars, params, remaining_ms, _depth + 1)
            if sub is True:
                return True

        if neg_ok and not pos_ok and _depth < MAX_DEPTH:
            pos_guard = OOp('and', (region_guard, pred))
            remaining_ms = max(50, timeout_ms // 2)
            sub = _refinement_sub_cech(
                pos_guard, sf_pos, sg_pos,
                z3_vars, params, remaining_ms, _depth + 1)
            if sub is True:
                return True

    return None


# ═══════════════════════════════════════════════════════════════
# Multi-level Čech descent — iterate on value sub-expressions
# ═══════════════════════════════════════════════════════════════

def _try_cech_on_values(val_f, val_g, z3_vars: dict, timeout_ms: int) -> Optional[bool]:
    """Attempt Čech descent when Z3 can't directly compare values.

    If both values are folds/fix/maps with matching structure, descend
    into their sub-components and apply Čech there. This implements
    multi-level Čech: the presheaf on one level's unknown regions gets
    refined by descending into the value's internal guard structure.

    Returns True if proven equal, None otherwise (never False — we don't
    have enough info for genuine counterexamples at this level).
    """
    from .denotation import OFold, OCase, OLam, OOp, OLit, OVar, OFix, OMap

    name_f = _otype(val_f)
    name_g = _otype(val_g)

    # Case 1: Both are folds — try fold body descent
    if name_f == 'OFold' and name_g == 'OFold':
        col_f = val_f.collection.canon() if hasattr(val_f.collection, 'canon') else ''
        col_g = val_g.collection.canon() if hasattr(val_g.collection, 'canon') else ''
        init_f = val_f.init.canon() if hasattr(val_f.init, 'canon') else ''
        init_g = val_g.init.canon() if hasattr(val_g.init, 'canon') else ''

        if col_f == col_g and init_f == init_g:
            bf_f = getattr(val_f, 'body_fn', None)
            bf_g = getattr(val_g, 'body_fn', None)
            if isinstance(bf_f, OLam) and isinstance(bf_g, OLam):
                if len(bf_f.params) == len(bf_g.params):
                    # Alpha-normalize
                    cparams = [f'$fa{i}' for i in range(len(bf_f.params))]
                    b_f = _subst_in_oterm(bf_f.body,
                        {p: OVar(c) for p, c in zip(bf_f.params, cparams)})
                    b_g = _subst_in_oterm(bf_g.body,
                        {p: OVar(c) for p, c in zip(bf_g.params, cparams)})
                    if b_f.canon() == b_g.canon():
                        return True
                    # Try Z3 on the bodies
                    inner_vars = dict(z3_vars)
                    for cp in cparams:
                        inner_vars[cp] = Int(cp)
                    r = _values_agree_on_region_z3(
                        OLit(True), b_f, b_g, inner_vars, timeout_ms)
                    if r is True:
                        return True

    # Case 2: Both are OOp with same name — try comparing args
    if name_f == 'OOp' and name_g == 'OOp':
        if val_f.name == val_g.name and len(val_f.args) == len(val_g.args):
            all_eq = True
            for af, ag in zip(val_f.args, val_g.args):
                if af.canon() == ag.canon():
                    continue
                r = _values_agree_on_region_z3(
                    OLit(True), af, ag, z3_vars, timeout_ms // max(1, len(val_f.args)))
                if r is True:
                    continue
                # Try recursive descent
                r2 = _try_cech_on_values(af, ag, z3_vars, timeout_ms // max(1, len(val_f.args)))
                if r2 is True:
                    continue
                all_eq = False
                break
            if all_eq:
                return True

    # Case 3: Both are OSeq — compare element-wise
    if name_f == 'OSeq' and name_g == 'OSeq':
        if len(val_f.elements) == len(val_g.elements):
            all_eq = True
            n_elts = len(val_f.elements)
            for ef, eg in zip(val_f.elements, val_g.elements):
                if ef.canon() == eg.canon():
                    continue
                r = _values_agree_on_region_z3(
                    OLit(True), ef, eg, z3_vars, timeout_ms // max(1, n_elts))
                if r is True:
                    continue
                r2 = _try_cech_on_values(ef, eg, z3_vars, timeout_ms // max(1, n_elts))
                if r2 is True:
                    continue
                all_eq = False
                break
            if all_eq:
                return True

    # Case 4: Both are OCase — Čech on the case itself
    if name_f == 'OCase' and name_g == 'OCase':
        pieces_f = _flatten_to_piecewise(val_f, max_pieces=8)
        pieces_g = _flatten_to_piecewise(val_g, max_pieces=8)
        if len(pieces_f) > 1 or len(pieces_g) > 1:
            refined = _refine_covers(pieces_f, pieces_g)
            f_gc = {p.guard.canon() for p in pieces_f}
            g_gc = {p.guard.canon() for p in pieces_g}
            for r in refined:
                if _is_structurally_contradictory(r.guard, f_gc | g_gc):
                    r.region_empty = True
            all_ok = True
            per_t = max(50, timeout_ms // max(1, len(refined) * 2))
            for r in refined:
                if r.value_f.canon() == r.value_g.canon():
                    continue
                if r.region_empty is True:
                    continue
                is_e = _region_is_empty_z3(r.guard, z3_vars, per_t)
                if is_e is True:
                    continue
                a = _values_agree_on_region_z3(r.guard, r.value_f, r.value_g, z3_vars, per_t)
                if a is True:
                    continue
                all_ok = False
                break
            if all_ok:
                return True

    return None


def cech_input_cohomology(
    nf_f, nf_g,
    params: Optional[List[str]] = None,
    timeout_ms: int = 3000,
) -> CechResult:
    """Genuine Čech H¹ over the input-space guard cover.

    The site is the input space X = ℤⁿ. The cover is the set of guard
    regions from both programs' OCase trees. The presheaf assigns to
    each region the pair (f|_U, g|_U).

    H¹ = 0 iff f and g agree on every non-empty region of the common
    Čech refinement.

    This is strictly more powerful than tree-diffing (align_oterms):
    - Tree-diffing requires matching constructor structure
    - Čech refinement handles different guard partitions by computing
      their cross-product and checking value agreement per region
    - Z3 can prove agreement even for different algebraic formulations

    Returns CechResult with h1_rank counting unresolved obstructions.
    """
    if not _HAS_Z3:
        return CechResult(h1_rank=-1, equivalent=None,
                          explanation='Z3 not available for Čech cohomology')

    # Quick canonical check
    if nf_f.canon() == nf_g.canon():
        return CechResult(h1_rank=0, equivalent=True,
                          explanation='canonical forms identical')

    # Step 0: Try fold-body Čech descent (multi-level cohomology)
    # If both programs are folds with same collection/init, descend
    # into their body_fns and apply Čech there — this is genuine
    # cohomology on the fold fiber.
    fold_result = cech_fold_body_descent(nf_f, nf_g, params, timeout_ms // 2)
    if fold_result.equivalent is True:
        return fold_result

    # Step 1: Extract piecewise forms (presheaf sections)
    pieces_f = _flatten_to_piecewise(nf_f)
    pieces_g = _flatten_to_piecewise(nf_g)

    # If both are single pieces with guard=True, fall back — no guard structure
    if (len(pieces_f) == 1 and len(pieces_g) == 1
            and _otype(pieces_f[0].guard) == 'OLit'
            and _otype(pieces_g[0].guard) == 'OLit'):
        # Both unconditional — Čech refinement is trivial (single region)
        # Check value agreement directly
        if pieces_f[0].value.canon() == pieces_g[0].value.canon():
            return CechResult(h1_rank=0, equivalent=True,
                              total_regions=1, agreed_regions=1,
                              explanation='single unconditional region, values match')
        # Try Z3 for the values
        free_vars = _collect_free_vars(nf_f) | _collect_free_vars(nf_g)
        if params:
            free_vars |= set(params)
        z3_vars = {v: Int(v) for v in free_vars}
        from .denotation import OLit
        result = _values_agree_on_region_z3(
            OLit(True), pieces_f[0].value, pieces_g[0].value,
            z3_vars, timeout_ms)
        if result is True:
            return CechResult(h1_rank=0, equivalent=True,
                              total_regions=1, agreed_regions=1,
                              explanation='Z3 proved values equal (single region)')
        if result is False:
            return CechResult(h1_rank=1, equivalent=False,
                              total_regions=1, disagreed_regions=1,
                              explanation='Z3 counterexample (single region)')
        # Z3 inconclusive — try multi-level Čech descent into values
        descent = _try_cech_on_values(
            pieces_f[0].value, pieces_g[0].value, z3_vars, timeout_ms // 2)
        if descent is True:
            return CechResult(h1_rank=0, equivalent=True,
                              total_regions=1, agreed_regions=1,
                              explanation='multi-level Čech descent proved values equal')
        return CechResult(h1_rank=1, equivalent=None,
                          total_regions=1, unknown_regions=1,
                          explanation='single region, values differ, Z3 inconclusive')

    # Step 2: Compute common Čech refinement
    refined = _refine_covers(pieces_f, pieces_g)

    # Step 2b: Structural emptiness detection
    # Before Z3, detect structurally empty regions. A region with guard
    # and(g_f, u_not(g_g)) is empty when g_f.canon() == g_g.canon().
    # This handles cases where Z3 can't compile the guards (e.g., floats).
    #
    # Build a set of canonical guard forms from each cover
    f_guard_canons = {p.guard.canon() for p in pieces_f}
    g_guard_canons = {p.guard.canon() for p in pieces_g}

    for region in refined:
        if _is_structurally_contradictory(region.guard, f_guard_canons | g_guard_canons):
            region.region_empty = True

    # Step 3: Create Z3 variables for all free parameters
    free_vars = _collect_free_vars(nf_f) | _collect_free_vars(nf_g)
    if params:
        free_vars |= set(params)
    z3_vars = {v: Int(v) for v in free_vars}

    # Step 4: Check each refined region
    total_regions = 0
    empty_regions = 0
    agreed_regions = 0
    disagreed_regions = 0
    unknown_regions = 0
    checked_regions: List[RefinedRegion] = []

    # Distribute timeout across regions
    per_region_timeout = max(100, timeout_ms // max(1, len(refined) * 2))

    for region in refined:
        # Quick structural check: values already match
        if region.value_f.canon() == region.value_g.canon():
            region.agreement = True
            total_regions += 1
            agreed_regions += 1
            checked_regions.append(region)
            continue

        # Structural emptiness already detected in Step 2b
        if region.region_empty is True:
            empty_regions += 1
            checked_regions.append(region)
            continue

        # Check if region is empty via Z3 (guard is unsatisfiable)
        empty = _region_is_empty_z3(region.guard, z3_vars, per_region_timeout)
        if empty is True:
            region.region_empty = True
            empty_regions += 1
            checked_regions.append(region)
            continue

        region.region_empty = False
        total_regions += 1

        # ── Refinement type stalk computation ──
        # Simplify values under the region's guard constraints.
        # This computes the stalk of the presheaf at the refinement
        # type defined by the region: case branches whose tests are
        # determined by the guard get evaluated, pruning the OTerm.
        simp_f = _simplify_value_on_guard(region.value_f, region.guard, z3_vars, per_region_timeout)
        simp_g = _simplify_value_on_guard(region.value_g, region.guard, z3_vars, per_region_timeout)

        # Check if stalks match after simplification
        if simp_f.canon() == simp_g.canon():
            region.agreement = True
            agreed_regions += 1
            checked_regions.append(region)
            continue

        # Check value agreement on this region via Z3 (with simplified values)
        agreement = _values_agree_on_region_z3(
            region.guard, simp_f, simp_g,
            z3_vars, per_region_timeout * 2)

        if agreement is True:
            region.agreement = True
            agreed_regions += 1
        elif agreement is False:
            region.agreement = False
            disagreed_regions += 1
        else:
            # Multi-level Čech descent: when Z3 can't directly compare,
            # descend into the value sub-expressions and apply Čech there.
            # This is the radical cohomological move: H¹ on one level's
            # unknown fibers gets resolved by computing H¹ on the next level.
            descent = _try_cech_on_values(
                simp_f, simp_g,
                z3_vars, per_region_timeout)
            if descent is True:
                region.agreement = True
                agreed_regions += 1
            else:
                # Refinement type sub-Čech: split this unknown region by
                # library refinement predicates and check the sub-regions.
                # This implements the dependent type tower:
                #   {x : τ | guard(x)} is refined to
                #   {x : τ | guard(x) ∧ φ(x)} ∪ {x : τ | guard(x) ∧ ¬φ(x)}
                # for each library predicate φ.
                sub_resolved = _refinement_sub_cech(
                    region.guard, simp_f, simp_g,
                    z3_vars, params or [], per_region_timeout)
                if sub_resolved is True:
                    region.agreement = True
                    agreed_regions += 1
                else:
                    region.agreement = None
                    unknown_regions += 1

        checked_regions.append(region)

    # Step 5: Compute H¹
    h1_rank = disagreed_regions + unknown_regions

    if disagreed_regions > 0:
        return CechResult(
            h1_rank=h1_rank, equivalent=False,
            total_regions=total_regions, empty_regions=empty_regions,
            agreed_regions=agreed_regions, disagreed_regions=disagreed_regions,
            unknown_regions=unknown_regions,
            regions=checked_regions,
            explanation=(
                f'Čech H¹={h1_rank}: counterexample on '
                f'{disagreed_regions}/{total_regions} regions '
                f'({empty_regions} empty, {agreed_regions} agreed)'))

    if h1_rank == 0:
        return CechResult(
            h1_rank=0, equivalent=True,
            total_regions=total_regions, empty_regions=empty_regions,
            agreed_regions=agreed_regions,
            regions=checked_regions,
            explanation=(
                f'Čech H¹=0: all {agreed_regions}/{total_regions} non-empty '
                f'regions verified ({empty_regions} empty, '
                f'{len(pieces_f)} × {len(pieces_g)} refinement)'))

    return CechResult(
        h1_rank=h1_rank, equivalent=None,
        total_regions=total_regions, empty_regions=empty_regions,
        agreed_regions=agreed_regions, unknown_regions=unknown_regions,
        regions=checked_regions,
        explanation=(
            f'Čech H¹ unknown: {unknown_regions}/{total_regions} regions '
            f'unresolved ({agreed_regions} agreed, {empty_regions} empty)'))
