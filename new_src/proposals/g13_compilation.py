"""Proposals for Chapters 27-31 (Nat-Eliminator through Normalization Traces).

These proposals strengthen the normalizer with:
  1. Nat-eliminator extraction from OFix bodies (Ch 27)
  2. Course-of-values recursion detection (Ch 29)
  3. Map-map fusion in Phase 4 (Ch 30)
  4. A trace() function that logs per-phase OTerm snapshots (Ch 31)
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional, Tuple

# ── Import OTerm types from denotation ──────────────────────
# In production these come from new_src.cctt.denotation
from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, OLam, OMap,
    OQuotient, ODict, OUnknown, OAbstract, OCatch,
    normalize,
    _phase1_beta, _phase2_ring, _phase3_fold,
    _phase4_hof, _phase5_unify, _phase6_quotient, _phase7_piecewise,
    _subst,
)


# ═══════════════════════════════════════════════════════════
# Proposal 1: Nat-eliminator extraction from OFix (Ch 27)
# ═══════════════════════════════════════════════════════════

@dataclass
class NatElimParams:
    """Parameters extracted by the Nat-eliminator."""
    base_val: OTerm       # value returned at base case
    threshold: OTerm      # comparison threshold
    op_name: str          # binary operation name (e.g. 'mult', 'add')
    param_name: str       # recursion parameter name
    cmp_op: str           # comparison operator ('lte', 'lt', 'eq')


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

    # Test must be a comparison: cmp(param, threshold)
    test = body.test
    if not isinstance(test, OOp) or test.name not in ('lte', 'lt', 'eq'):
        return None
    if len(test.args) != 2:
        return None

    # True branch is the base value (should be a literal or simple term)
    base_val = body.true_branch

    # False branch should be OOp(binop, (param, recursive_call))
    step = body.false_branch
    if not isinstance(step, OOp) or len(step.args) != 2:
        return None

    # Check that one of the args contains a self-reference
    param_arg = test.args[0]
    if not isinstance(param_arg, OVar):
        return None

    # Verify the recursive call is present in the step
    # (the self-reference uses the fix name)
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
        return fix  # can't extract; leave as OFix

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
    return False


# ═══════════════════════════════════════════════════════════
# Proposal 2: Course-of-values detection (Ch 29)
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
    # refs should be {1, 2, ..., k}
    if refs == set(range(1, max(refs) + 1)):
        return max(refs)
    return None


def _collect_recursive_offsets(term: OTerm, fix_name: str) -> set:
    """Collect the set of recursion offsets {d : f(n-d) appears}."""
    offsets = set()
    if isinstance(term, OOp):
        # Check if this is fix_name(n - d) for literal d
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
    return offsets


# ═══════════════════════════════════════════════════════════
# Proposal 3: Map-map fusion (Phase 4, Ch 30)
# ═══════════════════════════════════════════════════════════

def fuse_map_map(outer_f: OLam, inner_g: OLam) -> OLam:
    """Compose two OLam values: f . g = lambda x: f(g(x)).

    Implements the map composition rule from Section 30.0.3:
        map(f, map(g, xs)) -> map(f . g, xs)

    Uses alpha-normalization so that the result is canonical.
    """
    if len(outer_f.params) != 1 or len(inner_g.params) != 1:
        # Only fuse unary lambdas
        raise ValueError("Can only fuse unary lambdas")

    # Compose: lambda z: f_body[f_param := g_body[g_param := z]]
    z = '_composed_0'
    inner_applied = _subst(inner_g.body, {inner_g.params[0]: OVar(z)})
    composed_body = _subst(outer_f.body, {outer_f.params[0]: inner_applied})
    return OLam((z,), composed_body)


def phase4_map_fusion(term: OTerm) -> OTerm:
    """Enhanced Phase 4: detect and apply map-map fusion.

    When we see OMap(f, OMap(g, xs)), replace with OMap(f.g, xs).
    This avoids an intermediate collection and enables further
    simplification.
    """
    if isinstance(term, OMap):
        t = phase4_map_fusion(term.transform)
        c = phase4_map_fusion(term.collection)
        f = phase4_map_fusion(term.filter_pred) if term.filter_pred else None

        # map(f, map(g, xs)) -> map(f.g, xs) when no filter on inner
        if isinstance(c, OMap) and c.filter_pred is None:
            if isinstance(t, OLam) and isinstance(c.transform, OLam):
                composed = fuse_map_map(t, c.transform)
                return OMap(composed, c.collection, f)

        return OMap(t, c, f)

    if isinstance(term, OOp):
        return OOp(term.name, tuple(phase4_map_fusion(a) for a in term.args))
    if isinstance(term, OCase):
        return OCase(phase4_map_fusion(term.test),
                     phase4_map_fusion(term.true_branch),
                     phase4_map_fusion(term.false_branch))
    if isinstance(term, OFold):
        return OFold(term.op_name, phase4_map_fusion(term.init),
                     phase4_map_fusion(term.collection))
    if isinstance(term, OSeq):
        return OSeq(tuple(phase4_map_fusion(e) for e in term.elements))
    if isinstance(term, OLam):
        return OLam(term.params, phase4_map_fusion(term.body))
    return term


# ═══════════════════════════════════════════════════════════
# Proposal 4: Normalization trace (Ch 31)
# ═══════════════════════════════════════════════════════════

@dataclass
class PhaseSnapshot:
    """A snapshot of the OTerm after one normalization phase."""
    phase: int         # 1-7
    phase_name: str
    term: OTerm
    canon: str         # canonical string representation
    changed: bool      # whether this phase changed the term


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
            lines.append(f"  [{marker}] P{snap.phase} ({snap.phase_name}): {snap.canon}")
        lines.append(f"  Output: {self.output_term.canon()}")
        return '\n'.join(lines)


PHASE_NAMES = {
    1: 'beta-reduction',
    2: 'ring/lattice',
    3: 'fold-canon',
    4: 'HOF-fusion',
    5: 'dichotomy',
    6: 'quotient',
    7: 'piecewise',
}

PHASE_FNS = [
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
    of each iteration.  This implements the trace machinery described
    in Chapter 31.
    """
    snapshots: List[PhaseSnapshot] = []
    prev_canon = None
    current = term
    iterations = 0

    for _ in range(8):
        iterations += 1
        for phase_num, phase_fn in PHASE_FNS:
            before = current.canon()
            current = phase_fn(current)
            after = current.canon()
            snapshots.append(PhaseSnapshot(
                phase=phase_num,
                phase_name=PHASE_NAMES[phase_num],
                term=current,
                canon=after,
                changed=(before != after),
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


# ═══════════════════════════════════════════════════════════
# Demonstration: Trace the absolute-value example (Trace 6)
# ═══════════════════════════════════════════════════════════

def demo_abs_trace():
    """Demonstrate Trace 6 from Chapter 31: abs(n) vs if n<0: -n else n.

    Shows Phase 4 expanding abs() to a piecewise case, after which
    both programs have the same OTerm.
    """
    # Program A: abs(n)
    prog_a = OOp('abs', (OVar('n'),))

    # Program B: if n < 0: return -n; else: return n
    prog_b = OCase(
        OOp('lt', (OVar('n'), OLit(0))),
        OOp('u_usub', (OVar('n'),)),
        OVar('n'),
    )

    trace_a = normalize_with_trace(prog_a)
    trace_b = normalize_with_trace(prog_b)

    print("=== Program A: abs(n) ===")
    print(trace_a.summary())
    print()
    print("=== Program B: if n<0: -n else n ===")
    print(trace_b.summary())
    print()

    if trace_a.output_term.canon() == trace_b.output_term.canon():
        print("MATCH: both normalize to the same OTerm")
    else:
        print("DIVERGE: different canonical forms")
        print(f"  A: {trace_a.output_term.canon()}")
        print(f"  B: {trace_b.output_term.canon()}")


if __name__ == '__main__':
    demo_abs_trace()
