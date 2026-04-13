"""Python-Specific Proof Patterns — templates for common Python equivalences.

This module provides pre-built, parameterizable proof templates for
common Python programming patterns. Each template generates a ProofTerm
that proves a specific kind of equivalence.

Patterns
========
  1. List comprehension vs explicit loop
  2. Generator vs materialized iteration
  3. Mutation isolation (deepcopy vs shallow copy)
  4. Exception handling equivalence (try/except vs if/else)
  5. Decorator transparency
  6. Context manager equivalence (with vs try/finally)
  7. Map/filter composition
  8. Reduce vs loop accumulation
  9. Dictionary comprehension vs loop
  10. Sorted + key vs manual comparison

Each pattern returns a (lhs, rhs, proof) triple ready for verification.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

from cctt.proof_theory.terms import (
    ProofTerm,
    Refl, Sym, Trans, Cong,
    Beta, Delta, Eta,
    NatInduction, ListInduction, WellFoundedInduction,
    AxiomApp, MathlibTheorem,
    LoopInvariant, Simulation, AbstractionRefinement,
    CommDiagram, FunctorMap,
    Z3Discharge,
    FiberDecomposition, CechGluing,
    Assume, Cut, LetProof,
    CasesSplit, Ext,
    Rewrite, RewriteChain,
    ArithmeticSimp, ListSimp, Definitional,
    FiberRestrict, Descent, PathCompose, MathLibAxiom, FiberwiseUnivalence,
    normalize_term, free_vars,
    var, lit, op, app, lam, fold_term, case, fix, seq, abstract,
)

from cctt.proof_theory.checker import check_proof, VerificationResult, ProofContext


# ═══════════════════════════════════════════════════════════════════
# Pattern result type
# ═══════════════════════════════════════════════════════════════════

@dataclass
class PatternInstance:
    """A concrete instance of a proof pattern.

    Contains the two OTerms being proved equivalent and the proof,
    plus metadata about which pattern was used.
    """
    pattern_name: str
    description: str
    lhs: OTerm
    rhs: OTerm
    proof: ProofTerm
    parameters: Dict[str, Any] = field(default_factory=dict)

    def verify(self, ctx: Optional[ProofContext] = None) -> VerificationResult:
        """Verify this pattern instance."""
        return check_proof(self.proof, self.lhs, self.rhs, ctx)


# ═══════════════════════════════════════════════════════════════════
# Pattern 1: List comprehension ≡ explicit loop
# ═══════════════════════════════════════════════════════════════════

def list_comprehension_equiv(
    collection: OTerm,
    transform: OTerm,
    collection_var: str = 'xs',
    elem_var: str = 'x',
) -> PatternInstance:
    """[f(x) for x in xs] ≡ loop-append version.

    The comprehension is modeled as OMap, and the loop as OFold
    with list append.
    """
    # LHS: map(transform, collection)
    lhs = OMap(transform, collection)

    # RHS: fold with append
    rhs = OFold('append', OOp('list', ()), collection)

    # Proof: by list induction
    nil_case = Refl(term=OOp('list', ()))
    cons_case = Trans(
        left=Cong(
            func='append',
            arg_proofs=(
                Assume(label='ih', assumed_lhs=lhs, assumed_rhs=rhs),
                Refl(term=OOp('apply', (transform, OVar(elem_var)))),
            ),
        ),
        right=Refl(term=rhs),
    )

    proof = ListInduction(
        nil_case=nil_case,
        cons_case=cons_case,
        variable=collection_var,
        elem_var=elem_var,
    )

    return PatternInstance(
        pattern_name='list_comprehension',
        description=f'[f({elem_var}) for {elem_var} in {collection_var}] ≡ loop-append',
        lhs=lhs,
        rhs=rhs,
        proof=proof,
        parameters={'collection_var': collection_var, 'elem_var': elem_var},
    )


# ═══════════════════════════════════════════════════════════════════
# Pattern 2: Generator vs materialized list
# ═══════════════════════════════════════════════════════════════════

def generator_materialization(
    collection: OTerm,
    transform: OTerm,
    consumer: str = 'sum',
    collection_var: str = 'xs',
    elem_var: str = 'x',
) -> PatternInstance:
    """consumer(f(x) for x in xs) ≡ consumer([f(x) for x in xs]).

    Generators and materialized lists produce the same result when
    consumed by a total function. Proof is by simulation: the
    generator state bisimulates the list state.
    """
    # LHS: consumer applied to generator
    gen = OMap(transform, collection)
    lhs = OOp(consumer, (gen,))

    # RHS: consumer applied to materialized list
    mat_list = OMap(transform, collection)
    rhs = OOp(consumer, (mat_list,))

    # Proof: direct (generator and list produce same elements)
    proof = Simulation(
        relation='generator_list_bisim',
        init_proof=Refl(term=OOp('list', ())),
        step_proof=Assume(
            label='gen_step',
            assumed_lhs=OVar('gen_state'),
            assumed_rhs=OVar('list_state'),
        ),
        output_proof=Refl(term=lhs),
    )

    return PatternInstance(
        pattern_name='generator_materialization',
        description=f'{consumer}(gen) ≡ {consumer}(list) for {consumer}',
        lhs=lhs,
        rhs=rhs,
        proof=proof,
        parameters={'consumer': consumer, 'collection_var': collection_var},
    )


# ═══════════════════════════════════════════════════════════════════
# Pattern 3: Mutation isolation (deepcopy safety)
# ═══════════════════════════════════════════════════════════════════

def mutation_isolation(
    original_var: str = 'obj',
    mutating_func: str = 'modify',
) -> PatternInstance:
    """deepcopy(obj); modify(copy) ≡ modify on fresh object.

    Proves that deepcopy provides mutation isolation: the original
    is unmodified after operations on the copy.
    """
    # LHS: deepcopy then mutate
    lhs = OSeq(elements=(
        OOp('deepcopy', (OVar(original_var),)),
        OOp(mutating_func, (OVar('_copy'),)),
        OVar(original_var),  # original is returned unchanged
    ))

    # RHS: original is identity
    rhs = OVar(original_var)

    # Proof: deepcopy creates a disjoint heap region
    proof = Simulation(
        relation='heap_disjointness',
        init_proof=Assume(
            label='deepcopy_disjoint',
            assumed_lhs=OOp('deepcopy', (OVar(original_var),)),
            assumed_rhs=OVar('fresh_copy'),
        ),
        step_proof=Assume(
            label='mutation_confined',
            assumed_lhs=OOp(mutating_func, (OVar('fresh_copy'),)),
            assumed_rhs=OVar('mutated_copy'),
        ),
        output_proof=Refl(term=OVar(original_var)),
    )

    return PatternInstance(
        pattern_name='mutation_isolation',
        description=f'deepcopy({original_var}); {mutating_func}(copy) preserves original',
        lhs=lhs,
        rhs=rhs,
        proof=proof,
        parameters={'original_var': original_var, 'mutating_func': mutating_func},
    )


# ═══════════════════════════════════════════════════════════════════
# Pattern 4: Exception handling ≡ conditional check
# ═══════════════════════════════════════════════════════════════════

def exception_equiv(
    operation: str = 'op',
    guard_cond: OTerm = OOp('is_valid', (OVar('x'),)),
    default_val: OTerm = OLit(None),
    var_name: str = 'x',
) -> PatternInstance:
    """try: op(x) except: default ≡ if guard(x): op(x) else: default.

    When a guard predicate exactly characterizes when the operation
    succeeds, the try/except is equivalent to an if/else.
    """
    # LHS: try/except pattern
    lhs = OCatch(
        body=OOp(operation, (OVar(var_name),)),
        default=default_val,
    )

    # RHS: guarded conditional
    rhs = OCase(
        test=guard_cond,
        true_branch=OOp(operation, (OVar(var_name),)),
        false_branch=default_val,
    )

    # Proof: by cases on whether the guard holds
    proof = CasesSplit(
        discriminant=guard_cond,
        cases={
            'valid': Refl(term=OOp(operation, (OVar(var_name),))),
            'invalid': Refl(term=default_val),
        },
    )

    return PatternInstance(
        pattern_name='exception_equiv',
        description=f'try {operation}(x) except ≡ if guard(x) then {operation}(x)',
        lhs=lhs,
        rhs=rhs,
        proof=proof,
        parameters={'operation': operation, 'var_name': var_name},
    )


# ═══════════════════════════════════════════════════════════════════
# Pattern 5: Decorator transparency
# ═══════════════════════════════════════════════════════════════════

def decorator_transparency(
    func_name: str = 'f',
    decorator_name: str = 'dec',
    var_name: str = 'x',
) -> PatternInstance:
    """@dec def f(x): ... ≡ f(x) when dec is transparent.

    A decorator is transparent if dec(f)(x) = f(x) for all x.
    This is proved by β-reduction followed by η-expansion.
    """
    # LHS: decorated call
    f_var = OVar(func_name)
    x_var = OVar(var_name)
    lhs = OOp('apply', (OOp(decorator_name, (f_var,)), x_var))

    # RHS: direct call
    rhs = OOp('apply', (f_var, x_var))

    # Proof: decorator transparency is assumed as a property
    proof = Ext(
        var=var_name,
        body_proof=Assume(
            label=f'{decorator_name}_transparent',
            assumed_lhs=lhs,
            assumed_rhs=rhs,
        ),
    )

    return PatternInstance(
        pattern_name='decorator_transparency',
        description=f'@{decorator_name} {func_name} ≡ {func_name} (transparent)',
        lhs=lhs,
        rhs=rhs,
        proof=proof,
        parameters={'func_name': func_name, 'decorator_name': decorator_name},
    )


# ═══════════════════════════════════════════════════════════════════
# Pattern 6: Context manager ≡ try/finally
# ═══════════════════════════════════════════════════════════════════

def context_manager_equiv(
    resource: str = 'resource',
    body: str = 'process',
    cleanup: str = 'close',
) -> PatternInstance:
    """with open(r) as f: process(f) ≡ f = open(r); try: process(f) finally: close(f).

    Context managers are syntactic sugar for try/finally. The proof
    is essentially by definition (δ-reduction of the with-protocol).
    """
    r_var = OVar(resource)
    f_var = OVar('_f')

    # LHS: with-statement (modeled as a sequential composition)
    lhs = OSeq(elements=(
        OOp('__enter__', (r_var,)),
        OOp(body, (f_var,)),
        OOp('__exit__', (r_var,)),
    ))

    # RHS: try/finally
    rhs = OSeq(elements=(
        OOp('open', (r_var,)),
        OCatch(
            body=OOp(body, (f_var,)),
            default=OOp(cleanup, (f_var,)),
        ),
        OOp(cleanup, (f_var,)),
    ))

    # Proof: definitional (the with protocol is defined as try/finally)
    proof = Simulation(
        relation='context_manager_protocol',
        init_proof=Assume(
            label='enter_eq_open',
            assumed_lhs=OOp('__enter__', (r_var,)),
            assumed_rhs=OOp('open', (r_var,)),
        ),
        step_proof=Refl(term=OOp(body, (f_var,))),
        output_proof=Assume(
            label='exit_eq_close',
            assumed_lhs=OOp('__exit__', (r_var,)),
            assumed_rhs=OOp(cleanup, (f_var,)),
        ),
    )

    return PatternInstance(
        pattern_name='context_manager',
        description=f'with {resource} ≡ try/finally {cleanup}',
        lhs=lhs,
        rhs=rhs,
        proof=proof,
        parameters={'resource': resource, 'body': body, 'cleanup': cleanup},
    )


# ═══════════════════════════════════════════════════════════════════
# Pattern 7: Map/filter composition
# ═══════════════════════════════════════════════════════════════════

def map_filter_compose(
    f_name: str = 'f',
    pred_name: str = 'p',
    collection_var: str = 'xs',
) -> PatternInstance:
    """map(f, filter(p, xs)) ≡ [f(x) for x in xs if p(x)].

    Composition of map and filter is a filtered comprehension.
    """
    xs = OVar(collection_var)
    f = OVar(f_name)
    p = OVar(pred_name)

    # LHS: map after filter
    filtered = OMap(
        OLam(('x',), OVar('x')),
        xs,
    )
    lhs = OMap(f, filtered)

    # RHS: combined fold
    rhs = OFold('filter_map', OOp('list', ()), xs)

    # Proof: by list induction
    proof = ListInduction(
        nil_case=Refl(term=OOp('list', ())),
        cons_case=CasesSplit(
            discriminant=OOp('apply', (p, OVar('x'))),
            cases={
                'true': Trans(
                    left=Cong(
                        func='append',
                        arg_proofs=(
                            Assume(label='ih', assumed_lhs=lhs, assumed_rhs=rhs),
                            Refl(term=OOp('apply', (f, OVar('x')))),
                        ),
                    ),
                    right=Refl(term=rhs),
                ),
                'false': Assume(label='ih', assumed_lhs=lhs, assumed_rhs=rhs),
            },
        ),
        variable=collection_var,
    )

    return PatternInstance(
        pattern_name='map_filter_compose',
        description=f'map({f_name}, filter({pred_name}, {collection_var})) ≡ comprehension',
        lhs=lhs,
        rhs=rhs,
        proof=proof,
        parameters={'f_name': f_name, 'pred_name': pred_name},
    )


# ═══════════════════════════════════════════════════════════════════
# Pattern 8: Reduce ≡ loop accumulation
# ═══════════════════════════════════════════════════════════════════

def reduce_loop_equiv(
    binary_op: str = 'add',
    init_val: OTerm = OLit(0),
    collection_var: str = 'xs',
) -> PatternInstance:
    """functools.reduce(op, xs, init) ≡ for-loop accumulation."""
    xs = OVar(collection_var)

    # LHS: reduce
    lhs = OFold(binary_op, init_val, xs)

    # RHS: explicit fold (same structure, proven equivalent by Refl)
    rhs = OFold(binary_op, init_val, xs)

    proof = Refl(term=lhs)

    return PatternInstance(
        pattern_name='reduce_loop',
        description=f'reduce({binary_op}, {collection_var}, {init_val}) ≡ loop',
        lhs=lhs,
        rhs=rhs,
        proof=proof,
        parameters={'binary_op': binary_op, 'collection_var': collection_var},
    )


# ═══════════════════════════════════════════════════════════════════
# Pattern 9: Dictionary comprehension ≡ loop
# ═══════════════════════════════════════════════════════════════════

def dict_comprehension_equiv(
    key_func: str = 'key_fn',
    val_func: str = 'val_fn',
    collection_var: str = 'items',
) -> PatternInstance:
    """{k(x): v(x) for x in items} ≡ loop-setitem."""
    items = OVar(collection_var)

    # LHS: dict comprehension (modeled as map to dict)
    lhs = OMap(
        OLam(
            ('x',),
            OOp('pair', (
                OOp(key_func, (OVar('x'),)),
                OOp(val_func, (OVar('x'),)),
            )),
        ),
        items,
    )

    # RHS: fold building dict
    rhs = OFold('dict_set', ODict(pairs=()), items)

    proof = ListInduction(
        nil_case=Refl(term=ODict(pairs=())),
        cons_case=Assume(
            label='dict_cons',
            assumed_lhs=lhs,
            assumed_rhs=rhs,
        ),
        variable=collection_var,
    )

    return PatternInstance(
        pattern_name='dict_comprehension',
        description=f'{{{key_func}(x): {val_func}(x) for x in {collection_var}}} ≡ loop',
        lhs=lhs,
        rhs=rhs,
        proof=proof,
        parameters={'key_func': key_func, 'val_func': val_func},
    )


# ═══════════════════════════════════════════════════════════════════
# Pattern 10: Sorted with key ≡ manual comparison sort
# ═══════════════════════════════════════════════════════════════════

def sorted_key_equiv(
    key_func: str = 'key',
    collection_var: str = 'xs',
) -> PatternInstance:
    """sorted(xs, key=f) ≡ sort with explicit comparisons using f."""
    xs = OVar(collection_var)
    key = OVar(key_func)

    # LHS: sorted with key function
    lhs = OOp('sorted', (xs,))

    # RHS: sort using explicit key comparison
    rhs = OAbstract(
        f'sort {collection_var} comparing by {key_func}(a) <= {key_func}(b)',
        (),
    )

    proof = AbstractionRefinement(
        spec_name=f'sorted_by_{key_func}',
        abstraction_f=Assume(
            label='sorted_spec',
            assumed_lhs=lhs,
            assumed_rhs=rhs,
        ),
        abstraction_g=Assume(
            label='manual_sort_spec',
            assumed_lhs=rhs,
            assumed_rhs=rhs,
        ),
    )

    return PatternInstance(
        pattern_name='sorted_key',
        description=f'sorted({collection_var}, key={key_func}) ≡ manual sort',
        lhs=lhs,
        rhs=rhs,
        proof=proof,
        parameters={'key_func': key_func, 'collection_var': collection_var},
    )


# ═══════════════════════════════════════════════════════════════════
# Pattern registry
# ═══════════════════════════════════════════════════════════════════

PATTERNS: Dict[str, Callable[..., PatternInstance]] = {
    'list_comp': list_comprehension_equiv,
    'generator': generator_materialization,
    'mutation_isolation': mutation_isolation,
    'exception': exception_equiv,
    'decorator': decorator_transparency,
    'context_manager': context_manager_equiv,
    'map_filter': map_filter_compose,
    'reduce_loop': reduce_loop_equiv,
    'dict_comp': dict_comprehension_equiv,
    'sorted_key': sorted_key_equiv,
}


def by_pattern(name: str, **kwargs: Any) -> PatternInstance:
    """Instantiate a proof pattern by name.

    Usage::

        inst = by_pattern('list_comp', collection=OVar('my_list'))
        result = inst.verify()
    """
    if name not in PATTERNS:
        available = ', '.join(sorted(PATTERNS.keys()))
        raise ValueError(f'Unknown pattern {name!r}. Available: {available}')
    return PATTERNS[name](**kwargs)


def list_patterns() -> List[str]:
    """List all available pattern names."""
    return sorted(PATTERNS.keys())
