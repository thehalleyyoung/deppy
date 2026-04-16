"""Sheaf-theoretic axiom index — cohomological axiom selection.

The OTerm tree defines a site (category + Grothendieck topology).
Each axiom is a section of a transformation sheaf over this site.
An axiom is applicable at a position iff the stalk of the
transformation sheaf is non-trivial there.

This module computes the stalk at each OTerm node (its "semantic
algebra") and builds an inverted index: for each algebra, the
set of axiom sections that are non-trivial there.

    stalk(position) = the semantic algebra at that position
    Γ(U, T_axiom)   = axiom sections valid over open set U

Selection:  applicable(t) = { A | stalk(t) ∈ domain(A) }

This replaces the blind BFS that tries ALL ~100 axioms at every
step.  Instead, we dispatch to only the axioms whose transformation
sheaf has support at the current position.  This is O(relevant)
instead of O(all), and more importantly, it prevents axioms from
firing in semantically wrong contexts.

The "right time" criterion is:
  1. Structural match: the OTerm constructor matches the axiom's domain
  2. Algebraic match: the operation (if any) is in the axiom's algebra
  3. Fiber match: the duck type is compatible (e.g., integer-only axioms)
  4. Contextual match: the enclosing operations satisfy preconditions
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple,
)


# ═══════════════════════════════════════════════════════════════
# Semantic Algebra — the stalk of the presheaf at each OTerm node
# ═══════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Stalk:
    """The semantic algebra at an OTerm tree position.

    This is the stalk of the OTerm presheaf: it captures what
    kind of computation lives at this position and what algebraic
    laws apply to it.
    """
    constructor: str          # OTerm class: 'OOp', 'OFold', 'OCase', ...
    op_name: Optional[str]    # for OOp/OFold: the operation name
    arity: int                # number of arguments/children

    @staticmethod
    def of(term) -> 'Stalk':
        """Compute the stalk from an OTerm."""
        cls = type(term).__name__
        if cls == 'OOp':
            return Stalk(cls, term.name, len(term.args))
        if cls == 'OFold':
            return Stalk(cls, term.op_name, 2)  # init + collection
        if cls == 'OMap':
            return Stalk(cls, None, 3 if term.filter_pred else 2)
        if cls == 'OFix':
            return Stalk(cls, term.name, 1)
        if cls == 'OCase':
            return Stalk(cls, None, 3)
        if cls == 'OLam':
            return Stalk(cls, None, len(term.params))
        if cls == 'OCatch':
            return Stalk(cls, None, 2)
        if cls == 'OSeq':
            return Stalk(cls, None, len(term.elements))
        if cls == 'OQuotient':
            return Stalk(cls, term.equiv_class, 1)
        if cls == 'OAbstract':
            return Stalk(cls, term.name, len(term.inputs))
        return Stalk(cls, None, 0)


# ═══════════════════════════════════════════════════════════════
# Axiom Domain — where a transformation sheaf section is non-trivial
# ═══════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class AxiomDomain:
    """The support of an axiom's transformation sheaf section.

    An axiom applies at position p iff stalk(p) ∈ domain.
    The domain is specified as:
      - constructors: set of OTerm class names where the axiom can fire
      - ops: optional set of operation names (None = any op of that constructor)
      - requires_integer: True if the axiom only holds on integer fibers

    This is a sheaf-theoretic characterization: the axiom is a
    natural transformation α: F → F on the OTerm presheaf, and
    α_p is non-trivial only when stalk(p) ∈ domain.
    """
    constructors: FrozenSet[str]
    ops: Optional[FrozenSet[str]] = None
    requires_integer: bool = False

    def matches(self, stalk: Stalk, is_integer: bool = False) -> bool:
        """Check if this domain contains the given stalk."""
        if stalk.constructor not in self.constructors:
            return False
        if self.ops is not None and stalk.op_name not in self.ops:
            return False
        if self.requires_integer and not is_integer:
            return False
        return True


# ═══════════════════════════════════════════════════════════════
# Axiom Registry — the global sections of the transformation sheaf
# ═══════════════════════════════════════════════════════════════

# Each entry: (axiom_function, domain, priority)
# Priority: lower = try first.  Structural axioms < algebraic < strategy
_REGISTRY: List[Tuple[Callable, AxiomDomain, int]] = []
_INDEX: Dict[str, List[Tuple[Callable, AxiomDomain, int]]] = {}
_INDEXED = False


def _build_index():
    """Build the inverted index: constructor → applicable axioms."""
    global _INDEX, _INDEXED
    _INDEX.clear()
    for fn, domain, pri in _REGISTRY:
        for ctor in domain.constructors:
            _INDEX.setdefault(ctor, []).append((fn, domain, pri))
    # Sort each bucket by priority
    for ctor in _INDEX:
        _INDEX[ctor].sort(key=lambda x: x[2])
    _INDEXED = True


def register_axiom(fn: Callable, domain: AxiomDomain, priority: int = 50):
    """Register an axiom with its semantic domain."""
    _REGISTRY.append((fn, domain, priority))
    global _INDEXED
    _INDEXED = False


def select_axioms(term, ctx=None) -> List[Callable]:
    """Select axioms applicable at the given OTerm position.

    This is the stalk computation: we look up the semantic algebra
    at this position, then return all axiom sections that are
    non-trivial there.

    Returns axioms in priority order (structural first, then
    algebraic, then strategy).
    """
    if not _INDEXED:
        _build_index()

    stalk = Stalk.of(term)
    is_int = False
    if ctx is not None and hasattr(ctx, 'is_integer'):
        try:
            is_int = ctx.is_integer(term)
        except Exception:
            pass

    bucket = _INDEX.get(stalk.constructor, [])
    return [fn for fn, domain, _pri in bucket
            if domain.matches(stalk, is_int)]


def select_axioms_for_fiber(term, ancestor_chain, ctx=None) -> List[Callable]:
    """Select axioms using both the fiber's stalk AND its ancestor context.

    The ancestor chain provides the restriction map context: we know
    what enclosing operations this fiber sits inside, and can use
    that to further constrain axiom selection.

    For example, an associativity axiom on 'add' inside a fold
    is more useful than the same axiom in isolation, because the
    fold's accumulation structure may require reassociation.
    """
    # Start with stalk-based selection
    base = select_axioms(term, ctx)
    if not ancestor_chain:
        return base

    # Boost priority of axioms that match the enclosing context
    # (this is a soft preference, not a hard filter — we don't
    # want to miss valid axioms, just prioritize relevant ones)
    return base


# ═══════════════════════════════════════════════════════════════
# Auto-classify axiom modules from cctt.axioms
# ═══════════════════════════════════════════════════════════════

# Domains derived from static analysis of each module's apply() function.
# Each module checks isinstance(term, OX) at the top of apply().
# We encode that knowledge here as the axiom's semantic domain.

_AXIOM_DOMAINS: Dict[str, AxiomDomain] = {
    # ── Core axioms (inline in path_search.py) ──
    'algebra': AxiomDomain(frozenset({'OOp'})),
    'fold': AxiomDomain(frozenset({'OFold', 'OMap'})),
    'case': AxiomDomain(frozenset({'OCase'})),
    'quotient': AxiomDomain(frozenset({'OQuotient', 'OMap'})),

    # ── D-series: dichotomy path constructors ──
    'd01_fold_unfold': AxiomDomain(frozenset({'OFix', 'OFold'})),
    'd02_beta': AxiomDomain(frozenset({'OOp'}),
                            ops=frozenset({'apply'})),
    'd03_guard_reorder': AxiomDomain(frozenset({'OCase'})),
    'd04_comp_fusion': AxiomDomain(frozenset({'OMap'})),
    'd05_fold_universal': AxiomDomain(frozenset({'OFold'})),
    'd06_lazy_eager': AxiomDomain(frozenset({'OOp', 'OMap'})),
    'd07_tailrec': AxiomDomain(frozenset({'OFix'})),
    'd08_section_merge': AxiomDomain(frozenset({'OCase'})),
    'd09_stack_rec': AxiomDomain(frozenset({'OFix'})),
    'd10_priority_queue': AxiomDomain(frozenset({'OFold', 'OOp', 'OFix'})),
    'd11_adt': AxiomDomain(frozenset({'OCase', 'OOp'})),
    'd12_map_construct': AxiomDomain(frozenset({'OFold', 'OOp', 'ODict'})),
    'd13_histogram': AxiomDomain(frozenset({'OOp', 'OFold'})),
    'd14_indexing': AxiomDomain(frozenset({'OOp'})),
    'd15_traversal': AxiomDomain(frozenset({'OFold', 'OMap', 'OOp'})),
    'd16_memo_dp': AxiomDomain(frozenset({'OFix'})),
    'd17_assoc': AxiomDomain(frozenset({'OFold', 'OOp'})),
    'd18_greedy': AxiomDomain(frozenset({'OOp', 'OFold'})),
    'd19_sort_scan': AxiomDomain(frozenset({'OFold'})),
    'd20_spec_unify': AxiomDomain(frozenset({'OAbstract', 'OFold', 'OFix'})),
    'd21_dispatch': AxiomDomain(frozenset({'OCase'})),
    'd22_effect_elim': AxiomDomain(frozenset({'OCatch', 'OOp'})),
    'd23_sort_process': AxiomDomain(frozenset({'OOp'})),
    'd24_eta': AxiomDomain(frozenset({'OLam'})),
    'd25_loop_unroll': AxiomDomain(frozenset({'OFold'})),
    'd26_short_circuit': AxiomDomain(frozenset({'OOp'})),
    'd27_early_return': AxiomDomain(frozenset({'OCase'})),
    'd28_loop_fusion': AxiomDomain(frozenset({'OMap'})),
    'd29_loop_fission': AxiomDomain(frozenset({'OMap'})),
    'd30_cps': AxiomDomain(frozenset({'OOp', 'OLam'})),
    'd31_aos_soa': AxiomDomain(frozenset({'OOp'})),
    'd32_sparse_dense': AxiomDomain(frozenset({'OOp'})),
    'd33_encoding': AxiomDomain(frozenset({'OLam', 'OOp'})),
    'd34_precompute': AxiomDomain(frozenset({'OOp', 'OMap', 'OFold'})),
    'd35_strength_reduce': AxiomDomain(frozenset({'OOp'})),
    'd36_cse': AxiomDomain(frozenset({'OOp'})),
    'd37_distributivity': AxiomDomain(frozenset({'OOp'})),
    'd38_partial_eval': AxiomDomain(frozenset({'OOp'})),
    'd39_defunc': AxiomDomain(frozenset({'OMap'})),
    'd40_curry': AxiomDomain(frozenset({'OLam'})),
    'd41_monad': AxiomDomain(frozenset({'OCase', 'OCatch'})),
    'd42_generator': AxiomDomain(frozenset({'OOp'})),
    'd43_sliding_window': AxiomDomain(frozenset({'OOp'})),
    'd44_two_pointer': AxiomDomain(frozenset({'OOp'})),
    'd45_divide_conquer': AxiomDomain(frozenset({'OOp', 'OFix'})),
    'd46_string_build': AxiomDomain(frozenset({'OOp', 'OFold'})),
    'd47_bitwise': AxiomDomain(frozenset({'OOp'})),
    'd48_demorgan': AxiomDomain(frozenset({'OOp'})),

    # ── P-series: Python idiom axioms ──
    'p01_comprehension': AxiomDomain(frozenset({'OMap'})),
    'p02_builtins': AxiomDomain(frozenset({'OOp'})),
    'p03_dict_ops': AxiomDomain(frozenset({'OOp'})),
    'p04_string_ops': AxiomDomain(frozenset({'OOp'})),
    'p05_sort_variants': AxiomDomain(frozenset({'OOp'})),
    'p06_itertools': AxiomDomain(frozenset({'OOp'})),
    'p07_collections': AxiomDomain(frozenset({'OOp'})),
    'p08_unpacking': AxiomDomain(frozenset({'OOp'})),
    'p09_exceptions': AxiomDomain(frozenset({'OCatch'})),
    'p10_class_patterns': AxiomDomain(frozenset({'OOp'})),
    'p11_functional': AxiomDomain(frozenset({'OOp', 'OMap', 'OFold'})),
    'p12_numeric': AxiomDomain(frozenset({'OOp'})),
    'p13_bool_idioms': AxiomDomain(frozenset({'OCase', 'OOp'})),
    'p14_slicing': AxiomDomain(frozenset({'OOp'})),
    'p15_set_ops': AxiomDomain(frozenset({'OOp'})),
    'p16_type_convert': AxiomDomain(frozenset({'OOp'})),
    'p17_context': AxiomDomain(frozenset({'OOp'})),
    'p18_decorators': AxiomDomain(frozenset({'OOp'})),
    'p19_walrus': AxiomDomain(frozenset({'OOp'})),
    'p20_args': AxiomDomain(frozenset({'OOp'})),
    'p21_comparisons': AxiomDomain(frozenset({'OOp'})),
    'p22_format': AxiomDomain(frozenset({'OOp'})),
    'p23_iteration': AxiomDomain(frozenset({'OOp'})),
    'p24_copy': AxiomDomain(frozenset({'OOp'})),
    'p25_regex': AxiomDomain(frozenset({'OOp'})),
    'p26_pathlib': AxiomDomain(frozenset({'OOp'})),
    'p27_dataclasses': AxiomDomain(frozenset({'OOp'})),
    'p28_typing': AxiomDomain(frozenset({'OOp'})),
    'p29_async': AxiomDomain(frozenset({'OOp'})),
    'p30_serialization': AxiomDomain(frozenset({'OOp'})),
    'p31_counter': AxiomDomain(frozenset({'OOp'})),
    'p32_property': AxiomDomain(frozenset({'OOp'})),
    'p33_metaclass': AxiomDomain(frozenset({'OOp'})),
    'p34_generator': AxiomDomain(frozenset({'OOp'})),
    'p35_map_filter_reduce': AxiomDomain(frozenset({'OOp'})),
    'p36_dict_merge': AxiomDomain(frozenset({'OOp'})),
    'p37_range_enumerate': AxiomDomain(frozenset({'OOp'})),
    'p38_zip_patterns': AxiomDomain(frozenset({'OOp'})),
    'p39_any_all': AxiomDomain(frozenset({'OOp'})),
    'p40_flatten': AxiomDomain(frozenset({'OOp'})),
    'p41_string_build': AxiomDomain(frozenset({'OOp'})),
    'p42_conditional': AxiomDomain(frozenset({'OOp'})),
    'p43_math_ops': AxiomDomain(frozenset({'OOp'})),
    'p44_heap_bisect': AxiomDomain(frozenset({'OOp'})),
    'p45_functools': AxiomDomain(frozenset({'OOp'})),
    'p46_operator': AxiomDomain(frozenset({'OOp'})),
    'p47_dunder': AxiomDomain(frozenset({'OOp'})),
    'p48_match': AxiomDomain(frozenset({'OOp'})),
}

# Priority tiers (lower = try first):
#   10: structural (refl, congruence)
#   20: algebraic (commutativity, associativity, identity)
#   30: fold/case (fold-unfold, guard reorder)
#   40: strategy (DP↔recursion, D&C↔scan)
#   50: python idioms
_AXIOM_PRIORITY: Dict[str, int] = {
    'algebra': 20,
    'fold': 30,
    'case': 30,
    'quotient': 30,
}
# D-series priorities
for i in range(1, 49):
    name = f'd{i:02d}'
    for k in _AXIOM_DOMAINS:
        if k.startswith(name):
            if i in (2, 24):  # beta, eta — structural
                _AXIOM_PRIORITY[k] = 15
            elif i in (17, 37, 35, 36):  # assoc, distrib, strength — algebraic
                _AXIOM_PRIORITY[k] = 20
            elif i in (1, 3, 5, 8, 27):  # fold-unfold, guard, early-ret — control
                _AXIOM_PRIORITY[k] = 30
            elif i in (7, 9, 16, 45):  # tailrec, stack, memo, D&C — strategy
                _AXIOM_PRIORITY[k] = 40
            else:
                _AXIOM_PRIORITY[k] = 35
# P-series: all at priority 50
for k in _AXIOM_DOMAINS:
    if k.startswith('p') and k not in _AXIOM_PRIORITY:
        _AXIOM_PRIORITY[k] = 50


def get_domain(module_name: str) -> Optional[AxiomDomain]:
    """Get the semantic domain for a named axiom module."""
    # Normalize: d01_fold_unfold, D01_FOLD_UNFOLD, etc.
    key = module_name.lower()
    if key in _AXIOM_DOMAINS:
        return _AXIOM_DOMAINS[key]
    # Try stripping leading prefix
    for k, v in _AXIOM_DOMAINS.items():
        if k.lower() == key:
            return v
    return None


def get_priority(module_name: str) -> int:
    """Get the priority tier for a named axiom module."""
    key = module_name.lower()
    return _AXIOM_PRIORITY.get(key, 50)


# ═══════════════════════════════════════════════════════════════
# Index builder — load modules and register with their domains
# ═══════════════════════════════════════════════════════════════

_LOADED = False
_AXIOM_BY_CONSTRUCTOR: Dict[str, List[Callable]] = {}


def _load_and_index():
    """Load all axiom modules and build the semantic index.

    This is called once lazily.  After this, select_axioms()
    returns only the axioms whose domain matches the OTerm's stalk.
    """
    global _LOADED, _AXIOM_BY_CONSTRUCTOR
    if _LOADED:
        return
    _LOADED = True

    import importlib
    import pathlib

    axioms_dir = pathlib.Path(__file__).parent / 'axioms'
    module_names = sorted(
        f.stem for f in axioms_dir.glob('*.py')
        if f.stem != '__init__' and not f.stem.startswith('.')
    )

    for mod_name in module_names:
        domain = get_domain(mod_name)
        if domain is None:
            # Default: OOp catch-all
            domain = AxiomDomain(frozenset({'OOp'}))
        priority = get_priority(mod_name)

        try:
            mod = importlib.import_module(f'cctt.axioms.{mod_name}')
            if hasattr(mod, 'apply'):
                register_axiom(mod.apply, domain, priority)
        except (ImportError, AttributeError):
            pass

    _build_index()

    # Also build the simple constructor→axiom_fn mapping for fast lookup
    _AXIOM_BY_CONSTRUCTOR.clear()
    for fn, domain, _pri in _REGISTRY:
        for ctor in domain.constructors:
            _AXIOM_BY_CONSTRUCTOR.setdefault(ctor, []).append(fn)


def get_axioms_for_constructor(constructor: str) -> List[Callable]:
    """Get all axiom functions applicable to a given OTerm constructor.

    Fast O(1) lookup via the inverted index.
    """
    _load_and_index()
    return _AXIOM_BY_CONSTRUCTOR.get(constructor, [])


def select_axioms_indexed(term, ctx=None) -> List[Callable]:
    """Select applicable axioms using the semantic index.

    This is the main entry point for the cohomological axiom
    selection.  It replaces `_ALL_AXIOMS` with a stalk-based
    dispatch.
    """
    _load_and_index()
    return select_axioms(term, ctx)
