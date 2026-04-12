"""Typed operations — morphisms in the Lawvere theory of programs.

Every program operation is a morphism in an abstract algebra:
  op : Sort₁ × ... × Sortₙ → Sort

Each operation carries:
  • Sort signature   — domain and codomain in the sort lattice
  • Refinements      — dependent-type predicates (sorted, injective, ...)
  • Effect           — computational side-effect (pure, mutate, recurse, ...)

Operations are the *generators* of the computational motive's algebra.
Two motives are isomorphic when there exists a bijection between their
generators that preserves sorts, refinements, effects, and composition.

From algebraic K-theory: the Grothendieck group K₀ of the effect monoid
classifies resource usage.  Programs using equivalent resources have
isomorphic K₀ groups — a necessary condition for motive isomorphism.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import IntEnum, auto
from typing import Dict, FrozenSet, Tuple

from deppy.motive.sorts import Sort


# ─── Refinement Predicates ─────────────────────────────────────────
#
# From Martin-Löf dependent type theory: each sort is refined by
# decidable predicates constraining its inhabitants.  These form the
# fiber structure of the dependent type bundle over the sort lattice.

class Refinement(IntEnum):
    """Decidable predicates refining abstract sorts (type fibers)."""
    SORTED            = 0
    REVERSED          = auto()
    LENGTH_PRESERVING = auto()
    PERMUTATION       = auto()
    FILTERED          = auto()
    MAPPED            = auto()
    ACCUMULATED       = auto()
    POSITIVE          = auto()
    NON_NEGATIVE      = auto()
    BOUNDED           = auto()
    INJECTIVE         = auto()
    IDEMPOTENT        = auto()
    MONOTONE          = auto()
    COMMUTATIVE       = auto()
    ASSOCIATIVE       = auto()


# ─── Computational Effects ─────────────────────────────────────────
#
# From algebraic effect theory: each operation carries an effect drawn
# from a monoid (Effect, ∘, PURE).

class Effect(IntEnum):
    """Computational effects forming a monoid."""
    PURE     = 0    # No side effects
    MUTATE   = auto()  # In-place mutation
    ALLOCATE = auto()  # Heap allocation
    ITERATE  = auto()  # Loop iteration (bounded recursion)
    RECURSE  = auto()  # General recursion (unbounded)
    CALL_EXT = auto()  # External/builtin call (opaque)
    IO       = auto()  # I/O side effect (print, file, network)


# ─── Typed Operations ──────────────────────────────────────────────

@dataclass(frozen=True)
class TypedOp:
    """A morphism in the Lawvere theory: a typed operation with metadata.

    This is the fundamental building block of computational motives.
    The motive's algebraic signature Σ is a multiset of TypedOps.
    """
    name: str                               # Abstract operation name
    input_sorts: Tuple[Sort, ...]           # Domain sorts
    output_sort: Sort                       # Codomain sort
    refinements: FrozenSet[Refinement]      # Dependent type predicates
    effect: Effect                          # Computational effect

    @property
    def sort_signature(self) -> Tuple[Tuple[Sort, ...], Sort]:
        """The sort-level type of this operation (ignoring refinements)."""
        return (self.input_sorts, self.output_sort)

    @property
    def family(self) -> str:
        """The operation family (prefix before the dot)."""
        return self.name.split('.')[0] if '.' in self.name else self.name

    def classification_key(self) -> Tuple:
        """Full classification key — what a motive isomorphism must preserve."""
        return (
            self.name,
            self.sort_signature,
            self.effect,
            tuple(sorted(self.refinements)),
        )


# ─── Data Flow Edges ───────────────────────────────────────────────

@dataclass(frozen=True)
class FlowEdge:
    """A morphism in the data-flow category.

    Edges connect basic blocks and carry the type of data flowing between them.
    The collection of FlowEdges forms the data-flow graph G in the motive
    M(f) = (Σ, G, H).  The nerve of G is the site for Čech cohomology.
    """
    source_block: int
    target_block: int
    source_sort: Sort
    target_sort: Sort
    op_index: int


# ─── Operation Abstraction Tables ──────────────────────────────────
#
# These tables define the abstraction function α that maps concrete Python
# operations to abstract TypedOp names.  This is the Galois connection
# between concrete and abstract semantics.

# Method → abstract name (list.append and deque.append are both Seq.push)
OP_ABSTRACTION: Dict[str, str] = {
    'append': 'Seq.push', 'appendleft': 'Seq.push', 'extend': 'Seq.extend',
    'insert': 'Seq.insert', 'pop': 'Seq.pop', 'popleft': 'Seq.pop',
    'sort': 'Seq.sort', 'reverse': 'Seq.reverse',
    'add': 'Set.insert', 'discard': 'Set.remove', 'remove': 'Set.remove',
    'union': 'Set.union', 'intersection': 'Set.intersect', 'difference': 'Set.diff',
    'get': 'Map.lookup', 'setdefault': 'Map.insert_default',
    'update': 'Map.merge', 'keys': 'Map.keys', 'values': 'Map.values',
    'items': 'Map.items',
    'join': 'Str.join', 'split': 'Str.split', 'strip': 'Str.trim',
    'replace': 'Str.replace', 'find': 'Str.search',
    'lower': 'Str.transform', 'upper': 'Str.transform',
    'copy': 'Clone.shallow', 'deepcopy': 'Clone.deep',
}

# Operations and their associated refinement predicates
OP_REFINEMENTS: Dict[str, FrozenSet[Refinement]] = {
    'Seq.sort': frozenset({Refinement.SORTED, Refinement.PERMUTATION}),
    'Seq.reverse': frozenset({Refinement.REVERSED, Refinement.PERMUTATION}),
    'Seq.push': frozenset({Refinement.LENGTH_PRESERVING}),
    'Set.union': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT}),
    'Set.intersect': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT}),
}

# Accumulator operations (from AugAssign) and their refinements
AUGOP_ABSTRACTION: Dict[str, str] = {
    'Add': 'Accum.sum', 'Sub': 'Accum.diff',
    'Mult': 'Accum.product', 'BitOr': 'Accum.union',
    'BitAnd': 'Accum.intersect', 'BitXor': 'Accum.xor',
}

ACCUM_REFINEMENTS: Dict[str, FrozenSet[Refinement]] = {
    'Accum.sum': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.ACCUMULATED}),
    'Accum.product': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.ACCUMULATED}),
    'Accum.union': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT, Refinement.ACCUMULATED}),
    'Accum.intersect': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT, Refinement.ACCUMULATED}),
    'Accum.diff': frozenset({Refinement.ACCUMULATED}),
    'Accum.xor': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.ACCUMULATED}),
}

# Semantically incompatible operation pairs (for isomorphism checking)
INCOMPATIBLE_OPS: frozenset = frozenset({
    frozenset({'Clone.shallow', 'Clone.deep'}),
    frozenset({'Arith.FloorDiv', 'Arith.TrueDiv'}),
    frozenset({'Cmp.lt', 'Cmp.gt'}),
    frozenset({'Cmp.le', 'Cmp.ge'}),
    frozenset({'Accum.sum', 'Accum.product'}),
    frozenset({'Accum.sum', 'Accum.intersect'}),
    frozenset({'Accum.product', 'Accum.union'}),
    frozenset({'Seq.sort', 'Seq.reverse'}),
    frozenset({'Arith.Add', 'Arith.Sub'}),
    frozenset({'Arith.Mult', 'Arith.Div'}),
    frozenset({'Arith.Mod', 'Arith.FloorDiv'}),
    frozenset({'Logic.And', 'Logic.Or'}),
})

# Families that are compatible under isomorphism
COMPATIBLE_FAMILIES: frozenset = frozenset({
    frozenset({'Seq', 'Construct'}),
    frozenset({'Iter', 'Loop'}),
    frozenset({'Accum', 'Arith'}),
    frozenset({'Comprehension', 'Iter'}),
    frozenset({'Comprehension', 'Loop'}),
})
