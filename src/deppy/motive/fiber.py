"""TypeFiber — the dependent type at a program point.

From Martin-Löf dependent type theory, a TypeFiber is the type that
sits over a particular sort at a particular program point.  Formally:

    Fiber(p) = Σ(s : Sort). {r ∈ Refinement | r holds at p} × Scope(p)

where Scope(p) maps each variable in scope at p to its sort.

The fiber is the *section* of the type presheaf at a single point.
The restriction map between fibers (along a data flow edge) is the
projection that drops out-of-scope variables and propagates refinements.

Two fibers *agree on overlap* (the Čech cocycle condition) iff their
common variables have compatible sorts and compatible refinements.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, FrozenSet, Optional, Set, Tuple

from deppy.motive.sorts import Sort, sorts_compatible, sort_join
from deppy.motive.operations import Refinement, Effect, TypedOp


@dataclass(frozen=True)
class TypeFiber:
    """The dependent type fiber at a program point.

    This is the mathematical object assigned by the type presheaf
    to each vertex of the nerve complex.

    Attributes:
        sort: The principal sort produced at this point.
        refinements: Decidable predicates refining the sort.
        scope: Variables in scope with their sorts (the context Γ).
        reads: Variables read at this point.
        writes: Variables written at this point.
        operations: TypedOps performed at this point.
    """
    sort: Sort = Sort.TOP
    refinements: FrozenSet[Refinement] = frozenset()
    scope: FrozenSet[Tuple[str, Sort]] = frozenset()
    reads: FrozenSet[str] = frozenset()
    writes: FrozenSet[str] = frozenset()
    operations: Tuple[TypedOp, ...] = ()

    @property
    def scope_dict(self) -> Dict[str, Sort]:
        """Scope as a mutable dict."""
        return dict(self.scope)

    @property
    def sort_set(self) -> Set[Sort]:
        """All sorts present in this fiber (including scope)."""
        result = {self.sort}
        for _, s in self.scope:
            result.add(s)
        return result

    def restrict(self, variables: FrozenSet[str]) -> TypeFiber:
        """Restrict this fiber to a subset of variables.

        This is the restriction map of the presheaf along an inclusion
        morphism.  It projects the scope down to the specified variables.
        """
        new_scope = frozenset((v, s) for v, s in self.scope if v in variables)
        new_reads = self.reads & variables
        new_writes = self.writes & variables
        return TypeFiber(
            sort=self.sort,
            refinements=self.refinements,
            scope=new_scope,
            reads=new_reads,
            writes=new_writes,
            operations=self.operations,
        )

    def agrees_with(self, other: TypeFiber) -> bool:
        """Check if two fibers agree on their overlap (Čech cocycle condition).

        Two fibers agree iff:
        1. Their principal sorts are compatible
        2. All shared variables have compatible sorts
        3. Their refinement sets are not contradictory
        """
        # Sort compatibility
        if not sorts_compatible(self.sort, other.sort):
            return False

        # Scope overlap check
        self_scope = self.scope_dict
        other_scope = other.scope_dict
        shared_vars = set(self_scope.keys()) & set(other_scope.keys())
        for var in shared_vars:
            if not sorts_compatible(self_scope[var], other_scope[var]):
                return False

        # Refinement compatibility: contradictory pairs
        _CONTRADICTIONS = {
            (Refinement.SORTED, Refinement.REVERSED),
            (Refinement.POSITIVE, Refinement.NON_NEGATIVE),  # not contradictory but distinct
        }
        for r1 in self.refinements:
            for r2 in other.refinements:
                if (r1, r2) in _CONTRADICTIONS or (r2, r1) in _CONTRADICTIONS:
                    return False

        return True

    def join(self, other: TypeFiber) -> TypeFiber:
        """Join two fibers (least upper bound in the fiber lattice).

        Used when merging branches (if/else) or gluing sections.
        """
        new_sort = sort_join(self.sort, other.sort)
        new_refinements = self.refinements & other.refinements  # intersection
        self_scope = self.scope_dict
        other_scope = other.scope_dict
        all_vars = set(self_scope.keys()) | set(other_scope.keys())
        new_scope_items = []
        for v in sorted(all_vars):
            s1 = self_scope.get(v, Sort.BOT)
            s2 = other_scope.get(v, Sort.BOT)
            new_scope_items.append((v, sort_join(s1, s2)))
        return TypeFiber(
            sort=new_sort,
            refinements=new_refinements,
            scope=frozenset(new_scope_items),
            reads=self.reads | other.reads,
            writes=self.writes | other.writes,
            operations=self.operations + other.operations,
        )

    @staticmethod
    def empty() -> TypeFiber:
        """The trivial (empty) fiber — initial object in the fiber category."""
        return TypeFiber()

    def obstruction_with(self, other: TypeFiber) -> Optional[str]:
        """Compute the obstruction between two fibers.

        Returns None if they agree, or a description of the obstruction
        (which becomes an element of H¹).
        """
        if not sorts_compatible(self.sort, other.sort):
            return f"sort {self.sort.name} ≠ {other.sort.name}"

        self_scope = self.scope_dict
        other_scope = other.scope_dict
        for var in set(self_scope.keys()) & set(other_scope.keys()):
            if not sorts_compatible(self_scope[var], other_scope[var]):
                return f"var {var}: {self_scope[var].name} ≠ {other_scope[var].name}"

        return None


@dataclass(frozen=True)
class FiberMorphism:
    """A morphism between type fibers (restriction along an operation).

    This is the structure map of the type presheaf.  Given an operation
    op: A → B, the fiber morphism maps Fiber(B) back to Fiber(A)
    (contravariant, since presheaves are contravariant functors).
    """
    source_fiber: TypeFiber
    target_fiber: TypeFiber
    operation: TypedOp
    sort_compatible: bool = True

    @staticmethod
    def from_operation(source: TypeFiber, target: TypeFiber,
                       op: TypedOp) -> FiberMorphism:
        """Construct a fiber morphism from an operation."""
        compatible = sorts_compatible(source.sort, op.output_sort)
        return FiberMorphism(
            source_fiber=source,
            target_fiber=target,
            operation=op,
            sort_compatible=compatible,
        )

    @property
    def is_obstruction(self) -> bool:
        """True if this morphism represents a type obstruction (H¹ class)."""
        return not self.sort_compatible or not self.source_fiber.agrees_with(self.target_fiber)
