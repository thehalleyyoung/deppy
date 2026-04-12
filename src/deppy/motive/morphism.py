"""MotiveMorphism — structure-preserving maps between motives.

A morphism φ: M(f) → M(g) between computational motives consists of:

    φ_Σ : Σ_f → Σ_g       — mapping between algebraic signatures
    φ_G : G_f → G_g       — functor between data flow categories
    φ_H : H_f → H_g       — induced map on cohomology

such that all three components are compatible:
    φ_H = H(φ_G)          — the cohomology map is induced by the functor
    φ_Σ respects sorts     — sort(φ_Σ(op)) = sort(op)
    φ_Σ respects effects   — effect(φ_Σ(op)) = effect(op)
    φ_Σ respects refinements

An isomorphism is a morphism where φ_Σ is a bijection.
A refinement is a morphism where φ_Σ is an injection (spec → impl).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from deppy.motive.sorts import sorts_compatible
from deppy.motive.operations import TypedOp, INCOMPATIBLE_OPS, COMPATIBLE_FAMILIES
from deppy.motive.motive import Motive


@dataclass
class MotiveMorphism:
    """A structure-preserving map between computational motives."""
    source: Motive
    target: Motive
    op_mapping: Dict[int, int] = field(default_factory=dict)
    is_valid: bool = False
    explanation: str = ""

    @property
    def is_bijection(self) -> bool:
        """True if the operation mapping is a bijection (isomorphism)."""
        if not self.is_valid:
            return False
        if len(self.op_mapping) != len(self.source.operations):
            return False
        return len(set(self.op_mapping.values())) == len(self.target.operations)

    @property
    def is_injection(self) -> bool:
        """True if the mapping is injective (refinement)."""
        if not self.is_valid:
            return False
        return len(set(self.op_mapping.values())) == len(self.op_mapping)

    @staticmethod
    def names_compatible(name_f: str, name_g: str) -> bool:
        """Check if two abstract operation names are compatible under φ.

        STRICT: requires exact name match, or explicit cross-family
        compatibility for structural equivalences (e.g., Loop↔Comprehension).
        Same-family different-operation names are NOT compatible
        (Arith.add ≠ Arith.mul) — this is the key correctness constraint.
        """
        if name_f == name_g:
            return True

        # Check forbidden pairs (case-insensitive)
        pair = frozenset({name_f.lower(), name_g.lower()})
        norm_incompat = frozenset(
            frozenset(n.lower() for n in p) for p in INCOMPATIBLE_OPS
        )
        if pair in norm_incompat:
            return False

        # Only allow cross-family compatibility, NOT same-family different-op
        family_f = name_f.split('.')[0] if '.' in name_f else name_f
        family_g = name_g.split('.')[0] if '.' in name_g else name_g

        # Same family, different operation → NOT compatible
        if family_f == family_g:
            return False

        # Cross-family compatibility (structural equivalences)
        if frozenset({family_f, family_g}) in COMPATIBLE_FAMILIES:
            return True

        return False

    @staticmethod
    def ops_compatible(op_f: TypedOp, op_g: TypedOp) -> bool:
        """Check if two typed operations can be mapped to each other."""
        # Name compatibility
        if not MotiveMorphism.names_compatible(op_f.name, op_g.name):
            return False

        # Sort signature
        if len(op_f.input_sorts) != len(op_g.input_sorts):
            return False
        if not sorts_compatible(op_f.output_sort, op_g.output_sort):
            return False
        for sf, sg in zip(op_f.input_sorts, op_g.input_sorts):
            if not sorts_compatible(sf, sg):
                return False

        # Effect
        if op_f.effect != op_g.effect:
            return False

        # Refinements: must overlap if both non-empty
        if op_f.refinements and op_g.refinements:
            if not (op_f.refinements & op_g.refinements):
                return False

        return True
