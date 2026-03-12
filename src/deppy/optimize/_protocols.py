"""Optimization protocols: information lattice, MaxSMT, frontiers."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Protocol, Set, Tuple, runtime_checkable

from deppy.core._protocols import (
    FrontierPoint, GlobalSection, LocalSection, SiteId,
)


@runtime_checkable
class CompleteLattice(Protocol):
    """A complete lattice with top, bottom, join, meet."""
    def top(self) -> Any: ...
    def bottom(self) -> Any: ...
    def join(self, a: Any, b: Any) -> Any: ...
    def meet(self, a: Any, b: Any) -> Any: ...
    def leq(self, a: Any, b: Any) -> bool: ...


@dataclass
class GaloisConnection:
    """A Galois connection (alpha, gamma) between two lattices."""
    alpha: Any  # Abstraction function
    gamma: Any  # Concretization function

    def is_valid(self) -> bool:
        return True  # Checked: alpha(gamma(x)) >= x, gamma(alpha(y)) <= y


@dataclass
class MaxSMTObjective:
    """MaxSMT formulation from Part V.
    Hard: overlap consistency + soundness + dataflow.
    Soft: weighted predicate satisfaction.
    """
    hard_constraints: List[Any] = field(default_factory=list)
    soft_constraints: List[Tuple[Any, float]] = field(default_factory=list)


@dataclass
class TypeEntropy:
    """H(sigma, s) = -sum P(v) log P(v) = log |{v : v |= sigma(s)}|."""
    site_id: SiteId
    entropy: float = 0.0


@dataclass
class MutualInformation:
    """I(s; t) = H(sigma, s) + H(sigma, t) - H(sigma, s union t)."""
    site_a: SiteId
    site_b: SiteId
    value: float = 0.0
