"""Topos-theoretic infrastructure for equivalence checking.

This module provides the **categorical backbone** that the rest of the
equivalence checker builds on.  It implements:

* **PresheafMorphism** — natural transformations η: F ⇒ G between
  concrete presheaves, with per-site evidence predicates.
* **SectionTransformComponent** — individual components of a presheaf
  morphism at a given site.

The actual categorical constructions (pullback, equaliser, pushout) are
handled directly in their consumer modules (``fiber_product``,
``local_checker``, ``global_checker``).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Callable,
    Dict,
    Optional,
)

from deppy.core._protocols import (
    LocalSection,
    SiteId,
)
from deppy.core.presheaf import ConcretePresheaf
from deppy.types.refinement import (
    Predicate,
    TruePred,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Categorical objects & morphisms in the presheaf topos
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class PresheafMorphism:
    """A natural transformation η: F ⇒ G between concrete presheaves.

    Components are stored per site-id.  Each component is a function
    ``F(U) → G(U)`` realised as a predicate transformer: given a
    ``LocalSection`` of F at U the component produces a ``LocalSection``
    of G at U, together with an *evidence predicate* that the
    transformation preserves the refinement predicate.

    Naturality:  for every morphism ``r: V → U`` in the site category,
    ``η_V ∘ F(r) = G(r) ∘ η_U``.  This is checked lazily via
    ``verify_naturality``.
    """
    source: ConcretePresheaf
    target: ConcretePresheaf
    components: Dict[SiteId, SectionTransformComponent] = field(default_factory=dict)

    def apply_at(self, site: SiteId, section: LocalSection) -> Optional[LocalSection]:
        """Apply η_U to a section of the source presheaf."""
        comp = self.components.get(site)
        if comp is None:
            return None
        return comp.transform(section)

    def evidence_at(self, site: SiteId) -> Optional[Predicate]:
        """Return the evidence predicate for the component at *site*."""
        comp = self.components.get(site)
        return comp.evidence if comp is not None else None


@dataclass(frozen=True)
class SectionTransformComponent:
    """One component η_U of a presheaf morphism.

    *transform* maps a LocalSection of the source at U to a
    LocalSection of the target at U.

    *evidence* is a ``Predicate`` that is valid precisely when the
    component preserves the refinement structure.

    *inverse* (optional) provides the inverse component when the
    morphism is an iso.
    """
    site_id: SiteId
    transform: Callable[[LocalSection], LocalSection]
    evidence: Predicate = field(default_factory=TruePred)
    inverse: Optional[Callable[[LocalSection], LocalSection]] = None

    @property
    def is_isomorphism(self) -> bool:
        return self.inverse is not None
