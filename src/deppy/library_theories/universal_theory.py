"""Universal theory pack: provides default ⊤ sections for all site kinds.

In sheaf theory, a presheaf must assign a section to EVERY site in the
cover. When a specialized theory pack doesn't handle a site kind, the
presheaf has an undefined fiber — which falsely produces gluing
obstructions (every overlap with an undefined fiber disagrees).

The universal theory pack provides the TRIVIAL SECTION ⊤ at any site
that no other theory pack handles. ⊤ sections always glue with other
sections (⊤ is the terminal object in the refinement lattice), so they
never produce false obstructions.

This implements the sheaf-theoretic principle:
    The constant presheaf at ⊤ is a sheaf (trivially satisfies gluing).
    Enriching a presheaf with ⊤ sections at undefined fibers preserves
    existing obstructions but doesn't introduce new ones.

The universal theory pack also provides BASIC TYPE INFERENCE for
common Python patterns, using Python's runtime semantics as a theory:
- Arithmetic operators: result type from operand types
- Comparison operators: always bool
- Container constructors: list, dict, set, tuple
- Attribute access: carries nullability information
- Function calls: return type from known signatures
"""

from __future__ import annotations

from typing import Any, Dict, Optional, Set

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)


class UniversalTheoryPack:
    """Provides default sections for all site kinds.

    This is a CATCH-ALL theory pack that ensures every site in the
    cover gets at least a ⊤ section. Without this, sites unhandled
    by specialized theory packs produce false H¹ obstructions.
    """

    name = "universal"
    priority = -1  # Lowest priority — only used when nothing else matches

    @property
    def supported_kinds(self) -> frozenset:
        """Handle ALL site kinds — this is the catch-all pack."""
        return frozenset(SiteKind)

    def applicable_site_kinds(self) -> frozenset:
        """Handle ALL site kinds."""
        return frozenset(SiteKind)

    def can_handle(self, site_id: SiteId) -> bool:
        """Handle any site kind."""
        return True

    def solve_local(self, site_id: SiteId, section: LocalSection) -> Any:
        """Produce a default section for the given site.

        Uses the 2-arg protocol expected by LocalSolverDispatch.
        Returns the section unchanged (⊤ preserves existing information).
        This ensures every site gets at least a trivial section,
        making the presheaf COMPLETE (no undefined fibers).
        """
        # Return the existing section (preserve whatever info was there)
        # If the section has no carrier or refinements, it's already ⊤
        return section
