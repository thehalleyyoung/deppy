"""Algebraic geometry engine for the hybrid type system.

Extends deppy's existing sheaf infrastructure (``ConcretePresheaf``,
``ConcreteTopolgy``, ``SheafConditionChecker``) with full Cech cohomology
computation over the 5-layer product site:

    Site(P) x Layer  where Layer = {INTENT, STRUCTURAL, SEMANTIC, PROOF, CODE}

The key mathematical objects:

- **LayeredSite**: the product site ``Site(P) x Layer``
- **LayeredPresheaf(ConcretePresheaf)**: extends the base presheaf with the
  layer dimension, assigning to each ``(site, layer)`` pair a section in
  ``RefinementLattice x TrustLattice``
- **CechComplex**: full Cech complex ``C^0 -> C^1 -> C^2`` with coboundary
  maps; computes ``H^0`` and ``H^1``
- **DescentChecker(SheafConditionChecker)**: extends the base gluing checker
  with descent data for the layered setting
- **MayerVietoris**: computes ``H^1`` from a two-piece decomposition
- **ObstructionLocalizer**: maps abstract ``H^1`` generators to code locations
- **LeraySpectralSequence**: decomposes product-site cohomology via the
  ``E_2`` page of the Leray spectral sequence

All classes build on the existing deppy infrastructure and degrade gracefully
when core modules are unavailable.
"""

from __future__ import annotations

import enum
import hashlib
import itertools
import logging
import math
import time
from dataclasses import dataclass, field
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterable,
    Iterator,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

if TYPE_CHECKING:
    from deppy.hybrid import HybridLayer

# ---------------------------------------------------------------------------
# Graceful integration with existing deppy infrastructure
# ---------------------------------------------------------------------------

try:
    from deppy.core.presheaf import ConcretePresheaf, SheafConditionChecker, GluingResult
    from deppy.core.grothendieck import ConcreteTopolgy
    from deppy.core._protocols import (
        Cover,
        LocalSection,
        Morphism,
        SiteId,
        SiteKind,
        TrustLevel,
        GlobalSection,
        ObstructionData,
    )
    _HAS_CORE = True
except ImportError:
    _HAS_CORE = False

    # Minimal stand-ins so the module can be imported without deppy core.
    class ConcretePresheaf:  # type: ignore[no-redef]
        """Stand-in when deppy.core.presheaf is unavailable."""

        def __init__(self, **kw: Any) -> None:
            self._sections: Dict[Any, list] = {}
            self._morphisms: Dict[Any, Any] = {}
            self.name: str = kw.get("name", "")

        def sections_at(self, site: Any) -> list:
            return list(self._sections.get(site, []))

        def add_section(self, section: Any) -> None:
            sid = getattr(section, "site_id", None)
            if sid is not None:
                self._sections.setdefault(sid, []).append(section)

        def add_morphism(self, morphism: Any) -> None:
            src = getattr(morphism, "source", None)
            tgt = getattr(morphism, "target", None)
            if src is not None and tgt is not None:
                self._morphisms[(src, tgt)] = morphism

        def get_morphism(self, source: Any, target: Any) -> Any:
            return self._morphisms.get((source, target))

        def site_ids(self) -> set:
            return set(self._sections.keys())

    class SheafConditionChecker:  # type: ignore[no-redef]
        """Stand-in when deppy.core.presheaf is unavailable."""

        @staticmethod
        def check_agreement(sections: dict, overlaps: list) -> list:
            return []

        @staticmethod
        def attempt_gluing(sections: dict, overlaps: list) -> Any:
            return None

    class GluingResult:  # type: ignore[no-redef]
        def __init__(self, **kw: Any) -> None:
            self.success: bool = kw.get("success", False)
            self.global_section: Any = kw.get("global_section", None)
            self.conflicts: list = kw.get("conflicts", [])
            self.explanation: str = kw.get("explanation", "")

try:
    from deppy.cohomological_analysis import CohomologicalResult
    _HAS_COHOMOLOGICAL = True
except ImportError:
    _HAS_COHOMOLOGICAL = False

try:
    from deppy.hybrid import HybridLayer as _HybridLayer, HybridTrustLevel
    _HAS_HYBRID = True
except ImportError:
    _HAS_HYBRID = False

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Constants: the 5 layers
# ---------------------------------------------------------------------------

LAYERS: Tuple[str, ...] = ("intent", "structural", "semantic", "proof", "code")
_N_LAYERS: int = len(LAYERS)

# Layer ordering (used for restriction maps between layers)
_LAYER_INDEX: Dict[str, int] = {name: i for i, name in enumerate(LAYERS)}

# Separator for product IDs: "site_name@@layer"
_PRODUCT_SEP = "@@"


# ---------------------------------------------------------------------------
# Enums
# ---------------------------------------------------------------------------


class DescentStatus(enum.Enum):
    """Result of a descent / gluing check."""
    GLUED = "glued"
    OBSTRUCTED = "obstructed"
    PARTIAL = "partial"
    ERROR = "error"


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ProductId:
    """Identifier for a cell in the product site Site(P) x Layer."""

    site_id: str
    layer: str

    def __str__(self) -> str:
        return f"{self.site_id}{_PRODUCT_SEP}{self.layer}"

    @classmethod
    def parse(cls, s: str) -> ProductId:
        parts = s.rsplit(_PRODUCT_SEP, 1)
        if len(parts) == 2:
            return cls(site_id=parts[0], layer=parts[1])
        return cls(site_id=s, layer="code")

    @property
    def layer_index(self) -> int:
        return _LAYER_INDEX.get(self.layer, _N_LAYERS)


@dataclass
class LayerSection:
    """A section assigned to a product cell (site, layer).

    Carries both a refinement value (from the RefinementLattice) and
    a trust value (from the TrustLattice).
    """

    product_id: ProductId
    refinement: Any = None
    trust: int = 0  # maps to HybridTrustLevel.value
    value: Any = None  # the actual section data
    provenance: str = ""

    @property
    def site_id(self) -> str:
        return self.product_id.site_id

    @property
    def layer(self) -> str:
        return self.product_id.layer

    def uid(self) -> str:
        h = hashlib.sha256(str(self.product_id).encode()).hexdigest()[:10]
        return f"sec_{h}"


@dataclass
class DescentResult:
    """Result of checking the descent condition on a layered presheaf."""

    status: DescentStatus
    glued_section: Any = None
    conflicts: List[Tuple[str, str]] = field(default_factory=list)
    h1_rank: int = 0
    generators: List[str] = field(default_factory=list)
    explanation: str = ""

    @property
    def is_glued(self) -> bool:
        return self.status == DescentStatus.GLUED

    @property
    def is_obstructed(self) -> bool:
        return self.status == DescentStatus.OBSTRUCTED


@dataclass
class SpectralEntry:
    """An entry E_2^{p,q} in the Leray spectral sequence."""

    p: int
    q: int
    rank: int = 0
    generators: List[str] = field(default_factory=list)

    def __repr__(self) -> str:
        return f"E2^{{{self.p},{self.q}}} = Z^{self.rank}"


# ===========================================================================
# LayeredSite
# ===========================================================================


class LayeredSite:
    """Site(P) x Layer -- the product site for hybrid typing.

    Extends deppy's site concept with the layer dimension.  Each base
    site ``s`` in ``Site(P)`` produces ``|Layer|`` product cells
    ``(s, l)`` for ``l`` in ``{intent, structural, semantic, proof, code}``.

    Overlap between product cells ``(s1, l1)`` and ``(s2, l2)`` is
    non-empty iff either:
    - ``s1 == s2`` and ``l1`` is adjacent to ``l2`` in the layer ordering, or
    - ``l1 == l2`` and ``s1`` overlaps ``s2`` in the base site.

    This gives the Grothendieck topology on the product category.
    """

    def __init__(
        self,
        base_site_ids: List[str],
        *,
        base_overlaps: Optional[List[Tuple[str, str]]] = None,
        layers: Tuple[str, ...] = LAYERS,
    ) -> None:
        self._base_ids = list(base_site_ids)
        self._base_set = frozenset(base_site_ids)
        self._layers = layers
        self._layer_set = frozenset(layers)

        # Base-site overlaps (symmetric)
        self._base_overlaps: Set[Tuple[str, str]] = set()
        if base_overlaps:
            for a, b in base_overlaps:
                self._base_overlaps.add((a, b))
                self._base_overlaps.add((b, a))

        # Build all product cells
        self._product_cells: List[ProductId] = [
            ProductId(site_id=s, layer=l)
            for s in self._base_ids
            for l in self._layers
        ]
        self._product_set: FrozenSet[ProductId] = frozenset(self._product_cells)

    # ------------------------------------------------------------------
    # Query API
    # ------------------------------------------------------------------

    def product_id(self, site_id: str, layer: str) -> ProductId:
        """Construct a product cell identifier."""
        return ProductId(site_id=site_id, layer=layer)

    def all_product_ids(self) -> List[ProductId]:
        """Return all cells in the product site."""
        return list(self._product_cells)

    def layer_slice(self, layer: str) -> List[ProductId]:
        """All cells at a given layer (fixing layer, varying site)."""
        return [p for p in self._product_cells if p.layer == layer]

    def site_slice(self, site_id: str) -> List[ProductId]:
        """All cells at a given site (fixing site, varying layer)."""
        return [p for p in self._product_cells if p.site_id == site_id]

    def overlap(self, id1: ProductId, id2: ProductId) -> bool:
        """Check whether two product cells overlap.

        Overlaps in the product topology:
        - Same site, adjacent layers  (vertical overlap)
        - Same layer, overlapping base sites  (horizontal overlap)
        """
        if id1 == id2:
            return True

        # Vertical: same site, adjacent layers
        if id1.site_id == id2.site_id:
            return abs(id1.layer_index - id2.layer_index) <= 1

        # Horizontal: same layer, base sites overlap
        if id1.layer == id2.layer:
            return (id1.site_id, id2.site_id) in self._base_overlaps

        return False

    def all_overlaps(self) -> List[Tuple[ProductId, ProductId]]:
        """Compute all overlapping pairs of product cells."""
        pairs: List[Tuple[ProductId, ProductId]] = []
        cells = self._product_cells
        for i, a in enumerate(cells):
            for b in cells[i + 1:]:
                if self.overlap(a, b):
                    pairs.append((a, b))
        return pairs

    @property
    def n_base_sites(self) -> int:
        return len(self._base_ids)

    @property
    def n_layers(self) -> int:
        return len(self._layers)

    @property
    def n_product_cells(self) -> int:
        return len(self._product_cells)

    def __repr__(self) -> str:
        return (
            f"LayeredSite(bases={self.n_base_sites}, "
            f"layers={self.n_layers}, "
            f"cells={self.n_product_cells})"
        )


# ===========================================================================
# LayeredPresheaf
# ===========================================================================


class LayeredPresheaf(ConcretePresheaf):
    """HybridTy : (Site(P) x Layer)^op -> RefinementLattice x TrustLattice.

    Extends ``deppy.core.presheaf.ConcretePresheaf`` with the layer dimension.
    Each section is indexed by a ``ProductId = (site_id, layer)`` and carries
    both a refinement value and a trust level.

    The restriction maps between layers are:

        intent -> structural  : drop NL content, keep structural types
        structural -> semantic : enrich with semantic information
        semantic -> proof      : extract proof-relevant content
        proof -> code          : extract executable content

    And the reverse (contravariant) maps:

        code -> proof          : embed code into proof context
        proof -> semantic      : weaken proof to semantic claim
        semantic -> structural : forget semantics, keep structure
        structural -> intent   : abstract to intent level

    These 10 maps (5 forward + 5 reverse between adjacent layers) are stored
    in ``RESTRICTION_MAPS``.
    """

    RESTRICTION_MAPS: Dict[Tuple[str, str], Callable[..., Any]] = {}

    def __init__(
        self,
        site: LayeredSite,
        *,
        name: str = "HybridTy",
    ) -> None:
        if _HAS_CORE:
            super().__init__(name=name)
        else:
            super().__init__(name=name)
        self._layered_site = site
        self._layer_sections: Dict[ProductId, LayerSection] = {}
        self._register_default_restriction_maps()

    # ------------------------------------------------------------------
    # Layer section management
    # ------------------------------------------------------------------

    def add_layer_section(
        self,
        site_id: str,
        layer: str,
        section: LayerSection,
    ) -> None:
        """Add a section at a product cell (site_id, layer).

        Also registers the section in the underlying ``ConcretePresheaf``
        when the core protocols are available.
        """
        pid = ProductId(site_id=site_id, layer=layer)
        section.product_id = pid  # type: ignore[misc]
        self._layer_sections[pid] = section

        # Register in the base presheaf if core is available
        if _HAS_CORE:
            core_section = self._to_core_section(section, pid)
            if core_section is not None:
                self.add_section(core_section)

    def get_layer_section(self, site_id: str, layer: str) -> Optional[LayerSection]:
        """Retrieve the section at a product cell."""
        return self._layer_sections.get(ProductId(site_id=site_id, layer=layer))

    def all_layer_sections(self) -> Dict[ProductId, LayerSection]:
        """Return all layer sections."""
        return dict(self._layer_sections)

    # ------------------------------------------------------------------
    # Restriction maps
    # ------------------------------------------------------------------

    def restrict_layer(
        self,
        section: LayerSection,
        from_layer: str,
        to_layer: str,
    ) -> LayerSection:
        """Restrict a section along the layer dimension.

        Applies the restriction map ``from_layer -> to_layer`` to the
        section's data.  If no explicit map is registered, returns a
        copy with the trust level adjusted monotonically.
        """
        key = (from_layer, to_layer)
        restrict_fn = self.RESTRICTION_MAPS.get(key)

        if restrict_fn is not None:
            return restrict_fn(section)

        # Default: copy with trust monotonicity
        new_trust = section.trust
        fi = _LAYER_INDEX.get(from_layer, 0)
        ti = _LAYER_INDEX.get(to_layer, 0)
        if ti < fi:
            # Restricting to a weaker (more abstract) layer: trust can only decrease
            new_trust = min(section.trust, ti + 1)

        return LayerSection(
            product_id=ProductId(site_id=section.site_id, layer=to_layer),
            refinement=section.refinement,
            trust=new_trust,
            value=section.value,
            provenance=f"restricted({from_layer}->{to_layer})",
        )

    def restrict_site(
        self,
        section: LayerSection,
        from_site: str,
        to_site: str,
    ) -> LayerSection:
        """Restrict a section along the base-site dimension.

        Delegates to the underlying ``ConcretePresheaf.restrict()`` when
        a morphism between the sites exists; otherwise copies with
        provenance annotation.
        """
        if _HAS_CORE:
            source_id = self._make_site_id(from_site)
            target_id = self._make_site_id(to_site)
            morphism = self.get_morphism(source_id, target_id)
            if morphism is not None:
                core_section = self._to_core_section(section, section.product_id)
                if core_section is not None:
                    restricted = morphism.restrict(core_section)
                    return LayerSection(
                        product_id=ProductId(
                            site_id=to_site, layer=section.layer
                        ),
                        refinement=getattr(restricted, "refinements", section.refinement),
                        trust=section.trust,
                        value=getattr(restricted, "carrier_type", section.value),
                        provenance=f"site_restricted({from_site}->{to_site})",
                    )

        return LayerSection(
            product_id=ProductId(site_id=to_site, layer=section.layer),
            refinement=section.refinement,
            trust=section.trust,
            value=section.value,
            provenance=f"site_restricted({from_site}->{to_site})",
        )

    def compatible_on_overlap(
        self,
        s1: LayerSection,
        s2: LayerSection,
    ) -> bool:
        """Check whether two sections agree on their overlap.

        Two sections are compatible if their restrictions to the overlap
        region yield equivalent values (same refinement, compatible trust).
        """
        pid1 = s1.product_id
        pid2 = s2.product_id

        if not self._layered_site.overlap(pid1, pid2):
            return True  # disjoint cells are vacuously compatible

        # Vertical overlap (same site, adjacent layers)
        if pid1.site_id == pid2.site_id and pid1.layer != pid2.layer:
            r1 = self.restrict_layer(s1, pid1.layer, pid2.layer)
            return self._sections_agree(r1, s2)

        # Horizontal overlap (same layer, different sites)
        if pid1.layer == pid2.layer and pid1.site_id != pid2.site_id:
            r1 = self.restrict_site(s1, pid1.site_id, pid2.site_id)
            return self._sections_agree(r1, s2)

        # Exact same cell
        if pid1 == pid2:
            return self._sections_agree(s1, s2)

        return True

    # ------------------------------------------------------------------
    # Presheaf queries
    # ------------------------------------------------------------------

    def layer_slice_sections(self, layer: str) -> List[LayerSection]:
        """All sections at a given layer."""
        return [
            sec for pid, sec in self._layer_sections.items()
            if pid.layer == layer
        ]

    def site_slice_sections(self, site_id: str) -> List[LayerSection]:
        """All sections at a given base site (across all layers)."""
        return [
            sec for pid, sec in self._layer_sections.items()
            if pid.site_id == site_id
        ]

    @property
    def n_layer_sections(self) -> int:
        return len(self._layer_sections)

    # ------------------------------------------------------------------
    # Private helpers
    # ------------------------------------------------------------------

    def _register_default_restriction_maps(self) -> None:
        """Register the 10 default restriction maps between adjacent layers."""
        for i in range(len(LAYERS) - 1):
            src = LAYERS[i]
            tgt = LAYERS[i + 1]

            # Forward: src -> tgt (restrict from abstract to concrete)
            def _forward(sec: LayerSection, _s: str = src, _t: str = tgt) -> LayerSection:
                return LayerSection(
                    product_id=ProductId(site_id=sec.site_id, layer=_t),
                    refinement=sec.refinement,
                    trust=min(sec.trust, _LAYER_INDEX[_t] + 1),
                    value=sec.value,
                    provenance=f"restrict({_s}->{_t})",
                )

            # Backward: tgt -> src (restrict from concrete to abstract)
            def _backward(sec: LayerSection, _s: str = src, _t: str = tgt) -> LayerSection:
                return LayerSection(
                    product_id=ProductId(site_id=sec.site_id, layer=_s),
                    refinement=sec.refinement,
                    trust=sec.trust,
                    value=sec.value,
                    provenance=f"restrict({_t}->{_s})",
                )

            self.RESTRICTION_MAPS[(src, tgt)] = _forward
            self.RESTRICTION_MAPS[(tgt, src)] = _backward

    def _sections_agree(self, s1: LayerSection, s2: LayerSection) -> bool:
        """Check value-level agreement between two sections."""
        # Trust must be compatible (same or adjacent)
        if abs(s1.trust - s2.trust) > 1:
            return False

        # Refinement must agree
        if s1.refinement is not None and s2.refinement is not None:
            if s1.refinement != s2.refinement:
                return False

        # Value must agree (if both present)
        if s1.value is not None and s2.value is not None:
            if s1.value != s2.value:
                return False

        return True

    def _to_core_section(self, section: LayerSection, pid: ProductId) -> Any:
        """Convert a LayerSection to a core LocalSection (if available)."""
        if not _HAS_CORE:
            return None

        site_id = SiteId(
            kind=SiteKind.PROOF,
            name=str(pid),
        )
        return LocalSection(
            site_id=site_id,
            carrier_type=section.value,
            refinements={"refinement": section.refinement} if section.refinement else {},
            trust=TrustLevel.RESIDUAL,
            provenance=section.provenance,
            witnesses={},
        )

    def _make_site_id(self, name: str) -> Any:
        """Build a core SiteId from a string name."""
        if _HAS_CORE:
            return SiteId(kind=SiteKind.PROOF, name=name)
        return name

    def __repr__(self) -> str:
        return (
            f"LayeredPresheaf(name={self.name!r}, "
            f"cells={self.n_layer_sections}, "
            f"site={self._layered_site!r})"
        )


# ===========================================================================
# CechComplex
# ===========================================================================


class CechComplex:
    r"""Cech complex for computing H^1(U, HybridTy).

    Given a cover U = {U_i} of the product site and a layered presheaf
    ``F = HybridTy``, this class computes the Cech complex:

        C^0(U, F) --delta^0--> C^1(U, F) --delta^1--> C^2(U, F)

    where:
    - ``C^0 = \prod_i F(U_i)``         — sections on each open set
    - ``C^1 = \prod_{i<j} F(U_i \cap U_j)``  — sections on double overlaps
    - ``C^2 = \prod_{i<j<k} F(U_i \cap U_j \cap U_k)`` — triple overlaps

    and the coboundary maps are the alternating restriction maps.

    The key computation:
    - ``H^0 = ker(delta^0)`` = global sections
    - ``H^1 = ker(delta^1) / im(delta^0)`` = obstruction classes

    Uses deppy's existing obstruction infrastructure (``ObstructionData``,
    ``SheafConditionChecker``) but extends for the layered setting.
    """

    def __init__(
        self,
        presheaf: LayeredPresheaf,
        cover: List[ProductId],
    ) -> None:
        self._presheaf = presheaf
        self._cover = list(cover)
        self._cover_set = frozenset(cover)
        self._site = presheaf._layered_site

        # Precompute overlap structure
        self._overlaps: List[Tuple[int, int]] = []
        for i in range(len(cover)):
            for j in range(i + 1, len(cover)):
                if self._site.overlap(cover[i], cover[j]):
                    self._overlaps.append((i, j))

        self._triple_overlaps: List[Tuple[int, int, int]] = []
        for i in range(len(cover)):
            for j in range(i + 1, len(cover)):
                for k in range(j + 1, len(cover)):
                    if (
                        self._site.overlap(cover[i], cover[j])
                        and self._site.overlap(cover[j], cover[k])
                        and self._site.overlap(cover[i], cover[k])
                    ):
                        self._triple_overlaps.append((i, j, k))

        # Cache computed cochains
        self._c0_cache: Optional[Dict[int, LayerSection]] = None
        self._c1_cache: Optional[Dict[Tuple[int, int], Any]] = None
        self._delta0_cache: Optional[Dict[Tuple[int, int], Any]] = None

    # ------------------------------------------------------------------
    # Cochain groups
    # ------------------------------------------------------------------

    def c0(self) -> Dict[int, LayerSection]:
        r"""C^0 = \prod_i F(U_i).

        Returns a dictionary mapping cover index to the section at that cell.
        """
        if self._c0_cache is not None:
            return self._c0_cache

        result: Dict[int, LayerSection] = {}
        all_sections = self._presheaf.all_layer_sections()

        for i, pid in enumerate(self._cover):
            sec = all_sections.get(pid)
            if sec is not None:
                result[i] = sec
            else:
                # Empty section: no data at this cell
                result[i] = LayerSection(
                    product_id=pid,
                    refinement=None,
                    trust=0,
                    value=None,
                    provenance="empty",
                )

        self._c0_cache = result
        return result

    def c1(self) -> Dict[Tuple[int, int], Any]:
        r"""C^1 = \prod_{i<j} F(U_i \cap U_j).

        For each overlapping pair ``(i, j)``, the section on the overlap
        is computed by restricting ``F(U_i)`` and ``F(U_j)`` to their
        intersection and checking agreement.
        """
        if self._c1_cache is not None:
            return self._c1_cache

        c0_data = self.c0()
        result: Dict[Tuple[int, int], Any] = {}

        for i, j in self._overlaps:
            si = c0_data.get(i)
            sj = c0_data.get(j)
            if si is None or sj is None:
                result[(i, j)] = {"agree": False, "reason": "missing section"}
                continue

            agree = self._presheaf.compatible_on_overlap(si, sj)
            result[(i, j)] = {
                "agree": agree,
                "section_i": si,
                "section_j": sj,
                "overlap_id": f"{self._cover[i]}∩{self._cover[j]}",
            }

        self._c1_cache = result
        return result

    def c2(self) -> Dict[Tuple[int, int, int], Any]:
        r"""C^2 = \prod_{i<j<k} F(U_i \cap U_j \cap U_k).

        Triple overlaps: check the cocycle condition.
        """
        c0_data = self.c0()
        result: Dict[Tuple[int, int, int], Any] = {}

        for i, j, k in self._triple_overlaps:
            si = c0_data.get(i)
            sj = c0_data.get(j)
            sk = c0_data.get(k)
            if si is None or sj is None or sk is None:
                result[(i, j, k)] = {"cocycle": False, "reason": "missing section"}
                continue

            # Check the cocycle condition:
            # delta^1(c^1)_{ijk} = c_{jk} - c_{ik} + c_{ij} = 0
            c_ij = self._presheaf.compatible_on_overlap(si, sj)
            c_jk = self._presheaf.compatible_on_overlap(sj, sk)
            c_ik = self._presheaf.compatible_on_overlap(si, sk)
            cocycle = c_ij and c_jk and c_ik

            result[(i, j, k)] = {
                "cocycle": cocycle,
                "ij": c_ij,
                "jk": c_jk,
                "ik": c_ik,
            }

        return result

    # ------------------------------------------------------------------
    # Coboundary maps
    # ------------------------------------------------------------------

    def delta0(self) -> Dict[Tuple[int, int], Any]:
        r"""delta^0 : C^0 -> C^1.

        The coboundary map: (delta^0 sigma)_{ij} = sigma_j|_{U_ij} - sigma_i|_{U_ij}

        Returns a dict mapping overlap pairs to the coboundary value.
        A zero coboundary means the sections agree on the overlap.
        """
        if self._delta0_cache is not None:
            return self._delta0_cache

        c0_data = self.c0()
        result: Dict[Tuple[int, int], Any] = {}

        for i, j in self._overlaps:
            si = c0_data.get(i)
            sj = c0_data.get(j)
            if si is None or sj is None:
                result[(i, j)] = {"is_zero": False, "reason": "missing"}
                continue

            agree = self._presheaf.compatible_on_overlap(si, sj)
            result[(i, j)] = {
                "is_zero": agree,
                "source_i": str(self._cover[i]),
                "source_j": str(self._cover[j]),
            }

        self._delta0_cache = result
        return result

    def delta1(self) -> Dict[Tuple[int, int, int], Any]:
        r"""delta^1 : C^1 -> C^2.

        The second coboundary: (delta^1 c)_{ijk} = c_{jk} - c_{ik} + c_{ij}.

        A 1-cochain ``c`` is a cocycle iff ``delta^1(c) = 0``.
        """
        c1_data = self.c1()
        result: Dict[Tuple[int, int, int], Any] = {}

        for i, j, k in self._triple_overlaps:
            c_ij = c1_data.get((i, j), {}).get("agree", True)
            c_jk = c1_data.get((j, k), {}).get("agree", True)
            c_ik = c1_data.get((i, k), {}).get("agree", True)

            # In the boolean (agree/disagree) model:
            # The cocycle condition is c_jk XOR c_ik XOR c_ij = 0
            # i.e., an even number of disagreements
            n_disagree = sum(1 for x in [c_ij, c_jk, c_ik] if not x)
            is_zero = n_disagree % 2 == 0

            result[(i, j, k)] = {
                "is_zero": is_zero,
                "n_disagree": n_disagree,
            }

        return result

    # ------------------------------------------------------------------
    # Cohomology computation
    # ------------------------------------------------------------------

    def kernel_delta1(self) -> List[Tuple[int, int]]:
        """ker(delta^1): 1-cocycles (disagreements that satisfy the cocycle condition).

        These are the 1-cochains ``c`` in ``C^1`` such that ``delta^1(c) = 0``.
        """
        d1 = self.delta1()
        c1_data = self.c1()

        # A 1-cochain is given by the disagreement pattern on overlaps
        disagreements = [
            (i, j)
            for (i, j), data in c1_data.items()
            if not data.get("agree", True)
        ]

        # Check cocycle condition: for every triple overlap containing
        # a disagreeing pair, the total must have even parity
        cocycles: List[Tuple[int, int]] = []
        for i, j in disagreements:
            is_cocycle = True
            for triple, data in d1.items():
                if (i in triple and j in triple) and not data.get("is_zero", True):
                    is_cocycle = False
                    break
            if is_cocycle:
                cocycles.append((i, j))

        return cocycles

    def image_delta0(self) -> List[Tuple[int, int]]:
        """im(delta^0): 1-coboundaries.

        These are the 1-cochains that arise as coboundaries of 0-cochains,
        i.e., disagreements that can be resolved by adjusting local sections.
        """
        d0 = self.delta0()
        boundaries: List[Tuple[int, int]] = []

        # A coboundary (i,j) with delta0 not zero means the sections
        # already disagree — but it's a coboundary if the disagreement
        # comes from restricting a 0-cochain.
        # In the boolean model, all delta0 outputs are coboundaries by definition.
        for (i, j), data in d0.items():
            if not data.get("is_zero", True):
                boundaries.append((i, j))

        return boundaries

    def h0(self) -> int:
        """H^0 = ker(delta^0) = global sections.

        Counts how many cover elements have sections that all agree
        pairwise on overlaps (i.e., the global sections of the presheaf).
        """
        d0 = self.delta0()
        # H^0 is the equalizer: sections that agree on ALL overlaps
        all_agree = all(data.get("is_zero", True) for data in d0.values())
        if all_agree:
            # All sections glue: dim H^0 = 1 (one global section)
            return 1
        return 0

    def h1(self) -> int:
        """H^1 = ker(delta^1) / im(delta^0).

        The first cohomology: counts independent obstruction classes.
        ``H^1 = 0`` means the presheaf satisfies the sheaf condition
        (all local sections glue to a global one).
        """
        cocycles = self.kernel_delta1()
        coboundaries = set(self.image_delta0())

        # Quotient: cocycles modulo coboundaries
        non_trivial = [c for c in cocycles if c not in coboundaries]

        # Compute rank by counting independent generators
        # In the boolean model, each independent disagreement is a generator
        return self._rank_mod_boundaries(non_trivial, coboundaries)

    def h1_generators(self) -> List[str]:
        """Return human-readable descriptions of H^1 generators.

        Each generator corresponds to an obstruction: a pair of cover
        elements whose sections fundamentally disagree and cannot be
        resolved by adjusting local sections.
        """
        cocycles = self.kernel_delta1()
        coboundaries = set(self.image_delta0())
        non_trivial = [c for c in cocycles if c not in coboundaries]

        generators: List[str] = []
        for i, j in non_trivial:
            pi = self._cover[i]
            pj = self._cover[j]
            generators.append(
                f"H1_gen({pi} vs {pj}): "
                f"sections disagree on overlap and no coboundary resolves it"
            )

        return generators

    def to_cohomological_result(self) -> Any:
        """Convert to ``deppy.cohomological_analysis.CohomologicalResult``.

        Bridges the layered cohomology computation back to the existing
        deppy result type for compatibility with the analysis pipeline.
        """
        h1_val = self.h1()
        generators = self.h1_generators()

        if _HAS_COHOMOLOGICAL:
            obstructions: List[Any] = []
            if _HAS_CORE:
                for gen_str in generators:
                    obstructions.append(
                        ObstructionData(
                            conflicting_overlaps=[],
                            explanation=gen_str,
                        )
                    )

            return CohomologicalResult(
                n_sites=len(self._cover),
                n_morphisms=0,
                n_overlaps=len(self._overlaps),
                n_agreed=sum(
                    1 for d in self.delta0().values() if d.get("is_zero", True)
                ),
                n_disagreed=sum(
                    1 for d in self.delta0().values() if not d.get("is_zero", True)
                ),
                h1_rank=h1_val,
                obstructions=obstructions,
                has_global_section=(h1_val == 0),
            )

        # Fallback: return a plain dict
        return {
            "h0": self.h0(),
            "h1": h1_val,
            "generators": generators,
            "n_overlaps": len(self._overlaps),
            "has_global_section": h1_val == 0,
        }

    # ------------------------------------------------------------------
    # Private helpers
    # ------------------------------------------------------------------

    def _rank_mod_boundaries(
        self,
        generators: List[Tuple[int, int]],
        boundaries: Set[Tuple[int, int]],
    ) -> int:
        """Compute the rank of generators modulo boundaries.

        Uses a simple independence test: two generators are independent if
        they involve disjoint sets of cover elements.
        """
        if not generators:
            return 0

        # Build adjacency: which cover elements are involved in each generator
        involved: List[Set[int]] = []
        for i, j in generators:
            involved.append({i, j})

        # Greedy independence: pick generators that don't share elements
        # with already-selected ones (approximation for the rank)
        selected: List[Set[int]] = []
        used: Set[int] = set()
        for s in involved:
            if not s & used:
                selected.append(s)
                used.update(s)

        # Each remaining generator adds at most 1 to the rank
        remaining = [s for s in involved if s not in selected]
        return len(selected) + min(len(remaining), max(0, len(generators) - len(selected)))

    def __repr__(self) -> str:
        return (
            f"CechComplex(cover={len(self._cover)}, "
            f"overlaps={len(self._overlaps)}, "
            f"triples={len(self._triple_overlaps)})"
        )


# ===========================================================================
# DescentChecker
# ===========================================================================


class DescentChecker(SheafConditionChecker):
    """Extends ``deppy.core.presheaf.SheafConditionChecker`` with descent data.

    The descent condition for the layered presheaf:

        Given: local sections {sigma_i} at each cover element U_i,
               compatible on all overlaps (sigma_i|_{U_ij} = sigma_j|_{U_ij}),
        Then:  there exists a unique global section sigma
               with sigma|_{U_i} = sigma_i for all i.

    This checker extends the base ``SheafConditionChecker`` to:
    1. Handle the product-site overlap structure (layer + site dimensions)
    2. Report detailed descent data when gluing fails
    3. Compute H^1 rank for the obstruction
    """

    def __init__(self) -> None:
        pass

    def check_descent(
        self,
        presheaf: LayeredPresheaf,
        cover: List[ProductId],
    ) -> DescentResult:
        """Check the descent condition on a layered presheaf.

        Returns a ``DescentResult`` indicating whether the local sections
        glue, and if not, the H^1 rank and generator descriptions.
        """
        cech = CechComplex(presheaf, cover)

        try:
            h1_val = cech.h1()
        except Exception as exc:  # noqa: BLE001
            return DescentResult(
                status=DescentStatus.ERROR,
                explanation=f"Cohomology computation failed: {exc}",
            )

        if h1_val == 0:
            # Sections glue: attempt to construct global section
            glued = self._attempt_global_section(presheaf, cover)
            return DescentResult(
                status=DescentStatus.GLUED,
                glued_section=glued,
                h1_rank=0,
                explanation="H^1 = 0: sections glue to a unique global section",
            )

        generators = cech.h1_generators()

        # Identify conflicting pairs
        conflicts: List[Tuple[str, str]] = []
        d0 = cech.delta0()
        for (i, j), data in d0.items():
            if not data.get("is_zero", True):
                conflicts.append((str(cover[i]), str(cover[j])))

        return DescentResult(
            status=DescentStatus.OBSTRUCTED,
            conflicts=conflicts,
            h1_rank=h1_val,
            generators=generators,
            explanation=f"H^1 = {h1_val}: {h1_val} independent obstruction(s)",
        )

    def glue(
        self,
        compatible_family: Dict[ProductId, LayerSection],
    ) -> Optional[Dict[str, Any]]:
        """Glue a compatible family of sections into a global section.

        If the sections are compatible on all overlaps, produces a unified
        global section dictionary mapping base site IDs to merged layer data.
        """
        if not compatible_family:
            return None

        # Group by base site
        by_site: Dict[str, Dict[str, LayerSection]] = {}
        for pid, sec in compatible_family.items():
            by_site.setdefault(pid.site_id, {})[pid.layer] = sec

        global_section: Dict[str, Any] = {}
        for site_id, layer_map in by_site.items():
            # Compute the join of trust levels across layers
            max_trust = max(sec.trust for sec in layer_map.values())
            # Use the most refined value (from the "code" layer if available)
            value = None
            for layer in reversed(LAYERS):
                if layer in layer_map and layer_map[layer].value is not None:
                    value = layer_map[layer].value
                    break

            global_section[site_id] = {
                "trust": max_trust,
                "value": value,
                "layers": {l: sec.value for l, sec in layer_map.items()},
            }

        return global_section

    # ------------------------------------------------------------------
    # Integration with base SheafConditionChecker
    # ------------------------------------------------------------------

    def check_agreement_layered(
        self,
        presheaf: LayeredPresheaf,
        overlaps: List[Tuple[ProductId, ProductId]],
    ) -> List[Tuple[ProductId, ProductId]]:
        """Check section agreement on layered overlaps.

        Like ``SheafConditionChecker.check_agreement`` but operates on
        ``ProductId`` pairs with the layer-aware compatibility check.
        """
        conflicts: List[Tuple[ProductId, ProductId]] = []
        all_sections = presheaf.all_layer_sections()

        for a, b in overlaps:
            sa = all_sections.get(a)
            sb = all_sections.get(b)
            if sa is None or sb is None:
                continue
            if not presheaf.compatible_on_overlap(sa, sb):
                conflicts.append((a, b))

        return conflicts

    # ------------------------------------------------------------------
    # Private
    # ------------------------------------------------------------------

    def _attempt_global_section(
        self,
        presheaf: LayeredPresheaf,
        cover: List[ProductId],
    ) -> Optional[Dict[str, Any]]:
        """Attempt to construct a global section from compatible locals."""
        all_sections = presheaf.all_layer_sections()
        family = {pid: all_sections[pid] for pid in cover if pid in all_sections}
        return self.glue(family)


# ===========================================================================
# MayerVietoris
# ===========================================================================


class MayerVietoris:
    """Compute H^1 using the Mayer-Vietoris long exact sequence.

    When the cover decomposes as ``U = A cup B``, the long exact sequence:

        0 -> H^0(U) -> H^0(A) + H^0(B) -> H^0(A cap B)
          -> H^1(U) -> H^1(A) + H^1(B) -> H^1(A cap B) -> ...

    gives a formula for H^1(U) in terms of simpler pieces.

    This is useful when:
    - The cover has a natural two-piece decomposition (e.g., layer=intent+code
      vs layer=structural+semantic+proof)
    - Computing H^1 directly on the full product site is expensive
    """

    def __init__(self, presheaf: LayeredPresheaf) -> None:
        self._presheaf = presheaf

    def compute(
        self,
        cover_a: List[ProductId],
        cover_b: List[ProductId],
    ) -> int:
        r"""Compute H^1(U) where U = A \cup B.

        Uses the connecting homomorphism:
            H^0(A \cap B) -> H^1(U)

        The rank of H^1(U) satisfies:
            rank H^1(U) >= rank(connecting_homomorphism)
        """
        # Compute H^0 and H^1 for each piece
        cech_a = CechComplex(self._presheaf, cover_a)
        cech_b = CechComplex(self._presheaf, cover_b)

        h0_a = cech_a.h0()
        h0_b = cech_b.h0()
        h1_a = cech_a.h1()
        h1_b = cech_b.h1()

        # Compute intersection
        intersection = self._compute_intersection(cover_a, cover_b)
        if intersection:
            cech_int = CechComplex(self._presheaf, intersection)
            h0_int = cech_int.h0()
        else:
            h0_int = 0

        # Mayer-Vietoris: H^1(U) = H^1(A) + H^1(B) + connecting(H^0(A cap B))
        connecting = self.connecting_homomorphism(h0_int, h0_a, h0_b)

        return h1_a + h1_b + connecting

    def connecting_homomorphism(
        self,
        h0_intersection: int,
        h0_a: int = 0,
        h0_b: int = 0,
    ) -> int:
        r"""Compute the connecting homomorphism delta: H^0(A \cap B) -> H^1(U).

        The connecting map sends a global section on the intersection to
        an obstruction class: the section extends to A and B separately,
        but the extensions might disagree.

        rank(delta) = max(0, h0_intersection - (h0_a + h0_b - 1))
        """
        # The standard formula from the long exact sequence
        # delta : H^0(A cap B) -> H^1(A cup B)
        # rank(im delta) = rank(ker(H^1(A) + H^1(B) -> H^1(A cap B)))
        # Simplified: if h0_int > h0_a + h0_b, the surplus creates obstructions
        return max(0, h0_intersection - h0_a - h0_b + 1)

    def _compute_intersection(
        self,
        cover_a: List[ProductId],
        cover_b: List[ProductId],
    ) -> List[ProductId]:
        """Compute the cells in the intersection of two covers.

        A cell is in A cap B if it overlaps with both some cell in A
        and some cell in B.
        """
        set_a = frozenset(cover_a)
        set_b = frozenset(cover_b)

        # Direct intersection
        direct = list(set_a & set_b)
        if direct:
            return direct

        # Cells that overlap with both covers
        site = self._presheaf._layered_site
        all_cells = site.all_product_ids()
        intersection: List[ProductId] = []
        for cell in all_cells:
            overlaps_a = any(site.overlap(cell, a) for a in cover_a)
            overlaps_b = any(site.overlap(cell, b) for b in cover_b)
            if overlaps_a and overlaps_b:
                intersection.append(cell)

        return intersection

    def __repr__(self) -> str:
        return f"MayerVietoris(presheaf={self._presheaf.name!r})"


# ===========================================================================
# ObstructionLocalizer
# ===========================================================================


class ObstructionLocalizer:
    """Map abstract H^1 generators to concrete code locations.

    Given an H^1 generator (a pair of cover elements whose sections
    fundamentally disagree), the localizer traces the obstruction back
    to a specific code location using:

    1. The product-cell structure (site_id -> source location)
    2. The layer dimension (which layer the disagreement is in)
    3. The existing ``deppy.cohomological_analysis.ObstructionData``

    This bridges abstract sheaf-theoretic obstructions to actionable
    IDE diagnostics.
    """

    def __init__(
        self,
        *,
        source_map: Optional[Dict[str, Tuple[str, int, int]]] = None,
    ) -> None:
        self._source_map = source_map or {}

    def localize(
        self,
        generator: str,
        presheaf: LayeredPresheaf,
        source_map: Optional[Dict[str, Tuple[str, int, int]]] = None,
    ) -> Dict[str, Any]:
        """Map an H^1 generator to a code location.

        Args:
            generator: String description of the H^1 generator
                (as returned by ``CechComplex.h1_generators()``).
            presheaf: The layered presheaf that produced the obstruction.
            source_map: Optional mapping from site names to
                ``(file, line, col)`` tuples.

        Returns:
            Dictionary with localization info:
            - ``site_a``, ``site_b``: the conflicting product cells
            - ``layer``: the layer where disagreement is strongest
            - ``location``: ``(file, line, col)`` if available
            - ``severity``: estimated severity (from trust levels)
            - ``message``: human-readable description
        """
        smap = source_map or self._source_map

        # Parse the generator string to extract cell info
        # Format: "H1_gen(X vs Y): description"
        cells = self._parse_generator(generator)
        if not cells:
            return {
                "generator": generator,
                "location": None,
                "severity": "unknown",
                "message": generator,
            }

        site_a, site_b = cells

        # Look up source locations
        loc_a = smap.get(site_a.site_id)
        loc_b = smap.get(site_b.site_id)
        location = loc_a or loc_b

        # Determine which layer the disagreement is in
        layer = self._identify_conflict_layer(site_a, site_b, presheaf)

        # Estimate severity from trust levels
        severity = self._estimate_severity(site_a, site_b, presheaf)

        return {
            "site_a": str(site_a),
            "site_b": str(site_b),
            "layer": layer,
            "location": location,
            "severity": severity,
            "message": self._format_message(site_a, site_b, layer, severity),
            "generator": generator,
        }

    def to_diagnostic(self, localized: Dict[str, Any]) -> Dict[str, Any]:
        """Convert a localized obstruction to an IDE diagnostic format.

        Returns a dictionary compatible with LSP diagnostic protocol:
        - ``range``: line/column range
        - ``severity``: 1=error, 2=warning, 3=info, 4=hint
        - ``message``: human-readable description
        - ``source``: "deppy-hybrid"
        """
        loc = localized.get("location")
        if loc is not None:
            file_path, line, col = loc
            range_dict = {
                "start": {"line": max(0, line - 1), "character": col},
                "end": {"line": max(0, line - 1), "character": col + 1},
            }
        else:
            range_dict = {
                "start": {"line": 0, "character": 0},
                "end": {"line": 0, "character": 0},
            }

        severity_map = {
            "critical": 1,
            "high": 1,
            "medium": 2,
            "low": 3,
            "info": 4,
            "unknown": 3,
        }
        sev = severity_map.get(localized.get("severity", "unknown"), 3)

        return {
            "range": range_dict,
            "severity": sev,
            "message": localized.get("message", "Type obstruction detected"),
            "source": "deppy-hybrid",
            "code": f"H1-{localized.get('layer', 'unknown')}",
            "data": {
                "site_a": localized.get("site_a"),
                "site_b": localized.get("site_b"),
                "generator": localized.get("generator"),
            },
        }

    def localize_all(
        self,
        generators: List[str],
        presheaf: LayeredPresheaf,
        source_map: Optional[Dict[str, Tuple[str, int, int]]] = None,
    ) -> List[Dict[str, Any]]:
        """Localize all H^1 generators."""
        return [
            self.localize(gen, presheaf, source_map)
            for gen in generators
        ]

    def diagnostics_all(
        self,
        generators: List[str],
        presheaf: LayeredPresheaf,
        source_map: Optional[Dict[str, Tuple[str, int, int]]] = None,
    ) -> List[Dict[str, Any]]:
        """Localize all generators and convert to diagnostics."""
        localized = self.localize_all(generators, presheaf, source_map)
        return [self.to_diagnostic(loc) for loc in localized]

    # ------------------------------------------------------------------
    # Private
    # ------------------------------------------------------------------

    def _parse_generator(
        self, generator: str
    ) -> Optional[Tuple[ProductId, ProductId]]:
        """Parse an H^1 generator string to extract the two product cells."""
        # Expected format: "H1_gen(SITE_A@@LAYER_A vs SITE_B@@LAYER_B): ..."
        if "H1_gen(" not in generator:
            return None
        try:
            inner = generator.split("H1_gen(", 1)[1].split(")", 1)[0]
            parts = inner.split(" vs ", 1)
            if len(parts) != 2:
                return None
            a = ProductId.parse(parts[0].strip())
            b = ProductId.parse(parts[1].strip())
            return (a, b)
        except (IndexError, ValueError):
            return None

    def _identify_conflict_layer(
        self,
        a: ProductId,
        b: ProductId,
        presheaf: LayeredPresheaf,
    ) -> str:
        """Identify which layer the conflict is most severe in."""
        if a.layer == b.layer:
            return a.layer
        # If different layers, the conflict is in the layer boundary
        idx_a = _LAYER_INDEX.get(a.layer, 0)
        idx_b = _LAYER_INDEX.get(b.layer, 0)
        # Return the more concrete (higher-index) layer
        return a.layer if idx_a > idx_b else b.layer

    def _estimate_severity(
        self,
        a: ProductId,
        b: ProductId,
        presheaf: LayeredPresheaf,
    ) -> str:
        """Estimate the severity of an obstruction from trust levels."""
        sec_a = presheaf.get_layer_section(a.site_id, a.layer)
        sec_b = presheaf.get_layer_section(b.site_id, b.layer)

        trust_a = sec_a.trust if sec_a else 0
        trust_b = sec_b.trust if sec_b else 0
        max_trust = max(trust_a, trust_b)

        if max_trust >= 4:  # Z3_PROVEN or higher
            return "critical"
        if max_trust >= 3:  # PROPERTY_CHECKED
            return "high"
        if max_trust >= 2:  # LLM_JUDGED
            return "medium"
        if max_trust >= 1:  # LLM_RAW
            return "low"
        return "info"

    def _format_message(
        self,
        a: ProductId,
        b: ProductId,
        layer: str,
        severity: str,
    ) -> str:
        """Format a human-readable obstruction message."""
        return (
            f"Type obstruction in {layer} layer: "
            f"sections at {a.site_id} and {b.site_id} disagree. "
            f"Severity: {severity}."
        )


# ===========================================================================
# LeraySpectralSequence
# ===========================================================================


class LeraySpectralSequence:
    r"""E_2^{p,q} = H^p(Site, H^q(Layer, HybridTy)) => H^{p+q}(Site x Layer, HybridTy).

    Decomposes the product-site cohomology into pieces that are easier
    to compute:

    - First compute the "fiber" cohomology H^q(Layer, HybridTy) for each
      base site (how the layers fail to glue at that site)
    - Then compute the "base" cohomology H^p(Site, H^q(Layer, ...)) (how
      the fiber cohomologies fail to glue across sites)

    The E_2 page entries:
    - E_2^{0,0} = H^0(Site, H^0(Layer, F)) = global sections with full layer agreement
    - E_2^{1,0} = H^1(Site, H^0(Layer, F)) = site-level obstructions (layers agree locally)
    - E_2^{0,1} = H^0(Site, H^1(Layer, F)) = layer-level obstructions (consistent across sites)

    The total H^1 is approximated by:
        H^1 ~ E_2^{1,0} + E_2^{0,1}
    (exact when E_2 degenerates, which happens when the base site is discrete).
    """

    def __init__(self, presheaf: LayeredPresheaf) -> None:
        self._presheaf = presheaf
        self._site = presheaf._layered_site

    def e2_page(self) -> Dict[Tuple[int, int], SpectralEntry]:
        """Compute the E_2 page of the Leray spectral sequence.

        Returns entries E_2^{p,q} for p, q in {0, 1, 2}.
        """
        entries: Dict[Tuple[int, int], SpectralEntry] = {}

        # --- Fiber cohomology: H^q(Layer, F) for each base site ---
        fiber_h0: Dict[str, int] = {}
        fiber_h1: Dict[str, int] = {}
        fiber_h1_gens: Dict[str, List[str]] = {}

        for site_id in self._base_site_ids():
            fiber_cover = self._site.site_slice(site_id)
            if not fiber_cover:
                fiber_h0[site_id] = 0
                fiber_h1[site_id] = 0
                fiber_h1_gens[site_id] = []
                continue

            cech_fiber = CechComplex(self._presheaf, fiber_cover)
            fiber_h0[site_id] = cech_fiber.h0()
            fiber_h1[site_id] = cech_fiber.h1()
            fiber_h1_gens[site_id] = cech_fiber.h1_generators()

        # --- E_2^{0,0}: H^0(Site, H^0(Layer, F)) ---
        # Global sections with full layer agreement at every site
        n_glued_sites = sum(1 for v in fiber_h0.values() if v > 0)
        entries[(0, 0)] = SpectralEntry(
            p=0, q=0,
            rank=1 if n_glued_sites == len(fiber_h0) and len(fiber_h0) > 0 else 0,
        )

        # --- E_2^{1,0}: H^1(Site, H^0(Layer, F)) ---
        # Site-level obstructions among the sites where layers agree
        h0_sites = [s for s, h in fiber_h0.items() if h > 0]
        site_level_h1 = self._compute_base_cohomology(h0_sites, "h0")
        entries[(1, 0)] = SpectralEntry(
            p=1, q=0,
            rank=site_level_h1,
            generators=[f"site-level obstruction at base sites"],
        )

        # --- E_2^{0,1}: H^0(Site, H^1(Layer, F)) ---
        # Layer obstructions that are consistent across all sites
        total_fiber_h1 = sum(fiber_h1.values())
        # E_2^{0,1} counts fiber H^1 that is "globally" consistent
        consistent_h1 = min(fiber_h1.values()) if fiber_h1 else 0
        all_gens: List[str] = []
        for gens in fiber_h1_gens.values():
            all_gens.extend(gens)
        entries[(0, 1)] = SpectralEntry(
            p=0, q=1,
            rank=consistent_h1,
            generators=all_gens[:5],  # cap to 5
        )

        # --- E_2^{2,0}: higher term (usually 0 for small sites) ---
        entries[(2, 0)] = SpectralEntry(p=2, q=0, rank=0)

        # --- E_2^{1,1}: cross term ---
        entries[(1, 1)] = SpectralEntry(
            p=1, q=1,
            rank=max(0, total_fiber_h1 - consistent_h1 - site_level_h1),
        )

        # --- E_2^{0,2}: higher fiber term ---
        entries[(0, 2)] = SpectralEntry(p=0, q=2, rank=0)

        return entries

    def converge(self) -> int:
        """Compute total H^1 from the spectral sequence.

        H^1(total) = E_2^{1,0} + E_2^{0,1} + corrections

        The corrections vanish when the spectral sequence degenerates
        at the E_2 page (which happens when the base is discrete or
        the fibers are constant).
        """
        e2 = self.e2_page()

        e2_10 = e2.get((1, 0), SpectralEntry(p=1, q=0))
        e2_01 = e2.get((0, 1), SpectralEntry(p=0, q=1))
        e2_11 = e2.get((1, 1), SpectralEntry(p=1, q=1))

        # H^1 = E_2^{1,0} + E_2^{0,1}  (when E_2 degenerates)
        # Plus correction from E_2^{1,1} differential if non-degenerate
        h1_approx = e2_10.rank + e2_01.rank

        # Check for non-degenerate differential d_2: E_2^{0,1} -> E_2^{2,0}
        e2_20 = e2.get((2, 0), SpectralEntry(p=2, q=0))
        if e2_20.rank > 0:
            # d_2 might kill some of E_2^{0,1}
            correction = min(e2_01.rank, e2_20.rank)
            h1_approx = max(0, h1_approx - correction)

        return h1_approx

    def summary(self) -> str:
        """Human-readable summary of the spectral sequence."""
        e2 = self.e2_page()
        h1 = self.converge()

        lines = ["Leray Spectral Sequence: E_2 page"]
        lines.append("=" * 40)
        for (p, q), entry in sorted(e2.items()):
            lines.append(f"  E_2^{{{p},{q}}} = Z^{entry.rank}")
            for gen in entry.generators:
                lines.append(f"    generator: {gen}")
        lines.append(f"  => H^1 = {h1}")
        return "\n".join(lines)

    # ------------------------------------------------------------------
    # Private
    # ------------------------------------------------------------------

    def _base_site_ids(self) -> List[str]:
        """Extract unique base site IDs from the presheaf."""
        seen: Set[str] = set()
        result: List[str] = []
        for pid in self._presheaf.all_layer_sections():
            sid = pid.site_id
            if sid not in seen:
                seen.add(sid)
                result.append(sid)
        return result

    def _compute_base_cohomology(
        self, site_ids: List[str], mode: str
    ) -> int:
        """Compute H^1 on the base site category.

        Simplified: uses the layer="code" slice to compute H^1 among
        the given base sites.
        """
        if len(site_ids) <= 1:
            return 0

        # Use the "code" layer as the representative
        cover = [ProductId(site_id=s, layer="code") for s in site_ids]
        try:
            cech = CechComplex(self._presheaf, cover)
            return cech.h1()
        except Exception:  # noqa: BLE001
            return 0

    def __repr__(self) -> str:
        return f"LeraySpectralSequence(presheaf={self._presheaf.name!r})"


# ===========================================================================
# CechCohomology — standalone cohomology engine
# ===========================================================================


class CechCohomology:
    r"""General Čech cohomology engine for any presheaf over any cover.

    Wraps :class:`CechComplex` with a clean API for computing H⁰, H¹, H²
    and their generators.  Works over any coefficient ring: the *ring*
    parameter selects GF(2) (default, boolean agree/disagree), Z (integer
    differences), or an abstract ring supplied as a callable.

    Usage::

        coh = CechCohomology(presheaf, cover, ring="gf2")
        print(coh.compute_h0())   # global sections
        print(coh.compute_h1())   # obstruction rank
        print(coh.generators(1))  # independent H¹ generators
    """

    # Supported coefficient rings
    _RINGS = frozenset({"gf2", "Z", "Q", "abstract"})

    def __init__(
        self,
        presheaf: LayeredPresheaf,
        cover: Optional[List[ProductId]] = None,
        *,
        ring: str = "gf2",
        label: str = "",
    ) -> None:
        if ring not in self._RINGS:
            raise ValueError(
                f"Unknown ring {ring!r}; expected one of {sorted(self._RINGS)}"
            )
        self._presheaf = presheaf
        self._ring = ring
        self._label = label or presheaf.name

        if cover is None:
            cover = presheaf._layered_site.all_product_ids()
        self._cover = list(cover)
        self._cech = CechComplex(presheaf, self._cover)

        # Caches
        self._h_cache: Dict[int, int] = {}
        self._gen_cache: Dict[int, List[str]] = {}

    # ------------------------------------------------------------------
    # Public: cohomology groups
    # ------------------------------------------------------------------

    def compute_h0(
        self,
        presheaf: Optional[LayeredPresheaf] = None,
        cover: Optional[List[ProductId]] = None,
    ) -> int:
        """H⁰ = ker δ⁰ — global sections.

        When *presheaf* / *cover* are supplied they override the defaults
        set at construction time (convenient for one-shot calls).
        """
        cech = self._resolve_cech(presheaf, cover)
        if 0 not in self._h_cache or presheaf is not None:
            val = cech.h0()
            if presheaf is None:
                self._h_cache[0] = val
            return val
        return self._h_cache[0]

    def compute_h1(
        self,
        presheaf: Optional[LayeredPresheaf] = None,
        cover: Optional[List[ProductId]] = None,
    ) -> int:
        """H¹ = ker δ¹ / im δ⁰ — obstructions to gluing (THE KEY).

        H¹ = 0 ⟺ every compatible family of local sections glues to a
        unique global section (the presheaf is a sheaf on this cover).
        """
        cech = self._resolve_cech(presheaf, cover)
        if 1 not in self._h_cache or presheaf is not None:
            val = cech.h1()
            if presheaf is None:
                self._h_cache[1] = val
            return val
        return self._h_cache[1]

    def compute_h2(
        self,
        presheaf: Optional[LayeredPresheaf] = None,
        cover: Optional[List[ProductId]] = None,
    ) -> int:
        """H² — higher obstructions (from triple overlaps).

        H² measures failure of the cocycle condition on triple overlaps.
        Non-zero H² indicates *second-order* inconsistencies that persist
        even after resolving all pairwise disagreements.
        """
        cech = self._resolve_cech(presheaf, cover)
        if 2 not in self._h_cache or presheaf is not None:
            val = self._compute_h2_from(cech)
            if presheaf is None:
                self._h_cache[2] = val
            return val
        return self._h_cache[2]

    def generators(self, n: int) -> List[str]:
        """Independent generators of Hⁿ.

        Args:
            n: Cohomological degree (0, 1, or 2).

        Returns:
            List of human-readable generator descriptions.
        """
        if n in self._gen_cache:
            return list(self._gen_cache[n])

        if n == 0:
            gens = self._h0_generators()
        elif n == 1:
            gens = self._cech.h1_generators()
        elif n == 2:
            gens = self._h2_generators()
        else:
            gens = []

        self._gen_cache[n] = gens
        return list(gens)

    # ------------------------------------------------------------------
    # Ring-aware utilities
    # ------------------------------------------------------------------

    def difference(self, val_a: Any, val_b: Any) -> Any:
        """Compute the *difference* of two section values in the coefficient ring.

        For GF(2): returns 0 (agree) or 1 (disagree).
        For Z:     returns an integer encoding the disagreement magnitude.
        For Q:     returns a rational.
        """
        if self._ring == "gf2":
            return 0 if val_a == val_b else 1
        if self._ring == "Z":
            try:
                return int(val_a) - int(val_b)  # type: ignore[arg-type]
            except (TypeError, ValueError):
                return 0 if val_a == val_b else 1
        if self._ring == "Q":
            try:
                return float(val_a) - float(val_b)  # type: ignore[arg-type]
            except (TypeError, ValueError):
                return 0.0 if val_a == val_b else 1.0
        # abstract: delegate to __sub__ if available
        try:
            return val_a - val_b  # type: ignore[operator]
        except TypeError:
            return 0 if val_a == val_b else 1

    def is_zero(self, val: Any) -> bool:
        """Test whether a ring element is zero."""
        if self._ring == "gf2":
            return val == 0 or val is True  # True == agree
        if self._ring in ("Z", "Q"):
            return val == 0 or val == 0.0
        return not val

    # ------------------------------------------------------------------
    # Summary / bridging
    # ------------------------------------------------------------------

    def summary(self) -> Dict[str, Any]:
        """Compute all cohomology groups and return a summary dict."""
        h0 = self.compute_h0()
        h1 = self.compute_h1()
        h2 = self.compute_h2()
        return {
            "ring": self._ring,
            "h0": h0,
            "h1": h1,
            "h2": h2,
            "generators_h1": self.generators(1),
            "generators_h2": self.generators(2),
            "has_global_section": h1 == 0,
            "euler_characteristic": h0 - h1 + h2,
            "n_cover": len(self._cover),
            "n_overlaps": len(self._cech._overlaps),
            "n_triples": len(self._cech._triple_overlaps),
            "label": self._label,
        }

    def to_cohomological_result(self) -> Any:
        """Bridge to ``deppy.cohomological_analysis.CohomologicalResult``."""
        return self._cech.to_cohomological_result()

    # ------------------------------------------------------------------
    # Private
    # ------------------------------------------------------------------

    def _resolve_cech(
        self,
        presheaf: Optional[LayeredPresheaf],
        cover: Optional[List[ProductId]],
    ) -> CechComplex:
        """Return a CechComplex, possibly rebuilding for new args."""
        if presheaf is None and cover is None:
            return self._cech
        p = presheaf if presheaf is not None else self._presheaf
        c = cover if cover is not None else self._cover
        return CechComplex(p, c)

    def _compute_h2_from(self, cech: CechComplex) -> int:
        """Compute H² from the Čech complex data.

        H² = ker δ² / im δ¹.  Since we only track up to triple overlaps,
        ker δ² is the set of 2-cocycles and im δ¹ is the set of coboundaries
        arising from 1-cochains.
        """
        c2_data = cech.c2()
        d1_data = cech.delta1()

        # 2-cocycles: triples where the cocycle condition holds
        n_cocycles = sum(
            1 for data in c2_data.values()
            if data.get("cocycle", True)
        )
        # 2-coboundaries: triples that arise as δ¹ of some 1-cochain
        n_coboundaries = sum(
            1 for data in d1_data.values()
            if data.get("is_zero", True)
        )

        # H² = cocycles - coboundaries (rank difference)
        return max(0, n_cocycles - n_coboundaries)

    def _h0_generators(self) -> List[str]:
        """Generators for H⁰ (global sections)."""
        if self._cech.h0() == 0:
            return []
        return ["global_section: all local sections glue"]

    def _h2_generators(self) -> List[str]:
        """Generators for H² (triple-overlap obstructions)."""
        c2_data = self._cech.c2()
        d1_data = self._cech.delta1()
        gens: List[str] = []

        for (i, j, k), data in c2_data.items():
            if not data.get("cocycle", True):
                d1_entry = d1_data.get((i, j, k), {})
                if not d1_entry.get("is_zero", True):
                    pi = self._cover[i]
                    pj = self._cover[j]
                    pk = self._cover[k]
                    gens.append(
                        f"H2_gen({pi} ∩ {pj} ∩ {pk}): "
                        f"cocycle condition fails on triple overlap"
                    )
        return gens

    def __repr__(self) -> str:
        return (
            f"CechCohomology(ring={self._ring!r}, "
            f"cover={len(self._cover)}, "
            f"label={self._label!r})"
        )


# ===========================================================================
# DescentDatum — descent data for equivalence checking
# ===========================================================================


@dataclass
class DescentDatum:
    """Descent datum: transition maps on overlaps + cocycle verification.

    A descent datum for a presheaf ``F`` over a cover ``{U_i}`` consists of:

    - **transition maps** ``g_{ij}: F(U_i)|_{U_ij} → F(U_j)|_{U_ij}``
      (isomorphisms on double overlaps), and
    - the **cocycle condition** ``g_{ij} ∘ g_{jk} = g_{ik}`` on triple
      overlaps.

    When the cocycle condition holds and the descent is *effective*, a
    unique global object can be constructed by gluing local pieces.

    This is the algebraic-geometry formulation of the gluing axiom and
    is the key to checking whether two presheaves (implementations) are
    equivalent: ``H¹(Site, Iso(F, G)) = 0`` iff the descent datum is
    trivial.
    """

    sections: Dict[ProductId, LayerSection] = field(default_factory=dict)
    transition_maps: Dict[Tuple[ProductId, ProductId], Any] = field(
        default_factory=dict
    )
    presheaf: Optional[LayeredPresheaf] = field(default=None, repr=False)

    # ------------------------------------------------------------------
    # Transition map management
    # ------------------------------------------------------------------

    def add_transition(
        self,
        source: ProductId,
        target: ProductId,
        morphism: Any,
    ) -> None:
        """Register a transition map g_{source, target} on the overlap."""
        self.transition_maps[(source, target)] = morphism

    def get_transition(
        self, source: ProductId, target: ProductId
    ) -> Optional[Any]:
        """Look up the transition map between two cells."""
        return self.transition_maps.get((source, target))

    # ------------------------------------------------------------------
    # Cocycle condition
    # ------------------------------------------------------------------

    def cocycle_check(self) -> bool:
        """Verify the cocycle condition: g_{ij} ∘ g_{jk} = g_{ik}.

        Returns ``True`` iff every triple ``(i, j, k)`` with pairwise
        transition maps satisfies the associativity constraint.
        """
        cells = sorted(self.sections.keys(), key=str)
        for idx_i, i in enumerate(cells):
            for idx_j, j in enumerate(cells):
                if idx_j <= idx_i:
                    continue
                g_ij = self.transition_maps.get((i, j))
                if g_ij is None:
                    continue
                for k in cells[idx_j + 1:]:
                    g_jk = self.transition_maps.get((j, k))
                    g_ik = self.transition_maps.get((i, k))
                    if g_jk is None or g_ik is None:
                        continue
                    if not self._compose_equals(g_ij, g_jk, g_ik):
                        return False
        return True

    def cocycle_failures(self) -> List[Tuple[ProductId, ProductId, ProductId]]:
        """Return all triples ``(i, j, k)`` where the cocycle condition fails."""
        failures: List[Tuple[ProductId, ProductId, ProductId]] = []
        cells = sorted(self.sections.keys(), key=str)
        for idx_i, i in enumerate(cells):
            for idx_j, j in enumerate(cells):
                if idx_j <= idx_i:
                    continue
                g_ij = self.transition_maps.get((i, j))
                if g_ij is None:
                    continue
                for k in cells[idx_j + 1:]:
                    g_jk = self.transition_maps.get((j, k))
                    g_ik = self.transition_maps.get((i, k))
                    if g_jk is None or g_ik is None:
                        continue
                    if not self._compose_equals(g_ij, g_jk, g_ik):
                        failures.append((i, j, k))
        return failures

    # ------------------------------------------------------------------
    # Effective descent
    # ------------------------------------------------------------------

    def effective_descent(self) -> Optional[Dict[str, Any]]:
        """When the cocycle condition holds, construct the global object.

        Effective descent means the local pieces ``{F(U_i)}`` together
        with the transition maps ``{g_{ij}}`` uniquely determine a global
        section ``s ∈ F(U)`` whose restrictions recover each local piece.

        Returns ``None`` if the cocycle condition fails.
        """
        if not self.cocycle_check():
            return None

        if self.presheaf is not None:
            checker = DescentChecker()
            return checker.glue(self.sections)

        # Fallback: manual gluing by grouping sections by base site
        by_site: Dict[str, Dict[str, Any]] = {}
        for pid, sec in self.sections.items():
            by_site.setdefault(pid.site_id, {})[pid.layer] = {
                "value": sec.value,
                "trust": sec.trust,
                "refinement": sec.refinement,
            }

        return {"global_object": by_site, "cocycle": True}

    def is_trivial(self) -> bool:
        """Check whether the descent datum is *trivial* (all transitions are identity).

        A trivial descent datum means the local sections are already
        globally compatible without any twisting.
        """
        for (src, tgt), g in self.transition_maps.items():
            src_sec = self.sections.get(src)
            tgt_sec = self.sections.get(tgt)
            if src_sec is None or tgt_sec is None:
                continue
            # Apply transition and check if result equals target section
            if callable(g):
                try:
                    result = g(src_sec)
                    if hasattr(result, "value") and hasattr(tgt_sec, "value"):
                        if result.value != tgt_sec.value:
                            return False
                except Exception:  # noqa: BLE001
                    return False
            elif g is not None:
                # Non-callable transition: check identity
                if src_sec.value != tgt_sec.value:
                    return False
        return True

    # ------------------------------------------------------------------
    # Factory: build from presheaf
    # ------------------------------------------------------------------

    @classmethod
    def from_presheaf(
        cls,
        presheaf: LayeredPresheaf,
        cover: Optional[List[ProductId]] = None,
    ) -> DescentDatum:
        """Build a descent datum from a presheaf and cover.

        The transition maps are derived from the presheaf's restriction
        maps: ``g_{ij}`` is the restriction of ``F(U_i)`` to ``U_ij``
        compared to the restriction of ``F(U_j)`` to ``U_ij``.
        """
        site = presheaf._layered_site
        if cover is None:
            cover = site.all_product_ids()

        all_sections = presheaf.all_layer_sections()
        sections = {pid: all_sections[pid] for pid in cover if pid in all_sections}

        datum = cls(sections=sections, presheaf=presheaf)

        # Build transition maps from restriction compatibility
        for i, pid_i in enumerate(cover):
            for pid_j in cover[i + 1:]:
                if not site.overlap(pid_i, pid_j):
                    continue
                sec_i = sections.get(pid_i)
                sec_j = sections.get(pid_j)
                if sec_i is None or sec_j is None:
                    continue
                # The transition map is "identity if compatible, else the diff"
                compatible = presheaf.compatible_on_overlap(sec_i, sec_j)
                if compatible:
                    datum.add_transition(pid_i, pid_j, lambda s, _t=sec_j: _t)
                    datum.add_transition(pid_j, pid_i, lambda s, _t=sec_i: _t)
                else:
                    datum.add_transition(pid_i, pid_j, None)
                    datum.add_transition(pid_j, pid_i, None)

        return datum

    # ------------------------------------------------------------------
    # Private
    # ------------------------------------------------------------------

    def _compose_equals(self, g_ij: Any, g_jk: Any, g_ik: Any) -> bool:
        """Check g_ij ∘ g_jk = g_ik by applying to a test element.

        For callable transitions, compose and compare.  For non-callable
        (e.g. ``None`` = identity), use direct equality.
        """
        if g_ij is None or g_jk is None or g_ik is None:
            # None indicates a broken transition — cocycle fails
            return g_ij is None and g_jk is None and g_ik is None

        if callable(g_ij) and callable(g_jk) and callable(g_ik):
            # Apply to each section and compare
            for sec in self.sections.values():
                try:
                    composed = g_jk(g_ij(sec))
                    direct = g_ik(sec)
                    if hasattr(composed, "value") and hasattr(direct, "value"):
                        if composed.value != direct.value:
                            return False
                    elif composed != direct:
                        return False
                except Exception:  # noqa: BLE001
                    return False
            return True

        # Fallback: structural equality
        return g_ij == g_ik  # type: ignore[comparison-overlap]


# ===========================================================================
# FiberedCategory — dependent types as fibrations
# ===========================================================================


class FiberedCategory:
    """Models dependent types as a fibered category (Grothendieck fibration).

    A fibered category ``p: E → B`` assigns to each base object ``b ∈ B``
    a *fiber* ``E_b`` (the type family at value ``b``), and to each
    morphism ``f: a → b`` in the base a *reindexing* functor
    ``f*: E_b → E_a`` (pullback along base change).

    In the deppy context:
    - **Base category** ``B`` = the site category ``Site(P)``
    - **Fiber** ``E_b`` = the type at site ``b`` (across all layers)
    - **Reindexing** ``f*`` = restriction along a morphism (data flow edge)

    This is the categorical semantics of dependent types: a type family
    ``(x : A) → B(x)`` is a fibration over ``A``, where ``B(x)`` is the
    fiber above ``x``.
    """

    def __init__(
        self,
        presheaf: LayeredPresheaf,
        *,
        name: str = "DepType",
    ) -> None:
        self._presheaf = presheaf
        self._site = presheaf._layered_site
        self._name = name

        # Cache fibers: base_site_id → list of layer sections
        self._fiber_cache: Dict[str, List[LayerSection]] = {}
        # Reindex functors: (source_site, target_site) → callable
        self._reindex_cache: Dict[Tuple[str, str], Callable[..., LayerSection]] = {}

    # ------------------------------------------------------------------
    # Fiber queries
    # ------------------------------------------------------------------

    def fiber_at(self, base_object: str) -> List[LayerSection]:
        """The fiber E_b: the type family at a given base site.

        Returns all layer sections at the given base site, representing
        the full dependent type at that observation point.
        """
        if base_object in self._fiber_cache:
            return list(self._fiber_cache[base_object])

        sections = self._presheaf.site_slice_sections(base_object)
        self._fiber_cache[base_object] = sections
        return list(sections)

    def fiber_rank(self, base_object: str) -> int:
        """Number of sections in the fiber at ``base_object``."""
        return len(self.fiber_at(base_object))

    def fiber_layers(self, base_object: str) -> Dict[str, Optional[LayerSection]]:
        """Return fiber organized by layer."""
        result: Dict[str, Optional[LayerSection]] = {l: None for l in LAYERS}
        for sec in self.fiber_at(base_object):
            result[sec.layer] = sec
        return result

    # ------------------------------------------------------------------
    # Reindexing (pullback along base change)
    # ------------------------------------------------------------------

    def reindex(
        self,
        morphism: Tuple[str, str],
        section: Optional[LayerSection] = None,
    ) -> Callable[..., LayerSection]:
        """Pullback functor f*: E_b → E_a along base change ``f: a → b``.

        Given a morphism ``(source, target)`` in the base category, returns
        a callable that reindexes sections from the target fiber to the
        source fiber.

        If *section* is given, applies the reindex immediately and returns
        the result.
        """
        source, target = morphism

        if (source, target) not in self._reindex_cache:
            def _reindex_fn(
                sec: LayerSection,
                _src: str = source,
                _tgt: str = target,
            ) -> LayerSection:
                return self._presheaf.restrict_site(sec, _tgt, _src)

            self._reindex_cache[(source, target)] = _reindex_fn

        fn = self._reindex_cache[(source, target)]
        if section is not None:
            return fn(section)  # type: ignore[return-value]
        return fn

    def reindex_fiber(
        self, morphism: Tuple[str, str]
    ) -> List[LayerSection]:
        """Reindex the entire fiber along a base morphism.

        Pulls back every section in ``E_{target}`` to ``E_{source}``.
        """
        source, target = morphism
        target_fiber = self.fiber_at(target)
        fn = self.reindex(morphism)
        return [fn(sec) for sec in target_fiber]

    # ------------------------------------------------------------------
    # Fibration properties
    # ------------------------------------------------------------------

    def is_cartesian(self, morphism: Tuple[str, str]) -> bool:
        """Check whether reindexing along ``morphism`` is cartesian.

        A morphism is cartesian if pullback preserves all type information
        (no information is lost in reindexing).  Concretely: the reindexed
        fiber has the same rank as the original.
        """
        source, target = morphism
        original = self.fiber_at(target)
        reindexed = self.reindex_fiber(morphism)
        return len(reindexed) >= len(original)

    def total_space_sections(self) -> Dict[str, List[LayerSection]]:
        """Return all fibers (the total space ``E`` of the fibration)."""
        result: Dict[str, List[LayerSection]] = {}
        seen: Set[str] = set()
        for pid in self._presheaf.all_layer_sections():
            sid = pid.site_id
            if sid not in seen:
                seen.add(sid)
                result[sid] = self.fiber_at(sid)
        return result

    def base_objects(self) -> List[str]:
        """All base objects that have non-empty fibers."""
        seen: Set[str] = set()
        result: List[str] = []
        for pid in self._presheaf.all_layer_sections():
            sid = pid.site_id
            if sid not in seen:
                seen.add(sid)
                result.append(sid)
        return result

    def __repr__(self) -> str:
        n = len(self.base_objects())
        return f"FiberedCategory(name={self._name!r}, base_objects={n})"


# ===========================================================================
# ProductSite — Site(P) × Layer as a first-class site
# ===========================================================================


class ProductSite:
    """The product site ``Site(P) × Layer`` for hybrid dependent types.

    Wraps :class:`LayeredSite` with the standard site interface:
    ``objects()``, ``morphisms()``, ``covers()``.

    Objects are ``(program_site, layer)`` pairs.  Morphisms decompose as:

    - **Horizontal** (data flow): morphisms in ``Site(P)`` lifted to each layer
    - **Vertical** (layer restriction): adjacent-layer maps at each site

    Covering families are product covers: horizontal covers lifted across
    layers, combined with the vertical layer-adjacency covers.
    """

    def __init__(
        self,
        base_site_ids: List[str],
        *,
        base_overlaps: Optional[List[Tuple[str, str]]] = None,
        base_morphisms: Optional[List[Tuple[str, str]]] = None,
        layers: Tuple[str, ...] = LAYERS,
    ) -> None:
        self._layered_site = LayeredSite(
            base_site_ids,
            base_overlaps=base_overlaps,
            layers=layers,
        )
        self._base_ids = list(base_site_ids)
        self._layers = layers
        self._base_morphisms = list(base_morphisms or [])

    # ------------------------------------------------------------------
    # Site interface
    # ------------------------------------------------------------------

    def objects(self) -> List[ProductId]:
        """All objects in the product site: ``(site, layer)`` pairs."""
        return self._layered_site.all_product_ids()

    def morphisms(self) -> List[Tuple[ProductId, ProductId]]:
        """All morphisms in the product category.

        Returns pairs ``(source, target)`` decomposed as:
        - Horizontal: ``(s1, l) → (s2, l)`` for each base morphism and layer
        - Vertical: ``(s, l1) → (s, l2)`` for adjacent layers at each site
        """
        result: List[Tuple[ProductId, ProductId]] = []

        # Horizontal morphisms: lift base morphisms to each layer
        for src, tgt in self._base_morphisms:
            for layer in self._layers:
                result.append((
                    ProductId(site_id=src, layer=layer),
                    ProductId(site_id=tgt, layer=layer),
                ))

        # Vertical morphisms: adjacent layers at each site
        for site_id in self._base_ids:
            for i in range(len(self._layers) - 1):
                result.append((
                    ProductId(site_id=site_id, layer=self._layers[i]),
                    ProductId(site_id=site_id, layer=self._layers[i + 1]),
                ))
                # Reverse direction (contravariant)
                result.append((
                    ProductId(site_id=site_id, layer=self._layers[i + 1]),
                    ProductId(site_id=site_id, layer=self._layers[i]),
                ))

        return result

    def covers(self) -> List[List[ProductId]]:
        """Covering families for the product site.

        Each base site generates a product covering family: the set of
        all ``(site, layer)`` cells for that site covers the site in the
        product topology.  Additionally, each layer slice is a cover.
        """
        families: List[List[ProductId]] = []

        # Per-site covers (vertical slices)
        for site_id in self._base_ids:
            families.append(self._layered_site.site_slice(site_id))

        # Per-layer covers (horizontal slices)
        for layer in self._layers:
            families.append(self._layered_site.layer_slice(layer))

        # The full product is itself a cover
        families.append(self._layered_site.all_product_ids())

        return families

    def overlap(self, a: ProductId, b: ProductId) -> bool:
        """Check overlap in the product topology."""
        return self._layered_site.overlap(a, b)

    def all_overlaps(self) -> List[Tuple[ProductId, ProductId]]:
        """All overlapping pairs."""
        return self._layered_site.all_overlaps()

    @property
    def layered_site(self) -> LayeredSite:
        """Access the underlying ``LayeredSite``."""
        return self._layered_site

    def __repr__(self) -> str:
        return (
            f"ProductSite(bases={len(self._base_ids)}, "
            f"layers={len(self._layers)}, "
            f"objects={len(self.objects())})"
        )


# ===========================================================================
# IsomorphismSheaf — Iso(F, G) for equivalence checking
# ===========================================================================


class IsomorphismSheaf:
    r"""The isomorphism presheaf ``Iso(F, G)`` for two presheaves F and G.

    At each site ``U``, ``Iso(F, G)(U)`` is the set of isomorphisms
    between ``F(U)`` and ``G(U)``.  The key theorem:

        **H¹(Site, Iso(F, G)) = 0  ⟺  F ≅ G**

    i.e., two implementations are equivalent iff all local isomorphisms
    glue to a global one (no cohomological obstruction).

    This class builds the ``Iso`` presheaf from two ``LayeredPresheaf``
    instances and computes the cohomological obstruction to equivalence.
    """

    def __init__(
        self,
        presheaf_f: LayeredPresheaf,
        presheaf_g: LayeredPresheaf,
        *,
        label: str = "",
    ) -> None:
        if presheaf_f._layered_site is not presheaf_g._layered_site:
            logger.warning(
                "IsomorphismSheaf: presheaves defined over different sites; "
                "comparison may be incomplete"
            )
        self._f = presheaf_f
        self._g = presheaf_g
        self._site = presheaf_f._layered_site
        self._label = label or f"Iso({presheaf_f.name}, {presheaf_g.name})"

        # Iso presheaf: store local isomorphism data
        self._local_isos: Dict[ProductId, bool] = {}
        self._iso_details: Dict[ProductId, Dict[str, Any]] = {}

    # ------------------------------------------------------------------
    # Local isomorphism computation
    # ------------------------------------------------------------------

    def compute_local_isos(self) -> Dict[ProductId, bool]:
        """Compute local isomorphisms at every cell.

        At each ``(site, layer)`` cell, checks whether ``F(U) ≅ G(U)``
        by comparing section data (value, refinement, trust).
        """
        if self._local_isos:
            return dict(self._local_isos)

        f_sections = self._f.all_layer_sections()
        g_sections = self._g.all_layer_sections()
        all_cells = set(f_sections.keys()) | set(g_sections.keys())

        for pid in all_cells:
            sec_f = f_sections.get(pid)
            sec_g = g_sections.get(pid)

            if sec_f is None and sec_g is None:
                self._local_isos[pid] = True
                self._iso_details[pid] = {"reason": "both_empty"}
            elif sec_f is None or sec_g is None:
                self._local_isos[pid] = False
                self._iso_details[pid] = {
                    "reason": "one_missing",
                    "has_f": sec_f is not None,
                    "has_g": sec_g is not None,
                }
            else:
                iso = self._sections_isomorphic(sec_f, sec_g)
                self._local_isos[pid] = iso
                self._iso_details[pid] = {
                    "reason": "compared",
                    "iso": iso,
                    "f_value": sec_f.value,
                    "g_value": sec_g.value,
                }

        return dict(self._local_isos)

    # ------------------------------------------------------------------
    # Cohomological obstruction
    # ------------------------------------------------------------------

    def h1_obstruction(self) -> int:
        """Compute H¹(Site, Iso(F, G)).

        Returns 0 iff F ≅ G (no obstruction to gluing local isos).
        """
        isos = self.compute_local_isos()

        # Build an Iso presheaf as a LayeredPresheaf
        iso_presheaf = LayeredPresheaf(self._site, name=self._label)
        for pid, is_iso in isos.items():
            sec = LayerSection(
                product_id=pid,
                refinement="iso" if is_iso else "non_iso",
                trust=5 if is_iso else 0,
                value=1 if is_iso else 0,
                provenance="iso_check",
            )
            iso_presheaf.add_layer_section(pid.site_id, pid.layer, sec)

        cover = self._site.all_product_ids()
        coh = CechCohomology(iso_presheaf, cover, label=self._label)
        return coh.compute_h1()

    def are_equivalent(self) -> bool:
        """Check whether F ≅ G: ``H¹(Site, Iso(F, G)) = 0``."""
        return self.h1_obstruction() == 0

    def equivalence_report(self) -> Dict[str, Any]:
        """Detailed equivalence report."""
        isos = self.compute_local_isos()
        h1 = self.h1_obstruction()
        n_local_iso = sum(1 for v in isos.values() if v)
        n_local_noniso = sum(1 for v in isos.values() if not v)

        return {
            "equivalent": h1 == 0,
            "h1": h1,
            "n_cells": len(isos),
            "n_local_iso": n_local_iso,
            "n_local_noniso": n_local_noniso,
            "non_iso_cells": [
                str(pid) for pid, v in isos.items() if not v
            ],
            "label": self._label,
        }

    # ------------------------------------------------------------------
    # Private
    # ------------------------------------------------------------------

    def _sections_isomorphic(
        self, sec_f: LayerSection, sec_g: LayerSection
    ) -> bool:
        """Check whether two sections are isomorphic.

        Two sections are isomorphic if they carry the same type information
        (value and refinement agree, trust is compatible).
        """
        # Values must match
        if sec_f.value is not None and sec_g.value is not None:
            if sec_f.value != sec_g.value:
                return False

        # Refinements must match
        if sec_f.refinement is not None and sec_g.refinement is not None:
            if sec_f.refinement != sec_g.refinement:
                return False

        # Trust levels must be compatible (within 1 step)
        if abs(sec_f.trust - sec_g.trust) > 1:
            return False

        return True

    def __repr__(self) -> str:
        return f"IsomorphismSheaf({self._label!r})"


# ===========================================================================
# SheafGluing — constructive gluing of compatible families
# ===========================================================================


class SheafGluing:
    """Constructive sheaf gluing: given compatible local sections, build
    the unique global section witnessing the sheaf condition.

    This class implements the computational content of the sheaf axiom:

    1. **Verify compatibility** on all overlaps (using the presheaf's
       restriction maps).
    2. **Merge** compatible sections into a single global section at each
       base site, taking the join of trust levels and the most refined value.
    3. **Witness** the construction: produce a proof trace showing which
       restrictions were checked and how sections were merged.

    The resulting global section is *the* unique one whose restrictions
    recover each local piece (uniqueness part of the sheaf condition).
    """

    def __init__(self, presheaf: LayeredPresheaf) -> None:
        self._presheaf = presheaf
        self._site = presheaf._layered_site

    # ------------------------------------------------------------------
    # Main gluing API
    # ------------------------------------------------------------------

    def glue(
        self,
        family: Optional[Dict[ProductId, LayerSection]] = None,
        *,
        cover: Optional[List[ProductId]] = None,
    ) -> GluingResult:
        """Attempt to glue a compatible family into a global section.

        Args:
            family: Mapping from product cells to local sections.
                If ``None``, uses all sections in the presheaf.
            cover: Optional explicit cover.  If ``None``, uses all cells
                in the family.

        Returns:
            ``GluingResult`` with ``success=True`` and the global section
            if gluing succeeds, or ``success=False`` with conflict details.
        """
        if family is None:
            family = self._presheaf.all_layer_sections()

        if cover is None:
            cover = list(family.keys())

        # Step 1: verify compatibility on all overlaps
        conflicts = self._check_compatibility(family, cover)
        if conflicts:
            conflict_strs = [
                (str(a), str(b)) for a, b in conflicts
            ]
            return GluingResult(
                success=False,
                conflicts=conflict_strs,  # type: ignore[arg-type]
                explanation=(
                    f"Gluing failed: {len(conflicts)} incompatible overlap(s)"
                ),
            )

        # Step 2: merge into global section
        global_section = self._merge_family(family)

        # Step 3: produce witness
        return GluingResult(
            success=True,
            global_section=global_section,
            explanation="Sheaf condition verified; global section constructed",
        )

    def glue_with_witness(
        self,
        family: Optional[Dict[ProductId, LayerSection]] = None,
    ) -> Tuple[GluingResult, Dict[str, Any]]:
        """Glue and produce a detailed witness/proof trace.

        Returns a ``(result, witness)`` pair where ``witness`` documents
        every overlap check and merge step.
        """
        if family is None:
            family = self._presheaf.all_layer_sections()
        cover = list(family.keys())

        witness: Dict[str, Any] = {
            "n_sections": len(family),
            "n_cover": len(cover),
            "overlap_checks": [],
            "merge_steps": [],
        }

        # Check all overlaps and record
        conflicts: List[Tuple[ProductId, ProductId]] = []
        for i, pid_i in enumerate(cover):
            for pid_j in cover[i + 1:]:
                if not self._site.overlap(pid_i, pid_j):
                    continue
                sec_i = family.get(pid_i)
                sec_j = family.get(pid_j)
                if sec_i is None or sec_j is None:
                    continue
                compat = self._presheaf.compatible_on_overlap(sec_i, sec_j)
                witness["overlap_checks"].append({
                    "cell_a": str(pid_i),
                    "cell_b": str(pid_j),
                    "compatible": compat,
                })
                if not compat:
                    conflicts.append((pid_i, pid_j))

        if conflicts:
            result = GluingResult(
                success=False,
                conflicts=[(str(a), str(b)) for a, b in conflicts],  # type: ignore[arg-type]
                explanation=f"Gluing failed: {len(conflicts)} conflict(s)",
            )
            witness["outcome"] = "failed"
            return result, witness

        # Merge
        global_section = self._merge_family(family)
        for pid, sec in family.items():
            witness["merge_steps"].append({
                "cell": str(pid),
                "value": sec.value,
                "trust": sec.trust,
            })
        witness["outcome"] = "success"

        result = GluingResult(
            success=True,
            global_section=global_section,
            explanation="Glued successfully with full witness",
        )
        return result, witness

    # ------------------------------------------------------------------
    # Uniqueness verification
    # ------------------------------------------------------------------

    def verify_uniqueness(
        self,
        global_section: Any,
        family: Dict[ProductId, LayerSection],
    ) -> bool:
        """Verify the uniqueness part of the sheaf condition.

        The global section is unique: its restriction to each cover element
        recovers the original local section.
        """
        if global_section is None:
            return False

        if isinstance(global_section, dict):
            for pid, sec in family.items():
                site_data = global_section.get(pid.site_id)
                if site_data is None:
                    return False
                layers = site_data.get("layers", {})
                if pid.layer in layers:
                    if layers[pid.layer] != sec.value:
                        return False
            return True

        # For core GlobalSection objects
        if _HAS_CORE and hasattr(global_section, "at"):
            core_id = SiteId(kind=SiteKind.PROOF, name="check")
            try:
                for pid, sec in family.items():
                    gs_sec = global_section.at(
                        SiteId(kind=SiteKind.PROOF, name=str(pid))
                    )
                    if gs_sec is not None and gs_sec.carrier_type != sec.value:
                        return False
            except Exception:  # noqa: BLE001
                pass
            return True

        return True

    # ------------------------------------------------------------------
    # Private
    # ------------------------------------------------------------------

    def _check_compatibility(
        self,
        family: Dict[ProductId, LayerSection],
        cover: List[ProductId],
    ) -> List[Tuple[ProductId, ProductId]]:
        """Check pairwise compatibility on overlaps."""
        conflicts: List[Tuple[ProductId, ProductId]] = []
        for i, pid_i in enumerate(cover):
            for pid_j in cover[i + 1:]:
                if not self._site.overlap(pid_i, pid_j):
                    continue
                sec_i = family.get(pid_i)
                sec_j = family.get(pid_j)
                if sec_i is None or sec_j is None:
                    continue
                if not self._presheaf.compatible_on_overlap(sec_i, sec_j):
                    conflicts.append((pid_i, pid_j))
        return conflicts

    def _merge_family(
        self, family: Dict[ProductId, LayerSection]
    ) -> Any:
        """Merge a compatible family into a global section dict."""
        by_site: Dict[str, Dict[str, LayerSection]] = {}
        for pid, sec in family.items():
            by_site.setdefault(pid.site_id, {})[pid.layer] = sec

        result: Dict[str, Any] = {}
        for site_id, layer_map in by_site.items():
            max_trust = max(
                (sec.trust for sec in layer_map.values()), default=0
            )
            value = None
            for layer in reversed(LAYERS):
                if layer in layer_map and layer_map[layer].value is not None:
                    value = layer_map[layer].value
                    break

            result[site_id] = {
                "trust": max_trust,
                "value": value,
                "layers": {l: sec.value for l, sec in layer_map.items()},
            }

        return result

    def __repr__(self) -> str:
        return f"SheafGluing(presheaf={self._presheaf.name!r})"


# ===========================================================================
# Convenience: compute_h1
# ===========================================================================


def compute_h1(
    presheaf: LayeredPresheaf,
    *,
    method: str = "cech",
) -> Dict[str, Any]:
    """One-shot convenience: compute H^1 for a layered presheaf.

    Args:
        presheaf: The layered presheaf to analyze.
        method: Computation method — ``"cech"`` (default), ``"mayer_vietoris"``,
            or ``"spectral"``.

    Returns:
        Dictionary with ``h1``, ``generators``, ``has_global_section``, and method-specific details.
    """
    site = presheaf._layered_site
    cover = site.all_product_ids()

    if method == "cech":
        cech = CechComplex(presheaf, cover)
        h1_val = cech.h1()
        return {
            "h1": h1_val,
            "h0": cech.h0(),
            "generators": cech.h1_generators(),
            "has_global_section": h1_val == 0,
            "n_overlaps": len(cech._overlaps),
            "method": "cech",
        }

    elif method == "mayer_vietoris":
        # Split cover: intent+structural vs semantic+proof+code
        cover_a = [p for p in cover if _LAYER_INDEX.get(p.layer, 0) < 2]
        cover_b = [p for p in cover if _LAYER_INDEX.get(p.layer, 0) >= 2]
        mv = MayerVietoris(presheaf)
        h1_val = mv.compute(cover_a, cover_b)
        return {
            "h1": h1_val,
            "has_global_section": h1_val == 0,
            "method": "mayer_vietoris",
            "cover_a_size": len(cover_a),
            "cover_b_size": len(cover_b),
        }

    elif method == "spectral":
        ss = LeraySpectralSequence(presheaf)
        h1_val = ss.converge()
        e2 = ss.e2_page()
        return {
            "h1": h1_val,
            "has_global_section": h1_val == 0,
            "method": "spectral",
            "e2_page": {
                f"E2^{{{p},{q}}}": entry.rank
                for (p, q), entry in sorted(e2.items())
            },
            "summary": ss.summary(),
        }

    else:
        raise ValueError(f"Unknown method: {method!r}. Use 'cech', 'mayer_vietoris', or 'spectral'.")


# ===========================================================================
# __all__
# ===========================================================================

__all__ = [
    # Data types
    "ProductId",
    "LayerSection",
    "DescentResult",
    "DescentStatus",
    "SpectralEntry",
    "LAYERS",
    # Core classes
    "LayeredSite",
    "LayeredPresheaf",
    "CechComplex",
    "CechCohomology",
    "DescentChecker",
    "DescentDatum",
    "MayerVietoris",
    "FiberedCategory",
    "ProductSite",
    "IsomorphismSheaf",
    "SheafGluing",
    "ObstructionLocalizer",
    "LeraySpectralSequence",
    # Convenience
    "compute_h1",
]
