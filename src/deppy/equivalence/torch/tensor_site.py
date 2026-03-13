"""
Tensor observation site category — the Grothendieck topology for PyTorch programs.

A PyTorch function f: Tensor^n → Tensor^m is modelled as a presheaf on a
site category whose objects are *observation sites* — typed slices through
which we can probe f's behaviour.  The sites are organized into a
canonical filtration (partial order of strata):

    METADATA ≤ STRUCTURAL ≤ NUMERICAL ≤ BEHAVIORAL

Each stratum adds finer-grained observations.  A *cover* of a tensor
signature is a collection of sites whose union sees all observable
behaviour: shape, dtype, device, strides, numerical values, autograd, etc.

Morphisms between sites encode how one observation restricts to another:
broadcasting restricts shapes, dtype promotion restricts dtypes, device
transfer restricts placements, etc.

Sheaf-theoretically, a function f is a *section* over a cover U; two
functions f,g are equivalent iff their section-pairs glue across the
Čech nerve of U.
"""

from __future__ import annotations

import hashlib
import itertools
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from ._protocols import (
    Cover,
    EquivalenceVerdict,
    LocalSection,
    MLIRDialect,
    MLIRModuleSpec,
    NumericalToleranceSpec,
    SiteId,
    SiteKind,
    TensorEquivalenceConfig,
    TensorLocalJudgment,
    TensorMorphismKind,
    TensorObstruction,
    TensorObstructionKind,
    TensorSiteCategory,
    TensorSiteKind,
    TensorSiteMorphism,
    TensorSpec,
    TensorStratum,
    TritonKernelSpec,
    SITE_KIND_STRATUM,
)


# ---------------------------------------------------------------------------
# Canonical site lattice
# ---------------------------------------------------------------------------

# Stratum partial order: METADATA < STRUCTURAL < NUMERICAL < BEHAVIORAL
_STRATUM_ORDER: Dict[TensorStratum, int] = {
    TensorStratum.METADATA: 0,
    TensorStratum.STRUCTURAL: 1,
    TensorStratum.NUMERICAL: 2,
    TensorStratum.BEHAVIORAL: 3,
}


def stratum_leq(a: TensorStratum, b: TensorStratum) -> bool:
    """a ≤ b in the stratum partial order."""
    return _STRATUM_ORDER[a] <= _STRATUM_ORDER[b]


def stratum_join(a: TensorStratum, b: TensorStratum) -> TensorStratum:
    """Least upper bound (join) of two strata."""
    if _STRATUM_ORDER[a] >= _STRATUM_ORDER[b]:
        return a
    return b


def stratum_meet(a: TensorStratum, b: TensorStratum) -> TensorStratum:
    """Greatest lower bound (meet) of two strata."""
    if _STRATUM_ORDER[a] <= _STRATUM_ORDER[b]:
        return a
    return b


# ---------------------------------------------------------------------------
# Observation site
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TensorObservationSite:
    """
    An observation site in the tensor site category.

    Each site probes *one aspect* of a tensor function:
      - shape site: observes output shapes given input shapes
      - dtype site: observes output dtypes given input dtypes
      - device site: observes output devices given input devices
      - stride site: observes output strides / contiguity
      - numerical site: observes concrete output values at specific inputs
      - autograd site: observes gradient computation
      - kernel_config: observes Triton launch grid / block sizing
      - triton_block: observes per-block tile computation
      - triton_memory: observes memory access patterns
      - triton_reduction: observes reduction order / associativity
      - mlir_op: observes MLIR operation semantics

    The site_id is a content-addressed hash of (kind, spec, params).
    """
    kind: TensorSiteKind
    spec: Optional[TensorSpec] = None
    triton_spec: Optional[TritonKernelSpec] = None
    mlir_spec: Optional[MLIRModuleSpec] = None
    params: Tuple[Tuple[str, Any], ...] = ()
    _site_id: Optional[SiteId] = field(default=None, repr=False)

    @property
    def site_id(self) -> SiteId:
        if self._site_id is not None:
            return self._site_id
        h = hashlib.sha256()
        h.update(self.kind.name.encode())
        if self.spec is not None:
            h.update(repr(self.spec).encode())
        if self.triton_spec is not None:
            h.update(repr(self.triton_spec).encode())
        if self.mlir_spec is not None:
            h.update(repr(self.mlir_spec).encode())
        for k, v in self.params:
            h.update(f"{k}={v}".encode())
        return SiteId(kind=SiteKind.TENSOR_SHAPE, name=f"{self.kind.name}_{h.hexdigest()[:12]}")

    @property
    def stratum(self) -> TensorStratum:
        return SITE_KIND_STRATUM[self.kind]


# ---------------------------------------------------------------------------
# Covering family
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TensorCover:
    """
    A covering family in the tensor Grothendieck topology.

    A cover is a collection of observation sites whose union sees all
    observable behaviour of a tensor function up to a given stratum.
    The cover satisfies the *sieve axiom*: for every morphism
    s: U → V in the site category, if V ∈ cover then the pullback
    s*(V) is also covered.

    The stratum field records the maximum stratum the cover reaches.
    """
    sites: FrozenSet[TensorObservationSite]
    stratum: TensorStratum
    name: str = ""

    @property
    def site_ids(self) -> FrozenSet[SiteId]:
        return frozenset(s.site_id for s in self.sites)

    def restrict_to_stratum(self, s: TensorStratum) -> "TensorCover":
        """Restrict cover to sites at or below stratum s."""
        restricted = frozenset(
            site for site in self.sites if stratum_leq(site.stratum, s)
        )
        return TensorCover(
            sites=restricted,
            stratum=stratum_meet(self.stratum, s),
            name=f"{self.name}|≤{s.name}",
        )

    def union(self, other: "TensorCover") -> "TensorCover":
        """Union of two covers (the join in the cover lattice)."""
        return TensorCover(
            sites=self.sites | other.sites,
            stratum=stratum_join(self.stratum, other.stratum),
            name=f"{self.name}∪{other.name}",
        )

    def intersect(self, other: "TensorCover") -> "TensorCover":
        """Intersection of two covers."""
        common = self.sites & other.sites
        if not common:
            st = TensorStratum.METADATA
        else:
            st = max((s.stratum for s in common),
                     key=lambda x: _STRATUM_ORDER[x])
        return TensorCover(
            sites=common,
            stratum=st,
            name=f"{self.name}∩{other.name}",
        )


# ---------------------------------------------------------------------------
# Restriction maps
# ---------------------------------------------------------------------------

def _broadcast_restriction(source_shape: Tuple[int, ...],
                           target_shape: Tuple[int, ...]) -> Optional[Callable]:
    """
    Build the restriction map for a BROADCAST morphism.
    Returns a callable that restricts a section from target shape to
    source shape by undoing broadcasting.
    """
    try:
        import torch
        # Verify broadcastability
        torch.broadcast_shapes(source_shape, target_shape)
    except Exception:
        return None

    def restrict(section: Any) -> Any:
        """Restrict by summing over broadcast dimensions."""
        return section  # Symbolic — actual restriction in numerical checker
    return restrict


def _promote_restriction(source_dtype: str, target_dtype: str) -> Optional[Callable]:
    """Build restriction map for PROMOTE morphism (dtype promotion)."""
    try:
        import torch
        src = getattr(torch, source_dtype, None)
        tgt = getattr(torch, target_dtype, None)
        if src is None or tgt is None:
            return None
        result = torch.result_type(torch.zeros(1, dtype=src),
                                   torch.zeros(1, dtype=tgt))
        if result != tgt:
            return None
    except Exception:
        return None

    def restrict(section: Any) -> Any:
        return section
    return restrict


def _transfer_restriction(source_device: str, target_device: str) -> Optional[Callable]:
    """Build restriction map for TRANSFER morphism (device placement)."""
    def restrict(section: Any) -> Any:
        return section
    return restrict


def _identity_restriction() -> Callable:
    def restrict(section: Any) -> Any:
        return section
    return restrict


# ---------------------------------------------------------------------------
# Site category builder
# ---------------------------------------------------------------------------

class TensorSiteCategoryBuilder:
    """
    Constructs the tensor site category from function signatures.

    The builder inspects input/output tensor specs and creates:
    1. One observation site per (site_kind, tensor_position) pair
    2. Morphisms encoding how observations restrict across strata
    3. A canonical cover for each stratum level

    The resulting TensorSiteCategory is the underlying category of the
    Grothendieck topology on which tensor presheaves are defined.
    """

    def __init__(self, config: TensorEquivalenceConfig):
        self._config = config
        self._sites: List[TensorObservationSite] = []
        self._morphisms: List[TensorSiteMorphism] = []
        self._site_map: Dict[SiteId, TensorObservationSite] = {}

    def _add_site(self, site: TensorObservationSite) -> SiteId:
        sid = site.site_id
        if sid not in self._site_map:
            self._sites.append(site)
            self._site_map[sid] = site
        return sid

    def _add_morphism(self, source: SiteId, target: SiteId,
                      kind: TensorMorphismKind,
                      restriction: Optional[Callable] = None,
                      metadata: Optional[Dict[str, Any]] = None) -> None:
        self._morphisms.append(TensorSiteMorphism(
            source=source,
            target=target,
            kind=kind,
            restriction_map=restriction or _identity_restriction(),
            metadata=metadata or {},
        ))

    # -- Core site generation -----------------------------------------------

    def _generate_shape_sites(self, inputs: Sequence[TensorSpec],
                              outputs: Sequence[TensorSpec]) -> List[SiteId]:
        """Generate shape observation sites for each tensor position."""
        sids: List[SiteId] = []
        for i, spec in enumerate(inputs):
            site = TensorObservationSite(
                kind=TensorSiteKind.SHAPE,
                spec=spec,
                params=(("position", f"input_{i}"),),
            )
            sids.append(self._add_site(site))
        for i, spec in enumerate(outputs):
            site = TensorObservationSite(
                kind=TensorSiteKind.SHAPE,
                spec=spec,
                params=(("position", f"output_{i}"),),
            )
            sids.append(self._add_site(site))
        return sids

    def _generate_dtype_sites(self, inputs: Sequence[TensorSpec],
                              outputs: Sequence[TensorSpec]) -> List[SiteId]:
        sids: List[SiteId] = []
        for i, spec in enumerate(inputs):
            site = TensorObservationSite(
                kind=TensorSiteKind.DTYPE,
                spec=spec,
                params=(("position", f"input_{i}"),),
            )
            sids.append(self._add_site(site))
        for i, spec in enumerate(outputs):
            site = TensorObservationSite(
                kind=TensorSiteKind.DTYPE,
                spec=spec,
                params=(("position", f"output_{i}"),),
            )
            sids.append(self._add_site(site))
        return sids

    def _generate_device_sites(self, inputs: Sequence[TensorSpec],
                               outputs: Sequence[TensorSpec]) -> List[SiteId]:
        sids: List[SiteId] = []
        for i, spec in enumerate(inputs):
            site = TensorObservationSite(
                kind=TensorSiteKind.DEVICE,
                spec=spec,
                params=(("position", f"input_{i}"),),
            )
            sids.append(self._add_site(site))
        return sids

    def _generate_stride_sites(self, inputs: Sequence[TensorSpec],
                                outputs: Sequence[TensorSpec]) -> List[SiteId]:
        sids: List[SiteId] = []
        for i, spec in enumerate(inputs):
            if spec.strides is not None:
                site = TensorObservationSite(
                    kind=TensorSiteKind.STRIDE,
                    spec=spec,
                    params=(("position", f"input_{i}"),),
                )
                sids.append(self._add_site(site))
        for i, spec in enumerate(outputs):
            if spec.strides is not None:
                site = TensorObservationSite(
                    kind=TensorSiteKind.STRIDE,
                    spec=spec,
                    params=(("position", f"output_{i}"),),
                )
                sids.append(self._add_site(site))
        return sids

    def _generate_numerical_sites(self, inputs: Sequence[TensorSpec],
                                   outputs: Sequence[TensorSpec]) -> List[SiteId]:
        sids: List[SiteId] = []
        for i, spec in enumerate(outputs):
            site = TensorObservationSite(
                kind=TensorSiteKind.NUMERICAL,
                spec=spec,
                params=(("position", f"output_{i}"),),
            )
            sids.append(self._add_site(site))
        return sids

    def _generate_autograd_sites(self, inputs: Sequence[TensorSpec],
                                  outputs: Sequence[TensorSpec]) -> List[SiteId]:
        sids: List[SiteId] = []
        grad_inputs = [s for s in inputs if s.requires_grad]
        if grad_inputs:
            for i, spec in enumerate(grad_inputs):
                site = TensorObservationSite(
                    kind=TensorSiteKind.AUTOGRAD,
                    spec=spec,
                    params=(("position", f"grad_input_{i}"),),
                )
                sids.append(self._add_site(site))
        return sids

    def _generate_triton_sites(self, kernel: TritonKernelSpec) -> List[SiteId]:
        """Generate sites for a Triton kernel: block, memory, reduction."""
        sids: List[SiteId] = []
        # One TRITON_BLOCK site per block spec
        for bs in kernel.block_specs:
            site = TensorObservationSite(
                kind=TensorSiteKind.TRITON_BLOCK,
                triton_spec=kernel,
                params=(("block", bs.name), ("size", bs.size)),
            )
            sids.append(self._add_site(site))
        # Kernel config site
        config_site = TensorObservationSite(
            kind=TensorSiteKind.KERNEL_CONFIG,
            triton_spec=kernel,
            params=(("num_warps", kernel.num_warps),
                    ("num_stages", kernel.num_stages)),
        )
        sids.append(self._add_site(config_site))
        # Memory access sites
        for ma in kernel.memory_accesses:
            site = TensorObservationSite(
                kind=TensorSiteKind.TRITON_MEMORY,
                triton_spec=kernel,
                params=(("pointer", ma.pointer_name),
                        ("is_load", ma.is_load)),
            )
            sids.append(self._add_site(site))
        # Reduction sites
        for red in kernel.reductions:
            site = TensorObservationSite(
                kind=TensorSiteKind.TRITON_REDUCTION,
                triton_spec=kernel,
                params=(("op", red.op), ("axis", red.axis)),
            )
            sids.append(self._add_site(site))
        return sids

    def _generate_mlir_sites(self, module: MLIRModuleSpec) -> List[SiteId]:
        """Generate sites for an MLIR module: one per dialect op."""
        sids: List[SiteId] = []
        for op in module.dialect_ops:
            site = TensorObservationSite(
                kind=TensorSiteKind.MLIR_OP,
                mlir_spec=module,
                params=(("dialect", op.dialect.name),
                        ("op", op.op_name)),
            )
            sids.append(self._add_site(site))
        return sids

    # -- Morphism generation ------------------------------------------------

    def _generate_stratum_morphisms(self) -> None:
        """
        Generate morphisms between sites encoding the stratum filtration.

        For each pair of sites where one is at a coarser stratum than the
        other, create a restriction morphism.  This encodes the presheaf
        functoriality: sections at finer strata restrict to coarser ones.
        """
        sites_by_stratum: Dict[TensorStratum, List[TensorObservationSite]] = {}
        for site in self._sites:
            sites_by_stratum.setdefault(site.stratum, []).append(site)

        strata_sorted = sorted(sites_by_stratum.keys(),
                               key=lambda s: _STRATUM_ORDER[s])

        for i, coarse in enumerate(strata_sorted):
            for fine in strata_sorted[i + 1:]:
                coarse_sites = sites_by_stratum[coarse]
                fine_sites = sites_by_stratum[fine]
                for cs in coarse_sites:
                    for fs in fine_sites:
                        if self._sites_compatible(cs, fs):
                            self._add_morphism(
                                source=fs.site_id,
                                target=cs.site_id,
                                kind=TensorMorphismKind.IDENTITY,
                                metadata={"stratum_restriction": True,
                                          "from": fine.name,
                                          "to": coarse.name},
                            )

    def _sites_compatible(self, coarse: TensorObservationSite,
                          fine: TensorObservationSite) -> bool:
        """
        Check if two sites are compatible for stratum restriction.
        Sites are compatible if they refer to the same tensor position.
        """
        coarse_pos = dict(coarse.params).get("position")
        fine_pos = dict(fine.params).get("position")
        if coarse_pos is None or fine_pos is None:
            return False
        return coarse_pos == fine_pos

    def _generate_broadcast_morphisms(self, shape_sids: List[SiteId]) -> None:
        """Generate BROADCAST morphisms between shape sites."""
        for i, sid_a in enumerate(shape_sids):
            for sid_b in shape_sids[i + 1:]:
                site_a = self._site_map[sid_a]
                site_b = self._site_map[sid_b]
                if site_a.spec and site_b.spec:
                    r = _broadcast_restriction(site_a.spec.shape, site_b.spec.shape)
                    if r is not None:
                        self._add_morphism(
                            source=sid_a, target=sid_b,
                            kind=TensorMorphismKind.BROADCAST,
                            restriction=r,
                            metadata={"from_shape": site_a.spec.shape,
                                      "to_shape": site_b.spec.shape},
                        )

    def _generate_promote_morphisms(self, dtype_sids: List[SiteId]) -> None:
        """Generate PROMOTE morphisms between dtype sites."""
        for i, sid_a in enumerate(dtype_sids):
            for sid_b in dtype_sids[i + 1:]:
                site_a = self._site_map[sid_a]
                site_b = self._site_map[sid_b]
                if site_a.spec and site_b.spec:
                    r = _promote_restriction(site_a.spec.dtype, site_b.spec.dtype)
                    if r is not None:
                        self._add_morphism(
                            source=sid_a, target=sid_b,
                            kind=TensorMorphismKind.PROMOTE,
                            restriction=r,
                            metadata={"from_dtype": site_a.spec.dtype,
                                      "to_dtype": site_b.spec.dtype},
                        )

    def _generate_triton_morphisms(self, triton_sids: List[SiteId]) -> None:
        """Generate TILE_REFINE and MASK_SIEVE morphisms for Triton."""
        block_sids = [s for s in triton_sids
                      if self._site_map[s].kind == TensorSiteKind.TRITON_BLOCK]
        config_sids = [s for s in triton_sids
                       if self._site_map[s].kind == TensorSiteKind.KERNEL_CONFIG]

        # Block → config restriction (tile refinement)
        for bsid in block_sids:
            for csid in config_sids:
                self._add_morphism(
                    source=bsid, target=csid,
                    kind=TensorMorphismKind.TILE_REFINE,
                    metadata={"tile_to_config": True},
                )

    def _generate_mlir_morphisms(self, mlir_sids: List[SiteId]) -> None:
        """Generate DIALECT_LOWER morphisms for MLIR lowering chain."""
        # MLIR sites for the same module form a lowering chain
        for i, sid_a in enumerate(mlir_sids):
            for sid_b in mlir_sids[i + 1:]:
                self._add_morphism(
                    source=sid_a, target=sid_b,
                    kind=TensorMorphismKind.DIALECT_LOWER,
                    metadata={"lowering_step": True},
                )

    # -- Build API ----------------------------------------------------------

    def build_from_specs(
        self,
        inputs: Sequence[TensorSpec],
        outputs: Sequence[TensorSpec],
        triton_kernel: Optional[TritonKernelSpec] = None,
        mlir_module: Optional[MLIRModuleSpec] = None,
    ) -> Tuple[TensorSiteCategory, TensorCover]:
        """
        Build the site category and canonical cover from tensor specs.

        Returns (category, cover) where the cover is the maximal cover
        including all enabled site kinds from the config.
        """
        cfg = self._config
        all_sids: List[SiteId] = []

        # Phase 1: Generate sites per stratum
        shape_sids = self._generate_shape_sites(inputs, outputs) if cfg.check_shape else []
        dtype_sids = self._generate_dtype_sites(inputs, outputs) if cfg.check_dtype else []
        device_sids = self._generate_device_sites(inputs, outputs) if cfg.check_device else []
        stride_sids = self._generate_stride_sites(inputs, outputs) if cfg.check_stride else []
        numerical_sids = self._generate_numerical_sites(inputs, outputs) if cfg.check_numerical else []
        autograd_sids = self._generate_autograd_sites(inputs, outputs) if cfg.check_autograd else []
        triton_sids = self._generate_triton_sites(triton_kernel) if triton_kernel and cfg.check_triton_ir else []
        mlir_sids = self._generate_mlir_sites(mlir_module) if mlir_module and cfg.check_mlir_ops else []

        all_sids = (shape_sids + dtype_sids + device_sids + stride_sids +
                    numerical_sids + autograd_sids + triton_sids + mlir_sids)

        # Phase 2: Generate morphisms
        self._generate_broadcast_morphisms(shape_sids)
        self._generate_promote_morphisms(dtype_sids)
        self._generate_triton_morphisms(triton_sids)
        self._generate_mlir_morphisms(mlir_sids)
        self._generate_stratum_morphisms()

        # Build outgoing adjacency
        outgoing: Dict[SiteId, List[TensorSiteMorphism]] = {}
        for m in self._morphisms:
            outgoing.setdefault(m.source, []).append(m)

        # Phase 3: Assemble category
        site_id_set = frozenset(all_sids)
        category = TensorSiteCategory(
            sites=site_id_set,
            morphisms=tuple(self._morphisms),
            _outgoing=outgoing,
        )

        # Phase 4: Build canonical cover
        max_stratum = TensorStratum.METADATA
        for site in self._sites:
            max_stratum = stratum_join(max_stratum, site.stratum)

        cover = TensorCover(
            sites=frozenset(self._sites),
            stratum=max_stratum,
            name="canonical",
        )

        return category, cover

    def build_from_signatures(
        self,
        sig_f: "TensorSignature",
        sig_g: "TensorSignature",
        triton_f: Optional[TritonKernelSpec] = None,
        triton_g: Optional[TritonKernelSpec] = None,
        mlir_f: Optional[MLIRModuleSpec] = None,
        mlir_g: Optional[MLIRModuleSpec] = None,
    ) -> Tuple[TensorSiteCategory, TensorCover, TensorCover]:
        """
        Build the tensor site category from two function signatures.

        Returns (category, cover_f, cover_g) where each cover represents
        the observation sites relevant to each function.  The *common
        refinement* of cover_f and cover_g is the domain for equivalence
        checking.
        """
        from ._protocols import TensorSignature

        # Build sites for f
        builder_f = TensorSiteCategoryBuilder(self._config)
        cat_f, cover_f = builder_f.build_from_specs(
            sig_f.inputs, sig_f.outputs, triton_f, mlir_f
        )

        # Build sites for g
        builder_g = TensorSiteCategoryBuilder(self._config)
        cat_g, cover_g = builder_g.build_from_specs(
            sig_g.inputs, sig_g.outputs, triton_g, mlir_g
        )

        # Merge into a single site category
        all_sites = cat_f.sites | cat_g.sites
        all_morphisms = list(cat_f.morphisms) + list(cat_g.morphisms)
        merged_outgoing: Dict[SiteId, List[TensorSiteMorphism]] = {}
        for m in all_morphisms:
            merged_outgoing.setdefault(m.source, []).append(m)

        merged_cat = TensorSiteCategory(
            sites=all_sites,
            morphisms=tuple(all_morphisms),
            _outgoing=merged_outgoing,
        )

        return merged_cat, cover_f, cover_g


# ---------------------------------------------------------------------------
# Common refinement
# ---------------------------------------------------------------------------

def common_refinement(cover_f: TensorCover,
                      cover_g: TensorCover) -> TensorCover:
    """
    Compute the common refinement of two tensor covers.

    In the Grothendieck topology, the common refinement U ∧ V is the
    smallest cover refining both U and V.  For tensor covers, this is
    the union of all sites present in both covers (by kind), plus any
    sites unique to one cover that have a compatible morphism target
    in the other.

    In the simplest case, this is U ∪ V (since both need to be checked).
    """
    return cover_f.union(cover_g)


# ---------------------------------------------------------------------------
# Čech nerve of a tensor cover
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CechSimplex:
    """A simplex in the Čech nerve of a tensor cover."""
    sites: Tuple[TensorObservationSite, ...]

    @property
    def dimension(self) -> int:
        return len(self.sites) - 1

    @property
    def site_ids(self) -> Tuple[SiteId, ...]:
        return tuple(s.site_id for s in self.sites)


def cech_nerve(cover: TensorCover, max_dim: int = 2) -> List[CechSimplex]:
    """
    Compute the Čech nerve of a tensor cover up to dimension max_dim.

    The Čech nerve N(U) is the simplicial complex whose k-simplices are
    (k+1)-fold intersections of cover elements.  Two sites intersect if
    they observe the same tensor position (compatible sites).

    For equivalence checking, the 0-simplices are individual sites,
    1-simplices are pairs of compatible sites (where gluing must agree),
    and 2-simplices encode cocycle conditions.
    """
    sites_list = sorted(cover.sites, key=lambda s: s.site_id)
    simplices: List[CechSimplex] = []

    # 0-simplices: individual sites
    for s in sites_list:
        simplices.append(CechSimplex(sites=(s,)))

    if max_dim < 1:
        return simplices

    # 1-simplices: compatible pairs
    for i, s1 in enumerate(sites_list):
        for s2 in sites_list[i + 1:]:
            if _sites_overlap(s1, s2):
                simplices.append(CechSimplex(sites=(s1, s2)))

    if max_dim < 2:
        return simplices

    # 2-simplices: compatible triples
    for i, s1 in enumerate(sites_list):
        for j, s2 in enumerate(sites_list[i + 1:], start=i + 1):
            for s3 in sites_list[j + 1:]:
                if (_sites_overlap(s1, s2) and _sites_overlap(s2, s3)
                        and _sites_overlap(s1, s3)):
                    simplices.append(CechSimplex(sites=(s1, s2, s3)))

    return simplices


def _sites_overlap(a: TensorObservationSite, b: TensorObservationSite) -> bool:
    """Two sites overlap if they share a tensor position parameter."""
    pos_a = dict(a.params).get("position")
    pos_b = dict(b.params).get("position")
    if pos_a is not None and pos_b is not None and pos_a == pos_b:
        return True
    # Same Triton kernel
    if a.triton_spec is not None and b.triton_spec is not None:
        if a.triton_spec.name == b.triton_spec.name:
            return True
    # Same MLIR module
    if a.mlir_spec is not None and b.mlir_spec is not None:
        if a.mlir_spec.name == b.mlir_spec.name:
            return True
    return False


# ---------------------------------------------------------------------------
# Stratum filtration — the canonical partial order on covers
# ---------------------------------------------------------------------------

def filtration_covers(cover: TensorCover) -> Dict[TensorStratum, TensorCover]:
    """
    Decompose a cover along the stratum filtration.

    Returns {stratum: sub-cover} where each sub-cover contains only
    sites at that stratum level.  This enables the global checker to
    work stratum-by-stratum: first check metadata, then structural,
    then numerical, then behavioral — each stratum being a necessary
    condition for the next.
    """
    result: Dict[TensorStratum, TensorCover] = {}
    for stratum in TensorStratum:
        sites = frozenset(s for s in cover.sites if s.stratum == stratum)
        if sites:
            result[stratum] = TensorCover(
                sites=sites,
                stratum=stratum,
                name=f"{cover.name}@{stratum.name}",
            )
    return result


# ---------------------------------------------------------------------------
# Test input generation (sites → concrete tensors)
# ---------------------------------------------------------------------------

def generate_test_input(spec: TensorSpec, seed: int = 42) -> Any:
    """
    Generate a concrete test tensor from a TensorSpec.

    This is the *stalk* construction: from the site (abstract observation),
    we produce a concrete point in the stalk (actual tensor value).
    """
    try:
        import torch
    except ImportError:
        return None

    gen = torch.Generator()
    gen.manual_seed(seed)

    dtype = getattr(torch, spec.dtype, torch.float32)
    device = spec.device or "cpu"

    if dtype in (torch.float32, torch.float64, torch.float16, torch.bfloat16):
        t = torch.randn(spec.shape, dtype=dtype, device=device, generator=gen)
    elif dtype in (torch.int32, torch.int64, torch.int16, torch.int8):
        t = torch.randint(-100, 100, spec.shape, dtype=dtype, device=device,
                          generator=gen)
    elif dtype == torch.bool:
        t = torch.randint(0, 2, spec.shape, dtype=torch.int8,
                          device=device, generator=gen).bool()
    elif dtype in (torch.complex64, torch.complex128):
        real = torch.randn(spec.shape, dtype=torch.float32, device=device,
                           generator=gen)
        imag = torch.randn(spec.shape, dtype=torch.float32, device=device,
                           generator=gen)
        t = torch.complex(real, imag)
        if dtype == torch.complex128:
            t = t.to(dtype)
    else:
        t = torch.randn(spec.shape, dtype=torch.float32, device=device,
                        generator=gen).to(dtype)

    if spec.requires_grad and t.is_floating_point():
        t = t.requires_grad_(True)

    return t


def generate_test_inputs(specs: Sequence[TensorSpec],
                         seed: int = 42,
                         n_random: int = 1) -> List[List[Any]]:
    """Generate batches of test tensors from specs.

    Returns a list of input batches.  Each batch is a list of tensors,
    one per spec.  When n_random > 1, different seeds produce diverse
    inputs so the checker can probe multiple points in input space.
    """
    batches: List[List[Any]] = []
    for r in range(max(1, n_random)):
        batch = [generate_test_input(spec, seed=seed + r * len(specs) + i)
                 for i, spec in enumerate(specs)]
        batches.append(batch)
    return batches


# ---------------------------------------------------------------------------
# Site category introspection
# ---------------------------------------------------------------------------

def sites_by_kind(category: TensorSiteCategory,
                  site_map: Dict[SiteId, TensorObservationSite],
                  kind: TensorSiteKind) -> List[SiteId]:
    """Filter sites in a category by their TensorSiteKind."""
    return [sid for sid in category.sites
            if sid in site_map and site_map[sid].kind == kind]


def sites_by_stratum(category: TensorSiteCategory,
                     site_map: Dict[SiteId, TensorObservationSite],
                     stratum: TensorStratum) -> List[SiteId]:
    """Filter sites in a category by their stratum."""
    return [sid for sid in category.sites
            if sid in site_map and site_map[sid].stratum == stratum]


def outgoing_morphisms(category: TensorSiteCategory,
                       site_id: SiteId) -> List[TensorSiteMorphism]:
    """Get all morphisms with the given site as source."""
    return category._outgoing.get(site_id, [])
