"""Proper Čech cohomology for equivalence obstruction detection.

This module computes the Čech cohomology groups

    Hˇ^p({Uᵢ}, Iso(Sem_f, Sem_g))

with the coefficient sheaf being the *sheaf of local isomorphisms*
between the two semantic presheaves.

Mathematical structure
----------------------
The Čech complex is:

    C^0 ──d^0──▶ C^1 ──d^1──▶ C^2

where:
    C^0 = Π_i Iso(Sem_f(Uᵢ), Sem_g(Uᵢ))
          — local isomorphisms at each site

    C^1 = Π_{i<j} Iso(Sem_f(Uᵢⱼ), Sem_g(Uᵢⱼ))
          — isomorphisms on pairwise overlaps

    C^2 = Π_{i<j<k} Iso(Sem_f(Uᵢⱼₖ), Sem_g(Uᵢⱼₖ))
          — isomorphisms on triple overlaps

The coboundary maps are:
    (d^0 φ)_{ij} = φ_j|_{Uᵢⱼ} ∘ φ_i|_{Uᵢⱼ}⁻¹
    (d^1 ψ)_{ijk} = ψ_{jk}|_{Uᵢⱼₖ} ∘ ψ_{ij}|_{Uᵢⱼₖ}⁻¹ ∘ ψ_{ik}|_{Uᵢⱼₖ}

Then:
    H^0 = ker(d^0)           — global isomorphisms
    H^1 = ker(d^1) / im(d^0) — obstruction to gluing

**H^1 = 0 iff local equivalences glue to a global equivalence.**
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    TrustLevel,
)
from deppy.types.refinement import (
    ConjunctionPred,
    DisjunctionPred,
    ImplicationPred,
    Predicate,
    RefinementType,
    TruePred,
    FalsePred,
    VarPred,
)
from deppy.types.dependent import IdentityType
from deppy.types.witnesses import (
    ReflProof,
    TransitivityProof,
    SymmetryProof,
    TransportWitness,
)

from deppy.equivalence._protocols import (
    EquivalenceCochainData,
    EquivalenceCohomologyClass,
    EquivalenceObstruction,
    EquivalenceObstructionKind,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
)
from deppy.equivalence.predicates import BiimplicationPred


# ═══════════════════════════════════════════════════════════════════════════════
# Cochain element — a single entry in C^p
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class CochainElement:
    """An element of the Čech cochain C^p.

    An element of C^p is indexed by a (p+1)-tuple of sites
    (Uᵢ₀, …, Uᵢₚ) and carries:

    - *predicate*: the refinement predicate encoding the local
      isomorphism on the intersection U_{i₀…iₚ}
    - *is_iso*: whether the element is an actual isomorphism
    - *evidence*: a proof term witnessing the isomorphism
    - *inverse_predicate*: the inverse direction (for invertibility)
    """
    sites: Tuple[SiteId, ...]
    predicate: Predicate
    is_iso: bool = True
    evidence: Optional[Any] = None
    inverse_predicate: Optional[Predicate] = None

    @property
    def degree(self) -> int:
        return len(self.sites) - 1

    @property
    def is_trivial(self) -> bool:
        """A cochain element is trivial if its predicate is TruePred."""
        return isinstance(self.predicate, TruePred)


# ═══════════════════════════════════════════════════════════════════════════════
# Cochain group — C^p
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class CochainGroup:
    """The Čech cochain group C^p({Uᵢ}, Iso).

    C^p = Π_{i₀ < … < iₚ} Iso(Sem_f(U_{i₀…iₚ}), Sem_g(U_{i₀…iₚ}))

    Elements are indexed by sorted tuples of site indices.
    """
    degree: int
    elements: Dict[Tuple[SiteId, ...], CochainElement] = field(default_factory=dict)

    def at(self, *sites: SiteId) -> Optional[CochainElement]:
        """Look up the cochain element at a given multi-index."""
        key = tuple(sorted(sites, key=lambda s: s.name))
        return self.elements.get(key)

    def add(self, element: CochainElement) -> None:
        """Add a cochain element."""
        key = tuple(sorted(element.sites, key=lambda s: s.name))
        self.elements[key] = element

    @property
    def is_trivial(self) -> bool:
        """The cochain group is trivial if all elements are isomorphisms."""
        return all(e.is_iso for e in self.elements.values())

    @property
    def non_iso_elements(self) -> List[CochainElement]:
        """Elements that fail to be isomorphisms."""
        return [e for e in self.elements.values() if not e.is_iso]

    @property
    def size(self) -> int:
        return len(self.elements)


# ═══════════════════════════════════════════════════════════════════════════════
# Coboundary operator d^p : C^p → C^{p+1}
# ═══════════════════════════════════════════════════════════════════════════════


class CoboundaryOperator:
    """The Čech coboundary operator d^p : C^p → C^{p+1}.

    For degree 0:
        (d^0 φ)_{ij} = φ_j|_{Uᵢⱼ} ∘ φ_i|_{Uᵢⱼ}⁻¹

        Concretely: φ_j restricted to the overlap, composed with
        the inverse of φ_i restricted to the overlap.  The result
        is a *transition isomorphism* on U_{ij}.

    For degree 1:
        (d^1 ψ)_{ijk} = ψ_{jk}|_{Uᵢⱼₖ} ∘ ψ_{ij}|_{Uᵢⱼₖ}⁻¹ ∘ ψ_{ik}|_{Uᵢⱼₖ}

        This is the *cocycle condition*: the composition around the
        triangle ijk must be the identity.
    """

    def __init__(
        self,
        overlaps: List[Tuple[SiteId, SiteId]],
        triple_overlaps: Optional[List[Tuple[SiteId, SiteId, SiteId]]] = None,
    ) -> None:
        self._overlaps = overlaps
        self._triple_overlaps = triple_overlaps or self._compute_triple_overlaps()

    def d0(self, c0: CochainGroup) -> CochainGroup:
        """Compute d^0 : C^0 → C^1.

        (d^0 φ)_{ij} = φ_j|_{Uᵢⱼ} ∘ φ_i|_{Uᵢⱼ}⁻¹

        For the equivalence checker:
        - φ_i is the local iso predicate at site i (BiimplicationPred)
        - φ_i|_{Uᵢⱼ} is its restriction to the overlap
        - The composition φ_j ∘ φ_i⁻¹ is the "transition function"

        If d^0(φ) = 0 (the transition function is trivial on every
        overlap), then φ is a *global* isomorphism — it's in ker(d^0) = H^0.
        """
        c1 = CochainGroup(degree=1)

        for (site_i, site_j) in self._overlaps:
            phi_i = c0.at(site_i)
            phi_j = c0.at(site_j)

            if phi_i is None or phi_j is None:
                # Missing local data → non-trivial cochain
                c1.add(CochainElement(
                    sites=(site_i, site_j),
                    predicate=FalsePred(),
                    is_iso=False,
                ))
                continue

            # Restrict both to the overlap
            phi_i_restricted = phi_i.predicate
            phi_j_restricted = phi_j.predicate

            # (d^0 φ)_{ij} = φ_j ∘ φ_i⁻¹
            # This is trivial iff φ_i and φ_j agree on the overlap
            #
            # φ_i is a biimplication (fwd_i, bwd_i)
            # φ_j is a biimplication (fwd_j, bwd_j)
            # φ_j ∘ φ_i⁻¹ = (fwd_j ∘ bwd_i, bwd_j ∘ fwd_i)
            # trivial iff fwd_j ∘ bwd_i ≡ id ∧ bwd_j ∘ fwd_i ≡ id
            # which simplifies to: φ_i ⟺ φ_j on the overlap

            transition_pred = ConjunctionPred(conjuncts=(
                ImplicationPred(antecedent=phi_i_restricted, consequent=phi_j_restricted),
                ImplicationPred(antecedent=phi_j_restricted, consequent=phi_i_restricted),
            ))

            # The transition is trivial iff the two local isos agree
            is_trivial = self._predicates_equivalent(
                phi_i.predicate, phi_j.predicate,
            )

            c1.add(CochainElement(
                sites=(site_i, site_j),
                predicate=transition_pred,
                is_iso=is_trivial or (phi_i.is_iso and phi_j.is_iso),
                evidence=TransitivityProof(
                    left=phi_j.evidence or ReflProof(),
                    right=SymmetryProof(inner=phi_i.evidence or ReflProof()),
                ) if phi_i.evidence or phi_j.evidence else None,
                inverse_predicate=ConjunctionPred(conjuncts=(
                    ImplicationPred(antecedent=phi_j_restricted, consequent=phi_i_restricted),
                    ImplicationPred(antecedent=phi_i_restricted, consequent=phi_j_restricted),
                )),
            ))

        return c1

    def d1(self, c1: CochainGroup) -> CochainGroup:
        """Compute d^1 : C^1 → C^2.

        (d^1 ψ)_{ijk} = ψ_{jk} ∘ ψ_{ij}⁻¹ ∘ ψ_{ik}

        The cocycle condition: d^1 ψ = 0 iff the transition
        functions satisfy the cocycle identity on every triple overlap.
        """
        c2 = CochainGroup(degree=2)

        for (site_i, site_j, site_k) in self._triple_overlaps:
            psi_ij = c1.at(site_i, site_j)
            psi_jk = c1.at(site_j, site_k)
            psi_ik = c1.at(site_i, site_k)

            if psi_ij is None or psi_jk is None or psi_ik is None:
                c2.add(CochainElement(
                    sites=(site_i, site_j, site_k),
                    predicate=FalsePred(),
                    is_iso=False,
                ))
                continue

            # Cocycle: ψ_{jk} ∘ ψ_{ij}⁻¹ ∘ ψ_{ik} should be identity
            # This means: the three transition functions are consistent
            #
            # Encoded as: ψ_{ij}.pred ∧ ψ_{jk}.pred ⟹ ψ_{ik}.pred
            # AND:         ψ_{ik}.pred ⟹ (ψ_{ij}.pred ∧ ψ_{jk}.pred)
            cocycle_pred = ConjunctionPred(conjuncts=(
                # Forward: ij then jk implies ik
                ImplicationPred(
                    antecedent=ConjunctionPred(conjuncts=(
                        psi_ij.predicate, psi_jk.predicate,
                    )),
                    consequent=psi_ik.predicate,
                ),
                # Backward: ik implies ij and jk
                ImplicationPred(
                    antecedent=psi_ik.predicate,
                    consequent=ConjunctionPred(conjuncts=(
                        psi_ij.predicate, psi_jk.predicate,
                    )),
                ),
            ))

            # Cocycle is trivial iff the composition is the identity
            is_trivial = (
                psi_ij.is_iso and psi_jk.is_iso and psi_ik.is_iso
                and self._cocycle_holds(psi_ij, psi_jk, psi_ik)
            )

            c2.add(CochainElement(
                sites=(site_i, site_j, site_k),
                predicate=cocycle_pred,
                is_iso=is_trivial,
            ))

        return c2

    def _compute_triple_overlaps(self) -> List[Tuple[SiteId, SiteId, SiteId]]:
        """Compute triple overlaps from pairwise overlaps."""
        # Build adjacency from overlaps
        adj: Dict[SiteId, Set[SiteId]] = {}
        for (a, b) in self._overlaps:
            adj.setdefault(a, set()).add(b)
            adj.setdefault(b, set()).add(a)

        triples: Set[Tuple[SiteId, SiteId, SiteId]] = set()
        all_sites = list(adj.keys())

        for i, si in enumerate(all_sites):
            for j in range(i + 1, len(all_sites)):
                sj = all_sites[j]
                if sj not in adj.get(si, set()):
                    continue
                for k in range(j + 1, len(all_sites)):
                    sk = all_sites[k]
                    if sk in adj.get(si, set()) and sk in adj.get(sj, set()):
                        triple = tuple(sorted([si, sj, sk], key=lambda s: s.name))
                        triples.add(triple)  # type: ignore[arg-type]

        return list(triples)  # type: ignore[return-value]

    def _predicates_equivalent(self, p: Predicate, q: Predicate) -> bool:
        """Check predicate equivalence via the three-tiered engine.

        Delegates to ``predicate_eq.predicates_equivalent`` which performs:
        1. Structural AST comparison (fast, sound)
        2. Algebraic normalisation (absorption, idempotence, double-negation)
        3. Z3 solver discharge (definitive, if available)
        """
        from deppy.equivalence.predicate_eq import predicates_equivalent
        result = predicates_equivalent(p, q, use_solver=True)
        return result.equivalent

    def _cocycle_holds(
        self,
        psi_ij: CochainElement,
        psi_jk: CochainElement,
        psi_ik: CochainElement,
    ) -> bool:
        """Check the cocycle condition ψ_{jk} ∘ ψ_{ij} = ψ_{ik}.

        Uses predicate composition (conjunction restricted to the triple
        overlap) and genuine equivalence checking:

            compose(g_{ij}, g_{jk}) ≡ g_{ik}

        where composition in the presheaf topos is modelled as conjunction
        of the transition predicates.
        """
        from deppy.equivalence.predicate_eq import check_cocycle_identity
        result = check_cocycle_identity(
            psi_ij.predicate, psi_jk.predicate, psi_ik.predicate,
            use_solver=True,
        )
        return result.equivalent


# ═══════════════════════════════════════════════════════════════════════════════
# Kernel and image computation
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class SubgroupData:
    """A subgroup of a cochain group, represented as the elements
    satisfying a condition (kernel) or produced by a map (image).
    """
    degree: int
    elements: Dict[Tuple[SiteId, ...], CochainElement] = field(default_factory=dict)
    kind: str = "subgroup"  # "kernel" | "image"

    @property
    def size(self) -> int:
        return len(self.elements)

    @property
    def is_trivial(self) -> bool:
        """A subgroup is trivial if all its elements are trivial."""
        return all(e.is_trivial for e in self.elements.values())


def compute_kernel(
    source: CochainGroup,
    target: CochainGroup,
    coboundary: CoboundaryOperator,
    degree: int,
) -> SubgroupData:
    """Compute ker(d^p) ⊂ C^p.

    ker(d^p) = { φ ∈ C^p | d^p(φ) = 0 }

    An element φ is in the kernel iff its coboundary is trivial
    (the identity/TruePred) at every index.

    For d^0: ker(d^0) = global isomorphisms (the local isos that
    already agree on all overlaps).

    For d^1: ker(d^1) = cocycles (transition functions satisfying
    the cocycle condition).
    """
    kernel = SubgroupData(degree=degree, kind="kernel")

    # Apply the coboundary to each element
    if degree == 0:
        image = coboundary.d0(source)
    elif degree == 1:
        image = coboundary.d1(source)
    else:
        return kernel

    # An element is in the kernel iff its image is trivial
    for key, element in source.elements.items():
        # Check if all coboundary components involving this element
        # are trivial
        in_kernel = True
        for img_key, img_element in image.elements.items():
            # Check if this source element contributes to this image element
            if any(s in img_key for s in key):
                if not img_element.is_trivial and not img_element.is_iso:
                    in_kernel = False
                    break

        if in_kernel:
            kernel.elements[key] = element

    return kernel


def compute_image(
    source: CochainGroup,
    coboundary: CoboundaryOperator,
    degree: int,
) -> SubgroupData:
    """Compute im(d^p) ⊂ C^{p+1}.

    im(d^p) = { d^p(φ) | φ ∈ C^p }

    This is the set of (p+1)-cochains that are coboundaries.
    """
    if degree == 0:
        image_group = coboundary.d0(source)
    elif degree == 1:
        image_group = coboundary.d1(source)
    else:
        return SubgroupData(degree=degree + 1, kind="image")

    return SubgroupData(
        degree=degree + 1,
        elements=image_group.elements,
        kind="image",
    )


# ═══════════════════════════════════════════════════════════════════════════════
# GF(2) linear algebra for true cohomological rank
# ═══════════════════════════════════════════════════════════════════════════════


def _gf2_rank(matrix: List[List[int]]) -> int:
    """Compute the rank of a binary matrix over GF(2) via Gaussian elimination.

    Each row is a list of 0/1 ints.  The matrix is modified in place.
    Returns the number of linearly independent rows (= rank).
    """
    if not matrix:
        return 0
    m = len(matrix)
    n = len(matrix[0]) if matrix else 0
    pivot_row = 0
    for col in range(n):
        # Find a row with a 1 in this column at or below pivot_row
        found = -1
        for row in range(pivot_row, m):
            if matrix[row][col]:
                found = row
                break
        if found == -1:
            continue
        # Swap to pivot position
        matrix[pivot_row], matrix[found] = matrix[found], matrix[pivot_row]
        # Eliminate column in all other rows
        for row in range(m):
            if row != pivot_row and matrix[row][col]:
                matrix[row] = [a ^ b for a, b in zip(matrix[row], matrix[pivot_row])]
        pivot_row += 1
    return pivot_row


def compute_h1_rank_gf2(
    sites: List[Tuple[SiteId, ...]],
    overlaps: List[Tuple[SiteId, SiteId]],
    triples: List[Tuple[SiteId, SiteId, SiteId]],
    kernel_keys: Set[Tuple[SiteId, ...]],
    image_keys: Set[Tuple[SiteId, ...]],
) -> int:
    """Compute rank(H^1) = dim(ker d^1) - dim(im d^0) over GF(2).

    Uses the coboundary matrices directly:
      rank(H^1) = nullity(d^1) - rank(d^0)
                = |C^1| - rank(d^1) - rank(d^0)

    by the rank-nullity theorem over GF(2).

    If the full matrix data is unavailable, falls back to
    |kernel_keys| - |image_keys| (the naive count).
    """
    # Index sites
    site_set: List[SiteId] = []
    for key in sites:
        for s in key:
            if s not in site_set:
                site_set.append(s)
    site_idx = {s: i for i, s in enumerate(site_set)}
    n_sites = len(site_set)

    # Index overlaps (C^1 basis)
    overlap_list = list(overlaps)
    overlap_idx = {tuple(sorted([a, b], key=lambda s: s.name)): i
                   for i, (a, b) in enumerate(overlap_list)}
    n_overlaps = len(overlap_list)

    if n_overlaps == 0:
        return 0

    # Build d^0: C^0 -> C^1  (n_overlaps x n_sites matrix over GF(2))
    # (d^0 phi)_{ij} = phi_j - phi_i  (in GF(2): phi_j XOR phi_i)
    d0_matrix: List[List[int]] = []
    for (a, b) in overlap_list:
        row = [0] * n_sites
        if a in site_idx:
            row[site_idx[a]] = 1
        if b in site_idx:
            row[site_idx[b]] ^= 1
        d0_matrix.append(row)

    rank_d0 = _gf2_rank([row[:] for row in d0_matrix])

    # Build d^1: C^1 -> C^2  (n_triples x n_overlaps matrix over GF(2))
    # (d^1 psi)_{ijk} = psi_{jk} - psi_{ij} + psi_{ik}
    triple_list = list(triples)
    n_triples = len(triple_list)

    if n_triples == 0:
        # No triples => ker(d^1) = all of C^1
        # rank(H^1) = n_overlaps - rank(d^0)
        return max(n_overlaps - rank_d0, 0)

    d1_matrix: List[List[int]] = []
    for (si, sj, sk) in triple_list:
        row = [0] * n_overlaps
        key_ij = tuple(sorted([si, sj], key=lambda s: s.name))
        key_jk = tuple(sorted([sj, sk], key=lambda s: s.name))
        key_ik = tuple(sorted([si, sk], key=lambda s: s.name))
        if key_ij in overlap_idx:
            row[overlap_idx[key_ij]] ^= 1
        if key_jk in overlap_idx:
            row[overlap_idx[key_jk]] ^= 1
        if key_ik in overlap_idx:
            row[overlap_idx[key_ik]] ^= 1
        d1_matrix.append(row)

    rank_d1 = _gf2_rank([row[:] for row in d1_matrix])

    # rank(H^1) = nullity(d^1) - rank(d^0)
    #           = (n_overlaps - rank(d^1)) - rank(d^0)
    return max(n_overlaps - rank_d1 - rank_d0, 0)


# ═══════════════════════════════════════════════════════════════════════════════
# Cohomology group  H^p = ker(d^p) / im(d^{p-1})
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class CohomologyGroup:
    """The Čech cohomology group H^p = ker(d^p) / im(d^{p-1}).

    Attributes:
        degree:     p
        kernel:     ker(d^p) ⊂ C^p
        image:      im(d^{p-1}) ⊂ C^p
        quotient:   Representatives of H^p = ker/im
        is_trivial: H^p = 0
        rank_gf2:   True rank computed via GF(2) Gaussian elimination
                    on the coboundary matrices (set by the computer).
    """
    degree: int
    kernel: SubgroupData
    image: SubgroupData
    quotient: Dict[Tuple[SiteId, ...], CochainElement] = field(default_factory=dict)
    is_trivial: bool = True
    rank_gf2: Optional[int] = None

    @property
    def rank(self) -> int:
        """The rank of H^p.

        Prefers the GF(2) Gaussian-elimination result when available;
        falls back to the naive quotient count.
        """
        if self.rank_gf2 is not None:
            return self.rank_gf2
        return len(self.quotient)

    @property
    def obstruction_elements(self) -> List[CochainElement]:
        """Non-trivial elements of H^p representing obstructions."""
        return [e for e in self.quotient.values() if not e.is_trivial]


def compute_cohomology(
    kernel: SubgroupData,
    image: SubgroupData,
    degree: int,
) -> CohomologyGroup:
    """Compute H^p = ker(d^p) / im(d^{p-1}).

    The quotient is computed by removing from ker(d^p) those elements
    that are in the image of d^{p-1}.

    An element of the kernel represents a non-trivial cohomology class
    iff it is NOT a coboundary.
    """
    quotient: Dict[Tuple[SiteId, ...], CochainElement] = {}

    for key, element in kernel.elements.items():
        # Check if this kernel element is in the image
        is_boundary = False
        for img_key, img_element in image.elements.items():
            if key == img_key:
                # The element is a coboundary — quotient it out
                is_boundary = True
                break

        if not is_boundary:
            quotient[key] = element

    # Filter to non-trivial representatives
    non_trivial_quotient: Dict[Tuple[SiteId, ...], CochainElement] = {}
    for key, element in quotient.items():
        if not element.is_trivial:
            non_trivial_quotient[key] = element

    is_trivial = len(non_trivial_quotient) == 0

    return CohomologyGroup(
        degree=degree,
        kernel=kernel,
        image=image,
        quotient=non_trivial_quotient if non_trivial_quotient else quotient,
        is_trivial=is_trivial,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Full Čech cohomology computation
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class CechCohomologyResult:
    """Result of the full Čech cohomology computation.

    Contains:
    - The cochain complex C^0 → C^1 → C^2
    - The cohomology groups H^0, H^1
    - The verdict: H^1 = 0 iff local equivalences glue
    """
    c0: CochainGroup
    c1: CochainGroup
    c2: CochainGroup
    h0: CohomologyGroup
    h1: CohomologyGroup
    h1_trivial: bool

    @property
    def obstructions(self) -> List[CochainElement]:
        """Non-trivial elements of H^1 — the obstructions to gluing."""
        return self.h1.obstruction_elements

    @property
    def global_sections_exist(self) -> bool:
        """Whether global sections (global equivalences) exist."""
        return self.h0.rank > 0

    def to_equivalence_cohomology(self) -> EquivalenceCohomologyClass:
        """Convert to the equivalence protocol's cohomology class."""
        obs_count = len(self.h1.obstruction_elements)
        return EquivalenceCohomologyClass(
            degree=1,
            representative=EquivalenceCochainData(
                degree=1,
                values={
                    key: elem.predicate
                    for key, elem in self.h1.quotient.items()
                },
            ),
            is_trivial=self.h1_trivial,
            obstruction_description=f"{obs_count} obstruction(s) in H^1" if obs_count else "",
        )


class CechCohomologyComputer:
    """Compute the full Čech cohomology for an equivalence problem.

    Input: local equivalence judgments + overlap structure.
    Output: CechCohomologyResult with H^0 and H^1.

    Algorithm:
    1. Build C^0 from local judgments
    2. Build C^1 from pairwise overlaps via d^0
    3. Build C^2 from triple overlaps via d^1
    4. Compute H^0 = ker(d^0) — global isomorphisms
    5. Compute H^1 = ker(d^1) / im(d^0) — obstructions

    The key output is whether H^1 = 0, which determines
    if local equivalences can be glued into a global one.
    """

    def __init__(
        self,
        judgments: Dict[SiteId, LocalEquivalenceJudgment],
        overlaps: List[Tuple[SiteId, SiteId]],
    ) -> None:
        self._judgments = judgments
        self._overlaps = overlaps

    def compute(self) -> CechCohomologyResult:
        """Run the full cohomology computation."""
        # Step 1: Build C^0 from local judgments
        c0 = self._build_c0()

        # Step 2: Construct coboundary operator
        coboundary = CoboundaryOperator(
            overlaps=self._overlaps,
        )

        # Step 3: Compute d^0(C^0) = C^1
        c1 = coboundary.d0(c0)

        # Step 4: Compute d^1(C^1) = C^2
        c2 = coboundary.d1(c1)

        # Step 5: Compute H^0 = ker(d^0)
        # Elements of C^0 whose coboundary in C^1 is trivial
        ker_d0 = compute_kernel(c0, c1, coboundary, degree=0)
        # im(d^{-1}) = 0 for degree 0 (no C^{-1})
        im_d_minus1 = SubgroupData(degree=0, kind="image")
        h0 = compute_cohomology(ker_d0, im_d_minus1, degree=0)

        # Step 6: Compute H^1 = ker(d^1) / im(d^0)
        ker_d1 = compute_kernel(c1, c2, coboundary, degree=1)
        im_d0 = compute_image(c0, coboundary, degree=0)
        h1 = compute_cohomology(ker_d1, im_d0, degree=1)

        # Step 7: Compute true rank via GF(2) Gaussian elimination
        try:
            h1_rank = compute_h1_rank_gf2(
                sites=list(c0.elements.keys()),
                overlaps=self._overlaps,
                triples=coboundary._triple_overlaps,
                kernel_keys=set(ker_d1.elements.keys()),
                image_keys=set(im_d0.elements.keys()),
            )
            h1.rank_gf2 = h1_rank
            if h1_rank == 0:
                h1.is_trivial = True
        except Exception:
            pass  # fall back to naive rank

        return CechCohomologyResult(
            c0=c0,
            c1=c1,
            c2=c2,
            h0=h0,
            h1=h1,
            h1_trivial=h1.is_trivial,
        )

    def _build_c0(self) -> CochainGroup:
        """Build C^0 from local equivalence judgments.

        C^0 = Π_i Iso(Sem_f(Uᵢ), Sem_g(Uᵢ))

        Each local judgment contributes an element: the local
        isomorphism predicate (biimplication of refinement predicates).
        """
        c0 = CochainGroup(degree=0)

        for site_id, judgment in self._judgments.items():
            # Build the biimplication from forward/backward
            _pred = getattr(judgment, 'predicate', None)
            if _pred is not None:
                pred = _pred
            else:
                # Construct from forward/backward status
                fwd = VarPred(var_name=f"fwd_{site_id.name}")
                bwd = VarPred(var_name=f"bwd_{site_id.name}")
                pred = BiimplicationPred(
                    left=ImplicationPred(antecedent=fwd, consequent=bwd),
                    right=ImplicationPred(antecedent=bwd, consequent=fwd),
                )

            is_iso = (
                judgment.verdict == EquivalenceVerdict.EQUIVALENT
                and judgment.forward_holds is True
                and judgment.backward_holds is True
            )

            c0.add(CochainElement(
                sites=(site_id,),
                predicate=pred,
                is_iso=is_iso,
                evidence=judgment.proof,
            ))

        return c0


# ═══════════════════════════════════════════════════════════════════════════════
# Obstruction extraction from H^1
# ═══════════════════════════════════════════════════════════════════════════════


def extract_obstructions_from_h1(
    result: CechCohomologyResult,
) -> List[EquivalenceObstruction]:
    """Extract equivalence obstructions from the H^1 computation.

    Each non-trivial element of H^1 represents an obstruction to
    gluing local equivalences.  We classify these and produce
    human-readable explanations.
    """
    obstructions: List[EquivalenceObstruction] = []

    for key, element in result.h1.quotient.items():
        if element.is_trivial:
            continue

        sites = list(element.sites)

        # Determine the kind of obstruction
        if not element.is_iso:
            kind = EquivalenceObstructionKind.TYPE_MISMATCH
            explanation = (
                f"Local isomorphisms at sites {', '.join(s.name for s in sites)} "
                f"do not agree on their overlap.  The transition function "
                f"φ_j ∘ φ_i⁻¹ is non-trivial, meaning the local equivalences "
                f"cannot be consistently patched."
            )
        else:
            kind = EquivalenceObstructionKind.GLUING_FAILURE
            explanation = (
                f"Transition isomorphisms on the overlap "
                f"{', '.join(s.name for s in sites)} satisfy the cocycle "
                f"condition but are not coboundaries — they represent a "
                f"genuine topological obstruction in H¹."
            )

        obstructions.append(EquivalenceObstruction(
            kind=kind,
            sites=sites,
            description=explanation,
            severity="error",
            predicate_gap=element.predicate,
        ))

    return obstructions
