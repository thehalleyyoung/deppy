"""
Formalizes intellectual domains as sites (categories with Grothendieck topology).

A "site" in mathematics is a category equipped with a Grothendieck topology —
a systematic way of saying when a collection of morphisms "covers" an object.
Here we model intellectual domains the same way:

  Objects   = Concepts (sheaf, type, model, functor, …)
  Morphisms = Relationships (IMPLIES, GENERALIZES, SPECIALIZES, …)
  Topology  = Covering families that explain when a set of concepts
              "decomposes" or "explains" another concept

This is the foundation for treating interdisciplinary ideation as a typing
problem: analogies become functors between sites, and valid cross-domain
transfers must respect the topology (i.e., preserve covering structure).
"""

from __future__ import annotations

import copy
from collections import deque
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Dict, List, Optional, Set

if TYPE_CHECKING:
    pass

# ---------------------------------------------------------------------------
# Valid morphism relation types
# ---------------------------------------------------------------------------

VALID_RELATIONS: frozenset[str] = frozenset(
    {
        "IMPLIES",
        "GENERALIZES",
        "SPECIALIZES",
        "USES",
        "PART_OF",
        "DUAL_TO",
    }
)

# =========================================================================
# 1. Concept
# =========================================================================


@dataclass
class Concept:
    """A single concept living inside an intellectual domain."""

    id: str
    domain: str
    name: str
    definition: str
    formal_type: Optional[str] = None
    keywords: List[str] = field(default_factory=list)
    related: List[str] = field(default_factory=list)

    # -- serialization -----------------------------------------------------

    def to_dict(self) -> Dict:
        return {
            "id": self.id,
            "domain": self.domain,
            "name": self.name,
            "definition": self.definition,
            "formal_type": self.formal_type,
            "keywords": list(self.keywords),
            "related": list(self.related),
        }

    @classmethod
    def from_dict(cls, data: Dict) -> Concept:
        return cls(
            id=data["id"],
            domain=data["domain"],
            name=data["name"],
            definition=data["definition"],
            formal_type=data.get("formal_type"),
            keywords=data.get("keywords", []),
            related=data.get("related", []),
        )

    def __repr__(self) -> str:
        return f"Concept({self.id!r}, {self.name!r})"


# =========================================================================
# 2. Morphism
# =========================================================================


@dataclass
class Morphism:
    """A directed relationship between two concepts."""

    source: str
    target: str
    relation: str
    description: str
    strength: float = 1.0

    def __post_init__(self) -> None:
        self._validate()

    def _validate(self) -> None:
        if self.relation not in VALID_RELATIONS:
            raise ValueError(
                f"Invalid relation {self.relation!r}. "
                f"Must be one of {sorted(VALID_RELATIONS)}."
            )
        if not 0.0 <= self.strength <= 1.0:
            raise ValueError(
                f"Strength must be in [0, 1], got {self.strength}."
            )

    # -- serialization -----------------------------------------------------

    def to_dict(self) -> Dict:
        return {
            "source": self.source,
            "target": self.target,
            "relation": self.relation,
            "description": self.description,
            "strength": self.strength,
        }

    @classmethod
    def from_dict(cls, data: Dict) -> Morphism:
        return cls(
            source=data["source"],
            target=data["target"],
            relation=data["relation"],
            description=data["description"],
            strength=data.get("strength", 1.0),
        )

    def __repr__(self) -> str:
        return (
            f"Morphism({self.source!r} --[{self.relation}]--> "
            f"{self.target!r})"
        )


# =========================================================================
# 3. CoveringFamily
# =========================================================================


@dataclass
class CoveringFamily:
    """
    A covering family in the Grothendieck topology of a domain site.

    The *covering* concepts collectively "explain" or "decompose" the
    *covered* concept — analogous to an open cover in topology.
    """

    covered: str
    covering: List[str] = field(default_factory=list)
    explanation: str = ""

    # -- serialization -----------------------------------------------------

    def to_dict(self) -> Dict:
        return {
            "covered": self.covered,
            "covering": list(self.covering),
            "explanation": self.explanation,
        }

    @classmethod
    def from_dict(cls, data: Dict) -> CoveringFamily:
        return cls(
            covered=data["covered"],
            covering=data.get("covering", []),
            explanation=data.get("explanation", ""),
        )

    def __repr__(self) -> str:
        ids = ", ".join(self.covering)
        return f"CoveringFamily({{{ids}}} ⊳ {self.covered})"


# =========================================================================
# 4. DomainSite
# =========================================================================


class DomainSite:
    """
    A site representing an intellectual domain.

    Objects   = concepts
    Morphisms = relationships between concepts
    Topology  = covering families (explanatory decompositions)
    """

    def __init__(self, name: str) -> None:
        self.name: str = name
        self.concepts: Dict[str, Concept] = {}
        self.morphisms: List[Morphism] = []
        self.covering_families: List[CoveringFamily] = []

    # -- mutators ----------------------------------------------------------

    def add_concept(self, concept: Concept) -> None:
        if concept.id in self.concepts:
            raise ValueError(
                f"Duplicate concept ID {concept.id!r} in site {self.name!r}."
            )
        self.concepts[concept.id] = concept

    def add_morphism(self, morphism: Morphism) -> None:
        if morphism.source not in self.concepts:
            raise ValueError(
                f"Source concept {morphism.source!r} not in site "
                f"{self.name!r}."
            )
        if morphism.target not in self.concepts:
            raise ValueError(
                f"Target concept {morphism.target!r} not in site "
                f"{self.name!r}."
            )
        self.morphisms.append(morphism)

    def add_covering(self, family: CoveringFamily) -> None:
        if family.covered not in self.concepts:
            raise ValueError(
                f"Covered concept {family.covered!r} not in site "
                f"{self.name!r}."
            )
        for cid in family.covering:
            if cid not in self.concepts:
                raise ValueError(
                    f"Covering concept {cid!r} not in site {self.name!r}."
                )
        self.covering_families.append(family)

    # -- queries -----------------------------------------------------------

    def objects(self) -> List[str]:
        """Return all concept IDs."""
        return list(self.concepts.keys())

    def morphisms_from(self, concept_id: str) -> List[Morphism]:
        """Morphisms originating from *concept_id*."""
        return [m for m in self.morphisms if m.source == concept_id]

    def morphisms_to(self, concept_id: str) -> List[Morphism]:
        """Morphisms targeting *concept_id*."""
        return [m for m in self.morphisms if m.target == concept_id]

    def covers_for(self, concept_id: str) -> List[CoveringFamily]:
        """Covering families for *concept_id*."""
        return [
            cf for cf in self.covering_families if cf.covered == concept_id
        ]

    def is_covered(self, concept_id: str) -> bool:
        """Whether *concept_id* has at least one covering family."""
        return any(cf.covered == concept_id for cf in self.covering_families)

    def uncovered_concepts(self) -> List[str]:
        """Concepts with no covering family."""
        covered_ids: Set[str] = {
            cf.covered for cf in self.covering_families
        }
        return [cid for cid in self.concepts if cid not in covered_ids]

    def neighbors(self, concept_id: str) -> List[str]:
        """Concepts connected to *concept_id* by any morphism."""
        nbrs: Set[str] = set()
        for m in self.morphisms:
            if m.source == concept_id:
                nbrs.add(m.target)
            elif m.target == concept_id:
                nbrs.add(m.source)
        return sorted(nbrs)

    def path_exists(self, start: str, end: str) -> bool:
        """BFS reachability check (treats morphisms as undirected)."""
        if start not in self.concepts or end not in self.concepts:
            return False
        if start == end:
            return True
        visited: Set[str] = {start}
        queue: deque[str] = deque([start])
        while queue:
            current = queue.popleft()
            for nbr in self.neighbors(current):
                if nbr == end:
                    return True
                if nbr not in visited:
                    visited.add(nbr)
                    queue.append(nbr)
        return False

    def connected_components(self) -> List[List[str]]:
        """Connected components via BFS (undirected view)."""
        visited: Set[str] = set()
        components: List[List[str]] = []
        for cid in self.concepts:
            if cid in visited:
                continue
            component: List[str] = []
            queue: deque[str] = deque([cid])
            visited.add(cid)
            while queue:
                current = queue.popleft()
                component.append(current)
                for nbr in self.neighbors(current):
                    if nbr not in visited:
                        visited.add(nbr)
                        queue.append(nbr)
            components.append(sorted(component))
        return components

    def subsite(self, concept_ids: List[str]) -> DomainSite:
        """Restrict to given concept IDs and their internal morphisms/covers."""
        ids = set(concept_ids)
        sub = DomainSite(f"{self.name}_sub")
        for cid in concept_ids:
            if cid in self.concepts:
                sub.concepts[cid] = copy.deepcopy(self.concepts[cid])
        for m in self.morphisms:
            if m.source in ids and m.target in ids:
                sub.morphisms.append(copy.deepcopy(m))
        for cf in self.covering_families:
            if cf.covered in ids and all(c in ids for c in cf.covering):
                sub.covering_families.append(copy.deepcopy(cf))
        return sub

    def overlap(self, other: DomainSite) -> DomainSite:
        """Intersection of two domain sites by concept ID."""
        shared_ids = set(self.concepts.keys()) & set(other.concepts.keys())
        if not shared_ids:
            return DomainSite(f"{self.name}_∩_{other.name}")
        return self.subsite(sorted(shared_ids))

    # -- serialization -----------------------------------------------------

    def to_dict(self) -> Dict:
        return {
            "name": self.name,
            "concepts": {
                cid: c.to_dict() for cid, c in self.concepts.items()
            },
            "morphisms": [m.to_dict() for m in self.morphisms],
            "covering_families": [
                cf.to_dict() for cf in self.covering_families
            ],
        }

    @classmethod
    def from_dict(cls, data: Dict) -> DomainSite:
        site = cls(data["name"])
        for cid, cdata in data.get("concepts", {}).items():
            site.concepts[cid] = Concept.from_dict(cdata)
        for mdata in data.get("morphisms", []):
            site.morphisms.append(Morphism.from_dict(mdata))
        for cfdata in data.get("covering_families", []):
            site.covering_families.append(CoveringFamily.from_dict(cfdata))
        return site

    # -- visualization -----------------------------------------------------

    def to_dot(self) -> str:
        """Produce a GraphViz DOT string."""
        lines = [f'digraph "{self.name}" {{', "  rankdir=LR;"]
        for cid, c in self.concepts.items():
            label = c.name.replace('"', '\\"')
            lines.append(f'  "{cid}" [label="{label}"];')
        for m in self.morphisms:
            lbl = m.relation
            lines.append(
                f'  "{m.source}" -> "{m.target}" [label="{lbl}"];'
            )
        lines.append("}")
        return "\n".join(lines)

    # -- dunder ------------------------------------------------------------

    def __repr__(self) -> str:
        return (
            f"DomainSite({self.name!r}, concepts={len(self.concepts)}, "
            f"morphisms={len(self.morphisms)}, "
            f"covers={len(self.covering_families)})"
        )

    def __len__(self) -> int:
        return len(self.concepts)


# #########################################################################
# 5. Pre-built Domain Sites
# #########################################################################

# -------------------------------------------------------------------------
# Helper: shorthand concept builder
# -------------------------------------------------------------------------


def _c(
    domain: str,
    prefix: str,
    name: str,
    definition: str,
    *,
    formal_type: Optional[str] = None,
    keywords: Optional[List[str]] = None,
    related: Optional[List[str]] = None,
) -> Concept:
    cid = f"{prefix}.{name}"
    return Concept(
        id=cid,
        domain=domain,
        name=name,
        definition=definition,
        formal_type=formal_type,
        keywords=keywords or [],
        related=related or [],
    )


def _m(
    prefix: str,
    src: str,
    tgt: str,
    rel: str,
    desc: str,
    strength: float = 0.8,
) -> Morphism:
    return Morphism(
        source=f"{prefix}.{src}",
        target=f"{prefix}.{tgt}",
        relation=rel,
        description=desc,
        strength=strength,
    )


def _cf(
    prefix: str,
    covered: str,
    covering: List[str],
    explanation: str,
) -> CoveringFamily:
    return CoveringFamily(
        covered=f"{prefix}.{covered}",
        covering=[f"{prefix}.{c}" for c in covering],
        explanation=explanation,
    )


# =========================================================================
# 5.1 Algebraic Geometry
# =========================================================================


def _build_algebraic_geometry() -> DomainSite:
    D = "algebraic_geometry"
    P = "alg_geom"
    site = DomainSite(D)

    concepts = [
        _c(D, P, "sheaf",
           "A presheaf satisfying the gluing axiom: compatible local sections paste to a unique global section.",
           formal_type="Sheaf C J", keywords=["sheaf", "local-to-global"]),
        _c(D, P, "presheaf",
           "A contravariant functor from an open-set category (or site) to a target category, assigning data to each open.",
           formal_type="Cᵒᵖ ⥤ D", keywords=["presheaf", "functor"]),
        _c(D, P, "cohomology",
           "Derived-functor invariants measuring obstructions to solving global problems from local data.",
           keywords=["cohomology", "derived functor"]),
        _c(D, P, "site",
           "A category equipped with a Grothendieck topology specifying which families of morphisms are covers.",
           keywords=["site", "topology", "category"]),
        _c(D, P, "grothendieck_topology",
           "A collection of covering sieves on each object satisfying base-change, locality, and transitivity axioms.",
           keywords=["topology", "sieve"]),
        _c(D, P, "covering_family",
           "A collection of morphisms into an object that jointly surject in the sense of the chosen topology.",
           keywords=["cover", "family"]),
        _c(D, P, "section",
           "An element of the value of a sheaf on an open set; a local datum.",
           keywords=["section", "local"]),
        _c(D, P, "restriction",
           "The map induced by an inclusion of opens, pulling sections back from a larger open to a smaller one.",
           keywords=["restriction", "pullback"]),
        _c(D, P, "gluing",
           "The sheaf axiom: if local sections agree on overlaps they paste to a unique global section.",
           keywords=["gluing", "patching"]),
        _c(D, P, "descent",
           "The higher-categorical generalisation of gluing, allowing reconstruction of objects from local data and cocycle conditions.",
           keywords=["descent", "cocycle"]),
        _c(D, P, "cech_complex",
           "A cochain complex built from a cover whose cohomology approximates sheaf cohomology.",
           keywords=["Cech", "complex", "cochain"]),
        _c(D, P, "obstruction",
           "A cohomology class whose vanishing is necessary and sufficient for a local-to-global extension to exist.",
           keywords=["obstruction", "extension"]),
        _c(D, P, "H0",
           "The zeroth cohomology group, isomorphic to the space of global sections of a sheaf.",
           keywords=["H0", "global sections"]),
        _c(D, P, "H1",
           "The first cohomology group, classifying torsors / principal bundles and measuring failure of surjectivity of global sections.",
           keywords=["H1", "torsor"]),
        _c(D, P, "H2",
           "The second cohomology group, classifying gerbes and obstructions to lifting problems.",
           keywords=["H2", "gerbe"]),
        _c(D, P, "fiber",
           "The inverse image of a point under a morphism of schemes or the stalk of a sheaf at a geometric point.",
           keywords=["fiber", "inverse image"]),
        _c(D, P, "stalk",
           "The colimit of a presheaf over all open neighbourhoods of a point; the germ of local data.",
           keywords=["stalk", "germ"]),
        _c(D, P, "etale",
           "A morphism that is flat, unramified, and locally of finite presentation — the algebraic analogue of a local isomorphism.",
           keywords=["etale", "flat", "unramified"]),
        _c(D, P, "base_change",
           "Pullback of a morphism along another morphism, fundamental for studying fibers and descent.",
           keywords=["base change", "pullback"]),
        _c(D, P, "pullback",
           "The fiber product in a category; used to change base or restrict families of objects.",
           keywords=["pullback", "fiber product"]),
        _c(D, P, "pushforward",
           "The direct image functor sending a sheaf on the source to a sheaf on the target of a morphism.",
           keywords=["pushforward", "direct image"]),
        _c(D, P, "exact_sequence",
           "A sequence of morphisms where the image of each equals the kernel of the next, capturing algebraic relations.",
           keywords=["exact", "kernel", "image"]),
        _c(D, P, "long_exact_sequence",
           "An exact sequence extending across cohomological degrees, arising from a short exact sequence of sheaves.",
           keywords=["long exact", "connecting homomorphism"]),
        _c(D, P, "mayer_vietoris",
           "A long exact sequence relating cohomology of a space to that of two overlapping open subsets.",
           keywords=["Mayer-Vietoris", "overlap"]),
        _c(D, P, "spectral_sequence",
           "An iterated homological algebra tool converging to the cohomology of a complex, refining filtration data page by page.",
           keywords=["spectral sequence", "filtration"]),
    ]
    for c in concepts:
        site.add_concept(c)

    morphisms = [
        _m(P, "presheaf", "sheaf", "GENERALIZES",
           "Every sheaf is a presheaf satisfying the gluing axiom."),
        _m(P, "sheaf", "gluing", "USES",
           "The sheaf condition is exactly the gluing axiom."),
        _m(P, "sheaf", "section", "USES",
           "Sheaves assign sections to opens."),
        _m(P, "sheaf", "restriction", "USES",
           "Sheaves use restriction maps between opens."),
        _m(P, "section", "restriction", "USES",
           "Sections are related by restriction along inclusions."),
        _m(P, "gluing", "descent", "SPECIALIZES",
           "Gluing is the 1-categorical special case of descent."),
        _m(P, "cohomology", "cech_complex", "USES",
           "Cech cohomology is computed from the Cech complex."),
        _m(P, "cohomology", "obstruction", "IMPLIES",
           "Non-vanishing cohomology classes give obstructions."),
        _m(P, "H0", "cohomology", "PART_OF",
           "H0 is the zeroth cohomology group."),
        _m(P, "H1", "cohomology", "PART_OF",
           "H1 is the first cohomology group."),
        _m(P, "H2", "cohomology", "PART_OF",
           "H2 is the second cohomology group."),
        _m(P, "H0", "section", "IMPLIES",
           "H0 is the space of global sections."),
        _m(P, "stalk", "fiber", "SPECIALIZES",
           "The stalk at a point is a special case of a fiber."),
        _m(P, "stalk", "section", "USES",
           "A stalk is a colimit of sections over neighborhoods."),
        _m(P, "site", "grothendieck_topology", "USES",
           "A site is a category equipped with a Grothendieck topology."),
        _m(P, "grothendieck_topology", "covering_family", "USES",
           "A Grothendieck topology is defined by its covering families."),
        _m(P, "etale", "site", "USES",
           "The etale topology defines a site on schemes.", 0.9),
        _m(P, "base_change", "pullback", "SPECIALIZES",
           "Base change is pullback along a morphism of bases."),
        _m(P, "pullback", "pushforward", "DUAL_TO",
           "Pullback and pushforward are adjoint operations."),
        _m(P, "exact_sequence", "long_exact_sequence", "SPECIALIZES",
           "A long exact sequence extends an exact sequence across degrees.", 0.9),
        _m(P, "long_exact_sequence", "cohomology", "USES",
           "Long exact sequences arise from short exact sequences of sheaves."),
        _m(P, "mayer_vietoris", "long_exact_sequence", "SPECIALIZES",
           "Mayer-Vietoris is a specific long exact sequence for open covers."),
        _m(P, "spectral_sequence", "cohomology", "USES",
           "Spectral sequences converge to cohomology groups."),
        _m(P, "spectral_sequence", "exact_sequence", "GENERALIZES",
           "Spectral sequences generalise long exact sequences."),
        _m(P, "descent", "covering_family", "USES",
           "Descent data is defined relative to a covering family."),
        _m(P, "cech_complex", "covering_family", "USES",
           "The Cech complex is built from a covering family."),
        _m(P, "obstruction", "H2", "USES",
           "Many obstructions live in H2.", 0.7),
        _m(P, "presheaf", "stalk", "USES",
           "Stalks are defined for presheaves as colimits over neighborhoods."),
        _m(P, "sheaf", "presheaf", "SPECIALIZES",
           "A sheaf is a presheaf satisfying the gluing axiom.", 1.0),
        _m(P, "covering_family", "gluing", "IMPLIES",
           "Covering families determine when gluing is possible.", 0.8),
    ]
    for m in morphisms:
        site.add_morphism(m)

    covers = [
        _cf(P, "sheaf", ["section", "restriction", "gluing"],
            "A sheaf is determined by its sections, restriction maps, and the gluing axiom."),
        _cf(P, "cohomology", ["H0", "H1", "H2", "long_exact_sequence"],
            "Cohomology is understood through its individual groups and connecting exact sequences."),
        _cf(P, "site", ["grothendieck_topology", "covering_family"],
            "A site is a category plus a Grothendieck topology given by covering families."),
        _cf(P, "descent", ["gluing", "covering_family", "base_change"],
            "Descent combines gluing data, covering families, and base-change compatibility."),
        _cf(P, "cech_complex", ["covering_family", "section", "restriction"],
            "The Cech complex is assembled from sections over a cover with restriction maps."),
        _cf(P, "obstruction", ["cohomology", "H1", "H2"],
            "Obstructions are cohomological: they live in H1 or H2."),
        _cf(P, "stalk", ["presheaf", "section"],
            "The stalk is a colimit of sections of a presheaf."),
        _cf(P, "long_exact_sequence", ["exact_sequence", "cohomology"],
            "A long exact sequence extends a short exact sequence through cohomological degrees."),
        _cf(P, "mayer_vietoris", ["long_exact_sequence", "covering_family", "cohomology"],
            "Mayer-Vietoris relates cohomology via a covering and a long exact sequence."),
        _cf(P, "spectral_sequence", ["exact_sequence", "cohomology", "H0", "H1"],
            "A spectral sequence is an iterated system of exact sequences converging to cohomology."),
        _cf(P, "presheaf", ["section", "restriction"],
            "A presheaf assigns sections to opens with compatible restriction maps."),
        _cf(P, "pullback", ["base_change", "fiber"],
            "A pullback is base change; it computes fibers over points."),
    ]
    for cf in covers:
        site.add_covering(cf)

    return site


# =========================================================================
# 5.2 Type Theory
# =========================================================================


def _build_type_theory() -> DomainSite:
    D = "type_theory"
    P = "tt"
    site = DomainSite(D)

    concepts = [
        _c(D, P, "type",
           "A classifier for terms: a type describes a collection of values and the operations allowed on them.",
           formal_type="Type u", keywords=["type", "sort"]),
        _c(D, P, "term",
           "An inhabitant of a type; the computational content that a type classifies.",
           keywords=["term", "expression"]),
        _c(D, P, "judgment",
           "A formal assertion such as 'a : A' (term a has type A) or 'Γ ⊢ a : A' (under context Γ).",
           keywords=["judgment", "typing"]),
        _c(D, P, "context",
           "An ordered list of variable-type bindings providing the assumptions under which a judgment is valid.",
           keywords=["context", "environment"]),
        _c(D, P, "pi_type",
           "The dependent function type Π(x:A).B(x): the type of functions whose return type may depend on the input.",
           formal_type="(x : A) → B x", keywords=["Pi", "dependent function"]),
        _c(D, P, "sigma_type",
           "The dependent pair type Σ(x:A).B(x): the type of pairs where the second component's type depends on the first.",
           formal_type="(x : A) × B x", keywords=["Sigma", "dependent pair"]),
        _c(D, P, "refinement_type",
           "A type {x:A | P(x)} restricting A to elements satisfying predicate P, combining typing with specification.",
           keywords=["refinement", "predicate subtype"]),
        _c(D, P, "identity_type",
           "The type Id_A(a,b) whose inhabitants are proofs that a and b are propositionally equal.",
           formal_type="a = b", keywords=["identity", "equality", "path"]),
        _c(D, P, "universe",
           "A type whose elements are themselves types; enables quantification over types (Type : Type with caveats).",
           formal_type="Type u", keywords=["universe", "Type"]),
        _c(D, P, "inhabitation",
           "A type is inhabited if it has at least one term; under propositions-as-types this means the proposition is provable.",
           keywords=["inhabited", "nonempty"]),
        _c(D, P, "type_checking",
           "The algorithmic problem of verifying that a term has a given type in a given context.",
           keywords=["checking", "verification"]),
        _c(D, P, "type_inference",
           "The algorithmic problem of deducing the type of a term when it is not fully annotated.",
           keywords=["inference", "reconstruction"]),
        _c(D, P, "bidirectional",
           "A type-checking strategy combining checking (push type in) and inference (pull type out) modes.",
           keywords=["bidirectional", "checking", "synthesis"]),
        _c(D, P, "subtyping",
           "A preorder on types: A <: B means every term of type A can be used where a B is expected.",
           keywords=["subtyping", "coercion"]),
        _c(D, P, "dependent_type",
           "A type that depends on a value, enabling types to express properties of their inhabitants.",
           keywords=["dependent", "indexed"]),
        _c(D, P, "inductive_type",
           "A type defined by its constructors and an elimination principle (recursion/induction).",
           keywords=["inductive", "constructor", "eliminator"]),
        _c(D, P, "coinductive_type",
           "A type defined by its observations/destructors, dual to inductive types; models infinite data.",
           keywords=["coinductive", "stream", "codata"]),
        _c(D, P, "hott",
           "Homotopy Type Theory: an interpretation of type theory where types are spaces and identity types are path spaces.",
           keywords=["HoTT", "homotopy"]),
        _c(D, P, "univalence",
           "The univalence axiom: equivalent types are equal, making the universe behave like a space of spaces.",
           keywords=["univalence", "equivalence"]),
        _c(D, P, "path",
           "In HoTT, an element of an identity type viewed as a path in the space corresponding to the type.",
           keywords=["path", "identity"]),
        _c(D, P, "transport",
           "Given a path p : a = b and P a, transport yields P b — carrying data along an equality proof.",
           keywords=["transport", "substitution"]),
    ]
    for c in concepts:
        site.add_concept(c)

    morphisms = [
        _m(P, "term", "type", "USES",
           "Every term is classified by a type."),
        _m(P, "judgment", "context", "USES",
           "A typing judgment is made relative to a context."),
        _m(P, "judgment", "term", "USES",
           "A judgment asserts a term has a type."),
        _m(P, "pi_type", "dependent_type", "SPECIALIZES",
           "Pi types are dependent function types."),
        _m(P, "sigma_type", "dependent_type", "SPECIALIZES",
           "Sigma types are dependent pair types."),
        _m(P, "refinement_type", "dependent_type", "SPECIALIZES",
           "Refinement types are a restricted form of dependent types."),
        _m(P, "pi_type", "sigma_type", "DUAL_TO",
           "Pi and Sigma are dual: universal vs. existential quantification over types."),
        _m(P, "identity_type", "type", "SPECIALIZES",
           "The identity type is a specific type family."),
        _m(P, "universe", "type", "GENERALIZES",
           "A universe is a type of types."),
        _m(P, "inhabitation", "type", "USES",
           "Inhabitation asks whether a type has a term."),
        _m(P, "type_checking", "judgment", "USES",
           "Type checking verifies a judgment."),
        _m(P, "type_inference", "judgment", "USES",
           "Type inference derives a judgment."),
        _m(P, "bidirectional", "type_checking", "USES",
           "Bidirectional type checking combines checking and inference."),
        _m(P, "bidirectional", "type_inference", "USES",
           "Bidirectional type checking uses inference in synthesis mode."),
        _m(P, "subtyping", "type", "USES",
           "Subtyping is a relation between types."),
        _m(P, "inductive_type", "type", "SPECIALIZES",
           "An inductive type is a type defined by constructors."),
        _m(P, "coinductive_type", "type", "SPECIALIZES",
           "A coinductive type is a type defined by destructors."),
        _m(P, "inductive_type", "coinductive_type", "DUAL_TO",
           "Inductive and coinductive types are dual."),
        _m(P, "hott", "identity_type", "USES",
           "HoTT reinterprets identity types as path spaces."),
        _m(P, "univalence", "identity_type", "USES",
           "Univalence equates equivalence of types with identity."),
        _m(P, "univalence", "hott", "PART_OF",
           "Univalence is a core axiom of HoTT."),
        _m(P, "path", "identity_type", "SPECIALIZES",
           "Paths are elements of identity types."),
        _m(P, "transport", "path", "USES",
           "Transport moves data along a path."),
        _m(P, "transport", "dependent_type", "USES",
           "Transport acts on dependent type families."),
        _m(P, "dependent_type", "type", "SPECIALIZES",
           "Dependent types are types indexed by values."),
        _m(P, "context", "type", "USES",
           "A context binds variables to types."),
        _m(P, "refinement_type", "subtyping", "USES",
           "Refinement types induce a subtyping relation.", 0.7),
    ]
    for m in morphisms:
        site.add_morphism(m)

    covers = [
        _cf(P, "judgment", ["context", "term", "type"],
            "A judgment Γ ⊢ a : A is determined by its context, term, and type."),
        _cf(P, "dependent_type", ["pi_type", "sigma_type", "identity_type"],
            "The main dependent type formers are Pi, Sigma, and identity types."),
        _cf(P, "bidirectional", ["type_checking", "type_inference"],
            "Bidirectional typing combines checking and inference modes."),
        _cf(P, "hott", ["identity_type", "univalence", "path", "transport"],
            "HoTT is built on identity types, univalence, paths, and transport."),
        _cf(P, "type", ["term", "inhabitation", "universe"],
            "A type is understood via its terms, inhabitation, and its place in a universe."),
        _cf(P, "inductive_type", ["type", "term"],
            "An inductive type is defined by its type signature and constructor terms."),
        _cf(P, "refinement_type", ["type", "subtyping"],
            "A refinement type combines a base type with a subtyping predicate."),
        _cf(P, "univalence", ["identity_type", "path"],
            "Univalence states that equivalences (paths in the universe) are identities."),
        _cf(P, "transport", ["path", "dependent_type"],
            "Transport is determined by a path and a dependent type family."),
        _cf(P, "type_checking", ["judgment", "context"],
            "Type checking validates a judgment in a given context."),
    ]
    for cf in covers:
        site.add_covering(cf)

    return site


# =========================================================================
# 5.3 Machine Learning
# =========================================================================


def _build_machine_learning() -> DomainSite:
    D = "machine_learning"
    P = "ml"
    site = DomainSite(D)

    concepts = [
        _c(D, P, "model",
           "A parameterised function mapping inputs to outputs, learned from data via optimization.",
           keywords=["model", "neural network"]),
        _c(D, P, "training",
           "The process of adjusting model parameters to minimize a loss function on a dataset.",
           keywords=["training", "learning"]),
        _c(D, P, "inference",
           "Using a trained model to produce predictions on new, unseen inputs.",
           keywords=["inference", "prediction"]),
        _c(D, P, "loss",
           "A scalar function measuring the discrepancy between model predictions and ground-truth labels.",
           keywords=["loss", "objective"]),
        _c(D, P, "gradient",
           "The vector of partial derivatives of the loss with respect to each parameter, indicating steepest ascent.",
           keywords=["gradient", "derivative"]),
        _c(D, P, "optimization",
           "The algorithmic process (e.g., SGD, Adam) of iteratively updating parameters to reduce the loss.",
           keywords=["optimization", "SGD", "Adam"]),
        _c(D, P, "overfitting",
           "When a model memorizes training data and performs poorly on unseen data due to excessive capacity.",
           keywords=["overfitting", "memorization"]),
        _c(D, P, "generalization",
           "A model's ability to perform well on data not seen during training.",
           keywords=["generalization", "test performance"]),
        _c(D, P, "hallucination",
           "When a generative model produces confident but factually incorrect or fabricated outputs.",
           keywords=["hallucination", "confabulation"]),
        _c(D, P, "confidence",
           "The model's self-reported certainty about a prediction, often calibrated poorly.",
           keywords=["confidence", "probability"]),
        _c(D, P, "calibration",
           "The property that a model's predicted probabilities match empirical frequencies of correctness.",
           keywords=["calibration", "reliability"]),
        _c(D, P, "prompt",
           "The input text given to a language model to elicit a particular kind of response.",
           keywords=["prompt", "input"]),
        _c(D, P, "completion",
           "The text generated by a language model in response to a prompt.",
           keywords=["completion", "generation"]),
        _c(D, P, "fine_tuning",
           "Continued training of a pre-trained model on a smaller, task-specific dataset.",
           keywords=["fine-tuning", "transfer learning"]),
        _c(D, P, "rlhf",
           "Reinforcement Learning from Human Feedback: aligning model outputs with human preferences via a reward model.",
           keywords=["RLHF", "alignment"]),
        _c(D, P, "attention",
           "A mechanism letting the model weigh the importance of different input positions when producing each output.",
           keywords=["attention", "self-attention"]),
        _c(D, P, "transformer",
           "An architecture built on self-attention layers, dominant in modern NLP and increasingly in other modalities.",
           keywords=["transformer", "architecture"]),
        _c(D, P, "embedding",
           "A learned dense vector representation of a discrete input (word, token, entity) in a continuous space.",
           keywords=["embedding", "representation"]),
        _c(D, P, "tokenization",
           "The process of splitting raw text into discrete tokens (subwords, characters, or words) for model input.",
           keywords=["tokenization", "BPE"]),
        _c(D, P, "temperature",
           "A sampling parameter that scales logits before softmax, controlling randomness of generation.",
           keywords=["temperature", "sampling"]),
    ]
    for c in concepts:
        site.add_concept(c)

    morphisms = [
        _m(P, "training", "model", "USES",
           "Training adjusts the parameters of a model."),
        _m(P, "training", "loss", "USES",
           "Training minimizes a loss function."),
        _m(P, "training", "gradient", "USES",
           "Training computes gradients to update parameters."),
        _m(P, "training", "optimization", "USES",
           "Training employs an optimization algorithm."),
        _m(P, "inference", "model", "USES",
           "Inference uses a trained model to make predictions."),
        _m(P, "loss", "gradient", "IMPLIES",
           "Differentiating the loss yields the gradient."),
        _m(P, "gradient", "optimization", "USES",
           "Optimization algorithms consume gradients."),
        _m(P, "overfitting", "generalization", "DUAL_TO",
           "Overfitting is the failure of generalization."),
        _m(P, "overfitting", "training", "USES",
           "Overfitting arises from excessive training."),
        _m(P, "generalization", "inference", "IMPLIES",
           "Good generalization implies reliable inference."),
        _m(P, "hallucination", "confidence", "USES",
           "Hallucinations are produced with high but unwarranted confidence."),
        _m(P, "calibration", "confidence", "USES",
           "Calibration measures how well confidence tracks accuracy."),
        _m(P, "prompt", "completion", "IMPLIES",
           "A prompt determines a distribution over completions."),
        _m(P, "fine_tuning", "training", "SPECIALIZES",
           "Fine-tuning is a special case of training on targeted data."),
        _m(P, "rlhf", "fine_tuning", "SPECIALIZES",
           "RLHF is a fine-tuning method using human feedback.", 0.9),
        _m(P, "rlhf", "loss", "USES",
           "RLHF defines a reward-based loss."),
        _m(P, "attention", "transformer", "PART_OF",
           "Attention is the core mechanism of the transformer."),
        _m(P, "transformer", "model", "SPECIALIZES",
           "A transformer is a specific model architecture."),
        _m(P, "embedding", "model", "PART_OF",
           "Embeddings are a component of model input processing."),
        _m(P, "tokenization", "embedding", "IMPLIES",
           "Tokenization precedes embedding: tokens are mapped to vectors."),
        _m(P, "tokenization", "prompt", "USES",
           "Prompts are tokenized before being fed to the model."),
        _m(P, "temperature", "completion", "USES",
           "Temperature controls the randomness of completions."),
        _m(P, "temperature", "confidence", "USES",
           "Temperature affects the sharpness of confidence distributions."),
        _m(P, "completion", "hallucination", "IMPLIES",
           "Completions may exhibit hallucination.", 0.5),
        _m(P, "model", "inference", "USES",
           "A model is used at inference time.", 0.9),
        _m(P, "embedding", "tokenization", "USES",
           "Embeddings are looked up by token ID.", 0.7),
    ]
    for m in morphisms:
        site.add_morphism(m)

    covers = [
        _cf(P, "training", ["model", "loss", "gradient", "optimization"],
            "Training is decomposed into model, loss, gradient computation, and optimization."),
        _cf(P, "model", ["transformer", "embedding"],
            "A modern language model consists of an embedding layer and transformer blocks."),
        _cf(P, "inference", ["model", "prompt", "completion"],
            "Inference takes a model and prompt to produce a completion."),
        _cf(P, "overfitting", ["training", "generalization"],
            "Overfitting is understood as the gap between training and generalization performance."),
        _cf(P, "hallucination", ["confidence", "calibration", "completion"],
            "Hallucination arises from poor calibration of confidence in completions."),
        _cf(P, "rlhf", ["fine_tuning", "loss", "training"],
            "RLHF is a fine-tuning technique with a reward-based loss for training."),
        _cf(P, "transformer", ["attention", "embedding"],
            "A transformer is built from attention mechanisms and embedding layers."),
        _cf(P, "completion", ["prompt", "temperature", "model"],
            "A completion depends on the prompt, temperature, and the model."),
        _cf(P, "calibration", ["confidence", "training"],
            "Calibration measures alignment of confidence with training accuracy."),
        _cf(P, "tokenization", ["prompt", "embedding"],
            "Tokenization converts prompts into sequences suitable for embedding."),
    ]
    for cf in covers:
        site.add_covering(cf)

    return site


# =========================================================================
# 5.4 Software Engineering
# =========================================================================


def _build_software_engineering() -> DomainSite:
    D = "software_engineering"
    P = "se"
    site = DomainSite(D)

    concepts = [
        _c(D, P, "module",
           "A self-contained unit of code that encapsulates related functionality behind a defined interface.",
           keywords=["module", "encapsulation"]),
        _c(D, P, "function",
           "A named, reusable block of code that takes inputs and produces an output.",
           keywords=["function", "subroutine"]),
        _c(D, P, "class_",
           "A blueprint for objects bundling data (fields) and behaviour (methods) together.",
           keywords=["class", "OOP"]),
        _c(D, P, "interface",
           "A contract specifying method signatures without implementation; a type boundary.",
           keywords=["interface", "contract"]),
        _c(D, P, "api",
           "Application Programming Interface: the set of public endpoints or functions exposed by a module or service.",
           keywords=["API", "endpoint"]),
        _c(D, P, "test",
           "Executable code that asserts expected behavior of production code, enabling regression detection.",
           keywords=["test", "assertion"]),
        _c(D, P, "bug",
           "A defect in software where actual behavior diverges from intended behavior.",
           keywords=["bug", "defect"]),
        _c(D, P, "refactor",
           "Restructuring existing code without changing its external behavior, improving readability or structure.",
           keywords=["refactor", "restructure"]),
        _c(D, P, "ci_cd",
           "Continuous Integration / Continuous Deployment: automated pipelines that build, test, and deploy code.",
           keywords=["CI/CD", "pipeline"]),
        _c(D, P, "deployment",
           "The process of releasing software to a production environment for end users.",
           keywords=["deployment", "release"]),
        _c(D, P, "code_review",
           "Systematic examination of source code by peers to find defects and ensure quality.",
           keywords=["code review", "peer review"]),
        _c(D, P, "version_control",
           "A system (e.g., git) tracking changes to files over time, enabling collaboration and rollback.",
           keywords=["git", "version control"]),
        _c(D, P, "dependency",
           "An external library or module that a project relies on to function.",
           keywords=["dependency", "library"]),
        _c(D, P, "package",
           "A distributable unit of software including code, metadata, and dependency declarations.",
           keywords=["package", "distribution"]),
        _c(D, P, "documentation",
           "Written material describing how code works, its API, or how to use it.",
           keywords=["documentation", "docs"]),
        _c(D, P, "linting",
           "Static analysis of source code to detect stylistic issues, potential bugs, and anti-patterns.",
           keywords=["linting", "static analysis"]),
        _c(D, P, "type_checking",
           "Verifying that values conform to their declared types, either statically or at runtime.",
           keywords=["type checking", "static typing"]),
        _c(D, P, "runtime_error",
           "An error that occurs during program execution, as opposed to a compile-time error.",
           keywords=["runtime error", "exception"]),
        _c(D, P, "specification",
           "A precise description of what a system or component should do, independent of implementation.",
           keywords=["specification", "spec"]),
        _c(D, P, "requirement",
           "A statement of need that a system must satisfy, derived from stakeholders or problem analysis.",
           keywords=["requirement", "need"]),
    ]
    for c in concepts:
        site.add_concept(c)

    morphisms = [
        _m(P, "module", "function", "USES",
           "Modules contain and organise functions."),
        _m(P, "module", "class_", "USES",
           "Modules may contain class definitions."),
        _m(P, "class_", "interface", "USES",
           "A class may implement one or more interfaces."),
        _m(P, "interface", "api", "IMPLIES",
           "An interface defines part of a module's API."),
        _m(P, "test", "bug", "IMPLIES",
           "Tests reveal bugs by asserting expected behavior.", 0.7),
        _m(P, "test", "function", "USES",
           "Tests exercise functions."),
        _m(P, "refactor", "module", "USES",
           "Refactoring restructures modules."),
        _m(P, "refactor", "test", "USES",
           "Refactoring relies on tests to ensure no behavior change."),
        _m(P, "ci_cd", "test", "USES",
           "CI/CD pipelines run tests automatically."),
        _m(P, "ci_cd", "deployment", "IMPLIES",
           "CI/CD automates deployment."),
        _m(P, "ci_cd", "linting", "USES",
           "CI/CD pipelines often include linting."),
        _m(P, "code_review", "bug", "IMPLIES",
           "Code review helps catch bugs.", 0.6),
        _m(P, "code_review", "refactor", "IMPLIES",
           "Code review may suggest refactoring.", 0.5),
        _m(P, "version_control", "code_review", "USES",
           "Code review is conducted through version control diffs."),
        _m(P, "dependency", "package", "USES",
           "Dependencies are managed as packages."),
        _m(P, "package", "module", "USES",
           "A package bundles one or more modules."),
        _m(P, "documentation", "api", "USES",
           "Documentation describes the API."),
        _m(P, "linting", "bug", "IMPLIES",
           "Linting catches potential bugs statically.", 0.5),
        _m(P, "type_checking", "runtime_error", "IMPLIES",
           "Type checking prevents certain runtime errors.", 0.8),
        _m(P, "type_checking", "linting", "GENERALIZES",
           "Type checking subsumes some lint checks."),
        _m(P, "specification", "requirement", "SPECIALIZES",
           "A specification is a formal refinement of requirements."),
        _m(P, "requirement", "test", "IMPLIES",
           "Requirements drive test design."),
        _m(P, "specification", "interface", "IMPLIES",
           "A specification can be realized as an interface."),
        _m(P, "bug", "runtime_error", "IMPLIES",
           "A bug may manifest as a runtime error."),
        _m(P, "function", "api", "PART_OF",
           "Public functions are part of an API."),
        _m(P, "deployment", "package", "USES",
           "Deployment ships a built package."),
        _m(P, "version_control", "ci_cd", "USES",
           "CI/CD is triggered by version-control events.", 0.9),
    ]
    for m in morphisms:
        site.add_morphism(m)

    covers = [
        _cf(P, "module", ["function", "class_", "interface"],
            "A module is composed of functions, classes, and interfaces."),
        _cf(P, "ci_cd", ["test", "linting", "deployment"],
            "CI/CD orchestrates testing, linting, and deployment."),
        _cf(P, "code_review", ["version_control", "test", "documentation"],
            "Code review uses version control diffs, tests, and documentation."),
        _cf(P, "bug", ["test", "linting", "type_checking"],
            "Bugs are caught by tests, linting, and type checking."),
        _cf(P, "api", ["function", "interface", "documentation"],
            "An API comprises functions, interfaces, and documentation."),
        _cf(P, "package", ["module", "dependency", "documentation"],
            "A package bundles modules, declares dependencies, and includes docs."),
        _cf(P, "refactor", ["module", "test"],
            "Refactoring restructures modules while being guarded by tests."),
        _cf(P, "deployment", ["ci_cd", "package"],
            "Deployment is achieved through CI/CD operating on a built package."),
        _cf(P, "specification", ["requirement", "interface"],
            "A specification formalizes requirements as interface contracts."),
        _cf(P, "runtime_error", ["bug", "type_checking"],
            "Runtime errors trace back to bugs that type checking might have caught."),
        _cf(P, "type_checking", ["linting", "interface"],
            "Type checking combines static analysis with interface conformance."),
    ]
    for cf in covers:
        site.add_covering(cf)

    return site


# =========================================================================
# 5.5 Category Theory
# =========================================================================


def _build_category_theory() -> DomainSite:
    D = "category_theory"
    P = "ct"
    site = DomainSite(D)

    concepts = [
        _c(D, P, "category",
           "A collection of objects and morphisms with associative composition and identities.",
           formal_type="Category", keywords=["category", "objects", "morphisms"]),
        _c(D, P, "functor",
           "A structure-preserving map between categories, sending objects to objects and morphisms to morphisms.",
           formal_type="C ⥤ D", keywords=["functor", "mapping"]),
        _c(D, P, "natural_transformation",
           "A family of morphisms between two functors that commutes with every morphism in the source category.",
           formal_type="F ⟶ G", keywords=["natural transformation", "component"]),
        _c(D, P, "adjunction",
           "A pair of functors (F ⊣ G) with a natural bijection Hom(F(a), b) ≅ Hom(a, G(b)).",
           keywords=["adjunction", "left adjoint", "right adjoint"]),
        _c(D, P, "limit",
           "A universal cone over a diagram: the most general object mapping into every object of the diagram compatibly.",
           keywords=["limit", "cone", "universal"]),
        _c(D, P, "colimit",
           "A universal cocone under a diagram: the most general object receiving maps from every object of the diagram.",
           keywords=["colimit", "cocone"]),
        _c(D, P, "kan_extension",
           "The universal solution to extending a functor along another functor; subsumes limits and colimits.",
           keywords=["Kan extension", "universal"]),
        _c(D, P, "yoneda",
           "The Yoneda lemma: Nat(Hom(a,−), F) ≅ F(a), embedding every category into its presheaf category.",
           keywords=["Yoneda", "embedding"]),
        _c(D, P, "monad",
           "An endofunctor T with unit η and multiplication μ satisfying associativity and unit laws; captures algebraic theories.",
           keywords=["monad", "unit", "multiplication"]),
        _c(D, P, "comonad",
           "The dual of a monad: an endofunctor with counit and comultiplication; models contexts and codata.",
           keywords=["comonad", "counit"]),
        _c(D, P, "topos",
           "A category that behaves like a category of sheaves: has finite limits, exponentials, and a subobject classifier.",
           keywords=["topos", "sheaf", "logic"]),
        _c(D, P, "presheaf_category",
           "The functor category [Cᵒᵖ, Set] of contravariant functors from C to Set; always a topos.",
           keywords=["presheaf", "functor category"]),
        _c(D, P, "slice_category",
           "The category C/X of objects over X: objects are morphisms into X, morphisms are commuting triangles.",
           keywords=["slice", "over category"]),
        _c(D, P, "enriched_category",
           "A category whose hom-sets carry extra structure (e.g., topological, metric, order) from a monoidal category.",
           keywords=["enriched", "monoidal"]),
        _c(D, P, "two_category",
           "A higher category with objects, 1-morphisms, and 2-morphisms, where composition is only associative up to isomorphism.",
           keywords=["2-category", "higher"]),
        _c(D, P, "equivalence",
           "A functor F : C → D with a pseudo-inverse G such that GF ≅ Id and FG ≅ Id; weaker than isomorphism.",
           keywords=["equivalence", "pseudo-inverse"]),
        _c(D, P, "isomorphism",
           "A morphism with a two-sided inverse; the strictest notion of sameness in a category.",
           keywords=["isomorphism", "invertible"]),
    ]
    for c in concepts:
        site.add_concept(c)

    morphisms = [
        _m(P, "functor", "category", "USES",
           "A functor maps between categories."),
        _m(P, "natural_transformation", "functor", "USES",
           "A natural transformation relates two functors."),
        _m(P, "adjunction", "functor", "USES",
           "An adjunction is a pair of functors with a universal property."),
        _m(P, "adjunction", "natural_transformation", "USES",
           "An adjunction includes unit and counit natural transformations."),
        _m(P, "limit", "category", "USES",
           "Limits are defined inside a category."),
        _m(P, "colimit", "category", "USES",
           "Colimits are defined inside a category."),
        _m(P, "limit", "colimit", "DUAL_TO",
           "Limits and colimits are categorically dual."),
        _m(P, "kan_extension", "functor", "GENERALIZES",
           "Kan extensions generalize extending functors."),
        _m(P, "kan_extension", "limit", "GENERALIZES",
           "Every limit is a right Kan extension along a unique functor."),
        _m(P, "kan_extension", "colimit", "GENERALIZES",
           "Every colimit is a left Kan extension."),
        _m(P, "yoneda", "presheaf_category", "USES",
           "The Yoneda embedding lands in the presheaf category."),
        _m(P, "yoneda", "functor", "USES",
           "The Yoneda lemma concerns representable functors."),
        _m(P, "monad", "adjunction", "USES",
           "Every adjunction gives rise to a monad.", 0.9),
        _m(P, "monad", "functor", "SPECIALIZES",
           "A monad is an endofunctor with extra structure."),
        _m(P, "comonad", "monad", "DUAL_TO",
           "A comonad is the categorical dual of a monad."),
        _m(P, "comonad", "functor", "SPECIALIZES",
           "A comonad is an endofunctor with counit and comultiplication."),
        _m(P, "topos", "presheaf_category", "GENERALIZES",
           "Every presheaf category is a topos; topoi generalise this.", 0.9),
        _m(P, "topos", "limit", "USES",
           "A topos has all finite limits."),
        _m(P, "presheaf_category", "functor", "USES",
           "A presheaf category is a functor category."),
        _m(P, "slice_category", "category", "SPECIALIZES",
           "A slice category is a category constructed over a fixed object."),
        _m(P, "enriched_category", "category", "GENERALIZES",
           "An enriched category generalises a category by replacing hom-sets."),
        _m(P, "two_category", "category", "GENERALIZES",
           "A 2-category adds 2-morphisms to a category."),
        _m(P, "equivalence", "isomorphism", "GENERALIZES",
           "An equivalence is a weakened isomorphism of categories."),
        _m(P, "equivalence", "functor", "USES",
           "An equivalence is realised by a functor with a pseudo-inverse."),
        _m(P, "isomorphism", "category", "PART_OF",
           "Isomorphisms live inside a category."),
        _m(P, "adjunction", "kan_extension", "SPECIALIZES",
           "An adjunction is a special case of a Kan extension.", 0.7),
        _m(P, "natural_transformation", "two_category", "PART_OF",
           "Natural transformations are the 2-morphisms of Cat.", 0.8),
    ]
    for m in morphisms:
        site.add_morphism(m)

    covers = [
        _cf(P, "category", ["functor", "natural_transformation", "isomorphism"],
            "A category is studied via its functors, natural transformations, and isomorphisms."),
        _cf(P, "adjunction", ["functor", "natural_transformation"],
            "An adjunction is a pair of functors linked by unit/counit natural transformations."),
        _cf(P, "kan_extension", ["functor", "limit", "colimit"],
            "Kan extensions subsume limits and colimits as special cases."),
        _cf(P, "monad", ["functor", "adjunction"],
            "A monad arises from an adjunction and is an endofunctor with extra structure."),
        _cf(P, "topos", ["presheaf_category", "limit"],
            "A topos is characterised by being a presheaf-like category with finite limits."),
        _cf(P, "yoneda", ["functor", "presheaf_category"],
            "Yoneda embeds a category fully and faithfully into its presheaf category."),
        _cf(P, "equivalence", ["functor", "isomorphism"],
            "An equivalence consists of functors whose composites are isomorphic to identities."),
        _cf(P, "two_category", ["category", "natural_transformation"],
            "A 2-category has categories as hom-categories, with natural transformations as 2-morphisms."),
        _cf(P, "enriched_category", ["category", "monad"],
            "Enriched categories generalise categories; monads on enrichment categories give examples."),
        _cf(P, "slice_category", ["category", "functor"],
            "A slice category is built from a category and the forgetful functor to the base."),
        _cf(P, "comonad", ["functor", "adjunction"],
            "A comonad arises from an adjunction, dual to a monad."),
    ]
    for cf in covers:
        site.add_covering(cf)

    return site


# =========================================================================
# 5.6 Formal Verification
# =========================================================================


def _build_formal_verification() -> DomainSite:
    D = "formal_verification"
    P = "fv"
    site = DomainSite(D)

    concepts = [
        _c(D, P, "proof",
           "A formal derivation establishing the truth of a proposition within a logical system.",
           keywords=["proof", "derivation"]),
        _c(D, P, "theorem",
           "A proposition that has been proved; a statement with an accompanying proof object.",
           keywords=["theorem", "proved"]),
        _c(D, P, "lemma",
           "A proved auxiliary proposition used as a stepping stone toward a theorem.",
           keywords=["lemma", "auxiliary"]),
        _c(D, P, "axiom",
           "A proposition accepted without proof, forming part of the foundation of a formal system.",
           keywords=["axiom", "assumption"]),
        _c(D, P, "tactic",
           "A proof-construction command in an interactive theorem prover that transforms proof goals.",
           keywords=["tactic", "proof automation"]),
        _c(D, P, "proof_obligation",
           "A logical condition generated by a verification tool that must be discharged to ensure correctness.",
           keywords=["proof obligation", "verification condition"]),
        _c(D, P, "invariant",
           "A property that holds throughout the execution of a program or loop, enabling inductive reasoning.",
           keywords=["invariant", "assertion"]),
        _c(D, P, "precondition",
           "A predicate that must hold before a function or operation executes to guarantee correct behavior.",
           keywords=["precondition", "requires"]),
        _c(D, P, "postcondition",
           "A predicate that must hold after a function or operation completes, specifying what it achieves.",
           keywords=["postcondition", "ensures"]),
        _c(D, P, "loop_invariant",
           "An invariant maintained across iterations of a loop, enabling proof of the loop's correctness.",
           keywords=["loop invariant", "induction"]),
        _c(D, P, "termination",
           "A proof that a computation eventually halts, typically via a well-founded decreasing measure.",
           keywords=["termination", "well-founded"]),
        _c(D, P, "soundness",
           "A property of a logic or algorithm: everything it proves/accepts is actually true/correct.",
           keywords=["soundness", "correct"]),
        _c(D, P, "completeness",
           "A property of a logic or algorithm: every true/correct statement can be proved/accepted.",
           keywords=["completeness", "all provable"]),
        _c(D, P, "decidability",
           "A property of a problem: there exists an algorithm that always terminates with a yes/no answer.",
           keywords=["decidability", "algorithm"]),
        _c(D, P, "smt",
           "Satisfiability Modulo Theories: solvers combining SAT with theory-specific decision procedures.",
           keywords=["SMT", "solver", "SAT"]),
        _c(D, P, "model_checking",
           "Exhaustive exploration of a system's state space to verify that a temporal property holds in all reachable states.",
           keywords=["model checking", "state space"]),
        _c(D, P, "refinement",
           "A relation between an abstract specification and a concrete implementation preserving observable behavior.",
           keywords=["refinement", "abstraction"]),
        _c(D, P, "abstraction",
           "Replacing a concrete system with a simpler over-approximation that preserves properties of interest.",
           keywords=["abstraction", "over-approximation"]),
        _c(D, P, "cegar",
           "Counter-Example Guided Abstraction Refinement: iteratively refining abstractions using spurious counterexamples.",
           keywords=["CEGAR", "counterexample"]),
    ]
    for c in concepts:
        site.add_concept(c)

    morphisms = [
        _m(P, "proof", "theorem", "IMPLIES",
           "A proof establishes a theorem."),
        _m(P, "lemma", "theorem", "USES",
           "Lemmas are used in proving theorems.", 0.9),
        _m(P, "lemma", "proof", "PART_OF",
           "Lemmas are components of proofs."),
        _m(P, "axiom", "proof", "USES",
           "Proofs may rely on axioms."),
        _m(P, "tactic", "proof", "USES",
           "Tactics construct proofs interactively."),
        _m(P, "proof_obligation", "proof", "IMPLIES",
           "Discharging a proof obligation yields a proof."),
        _m(P, "invariant", "proof_obligation", "USES",
           "Invariants generate proof obligations."),
        _m(P, "precondition", "proof_obligation", "USES",
           "Preconditions contribute to proof obligations."),
        _m(P, "postcondition", "proof_obligation", "USES",
           "Postconditions contribute to proof obligations."),
        _m(P, "loop_invariant", "invariant", "SPECIALIZES",
           "A loop invariant is an invariant specific to a loop."),
        _m(P, "termination", "proof", "USES",
           "Termination arguments are part of correctness proofs."),
        _m(P, "termination", "loop_invariant", "USES",
           "Termination proofs often use a loop invariant plus a decreasing variant."),
        _m(P, "soundness", "proof", "USES",
           "Soundness guarantees that proofs only establish true statements."),
        _m(P, "completeness", "soundness", "DUAL_TO",
           "Soundness and completeness are dual meta-logical properties."),
        _m(P, "decidability", "completeness", "IMPLIES",
           "Decidability of a theory implies a form of completeness.", 0.6),
        _m(P, "smt", "proof_obligation", "USES",
           "SMT solvers discharge proof obligations automatically."),
        _m(P, "smt", "decidability", "USES",
           "SMT solvers rely on decidable theories."),
        _m(P, "model_checking", "abstraction", "USES",
           "Model checking often uses abstract models of the state space."),
        _m(P, "refinement", "abstraction", "DUAL_TO",
           "Refinement and abstraction are dual: one adds detail, the other removes it."),
        _m(P, "refinement", "postcondition", "USES",
           "Refinement preserves postconditions.", 0.8),
        _m(P, "cegar", "model_checking", "USES",
           "CEGAR is a model-checking technique."),
        _m(P, "cegar", "abstraction", "USES",
           "CEGAR iteratively refines abstractions."),
        _m(P, "cegar", "refinement", "USES",
           "CEGAR uses refinement to eliminate spurious counterexamples."),
        _m(P, "proof_obligation", "precondition", "USES",
           "Proof obligations encode precondition verification."),
        _m(P, "proof_obligation", "postcondition", "USES",
           "Proof obligations encode postcondition verification."),
        _m(P, "invariant", "precondition", "GENERALIZES",
           "An invariant generalises a precondition across all program points."),
        _m(P, "tactic", "smt", "USES",
           "Tactics may invoke SMT solvers as backends.", 0.6),
    ]
    for m in morphisms:
        site.add_morphism(m)

    covers = [
        _cf(P, "proof", ["axiom", "lemma", "tactic"],
            "A proof is built from axioms, lemmas, and tactic-driven steps."),
        _cf(P, "theorem", ["proof", "lemma"],
            "A theorem consists of a proof possibly using lemmas."),
        _cf(P, "proof_obligation", ["precondition", "postcondition", "invariant"],
            "Proof obligations arise from preconditions, postconditions, and invariants."),
        _cf(P, "invariant", ["precondition", "postcondition", "loop_invariant"],
            "An invariant encompasses preconditions, postconditions, and loop invariants."),
        _cf(P, "cegar", ["model_checking", "abstraction", "refinement"],
            "CEGAR combines model checking with iterative abstraction-refinement."),
        _cf(P, "soundness", ["proof", "axiom"],
            "Soundness holds when the proof system and axioms are correct."),
        _cf(P, "model_checking", ["abstraction", "decidability"],
            "Model checking relies on decidable logics and abstract state spaces."),
        _cf(P, "termination", ["loop_invariant", "proof"],
            "Termination is proved via a loop invariant and a decreasing measure."),
        _cf(P, "smt", ["decidability", "proof_obligation"],
            "SMT solvers decide proof obligations in decidable theories."),
        _cf(P, "refinement", ["abstraction", "postcondition"],
            "Refinement maps abstract postconditions to concrete implementations."),
        _cf(P, "completeness", ["soundness", "decidability"],
            "Completeness relates to soundness and decidability of the underlying logic."),
    ]
    for cf in covers:
        site.add_covering(cf)

    return site


# =========================================================================
# 5.7 Linguistics
# =========================================================================


def _build_linguistics() -> DomainSite:
    D = "linguistics"
    P = "ling"
    site = DomainSite(D)

    concepts = [
        _c(D, P, "syntax",
           "The component of grammar governing the arrangement of words and phrases into well-formed sentences.",
           keywords=["syntax", "structure"]),
        _c(D, P, "semantics",
           "The study of meaning: how expressions map to denotations or truth conditions.",
           keywords=["semantics", "meaning"]),
        _c(D, P, "pragmatics",
           "The study of how context contributes to meaning beyond what is literally said.",
           keywords=["pragmatics", "context", "use"]),
        _c(D, P, "grammar",
           "The full system of rules (phonological, morphological, syntactic) governing a language.",
           keywords=["grammar", "rules"]),
        _c(D, P, "parse_tree",
           "A hierarchical tree structure representing the syntactic analysis of a sentence.",
           keywords=["parse tree", "syntax tree"]),
        _c(D, P, "ambiguity",
           "The property of an expression having more than one possible interpretation (syntactic or semantic).",
           keywords=["ambiguity", "polysemy"]),
        _c(D, P, "compositionality",
           "The principle that the meaning of a complex expression is determined by its parts and their mode of combination.",
           keywords=["compositionality", "Frege"]),
        _c(D, P, "reference",
           "The relation between a linguistic expression and the entity it picks out in the world or discourse.",
           keywords=["reference", "denotation"]),
        _c(D, P, "context",
           "The surrounding information (linguistic, situational, social) that influences interpretation.",
           keywords=["context", "situation"]),
        _c(D, P, "speech_act",
           "An utterance viewed as an action: asserting, requesting, promising, etc.",
           keywords=["speech act", "illocution"]),
        _c(D, P, "illocutionary_force",
           "The communicative intention behind a speech act (assertive, directive, commissive, expressive, declarative).",
           keywords=["illocutionary", "force"]),
        _c(D, P, "presupposition",
           "Background information taken for granted by the speaker, which must be accommodated for the utterance to be felicitous.",
           keywords=["presupposition", "background"]),
        _c(D, P, "implicature",
           "What is suggested or implied by an utterance beyond its literal content, often via Gricean maxims.",
           keywords=["implicature", "Grice"]),
        _c(D, P, "discourse",
           "Extended stretches of language (text or conversation) beyond the single sentence, with coherence relations.",
           keywords=["discourse", "text"]),
        _c(D, P, "coherence",
           "The property of a discourse being logically and thematically connected, enabling comprehension.",
           keywords=["coherence", "cohesion"]),
        _c(D, P, "anaphora",
           "The use of a pronoun or other expression to refer back to a previously introduced entity in discourse.",
           keywords=["anaphora", "pronoun", "coreference"]),
    ]
    for c in concepts:
        site.add_concept(c)

    morphisms = [
        _m(P, "syntax", "grammar", "PART_OF",
           "Syntax is a component of grammar."),
        _m(P, "semantics", "grammar", "PART_OF",
           "Semantics is a component of grammar (in a broad sense)."),
        _m(P, "pragmatics", "semantics", "GENERALIZES",
           "Pragmatics extends semantics with contextual meaning."),
        _m(P, "parse_tree", "syntax", "USES",
           "Parse trees represent syntactic structure."),
        _m(P, "ambiguity", "parse_tree", "USES",
           "Syntactic ambiguity yields multiple parse trees."),
        _m(P, "ambiguity", "semantics", "USES",
           "Semantic ambiguity yields multiple interpretations."),
        _m(P, "compositionality", "semantics", "USES",
           "Compositionality is a principle of semantic interpretation."),
        _m(P, "compositionality", "syntax", "USES",
           "Compositional semantics is guided by syntactic structure."),
        _m(P, "reference", "semantics", "PART_OF",
           "Reference is a core semantic relation."),
        _m(P, "context", "pragmatics", "USES",
           "Context is central to pragmatic interpretation."),
        _m(P, "context", "reference", "USES",
           "Context disambiguates reference."),
        _m(P, "speech_act", "pragmatics", "PART_OF",
           "Speech acts are studied under pragmatics."),
        _m(P, "illocutionary_force", "speech_act", "PART_OF",
           "Illocutionary force is a component of a speech act."),
        _m(P, "presupposition", "pragmatics", "PART_OF",
           "Presuppositions are a pragmatic phenomenon."),
        _m(P, "presupposition", "context", "USES",
           "Presuppositions must be supported by context."),
        _m(P, "implicature", "pragmatics", "PART_OF",
           "Implicatures are pragmatic inferences."),
        _m(P, "implicature", "context", "USES",
           "Implicatures depend on conversational context."),
        _m(P, "discourse", "coherence", "USES",
           "Discourse requires coherence to be interpretable."),
        _m(P, "discourse", "context", "USES",
           "Discourse unfolds within and creates context."),
        _m(P, "coherence", "anaphora", "USES",
           "Anaphora resolution is crucial for discourse coherence."),
        _m(P, "anaphora", "reference", "SPECIALIZES",
           "Anaphora is a special case of reference: referring back to a discourse entity."),
        _m(P, "anaphora", "context", "USES",
           "Anaphora resolution depends on discourse context."),
        _m(P, "speech_act", "context", "USES",
           "The force of a speech act depends on context."),
        _m(P, "grammar", "syntax", "USES",
           "Grammar includes syntactic rules."),
        _m(P, "grammar", "semantics", "USES",
           "Grammar pairs syntactic forms with meanings."),
        _m(P, "parse_tree", "compositionality", "IMPLIES",
           "Parse trees enable compositional semantic interpretation."),
    ]
    for m in morphisms:
        site.add_morphism(m)

    covers = [
        _cf(P, "grammar", ["syntax", "semantics"],
            "Grammar is decomposed into syntactic and semantic components."),
        _cf(P, "pragmatics", ["context", "speech_act", "implicature", "presupposition"],
            "Pragmatics is covered by context, speech acts, implicatures, and presuppositions."),
        _cf(P, "speech_act", ["illocutionary_force", "context"],
            "A speech act is determined by its illocutionary force and context."),
        _cf(P, "semantics", ["compositionality", "reference"],
            "Semantics is understood through compositionality and reference."),
        _cf(P, "ambiguity", ["parse_tree", "semantics"],
            "Ambiguity is located in multiple parse trees or semantic readings."),
        _cf(P, "discourse", ["coherence", "anaphora", "context"],
            "Discourse coheres through coherence relations, anaphora, and shared context."),
        _cf(P, "compositionality", ["syntax", "semantics"],
            "Compositionality relates syntactic structure to semantic interpretation."),
        _cf(P, "anaphora", ["reference", "context"],
            "Anaphora resolution requires referential and contextual information."),
        _cf(P, "implicature", ["context", "pragmatics"],
            "Implicatures are inferred from context using pragmatic principles."),
        _cf(P, "presupposition", ["context", "semantics"],
            "Presuppositions bridge semantic content and contextual requirements."),
        _cf(P, "coherence", ["anaphora", "discourse"],
            "Coherence is maintained through anaphoric links within discourse."),
    ]
    for cf in covers:
        site.add_covering(cf)

    return site


# #########################################################################
# Build all pre-built domains
# #########################################################################

ALGEBRAIC_GEOMETRY: DomainSite = _build_algebraic_geometry()
TYPE_THEORY: DomainSite = _build_type_theory()
MACHINE_LEARNING: DomainSite = _build_machine_learning()
SOFTWARE_ENGINEERING: DomainSite = _build_software_engineering()
CATEGORY_THEORY: DomainSite = _build_category_theory()
FORMAL_VERIFICATION: DomainSite = _build_formal_verification()
LINGUISTICS: DomainSite = _build_linguistics()


# =========================================================================
# 6. DomainRegistry
# =========================================================================


class DomainRegistry:
    """Registry of all known domain sites."""

    def __init__(self) -> None:
        self._domains: Dict[str, DomainSite] = {}
        for site in [
            ALGEBRAIC_GEOMETRY,
            TYPE_THEORY,
            MACHINE_LEARNING,
            SOFTWARE_ENGINEERING,
            CATEGORY_THEORY,
            FORMAL_VERIFICATION,
            LINGUISTICS,
        ]:
            self.register(site)

    def register(self, site: DomainSite) -> None:
        """Register a domain site by name."""
        self._domains[site.name] = site

    def get(self, name: str) -> DomainSite:
        """Retrieve a domain site by name."""
        if name not in self._domains:
            raise KeyError(
                f"Domain {name!r} not found. "
                f"Available: {sorted(self._domains.keys())}"
            )
        return self._domains[name]

    def all_domains(self) -> List[str]:
        """List all registered domain names."""
        return sorted(self._domains.keys())

    def overlap(self, d1: str, d2: str) -> DomainSite:
        """Compute the overlap (intersection) of two registered domain sites."""
        return self.get(d1).overlap(self.get(d2))

    def __repr__(self) -> str:
        return f"DomainRegistry({len(self._domains)} domains)"


# Module-level singleton
REGISTRY: DomainRegistry = DomainRegistry()
