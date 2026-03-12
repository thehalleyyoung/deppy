"""Invariant lowering: @loop_invariant/@class_invariant to site constraints.

This module converts user-facing invariant decorators (``@deppy.loop_invariant``
and ``@deppy.class_invariant``) into *invariant seeds* -- frozen intermediate
representations that attach predicate constraints to internal observation sites
(loop headers, class method boundaries, module boundaries).

The lowering pipeline is:

1. Parse decorator data into ``InvariantSeed`` frozen intermediates.
2. Variant seeds ``LoopInvariantSeed`` and ``ClassInvariantSeed`` carry
   scope-specific metadata (loop variable, class fields, etc.).
3. ``lower_loop_invariant`` and ``lower_class_invariant`` convert
   ``LoopInvariant`` / ``ClassInvariant`` contracts into seeds.
4. ``apply_invariant_to_cover`` enriches a ``Cover`` with invariant-
   constrained sites, induction morphisms, and frame conditions.

Unlike input/output boundary seeds, invariant seeds target *internal* sites
in the site category -- they constrain the local sections at loop headers
and class method entries rather than at function boundaries.
"""

from __future__ import annotations

import enum
import uuid
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
    Union,
)

from deppy.contracts.base import (
    Contract,
    Predicate,
    PredicateKind,
    SourceLocation,
    Term,
    TermKind,
)
from deppy.contracts.invariant import (
    ClassInvariant,
    InvariantContract,
    InvariantKind,
    LoopInvariant,
    ModuleInvariant,
)
from deppy.contracts.seed import BoundarySeed, InputBoundarySeed, OutputBoundarySeed
from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite, CoverBuilder
from deppy.static_analysis.observation_sites import SourceSpan
from deppy.static_analysis.restriction_maps import (
    RestrictionData,
    RestrictionKind,
    make_proof_transport,
    make_witness_flow_restriction,
)
from deppy.types.carriers import CarrierSchema, CarrierType, SchemaConstraint


# ---------------------------------------------------------------------------
# InvariantScope -- where an invariant binds in the site category
# ---------------------------------------------------------------------------


class InvariantScope(enum.Enum):
    """Classification of where invariant constraints attach."""

    LOOP_HEADER = "loop_header"
    LOOP_BACK_EDGE = "loop_back_edge"
    CLASS_INIT_EXIT = "class_init_exit"
    CLASS_METHOD_ENTRY = "class_method_entry"
    CLASS_METHOD_EXIT = "class_method_exit"
    MODULE_INIT = "module_init"
    MODULE_FUNCTION_ENTRY = "module_function_entry"


# ---------------------------------------------------------------------------
# InvariantSeed (base)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class InvariantSeed:
    """Frozen intermediate for a single invariant constraint.

    An invariant seed captures one user-supplied invariant predicate, the
    scope it applies to, and sufficient metadata to emit sites and
    morphisms during cover enrichment.

    Attributes:
        uid: Unique seed identifier.
        predicate: The invariant proposition (contracts-layer Predicate).
        scope_name: Human-readable scope (function name, class name, etc.).
        variables: Free variables referenced by the predicate.
        trust: How the invariant was established.
        source_location: Where the decorator appears in source.
        description: Optional human-readable gloss.
        kind: What scope the invariant covers (LOOP, CLASS, MODULE).
    """

    uid: str = field(default_factory=lambda: uuid.uuid4().hex[:12])
    predicate: Predicate = field(default_factory=Predicate.true_)
    scope_name: str = ""
    variables: Tuple[str, ...] = ()
    trust: TrustLevel = TrustLevel.RESIDUAL
    source_location: Optional[SourceLocation] = None
    description: Optional[str] = None
    kind: InvariantKind = InvariantKind.LOOP

    # -- pretty printing -----------------------------------------------------

    def pretty(self) -> str:
        """Human-readable summary."""
        return (
            f"InvariantSeed({self.kind.value}, scope={self.scope_name!r}, "
            f"vars={self.variables}, trust={self.trust.value})"
        )

    # -- helpers -------------------------------------------------------------

    def with_trust(self, trust: TrustLevel) -> InvariantSeed:
        """Return a copy with a different trust level."""
        return InvariantSeed(
            uid=self.uid,
            predicate=self.predicate,
            scope_name=self.scope_name,
            variables=self.variables,
            trust=trust,
            source_location=self.source_location,
            description=self.description,
            kind=self.kind,
        )

    def with_predicate(self, predicate: Predicate) -> InvariantSeed:
        """Return a copy with a strengthened/replaced predicate."""
        return InvariantSeed(
            uid=self.uid,
            predicate=predicate,
            scope_name=self.scope_name,
            variables=self.variables,
            trust=self.trust,
            source_location=self.source_location,
            description=self.description,
            kind=self.kind,
        )


# ---------------------------------------------------------------------------
# LoopInvariantSeed
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class LoopInvariantSeed(InvariantSeed):
    """Invariant seed specialised for loop headers.

    In addition to the base invariant predicate, a loop invariant seed
    carries the induction variable name, an optional termination measure,
    and a full predicate that conjoins the invariant with the termination
    condition.

    Attributes:
        loop_variable: Induction variable for the loop.
        decreases_term: Optional termination measure as a contracts-layer Term.
        full_predicate: Invariant AND termination (if present).
        back_edge_scope: Scope name for the back-edge site (loop latch).
    """

    loop_variable: Optional[str] = None
    decreases_term: Optional[Term] = None
    full_predicate: Optional[Predicate] = None
    back_edge_scope: Optional[str] = None

    def pretty(self) -> str:
        parts = [f"LoopInvariantSeed(scope={self.scope_name!r}"]
        if self.loop_variable:
            parts.append(f", var={self.loop_variable}")
        if self.decreases_term:
            parts.append(f", decreases={self.decreases_term.pretty()}")
        parts.append(f", trust={self.trust.value})")
        return "".join(parts)


# ---------------------------------------------------------------------------
# ClassInvariantSeed
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ClassInvariantSeed(InvariantSeed):
    """Invariant seed specialised for class invariants.

    A class invariant must be established by ``__init__`` and preserved by
    every public method.  The seed carries the list of fields referenced by
    the predicate and the set of methods that are subject to the invariant.

    Attributes:
        class_name: Fully qualified class name.
        fields_involved: Fields that the invariant references.
        applicable_methods: Methods that must preserve the invariant.
    """

    class_name: str = ""
    fields_involved: Tuple[str, ...] = ()
    applicable_methods: Tuple[str, ...] = ()

    def pretty(self) -> str:
        fields = ", ".join(self.fields_involved) if self.fields_involved else "*"
        return (
            f"ClassInvariantSeed(class={self.class_name!r}, "
            f"fields=[{fields}], trust={self.trust.value})"
        )


# ---------------------------------------------------------------------------
# ModuleInvariantSeed
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ModuleInvariantSeed(InvariantSeed):
    """Invariant seed for module-level invariants.

    A module invariant must hold after module initialisation and be
    preserved by every public function in the module.

    Attributes:
        module_name: Fully qualified module name.
    """

    module_name: str = ""

    def pretty(self) -> str:
        return (
            f"ModuleInvariantSeed(module={self.module_name!r}, "
            f"trust={self.trust.value})"
        )


# ---------------------------------------------------------------------------
# Lowering: LoopInvariant contract -> LoopInvariantSeed
# ---------------------------------------------------------------------------


def lower_loop_invariant(
    contract: LoopInvariant,
    scope_name: str = "",
) -> LoopInvariantSeed:
    """Lower a ``LoopInvariant`` contract into a ``LoopInvariantSeed``.

    Parameters
    ----------
    contract:
        The loop invariant contract from the contract layer.
    scope_name:
        Enclosing function/scope name for context.

    Returns
    -------
    LoopInvariantSeed:
        A frozen seed ready for cover enrichment.
    """
    scope = scope_name or contract.scope or "loop"
    variables = tuple(sorted(contract.predicate.free_variables()))
    full_pred = contract.full_predicate()

    return LoopInvariantSeed(
        predicate=contract.predicate,
        scope_name=scope,
        variables=variables,
        trust=contract.trust,
        source_location=contract.source_location,
        description=contract.description,
        kind=InvariantKind.LOOP,
        loop_variable=contract.loop_variable,
        decreases_term=contract.decreases,
        full_predicate=full_pred,
        back_edge_scope=f"{scope}$back_edge",
    )


# ---------------------------------------------------------------------------
# Lowering: ClassInvariant contract -> ClassInvariantSeed
# ---------------------------------------------------------------------------


def lower_class_invariant(
    contract: ClassInvariant,
    known_methods: Optional[Sequence[str]] = None,
) -> ClassInvariantSeed:
    """Lower a ``ClassInvariant`` contract into a ``ClassInvariantSeed``.

    Parameters
    ----------
    contract:
        The class invariant contract from the contract layer.
    known_methods:
        Optional list of method names in the class.  If provided, only
        those that ``applies_to_method`` returns True for are recorded.

    Returns
    -------
    ClassInvariantSeed:
        A frozen seed ready for cover enrichment.
    """
    variables = tuple(sorted(contract.predicate.free_variables()))
    fields = tuple(contract.fields_involved)

    applicable: Tuple[str, ...] = ()
    if known_methods is not None:
        applicable = tuple(m for m in known_methods if contract.applies_to_method(m))

    return ClassInvariantSeed(
        predicate=contract.predicate,
        scope_name=contract.class_name,
        variables=variables,
        trust=contract.trust,
        source_location=contract.source_location,
        description=contract.description,
        kind=InvariantKind.CLASS,
        class_name=contract.class_name,
        fields_involved=fields,
        applicable_methods=applicable,
    )


# ---------------------------------------------------------------------------
# Lowering: ModuleInvariant contract -> ModuleInvariantSeed
# ---------------------------------------------------------------------------


def lower_module_invariant(
    contract: ModuleInvariant,
) -> ModuleInvariantSeed:
    """Lower a ``ModuleInvariant`` contract into a ``ModuleInvariantSeed``.

    Parameters
    ----------
    contract:
        The module invariant contract from the contract layer.

    Returns
    -------
    ModuleInvariantSeed:
        A frozen seed ready for cover enrichment.
    """
    variables = tuple(sorted(contract.predicate.free_variables()))

    return ModuleInvariantSeed(
        predicate=contract.predicate,
        scope_name=contract.module_name,
        variables=variables,
        trust=contract.trust,
        source_location=contract.source_location,
        description=contract.description,
        kind=InvariantKind.MODULE,
        module_name=contract.module_name,
    )


# ---------------------------------------------------------------------------
# Batch lowering from a ContractSet
# ---------------------------------------------------------------------------


def lower_invariant_contracts(
    contract_set: Any,
    scope_name: str = "",
    known_methods: Optional[Sequence[str]] = None,
) -> List[InvariantSeed]:
    """Lower all invariant contracts in a ``ContractSet`` to seeds.

    Parameters
    ----------
    contract_set:
        A ``ContractSet`` (from ``deppy.contracts.base``) or any object
        with an ``invariants`` attribute that is a list of invariant
        contracts.
    scope_name:
        Enclosing scope name, used as fallback for loop invariant scopes.
    known_methods:
        Optional list of method names for class invariant applicability.

    Returns
    -------
    List[InvariantSeed]:
        All invariant seeds, in declaration order.
    """
    invariants: List[InvariantContract] = getattr(contract_set, "invariants", [])
    seeds: List[InvariantSeed] = []

    for inv in invariants:
        if isinstance(inv, LoopInvariant):
            seeds.append(lower_loop_invariant(inv, scope_name=scope_name))
        elif isinstance(inv, ClassInvariant):
            seeds.append(lower_class_invariant(inv, known_methods=known_methods))
        elif isinstance(inv, ModuleInvariant):
            seeds.append(lower_module_invariant(inv))
        else:
            # Generic InvariantContract -- lower to base seed
            variables = tuple(sorted(inv.predicate.free_variables()))
            seeds.append(
                InvariantSeed(
                    predicate=inv.predicate,
                    scope_name=inv.scope or scope_name,
                    variables=variables,
                    trust=inv.trust,
                    source_location=inv.source_location,
                    description=inv.description,
                    kind=inv.kind,
                )
            )

    return seeds


# ---------------------------------------------------------------------------
# Deduplication
# ---------------------------------------------------------------------------


def deduplicate_invariant_seeds(
    seeds: Sequence[InvariantSeed],
) -> List[InvariantSeed]:
    """Remove duplicate invariant seeds.

    Two seeds are considered duplicates if they have the same scope name,
    kind, and predicate string representation.  When duplicates exist,
    the one with the highest trust level is kept.

    Parameters
    ----------
    seeds:
        Invariant seeds (may contain duplicates).

    Returns
    -------
    List[InvariantSeed]:
        Deduplicated list, preserving first-occurrence order.
    """
    _TRUST_RANK: Dict[TrustLevel, int] = {
        TrustLevel.RESIDUAL: 0,
        TrustLevel.ASSUMED: 1,
        TrustLevel.TRACE_BACKED: 2,
        TrustLevel.BOUNDED_AUTO: 3,
        TrustLevel.TRUSTED_AUTO: 4,
        TrustLevel.PROOF_BACKED: 5,
    }

    seen: Dict[Tuple[str, str, str], InvariantSeed] = {}
    for seed in seeds:
        key = (seed.kind.value, seed.scope_name, seed.predicate.pretty())
        if key in seen:
            existing = seen[key]
            if _TRUST_RANK.get(seed.trust, 0) > _TRUST_RANK.get(existing.trust, 0):
                seen[key] = seed
        else:
            seen[key] = seed

    return list(seen.values())


# ---------------------------------------------------------------------------
# Site construction helpers
# ---------------------------------------------------------------------------


def _make_loop_header_site(
    seed: LoopInvariantSeed,
    func_name: str,
) -> ConcreteSite:
    """Create a loop-header invariant observation site."""
    site_id = SiteId(
        kind=SiteKind.LOOP_HEADER_INVARIANT,
        name=f"{func_name}${seed.scope_name}",
        source_location=(
            (seed.source_location.file, seed.source_location.line, seed.source_location.col)
            if seed.source_location
            else None
        ),
    )
    schema = CarrierSchema(
        name=f"loop_invariant_{seed.scope_name}",
        constraints=(
            SchemaConstraint(
                description=f"Loop invariant for {seed.scope_name}",
                field_names=seed.variables,
            ),
        ),
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={
            "origin": "invariant_lowering",
            "seed_uid": seed.uid,
            "loop_variable": seed.loop_variable,
            "has_decreases": seed.decreases_term is not None,
        },
    )


def _make_loop_back_edge_site(
    seed: LoopInvariantSeed,
    func_name: str,
) -> ConcreteSite:
    """Create a loop back-edge site for induction step verification."""
    site_id = SiteId(
        kind=SiteKind.LOOP_HEADER_INVARIANT,
        name=f"{func_name}${seed.back_edge_scope or seed.scope_name + '$back'}",
        source_location=(
            (seed.source_location.file, seed.source_location.line, seed.source_location.col)
            if seed.source_location
            else None
        ),
    )
    schema = CarrierSchema(
        name=f"loop_back_edge_{seed.scope_name}",
        constraints=(
            SchemaConstraint(
                description=f"Back-edge for {seed.scope_name} induction step",
                field_names=seed.variables,
            ),
        ),
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={
            "origin": "invariant_lowering",
            "seed_uid": seed.uid,
            "is_back_edge": True,
        },
    )


def _make_class_invariant_site(
    seed: ClassInvariantSeed,
    method_name: str,
    is_entry: bool,
) -> ConcreteSite:
    """Create a class-invariant observation site for a method entry/exit."""
    suffix = "entry" if is_entry else "exit"
    site_id = SiteId(
        kind=SiteKind.ARGUMENT_BOUNDARY if is_entry else SiteKind.RETURN_OUTPUT_BOUNDARY,
        name=f"{seed.class_name}.{method_name}${suffix}$inv",
        source_location=(
            (seed.source_location.file, seed.source_location.line, seed.source_location.col)
            if seed.source_location
            else None
        ),
    )
    schema = CarrierSchema(
        name=f"class_inv_{seed.class_name}_{method_name}_{suffix}",
        constraints=(
            SchemaConstraint(
                description=f"Class invariant at {method_name} {suffix}",
                field_names=seed.fields_involved,
            ),
        ),
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={
            "origin": "invariant_lowering",
            "seed_uid": seed.uid,
            "class_name": seed.class_name,
            "method_name": method_name,
            "is_entry": is_entry,
        },
    )


def _make_module_invariant_site(
    seed: ModuleInvariantSeed,
) -> ConcreteSite:
    """Create a module-level invariant observation site."""
    site_id = SiteId(
        kind=SiteKind.MODULE_SUMMARY,
        name=f"{seed.module_name}$inv",
        source_location=(
            (seed.source_location.file, seed.source_location.line, seed.source_location.col)
            if seed.source_location
            else None
        ),
    )
    schema = CarrierSchema(
        name=f"module_inv_{seed.module_name}",
        constraints=(
            SchemaConstraint(
                description=f"Module invariant for {seed.module_name}",
                field_names=seed.variables,
            ),
        ),
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={
            "origin": "invariant_lowering",
            "seed_uid": seed.uid,
            "module_name": seed.module_name,
        },
    )


# ---------------------------------------------------------------------------
# Morphism construction helpers
# ---------------------------------------------------------------------------


def _make_induction_morphism(
    header_site: ConcreteSite,
    back_edge_site: ConcreteSite,
    seed: LoopInvariantSeed,
) -> ConcreteMorphism:
    """Create a morphism from back-edge to header (induction step).

    This restriction map enforces that the invariant predicate at the
    loop latch implies the invariant at the next iteration header.
    """
    return ConcreteMorphism(
        _source=back_edge_site.site_id,
        _target=header_site.site_id,
        _metadata={
            "kind": "induction_step",
            "restriction_kind": RestrictionKind.PROOF_TRANSPORT.value,
            "seed_uid": seed.uid,
            "description": f"Induction step for {seed.scope_name}",
        },
    )


def _make_class_frame_morphism(
    entry_site: ConcreteSite,
    exit_site: ConcreteSite,
    seed: ClassInvariantSeed,
    method_name: str,
) -> ConcreteMorphism:
    """Create a frame morphism from method entry to method exit.

    This restriction map declares that the class invariant must be
    preserved across the method body: I(entry) -> body -> I(exit).
    """
    return ConcreteMorphism(
        _source=entry_site.site_id,
        _target=exit_site.site_id,
        _metadata={
            "kind": "class_invariant_frame",
            "restriction_kind": RestrictionKind.PROOF_TRANSPORT.value,
            "seed_uid": seed.uid,
            "class_name": seed.class_name,
            "method_name": method_name,
            "description": f"Frame condition: {seed.class_name}.{method_name} preserves invariant",
        },
    )


# ---------------------------------------------------------------------------
# apply_invariant_to_cover: loop invariant
# ---------------------------------------------------------------------------


def _apply_loop_invariant(
    seed: LoopInvariantSeed,
    cover: Cover,
    func_name: str,
) -> Cover:
    """Enrich a Cover with loop-invariant sites and morphisms.

    Creates:
    - A loop-header observation site carrying the invariant predicate.
    - A loop back-edge site for the induction step.
    - An induction morphism linking back-edge to header.
    """
    header_site = _make_loop_header_site(seed, func_name)
    back_edge_site = _make_loop_back_edge_site(seed, func_name)
    induction = _make_induction_morphism(header_site, back_edge_site, seed)

    new_sites = dict(cover.sites)
    new_sites[header_site.site_id] = header_site
    new_sites[back_edge_site.site_id] = back_edge_site

    new_morphisms = list(cover.morphisms) + [induction]

    return Cover(
        sites=new_sites,
        morphisms=new_morphisms,
        overlaps=cover.overlaps,
        error_sites=cover.error_sites,
        input_boundary=cover.input_boundary,
        output_boundary=cover.output_boundary,
    )


# ---------------------------------------------------------------------------
# apply_invariant_to_cover: class invariant
# ---------------------------------------------------------------------------


def _apply_class_invariant(
    seed: ClassInvariantSeed,
    cover: Cover,
) -> Cover:
    """Enrich a Cover with class-invariant sites and frame morphisms.

    For each applicable method, creates an entry site and exit site
    both constrained by the class invariant, plus a frame morphism
    linking them.
    """
    new_sites = dict(cover.sites)
    new_morphisms = list(cover.morphisms)

    methods = seed.applicable_methods
    if not methods:
        # Fallback: just create one pair for __init__
        methods = ("__init__",)

    for method_name in methods:
        entry = _make_class_invariant_site(seed, method_name, is_entry=True)
        exit_ = _make_class_invariant_site(seed, method_name, is_entry=False)
        frame = _make_class_frame_morphism(entry, exit_, seed, method_name)

        new_sites[entry.site_id] = entry
        new_sites[exit_.site_id] = exit_
        new_morphisms.append(frame)

    return Cover(
        sites=new_sites,
        morphisms=new_morphisms,
        overlaps=cover.overlaps,
        error_sites=cover.error_sites,
        input_boundary=cover.input_boundary,
        output_boundary=cover.output_boundary,
    )


# ---------------------------------------------------------------------------
# apply_invariant_to_cover: module invariant
# ---------------------------------------------------------------------------


def _apply_module_invariant(
    seed: ModuleInvariantSeed,
    cover: Cover,
) -> Cover:
    """Enrich a Cover with a module-invariant site."""
    site = _make_module_invariant_site(seed)

    new_sites = dict(cover.sites)
    new_sites[site.site_id] = site

    return Cover(
        sites=new_sites,
        morphisms=cover.morphisms,
        overlaps=cover.overlaps,
        error_sites=cover.error_sites,
        input_boundary=cover.input_boundary,
        output_boundary=cover.output_boundary,
    )


# ---------------------------------------------------------------------------
# apply_invariant_to_cover: dispatch
# ---------------------------------------------------------------------------


def apply_invariant_to_cover(
    seed: InvariantSeed,
    cover: Cover,
    func_name: str = "",
) -> Cover:
    """Enrich a ``Cover`` with sites and morphisms for a single invariant seed.

    Dispatches to the appropriate handler based on the seed type:

    - ``LoopInvariantSeed`` -> loop header + back-edge + induction morphism
    - ``ClassInvariantSeed`` -> entry/exit pairs + frame morphisms
    - ``ModuleInvariantSeed`` -> module summary site

    Parameters
    ----------
    seed:
        The invariant seed to install.
    cover:
        The current cover to enrich.
    func_name:
        Enclosing function name (used for site naming).

    Returns
    -------
    Cover:
        A new Cover with invariant sites and morphisms added.
    """
    if isinstance(seed, LoopInvariantSeed):
        return _apply_loop_invariant(seed, cover, func_name)
    elif isinstance(seed, ClassInvariantSeed):
        return _apply_class_invariant(seed, cover)
    elif isinstance(seed, ModuleInvariantSeed):
        return _apply_module_invariant(seed, cover)
    else:
        # Generic invariant: treat as loop-like with a single site
        site_id = SiteId(
            kind=SiteKind.LOOP_HEADER_INVARIANT,
            name=f"{func_name}${seed.scope_name}$generic",
        )
        schema = CarrierSchema(
            name=f"invariant_{seed.scope_name}",
            constraints=(
                SchemaConstraint(
                    description=f"Invariant for {seed.scope_name}",
                    field_names=seed.variables,
                ),
            ),
        )
        site = ConcreteSite(
            _site_id=site_id,
            _carrier_schema=schema,
            _metadata={
                "origin": "invariant_lowering",
                "seed_uid": seed.uid,
            },
        )
        new_sites = dict(cover.sites)
        new_sites[site.site_id] = site
        return Cover(
            sites=new_sites,
            morphisms=cover.morphisms,
            overlaps=cover.overlaps,
            error_sites=cover.error_sites,
            input_boundary=cover.input_boundary,
            output_boundary=cover.output_boundary,
        )


# ---------------------------------------------------------------------------
# Batch application
# ---------------------------------------------------------------------------


def apply_all_invariants(
    seeds: Sequence[InvariantSeed],
    cover: Cover,
    func_name: str = "",
) -> Cover:
    """Apply all invariant seeds to a cover.

    Parameters
    ----------
    seeds:
        All invariant seeds to install.
    cover:
        The initial cover.
    func_name:
        Enclosing function name.

    Returns
    -------
    Cover:
        The cover enriched with all invariant sites and morphisms.
    """
    result = cover
    for seed in seeds:
        result = apply_invariant_to_cover(seed, result, func_name=func_name)
    return result


# ---------------------------------------------------------------------------
# Convenience pipeline
# ---------------------------------------------------------------------------


def lower_and_apply_invariants(
    contract_set: Any,
    cover: Cover,
    func_name: str = "",
    known_methods: Optional[Sequence[str]] = None,
) -> Cover:
    """End-to-end pipeline: extract invariants from a ContractSet and
    install them into a Cover.

    Parameters
    ----------
    contract_set:
        A ``ContractSet`` or compatible object.
    cover:
        The cover to enrich.
    func_name:
        Enclosing function name.
    known_methods:
        Optional list of method names for class invariant applicability.

    Returns
    -------
    Cover:
        The enriched cover.
    """
    seeds = lower_invariant_contracts(
        contract_set,
        scope_name=func_name,
        known_methods=known_methods,
    )
    seeds = deduplicate_invariant_seeds(seeds)
    return apply_all_invariants(seeds, cover, func_name=func_name)
