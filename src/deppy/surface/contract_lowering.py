"""Contract lowering: @requires/@ensures to boundary seeds for the sheaf cover.

This module converts user-facing ``@deppy.requires`` and ``@deppy.ensures``
decorators into *boundary seeds* -- the atomic input/output constraints that
feed into Stage 1 (cover synthesis) of the DepPy pipeline.

The lowering pipeline is:

1. Parse decorator AST data into ``ContractSeed`` intermediates.
2. Split into ``RequiresSeed`` (input boundary) and ``EnsuresSeed`` (output
   boundary) frozen dataclasses.
3. Emit helper functions ``lower_requires`` and ``lower_ensures`` that turn
   predicate ASTs into seed lists.
4. ``apply_seeds_to_cover`` enriches a ``Cover`` with seed-derived sites,
   morphisms, and local sections.

Every seed carries a predicate, target parameters, and a trust level so the
synthesiser can weight them during cover construction.
"""

from __future__ import annotations

import ast
import enum
import hashlib
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
    ContractSet,
    Predicate as ContractPredicate,
    PredicateKind,
    SourceLocation,
    Term,
    TermKind,
)
from deppy.contracts.requires import (
    CompositeRequires,
    ParameterRequirement,
    RequiresContract,
)
from deppy.contracts.ensures import (
    CompositeEnsures,
    EnsuresContract,
    ExceptionalEnsures,
)
from deppy.contracts.seed import (
    BoundarySeed,
    InputBoundarySeed,
    OutputBoundarySeed,
    SeedCollection,
    SeedProvenance,
)
from deppy.core._protocols import (
    BoundarySection,
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite
from deppy.static_analysis.observation_sites import (
    SourceSpan,
    make_argument_boundary_site,
    make_return_boundary_site,
    make_proof_site,
)
from deppy.static_analysis.restriction_maps import (
    RestrictionData,
    RestrictionKind,
    make_input_projection,
    make_output_projection,
)
from deppy.types.carriers import CarrierSchema, SchemaConstraint


# ---------------------------------------------------------------------------
# Trust ordering
# ---------------------------------------------------------------------------

_TRUST_ORD: Dict[TrustLevel, int] = {
    TrustLevel.RESIDUAL: 0,
    TrustLevel.ASSUMED: 1,
    TrustLevel.TRACE_BACKED: 2,
    TrustLevel.BOUNDED_AUTO: 3,
    TrustLevel.TRUSTED_AUTO: 4,
    TrustLevel.PROOF_BACKED: 5,
}


# ---------------------------------------------------------------------------
# SeedOrigin: where the seed came from
# ---------------------------------------------------------------------------

class SeedOrigin(enum.Enum):
    """Tracks how a seed was generated during lowering."""
    DECORATOR_REQUIRES = "decorator_requires"
    DECORATOR_ENSURES = "decorator_ensures"
    DECORATOR_ENSURES_RAISES = "decorator_ensures_raises"
    INFERRED_REQUIRES = "inferred_requires"
    INFERRED_ENSURES = "inferred_ensures"
    LIBRARY_PACK = "library_pack"
    PROOF_TRANSPORT = "proof_transport"


# ---------------------------------------------------------------------------
# ContractSeed: generic intermediate
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ContractSeed:
    """Frozen intermediate form of a lowered contract decorator.

    This is the common ancestor for ``RequiresSeed`` and ``EnsuresSeed``.
    It pairs a predicate with target parameters and a trust level so the
    cover synthesiser can prioritise seeds.

    Attributes:
        predicate: The logical assertion from the contract.
        target_params: Parameter or result names this seed constrains.
        trust: How trustworthy this seed is.
        origin: Where the seed came from.
        source_location: Source span of the original decorator.
        description: Optional human-readable gloss.
        uid: Unique identifier for deduplication.
    """
    predicate: ContractPredicate
    target_params: Tuple[str, ...]
    trust: TrustLevel = TrustLevel.RESIDUAL
    origin: SeedOrigin = SeedOrigin.DECORATOR_REQUIRES
    source_location: Optional[SourceLocation] = None
    description: Optional[str] = None
    uid: str = field(default_factory=lambda: uuid.uuid4().hex[:12])

    @property
    def is_trivial(self) -> bool:
        """True if the predicate contributes no information."""
        return self.predicate.is_trivially_true

    @property
    def free_variables(self) -> FrozenSet[str]:
        """All free variables mentioned in the predicate."""
        return self.predicate.free_variables()

    def with_trust(self, trust: TrustLevel) -> ContractSeed:
        """Return a copy with a different trust level."""
        return ContractSeed(
            predicate=self.predicate,
            target_params=self.target_params,
            trust=trust,
            origin=self.origin,
            source_location=self.source_location,
            description=self.description,
            uid=self.uid,
        )

    def pretty(self) -> str:
        params = ", ".join(self.target_params) if self.target_params else "*"
        desc = f" # {self.description}" if self.description else ""
        return (
            f"ContractSeed({params})[{self.trust.value}/"
            f"{self.origin.value}]: {self.predicate.pretty()}{desc}"
        )

    def __repr__(self) -> str:
        return f"<ContractSeed params={self.target_params!r} trust={self.trust.value}>"


# ---------------------------------------------------------------------------
# RequiresSeed: input boundary seed from @requires
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class RequiresSeed:
    """Frozen seed derived from ``@deppy.requires``.

    Becomes an input boundary section refinement: it constrains one or
    more formal parameters.

    Attributes:
        predicate: The precondition predicate.
        parameter: The parameter name this seed constrains.
        trust: Trust level.
        origin: How the seed was produced.
        source_location: Source code location.
        description: Optional human-readable description.
        requirement_predicate: The requirement expression to attach
            as a refinement.
        uid: Unique identifier.
    """
    predicate: ContractPredicate
    parameter: str
    trust: TrustLevel = TrustLevel.RESIDUAL
    origin: SeedOrigin = SeedOrigin.DECORATOR_REQUIRES
    source_location: Optional[SourceLocation] = None
    description: Optional[str] = None
    requirement_predicate: Optional[ContractPredicate] = None
    uid: str = field(default_factory=lambda: uuid.uuid4().hex[:12])

    @property
    def effective_predicate(self) -> ContractPredicate:
        """The requirement predicate, falling back to the main predicate."""
        return self.requirement_predicate or self.predicate

    @property
    def is_trivial(self) -> bool:
        return self.predicate.is_trivially_true

    def to_input_boundary_seed(self) -> InputBoundarySeed:
        """Convert to the concrete InputBoundarySeed type for seed collection."""
        prov_map: Dict[SeedOrigin, SeedProvenance] = {
            SeedOrigin.DECORATOR_REQUIRES: SeedProvenance.SOURCE_ANNOTATION,
            SeedOrigin.INFERRED_REQUIRES: SeedProvenance.INFERRED,
            SeedOrigin.LIBRARY_PACK: SeedProvenance.LIBRARY_PACK,
            SeedOrigin.PROOF_TRANSPORT: SeedProvenance.PROOF_BACKED,
        }
        prov = prov_map.get(self.origin, SeedProvenance.SOURCE_ANNOTATION)

        return InputBoundarySeed(
            predicate=self.predicate,
            trust=self.trust,
            provenance=prov,
            source_location=self.source_location,
            parameter=self.parameter,
            requirement=self.effective_predicate,
        )

    def to_site_id(self, func_name: str) -> SiteId:
        """Generate a SiteId for this seed's target parameter."""
        loc: Optional[Tuple[str, int, int]] = None
        if self.source_location:
            loc = (
                self.source_location.file,
                self.source_location.line,
                self.source_location.col,
            )
        return SiteId(
            kind=SiteKind.ARGUMENT_BOUNDARY,
            name=f"{func_name}.{self.parameter}",
            source_location=loc,
        )

    def to_local_section(self, func_name: str) -> LocalSection:
        """Create a LocalSection from this seed."""
        sid = self.to_site_id(func_name)
        refinements: Dict[str, Any] = {
            "predicate": self.predicate.pretty(),
            "parameter": self.parameter,
        }
        if self.description:
            refinements["description"] = self.description
        return LocalSection(
            site_id=sid,
            refinements=refinements,
            trust=self.trust,
            provenance=f"requires:{self.origin.value}",
        )

    def pretty(self) -> str:
        desc = f" # {self.description}" if self.description else ""
        return (
            f"RequiresSeed({self.parameter})"
            f"[{self.trust.value}]: {self.predicate.pretty()}{desc}"
        )

    def __repr__(self) -> str:
        return f"<RequiresSeed param={self.parameter!r} trust={self.trust.value}>"


# ---------------------------------------------------------------------------
# EnsuresSeed: output boundary seed from @ensures
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class EnsuresSeed:
    """Frozen seed derived from ``@deppy.ensures``.

    Becomes an output boundary section refinement: it constrains the
    return value or an exceptional path.

    Attributes:
        predicate: The postcondition predicate.
        result_name: Name of the result component (e.g. ``"result"``).
        input_params: Input parameters referenced in the postcondition.
        trust: Trust level.
        origin: How the seed was produced.
        source_location: Source code location.
        description: Optional human-readable description.
        is_exceptional: Whether this constrains an exception path.
        exception_type: Exception class name if exceptional.
        guarantee_predicate: The guarantee expression to attach
            as a refinement.
        uid: Unique identifier.
    """
    predicate: ContractPredicate
    result_name: str = "result"
    input_params: Tuple[str, ...] = ()
    trust: TrustLevel = TrustLevel.RESIDUAL
    origin: SeedOrigin = SeedOrigin.DECORATOR_ENSURES
    source_location: Optional[SourceLocation] = None
    description: Optional[str] = None
    is_exceptional: bool = False
    exception_type: Optional[str] = None
    guarantee_predicate: Optional[ContractPredicate] = None
    uid: str = field(default_factory=lambda: uuid.uuid4().hex[:12])

    @property
    def effective_predicate(self) -> ContractPredicate:
        """The guarantee predicate, falling back to the main predicate."""
        return self.guarantee_predicate or self.predicate

    @property
    def is_trivial(self) -> bool:
        return self.predicate.is_trivially_true

    @property
    def result_component(self) -> str:
        """Result component identifier for seed collection."""
        if self.is_exceptional:
            return f"raises:{self.exception_type or 'Exception'}"
        return self.result_name

    def to_output_boundary_seed(self) -> OutputBoundarySeed:
        """Convert to the concrete OutputBoundarySeed for seed collection."""
        prov_map: Dict[SeedOrigin, SeedProvenance] = {
            SeedOrigin.DECORATOR_ENSURES: SeedProvenance.SOURCE_ANNOTATION,
            SeedOrigin.DECORATOR_ENSURES_RAISES: SeedProvenance.SOURCE_ANNOTATION,
            SeedOrigin.INFERRED_ENSURES: SeedProvenance.INFERRED,
            SeedOrigin.LIBRARY_PACK: SeedProvenance.LIBRARY_PACK,
            SeedOrigin.PROOF_TRANSPORT: SeedProvenance.PROOF_BACKED,
        }
        prov = prov_map.get(self.origin, SeedProvenance.SOURCE_ANNOTATION)

        return OutputBoundarySeed(
            predicate=self.predicate,
            trust=self.trust,
            provenance=prov,
            source_location=self.source_location,
            result_component=self.result_component,
            guarantee=self.effective_predicate,
        )

    def to_site_id(self, func_name: str) -> SiteId:
        """Generate a SiteId for this seed's return site."""
        loc: Optional[Tuple[str, int, int]] = None
        if self.source_location:
            loc = (
                self.source_location.file,
                self.source_location.line,
                self.source_location.col,
            )
        name_suffix = self.result_component
        return SiteId(
            kind=SiteKind.RETURN_OUTPUT_BOUNDARY,
            name=f"{func_name}.{name_suffix}",
            source_location=loc,
        )

    def to_local_section(self, func_name: str) -> LocalSection:
        """Create a LocalSection from this seed."""
        sid = self.to_site_id(func_name)
        refinements: Dict[str, Any] = {
            "predicate": self.predicate.pretty(),
            "result_component": self.result_component,
        }
        if self.input_params:
            refinements["input_params"] = list(self.input_params)
        if self.description:
            refinements["description"] = self.description
        return LocalSection(
            site_id=sid,
            refinements=refinements,
            trust=self.trust,
            provenance=f"ensures:{self.origin.value}",
        )

    def is_relational(self) -> bool:
        """Whether this postcondition relates inputs to outputs."""
        return len(self.input_params) > 0

    def pretty(self) -> str:
        comp = self.result_component
        params = ""
        if self.input_params:
            params = f", params=[{', '.join(self.input_params)}]"
        desc = f" # {self.description}" if self.description else ""
        return (
            f"EnsuresSeed({comp}{params})"
            f"[{self.trust.value}]: {self.predicate.pretty()}{desc}"
        )

    def __repr__(self) -> str:
        return f"<EnsuresSeed comp={self.result_component!r} trust={self.trust.value}>"


# ---------------------------------------------------------------------------
# Lowering functions: predicate AST -> seed lists
# ---------------------------------------------------------------------------

def lower_requires(
    predicate_ast: ContractPredicate,
    params: Sequence[str],
    *,
    trust: TrustLevel = TrustLevel.RESIDUAL,
    origin: SeedOrigin = SeedOrigin.DECORATOR_REQUIRES,
    source_location: Optional[SourceLocation] = None,
    description: Optional[str] = None,
) -> List[RequiresSeed]:
    """Lower a ``@requires`` predicate AST into a list of RequiresSeeds.

    If the predicate mentions specific parameters (detected via free
    variables), one seed per mentioned parameter is emitted.  If no
    specific parameters are detected, one seed per provided parameter
    name is emitted.

    Parameters:
        predicate_ast: The parsed contract predicate.
        params: Names of formal parameters the predicate may constrain.
        trust: Trust level to assign.
        origin: Origin tag for provenance.
        source_location: Source location of the decorator.
        description: Optional human-readable gloss.

    Returns:
        A list of ``RequiresSeed`` instances.
    """
    if predicate_ast.is_trivially_true:
        return []

    fv = predicate_ast.free_variables()
    mentioned_params = [p for p in params if p in fv]

    # If no params detected, broadcast to all provided params
    if not mentioned_params:
        mentioned_params = list(params) if params else ["*"]

    seeds: List[RequiresSeed] = []
    for param in mentioned_params:
        seed = RequiresSeed(
            predicate=predicate_ast,
            parameter=param,
            trust=trust,
            origin=origin,
            source_location=source_location,
            description=description,
            requirement_predicate=predicate_ast,
        )
        seeds.append(seed)

    return seeds


def lower_ensures(
    predicate_ast: ContractPredicate,
    return_name: str = "result",
    *,
    input_params: Sequence[str] = (),
    trust: TrustLevel = TrustLevel.RESIDUAL,
    origin: SeedOrigin = SeedOrigin.DECORATOR_ENSURES,
    source_location: Optional[SourceLocation] = None,
    description: Optional[str] = None,
    is_exceptional: bool = False,
    exception_type: Optional[str] = None,
) -> List[EnsuresSeed]:
    """Lower an ``@ensures`` predicate AST into a list of EnsuresSeeds.

    Typically emits a single seed for the return value, but exceptional
    ensures produce a separate seed for the exception path.

    Parameters:
        predicate_ast: The parsed contract predicate.
        return_name: Name of the result (default ``"result"``).
        input_params: Input parameter names referenced in the postcondition.
        trust: Trust level.
        origin: Origin tag.
        source_location: Source location of the decorator.
        description: Optional gloss.
        is_exceptional: Whether this is an exceptional ensures.
        exception_type: Exception class name if exceptional.

    Returns:
        A list of ``EnsuresSeed`` instances.
    """
    if predicate_ast.is_trivially_true:
        return []

    # Detect which input params are actually mentioned
    fv = predicate_ast.free_variables()
    mentioned_inputs = tuple(p for p in input_params if p in fv)

    if is_exceptional:
        eff_origin = SeedOrigin.DECORATOR_ENSURES_RAISES
    else:
        eff_origin = origin

    seed = EnsuresSeed(
        predicate=predicate_ast,
        result_name=return_name,
        input_params=mentioned_inputs,
        trust=trust,
        origin=eff_origin,
        source_location=source_location,
        description=description,
        is_exceptional=is_exceptional,
        exception_type=exception_type,
        guarantee_predicate=predicate_ast,
    )
    return [seed]


# ---------------------------------------------------------------------------
# Lower from RequiresContract / EnsuresContract
# ---------------------------------------------------------------------------

def lower_requires_contract(
    contract: RequiresContract,
    func_params: Sequence[str],
) -> List[RequiresSeed]:
    """Lower a ``RequiresContract`` into seeds for each target parameter.

    Parameters:
        contract: The requires contract to lower.
        func_params: All formal parameter names of the function.

    Returns:
        A list of ``RequiresSeed`` instances.
    """
    prov_map: Dict[str, SeedOrigin] = {
        "user_annotation": SeedOrigin.DECORATOR_REQUIRES,
        "synthesized": SeedOrigin.INFERRED_REQUIRES,
        "proof_backed": SeedOrigin.PROOF_TRANSPORT,
        "inferred": SeedOrigin.INFERRED_REQUIRES,
        "library_pack": SeedOrigin.LIBRARY_PACK,
    }
    origin = prov_map.get(contract.provenance, SeedOrigin.DECORATOR_REQUIRES)

    return lower_requires(
        predicate_ast=contract.predicate,
        params=contract.parameters if contract.parameters else list(func_params),
        trust=contract.trust,
        origin=origin,
        source_location=contract.source_location,
        description=contract.description,
    )


def lower_ensures_contract(
    contract: EnsuresContract,
    func_params: Sequence[str],
) -> List[EnsuresSeed]:
    """Lower an ``EnsuresContract`` into seeds.

    Parameters:
        contract: The ensures contract to lower.
        func_params: All formal parameter names of the function.

    Returns:
        A list of ``EnsuresSeed`` instances.
    """
    prov_map: Dict[str, SeedOrigin] = {
        "user_annotation": SeedOrigin.DECORATOR_ENSURES,
        "synthesized": SeedOrigin.INFERRED_ENSURES,
        "proof_backed": SeedOrigin.PROOF_TRANSPORT,
        "inferred": SeedOrigin.INFERRED_ENSURES,
        "library_pack": SeedOrigin.LIBRARY_PACK,
    }
    origin = prov_map.get(contract.provenance, SeedOrigin.DECORATOR_ENSURES)

    return lower_ensures(
        predicate_ast=contract.predicate,
        return_name=contract.result_name,
        input_params=contract.parameters if contract.parameters else list(func_params),
        trust=contract.trust,
        origin=origin,
        source_location=contract.source_location,
        description=contract.description,
        is_exceptional=contract.is_exceptional,
        exception_type=contract.exception_type,
    )


def lower_exceptional_ensures(
    contract: ExceptionalEnsures,
) -> List[EnsuresSeed]:
    """Lower an ``ExceptionalEnsures`` into seeds."""
    pred = contract.to_predicate()
    return lower_ensures(
        predicate_ast=pred,
        return_name="exception",
        trust=contract.trust,
        origin=SeedOrigin.DECORATOR_ENSURES_RAISES,
        source_location=contract.source_location,
        description=contract.description,
        is_exceptional=True,
        exception_type=contract.exception_type,
    )


# ---------------------------------------------------------------------------
# Lower an entire ContractSet
# ---------------------------------------------------------------------------

def lower_contract_set(
    contract_set: ContractSet,
    func_name: str,
    func_params: Sequence[str],
) -> Tuple[List[RequiresSeed], List[EnsuresSeed]]:
    """Lower all contracts in a ``ContractSet`` into require/ensure seeds.

    Parameters:
        contract_set: The set of contracts attached to a function.
        func_name: The function name (for provenance).
        func_params: The function's formal parameter names.

    Returns:
        A tuple of ``(requires_seeds, ensures_seeds)``.
    """
    requires_seeds: List[RequiresSeed] = []
    ensures_seeds: List[EnsuresSeed] = []

    for req in contract_set.requires:
        if isinstance(req, RequiresContract):
            requires_seeds.extend(lower_requires_contract(req, func_params))

    for ens in contract_set.ensures:
        if isinstance(ens, EnsuresContract):
            ensures_seeds.extend(lower_ensures_contract(ens, func_params))
        elif isinstance(ens, ExceptionalEnsures):
            ensures_seeds.extend(lower_exceptional_ensures(ens))

    return requires_seeds, ensures_seeds


# ---------------------------------------------------------------------------
# Seed deduplication
# ---------------------------------------------------------------------------

def _seed_key_requires(seed: RequiresSeed) -> Tuple[str, str]:
    """Deduplication key for requires seeds."""
    return (seed.parameter, seed.predicate.pretty())


def _seed_key_ensures(seed: EnsuresSeed) -> Tuple[str, str]:
    """Deduplication key for ensures seeds."""
    return (seed.result_component, seed.predicate.pretty())


def deduplicate_requires(seeds: List[RequiresSeed]) -> List[RequiresSeed]:
    """Remove duplicate requires seeds, keeping the highest trust."""
    best: Dict[Tuple[str, str], RequiresSeed] = {}
    for s in seeds:
        key = _seed_key_requires(s)
        existing = best.get(key)
        if existing is None or _TRUST_ORD.get(s.trust, 0) > _TRUST_ORD.get(existing.trust, 0):
            best[key] = s
    return list(best.values())


def deduplicate_ensures(seeds: List[EnsuresSeed]) -> List[EnsuresSeed]:
    """Remove duplicate ensures seeds, keeping the highest trust."""
    best: Dict[Tuple[str, str], EnsuresSeed] = {}
    for s in seeds:
        key = _seed_key_ensures(s)
        existing = best.get(key)
        if existing is None or _TRUST_ORD.get(s.trust, 0) > _TRUST_ORD.get(existing.trust, 0):
            best[key] = s
    return list(best.values())


# ---------------------------------------------------------------------------
# Seeds -> SeedCollection
# ---------------------------------------------------------------------------

def seeds_to_collection(
    requires_seeds: Sequence[RequiresSeed],
    ensures_seeds: Sequence[EnsuresSeed],
) -> SeedCollection:
    """Convert lowered seeds into a ``SeedCollection``."""
    collection = SeedCollection()
    for rs in requires_seeds:
        if not rs.is_trivial:
            collection.add_input(rs.to_input_boundary_seed())
    for es in ensures_seeds:
        if not es.is_trivial:
            collection.add_output(es.to_output_boundary_seed())
    return collection


# ---------------------------------------------------------------------------
# apply_seeds_to_cover: enrich a Cover with seed-derived sites
# ---------------------------------------------------------------------------

def _make_seed_schema(label: str, description: str) -> CarrierSchema:
    """Create a carrier schema for a seed-derived site."""
    return CarrierSchema(
        name=f"seed:{label}",
        constraints=(
            SchemaConstraint(
                description=description,
                field_names=("predicate",),
            ),
        ),
    )


def apply_seeds_to_cover(
    requires_seeds: Sequence[RequiresSeed],
    ensures_seeds: Sequence[EnsuresSeed],
    cover: Cover,
    func_name: str,
    *,
    source_file: str = "<unknown>",
) -> Cover:
    """Enrich *cover* with sites and sections derived from boundary seeds.

    For each requires seed, an argument-boundary site is created (if not
    already present) and a local section with the predicate refinement
    is installed.  For each ensures seed, a return-boundary site is
    created and similarly populated.

    Morphisms are added between seed-derived sites and the corresponding
    interior sites to enable sheaf gluing during descent.

    Parameters:
        requires_seeds: Input-boundary seeds to install.
        ensures_seeds: Output-boundary seeds to install.
        cover: The existing cover to enrich (not mutated; a new one is
            returned).
        func_name: Name of the function being analysed.
        source_file: Source file path for span construction.

    Returns:
        A new ``Cover`` with additional sites, morphisms, and boundary
        markers from the seeds.
    """
    # Work on copies of the mutable fields
    new_sites: Dict[SiteId, Any] = dict(cover.sites)
    new_morphisms: List[Any] = list(cover.morphisms)
    new_overlaps: List[Tuple[SiteId, SiteId]] = list(cover.overlaps)
    new_error_sites: Set[SiteId] = set(cover.error_sites)
    new_input_boundary: Set[SiteId] = set(cover.input_boundary)
    new_output_boundary: Set[SiteId] = set(cover.output_boundary)

    # -- requires seeds -> argument boundary sites --------------------------

    for seed in requires_seeds:
        if seed.is_trivial:
            continue

        sid = seed.to_site_id(func_name)

        if sid not in new_sites:
            loc = seed.source_location
            span = SourceSpan(
                file=loc.file if loc else source_file,
                start_line=loc.line if loc else 0,
                start_col=loc.col if loc else 0,
            )
            site = make_argument_boundary_site(
                func_name=func_name,
                param_name=seed.parameter,
                param_index=0,
                span=span,
            )
            new_sites[sid] = site

        new_input_boundary.add(sid)

    # -- ensures seeds -> return boundary sites -----------------------------

    for seed in ensures_seeds:
        if seed.is_trivial:
            continue

        sid = seed.to_site_id(func_name)

        if sid not in new_sites:
            loc = seed.source_location
            span = SourceSpan(
                file=loc.file if loc else source_file,
                start_line=loc.line if loc else 0,
                start_col=loc.col if loc else 0,
            )
            site = make_return_boundary_site(
                func_name=func_name,
                span=span,
                is_exceptional=seed.is_exceptional,
                exception_type=seed.exception_type,
            )
            new_sites[sid] = site

        new_output_boundary.add(sid)

    # -- connect boundary sites with input/output projections ---------------

    existing_interior_ids = set(cover.sites.keys()) - cover.input_boundary - cover.output_boundary
    for interior_id in existing_interior_ids:
        for input_id in (new_input_boundary - cover.input_boundary):
            if interior_id.kind == SiteKind.SSA_VALUE:
                morph = make_input_projection(interior_id, input_id)
                new_morphisms.append(morph)
                pair = (interior_id, input_id)
                rpair = (input_id, interior_id)
                if pair not in new_overlaps and rpair not in new_overlaps:
                    new_overlaps.append(pair)
                break  # one connection per new input site is enough

        for output_id in (new_output_boundary - cover.output_boundary):
            if interior_id.kind == SiteKind.SSA_VALUE:
                morph = make_output_projection(interior_id, output_id)
                new_morphisms.append(morph)
                pair = (interior_id, output_id)
                rpair = (output_id, interior_id)
                if pair not in new_overlaps and rpair not in new_overlaps:
                    new_overlaps.append(pair)
                break

    return Cover(
        sites=new_sites,
        morphisms=new_morphisms,
        overlaps=new_overlaps,
        error_sites=new_error_sites,
        input_boundary=new_input_boundary,
        output_boundary=new_output_boundary,
    )


# ---------------------------------------------------------------------------
# Convenience: full contract-lowering pipeline
# ---------------------------------------------------------------------------

def lower_and_apply(
    contract_set: ContractSet,
    cover: Cover,
    func_name: str,
    func_params: Sequence[str],
    *,
    source_file: str = "<unknown>",
    deduplicate: bool = True,
) -> Tuple[Cover, List[RequiresSeed], List[EnsuresSeed]]:
    """Full pipeline: lower contracts and apply seeds to the cover.

    Parameters:
        contract_set: Contracts attached to a function.
        cover: The existing cover to enrich.
        func_name: Function name.
        func_params: Formal parameter names.
        source_file: Source file path.
        deduplicate: Whether to deduplicate seeds.

    Returns:
        A tuple of ``(enriched_cover, requires_seeds, ensures_seeds)``.
    """
    requires_seeds, ensures_seeds = lower_contract_set(
        contract_set, func_name, func_params,
    )

    if deduplicate:
        requires_seeds = deduplicate_requires(requires_seeds)
        ensures_seeds = deduplicate_ensures(ensures_seeds)

    enriched = apply_seeds_to_cover(
        requires_seeds, ensures_seeds, cover, func_name,
        source_file=source_file,
    )

    return enriched, requires_seeds, ensures_seeds
