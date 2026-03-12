"""Proof-surface elaboration pipeline.

This module orchestrates the full proof-surface lowering: given an AST
tree (or a ``ContractSet`` collected from decorators) and an initial
``Cover``, the ``ProofSurface`` class runs every lowering pass in the
correct order and returns an enriched ``Cover`` ready for descent
checking.

Pipeline stages (executed in order):

1. **Contract lowering** -- @requires/@ensures to boundary seeds.
2. **Theorem lowering** -- @theorem/@lemma to proof sites + transport maps.
3. **Witness lowering** -- witness declarations to witness carriers.
4. **Invariant lowering** -- @loop_invariant/@class_invariant to site constraints.
5. **Decreases lowering** -- @decreases to ranking-function sites.
6. **Seed deduplication** -- remove redundant seeds across passes.
7. **Cover assembly** -- merge all sites, morphisms, and overlaps.

The ``ProofSurface`` is the single entry point that higher-level
pipeline stages (``deppy.pipeline``) call into.
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
    ContractSet,
    Predicate,
    SourceLocation,
    Term,
)
from deppy.contracts.invariant import (
    ClassInvariant,
    InvariantContract,
    LoopInvariant,
    ModuleInvariant,
)
from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite, CoverBuilder

# Import all lowering passes
from deppy.surface.contract_lowering import (
    EnsuresSeed,
    RequiresSeed,
    apply_seeds_to_cover,
    deduplicate_ensures,
    deduplicate_requires,
    lower_contract_set,
    seeds_to_collection,
)
from deppy.surface.decreases_lowering import (
    DecreasesSeed,
    create_all_ranking_sites,
    extract_decreases_seeds,
)
from deppy.surface.invariant_lowering import (
    ClassInvariantSeed,
    InvariantSeed,
    LoopInvariantSeed,
    ModuleInvariantSeed,
    apply_all_invariants,
    deduplicate_invariant_seeds,
    lower_invariant_contracts,
)
from deppy.surface.theorem_lowering import (
    LemmaSeed,
    ProofTransportSeed,
    TheoremSeed,
    create_proof_sites,
    lower_theorem_contracts,
)
from deppy.surface.witness_lowering import (
    WitnessSeed,
    inject_all_witnesses,
    lower_witness_contracts,
)


# ---------------------------------------------------------------------------
# ElaborationStage -- pipeline stage identifiers
# ---------------------------------------------------------------------------


class ElaborationStage(enum.Enum):
    """Identifiers for the stages in the elaboration pipeline."""

    CONTRACT_LOWERING = "contract_lowering"
    THEOREM_LOWERING = "theorem_lowering"
    WITNESS_LOWERING = "witness_lowering"
    INVARIANT_LOWERING = "invariant_lowering"
    DECREASES_LOWERING = "decreases_lowering"
    DEDUPLICATION = "deduplication"
    COVER_ASSEMBLY = "cover_assembly"


# ---------------------------------------------------------------------------
# ElaborationResult -- outcome of one pipeline run
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ElaborationResult:
    """Frozen result of proof-surface elaboration.

    Captures the enriched cover together with all intermediate seeds and
    diagnostics produced during the elaboration pipeline.

    Attributes:
        cover: The final enriched cover.
        requires_seeds: All requires seeds emitted during contract lowering.
        ensures_seeds: All ensures seeds emitted during contract lowering.
        theorem_seeds: All theorem seeds emitted during theorem lowering.
        lemma_seeds: All lemma seeds emitted during theorem lowering.
        transport_seeds: All transport seeds emitted during theorem lowering.
        witness_seeds: All witness seeds emitted during witness lowering.
        invariant_seeds: All invariant seeds emitted during invariant lowering.
        decreases_seeds: All decreases seeds emitted during decreases lowering.
        stages_completed: Which pipeline stages ran successfully.
        diagnostics: Any warnings or informational messages.
        sites_added: Count of new sites added to the cover.
        morphisms_added: Count of new morphisms added to the cover.
    """

    cover: Cover
    requires_seeds: Tuple[RequiresSeed, ...] = ()
    ensures_seeds: Tuple[EnsuresSeed, ...] = ()
    theorem_seeds: Tuple[TheoremSeed, ...] = ()
    lemma_seeds: Tuple[LemmaSeed, ...] = ()
    transport_seeds: Tuple[ProofTransportSeed, ...] = ()
    witness_seeds: Tuple[WitnessSeed, ...] = ()
    invariant_seeds: Tuple[InvariantSeed, ...] = ()
    decreases_seeds: Tuple[DecreasesSeed, ...] = ()
    stages_completed: Tuple[ElaborationStage, ...] = ()
    diagnostics: Tuple[str, ...] = ()
    sites_added: int = 0
    morphisms_added: int = 0


# ---------------------------------------------------------------------------
# ElaborationConfig -- configuration for the elaboration pipeline
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ElaborationConfig:
    """Configuration knobs for the proof-surface elaboration pipeline.

    Attributes:
        enable_contracts: Whether to run contract lowering.
        enable_theorems: Whether to run theorem lowering.
        enable_witnesses: Whether to run witness lowering.
        enable_invariants: Whether to run invariant lowering.
        enable_decreases: Whether to run decreases lowering.
        deduplicate: Whether to run seed deduplication.
        default_trust: Default trust level for seeds without explicit trust.
        known_methods: Method names for class invariant applicability.
        strict_mode: If True, halt on the first stage error.
        max_sites: Maximum number of sites to add (0 = unlimited).
    """

    enable_contracts: bool = True
    enable_theorems: bool = True
    enable_witnesses: bool = True
    enable_invariants: bool = True
    enable_decreases: bool = True
    deduplicate: bool = True
    default_trust: TrustLevel = TrustLevel.RESIDUAL
    known_methods: Optional[Tuple[str, ...]] = None
    strict_mode: bool = False
    max_sites: int = 0


# ---------------------------------------------------------------------------
# ProofSurface -- the orchestrator
# ---------------------------------------------------------------------------


class ProofSurface:
    """Full proof-surface elaboration pipeline.

    The ``ProofSurface`` orchestrates all lowering passes in the correct
    order, threading the ``Cover`` through each stage.  It is the single
    entry point for higher-level pipeline stages.

    Usage::

        surface = ProofSurface(config=ElaborationConfig())
        result = surface.elaborate(contract_set, cover, func_name="foo")
        enriched_cover = result.cover

    The class is stateless between calls to ``elaborate``; all
    intermediate results are captured in the returned
    ``ElaborationResult``.
    """

    def __init__(
        self,
        config: Optional[ElaborationConfig] = None,
    ) -> None:
        self._config = config or ElaborationConfig()

    @property
    def config(self) -> ElaborationConfig:
        """The current elaboration configuration."""
        return self._config

    # -- Main entry point ----------------------------------------------------

    def elaborate(
        self,
        contract_set: Any,
        cover: Cover,
        func_name: str = "",
        func_params: Optional[Sequence[str]] = None,
    ) -> ElaborationResult:
        """Run the full proof-surface elaboration pipeline.

        Parameters
        ----------
        contract_set:
            A ``ContractSet`` (from ``deppy.contracts.base``) or any
            compatible object with ``requires``, ``ensures``,
            ``invariants``, ``witnesses``, ``theorems`` attributes.
        cover:
            The initial cover to enrich.
        func_name:
            Enclosing function name (used for site naming).
        func_params:
            Parameter names of the enclosing function.

        Returns
        -------
        ElaborationResult:
            The enriched cover and all intermediate seeds.
        """
        params = list(func_params) if func_params else []
        stages: List[ElaborationStage] = []
        diagnostics: List[str] = []
        initial_site_count = len(cover.sites)
        initial_morph_count = len(cover.morphisms)

        # Accumulators for intermediate seeds
        all_requires: List[RequiresSeed] = []
        all_ensures: List[EnsuresSeed] = []
        all_theorems: List[TheoremSeed] = []
        all_lemmas: List[LemmaSeed] = []
        all_transports: List[ProofTransportSeed] = []
        all_witnesses: List[WitnessSeed] = []
        all_invariants: List[InvariantSeed] = []
        all_decreases: List[DecreasesSeed] = []

        current_cover = cover

        # -- Stage 1: Contract lowering --------------------------------------
        if self._config.enable_contracts:
            try:
                requires_seeds, ensures_seeds = lower_contract_set(
                    contract_set, func_name=func_name, func_params=params,
                )
                if self._config.deduplicate:
                    requires_seeds = deduplicate_requires(requires_seeds)
                    ensures_seeds = deduplicate_ensures(ensures_seeds)

                all_requires.extend(requires_seeds)
                all_ensures.extend(ensures_seeds)

                current_cover = apply_seeds_to_cover(
                    requires_seeds, ensures_seeds, current_cover, func_name=func_name,
                )
                stages.append(ElaborationStage.CONTRACT_LOWERING)
                diagnostics.append(
                    f"Contract lowering: {len(requires_seeds)} requires, "
                    f"{len(ensures_seeds)} ensures"
                )
            except Exception as exc:
                diagnostics.append(f"Contract lowering failed: {exc}")
                if self._config.strict_mode:
                    return self._make_result(
                        current_cover, stages, diagnostics,
                        all_requires, all_ensures, all_theorems, all_lemmas,
                        all_transports, all_witnesses, all_invariants, all_decreases,
                        initial_site_count, initial_morph_count,
                    )

        # -- Stage 2: Theorem lowering ---------------------------------------
        if self._config.enable_theorems:
            try:
                theorem_seeds, lemma_seeds, thm_morphisms, transport_seeds = (
                    lower_theorem_contracts(contract_set)
                )
                all_theorems.extend(theorem_seeds)
                all_lemmas.extend(lemma_seeds)
                all_transports.extend(transport_seeds)

                current_cover = create_proof_sites(
                    theorem_seeds, lemma_seeds, thm_morphisms, transport_seeds,
                    current_cover,
                )
                stages.append(ElaborationStage.THEOREM_LOWERING)
                diagnostics.append(
                    f"Theorem lowering: {len(theorem_seeds)} theorems, "
                    f"{len(lemma_seeds)} lemmas, {len(transport_seeds)} transports"
                )
            except Exception as exc:
                diagnostics.append(f"Theorem lowering failed: {exc}")
                if self._config.strict_mode:
                    return self._make_result(
                        current_cover, stages, diagnostics,
                        all_requires, all_ensures, all_theorems, all_lemmas,
                        all_transports, all_witnesses, all_invariants, all_decreases,
                        initial_site_count, initial_morph_count,
                    )

        # -- Stage 3: Witness lowering ---------------------------------------
        if self._config.enable_witnesses:
            try:
                witness_seeds = lower_witness_contracts(contract_set, func_name=func_name)
                all_witnesses.extend(witness_seeds)

                current_cover = inject_all_witnesses(
                    witness_seeds, current_cover, func_name=func_name,
                )
                stages.append(ElaborationStage.WITNESS_LOWERING)
                diagnostics.append(f"Witness lowering: {len(witness_seeds)} witnesses")
            except Exception as exc:
                diagnostics.append(f"Witness lowering failed: {exc}")
                if self._config.strict_mode:
                    return self._make_result(
                        current_cover, stages, diagnostics,
                        all_requires, all_ensures, all_theorems, all_lemmas,
                        all_transports, all_witnesses, all_invariants, all_decreases,
                        initial_site_count, initial_morph_count,
                    )

        # -- Stage 4: Invariant lowering -------------------------------------
        if self._config.enable_invariants:
            try:
                known_methods = (
                    list(self._config.known_methods)
                    if self._config.known_methods
                    else None
                )
                invariant_seeds = lower_invariant_contracts(
                    contract_set,
                    scope_name=func_name,
                    known_methods=known_methods,
                )
                if self._config.deduplicate:
                    invariant_seeds = deduplicate_invariant_seeds(invariant_seeds)

                all_invariants.extend(invariant_seeds)

                current_cover = apply_all_invariants(
                    invariant_seeds, current_cover, func_name=func_name,
                )
                stages.append(ElaborationStage.INVARIANT_LOWERING)
                diagnostics.append(f"Invariant lowering: {len(invariant_seeds)} invariants")
            except Exception as exc:
                diagnostics.append(f"Invariant lowering failed: {exc}")
                if self._config.strict_mode:
                    return self._make_result(
                        current_cover, stages, diagnostics,
                        all_requires, all_ensures, all_theorems, all_lemmas,
                        all_transports, all_witnesses, all_invariants, all_decreases,
                        initial_site_count, initial_morph_count,
                    )

        # -- Stage 5: Decreases lowering -------------------------------------
        if self._config.enable_decreases:
            try:
                decreases_seeds = extract_decreases_seeds(
                    contract_set, scope_name=func_name,
                )
                all_decreases.extend(decreases_seeds)

                # Try to link ranking sites to loop-header sites
                header_map = self._find_loop_header_sites(current_cover, func_name)

                current_cover = create_all_ranking_sites(
                    decreases_seeds, current_cover,
                    func_name=func_name,
                    loop_header_site_ids=header_map,
                )
                stages.append(ElaborationStage.DECREASES_LOWERING)
                diagnostics.append(
                    f"Decreases lowering: {len(decreases_seeds)} ranking functions"
                )
            except Exception as exc:
                diagnostics.append(f"Decreases lowering failed: {exc}")
                if self._config.strict_mode:
                    return self._make_result(
                        current_cover, stages, diagnostics,
                        all_requires, all_ensures, all_theorems, all_lemmas,
                        all_transports, all_witnesses, all_invariants, all_decreases,
                        initial_site_count, initial_morph_count,
                    )

        # -- Stage 6: Deduplication (already done per-stage if enabled) ------
        stages.append(ElaborationStage.DEDUPLICATION)

        # -- Stage 7: Cover assembly (already accumulated) -------------------
        stages.append(ElaborationStage.COVER_ASSEMBLY)

        # -- Check max_sites limit -------------------------------------------
        if self._config.max_sites > 0:
            sites_added = len(current_cover.sites) - initial_site_count
            if sites_added > self._config.max_sites:
                diagnostics.append(
                    f"Warning: {sites_added} sites added exceeds max_sites "
                    f"({self._config.max_sites})"
                )

        return self._make_result(
            current_cover, stages, diagnostics,
            all_requires, all_ensures, all_theorems, all_lemmas,
            all_transports, all_witnesses, all_invariants, all_decreases,
            initial_site_count, initial_morph_count,
        )

    # -- Helper: find loop-header sites in the current cover -----------------

    @staticmethod
    def _find_loop_header_sites(
        cover: Cover,
        func_name: str,
    ) -> Dict[str, SiteId]:
        """Scan the cover for loop-header invariant sites and build a
        scope-name -> SiteId mapping.

        This heuristic matches sites whose kind is LOOP_HEADER_INVARIANT
        and whose name starts with the enclosing function prefix.
        """
        header_map: Dict[str, SiteId] = {}
        prefix = f"{func_name}$" if func_name else ""

        for site_id, site in cover.sites.items():
            if site_id.kind == SiteKind.LOOP_HEADER_INVARIANT:
                name = site_id.name
                if prefix and name.startswith(prefix):
                    scope = name[len(prefix):]
                    # Strip trailing $back_edge if present
                    if "$back" not in scope:
                        header_map[scope] = site_id
                elif not prefix:
                    header_map[name] = site_id

        return header_map

    # -- Helper: assemble the ElaborationResult ------------------------------

    @staticmethod
    def _make_result(
        cover: Cover,
        stages: List[ElaborationStage],
        diagnostics: List[str],
        requires_seeds: List[RequiresSeed],
        ensures_seeds: List[EnsuresSeed],
        theorem_seeds: List[TheoremSeed],
        lemma_seeds: List[LemmaSeed],
        transport_seeds: List[ProofTransportSeed],
        witness_seeds: List[WitnessSeed],
        invariant_seeds: List[InvariantSeed],
        decreases_seeds: List[DecreasesSeed],
        initial_site_count: int,
        initial_morph_count: int,
    ) -> ElaborationResult:
        """Build a frozen ElaborationResult from mutable accumulators."""
        return ElaborationResult(
            cover=cover,
            requires_seeds=tuple(requires_seeds),
            ensures_seeds=tuple(ensures_seeds),
            theorem_seeds=tuple(theorem_seeds),
            lemma_seeds=tuple(lemma_seeds),
            transport_seeds=tuple(transport_seeds),
            witness_seeds=tuple(witness_seeds),
            invariant_seeds=tuple(invariant_seeds),
            decreases_seeds=tuple(decreases_seeds),
            stages_completed=tuple(stages),
            diagnostics=tuple(diagnostics),
            sites_added=len(cover.sites) - initial_site_count,
            morphisms_added=len(cover.morphisms) - initial_morph_count,
        )


# ---------------------------------------------------------------------------
# Module-level convenience function
# ---------------------------------------------------------------------------


def elaborate(
    contract_set: Any,
    cover: Cover,
    func_name: str = "",
    func_params: Optional[Sequence[str]] = None,
    config: Optional[ElaborationConfig] = None,
) -> Cover:
    """One-shot proof-surface elaboration: returns just the enriched Cover.

    This is the simplest entry point.  For access to intermediate seeds
    and diagnostics, use ``ProofSurface.elaborate`` directly.

    Parameters
    ----------
    contract_set:
        A ``ContractSet`` or compatible object.
    cover:
        The initial cover to enrich.
    func_name:
        Enclosing function name.
    func_params:
        Parameter names of the enclosing function.
    config:
        Optional elaboration configuration.

    Returns
    -------
    Cover:
        The enriched cover with all proof-surface sites and morphisms.
    """
    surface = ProofSurface(config=config)
    result = surface.elaborate(contract_set, cover, func_name=func_name, func_params=func_params)
    return result.cover


def elaborate_full(
    contract_set: Any,
    cover: Cover,
    func_name: str = "",
    func_params: Optional[Sequence[str]] = None,
    config: Optional[ElaborationConfig] = None,
) -> ElaborationResult:
    """One-shot proof-surface elaboration: returns the full result.

    Parameters
    ----------
    contract_set:
        A ``ContractSet`` or compatible object.
    cover:
        The initial cover to enrich.
    func_name:
        Enclosing function name.
    func_params:
        Parameter names of the enclosing function.
    config:
        Optional elaboration configuration.

    Returns
    -------
    ElaborationResult:
        The enriched cover, all intermediate seeds, and diagnostics.
    """
    surface = ProofSurface(config=config)
    return surface.elaborate(contract_set, cover, func_name=func_name, func_params=func_params)


# ---------------------------------------------------------------------------
# Selective elaboration: run only specific stages
# ---------------------------------------------------------------------------


def elaborate_contracts_only(
    contract_set: Any,
    cover: Cover,
    func_name: str = "",
    func_params: Optional[Sequence[str]] = None,
) -> Cover:
    """Run only contract lowering (@requires/@ensures).

    Parameters
    ----------
    contract_set:
        A ``ContractSet`` or compatible object.
    cover:
        The initial cover.
    func_name:
        Enclosing function name.
    func_params:
        Parameter names.

    Returns
    -------
    Cover:
        Cover with only contract-derived sites.
    """
    config = ElaborationConfig(
        enable_contracts=True,
        enable_theorems=False,
        enable_witnesses=False,
        enable_invariants=False,
        enable_decreases=False,
    )
    return elaborate(contract_set, cover, func_name, func_params, config)


def elaborate_proofs_only(
    contract_set: Any,
    cover: Cover,
    func_name: str = "",
) -> Cover:
    """Run only theorem + witness lowering.

    Parameters
    ----------
    contract_set:
        A ``ContractSet`` or compatible object.
    cover:
        The initial cover.
    func_name:
        Enclosing function name.

    Returns
    -------
    Cover:
        Cover with only proof-derived sites.
    """
    config = ElaborationConfig(
        enable_contracts=False,
        enable_theorems=True,
        enable_witnesses=True,
        enable_invariants=False,
        enable_decreases=False,
    )
    return elaborate(contract_set, cover, func_name, config=config)


def elaborate_invariants_only(
    contract_set: Any,
    cover: Cover,
    func_name: str = "",
    known_methods: Optional[Sequence[str]] = None,
) -> Cover:
    """Run only invariant + decreases lowering.

    Parameters
    ----------
    contract_set:
        A ``ContractSet`` or compatible object.
    cover:
        The initial cover.
    func_name:
        Enclosing function name.
    known_methods:
        Optional method names for class invariant applicability.

    Returns
    -------
    Cover:
        Cover with only invariant-derived sites.
    """
    km: Optional[Tuple[str, ...]] = tuple(known_methods) if known_methods else None
    config = ElaborationConfig(
        enable_contracts=False,
        enable_theorems=False,
        enable_witnesses=False,
        enable_invariants=True,
        enable_decreases=True,
        known_methods=km,
    )
    return elaborate(contract_set, cover, func_name, config=config)


# ---------------------------------------------------------------------------
# Summary / diagnostics helpers
# ---------------------------------------------------------------------------


def summarize_elaboration(result: ElaborationResult) -> str:
    """Produce a human-readable summary of an elaboration result.

    Parameters
    ----------
    result:
        The elaboration result to summarize.

    Returns
    -------
    str:
        Multi-line summary string.
    """
    lines: List[str] = []
    lines.append("=== Proof-Surface Elaboration Summary ===")
    lines.append(f"Stages completed: {len(result.stages_completed)}")
    for stage in result.stages_completed:
        lines.append(f"  - {stage.value}")
    lines.append(f"Sites added: {result.sites_added}")
    lines.append(f"Morphisms added: {result.morphisms_added}")
    lines.append(f"Seeds:")
    lines.append(f"  requires:   {len(result.requires_seeds)}")
    lines.append(f"  ensures:    {len(result.ensures_seeds)}")
    lines.append(f"  theorems:   {len(result.theorem_seeds)}")
    lines.append(f"  lemmas:     {len(result.lemma_seeds)}")
    lines.append(f"  transports: {len(result.transport_seeds)}")
    lines.append(f"  witnesses:  {len(result.witness_seeds)}")
    lines.append(f"  invariants: {len(result.invariant_seeds)}")
    lines.append(f"  decreases:  {len(result.decreases_seeds)}")
    if result.diagnostics:
        lines.append("Diagnostics:")
        for diag in result.diagnostics:
            lines.append(f"  {diag}")
    lines.append("=========================================")
    return "\n".join(lines)


def count_proof_obligations(result: ElaborationResult) -> Dict[str, int]:
    """Count the proof obligations generated by elaboration.

    Parameters
    ----------
    result:
        The elaboration result to analyze.

    Returns
    -------
    Dict[str, int]:
        Mapping from obligation category to count.
    """
    counts: Dict[str, int] = {
        "requires_checks": len(result.requires_seeds),
        "ensures_checks": len(result.ensures_seeds),
        "theorem_proofs": len(result.theorem_seeds),
        "lemma_proofs": len(result.lemma_seeds),
        "transport_obligations": len(result.transport_seeds),
        "witness_obligations": len(result.witness_seeds),
        "invariant_preservation": len(result.invariant_seeds),
        "termination_proofs": len(result.decreases_seeds),
        "total": (
            len(result.requires_seeds)
            + len(result.ensures_seeds)
            + len(result.theorem_seeds)
            + len(result.lemma_seeds)
            + len(result.transport_seeds)
            + len(result.witness_seeds)
            + len(result.invariant_seeds)
            + len(result.decreases_seeds)
        ),
    }
    return counts
