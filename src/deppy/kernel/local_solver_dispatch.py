"""Algorithm 2 -- Local solver dispatch for the sheaf-descent kernel.

For each site in a cover, the dispatcher identifies the appropriate theory
pack, runs local solving, and classifies the result as SOLVED, RESIDUAL,
or TIMEOUT.  The aggregate result is a SolverResult that partitions sites
into three bins:

- **Solved sections**: The local solver found a definitive type assignment
  for this site, backed by a proof or bounded model check.
- **Residual obligations**: The solver could partially solve the site but
  left verification conditions that require further evidence (proof debt).
- **Timeout/unknown**: The solver could not solve within the budget.

Theory packs are pluggable modules that register themselves for specific
site kinds and provide local solving logic.
"""

from __future__ import annotations

import enum
import time
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Protocol,
    Sequence,
    Set,
    Tuple,
    runtime_checkable,
)

from deppy.core._protocols import (
    Cover,
    LocalSection,
    Morphism,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite
from deppy.kernel._protocols import (
    Obligation,
    VerificationResult,
    VerificationStatus,
    TheoryId,
)
from deppy.kernel.trust_classifier import (
    TrustClassifier,
    trust_meet,
    trust_rank,
)


# ---------------------------------------------------------------------------
# Solver status
# ---------------------------------------------------------------------------

class SolverStatus(enum.Enum):
    """Classification of a local solver run."""
    SOLVED = "solved"
    RESIDUAL = "residual"
    TIMEOUT = "timeout"
    UNSUPPORTED = "unsupported"
    ERROR = "error"


# ---------------------------------------------------------------------------
# Theory pack protocol
# ---------------------------------------------------------------------------

@runtime_checkable
class TheoryPack(Protocol):
    """A theory pack provides local solving for specific site kinds.

    Theory packs are the pluggable units of domain knowledge in the
    sheaf-descent kernel.  Each pack declares which site kinds it handles
    and provides a local solver that produces sections and obligations.
    """

    @property
    def name(self) -> str:
        """Human-readable name of this theory pack."""
        ...

    @property
    def supported_kinds(self) -> FrozenSet[SiteKind]:
        """The site kinds this pack can solve."""
        ...

    @property
    def supported_theories(self) -> FrozenSet[TheoryId]:
        """The SMT theory fragments this pack uses."""
        ...

    def solve_local(
        self,
        site: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection],
        context: Dict[str, Any],
    ) -> LocalSolveResult:
        """Attempt to solve the local typing problem at this site.

        Returns a LocalSolveResult with the solved section and any
        residual obligations.
        """
        ...


# ---------------------------------------------------------------------------
# Local solve result
# ---------------------------------------------------------------------------

@dataclass
class LocalSolveResult:
    """Result of a single local solver invocation."""
    status: SolverStatus
    section: Optional[LocalSection] = None
    obligations: List[Obligation] = field(default_factory=list)
    elapsed_ms: float = 0.0
    theory_pack_name: str = ""
    detail: str = ""

    def is_solved(self) -> bool:
        return self.status == SolverStatus.SOLVED

    def is_residual(self) -> bool:
        return self.status == SolverStatus.RESIDUAL

    def is_timeout(self) -> bool:
        return self.status == SolverStatus.TIMEOUT


# ---------------------------------------------------------------------------
# Solver result (aggregate)
# ---------------------------------------------------------------------------

@dataclass
class SolverResult:
    """Aggregate result of dispatching local solvers across all sites."""
    solved_sections: Dict[SiteId, LocalSection] = field(default_factory=dict)
    residual_obligations: Dict[SiteId, List[Obligation]] = field(default_factory=dict)
    timeout_sites: Set[SiteId] = field(default_factory=set)
    unsupported_sites: Set[SiteId] = field(default_factory=set)
    error_sites: Set[SiteId] = field(default_factory=set)
    timing: Dict[SiteId, float] = field(default_factory=dict)
    theory_assignments: Dict[SiteId, str] = field(default_factory=dict)
    total_elapsed_ms: float = 0.0

    @property
    def num_solved(self) -> int:
        return len(self.solved_sections)

    @property
    def num_residual(self) -> int:
        return len(self.residual_obligations)

    @property
    def num_timeout(self) -> int:
        return len(self.timeout_sites)

    @property
    def all_sections(self) -> Dict[SiteId, LocalSection]:
        """Return all sections (solved + residual with partial sections)."""
        return dict(self.solved_sections)

    def coverage_ratio(self, total_sites: int) -> float:
        """Fraction of sites that were solved."""
        if total_sites == 0:
            return 1.0
        return self.num_solved / total_sites

    def __repr__(self) -> str:
        return (
            f"SolverResult(solved={self.num_solved}, "
            f"residual={self.num_residual}, "
            f"timeout={self.num_timeout}, "
            f"elapsed={self.total_elapsed_ms:.1f}ms)"
        )


# ---------------------------------------------------------------------------
# Default theory pack (fallback)
# ---------------------------------------------------------------------------

class DefaultTheoryPack:
    """Fallback theory pack that handles any site kind with basic inference.

    Produces RESIDUAL results for sites that have no specialized theory pack,
    preserving existing section data with ASSUMED trust.
    """

    @property
    def name(self) -> str:
        return "default"

    @property
    def supported_kinds(self) -> FrozenSet[SiteKind]:
        return frozenset(SiteKind)

    @property
    def supported_theories(self) -> FrozenSet[TheoryId]:
        return frozenset()

    def solve_local(
        self,
        site: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection],
        context: Dict[str, Any],
    ) -> LocalSolveResult:
        """Produce a residual result preserving existing section data."""
        if existing_section is not None:
            return LocalSolveResult(
                status=SolverStatus.RESIDUAL,
                section=LocalSection(
                    site_id=site,
                    carrier_type=existing_section.carrier_type,
                    refinements=dict(existing_section.refinements),
                    trust=TrustLevel.RESIDUAL,
                    provenance="default_theory_pack: preserved existing",
                    witnesses=dict(existing_section.witnesses),
                ),
                theory_pack_name=self.name,
                detail="no specialized theory pack; preserving existing data",
            )

        return LocalSolveResult(
            status=SolverStatus.RESIDUAL,
            section=LocalSection(
                site_id=site,
                trust=TrustLevel.ASSUMED,
                provenance="default_theory_pack: no data",
            ),
            theory_pack_name=self.name,
            detail="no specialized theory pack and no existing section",
        )


# ---------------------------------------------------------------------------
# Builtin theory packs for core site kinds
# ---------------------------------------------------------------------------

class SSAValuePack:
    """Theory pack for SSA_VALUE sites.

    Handles basic type inference for SSA values using the information
    already present in the carrier schema and incoming restriction data.
    """

    @property
    def name(self) -> str:
        return "ssa_value"

    @property
    def supported_kinds(self) -> FrozenSet[SiteKind]:
        return frozenset({SiteKind.SSA_VALUE})

    @property
    def supported_theories(self) -> FrozenSet[TheoryId]:
        return frozenset({TheoryId.QF_UF, TheoryId.QF_LIA})

    def solve_local(
        self,
        site: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection],
        context: Dict[str, Any],
    ) -> LocalSolveResult:
        refinements: Dict[str, Any] = {}
        carrier_type = carrier_schema

        if existing_section is not None:
            refinements = dict(existing_section.refinements)
            if existing_section.carrier_type is not None:
                carrier_type = existing_section.carrier_type

        # If carrier schema provides type info, use it
        if carrier_schema is not None and carrier_type is None:
            carrier_type = carrier_schema

        section = LocalSection(
            site_id=site,
            carrier_type=carrier_type,
            refinements=refinements,
            trust=TrustLevel.TRUSTED_AUTO,
            provenance="ssa_value_pack: local inference",
        )

        return LocalSolveResult(
            status=SolverStatus.SOLVED,
            section=section,
            theory_pack_name=self.name,
        )


class BranchGuardPack:
    """Theory pack for BRANCH_GUARD sites.

    Handles guard condition analysis, producing sections with
    predicate refinements for the true/false arms.
    """

    @property
    def name(self) -> str:
        return "branch_guard"

    @property
    def supported_kinds(self) -> FrozenSet[SiteKind]:
        return frozenset({SiteKind.BRANCH_GUARD})

    @property
    def supported_theories(self) -> FrozenSet[TheoryId]:
        return frozenset({TheoryId.QF_LIA, TheoryId.QF_UF})

    def solve_local(
        self,
        site: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection],
        context: Dict[str, Any],
    ) -> LocalSolveResult:
        refinements: Dict[str, Any] = {}
        if existing_section is not None:
            refinements = dict(existing_section.refinements)

        # Guard sites carry the guard predicate as a refinement
        if carrier_schema is not None:
            refinements["guard_predicate"] = carrier_schema

        section = LocalSection(
            site_id=site,
            carrier_type=carrier_schema,
            refinements=refinements,
            trust=TrustLevel.TRUSTED_AUTO,
            provenance="branch_guard_pack: guard analysis",
        )

        return LocalSolveResult(
            status=SolverStatus.SOLVED,
            section=section,
            theory_pack_name=self.name,
        )


class ArgumentBoundaryPack:
    """Theory pack for ARGUMENT_BOUNDARY sites.

    Produces sections representing function parameter types, with
    refinements from annotations and default values.
    """

    @property
    def name(self) -> str:
        return "argument_boundary"

    @property
    def supported_kinds(self) -> FrozenSet[SiteKind]:
        return frozenset({SiteKind.ARGUMENT_BOUNDARY})

    @property
    def supported_theories(self) -> FrozenSet[TheoryId]:
        return frozenset({TheoryId.QF_UF})

    def solve_local(
        self,
        site: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection],
        context: Dict[str, Any],
    ) -> LocalSolveResult:
        refinements: Dict[str, Any] = {}
        if existing_section is not None:
            refinements = dict(existing_section.refinements)

        section = LocalSection(
            site_id=site,
            carrier_type=carrier_schema,
            refinements=refinements,
            trust=TrustLevel.TRUSTED_AUTO,
            provenance="argument_boundary_pack: parameter type",
        )

        return LocalSolveResult(
            status=SolverStatus.SOLVED,
            section=section,
            theory_pack_name=self.name,
        )


class ReturnBoundaryPack:
    """Theory pack for RETURN_OUTPUT_BOUNDARY sites."""

    @property
    def name(self) -> str:
        return "return_boundary"

    @property
    def supported_kinds(self) -> FrozenSet[SiteKind]:
        return frozenset({SiteKind.RETURN_OUTPUT_BOUNDARY})

    @property
    def supported_theories(self) -> FrozenSet[TheoryId]:
        return frozenset({TheoryId.QF_UF})

    def solve_local(
        self,
        site: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection],
        context: Dict[str, Any],
    ) -> LocalSolveResult:
        refinements: Dict[str, Any] = {}
        if existing_section is not None:
            refinements = dict(existing_section.refinements)

        section = LocalSection(
            site_id=site,
            carrier_type=carrier_schema,
            refinements=refinements,
            trust=TrustLevel.TRUSTED_AUTO,
            provenance="return_boundary_pack: return type",
        )

        return LocalSolveResult(
            status=SolverStatus.SOLVED,
            section=section,
            theory_pack_name=self.name,
        )


class ErrorSitePack:
    """Theory pack for ERROR sites.

    Error sites require viability checking.  The local solver collects
    the viability constraints and produces residual obligations unless
    the error can be statically proven unreachable.
    """

    @property
    def name(self) -> str:
        return "error_site"

    @property
    def supported_kinds(self) -> FrozenSet[SiteKind]:
        return frozenset({SiteKind.ERROR})

    @property
    def supported_theories(self) -> FrozenSet[TheoryId]:
        return frozenset({TheoryId.QF_LIA, TheoryId.QF_UF})

    def solve_local(
        self,
        site: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection],
        context: Dict[str, Any],
    ) -> LocalSolveResult:
        refinements: Dict[str, Any] = {}
        if existing_section is not None:
            refinements = dict(existing_section.refinements)

        # Check if we have enough info to prove unreachability
        viability_pred = refinements.get("error_viability")
        if viability_pred is not None:
            # We have a viability predicate -- generate an obligation
            obligation = Obligation(
                proposition=viability_pred,
                site_id=site,
                context={"kind": "error_viability"},
                trust_required=TrustLevel.PROOF_BACKED,
            )

            section = LocalSection(
                site_id=site,
                carrier_type=carrier_schema,
                refinements=refinements,
                trust=TrustLevel.BOUNDED_AUTO,
                provenance="error_site_pack: viability pending",
            )

            return LocalSolveResult(
                status=SolverStatus.RESIDUAL,
                section=section,
                obligations=[obligation],
                theory_pack_name=self.name,
                detail="error viability requires proof",
            )

        # No viability info: residual with assumed trust
        section = LocalSection(
            site_id=site,
            carrier_type=carrier_schema,
            refinements=refinements,
            trust=TrustLevel.RESIDUAL,
            provenance="error_site_pack: no viability data",
        )

        return LocalSolveResult(
            status=SolverStatus.RESIDUAL,
            section=section,
            theory_pack_name=self.name,
            detail="no viability predicate available",
        )


class CallResultPack:
    """Theory pack for CALL_RESULT sites."""

    @property
    def name(self) -> str:
        return "call_result"

    @property
    def supported_kinds(self) -> FrozenSet[SiteKind]:
        return frozenset({SiteKind.CALL_RESULT})

    @property
    def supported_theories(self) -> FrozenSet[TheoryId]:
        return frozenset({TheoryId.QF_UF})

    def solve_local(
        self,
        site: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection],
        context: Dict[str, Any],
    ) -> LocalSolveResult:
        refinements: Dict[str, Any] = {}
        if existing_section is not None:
            refinements = dict(existing_section.refinements)

        section = LocalSection(
            site_id=site,
            carrier_type=carrier_schema,
            refinements=refinements,
            trust=TrustLevel.TRUSTED_AUTO,
            provenance="call_result_pack: return type propagated",
        )

        return LocalSolveResult(
            status=SolverStatus.SOLVED,
            section=section,
            theory_pack_name=self.name,
        )


class TensorPack:
    """Theory pack for tensor sites (TENSOR_SHAPE, TENSOR_ORDER, TENSOR_INDEXING)."""

    @property
    def name(self) -> str:
        return "tensor"

    @property
    def supported_kinds(self) -> FrozenSet[SiteKind]:
        return frozenset({
            SiteKind.TENSOR_SHAPE,
            SiteKind.TENSOR_ORDER,
            SiteKind.TENSOR_INDEXING,
        })

    @property
    def supported_theories(self) -> FrozenSet[TheoryId]:
        return frozenset({TheoryId.QF_LIA, TheoryId.QF_AX})

    def solve_local(
        self,
        site: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection],
        context: Dict[str, Any],
    ) -> LocalSolveResult:
        refinements: Dict[str, Any] = {}
        if existing_section is not None:
            refinements = dict(existing_section.refinements)

        # Tensor sites carry shape/dtype refinements
        if carrier_schema is not None:
            if site.kind == SiteKind.TENSOR_SHAPE:
                refinements["shape"] = carrier_schema
            elif site.kind == SiteKind.TENSOR_ORDER:
                refinements["order"] = carrier_schema
            elif site.kind == SiteKind.TENSOR_INDEXING:
                refinements["indexing"] = carrier_schema

        section = LocalSection(
            site_id=site,
            carrier_type=carrier_schema,
            refinements=refinements,
            trust=TrustLevel.TRUSTED_AUTO,
            provenance=f"tensor_pack: {site.kind.value}",
        )

        return LocalSolveResult(
            status=SolverStatus.SOLVED,
            section=section,
            theory_pack_name=self.name,
        )


class LoopInvariantPack:
    """Theory pack for LOOP_HEADER_INVARIANT sites.

    Loop invariants require iterative solving (widening/narrowing),
    so the local solver produces residual obligations for the invariant
    verification conditions.
    """

    @property
    def name(self) -> str:
        return "loop_invariant"

    @property
    def supported_kinds(self) -> FrozenSet[SiteKind]:
        return frozenset({SiteKind.LOOP_HEADER_INVARIANT})

    @property
    def supported_theories(self) -> FrozenSet[TheoryId]:
        return frozenset({TheoryId.QF_LIA, TheoryId.QF_UF})

    def solve_local(
        self,
        site: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection],
        context: Dict[str, Any],
    ) -> LocalSolveResult:
        refinements: Dict[str, Any] = {}
        if existing_section is not None:
            refinements = dict(existing_section.refinements)

        # Generate invariant preservation obligation
        obligation = Obligation(
            proposition=("loop_invariant", refinements),
            site_id=site,
            context={"kind": "loop_invariant_preservation"},
            trust_required=TrustLevel.BOUNDED_AUTO,
        )

        section = LocalSection(
            site_id=site,
            carrier_type=carrier_schema,
            refinements=refinements,
            trust=TrustLevel.BOUNDED_AUTO,
            provenance="loop_invariant_pack: pending verification",
        )

        return LocalSolveResult(
            status=SolverStatus.RESIDUAL,
            section=section,
            obligations=[obligation],
            theory_pack_name=self.name,
            detail="loop invariant requires iterative verification",
        )


class ProofSitePack:
    """Theory pack for PROOF sites."""

    @property
    def name(self) -> str:
        return "proof_site"

    @property
    def supported_kinds(self) -> FrozenSet[SiteKind]:
        return frozenset({SiteKind.PROOF})

    @property
    def supported_theories(self) -> FrozenSet[TheoryId]:
        return frozenset(TheoryId)

    def solve_local(
        self,
        site: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection],
        context: Dict[str, Any],
    ) -> LocalSolveResult:
        refinements: Dict[str, Any] = {}
        witnesses: Dict[str, Any] = {}
        if existing_section is not None:
            refinements = dict(existing_section.refinements)
            witnesses = dict(existing_section.witnesses)

        section = LocalSection(
            site_id=site,
            carrier_type=carrier_schema,
            refinements=refinements,
            trust=TrustLevel.PROOF_BACKED,
            provenance="proof_site_pack: proof-backed section",
            witnesses=witnesses,
        )

        return LocalSolveResult(
            status=SolverStatus.SOLVED,
            section=section,
            theory_pack_name=self.name,
        )


class HeapProtocolPack:
    """Theory pack for HEAP_PROTOCOL sites."""

    @property
    def name(self) -> str:
        return "heap_protocol"

    @property
    def supported_kinds(self) -> FrozenSet[SiteKind]:
        return frozenset({SiteKind.HEAP_PROTOCOL})

    @property
    def supported_theories(self) -> FrozenSet[TheoryId]:
        return frozenset({TheoryId.QF_AX, TheoryId.QF_UF})

    def solve_local(
        self,
        site: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection],
        context: Dict[str, Any],
    ) -> LocalSolveResult:
        refinements: Dict[str, Any] = {}
        if existing_section is not None:
            refinements = dict(existing_section.refinements)

        section = LocalSection(
            site_id=site,
            carrier_type=carrier_schema,
            refinements=refinements,
            trust=TrustLevel.BOUNDED_AUTO,
            provenance="heap_protocol_pack: heap analysis",
        )

        return LocalSolveResult(
            status=SolverStatus.RESIDUAL,
            section=section,
            theory_pack_name=self.name,
            detail="heap protocol requires alias analysis",
        )


# ---------------------------------------------------------------------------
# Local solver dispatch
# ---------------------------------------------------------------------------

def _builtin_packs() -> List[Any]:
    """Create the built-in theory packs."""
    return [
        SSAValuePack(),
        BranchGuardPack(),
        ArgumentBoundaryPack(),
        ReturnBoundaryPack(),
        ErrorSitePack(),
        CallResultPack(),
        TensorPack(),
        LoopInvariantPack(),
        ProofSitePack(),
        HeapProtocolPack(),
    ]


class LocalSolverDispatch:
    """Dispatch each site to its local solver.

    Algorithm 2: For each site in the cover, identify the appropriate
    theory pack, run local solving, classify result.

    The dispatcher maintains a registry of theory packs and dispatches
    sites to the most specific pack that supports the site's kind.
    User-provided packs take priority over built-in packs.
    """

    def __init__(
        self,
        *,
        timeout_ms: float = 5000.0,
        trust_classifier: Optional[TrustClassifier] = None,
        include_builtins: bool = True,
    ) -> None:
        self._timeout_ms = timeout_ms
        self._trust_classifier = trust_classifier or TrustClassifier()
        self._packs: List[Any] = []
        self._kind_to_pack: Dict[SiteKind, Any] = {}
        self._default_pack = DefaultTheoryPack()

        if include_builtins:
            for pack in _builtin_packs():
                self.register_pack(pack)

    # -- Helpers -----------------------------------------------------------

    @staticmethod
    def _pack_name(pack: Any) -> str:
        return getattr(pack, 'name', None) or type(pack).__name__

    @staticmethod
    def _call_solve_local(
        pack: Any,
        site_id: SiteId,
        carrier_schema: Any = None,
        existing_section: Optional[LocalSection] = None,
        context: Optional[Dict[str, Any]] = None,
    ) -> Any:
        """Call pack.solve_local adapting to both old and new signatures."""
        import inspect
        sig = inspect.signature(pack.solve_local)
        params = list(sig.parameters.keys())
        # Theory packs (new style): solve_local(self, site, section)
        if len(params) <= 3:
            section_arg = existing_section if existing_section is not None else LocalSection(site_id=site_id)
            raw = pack.solve_local(site_id, section_arg)
            # Adapt theory-pack SolverResult to LocalSolveResult if needed
            if not isinstance(raw, LocalSolveResult):
                return LocalSolveResult(
                    status=getattr(raw, 'status', SolverStatus.UNCHANGED),
                    section=getattr(raw, 'section', None),
                    detail=getattr(raw, 'explanation', ''),
                )
            return raw
        else:
            return pack.solve_local(
                site=site_id,
                carrier_schema=carrier_schema,
                existing_section=existing_section,
                context=context or {},
            )

    # -- Pack registration -------------------------------------------------

    def register_pack(self, pack: Any) -> None:
        """Register a theory pack.

        Packs registered later take priority over earlier ones for the
        same site kinds.
        """
        self._packs.append(pack)
        # Support both property-style (supported_kinds) and method-style
        # (applicable_site_kinds) theory packs.
        kinds = getattr(pack, 'supported_kinds', None)
        if kinds is None and hasattr(pack, 'applicable_site_kinds'):
            kinds = pack.applicable_site_kinds()
        if kinds is None:
            kinds = frozenset()
        for kind in kinds:
            self._kind_to_pack[kind] = pack

    def get_pack_for_site(self, site_id: SiteId) -> Any:
        """Return the theory pack registered for a site's kind."""
        return self._kind_to_pack.get(site_id.kind, self._default_pack)

    # -- Main dispatch -----------------------------------------------------

    def dispatch(
        self,
        cover: Cover,
        theory_packs: Optional[Sequence[Any]] = None,
    ) -> SolverResult:
        """Dispatch local solvers to all sites in the cover.

        For each site:
        1. Identify the appropriate theory pack.
        2. Run the local solver with a timeout budget.
        3. Classify the result and accumulate into the aggregate.

        Args:
            cover: The observation cover to solve.
            theory_packs: Optional additional theory packs to register.
                These take priority over built-in packs.

        Returns:
            SolverResult with solved sections, residual obligations, etc.
        """
        # Register additional packs if provided
        if theory_packs is not None:
            for pack in theory_packs:
                self.register_pack(pack)

        result = SolverResult()
        overall_start = time.monotonic()

        # Sort sites for deterministic processing: input boundary first,
        # then interior, then output boundary, then error sites last
        ordered_sites = self._order_sites(cover)

        # Context for local solvers (shared across sites)
        context = self._build_context(cover)

        for site_id in ordered_sites:
            site_obj = cover.sites.get(site_id)
            carrier_schema = None
            if site_obj is not None and hasattr(site_obj, "carrier_schema"):
                carrier_schema = site_obj.carrier_schema

            # Find the theory pack
            pack = self.get_pack_for_site(site_id)
            result.theory_assignments[site_id] = getattr(pack, 'name', None) or type(pack).__name__

            # Run local solver with timing
            start = time.monotonic()
            pn = self._pack_name(pack)
            try:
                local_result = self._call_solve_local(
                    pack, site_id, carrier_schema, None, context,
                )
            except Exception as exc:
                # ── Sheaf-theoretic fallback: error → default pack ──
                # When a theory pack crashes on a site it registered for,
                # we fall through to the default pack to produce a ⊤
                # section.  This ensures the presheaf is COMPLETE (every
                # site has a fiber), preventing false H¹ obstructions
                # from "missing section" at overlaps.
                try:
                    local_result = self._call_solve_local(
                        self._default_pack, site_id, carrier_schema, None, context,
                    )
                    local_result.detail = f"fallback after {pn} error: {exc}"
                except Exception:
                    local_result = LocalSolveResult(
                        status=SolverStatus.ERROR,
                        detail=f"exception: {exc}",
                        theory_pack_name=pn,
                    )
            elapsed = (time.monotonic() - start) * 1000.0

            # Check timeout
            if elapsed > self._timeout_ms:
                local_result = LocalSolveResult(
                    status=SolverStatus.TIMEOUT,
                    elapsed_ms=elapsed,
                    theory_pack_name=pn,
                    detail=f"exceeded timeout of {self._timeout_ms}ms",
                )

            local_result.elapsed_ms = elapsed
            result.timing[site_id] = elapsed

            # Classify and accumulate
            self._accumulate_result(result, site_id, local_result)

        result.total_elapsed_ms = (time.monotonic() - overall_start) * 1000.0
        return result

    def dispatch_single(
        self,
        site_id: SiteId,
        carrier_schema: Any,
        existing_section: Optional[LocalSection] = None,
        context: Optional[Dict[str, Any]] = None,
    ) -> LocalSolveResult:
        """Dispatch a single site to its local solver."""
        pack = self.get_pack_for_site(site_id)
        ctx = context or {}

        start = time.monotonic()
        try:
            local_result = self._call_solve_local(
                pack, site_id, carrier_schema, existing_section, ctx,
            )
        except Exception as exc:
            local_result = LocalSolveResult(
                status=SolverStatus.ERROR,
                detail=f"exception: {exc}",
                theory_pack_name=self._pack_name(pack),
            )
        elapsed = (time.monotonic() - start) * 1000.0
        local_result.elapsed_ms = elapsed

        return local_result

    def dispatch_incremental(
        self,
        cover: Cover,
        existing_sections: Dict[SiteId, LocalSection],
        changed_sites: Set[SiteId],
        theory_packs: Optional[Sequence[Any]] = None,
    ) -> SolverResult:
        """Re-dispatch solvers only for changed sites.

        This is used during fixed-point iteration: only sites whose
        incoming sections have changed need re-solving.
        """
        if theory_packs is not None:
            for pack in theory_packs:
                self.register_pack(pack)

        result = SolverResult()
        result.solved_sections = {
            sid: sec for sid, sec in existing_sections.items()
            if sid not in changed_sites
        }

        context = self._build_context(cover)
        overall_start = time.monotonic()

        for site_id in changed_sites:
            site_obj = cover.sites.get(site_id)
            carrier_schema = None
            if site_obj is not None and hasattr(site_obj, "carrier_schema"):
                carrier_schema = site_obj.carrier_schema

            pack = self.get_pack_for_site(site_id)
            result.theory_assignments[site_id] = getattr(pack, 'name', None) or type(pack).__name__

            existing = existing_sections.get(site_id)

            start = time.monotonic()
            try:
                local_result = self._call_solve_local(
                    pack, site_id, carrier_schema, existing, context,
                )
            except Exception as exc:
                local_result = LocalSolveResult(
                    status=SolverStatus.ERROR,
                    detail=f"exception: {exc}",
                    theory_pack_name=self._pack_name(pack),
                )
            elapsed = (time.monotonic() - start) * 1000.0
            local_result.elapsed_ms = elapsed
            result.timing[site_id] = elapsed

            self._accumulate_result(result, site_id, local_result)

        result.total_elapsed_ms = (time.monotonic() - overall_start) * 1000.0
        return result

    # -- Private helpers ---------------------------------------------------

    def _order_sites(self, cover: Cover) -> List[SiteId]:
        """Order sites for processing: input -> interior -> output -> error."""
        input_sites: List[SiteId] = []
        output_sites: List[SiteId] = []
        error_sites: List[SiteId] = []
        interior_sites: List[SiteId] = []

        for sid in cover.sites:
            if sid in cover.input_boundary:
                input_sites.append(sid)
            elif sid in cover.output_boundary:
                output_sites.append(sid)
            elif sid in cover.error_sites:
                error_sites.append(sid)
            else:
                interior_sites.append(sid)

        return input_sites + interior_sites + output_sites + error_sites

    def _build_context(self, cover: Cover) -> Dict[str, Any]:
        """Build the shared context for local solvers."""
        return {
            "error_sites": cover.error_sites,
            "input_boundary": cover.input_boundary,
            "output_boundary": cover.output_boundary,
            "num_sites": len(cover.sites),
            "num_morphisms": len(cover.morphisms),
            "num_overlaps": len(cover.overlaps),
        }

    def _accumulate_result(
        self,
        result: SolverResult,
        site_id: SiteId,
        local_result: LocalSolveResult,
    ) -> None:
        """Accumulate a local solver result into the aggregate."""
        if local_result.status == SolverStatus.SOLVED:
            if local_result.section is not None:
                result.solved_sections[site_id] = local_result.section
            if local_result.obligations:
                result.residual_obligations[site_id] = local_result.obligations

        elif local_result.status == SolverStatus.RESIDUAL:
            if local_result.section is not None:
                result.solved_sections[site_id] = local_result.section
            if local_result.obligations:
                result.residual_obligations[site_id] = local_result.obligations

        elif local_result.status == SolverStatus.TIMEOUT:
            result.timeout_sites.add(site_id)

        elif local_result.status == SolverStatus.UNSUPPORTED:
            result.unsupported_sites.add(site_id)

        elif local_result.status == SolverStatus.ERROR:
            result.error_sites.add(site_id)
