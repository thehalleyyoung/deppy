"""Viability checker for error-sensitive sites.

For each error site in the cover, the viability checker determines whether
the current sections provide sufficient evidence that the error site is
"viable" -- meaning either:

1. The error is *statically unreachable* (the guard conditions leading to
   the error are provably unsatisfiable given the input constraints).

2. The error has a *safe input region* -- there exist input conditions
   under which the error cannot occur, and backward synthesis has
   successfully propagated these conditions to the input boundary.

3. The error is *bounded* -- while not fully resolved, the viability
   predicate is satisfied with bounded confidence (model checking).

The checker supports multiple viability strategies:
- Static unreachability via guard predicate analysis
- Backward-propagated precondition satisfaction
- Witness-based evidence from proof sites
- Trust-gated acceptance (accept if trust exceeds threshold)
"""

from __future__ import annotations

import enum
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    Cover,
    LocalSection,
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism
from deppy.static_analysis.restriction_maps import (
    RestrictionData,
    RestrictionKind,
)
from deppy.kernel.trust_classifier import (
    TrustClassifier,
    trust_meet,
    trust_rank,
    _extract_restriction_data,
)


# ---------------------------------------------------------------------------
# Viability status
# ---------------------------------------------------------------------------

class ViabilityStatus(enum.Enum):
    """Result of checking a single error site's viability."""
    PROVEN_UNREACHABLE = "proven_unreachable"
    SAFE_INPUT_EXISTS = "safe_input_exists"
    BOUNDED_SAFE = "bounded_safe"
    TRUST_ACCEPTED = "trust_accepted"
    UNKNOWN = "unknown"
    VIOLATED = "violated"


# ---------------------------------------------------------------------------
# Viability result
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ViabilityResult:
    """Result of checking viability for a single error site."""
    _error_site: SiteId
    _status: ViabilityStatus
    _confidence: float
    _evidence_summary: str
    _trust_level: TrustLevel
    _upstream_sites: FrozenSet[SiteId] = frozenset()
    _viability_predicate: Any = None
    _witness: Any = None

    @property
    def error_site(self) -> SiteId:
        return self._error_site

    @property
    def status(self) -> ViabilityStatus:
        return self._status

    @property
    def confidence(self) -> float:
        return self._confidence

    @property
    def evidence_summary(self) -> str:
        return self._evidence_summary

    @property
    def trust_level(self) -> TrustLevel:
        return self._trust_level

    @property
    def upstream_sites(self) -> FrozenSet[SiteId]:
        return self._upstream_sites

    @property
    def is_viable(self) -> bool:
        """True if the error site is considered safe."""
        return self._status in (
            ViabilityStatus.PROVEN_UNREACHABLE,
            ViabilityStatus.SAFE_INPUT_EXISTS,
            ViabilityStatus.BOUNDED_SAFE,
            ViabilityStatus.TRUST_ACCEPTED,
        )

    @property
    def is_proven(self) -> bool:
        """True if viability is backed by a proof."""
        return self._status == ViabilityStatus.PROVEN_UNREACHABLE

    def __repr__(self) -> str:
        return (
            f"ViabilityResult(site={self._error_site}, "
            f"status={self._status.value}, "
            f"confidence={self._confidence:.2f}, "
            f"trust={self._trust_level.value})"
        )


# ---------------------------------------------------------------------------
# Aggregate viability summary
# ---------------------------------------------------------------------------

@dataclass
class ViabilitySummary:
    """Aggregate viability results across all error sites."""
    results: Dict[SiteId, ViabilityResult] = field(default_factory=dict)
    all_viable: bool = True
    num_proven: int = 0
    num_safe_input: int = 0
    num_bounded: int = 0
    num_trust_accepted: int = 0
    num_unknown: int = 0
    num_violated: int = 0

    @property
    def total_checked(self) -> int:
        return len(self.results)

    @property
    def viable_ratio(self) -> float:
        if self.total_checked == 0:
            return 1.0
        viable = sum(1 for r in self.results.values() if r.is_viable)
        return viable / self.total_checked

    def violated_sites(self) -> Set[SiteId]:
        """Return sites with violated viability."""
        return {
            sid for sid, r in self.results.items()
            if r.status == ViabilityStatus.VIOLATED
        }

    def unknown_sites(self) -> Set[SiteId]:
        """Return sites with unknown viability."""
        return {
            sid for sid, r in self.results.items()
            if r.status == ViabilityStatus.UNKNOWN
        }

    def __repr__(self) -> str:
        return (
            f"ViabilitySummary(checked={self.total_checked}, "
            f"all_viable={self.all_viable}, "
            f"proven={self.num_proven}, "
            f"violated={self.num_violated})"
        )


# ---------------------------------------------------------------------------
# Viability checker
# ---------------------------------------------------------------------------

class ViabilityChecker:
    """Check error-sensitive site viability predicates.

    For each error site, the checker runs a sequence of strategies to
    determine whether the error is safely handled.
    """

    def __init__(
        self,
        *,
        trust_threshold: TrustLevel = TrustLevel.BOUNDED_AUTO,
        trust_classifier: Optional[TrustClassifier] = None,
        allow_trust_gated: bool = True,
        confidence_threshold: float = 0.8,
    ) -> None:
        self._trust_threshold = trust_threshold
        self._trust_classifier = trust_classifier or TrustClassifier()
        self._allow_trust_gated = allow_trust_gated
        self._confidence_threshold = confidence_threshold

    # -- Main API ----------------------------------------------------------

    def check_all(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> ViabilitySummary:
        """Check viability for all error sites in the cover.

        Returns an aggregate summary with per-site results.
        """
        summary = ViabilitySummary()

        for error_site in cover.error_sites:
            result = self.check_single(error_site, cover, sections)
            summary.results[error_site] = result

            if result.status == ViabilityStatus.PROVEN_UNREACHABLE:
                summary.num_proven += 1
            elif result.status == ViabilityStatus.SAFE_INPUT_EXISTS:
                summary.num_safe_input += 1
            elif result.status == ViabilityStatus.BOUNDED_SAFE:
                summary.num_bounded += 1
            elif result.status == ViabilityStatus.TRUST_ACCEPTED:
                summary.num_trust_accepted += 1
            elif result.status == ViabilityStatus.UNKNOWN:
                summary.num_unknown += 1
            elif result.status == ViabilityStatus.VIOLATED:
                summary.num_violated += 1

        summary.all_viable = all(
            r.is_viable for r in summary.results.values()
        )

        return summary

    def check_single(
        self,
        error_site: SiteId,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> ViabilityResult:
        """Check viability for a single error site.

        Runs strategies in order of strength:
        1. Static unreachability
        2. Safe input existence
        3. Bounded safety
        4. Trust-gated acceptance
        """
        error_section = sections.get(error_site)
        if error_section is None:
            return ViabilityResult(
                _error_site=error_site,
                _status=ViabilityStatus.UNKNOWN,
                _confidence=0.0,
                _evidence_summary="no section at error site",
                _trust_level=TrustLevel.ASSUMED,
            )

        # Strategy 1: Static unreachability
        result = self._check_static_unreachability(
            error_site, error_section, cover, sections
        )
        if result is not None:
            return result

        # Strategy 2: Safe input existence (backward-propagated precondition)
        result = self._check_safe_input_existence(
            error_site, error_section, cover, sections
        )
        if result is not None:
            return result

        # Strategy 3: Witness-based evidence
        result = self._check_witness_evidence(
            error_site, error_section, cover, sections
        )
        if result is not None:
            return result

        # Strategy 4: Bounded safety
        result = self._check_bounded_safety(
            error_site, error_section, cover, sections
        )
        if result is not None:
            return result

        # Strategy 5: Trust-gated acceptance
        if self._allow_trust_gated:
            result = self._check_trust_gated(
                error_site, error_section, cover, sections
            )
            if result is not None:
                return result

        # No strategy succeeded
        return ViabilityResult(
            _error_site=error_site,
            _status=ViabilityStatus.UNKNOWN,
            _confidence=0.0,
            _evidence_summary="no viability evidence found",
            _trust_level=error_section.trust,
        )

    # -- Strategy 1: Static unreachability ---------------------------------

    def _check_static_unreachability(
        self,
        error_site: SiteId,
        error_section: LocalSection,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Optional[ViabilityResult]:
        """Check if the error site is statically unreachable.

        An error is unreachable if all guard paths leading to it are
        unsatisfiable given the current section constraints.
        """
        # Look for guard predicates in upstream sections that make
        # the error unreachable
        upstream = self._find_upstream_sites(error_site, cover)
        guard_evidence: List[str] = []

        for up_site in upstream:
            up_section = sections.get(up_site)
            if up_section is None:
                continue

            # Check for guard predicates that negate the error path
            for key, value in up_section.refinements.items():
                if "guard" in key:
                    # If the guard is proven (high trust), the error may
                    # be unreachable through this path
                    if trust_rank(up_section.trust) >= trust_rank(TrustLevel.PROOF_BACKED):
                        guard_evidence.append(
                            f"guard at {up_site} ({key}) is proof-backed"
                        )

        # Check if error section itself has unreachability markers
        for key, value in error_section.refinements.items():
            if "unreachable" in key or value == ("error_unreachable", error_site):
                if trust_rank(error_section.trust) >= trust_rank(TrustLevel.TRUSTED_AUTO):
                    return ViabilityResult(
                        _error_site=error_site,
                        _status=ViabilityStatus.PROVEN_UNREACHABLE,
                        _confidence=1.0,
                        _evidence_summary=f"error marked unreachable: {key}",
                        _trust_level=error_section.trust,
                        _upstream_sites=frozenset(upstream),
                    )

        if guard_evidence and len(guard_evidence) >= len(upstream):
            return ViabilityResult(
                _error_site=error_site,
                _status=ViabilityStatus.PROVEN_UNREACHABLE,
                _confidence=0.95,
                _evidence_summary=(
                    f"all paths guarded: {'; '.join(guard_evidence)}"
                ),
                _trust_level=TrustLevel.PROOF_BACKED,
                _upstream_sites=frozenset(upstream),
            )

        return None

    # -- Strategy 2: Safe input existence ----------------------------------

    def _check_safe_input_existence(
        self,
        error_site: SiteId,
        error_section: LocalSection,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Optional[ViabilityResult]:
        """Check if backward synthesis found safe input conditions.

        If the input boundary sections contain viability predicates
        for this error site, the error has a known safe-input region.
        """
        input_sites_with_viability: List[SiteId] = []

        for in_site in cover.input_boundary:
            in_section = sections.get(in_site)
            if in_section is None:
                continue

            for key, value in in_section.refinements.items():
                if "viability" in key or "error_viability" in key:
                    input_sites_with_viability.append(in_site)
                    break

        if not input_sites_with_viability:
            # Also check for refinements that match the error site
            for in_site in cover.input_boundary:
                in_section = sections.get(in_site)
                if in_section is None:
                    continue
                if in_section.refinements:
                    # Any non-empty refinements at input boundary count
                    # as potential safe-input evidence
                    input_sites_with_viability.append(in_site)

        if input_sites_with_viability:
            # Compute confidence based on trust of input sections
            confidences: List[float] = []
            for in_site in input_sites_with_viability:
                in_sec = sections.get(in_site)
                if in_sec is not None:
                    t = trust_rank(in_sec.trust)
                    confidences.append(min(1.0, t / 5.0))

            avg_confidence = sum(confidences) / len(confidences) if confidences else 0.0

            if avg_confidence >= self._confidence_threshold:
                return ViabilityResult(
                    _error_site=error_site,
                    _status=ViabilityStatus.SAFE_INPUT_EXISTS,
                    _confidence=avg_confidence,
                    _evidence_summary=(
                        f"safe input conditions at {len(input_sites_with_viability)} "
                        f"input sites"
                    ),
                    _trust_level=TrustLevel.BOUNDED_AUTO,
                    _upstream_sites=frozenset(input_sites_with_viability),
                )

        return None

    # -- Strategy 3: Witness evidence --------------------------------------

    def _check_witness_evidence(
        self,
        error_site: SiteId,
        error_section: LocalSection,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Optional[ViabilityResult]:
        """Check if witness/proof evidence resolves the error."""
        # Look for witnesses in the error section itself
        if error_section.witnesses:
            for key, witness in error_section.witnesses.items():
                if "safety" in key or "viability" in key:
                    return ViabilityResult(
                        _error_site=error_site,
                        _status=ViabilityStatus.PROVEN_UNREACHABLE,
                        _confidence=1.0,
                        _evidence_summary=f"witness evidence: {key}",
                        _trust_level=TrustLevel.PROOF_BACKED,
                        _witness=witness,
                    )

        # Look for proof sites that transport evidence to this error site
        for morphism in cover.morphisms:
            if morphism.target == error_site:
                source_section = sections.get(morphism.source)
                if source_section is None:
                    continue
                if source_section.site_id.kind == SiteKind.PROOF:
                    rdata = _extract_restriction_data(morphism)
                    if rdata is not None and rdata.kind == RestrictionKind.PROOF_TRANSPORT:
                        return ViabilityResult(
                            _error_site=error_site,
                            _status=ViabilityStatus.PROVEN_UNREACHABLE,
                            _confidence=1.0,
                            _evidence_summary=(
                                f"proof transport from {morphism.source}"
                            ),
                            _trust_level=TrustLevel.PROOF_BACKED,
                            _upstream_sites=frozenset({morphism.source}),
                        )

        return None

    # -- Strategy 4: Bounded safety ----------------------------------------

    def _check_bounded_safety(
        self,
        error_site: SiteId,
        error_section: LocalSection,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Optional[ViabilityResult]:
        """Check if bounded model checking provides safety evidence."""
        # Look for bounded-auto trust sections with viability data
        if trust_rank(error_section.trust) >= trust_rank(TrustLevel.BOUNDED_AUTO):
            viability_keys = [
                k for k in error_section.refinements
                if "viability" in k or "safety" in k or "bound" in k
            ]
            if viability_keys:
                return ViabilityResult(
                    _error_site=error_site,
                    _status=ViabilityStatus.BOUNDED_SAFE,
                    _confidence=0.75,
                    _evidence_summary=(
                        f"bounded safety via {', '.join(viability_keys)}"
                    ),
                    _trust_level=TrustLevel.BOUNDED_AUTO,
                    _viability_predicate=tuple(
                        error_section.refinements[k] for k in viability_keys
                    ),
                )

        return None

    # -- Strategy 5: Trust-gated ------------------------------------------

    def _check_trust_gated(
        self,
        error_site: SiteId,
        error_section: LocalSection,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Optional[ViabilityResult]:
        """Accept viability if trust level exceeds threshold.

        This is the weakest strategy: if the error section has sufficient
        trust (e.g., from runtime trace data), accept it as viable with
        reduced confidence.
        """
        if trust_rank(error_section.trust) >= trust_rank(self._trust_threshold):
            confidence = min(1.0, trust_rank(error_section.trust) / 5.0)
            return ViabilityResult(
                _error_site=error_site,
                _status=ViabilityStatus.TRUST_ACCEPTED,
                _confidence=confidence * 0.6,  # Reduce confidence for trust-gated
                _evidence_summary=(
                    f"trust-gated acceptance: "
                    f"{error_section.trust.value} >= "
                    f"{self._trust_threshold.value}"
                ),
                _trust_level=error_section.trust,
            )

        return None

    # -- Upstream site finder ----------------------------------------------

    def _find_upstream_sites(
        self,
        target: SiteId,
        cover: Cover,
    ) -> Set[SiteId]:
        """Find all sites with morphisms targeting the given site."""
        upstream: Set[SiteId] = set()
        for morphism in cover.morphisms:
            if morphism.target == target:
                upstream.add(morphism.source)
        return upstream

    # -- Batch checking with filtering -------------------------------------

    def check_subset(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
        error_subset: Set[SiteId],
    ) -> ViabilitySummary:
        """Check viability for a subset of error sites."""
        summary = ViabilitySummary()

        for error_site in error_subset:
            if error_site in cover.error_sites:
                result = self.check_single(error_site, cover, sections)
                summary.results[error_site] = result

                if result.status == ViabilityStatus.PROVEN_UNREACHABLE:
                    summary.num_proven += 1
                elif result.status == ViabilityStatus.SAFE_INPUT_EXISTS:
                    summary.num_safe_input += 1
                elif result.status == ViabilityStatus.BOUNDED_SAFE:
                    summary.num_bounded += 1
                elif result.status == ViabilityStatus.TRUST_ACCEPTED:
                    summary.num_trust_accepted += 1
                elif result.status == ViabilityStatus.UNKNOWN:
                    summary.num_unknown += 1
                elif result.status == ViabilityStatus.VIOLATED:
                    summary.num_violated += 1

        summary.all_viable = all(
            r.is_viable for r in summary.results.values()
        )

        return summary
