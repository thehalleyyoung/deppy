"""Infer viability of error sites from observed runtime behaviour.

An error site is *viable* (safe) when the operation it guards has never
been observed to raise an exception across all recorded traces.
Conversely, if the operation consistently fails, the site is marked
non-viable.  This module bridges dynamic observation with the
sheaf-descent framework's notion of error-site viability.

The primary entry-point is :func:`infer_viability`.

Viability levels
----------------
- **VIABLE** -- the operation succeeded in every trace.
- **CONDITIONALLY_VIABLE** -- the operation succeeded in some traces
  and failed in others, suggesting input-dependent safety.
- **NON_VIABLE** -- the operation failed in every trace.
- **UNKNOWN** -- no observations are available for this site.
"""

from __future__ import annotations

import enum
from collections import defaultdict
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
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.observe.trace_parser import (
    ExceptionObservation,
    FunctionObservation,
    ParsedTrace,
    VariableObservation,
)


# ---------------------------------------------------------------------------
# Viability classification
# ---------------------------------------------------------------------------

class ViabilityLevel(enum.Enum):
    """Classification of error-site viability based on traces."""
    VIABLE = "viable"
    CONDITIONALLY_VIABLE = "conditionally_viable"
    NON_VIABLE = "non_viable"
    UNKNOWN = "unknown"


# ---------------------------------------------------------------------------
# Per-site viability result
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SiteViability:
    """Viability assessment for a single error site.

    Attributes
    ----------
    site_id : SiteId
        The error site being assessed.
    level : ViabilityLevel
        The viability classification.
    success_count : int
        Number of traces where the site's operation succeeded.
    failure_count : int
        Number of traces where the site's operation failed.
    total_traces : int
        Total number of traces that exercised this site.
    failure_types : Tuple[str, ...]
        Exception types observed at failures.
    confidence : float
        Confidence in the assessment (0.0 -- 1.0), based on sample count.
    evidence_trace_ids : Tuple[str, ...]
        Trace ids that provide evidence for this assessment.
    explanation : str
        Human-readable explanation of the assessment.
    """

    site_id: SiteId
    level: ViabilityLevel = ViabilityLevel.UNKNOWN
    success_count: int = 0
    failure_count: int = 0
    total_traces: int = 0
    failure_types: Tuple[str, ...] = ()
    confidence: float = 0.0
    evidence_trace_ids: Tuple[str, ...] = ()
    explanation: str = ""

    @property
    def is_viable(self) -> bool:
        return self.level == ViabilityLevel.VIABLE

    @property
    def is_non_viable(self) -> bool:
        return self.level == ViabilityLevel.NON_VIABLE

    @property
    def success_rate(self) -> float:
        if self.total_traces == 0:
            return 0.0
        return self.success_count / self.total_traces


# ---------------------------------------------------------------------------
# Viability inference result
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ViabilityResult:
    """Complete viability inference result for all error sites.

    Attributes
    ----------
    site_viabilities : Tuple[SiteViability, ...]
        Per-site viability assessments.
    viable_sites : FrozenSet[SiteId]
        Sites classified as VIABLE.
    non_viable_sites : FrozenSet[SiteId]
        Sites classified as NON_VIABLE.
    conditional_sites : FrozenSet[SiteId]
        Sites classified as CONDITIONALLY_VIABLE.
    unknown_sites : FrozenSet[SiteId]
        Sites with no observations.
    total_traces_used : int
        How many traces contributed to this inference.
    overall_confidence : float
        Average confidence across all assessments.
    """

    site_viabilities: Tuple[SiteViability, ...] = ()
    viable_sites: FrozenSet[SiteId] = frozenset()
    non_viable_sites: FrozenSet[SiteId] = frozenset()
    conditional_sites: FrozenSet[SiteId] = frozenset()
    unknown_sites: FrozenSet[SiteId] = frozenset()
    total_traces_used: int = 0
    overall_confidence: float = 0.0

    def viability_of(self, site_id: SiteId) -> Optional[SiteViability]:
        """Look up viability for a specific site."""
        for sv in self.site_viabilities:
            if sv.site_id == site_id:
                return sv
        return None

    def is_viable(self, site_id: SiteId) -> bool:
        """Return True if the site is classified as viable."""
        return site_id in self.viable_sites

    def as_dict(self) -> Dict[SiteId, bool]:
        """Return a simple ``{SiteId: bool}`` mapping (viable or not)."""
        result: Dict[SiteId, bool] = {}
        for sv in self.site_viabilities:
            result[sv.site_id] = sv.is_viable
        return result


# ---------------------------------------------------------------------------
# Error-site matching helpers
# ---------------------------------------------------------------------------

def _site_matches_exception(
    site_id: SiteId,
    exc_obs: ExceptionObservation,
) -> bool:
    """Check whether an error site plausibly corresponds to an exception.

    Matching is by function name and error kind embedded in the site name.
    """
    # Extract the function from the site name (before the first dot)
    site_func = site_id.name.split(".")[0] if "." in site_id.name else site_id.name
    exc_func_parts = exc_obs.function.rsplit(".", 1)
    exc_func_short = exc_func_parts[-1]

    # Function name must match (possibly partial)
    if site_func != exc_func_short and site_func not in exc_obs.function:
        return False

    # Check if the error kind in the site name corresponds to the exception
    exc_short = exc_obs.exception_type.rsplit(".", 1)[-1]
    if exc_short.lower() in site_id.name.lower():
        return True

    # Fuzzy match: site name contains "error" and exception is in the same function
    if "error" in site_id.name.lower():
        return True

    return False


def _site_is_exercised_by_function(
    site_id: SiteId,
    func_obs: FunctionObservation,
) -> bool:
    """Check whether a function observation exercises a given error site."""
    site_func = site_id.name.split(".")[0] if "." in site_id.name else site_id.name
    func_short = func_obs.function.rsplit(".", 1)[-1]
    return site_func == func_short or site_func in func_obs.function


# ---------------------------------------------------------------------------
# Confidence computation
# ---------------------------------------------------------------------------

def _compute_confidence(
    success_count: int,
    failure_count: int,
    total: int,
) -> float:
    """Compute confidence in a viability assessment.

    Confidence grows with sample count and is reduced when
    success and failure counts are close (ambiguous signal).
    """
    if total == 0:
        return 0.0

    # Base confidence from sample size (asymptotic to 1.0)
    sample_confidence = 1.0 - (1.0 / (1.0 + total * 0.5))

    # Clarity: how skewed is the success/failure ratio?
    if total == 0:
        clarity = 0.0
    else:
        majority = max(success_count, failure_count)
        clarity = majority / total

    return min(1.0, sample_confidence * clarity)


# ---------------------------------------------------------------------------
# ViabilityInference
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ViabilityConfig:
    """Configuration for viability inference.

    Attributes
    ----------
    min_traces_for_viable : int
        Minimum number of successful traces required to classify as VIABLE.
    conditional_threshold : float
        If the success rate is between this value and 1.0, classify as
        CONDITIONALLY_VIABLE instead of NON_VIABLE.
    include_unknown : bool
        Whether to include UNKNOWN sites in the result.
    """

    min_traces_for_viable: int = 1
    conditional_threshold: float = 0.1
    include_unknown: bool = True


_DEFAULT_VIABILITY_CONFIG = ViabilityConfig()


class ViabilityInference:
    """Infers error-site viability from observed traces.

    Parameters
    ----------
    config : ViabilityConfig
        Configuration for the inference.
    """

    def __init__(
        self,
        config: ViabilityConfig = _DEFAULT_VIABILITY_CONFIG,
    ) -> None:
        self._config = config

    @property
    def config(self) -> ViabilityConfig:
        return self._config

    def infer(
        self,
        traces: Sequence[ParsedTrace],
        cover: Cover,
    ) -> ViabilityResult:
        """Infer viability for all error sites in *cover* using *traces*.

        Parameters
        ----------
        traces : Sequence[ParsedTrace]
            Parsed traces to analyse.
        cover : Cover
            The cover defining the error sites.

        Returns
        -------
        ViabilityResult
            Complete viability inference result.
        """
        error_site_ids = cover.error_sites
        if not error_site_ids:
            return ViabilityResult(total_traces_used=len(traces))

        # Accumulate per-site evidence across all traces
        site_successes: Dict[SiteId, int] = defaultdict(int)
        site_failures: Dict[SiteId, int] = defaultdict(int)
        site_failure_types: Dict[SiteId, Set[str]] = defaultdict(set)
        site_evidence_ids: Dict[SiteId, List[str]] = defaultdict(list)
        site_exercised: Dict[SiteId, int] = defaultdict(int)

        for trace in traces:
            # Collect all exceptions in this trace
            trace_exceptions: List[ExceptionObservation] = list(trace.all_exceptions)

            for site_id in error_site_ids:
                # Check if this trace exercises the site's function
                exercised = False
                for fo in trace.function_observations:
                    if _site_is_exercised_by_function(site_id, fo):
                        exercised = True
                        break

                if not exercised:
                    continue

                site_exercised[site_id] += 1
                site_evidence_ids[site_id].append(trace.trace_id)

                # Check if any exception matches this site
                matched_exception = False
                for exc in trace_exceptions:
                    if _site_matches_exception(site_id, exc):
                        site_failures[site_id] += 1
                        site_failure_types[site_id].add(exc.exception_type)
                        matched_exception = True
                        break

                if not matched_exception:
                    site_successes[site_id] += 1

        # Build per-site viability assessments
        viabilities: List[SiteViability] = []
        viable_set: Set[SiteId] = set()
        non_viable_set: Set[SiteId] = set()
        conditional_set: Set[SiteId] = set()
        unknown_set: Set[SiteId] = set()

        for site_id in error_site_ids:
            total = site_exercised.get(site_id, 0)
            successes = site_successes.get(site_id, 0)
            failures = site_failures.get(site_id, 0)
            failure_types = sorted(site_failure_types.get(site_id, set()))
            evidence_ids = site_evidence_ids.get(site_id, [])
            confidence = _compute_confidence(successes, failures, total)

            if total == 0:
                level = ViabilityLevel.UNKNOWN
                explanation = (
                    f"No traces exercised error site {site_id.name}"
                )
                unknown_set.add(site_id)
            elif failures == 0 and successes >= self._config.min_traces_for_viable:
                level = ViabilityLevel.VIABLE
                explanation = (
                    f"Error site {site_id.name} succeeded in all "
                    f"{successes} observed executions"
                )
                viable_set.add(site_id)
            elif successes == 0:
                level = ViabilityLevel.NON_VIABLE
                explanation = (
                    f"Error site {site_id.name} failed in all "
                    f"{failures} observed executions "
                    f"(exceptions: {', '.join(failure_types)})"
                )
                non_viable_set.add(site_id)
            else:
                success_rate = successes / total
                if success_rate >= (1.0 - self._config.conditional_threshold):
                    level = ViabilityLevel.VIABLE
                    explanation = (
                        f"Error site {site_id.name} succeeded in "
                        f"{successes}/{total} executions "
                        f"(rate={success_rate:.2%})"
                    )
                    viable_set.add(site_id)
                elif success_rate >= self._config.conditional_threshold:
                    level = ViabilityLevel.CONDITIONALLY_VIABLE
                    explanation = (
                        f"Error site {site_id.name} succeeded in "
                        f"{successes}/{total} executions "
                        f"(rate={success_rate:.2%}, input-dependent)"
                    )
                    conditional_set.add(site_id)
                else:
                    level = ViabilityLevel.NON_VIABLE
                    explanation = (
                        f"Error site {site_id.name} failed in "
                        f"{failures}/{total} executions "
                        f"(exceptions: {', '.join(failure_types)})"
                    )
                    non_viable_set.add(site_id)

            sv = SiteViability(
                site_id=site_id,
                level=level,
                success_count=successes,
                failure_count=failures,
                total_traces=total,
                failure_types=tuple(failure_types),
                confidence=confidence,
                evidence_trace_ids=tuple(evidence_ids[:20]),
                explanation=explanation,
            )
            if level != ViabilityLevel.UNKNOWN or self._config.include_unknown:
                viabilities.append(sv)

        # Overall confidence
        confidences = [sv.confidence for sv in viabilities if sv.total_traces > 0]
        overall_conf = sum(confidences) / len(confidences) if confidences else 0.0

        return ViabilityResult(
            site_viabilities=tuple(viabilities),
            viable_sites=frozenset(viable_set),
            non_viable_sites=frozenset(non_viable_set),
            conditional_sites=frozenset(conditional_set),
            unknown_sites=frozenset(unknown_set),
            total_traces_used=len(traces),
            overall_confidence=overall_conf,
        )


# ---------------------------------------------------------------------------
# Convenience function
# ---------------------------------------------------------------------------

def infer_viability(
    traces: Sequence[ParsedTrace],
    cover: Cover,
    *,
    min_traces_for_viable: int = 1,
    conditional_threshold: float = 0.1,
) -> Dict[SiteId, bool]:
    """Infer viability for error sites and return a simple boolean mapping.

    This is a convenience wrapper around :class:`ViabilityInference`.

    Parameters
    ----------
    traces : Sequence[ParsedTrace]
        Parsed traces to analyse.
    cover : Cover
        The cover defining error sites.
    min_traces_for_viable : int
        Minimum successful traces for VIABLE classification.
    conditional_threshold : float
        Threshold for conditional viability.

    Returns
    -------
    Dict[SiteId, bool]
        ``{site_id: True}`` for viable sites, ``False`` otherwise.
    """
    config = ViabilityConfig(
        min_traces_for_viable=min_traces_for_viable,
        conditional_threshold=conditional_threshold,
    )
    inference = ViabilityInference(config)
    result = inference.infer(traces, cover)
    return result.as_dict()


# ---------------------------------------------------------------------------
# Viability-to-section integration
# ---------------------------------------------------------------------------

def viability_to_sections(
    result: ViabilityResult,
) -> List[LocalSection]:
    """Convert viability assessments into :class:`LocalSection` objects.

    Each error site gets a section with its viability classification
    recorded in the refinements and ``trust=TrustLevel.TRACE_BACKED``.

    Parameters
    ----------
    result : ViabilityResult
        The viability inference result.

    Returns
    -------
    List[LocalSection]
        One section per assessed error site.
    """
    sections: List[LocalSection] = []
    for sv in result.site_viabilities:
        refinements: Dict[str, Any] = {
            "viable": sv.is_viable,
            "viability_level": sv.level.value,
            "success_count": sv.success_count,
            "failure_count": sv.failure_count,
            "total_traces": sv.total_traces,
            "confidence": sv.confidence,
            "success_rate": sv.success_rate,
        }
        if sv.failure_types:
            refinements["failure_types"] = list(sv.failure_types)

        witnesses: Dict[str, Any] = {
            "evidence_trace_ids": list(sv.evidence_trace_ids[:10]),
            "explanation": sv.explanation,
        }

        section = LocalSection(
            site_id=sv.site_id,
            carrier_type="viability",
            refinements=refinements,
            trust=TrustLevel.TRACE_BACKED,
            provenance=f"viability inference, {sv.total_traces} traces",
            witnesses=witnesses,
        )
        sections.append(section)

    return sections
