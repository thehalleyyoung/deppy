"""Recommend actions to resolve type diagnostics.

RecommendationEngine analyzes diagnostics and generates actionable
recommendations:  guard insertions, annotation additions, proof
obligations, trust upgrades, and refactoring suggestions.

Each recommendation carries a confidence score and is categorized
so that IDE integrations can present them as quick-fixes.
"""

from __future__ import annotations

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
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)


# ---------------------------------------------------------------------------
# Recommendation data types
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Recommendation:
    """An actionable recommendation to resolve a diagnostic.

    Attributes:
        kind: Category of the recommendation.
        title: Short title for display.
        description: Full description of the suggested action.
        code_action: Optional code snippet for the fix.
        target_sites: Sites this recommendation applies to.
        confidence: Confidence in the correctness of this suggestion.
        priority: Ordering priority (lower = more urgent).
        diagnostic_ref: Reference back to the originating diagnostic.
    """

    _kind: str
    _title: str
    _description: str
    _code_action: str = ""
    _target_sites: FrozenSet[SiteId] = field(default_factory=frozenset)
    _confidence: float = 0.5
    _priority: int = 5
    _diagnostic_ref: Optional[Any] = None

    @property
    def kind(self) -> str:
        return self._kind

    @property
    def title(self) -> str:
        return self._title

    @property
    def description(self) -> str:
        return self._description

    @property
    def code_action(self) -> str:
        return self._code_action

    @property
    def target_sites(self) -> FrozenSet[SiteId]:
        return self._target_sites

    @property
    def confidence(self) -> float:
        return self._confidence

    @property
    def priority(self) -> int:
        return self._priority

    @property
    def diagnostic_ref(self) -> Optional[Any]:
        return self._diagnostic_ref


# ---------------------------------------------------------------------------
# Recommendation kinds
# ---------------------------------------------------------------------------

class RecKind:
    """Standard recommendation categories."""

    GUARD = "add_guard"
    ANNOTATION = "add_annotation"
    PROOF = "add_proof"
    TRUST_UPGRADE = "upgrade_trust"
    REFACTOR = "refactor"
    WIDEN_TYPE = "widen_type"
    NARROW_TYPE = "narrow_type"
    INVARIANT = "add_invariant"
    NONE_CHECK = "add_none_check"
    BOUNDS_CHECK = "add_bounds_check"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _extract_variable(site_id: SiteId) -> str:
    """Extract variable name from site ID."""
    name = site_id.name
    for sep in (".", ":", "/"):
        parts = name.rsplit(sep, 1)
        if len(parts) == 2:
            return parts[1]
    return name


def _sites_from_diagnostic(diag: Any) -> Set[SiteId]:
    """Extract sites from a diagnostic or obstruction."""
    sites: Set[SiteId] = set()

    obs = None
    if isinstance(diag, ObstructionData):
        obs = diag
    elif hasattr(diag, "obstruction") and diag.obstruction is not None:
        obs = diag.obstruction

    if obs is not None:
        for a_id, b_id in obs.conflicting_overlaps:
            sites.add(a_id)
            sites.add(b_id)

    return sites


def _classify_diagnostic(diag: Any) -> str:
    """Classify a diagnostic by analyzing its content."""
    explanation = ""
    if isinstance(diag, ObstructionData):
        explanation = diag.explanation.lower()
    elif hasattr(diag, "obstruction") and diag.obstruction is not None:
        explanation = diag.obstruction.explanation.lower()
    elif hasattr(diag, "message"):
        explanation = diag.message.lower()

    if "guard" in explanation or "branch" in explanation or "narrowing" in explanation:
        return "guard"
    if "none" in explanation or "optional" in explanation or "nullable" in explanation:
        return "none_safety"
    if "bound" in explanation or "range" in explanation or "overflow" in explanation:
        return "bounds"
    if "annotation" in explanation or "missing type" in explanation:
        return "annotation"
    if "proof" in explanation or "invariant" in explanation:
        return "proof"
    if "mismatch" in explanation or "incompatible" in explanation:
        return "mismatch"
    if "shape" in explanation or "dimension" in explanation:
        return "shape"
    return "general"


# ---------------------------------------------------------------------------
# Individual recommendation generators
# ---------------------------------------------------------------------------

def _recommend_guard(
    diag: Any,
    sites: Set[SiteId],
) -> Recommendation:
    """Recommend adding a type guard."""
    var_names = sorted({_extract_variable(s) for s in sites})[:3]
    primary = var_names[0] if var_names else "x"

    return Recommendation(
        _kind=RecKind.GUARD,
        _title=f"Add type guard for '{primary}'",
        _description=(
            f"Insert an isinstance check or type guard for '{primary}' "
            f"to narrow the type on the relevant branch. This will "
            f"resolve the type ambiguity at the overlap."
        ),
        _code_action=(
            f"if isinstance({primary}, ExpectedType):\n"
            f"    # {primary} is narrowed to ExpectedType here\n"
            f"    ...\n"
            f"else:\n"
            f"    raise TypeError(f\"Unexpected type: {{type({primary})}}\")"
        ),
        _target_sites=frozenset(sites),
        _confidence=0.80,
        _priority=2,
        _diagnostic_ref=diag,
    )


def _recommend_annotation(
    diag: Any,
    sites: Set[SiteId],
) -> Recommendation:
    """Recommend adding type annotations."""
    boundary_sites = {
        s for s in sites
        if s.kind in (SiteKind.ARGUMENT_BOUNDARY, SiteKind.RETURN_OUTPUT_BOUNDARY)
    }
    target = boundary_sites if boundary_sites else sites

    var_names = sorted({_extract_variable(s) for s in target})[:3]
    vars_str = ", ".join(var_names)

    return Recommendation(
        _kind=RecKind.ANNOTATION,
        _title=f"Add type annotation for {vars_str}",
        _description=(
            f"Add explicit type annotations for {vars_str} to provide "
            f"the type information that could not be inferred."
        ),
        _code_action=(
            f"# Add type annotations:\n"
            f"def func({vars_str}: ExpectedType) -> ReturnType:\n"
            f"    ..."
        ),
        _target_sites=frozenset(target),
        _confidence=0.70,
        _priority=3,
        _diagnostic_ref=diag,
    )


def _recommend_proof(
    diag: Any,
    sites: Set[SiteId],
) -> Recommendation:
    """Recommend providing a proof obligation."""
    explanation = ""
    if isinstance(diag, ObstructionData):
        explanation = diag.explanation
    elif hasattr(diag, "obstruction") and diag.obstruction is not None:
        explanation = diag.obstruction.explanation

    return Recommendation(
        _kind=RecKind.PROOF,
        _title="Provide proof for verification condition",
        _description=(
            f"A verification condition could not be automatically "
            f"discharged. Provide a proof seed or theorem to verify: "
            f"{explanation[:100]}"
        ),
        _code_action=(
            "@deppy.proof\n"
            "def my_proof(x: T) -> deppy.Proof[property]:\n"
            "    return deppy.by_construction(...)"
        ),
        _target_sites=frozenset(sites),
        _confidence=0.65,
        _priority=4,
        _diagnostic_ref=diag,
    )


def _recommend_none_check(
    diag: Any,
    sites: Set[SiteId],
) -> Recommendation:
    """Recommend adding a None check."""
    var_names = sorted({_extract_variable(s) for s in sites})[:3]
    primary = var_names[0] if var_names else "value"

    return Recommendation(
        _kind=RecKind.NONE_CHECK,
        _title=f"Add None check for '{primary}'",
        _description=(
            f"The value '{primary}' may be None at this point. "
            f"Add a None check before use to prevent potential "
            f"NoneType errors."
        ),
        _code_action=(
            f"if {primary} is None:\n"
            f"    raise ValueError(\"{primary} must not be None\")\n"
            f"# {primary} is now guaranteed non-None"
        ),
        _target_sites=frozenset(sites),
        _confidence=0.90,
        _priority=1,
        _diagnostic_ref=diag,
    )


def _recommend_bounds_check(
    diag: Any,
    sites: Set[SiteId],
) -> Recommendation:
    """Recommend adding bounds validation."""
    var_names = sorted({_extract_variable(s) for s in sites})[:3]
    primary = var_names[0] if var_names else "value"

    return Recommendation(
        _kind=RecKind.BOUNDS_CHECK,
        _title=f"Add bounds check for '{primary}'",
        _description=(
            f"The value '{primary}' may exceed the expected bounds. "
            f"Add validation to ensure it stays within range."
        ),
        _code_action=(
            f"if not (LOWER <= {primary} <= UPPER):\n"
            f"    raise ValueError(\n"
            f"        f\"{primary} must be in [{{LOWER}}, {{UPPER}}], "
            f"got {{{primary}}}\"\n"
            f"    )"
        ),
        _target_sites=frozenset(sites),
        _confidence=0.80,
        _priority=2,
        _diagnostic_ref=diag,
    )


def _recommend_widen_type(
    diag: Any,
    sites: Set[SiteId],
) -> Recommendation:
    """Recommend widening the type to a Union."""
    return Recommendation(
        _kind=RecKind.WIDEN_TYPE,
        _title="Widen type annotation to Union",
        _description=(
            "The current type annotation is too narrow for the values "
            "that flow through this site. Consider widening to a Union "
            "type to accommodate all branches."
        ),
        _code_action=(
            "# Change the type annotation:\n"
            "x: Union[TypeA, TypeB] = ...  # was: x: TypeA"
        ),
        _target_sites=frozenset(sites),
        _confidence=0.65,
        _priority=4,
        _diagnostic_ref=diag,
    )


def _recommend_invariant(
    diag: Any,
    sites: Set[SiteId],
) -> Recommendation:
    """Recommend adding a loop invariant."""
    loop_sites = {s for s in sites if s.kind == SiteKind.LOOP_HEADER_INVARIANT}
    target = loop_sites if loop_sites else sites

    return Recommendation(
        _kind=RecKind.INVARIANT,
        _title="Add loop invariant",
        _description=(
            "The loop body could not be verified without an invariant. "
            "Provide an invariant annotation that captures the type "
            "relationship maintained across iterations."
        ),
        _code_action=(
            "@deppy.loop_invariant\n"
            "def invariant(i, acc):\n"
            "    return acc >= 0 and i >= 0"
        ),
        _target_sites=frozenset(target),
        _confidence=0.70,
        _priority=3,
        _diagnostic_ref=diag,
    )


# ---------------------------------------------------------------------------
# RecommendationEngine
# ---------------------------------------------------------------------------

class RecommendationEngine:
    """Generate actionable recommendations for type diagnostics.

    Analyzes diagnostics and produces prioritized recommendations
    for resolving type errors.

    Usage::

        engine = RecommendationEngine()
        recs = engine.recommend(diagnostics, cover)
        for r in recs:
            print(f"[{r.kind}] {r.title} (confidence={r.confidence:.0%})")
    """

    def __init__(
        self,
        *,
        min_confidence: float = 0.0,
        max_recommendations: int = 10,
        max_per_diagnostic: int = 3,
    ) -> None:
        self._min_confidence = min_confidence
        self._max_total = max_recommendations
        self._max_per_diag = max_per_diagnostic

    def recommend(
        self,
        diagnostics: List[Any],
        cover: Optional[Cover] = None,
    ) -> List[Recommendation]:
        """Generate recommendations for all diagnostics.

        Returns a list sorted by (priority, -confidence).
        """
        all_recs: List[Recommendation] = []

        for diag in diagnostics:
            recs = self._recommend_for_diagnostic(diag, cover)
            filtered = [
                r for r in recs if r.confidence >= self._min_confidence
            ]
            filtered.sort(key=lambda r: (r.priority, -r.confidence))
            all_recs.extend(filtered[: self._max_per_diag])

        all_recs.sort(key=lambda r: (r.priority, -r.confidence))
        return _deduplicate_recommendations(all_recs)[: self._max_total]

    def _recommend_for_diagnostic(
        self,
        diag: Any,
        cover: Optional[Cover],
    ) -> List[Recommendation]:
        """Generate recommendations for a single diagnostic."""
        sites = _sites_from_diagnostic(diag)
        classification = _classify_diagnostic(diag)
        recs: List[Recommendation] = []

        if classification == "none_safety":
            recs.append(_recommend_none_check(diag, sites))
            recs.append(_recommend_guard(diag, sites))
        elif classification == "guard":
            recs.append(_recommend_guard(diag, sites))
        elif classification == "bounds":
            recs.append(_recommend_bounds_check(diag, sites))
        elif classification == "annotation":
            recs.append(_recommend_annotation(diag, sites))
        elif classification == "proof":
            recs.append(_recommend_proof(diag, sites))
            loop_sites = {s for s in sites if s.kind == SiteKind.LOOP_HEADER_INVARIANT}
            if loop_sites:
                recs.append(_recommend_invariant(diag, sites))
        elif classification == "mismatch":
            recs.append(_recommend_guard(diag, sites))
            recs.append(_recommend_widen_type(diag, sites))
        elif classification == "shape":
            recs.append(_recommend_annotation(diag, sites))
        else:
            recs.append(_recommend_annotation(diag, sites))
            recs.append(_recommend_guard(diag, sites))

        return recs

    def _recommend_guard(self, diag: Any) -> Recommendation:
        """Instance method for guard recommendation."""
        sites = _sites_from_diagnostic(diag)
        return _recommend_guard(diag, sites)

    def _recommend_annotation(self, diag: Any) -> Recommendation:
        """Instance method for annotation recommendation."""
        sites = _sites_from_diagnostic(diag)
        return _recommend_annotation(diag, sites)

    def _recommend_proof(self, diag: Any) -> Recommendation:
        """Instance method for proof recommendation."""
        sites = _sites_from_diagnostic(diag)
        return _recommend_proof(diag, sites)

    def summarize(
        self,
        recommendations: List[Recommendation],
    ) -> str:
        """Produce a human-readable summary of recommendations."""
        if not recommendations:
            return "No recommendations generated."

        lines: List[str] = []
        lines.append(f"Recommendations ({len(recommendations)} total):")
        lines.append("=" * 60)

        by_kind: Dict[str, List[Recommendation]] = {}
        for r in recommendations:
            by_kind.setdefault(r.kind, []).append(r)

        for kind, kind_recs in sorted(by_kind.items()):
            lines.append(f"\n  [{kind}] ({len(kind_recs)} recommendations)")
            for i, r in enumerate(kind_recs, 1):
                lines.append(
                    f"    {i}. [{r.confidence:.0%}] {r.title}"
                )
                if r.code_action:
                    first_line = r.code_action.split("\n")[0]
                    lines.append(f"       Code: {first_line}")

        return "\n".join(lines)


def _deduplicate_recommendations(
    recs: List[Recommendation],
) -> List[Recommendation]:
    """Remove duplicate recommendations."""
    seen: Set[Tuple[str, FrozenSet[SiteId]]] = set()
    deduped: List[Recommendation] = []
    for r in recs:
        key = (r.kind, r.target_sites)
        if key not in seen:
            seen.add(key)
            deduped.append(r)
    return deduped
