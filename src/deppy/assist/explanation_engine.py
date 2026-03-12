"""Generate explanations for diagnostics.

ExplanationEngine produces human-readable explanations of *why* a type
error occurs by tracing back through the sheaf structure.  It follows
the provenance chain from the error site to its origins, explaining
each step in the derivation.
"""

from __future__ import annotations

from collections import defaultdict, deque
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
# Explanation data types
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ExplanationStep:
    """A single step in an explanation chain.

    Attributes:
        site_id: The site this step refers to.
        description: What happened at this step.
        detail: Additional detail (type info, refinements).
        is_origin: Whether this is the origin of the chain.
        is_error: Whether this is the error endpoint.
    """

    _site_id: SiteId
    _description: str
    _detail: str = ""
    _is_origin: bool = False
    _is_error: bool = False

    @property
    def site_id(self) -> SiteId:
        return self._site_id

    @property
    def description(self) -> str:
        return self._description

    @property
    def detail(self) -> str:
        return self._detail

    @property
    def is_origin(self) -> bool:
        return self._is_origin

    @property
    def is_error(self) -> bool:
        return self._is_error


@dataclass(frozen=True)
class Explanation:
    """A complete explanation for a diagnostic.

    Attributes:
        summary: One-sentence summary of the error.
        steps: Chain of explanation steps from origin to error.
        root_cause: Best-guess root cause description.
        affected_variables: Variable names involved.
        related_sites: Sites related to this explanation.
        obstruction: The underlying obstruction, if any.
    """

    _summary: str
    _steps: Tuple[ExplanationStep, ...]
    _root_cause: str = ""
    _affected_variables: FrozenSet[str] = field(default_factory=frozenset)
    _related_sites: FrozenSet[SiteId] = field(default_factory=frozenset)
    _obstruction: Optional[ObstructionData] = None

    @property
    def summary(self) -> str:
        return self._summary

    @property
    def steps(self) -> Tuple[ExplanationStep, ...]:
        return self._steps

    @property
    def root_cause(self) -> str:
        return self._root_cause

    @property
    def affected_variables(self) -> FrozenSet[str]:
        return self._affected_variables

    @property
    def related_sites(self) -> FrozenSet[SiteId]:
        return self._related_sites

    @property
    def obstruction(self) -> Optional[ObstructionData]:
        return self._obstruction


# ---------------------------------------------------------------------------
# Graph helpers
# ---------------------------------------------------------------------------

def _build_reverse_adj(cover: Cover) -> Dict[SiteId, Set[SiteId]]:
    """Build reverse adjacency from morphisms."""
    rev: Dict[SiteId, Set[SiteId]] = defaultdict(set)
    for m in cover.morphisms:
        rev[m.target].add(m.source)
    return rev


def _build_forward_adj(cover: Cover) -> Dict[SiteId, Set[SiteId]]:
    """Build forward adjacency from morphisms."""
    adj: Dict[SiteId, Set[SiteId]] = defaultdict(set)
    for m in cover.morphisms:
        adj[m.source].add(m.target)
    return adj


def _trace_back(
    site_id: SiteId,
    rev_adj: Dict[SiteId, Set[SiteId]],
    max_depth: int = 20,
) -> List[SiteId]:
    """Trace backward from a site to its origins."""
    path: List[SiteId] = [site_id]
    visited: Set[SiteId] = {site_id}
    current = site_id

    for _ in range(max_depth):
        predecessors = rev_adj.get(current, set()) - visited
        if not predecessors:
            break
        pred = min(predecessors, key=str)
        path.append(pred)
        visited.add(pred)
        current = pred

    path.reverse()
    return path


def _extract_variable_name(site_id: SiteId) -> str:
    """Extract variable name from site ID."""
    name = site_id.name
    for sep in (".", ":", "/"):
        parts = name.rsplit(sep, 1)
        if len(parts) == 2:
            return parts[1]
    return name


def _describe_site_kind(kind: SiteKind) -> str:
    """Get a human-readable description of a site kind."""
    descriptions = {
        SiteKind.ARGUMENT_BOUNDARY: "function parameter",
        SiteKind.RETURN_OUTPUT_BOUNDARY: "return value",
        SiteKind.SSA_VALUE: "local variable",
        SiteKind.BRANCH_GUARD: "branch condition",
        SiteKind.CALL_RESULT: "function call result",
        SiteKind.TENSOR_SHAPE: "tensor shape",
        SiteKind.TENSOR_ORDER: "tensor order",
        SiteKind.TENSOR_INDEXING: "tensor indexing",
        SiteKind.HEAP_PROTOCOL: "heap protocol",
        SiteKind.PROOF: "proof obligation",
        SiteKind.TRACE: "runtime trace",
        SiteKind.ERROR: "error handler",
        SiteKind.LOOP_HEADER_INVARIANT: "loop invariant",
        SiteKind.MODULE_SUMMARY: "module summary",
    }
    return descriptions.get(kind, kind.value)


def _describe_section(
    site_id: SiteId,
    sections: Dict[SiteId, LocalSection],
) -> str:
    """Describe a section at a site."""
    sec = sections.get(site_id)
    if sec is None:
        return "no type information available"

    parts: List[str] = []
    if sec.carrier_type is not None:
        parts.append(f"type is {repr(sec.carrier_type)}")
    if sec.refinements:
        ref_keys = sorted(sec.refinements.keys())[:3]
        parts.append(f"with refinements: {', '.join(ref_keys)}")
    parts.append(f"trust level: {sec.trust.value}")

    return ", ".join(parts)


def _classify_error(obs: ObstructionData) -> str:
    """Classify the error for explanation purposes."""
    explanation = obs.explanation.lower()
    if "guard" in explanation or "branch" in explanation:
        return "missing type guard"
    if "none" in explanation or "optional" in explanation:
        return "potential None usage"
    if "bound" in explanation or "range" in explanation:
        return "value out of bounds"
    if "mismatch" in explanation or "incompatible" in explanation:
        return "type mismatch"
    if "shape" in explanation:
        return "shape incompatibility"
    if "protocol" in explanation:
        return "protocol violation"
    return "type conflict"


# ---------------------------------------------------------------------------
# Provenance tracing
# ---------------------------------------------------------------------------

def _trace_provenance(
    site_id: SiteId,
    sections: Dict[SiteId, LocalSection],
    cover: Cover,
) -> List[str]:
    """Trace the provenance chain for a site.

    Follows section provenance strings and morphism structure to build
    a human-readable chain of reasoning steps.
    """
    chain: List[str] = []
    rev_adj = _build_reverse_adj(cover)
    path = _trace_back(site_id, rev_adj)

    for i, sid in enumerate(path):
        sec = sections.get(sid)
        kind_desc = _describe_site_kind(sid.kind)
        var_name = _extract_variable_name(sid)

        if i == 0:
            if sec is not None and sec.provenance:
                chain.append(
                    f"Origin: {kind_desc} '{var_name}' "
                    f"({sec.provenance})"
                )
            else:
                chain.append(f"Origin: {kind_desc} '{var_name}'")
        elif i == len(path) - 1:
            type_desc = ""
            if sec is not None and sec.carrier_type is not None:
                type_desc = f" with type {repr(sec.carrier_type)}"
            chain.append(
                f"Error site: {kind_desc} '{var_name}'{type_desc}"
            )
        else:
            if sec is not None and sec.provenance:
                chain.append(
                    f"Step {i}: {kind_desc} '{var_name}' "
                    f"({sec.provenance})"
                )
            else:
                chain.append(
                    f"Step {i}: passed through {kind_desc} '{var_name}'"
                )

    return chain


# ---------------------------------------------------------------------------
# ExplanationEngine
# ---------------------------------------------------------------------------

class ExplanationEngine:
    """Generate explanations for diagnostics by tracing sheaf structure.

    Produces human-readable explanations of why a type error occurs,
    tracing back through the cover's morphism structure and section
    provenance to identify the root cause.

    Usage::

        engine = ExplanationEngine()
        explanation = engine.explain(diagnostic, cover, sections)
        print(explanation.summary)
        for step in explanation.steps:
            print(f"  {step.description}")
    """

    def __init__(
        self,
        *,
        max_trace_depth: int = 20,
        include_type_details: bool = True,
        include_refinement_details: bool = True,
    ) -> None:
        self._max_depth = max_trace_depth
        self._include_types = include_type_details
        self._include_refs = include_refinement_details

    def explain(
        self,
        diagnostic: Any,
        cover: Cover,
        sections: Optional[Dict[SiteId, LocalSection]] = None,
    ) -> Explanation:
        """Generate a full explanation for a diagnostic.

        The diagnostic can be an ObstructionData or any object with
        an 'obstruction' attribute.
        """
        if sections is None:
            sections = {}

        obs: Optional[ObstructionData] = None
        if isinstance(diagnostic, ObstructionData):
            obs = diagnostic
        elif hasattr(diagnostic, "obstruction"):
            obs = diagnostic.obstruction

        if obs is None:
            return self._explain_generic(diagnostic, cover, sections)

        return self._explain_obstruction(obs, cover, sections)

    def _explain_obstruction(
        self,
        obs: ObstructionData,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Explanation:
        """Generate explanation for an obstruction."""
        error_class = _classify_error(obs)
        sites: Set[SiteId] = set()
        for a_id, b_id in obs.conflicting_overlaps:
            sites.add(a_id)
            sites.add(b_id)

        variables = frozenset(_extract_variable_name(s) for s in sites)
        vars_str = ", ".join(sorted(variables)[:3])

        summary = (
            f"{error_class.capitalize()} involving {vars_str}: "
            f"{obs.explanation}" if obs.explanation else
            f"{error_class.capitalize()} involving {vars_str}"
        )

        steps = self._build_steps(obs, cover, sections)
        root_cause = self._identify_root_cause(obs, cover, sections)

        return Explanation(
            _summary=summary,
            _steps=tuple(steps),
            _root_cause=root_cause,
            _affected_variables=variables,
            _related_sites=frozenset(sites),
            _obstruction=obs,
        )

    def _explain_generic(
        self,
        diagnostic: Any,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Explanation:
        """Generate explanation for a non-obstruction diagnostic."""
        message = getattr(diagnostic, "message", str(diagnostic))
        severity = getattr(diagnostic, "severity", "error")

        return Explanation(
            _summary=f"{severity}: {message}",
            _steps=(),
            _root_cause=message,
        )

    def _build_steps(
        self,
        obs: ObstructionData,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[ExplanationStep]:
        """Build explanation steps by tracing provenance."""
        steps: List[ExplanationStep] = []
        rev_adj = _build_reverse_adj(cover)

        error_sites: List[SiteId] = []
        for a_id, b_id in obs.conflicting_overlaps:
            error_sites.extend([a_id, b_id])

        traced_sites: Set[SiteId] = set()

        for error_site in error_sites:
            if error_site in traced_sites:
                continue

            path = _trace_back(error_site, rev_adj, self._max_depth)

            for i, sid in enumerate(path):
                if sid in traced_sites:
                    continue
                traced_sites.add(sid)

                sec = sections.get(sid)
                kind_desc = _describe_site_kind(sid.kind)
                var_name = _extract_variable_name(sid)

                is_origin = (i == 0)
                is_error = (i == len(path) - 1 and sid in error_sites)

                description = self._describe_step(
                    sid, sec, kind_desc, var_name, is_origin, is_error
                )
                detail = ""
                if self._include_types and sec is not None:
                    detail = _describe_section(sid, sections)

                steps.append(ExplanationStep(
                    _site_id=sid,
                    _description=description,
                    _detail=detail,
                    _is_origin=is_origin,
                    _is_error=is_error,
                ))

        return steps

    def _describe_step(
        self,
        site_id: SiteId,
        section: Optional[LocalSection],
        kind_desc: str,
        var_name: str,
        is_origin: bool,
        is_error: bool,
    ) -> str:
        """Generate a description for a single step."""
        if is_origin:
            desc = f"Type information originates at {kind_desc} '{var_name}'"
            if section is not None and section.carrier_type is not None:
                desc += f" with type {repr(section.carrier_type)}"
            return desc

        if is_error:
            desc = f"Type conflict detected at {kind_desc} '{var_name}'"
            return desc

        desc = f"Type flows through {kind_desc} '{var_name}'"
        if section is not None and section.provenance:
            desc += f" ({section.provenance})"
        return desc

    def _identify_root_cause(
        self,
        obs: ObstructionData,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> str:
        """Identify the likely root cause of an obstruction."""
        error_class = _classify_error(obs)

        if error_class == "missing type guard":
            return (
                "A type guard (isinstance check or similar) is needed "
                "to narrow the type before it can be used at this site."
            )
        if error_class == "potential None usage":
            return (
                "A value that may be None is used in a context that "
                "requires a non-None value."
            )
        if error_class == "value out of bounds":
            return (
                "A numeric value may exceed the expected bounds "
                "at this site."
            )
        if error_class == "type mismatch":
            if obs.conflicting_overlaps:
                a_id = obs.conflicting_overlaps[0][0]
                b_id = obs.conflicting_overlaps[0][1]
                sec_a = sections.get(a_id)
                sec_b = sections.get(b_id)
                if sec_a and sec_b:
                    return (
                        f"Type {repr(sec_a.carrier_type)} at "
                        f"{a_id.name} is incompatible with "
                        f"type {repr(sec_b.carrier_type)} at "
                        f"{b_id.name}."
                    )
            return (
                "Two sites carry incompatible types in their overlap "
                "region."
            )

        return obs.explanation or "Type conflict in the sheaf structure."

    def _trace_provenance(
        self,
        site: SiteId,
        sections: Dict[SiteId, LocalSection],
        cover: Optional[Cover] = None,
    ) -> List[str]:
        """Trace provenance for a site (public API)."""
        if cover is None:
            cover = Cover()
        return _trace_provenance(site, sections, cover)

    def explain_site(
        self,
        site_id: SiteId,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> str:
        """Generate a short explanation for a specific site."""
        kind_desc = _describe_site_kind(site_id.kind)
        var_name = _extract_variable_name(site_id)
        sec_desc = _describe_section(site_id, sections)
        provenance = _trace_provenance(site_id, sections, cover)

        lines: List[str] = []
        lines.append(f"Site: {kind_desc} '{var_name}'")
        lines.append(f"  {sec_desc}")

        if provenance:
            lines.append("  Provenance:")
            for step in provenance:
                lines.append(f"    {step}")

        return "\n".join(lines)

    def explain_overlap(
        self,
        site_a: SiteId,
        site_b: SiteId,
        sections: Dict[SiteId, LocalSection],
    ) -> str:
        """Explain why two sites conflict on their overlap."""
        sec_a = sections.get(site_a)
        sec_b = sections.get(site_b)

        lines: List[str] = []
        lines.append(
            f"Overlap between '{site_a.name}' and '{site_b.name}':"
        )

        if sec_a is not None:
            lines.append(
                f"  Left:  type={repr(sec_a.carrier_type)}, "
                f"trust={sec_a.trust.value}"
            )
        else:
            lines.append("  Left:  (no section)")

        if sec_b is not None:
            lines.append(
                f"  Right: type={repr(sec_b.carrier_type)}, "
                f"trust={sec_b.trust.value}"
            )
        else:
            lines.append("  Right: (no section)")

        if sec_a is not None and sec_b is not None:
            common = set(sec_a.refinements.keys()) & set(sec_b.refinements.keys())
            conflicts: List[str] = []
            for k in sorted(common):
                if sec_a.refinements[k] != sec_b.refinements[k]:
                    conflicts.append(
                        f"    '{k}': {sec_a.refinements[k]!r} vs "
                        f"{sec_b.refinements[k]!r}"
                    )
            if conflicts:
                lines.append("  Conflicting refinements:")
                lines.extend(conflicts)
            else:
                if repr(sec_a.carrier_type) != repr(sec_b.carrier_type):
                    lines.append(
                        f"  Carrier types differ: "
                        f"{repr(sec_a.carrier_type)} vs "
                        f"{repr(sec_b.carrier_type)}"
                    )
                else:
                    lines.append("  No obvious conflict in refinements.")

        return "\n".join(lines)
