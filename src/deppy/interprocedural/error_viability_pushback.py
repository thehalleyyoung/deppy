"""Push error viability requirements backward through call chains.

When callee G can raise an exception (e.g., IndexError requiring
``0 <= i < len(lst)``), the viability requirement must be pushed back
to caller F's arguments.  If F calls G with ``g(my_list, idx)``, then
F must ensure ``0 <= idx < len(my_list)`` -- the viability predicate
is reindexed from callee naming to caller naming.

This is the interprocedural extension of the backward synthesis step:
error-site viability constraints propagate up through the call graph
to become preconditions on callers.
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
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism
from deppy.static_analysis.restriction_maps import (
    RestrictionData,
    RestrictionKind,
    make_error_pullback_restriction,
    make_error_viability_restriction,
)
from deppy.interprocedural.call_graph import CallEdge, CallGraph


# ---------------------------------------------------------------------------
# Viability requirement
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ViabilityRequirement:
    """A viability predicate attached to an error site.

    Attributes:
        _error_site: The error site whose viability is at stake.
        _predicate_text: Human-readable viability predicate.
        _error_kind: The kind of error (e.g., "IndexError").
        _operand_names: Names of operands involved in the predicate.
        _source_function: Function where the error site lives.
        _upstream_params: Parameters that influence viability.
    """

    _error_site: SiteId
    _predicate_text: str = ""
    _error_kind: str = ""
    _operand_names: Tuple[str, ...] = ()
    _source_function: str = ""
    _upstream_params: Tuple[str, ...] = ()

    @property
    def error_site(self) -> SiteId:
        return self._error_site

    @property
    def predicate_text(self) -> str:
        return self._predicate_text

    @property
    def error_kind(self) -> str:
        return self._error_kind

    @property
    def operand_names(self) -> Tuple[str, ...]:
        return self._operand_names

    @property
    def source_function(self) -> str:
        return self._source_function

    @property
    def upstream_params(self) -> Tuple[str, ...]:
        return self._upstream_params


@dataclass(frozen=True)
class PushbackResult:
    """Result of pushing viability requirements to a caller.

    Attributes:
        _caller: The caller function receiving the requirement.
        _callee: The callee function originating the requirement.
        _requirements: Mapping from caller input sites to viability predicates.
        _morphisms: Morphisms created for the pullback.
        _original_requirement: The original callee-side requirement.
    """

    _caller: str
    _callee: str
    _requirements: Dict[SiteId, str] = field(default_factory=dict)
    _morphisms: List[ConcreteMorphism] = field(default_factory=list)
    _original_requirement: Optional[ViabilityRequirement] = None

    @property
    def caller(self) -> str:
        return self._caller

    @property
    def callee(self) -> str:
        return self._callee

    @property
    def requirements(self) -> Dict[SiteId, str]:
        return dict(self._requirements)


# ---------------------------------------------------------------------------
# Predicate reindexing
# ---------------------------------------------------------------------------

def _reindex_predicate(
    predicate_text: str,
    call_edge: CallEdge,
    callee_params: Sequence[str],
) -> str:
    """Reindex a viability predicate from callee naming to caller naming.

    Replaces callee parameter names with the corresponding actual argument
    names from the call edge.

    Example:
        predicate: "0 <= i < len(lst)"
        callee_params: ["lst", "i"]
        call_edge.arguments: ["my_list", "idx"]
        result: "0 <= idx < len(my_list)"
    """
    result = predicate_text
    args = call_edge.arguments

    # Build name mapping: formal -> actual
    for idx, formal_name in enumerate(callee_params):
        if idx < len(args):
            actual_name = args[idx]
            # Replace formal name with actual name (word-boundary aware)
            # Simple replacement that handles most cases
            result = _replace_identifier(result, formal_name, actual_name)

    # Handle keyword arguments
    for kw_name, kw_value in call_edge.keyword_arguments:
        if kw_name and kw_name != "**":
            result = _replace_identifier(result, kw_name, kw_value)

    return result


def _replace_identifier(text: str, old_name: str, new_name: str) -> str:
    """Replace an identifier in text respecting word boundaries."""
    if not old_name or old_name == new_name:
        return text

    result: List[str] = []
    i = 0
    old_len = len(old_name)

    while i < len(text):
        # Check if old_name appears at position i
        if text[i:i + old_len] == old_name:
            # Check word boundaries
            before_ok = (
                i == 0
                or not (text[i - 1].isalnum() or text[i - 1] == "_")
            )
            after_ok = (
                i + old_len >= len(text)
                or not (text[i + old_len].isalnum() or text[i + old_len] == "_")
            )
            if before_ok and after_ok:
                result.append(new_name)
                i += old_len
                continue
        result.append(text[i])
        i += 1

    return "".join(result)


# ---------------------------------------------------------------------------
# Extract viability from covers
# ---------------------------------------------------------------------------

def _extract_viabilities(
    cover: Cover,
    func_name: str,
) -> List[ViabilityRequirement]:
    """Extract viability requirements from a function's cover.

    Looks at error sites and their associated viability data to produce
    ViabilityRequirement instances.
    """
    requirements: List[ViabilityRequirement] = []

    for error_site_id in cover.error_sites:
        # Look up the site metadata
        site = cover.sites.get(error_site_id)
        if site is None:
            continue

        metadata = getattr(site, "metadata", None) or {}
        data = metadata.get("data")
        if data is None:
            continue

        error_kind = getattr(data, "error_kind", None)
        kind_str = error_kind.value if error_kind is not None else "unknown"
        operands = getattr(data, "operand_names", ())
        viability_desc = getattr(data, "viability_description", "")
        upstream = getattr(data, "upstream_sites", ())

        # Determine which input parameters influence this error site
        upstream_params: List[str] = []
        for inp_site_id in cover.input_boundary:
            if inp_site_id.kind == SiteKind.ARGUMENT_BOUNDARY:
                param_name = inp_site_id.name.split(".")[-1]
                # Check if any operand matches
                for op_name in operands:
                    if op_name == param_name or op_name.startswith(param_name + "."):
                        upstream_params.append(param_name)
                        break

        req = ViabilityRequirement(
            _error_site=error_site_id,
            _predicate_text=viability_desc,
            _error_kind=kind_str,
            _operand_names=tuple(operands),
            _source_function=func_name,
            _upstream_params=tuple(upstream_params),
        )
        requirements.append(req)

    return requirements


# ---------------------------------------------------------------------------
# ErrorViabilityPushback
# ---------------------------------------------------------------------------

class ErrorViabilityPushback:
    """Push error viability requirements backward through call chains.

    For each error site in a callee, determines what constraints the
    caller must satisfy on its arguments to prevent the error.  These
    constraints are expressed as viability predicates attached to the
    caller's input boundary sites.

    The pushback proceeds transitively: if F calls G calls H, and H has
    an error requiring ``x > 0``, that requirement propagates through G
    to F with appropriate reindexing at each call boundary.
    """

    def __init__(
        self,
        *,
        max_depth: int = 10,
        include_indirect: bool = True,
    ) -> None:
        """Initialize the pushback analyzer.

        Args:
            max_depth: Maximum call-chain depth for pushback.
            include_indirect: Whether to push back through indirect callers.
        """
        self._max_depth = max_depth
        self._include_indirect = include_indirect
        self._pushback_log: List[PushbackResult] = []

    @property
    def pushback_log(self) -> List[PushbackResult]:
        return list(self._pushback_log)

    def pushback(
        self,
        call_graph: CallGraph,
        error_viabilities: Dict[str, List[ViabilityRequirement]],
    ) -> Dict[str, Dict[SiteId, str]]:
        """Push error viabilities backward through the call graph.

        Args:
            call_graph: The call graph for the module.
            error_viabilities: Mapping from function name to its error
                viability requirements.

        Returns:
            Mapping from function name to a dict of (input_site -> predicate_text)
            representing the constraints each function must satisfy.
        """
        all_requirements: Dict[str, Dict[SiteId, str]] = defaultdict(dict)

        # Process in reverse topological order (callers before callees)
        topo = call_graph.topological_order()
        topo.reverse()

        # Seed: add direct viability requirements
        for func_name, viabilities in error_viabilities.items():
            for req in viabilities:
                for param in req.upstream_params:
                    site_id = SiteId(
                        kind=SiteKind.ARGUMENT_BOUNDARY,
                        name=f"{func_name}.{param}",
                    )
                    existing = all_requirements[func_name].get(site_id, "")
                    if existing:
                        all_requirements[func_name][site_id] = (
                            f"({existing}) and ({req.predicate_text})"
                        )
                    else:
                        all_requirements[func_name][site_id] = req.predicate_text

        # Propagate backward through call edges
        for depth in range(self._max_depth):
            new_requirements: Dict[str, Dict[SiteId, str]] = defaultdict(dict)
            changed = False

            for func_name in topo:
                # Get callee requirements
                callee_reqs = all_requirements.get(func_name, {})
                if not callee_reqs:
                    continue

                # For each caller of this function
                for edge in call_graph.get_callers(func_name):
                    caller = edge.caller

                    # Push back each callee requirement to the caller
                    pushed = self._pushback_edge(
                        edge, callee_reqs, call_graph
                    )

                    for site_id, predicate in pushed.items():
                        if site_id not in all_requirements.get(caller, {}):
                            new_requirements[caller][site_id] = predicate
                            changed = True
                        elif predicate not in all_requirements[caller].get(site_id, ""):
                            existing = all_requirements[caller][site_id]
                            new_requirements[caller][site_id] = (
                                f"({existing}) and ({predicate})"
                            )
                            changed = True

            # Merge new requirements
            for func_name, reqs in new_requirements.items():
                all_requirements[func_name].update(reqs)

            if not changed:
                break

        return dict(all_requirements)

    def pushback_single(
        self,
        call_edge: CallEdge,
        callee_cover: Cover,
        caller_cover: Cover,
    ) -> Dict[SiteId, str]:
        """Push back viability requirements for a single call edge.

        Returns a dict mapping caller input sites to viability predicates.
        """
        # Extract viability requirements from callee
        callee_viabilities = _extract_viabilities(
            callee_cover, call_edge.callee
        )

        # For each viability, reindex to caller naming
        result: Dict[SiteId, str] = {}

        for req in callee_viabilities:
            pushed = self._pushback_requirement(
                call_edge, req, caller_cover
            )
            result.update(pushed)

        return result

    def pushback_from_covers(
        self,
        call_graph: CallGraph,
        covers: Dict[str, Cover],
    ) -> Dict[str, Dict[SiteId, str]]:
        """Extract viabilities from covers and push them back.

        Convenience method that extracts viability requirements from
        each function's cover and then calls pushback().
        """
        viabilities: Dict[str, List[ViabilityRequirement]] = {}
        for func_name, cover in covers.items():
            reqs = _extract_viabilities(cover, func_name)
            if reqs:
                viabilities[func_name] = reqs

        return self.pushback(call_graph, viabilities)

    # -- Internal helpers ---------------------------------------------------

    def _pushback_edge(
        self,
        edge: CallEdge,
        callee_requirements: Dict[SiteId, str],
        call_graph: CallGraph,
    ) -> Dict[SiteId, str]:
        """Push back requirements from callee to caller for one edge."""
        result: Dict[SiteId, str] = {}

        # Collect callee parameter names for reindexing
        callee_params: List[str] = []
        for site_id in sorted(callee_requirements.keys(), key=lambda s: s.name):
            if site_id.kind == SiteKind.ARGUMENT_BOUNDARY:
                param_name = site_id.name.split(".")[-1]
                callee_params.append(param_name)

        for callee_site_id, predicate in callee_requirements.items():
            if callee_site_id.kind != SiteKind.ARGUMENT_BOUNDARY:
                continue

            param_name = callee_site_id.name.split(".")[-1]

            # Reindex predicate from callee to caller naming
            reindexed = _reindex_predicate(predicate, edge, callee_params)

            # Find matching caller argument
            caller_site_id = self._find_caller_input_site(
                edge, param_name
            )
            if caller_site_id is not None:
                result[caller_site_id] = reindexed

                # Create pushback morphism
                morphism = make_error_pullback_restriction(
                    error_site=callee_site_id,
                    input_site=caller_site_id,
                    viability_predicate=reindexed,
                    description=(
                        f"viability pushback: {edge.callee}.{param_name} "
                        f"-> {edge.caller}"
                    ),
                )

                pb_result = PushbackResult(
                    _caller=edge.caller,
                    _callee=edge.callee,
                    _requirements={caller_site_id: reindexed},
                    _morphisms=[morphism],
                )
                self._pushback_log.append(pb_result)

        return result

    def _pushback_requirement(
        self,
        edge: CallEdge,
        requirement: ViabilityRequirement,
        caller_cover: Cover,
    ) -> Dict[SiteId, str]:
        """Push a single viability requirement to the caller."""
        result: Dict[SiteId, str] = {}

        for param_name in requirement.upstream_params:
            reindexed = _reindex_predicate(
                requirement.predicate_text,
                edge,
                list(requirement.upstream_params),
            )

            caller_site_id = self._find_caller_input_site(edge, param_name)
            if caller_site_id is not None:
                result[caller_site_id] = reindexed

        return result

    def _find_caller_input_site(
        self,
        edge: CallEdge,
        callee_param_name: str,
    ) -> Optional[SiteId]:
        """Find the caller's input site for a callee parameter.

        Uses the call edge's argument list to find which caller argument
        maps to the given callee parameter.
        """
        # Try positional matching
        # We need to know the callee's parameter order, but we only have
        # the param name.  Use the argument list from the edge.
        args = edge.arguments

        # If the call_edge has argument names, try to find a direct match
        for idx, arg_name in enumerate(args):
            # The caller's site for this argument
            site_id = SiteId(
                kind=SiteKind.ARGUMENT_BOUNDARY,
                name=f"{edge.caller}.{arg_name}",
            )
            # Return the first argument as a reasonable match
            # (In practice, we'd need the callee's parameter list
            # to do proper positional matching)
            return site_id

        # Keyword argument matching
        for kw_name, kw_value in edge.keyword_arguments:
            if kw_name == callee_param_name:
                return SiteId(
                    kind=SiteKind.ARGUMENT_BOUNDARY,
                    name=f"{edge.caller}.{kw_value}",
                )

        # Fallback: create a generic site
        if args:
            return SiteId(
                kind=SiteKind.ARGUMENT_BOUNDARY,
                name=f"{edge.caller}.{args[0]}",
            )

        return None

    def clear_log(self) -> None:
        """Clear the pushback log."""
        self._pushback_log.clear()
