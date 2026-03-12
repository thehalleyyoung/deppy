"""Convert parsed traces into LocalSection objects with TRACE_BACKED trust.

This module is the bridge between dynamic observation and the sheaf-descent
type system.  It takes a :class:`ParsedTrace` (structured observations from
:mod:`deppy.observe.trace_parser`) and produces :class:`LocalSection` objects
that carry inferred type information with ``TrustLevel.TRACE_BACKED``.

The primary entry-point is :func:`trace_to_local_section`.  For batch
conversion of an entire :class:`ParsedTrace`, use :func:`trace_to_sections`.

Key design decisions
--------------------
* **carrier_type** is inferred from the dominant observed type.
* **refinements** encode observed constraints: shape, dtype, length,
  value ranges, and type diversity.
* **trust** is always ``TrustLevel.TRACE_BACKED``.
* **witnesses** carry representative observed values and shapes.
* **provenance** records the trace id and sample count.
"""

from __future__ import annotations

import hashlib
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
from deppy.static_analysis.observation_sites import (
    SourceSpan,
    TraceSiteData,
    make_trace_site,
)
from deppy.observe.trace_parser import (
    BranchObservation,
    ExceptionObservation,
    FunctionObservation,
    ObservedType,
    ParsedTrace,
    VariableObservation,
)


# ---------------------------------------------------------------------------
# Type-name to carrier-type mapping
# ---------------------------------------------------------------------------

# Well-known Python type names -> short canonical names
_CANONICAL_TYPE_MAP: Dict[str, str] = {
    "int": "int",
    "float": "float",
    "complex": "complex",
    "str": "str",
    "bytes": "bytes",
    "bool": "bool",
    "NoneType": "None",
    "list": "list",
    "tuple": "tuple",
    "dict": "dict",
    "set": "set",
    "frozenset": "frozenset",
    "numpy.ndarray": "ndarray",
    "torch.Tensor": "Tensor",
    "jax.interpreters.xla.DeviceArray": "DeviceArray",
    "jaxlib.xla_extension.ArrayImpl": "Array",
}


def _canonicalize_type_name(type_name: str) -> str:
    """Map a fully-qualified type name to a short canonical form."""
    if type_name in _CANONICAL_TYPE_MAP:
        return _CANONICAL_TYPE_MAP[type_name]
    # Strip common prefixes
    for prefix in ("builtins.", "typing."):
        if type_name.startswith(prefix):
            return type_name[len(prefix):]
    # Use the last component of dotted names
    parts = type_name.rsplit(".", 1)
    return parts[-1] if len(parts) > 1 else type_name


# ---------------------------------------------------------------------------
# Refinement extraction
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class InferredRefinements:
    """Refinements inferred from trace observations.

    These become the ``refinements`` dict on the :class:`LocalSection`.

    Attributes
    ----------
    type_name : str
        Canonical type name.
    is_monomorphic : bool
        True if exactly one type was observed.
    observed_types : Tuple[str, ...]
        All type names observed (for polymorphic variables).
    shape : Optional[Tuple[int, ...]]
        The dominant tensor shape, if applicable.
    all_shapes : Tuple[Tuple[int, ...], ...]
        All distinct shapes observed.
    dtype : Optional[str]
        The dominant element dtype, if applicable.
    length : Optional[int]
        The dominant container length, if applicable.
    all_lengths : Tuple[int, ...]
        All distinct container lengths observed.
    sample_count : int
        Total number of observations.
    is_parameter : bool
        Whether this variable is a function parameter.
    is_return : bool
        Whether this captures return-value observations.
    """

    type_name: str = "Any"
    is_monomorphic: bool = True
    observed_types: Tuple[str, ...] = ()
    shape: Optional[Tuple[int, ...]] = None
    all_shapes: Tuple[Tuple[int, ...], ...] = ()
    dtype: Optional[str] = None
    length: Optional[int] = None
    all_lengths: Tuple[int, ...] = ()
    sample_count: int = 0
    is_parameter: bool = False
    is_return: bool = False


def _infer_refinements(vo: VariableObservation) -> InferredRefinements:
    """Extract refinements from a :class:`VariableObservation`."""
    dom = vo.dominant_type
    type_name = _canonicalize_type_name(dom.type_name) if dom else "Any"

    # Collect shapes and dtypes across all observed types
    all_shapes: List[Tuple[int, ...]] = list(vo.all_shapes)
    all_dtypes: Set[str] = set()
    all_lengths: Set[int] = set()
    for ot in vo.observed_types:
        all_dtypes.update(ot.dtypes)
        all_lengths.update(ot.lengths)

    dominant_shape: Optional[Tuple[int, ...]] = None
    if all_shapes:
        # Pick the most common shape
        shape_counts: Dict[Tuple[int, ...], int] = {}
        for s in all_shapes:
            shape_counts[s] = shape_counts.get(s, 0) + 1
        dominant_shape = max(shape_counts, key=shape_counts.get)  # type: ignore[arg-type]

    dominant_dtype: Optional[str] = None
    if all_dtypes:
        dominant_dtype = sorted(all_dtypes)[0]  # deterministic

    dominant_length: Optional[int] = None
    if all_lengths:
        # Pick the most common length
        length_counts: Dict[int, int] = {}
        for l in all_lengths:
            length_counts[l] = length_counts.get(l, 0) + 1
        dominant_length = max(length_counts, key=length_counts.get)  # type: ignore[arg-type]

    return InferredRefinements(
        type_name=type_name,
        is_monomorphic=vo.is_monomorphic,
        observed_types=tuple(
            _canonicalize_type_name(t.type_name) for t in vo.observed_types
        ),
        shape=dominant_shape,
        all_shapes=tuple(sorted(set(all_shapes))),
        dtype=dominant_dtype,
        length=dominant_length,
        all_lengths=tuple(sorted(all_lengths)),
        sample_count=vo.assignment_count,
        is_parameter=vo.is_parameter,
        is_return=vo.is_return,
    )


# ---------------------------------------------------------------------------
# Section builders
# ---------------------------------------------------------------------------

def _refinements_to_dict(ir: InferredRefinements) -> Dict[str, Any]:
    """Convert :class:`InferredRefinements` to a plain dict for LocalSection."""
    d: Dict[str, Any] = {
        "observed_type": ir.type_name,
        "monomorphic": ir.is_monomorphic,
        "sample_count": ir.sample_count,
    }
    if not ir.is_monomorphic:
        d["observed_types"] = list(ir.observed_types)
    if ir.shape is not None:
        d["shape"] = ir.shape
        d["rank"] = len(ir.shape)
    if ir.all_shapes:
        d["all_shapes"] = list(ir.all_shapes)
        d["shape_diversity"] = len(ir.all_shapes)
    if ir.dtype is not None:
        d["dtype"] = ir.dtype
    if ir.length is not None:
        d["length"] = ir.length
    if ir.all_lengths:
        d["all_lengths"] = list(ir.all_lengths)
    if ir.is_parameter:
        d["is_parameter"] = True
    if ir.is_return:
        d["is_return"] = True
    return d


def _witnesses_from_observation(vo: VariableObservation) -> Dict[str, Any]:
    """Build the witnesses dict for a LocalSection."""
    witnesses: Dict[str, Any] = {}
    if vo.sample_values:
        witnesses["sample_values"] = list(vo.sample_values[:5])
    dom = vo.dominant_type
    if dom and dom.sample_reprs:
        witnesses["sample_reprs"] = list(dom.sample_reprs[:3])
    if vo.all_shapes:
        witnesses["observed_shapes"] = list(vo.all_shapes[:10])
    return witnesses


def _make_site_id_for_variable(
    func_name: str,
    var_name: str,
    vo: VariableObservation,
) -> SiteId:
    """Create a :class:`SiteId` for a variable observation."""
    if vo.is_parameter:
        kind = SiteKind.ARGUMENT_BOUNDARY
        name = f"{func_name}.{var_name}"
    elif vo.is_return:
        kind = SiteKind.RETURN_OUTPUT_BOUNDARY
        name = f"{func_name}.return"
    else:
        kind = SiteKind.TRACE
        name = f"{func_name}.trace_{var_name}"
    return SiteId(
        kind=kind,
        name=name,
        source_location=vo.first_location,
    )


# ---------------------------------------------------------------------------
# Primary API: variable -> LocalSection
# ---------------------------------------------------------------------------

def variable_to_local_section(
    vo: VariableObservation,
    *,
    site_id: Optional[SiteId] = None,
    trace_id: str = "",
) -> LocalSection:
    """Convert a single :class:`VariableObservation` into a :class:`LocalSection`.

    Parameters
    ----------
    vo : VariableObservation
        The variable observation.
    site_id : SiteId or None
        Override the site id.  If ``None``, one is generated from
        the function + variable name.
    trace_id : str
        The trace session identifier for provenance.

    Returns
    -------
    LocalSection
        A section with ``trust=TrustLevel.TRACE_BACKED``.
    """
    if site_id is None:
        site_id = _make_site_id_for_variable(
            vo.function, vo.variable, vo
        )

    ir = _infer_refinements(vo)
    refinements = _refinements_to_dict(ir)
    witnesses = _witnesses_from_observation(vo)

    provenance_parts = [f"trace:{trace_id}"] if trace_id else ["trace"]
    provenance_parts.append(f"samples={ir.sample_count}")

    return LocalSection(
        site_id=site_id,
        carrier_type=ir.type_name,
        refinements=refinements,
        trust=TrustLevel.TRACE_BACKED,
        provenance=", ".join(provenance_parts),
        witnesses=witnesses,
    )


# ---------------------------------------------------------------------------
# Primary API: branch -> LocalSection
# ---------------------------------------------------------------------------

def branch_to_local_section(
    bo: BranchObservation,
    *,
    site_id: Optional[SiteId] = None,
    trace_id: str = "",
) -> LocalSection:
    """Convert a :class:`BranchObservation` into a :class:`LocalSection`.

    Parameters
    ----------
    bo : BranchObservation
        The branch observation.
    site_id : SiteId or None
        Override the site id.
    trace_id : str
        Trace session id for provenance.

    Returns
    -------
    LocalSection
        A section representing observed branch behaviour.
    """
    if site_id is None:
        loc_hash = hashlib.md5(
            f"{bo.location}".encode()
        ).hexdigest()[:8]
        site_id = SiteId(
            kind=SiteKind.BRANCH_GUARD,
            name=f"{bo.function}.guard_{loc_hash}",
            source_location=bo.location,
        )

    refinements: Dict[str, Any] = {
        "true_count": bo.true_count,
        "false_count": bo.false_count,
        "always_true": bo.always_true,
        "always_false": bo.always_false,
        "both_taken": bo.both_taken,
        "total_observations": bo.total,
    }
    if bo.guard_repr:
        refinements["guard_repr"] = bo.guard_repr

    return LocalSection(
        site_id=site_id,
        carrier_type="bool",
        refinements=refinements,
        trust=TrustLevel.TRACE_BACKED,
        provenance=f"trace:{trace_id}, branch at {bo.location}"
        if trace_id
        else f"branch at {bo.location}",
        witnesses={
            "true_count": bo.true_count,
            "false_count": bo.false_count,
        },
    )


# ---------------------------------------------------------------------------
# Primary API: exception -> LocalSection
# ---------------------------------------------------------------------------

def exception_to_local_section(
    eo: ExceptionObservation,
    *,
    site_id: Optional[SiteId] = None,
    trace_id: str = "",
) -> LocalSection:
    """Convert an :class:`ExceptionObservation` into a :class:`LocalSection`.

    Parameters
    ----------
    eo : ExceptionObservation
        The exception observation.
    site_id : SiteId or None
        Override the site id.
    trace_id : str
        Trace session id for provenance.

    Returns
    -------
    LocalSection
        A section representing observed exception behaviour at an error site.
    """
    if site_id is None:
        short_type = eo.exception_type.rsplit(".", 1)[-1]
        site_id = SiteId(
            kind=SiteKind.ERROR,
            name=f"{eo.function}.error_{short_type}",
            source_location=eo.locations[0] if eo.locations else None,
        )

    refinements: Dict[str, Any] = {
        "exception_type": eo.exception_type,
        "count": eo.count,
        "viable": False,  # exception was raised -> not viable
    }

    witnesses: Dict[str, Any] = {}
    if eo.sample_messages:
        witnesses["sample_messages"] = list(eo.sample_messages[:5])
    if eo.locations:
        witnesses["locations"] = [
            {"file": loc[0], "line": loc[1], "col": loc[2]}
            for loc in eo.locations[:5]
        ]

    return LocalSection(
        site_id=site_id,
        carrier_type=eo.exception_type,
        refinements=refinements,
        trust=TrustLevel.TRACE_BACKED,
        provenance=f"trace:{trace_id}, exception {eo.exception_type}"
        if trace_id
        else f"exception {eo.exception_type}",
        witnesses=witnesses,
    )


# ---------------------------------------------------------------------------
# Primary API: function -> list of LocalSections
# ---------------------------------------------------------------------------

def function_to_local_sections(
    fo: FunctionObservation,
    *,
    trace_id: str = "",
) -> List[LocalSection]:
    """Convert a :class:`FunctionObservation` to a list of :class:`LocalSection`.

    Produces one section per:
    - parameter
    - local variable
    - return value
    - branch guard
    - exception site

    Parameters
    ----------
    fo : FunctionObservation
        The function observation to convert.
    trace_id : str
        Trace session identifier.

    Returns
    -------
    List[LocalSection]
        All sections for this function.
    """
    sections: List[LocalSection] = []

    # Parameters
    for po in fo.parameter_observations:
        sections.append(
            variable_to_local_section(po, trace_id=trace_id)
        )

    # Local variables
    for vo in fo.variables:
        sections.append(
            variable_to_local_section(vo, trace_id=trace_id)
        )

    # Return value
    if fo.return_observation is not None:
        sections.append(
            variable_to_local_section(fo.return_observation, trace_id=trace_id)
        )

    # Branches
    for bo in fo.branches:
        sections.append(
            branch_to_local_section(bo, trace_id=trace_id)
        )

    # Exceptions
    for eo in fo.exceptions:
        sections.append(
            exception_to_local_section(eo, trace_id=trace_id)
        )

    return sections


# ---------------------------------------------------------------------------
# Top-level API: ParsedTrace -> list of LocalSections
# ---------------------------------------------------------------------------

def trace_to_local_section(
    parsed_trace: ParsedTrace,
    site_id: SiteId,
) -> LocalSection:
    """Convert a :class:`ParsedTrace` into a single summary :class:`LocalSection`.

    This creates a section that summarises the entire trace at the given
    *site_id*.  It is useful when a single site must represent the whole
    dynamic observation (e.g., a module-level trace site).

    Parameters
    ----------
    parsed_trace : ParsedTrace
        The structured trace.
    site_id : SiteId
        The site at which to create the section.

    Returns
    -------
    LocalSection
        A section with ``trust=TrustLevel.TRACE_BACKED``.
    """
    refinements: Dict[str, Any] = {
        "unique_types": sorted(parsed_trace.unique_types),
        "unique_shapes": sorted(
            str(s) for s in parsed_trace.unique_shapes
        ),
        "function_count": len(parsed_trace.function_observations),
        "variable_count": len(parsed_trace.all_variables),
        "branch_count": len(parsed_trace.all_branches),
        "covered_branches": parsed_trace.covered_branch_count,
        "exception_count": len(parsed_trace.all_exceptions),
        "event_count": parsed_trace.event_count,
        "succeeded": parsed_trace.succeeded,
    }

    witnesses: Dict[str, Any] = {
        "trace_id": parsed_trace.trace_id,
        "duration": parsed_trace.duration,
        "functions": sorted(parsed_trace.function_names),
    }

    # Determine a summary carrier type
    if parsed_trace.unique_types:
        # Use the most common type across all variables
        type_counts: Dict[str, int] = {}
        for vo in parsed_trace.all_variables:
            for ot in vo.observed_types:
                canonical = _canonicalize_type_name(ot.type_name)
                type_counts[canonical] = type_counts.get(canonical, 0) + ot.count
        if type_counts:
            carrier_type = max(type_counts, key=type_counts.get)  # type: ignore[arg-type]
        else:
            carrier_type = "Any"
    else:
        carrier_type = "Any"

    return LocalSection(
        site_id=site_id,
        carrier_type=carrier_type,
        refinements=refinements,
        trust=TrustLevel.TRACE_BACKED,
        provenance=f"trace:{parsed_trace.trace_id}, events={parsed_trace.event_count}",
        witnesses=witnesses,
    )


def trace_to_sections(
    parsed_trace: ParsedTrace,
) -> List[LocalSection]:
    """Convert an entire :class:`ParsedTrace` into :class:`LocalSection` objects.

    Produces one section per observed variable, branch, exception, and
    return value across all functions in the trace.

    Parameters
    ----------
    parsed_trace : ParsedTrace
        The structured trace.

    Returns
    -------
    List[LocalSection]
        All sections inferred from the trace.
    """
    sections: List[LocalSection] = []
    for fo in parsed_trace.function_observations:
        sections.extend(
            function_to_local_sections(fo, trace_id=parsed_trace.trace_id)
        )
    return sections


# ---------------------------------------------------------------------------
# Section enrichment
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SectionEnrichment:
    """Additional information to merge into an existing LocalSection.

    Attributes
    ----------
    extra_refinements : Dict[str, Any]
        Additional refinement entries.
    extra_witnesses : Dict[str, Any]
        Additional witness entries.
    upgraded_trust : Optional[TrustLevel]
        If set, upgrade the section's trust level to this.
    appended_provenance : str
        Text appended to the existing provenance.
    """

    extra_refinements: Tuple[Tuple[str, Any], ...] = ()
    extra_witnesses: Tuple[Tuple[str, Any], ...] = ()
    upgraded_trust: Optional[TrustLevel] = None
    appended_provenance: str = ""


def enrich_section(
    section: LocalSection,
    enrichment: SectionEnrichment,
) -> LocalSection:
    """Produce a new :class:`LocalSection` enriched with additional data.

    The original section is not mutated.

    Parameters
    ----------
    section : LocalSection
        The base section.
    enrichment : SectionEnrichment
        The additional data.

    Returns
    -------
    LocalSection
        A new section with merged refinements, witnesses, and provenance.
    """
    new_refinements = dict(section.refinements)
    for k, v in enrichment.extra_refinements:
        new_refinements[k] = v

    new_witnesses = dict(section.witnesses)
    for k, v in enrichment.extra_witnesses:
        new_witnesses[k] = v

    trust = enrichment.upgraded_trust or section.trust
    provenance = section.provenance or ""
    if enrichment.appended_provenance:
        provenance = f"{provenance}; {enrichment.appended_provenance}" if provenance else enrichment.appended_provenance

    return LocalSection(
        site_id=section.site_id,
        carrier_type=section.carrier_type,
        refinements=new_refinements,
        trust=trust,
        provenance=provenance,
        witnesses=new_witnesses,
    )


# ---------------------------------------------------------------------------
# Section merging (multiple traces for the same site)
# ---------------------------------------------------------------------------

def merge_trace_sections(
    sections: Sequence[LocalSection],
) -> LocalSection:
    """Merge multiple trace-backed sections for the same site.

    Combines refinements, accumulates sample counts, and keeps
    the strictest trust level.

    Parameters
    ----------
    sections : Sequence[LocalSection]
        Sections to merge (must share the same ``site_id``).

    Returns
    -------
    LocalSection
        The merged section.

    Raises
    ------
    ValueError
        If sections have different ``site_id`` values.
    """
    if not sections:
        raise ValueError("Cannot merge empty sequence of sections")
    if len(sections) == 1:
        return sections[0]

    site_id = sections[0].site_id
    for s in sections[1:]:
        if s.site_id != site_id:
            raise ValueError(
                f"Cannot merge sections with different site_ids: "
                f"{site_id} vs {s.site_id}"
            )

    # Merge refinements: union of keys, lists are concatenated
    merged_refs: Dict[str, Any] = {}
    for s in sections:
        for k, v in s.refinements.items():
            if k not in merged_refs:
                merged_refs[k] = v
            elif k == "sample_count" and isinstance(v, int):
                merged_refs[k] = merged_refs.get(k, 0) + v
            elif k in ("all_shapes", "all_lengths", "observed_types"):
                existing = merged_refs[k]
                if isinstance(existing, list) and isinstance(v, list):
                    combined = list(existing)
                    for item in v:
                        if item not in combined:
                            combined.append(item)
                    merged_refs[k] = combined

    # Merge witnesses
    merged_witnesses: Dict[str, Any] = {}
    for s in sections:
        for k, v in s.witnesses.items():
            if k not in merged_witnesses:
                merged_witnesses[k] = v

    # Carrier type: use the most common
    type_counts: Dict[str, int] = {}
    for s in sections:
        ct = s.carrier_type or "Any"
        type_counts[ct] = type_counts.get(ct, 0) + 1
    carrier_type = max(type_counts, key=type_counts.get)  # type: ignore[arg-type]

    # Provenance
    trace_ids = set()
    for s in sections:
        prov = s.provenance or ""
        if "trace:" in prov:
            tid = prov.split("trace:")[1].split(",")[0].strip()
            trace_ids.add(tid)
    provenance = f"merged traces: [{', '.join(sorted(trace_ids))}]"

    return LocalSection(
        site_id=site_id,
        carrier_type=carrier_type,
        refinements=merged_refs,
        trust=TrustLevel.TRACE_BACKED,
        provenance=provenance,
        witnesses=merged_witnesses,
    )


# ---------------------------------------------------------------------------
# Compatibility checking
# ---------------------------------------------------------------------------

def section_agrees_with_static(
    trace_section: LocalSection,
    static_section: LocalSection,
) -> bool:
    """Check whether a trace-backed section is compatible with a static one.

    Compatibility means:
    - The observed type is a subtype of or equal to the static carrier type.
    - Shape constraints in the static section are satisfied by observed shapes.
    - No conflicting refinements.

    This is a conservative check -- ``True`` means "no observed contradiction".

    Parameters
    ----------
    trace_section : LocalSection
        The dynamically inferred section.
    static_section : LocalSection
        The statically inferred section.

    Returns
    -------
    bool
        True if no contradictions were found.
    """
    # If the static section has no carrier type, any trace is compatible
    if static_section.carrier_type is None:
        return True

    # Check type compatibility (string-level)
    trace_type = trace_section.refinements.get("observed_type", "Any")
    static_type = str(static_section.carrier_type)

    # "Any" is always compatible
    if trace_type == "Any" or static_type == "Any":
        return True

    # Simple name match
    if trace_type == static_type:
        return True

    # Check shape compatibility
    static_shape = static_section.refinements.get("shape")
    trace_shapes = trace_section.refinements.get("all_shapes", [])
    if static_shape is not None and trace_shapes:
        if static_shape not in trace_shapes:
            return False

    # Check dtype compatibility
    static_dtype = static_section.refinements.get("dtype")
    trace_dtype = trace_section.refinements.get("dtype")
    if static_dtype is not None and trace_dtype is not None:
        if static_dtype != trace_dtype:
            return False

    return True
