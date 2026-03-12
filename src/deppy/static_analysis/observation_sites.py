"""Observation site constructors for the site category S.

Every program fragment that can carry local semantic information becomes an
observation site.  This module provides constructors for all 14 site families
defined in the site-family catalogue (§ Site-family catalogue of the monograph).

The output of these constructors is always a ``ConcreteSite`` from
``deppy.core.site`` together with a ``CarrierSchema`` from ``deppy.types.carriers``
that declares what local payload the site expects.  No classical CFG or SSA
infrastructure is introduced; the only structural notion is the observation
site category itself.
"""

from __future__ import annotations

import ast
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
    Union,
)

from deppy.core._protocols import (
    BoundarySection,
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite, SiteCategory
from deppy.types.carriers import CarrierSchema, CarrierType, SchemaConstraint


# ---------------------------------------------------------------------------
# Source location helper
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SourceSpan:
    """A span in the original Python source."""
    file: str
    start_line: int
    start_col: int
    end_line: int = -1
    end_col: int = -1

    @classmethod
    def from_ast(cls, node: ast.AST, file: str = "<unknown>") -> SourceSpan:
        end_line = getattr(node, "end_lineno", -1) or -1
        end_col = getattr(node, "end_col_offset", -1) or -1
        return cls(
            file=file,
            start_line=getattr(node, "lineno", 0),
            start_col=getattr(node, "col_offset", 0),
            end_line=end_line,
            end_col=end_col,
        )

    def as_tuple(self) -> Tuple[str, int, int]:
        return (self.file, self.start_line, self.start_col)


# ---------------------------------------------------------------------------
# Site payload: what a local section at this site should carry
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SitePayloadSpec:
    """Declares the shape of local semantic data expected at a site.

    This is the sheaf-theoretic analogue of a "carrier schema": it says which
    coordinates a local section must provide so that restriction maps can
    project them to neighbouring sites.
    """
    carrier_schema: CarrierSchema
    required_refinement_keys: FrozenSet[str] = frozenset()
    optional_refinement_keys: FrozenSet[str] = frozenset()
    supports_witnesses: bool = False
    supports_viability: bool = False


# ---------------------------------------------------------------------------
# Argument-boundary sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ArgumentBoundarySiteData:
    """Payload for an argument-boundary site.

    Represents formal parameters, receiver objects, ambient module state,
    and optional ghost inputs.
    """
    param_name: str
    param_index: int
    annotation: Optional[Any] = None  # Python type annotation AST node
    default_value: Optional[ast.expr] = None
    is_self: bool = False
    is_ghost: bool = False
    harvested_guards: Tuple[Any, ...] = ()
    protocol_assumptions: Tuple[str, ...] = ()


def make_argument_boundary_site(
    func_name: str,
    param_name: str,
    param_index: int,
    span: SourceSpan,
    *,
    annotation: Optional[Any] = None,
    default_value: Optional[ast.expr] = None,
    is_self: bool = False,
    is_ghost: bool = False,
) -> ConcreteSite:
    """Create an argument-boundary observation site for a formal parameter."""
    site_id = SiteId(
        kind=SiteKind.ARGUMENT_BOUNDARY,
        name=f"{func_name}.{param_name}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"arg:{param_name}",
        constraints=[
            SchemaConstraint(
                field_names=("carrier_type",),
                description=f"base type of parameter {param_name}",
            ),
        ],
    )
    data = ArgumentBoundarySiteData(
        param_name=param_name,
        param_index=param_index,
        annotation=annotation,
        default_value=default_value,
        is_self=is_self,
        is_ghost=is_ghost,
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# Return / output-boundary sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ReturnBoundarySiteData:
    """Payload for a return / output-boundary site."""
    return_index: int = 0
    is_exceptional: bool = False
    exception_type: Optional[str] = None
    is_mutation: bool = False
    mutated_name: Optional[str] = None
    is_witness_export: bool = False


def make_return_boundary_site(
    func_name: str,
    span: SourceSpan,
    *,
    return_index: int = 0,
    is_exceptional: bool = False,
    exception_type: Optional[str] = None,
    is_mutation: bool = False,
    mutated_name: Optional[str] = None,
    is_witness_export: bool = False,
) -> ConcreteSite:
    """Create a return / output-boundary observation site."""
    suffix = f".return_{return_index}"
    if is_exceptional:
        suffix = f".exc_{exception_type or 'Unknown'}"
    elif is_mutation:
        suffix = f".mutate_{mutated_name or 'heap'}"
    elif is_witness_export:
        suffix = f".witness_{return_index}"

    site_id = SiteId(
        kind=SiteKind.RETURN_OUTPUT_BOUNDARY,
        name=f"{func_name}{suffix}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"output:{func_name}{suffix}",
        constraints=[
            SchemaConstraint(
                field_names=("carrier_type",),
                description="base type of return value",
            ),
        ],
    )
    data = ReturnBoundarySiteData(
        return_index=return_index,
        is_exceptional=is_exceptional,
        exception_type=exception_type,
        is_mutation=is_mutation,
        mutated_name=mutated_name,
        is_witness_export=is_witness_export,
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# SSA-value sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SSAValueSiteData:
    """Payload for an SSA-value site.

    Represents a versioned local, tuple projection, alias chain,
    or phi-merge point.  In the sheaf view a phi-node is an overlap
    site where predecessor sections must agree or expose an obstruction.
    """
    variable_name: str
    version: int = 0
    is_phi: bool = False
    predecessor_versions: Tuple[Tuple[str, int], ...] = ()
    lineage_parent: Optional[str] = None
    defining_ast_node_type: Optional[str] = None


def make_ssa_value_site(
    func_name: str,
    variable_name: str,
    version: int,
    span: SourceSpan,
    *,
    is_phi: bool = False,
    predecessor_versions: Sequence[Tuple[str, int]] = (),
    lineage_parent: Optional[str] = None,
    defining_ast_node_type: Optional[str] = None,
) -> ConcreteSite:
    """Create an SSA-value observation site for a versioned local."""
    site_id = SiteId(
        kind=SiteKind.SSA_VALUE,
        name=f"{func_name}.{variable_name}_{version}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"ssa:{variable_name}_{version}",
        constraints=[
            SchemaConstraint(
                field_names=("carrier_type",),
                description=f"type of {variable_name} at version {version}",
            ),
        ],
    )
    data = SSAValueSiteData(
        variable_name=variable_name,
        version=version,
        is_phi=is_phi,
        predecessor_versions=tuple(predecessor_versions),
        lineage_parent=lineage_parent,
        defining_ast_node_type=defining_ast_node_type,
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# Branch-guard sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class BranchGuardSiteData:
    """Payload for a branch-guard site.

    Represents control-dependent refinements: if-statements, assertions,
    match-like structures.  The guard predicate narrows types in the
    true / false arms.
    """
    guard_expression: Optional[str] = None  # Pretty-printed guard
    polarity: bool = True  # True = true-branch, False = false-branch
    is_assertion: bool = False
    is_match: bool = False
    narrowed_variables: Tuple[str, ...] = ()


def make_branch_guard_site(
    func_name: str,
    guard_label: str,
    span: SourceSpan,
    *,
    guard_expression: Optional[str] = None,
    polarity: bool = True,
    is_assertion: bool = False,
    is_match: bool = False,
    narrowed_variables: Sequence[str] = (),
) -> ConcreteSite:
    """Create a branch-guard observation site."""
    pol = "T" if polarity else "F"
    site_id = SiteId(
        kind=SiteKind.BRANCH_GUARD,
        name=f"{func_name}.guard_{guard_label}_{pol}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"guard:{guard_label}",
        constraints=[
            SchemaConstraint(
                field_names=("predicate",),
                description="guard predicate for narrowing",
            ),
        ],
    )
    data = BranchGuardSiteData(
        guard_expression=guard_expression,
        polarity=polarity,
        is_assertion=is_assertion,
        is_match=is_match,
        narrowed_variables=tuple(narrowed_variables),
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# Call-result sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CallResultSiteData:
    """Payload for a call-result site.

    Represents the semantic neighbourhood created at a function/method call.
    The callee's boundary sections are imported here via actual-to-formal
    reindexing.
    """
    callee_name: str
    arguments: Tuple[str, ...] = ()
    is_method_call: bool = False
    receiver_variable: Optional[str] = None
    has_callee_summary: bool = False


def make_call_result_site(
    func_name: str,
    call_label: str,
    callee_name: str,
    span: SourceSpan,
    *,
    arguments: Sequence[str] = (),
    is_method_call: bool = False,
    receiver_variable: Optional[str] = None,
) -> ConcreteSite:
    """Create a call-result observation site."""
    site_id = SiteId(
        kind=SiteKind.CALL_RESULT,
        name=f"{func_name}.call_{call_label}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"call:{callee_name}",
        constraints=[
            SchemaConstraint(
                field_names=("carrier_type",),
                description="return type from callee",
            ),
        ],
    )
    data = CallResultSiteData(
        callee_name=callee_name,
        arguments=tuple(arguments),
        is_method_call=is_method_call,
        receiver_variable=receiver_variable,
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# Tensor-shape sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TensorShapeSiteData:
    """Payload for a tensor-shape site.

    Covers rank, shape tuple, broadcasting, reshape/view legality,
    and reduction preconditions.
    """
    operation: str  # e.g. "reshape", "view", "broadcast", "matmul"
    source_variable: Optional[str] = None
    target_shape: Optional[Tuple[Any, ...]] = None
    requires_contiguity: bool = False
    is_reduction: bool = False
    reduced_dim: Optional[int] = None


def make_tensor_shape_site(
    func_name: str,
    shape_label: str,
    operation: str,
    span: SourceSpan,
    *,
    source_variable: Optional[str] = None,
    target_shape: Optional[Tuple[Any, ...]] = None,
    requires_contiguity: bool = False,
    is_reduction: bool = False,
    reduced_dim: Optional[int] = None,
) -> ConcreteSite:
    """Create a tensor-shape observation site."""
    site_id = SiteId(
        kind=SiteKind.TENSOR_SHAPE,
        name=f"{func_name}.shape_{shape_label}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"shape:{operation}",
        constraints=[
            SchemaConstraint(field_names=("rank",), description="tensor rank"),
            SchemaConstraint(field_names=("shape_tuple",), description="dimension extents"),
            SchemaConstraint(field_names=("cardinality",), description="total element count"),
        ],
    )
    data = TensorShapeSiteData(
        operation=operation,
        source_variable=source_variable,
        target_shape=target_shape,
        requires_contiguity=requires_contiguity,
        is_reduction=is_reduction,
        reduced_dim=reduced_dim,
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# Tensor-order sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TensorOrderSiteData:
    """Payload for a tensor-order site.

    Covers sortedness, argsort, permutation, monotone slices,
    and value-index coupling.
    """
    operation: str  # e.g. "sort", "argsort", "topk"
    source_variable: Optional[str] = None
    produces_values: bool = True
    produces_indices: bool = True
    descending: bool = False
    dim: Optional[int] = None


def make_tensor_order_site(
    func_name: str,
    order_label: str,
    operation: str,
    span: SourceSpan,
    *,
    source_variable: Optional[str] = None,
    produces_values: bool = True,
    produces_indices: bool = True,
    descending: bool = False,
    dim: Optional[int] = None,
) -> ConcreteSite:
    """Create a tensor-order observation site."""
    site_id = SiteId(
        kind=SiteKind.TENSOR_ORDER,
        name=f"{func_name}.order_{order_label}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"order:{operation}",
        constraints=[
            SchemaConstraint(field_names=("sorted",), description="sortedness predicate"),
            SchemaConstraint(field_names=("permutation",), description="permutation witness"),
        ],
    )
    data = TensorOrderSiteData(
        operation=operation,
        source_variable=source_variable,
        produces_values=produces_values,
        produces_indices=produces_indices,
        descending=descending,
        dim=dim,
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# Tensor-indexing sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TensorIndexingSiteData:
    """Payload for a tensor-indexing site.

    Covers selectors, slices, gather/index-select domains,
    and source-target value relations.
    """
    operation: str  # e.g. "subscript", "gather", "index_select", "slice"
    source_variable: Optional[str] = None
    index_variable: Optional[str] = None
    dim: Optional[int] = None
    is_advanced_indexing: bool = False


def make_tensor_indexing_site(
    func_name: str,
    index_label: str,
    operation: str,
    span: SourceSpan,
    *,
    source_variable: Optional[str] = None,
    index_variable: Optional[str] = None,
    dim: Optional[int] = None,
    is_advanced_indexing: bool = False,
) -> ConcreteSite:
    """Create a tensor-indexing observation site."""
    site_id = SiteId(
        kind=SiteKind.TENSOR_INDEXING,
        name=f"{func_name}.index_{index_label}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"index:{operation}",
        constraints=[
            SchemaConstraint(field_names=("selector_domain",), description="valid index range"),
            SchemaConstraint(field_names=("source_extent",), description="source dimension size"),
        ],
    )
    data = TensorIndexingSiteData(
        operation=operation,
        source_variable=source_variable,
        index_variable=index_variable,
        dim=dim,
        is_advanced_indexing=is_advanced_indexing,
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# Heap / protocol sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class HeapProtocolSiteData:
    """Payload for a heap/protocol site.

    Covers attribute existence, field initialization, alias frames,
    protocol method availability, and ownership.
    """
    class_name: Optional[str] = None
    field_name: Optional[str] = None
    method_name: Optional[str] = None
    is_constructor: bool = False
    is_read: bool = False
    is_write: bool = False
    protocol_name: Optional[str] = None
    frame_id: Optional[str] = None


def make_heap_protocol_site(
    func_name: str,
    heap_label: str,
    span: SourceSpan,
    *,
    class_name: Optional[str] = None,
    field_name: Optional[str] = None,
    method_name: Optional[str] = None,
    is_constructor: bool = False,
    is_read: bool = False,
    is_write: bool = False,
    protocol_name: Optional[str] = None,
    frame_id: Optional[str] = None,
) -> ConcreteSite:
    """Create a heap/protocol observation site."""
    site_id = SiteId(
        kind=SiteKind.HEAP_PROTOCOL,
        name=f"{func_name}.heap_{heap_label}",
        source_location=span.as_tuple(),
    )
    desc_parts: List[str] = []
    if field_name:
        desc_parts.append(f"field:{field_name}")
    if method_name:
        desc_parts.append(f"method:{method_name}")
    if protocol_name:
        desc_parts.append(f"protocol:{protocol_name}")
    schema = CarrierSchema(
        name=f"heap:{heap_label}",
        constraints=[
            SchemaConstraint(
                field_names=("heap_state",),
                description=" + ".join(desc_parts) or "heap state",
            ),
        ],
    )
    data = HeapProtocolSiteData(
        class_name=class_name,
        field_name=field_name,
        method_name=method_name,
        is_constructor=is_constructor,
        is_read=is_read,
        is_write=is_write,
        protocol_name=protocol_name,
        frame_id=frame_id,
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# Proof sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ProofSiteData:
    """Payload for a proof site.

    Represents theorem declarations, lemma bodies, witness exports,
    decreases obligations, and transport seeds.
    """
    theorem_name: Optional[str] = None
    is_lemma: bool = False
    is_transport: bool = False
    is_decreases: bool = False
    is_witness_export: bool = False
    obligation_text: Optional[str] = None
    transport_source: Optional[str] = None
    transport_target: Optional[str] = None


def make_proof_site(
    func_name: str,
    proof_label: str,
    span: SourceSpan,
    *,
    theorem_name: Optional[str] = None,
    is_lemma: bool = False,
    is_transport: bool = False,
    is_decreases: bool = False,
    is_witness_export: bool = False,
    obligation_text: Optional[str] = None,
    transport_source: Optional[str] = None,
    transport_target: Optional[str] = None,
) -> ConcreteSite:
    """Create a proof observation site."""
    site_id = SiteId(
        kind=SiteKind.PROOF,
        name=f"{func_name}.proof_{proof_label}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"proof:{proof_label}",
        constraints=[
            SchemaConstraint(
                field_names=("obligation",),
                description="proof obligation or witness",
            ),
        ],
    )
    data = ProofSiteData(
        theorem_name=theorem_name,
        is_lemma=is_lemma,
        is_transport=is_transport,
        is_decreases=is_decreases,
        is_witness_export=is_witness_export,
        obligation_text=obligation_text,
        transport_source=transport_source,
        transport_target=transport_target,
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# Trace sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TraceSiteData:
    """Payload for a trace site.

    Represents observed shapes, branch outcomes, assertion passes,
    and sampled value relations from dynamic execution.
    """
    trace_id: str
    observed_type: Optional[str] = None
    observed_shape: Optional[Tuple[int, ...]] = None
    observed_branch: Optional[bool] = None
    observed_value_relation: Optional[str] = None
    sample_count: int = 1


def make_trace_site(
    func_name: str,
    trace_label: str,
    trace_id: str,
    span: SourceSpan,
    *,
    observed_type: Optional[str] = None,
    observed_shape: Optional[Tuple[int, ...]] = None,
    observed_branch: Optional[bool] = None,
    observed_value_relation: Optional[str] = None,
    sample_count: int = 1,
) -> ConcreteSite:
    """Create a trace observation site from dynamic execution data."""
    site_id = SiteId(
        kind=SiteKind.TRACE,
        name=f"{func_name}.trace_{trace_label}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"trace:{trace_label}",
        constraints=[
            SchemaConstraint(
                field_names=("observed",),
                description="dynamically observed facts",
            ),
        ],
    )
    data = TraceSiteData(
        trace_id=trace_id,
        observed_type=observed_type,
        observed_shape=observed_shape,
        observed_branch=observed_branch,
        observed_value_relation=observed_value_relation,
        sample_count=sample_count,
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# Error sites
# ---------------------------------------------------------------------------

class ErrorKind(enum.Enum):
    """Classification of error-sensitive operations."""
    INDEX_ERROR = "IndexError"
    KEY_ERROR = "KeyError"
    ATTRIBUTE_ERROR = "AttributeError"
    TYPE_ERROR = "TypeError"
    VALUE_ERROR = "ValueError"
    ZERO_DIVISION = "ZeroDivisionError"
    ASSERTION_ERROR = "AssertionError"
    RUNTIME_ERROR = "RuntimeError"
    # Torch-specific
    INVALID_RESHAPE = "invalid_reshape"
    BROADCAST_MISMATCH = "broadcast_mismatch"
    OUT_OF_RANGE_INDEX = "out_of_range_index"
    EMPTY_REDUCTION = "empty_reduction"
    DEVICE_MISMATCH = "device_mismatch"
    DTYPE_INCOMPATIBLE = "dtype_incompatible"
    MATRIX_SHAPE_ERROR = "matrix_shape_error"
    SORT_MISUSE = "sort_misuse"
    # Heap-specific
    MISSING_FIELD = "missing_field"
    STALE_ALIAS = "stale_alias"
    FRAME_ESCAPE = "frame_escape"
    CONSTRUCTOR_INVARIANT = "constructor_invariant"
    PROTOCOL_VIOLATION = "protocol_violation"
    # Proof-specific
    MISSING_TRANSPORT = "missing_transport"
    UNVERIFIED_WITNESS = "unverified_witness"
    DECREASES_FAILURE = "decreases_failure"


@dataclass(frozen=True)
class ErrorSiteData:
    """Payload for an error-sensitive site.

    Each error site provides:
    1. Constructor identifying where the site comes from and which operands it sees
    2. Local viability predicate (when is the site safe?)
    3. Explanation generator (render to user)
    4. Pullback rule (viability → constraint on upstream neighbourhoods)
    """
    error_kind: ErrorKind
    operand_names: Tuple[str, ...] = ()
    viability_description: str = ""
    explanation_template: str = ""
    upstream_sites: Tuple[str, ...] = ()


def make_error_site(
    func_name: str,
    error_label: str,
    error_kind: ErrorKind,
    span: SourceSpan,
    *,
    operand_names: Sequence[str] = (),
    viability_description: str = "",
    explanation_template: str = "",
    upstream_sites: Sequence[str] = (),
) -> ConcreteSite:
    """Create an error-sensitive observation site."""
    site_id = SiteId(
        kind=SiteKind.ERROR,
        name=f"{func_name}.error_{error_label}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"error:{error_kind.value}",
        constraints=[
            SchemaConstraint(
                field_names=("viability",),
                description=viability_description or f"viability for {error_kind.value}",
            ),
        ],
    )
    data = ErrorSiteData(
        error_kind=error_kind,
        operand_names=tuple(operand_names),
        viability_description=viability_description,
        explanation_template=explanation_template,
        upstream_sites=tuple(upstream_sites),
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# Loop-header / invariant sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class LoopInvariantSiteData:
    """Payload for a loop-header / invariant site.

    Represents repeated states at loop heads, candidate invariants,
    and ranking data for well-founded recursion.
    """
    loop_variable: Optional[str] = None
    is_for_loop: bool = False
    is_while_loop: bool = False
    candidate_invariant: Optional[str] = None
    decreases_expression: Optional[str] = None
    iteration_bound: Optional[int] = None


def make_loop_invariant_site(
    func_name: str,
    loop_label: str,
    span: SourceSpan,
    *,
    loop_variable: Optional[str] = None,
    is_for_loop: bool = False,
    is_while_loop: bool = False,
    candidate_invariant: Optional[str] = None,
    decreases_expression: Optional[str] = None,
    iteration_bound: Optional[int] = None,
) -> ConcreteSite:
    """Create a loop-header / invariant observation site."""
    site_id = SiteId(
        kind=SiteKind.LOOP_HEADER_INVARIANT,
        name=f"{func_name}.loop_{loop_label}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"loop:{loop_label}",
        constraints=[
            SchemaConstraint(
                field_names=("invariant",),
                description="candidate loop invariant",
            ),
            SchemaConstraint(
                field_names=("decreases",),
                description="ranking function for termination",
            ),
        ],
    )
    data = LoopInvariantSiteData(
        loop_variable=loop_variable,
        is_for_loop=is_for_loop,
        is_while_loop=is_while_loop,
        candidate_invariant=candidate_invariant,
        decreases_expression=decreases_expression,
        iteration_bound=iteration_bound,
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )


# ---------------------------------------------------------------------------
# Module-summary sites
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ModuleSummarySiteData:
    """Payload for a module-summary site.

    Represents module-wide exports, public API contracts,
    and cached interprocedural summaries.
    """
    module_name: str
    exported_functions: Tuple[str, ...] = ()
    exported_classes: Tuple[str, ...] = ()
    has_cached_summary: bool = False


def make_module_summary_site(
    module_name: str,
    span: SourceSpan,
    *,
    exported_functions: Sequence[str] = (),
    exported_classes: Sequence[str] = (),
) -> ConcreteSite:
    """Create a module-summary observation site."""
    site_id = SiteId(
        kind=SiteKind.MODULE_SUMMARY,
        name=f"module:{module_name}",
        source_location=span.as_tuple(),
    )
    schema = CarrierSchema(
        name=f"module:{module_name}",
        constraints=[
            SchemaConstraint(
                field_names=("public_boundary",),
                description="public API boundary sections",
            ),
        ],
    )
    data = ModuleSummarySiteData(
        module_name=module_name,
        exported_functions=tuple(exported_functions),
        exported_classes=tuple(exported_classes),
    )
    return ConcreteSite(
        _site_id=site_id,
        _carrier_schema=schema,
        _metadata={"data": data, "span": span},
    )
