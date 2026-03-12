"""Factory methods for creating observation sites.

Provides :class:`SiteFactory` with a unified ``create_site`` entry point
and 14 specialised factory methods, one per SiteKind.  Each factory method
sets up the appropriate :class:`CarrierSchema` (with fields and constraints)
and metadata for that site family, producing a :class:`ConcreteSite`.

Usage::

    factory = SiteFactory()
    site = factory.create_argument_site("x", param_index=0, annotation="int")
    site = factory.create_site(SiteKind.SSA_VALUE, "y_1", ssa_version=1)
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import SiteId, SiteKind
from deppy.core.site import ConcreteSite
from deppy.types.base import (
    TypeBase,
    ANY_TYPE,
    BOOL_TYPE,
    INT_TYPE,
    FLOAT_TYPE,
    NONE_TYPE,
    STR_TYPE,
)
from deppy.types.carriers import CarrierSchema, SchemaConstraint


# ═══════════════════════════════════════════════════════════════════════════════
# Schema builders for each site family
# ═══════════════════════════════════════════════════════════════════════════════


def _argument_schema(
    param_name: str,
    annotation: Optional[str] = None,
    default_present: bool = False,
) -> CarrierSchema:
    """Build a carrier schema for an argument boundary site."""
    fields: Dict[str, TypeBase] = {
        "param_name": STR_TYPE,
        "param_type": ANY_TYPE,
    }
    constraints: list[SchemaConstraint] = []
    if annotation:
        constraints.append(SchemaConstraint(
            f"annotation present: {annotation}",
            ("param_type",),
        ))
    if default_present:
        fields["has_default"] = BOOL_TYPE
    return CarrierSchema(fields=fields, constraints=tuple(constraints), name=f"arg_{param_name}")


def _return_schema(return_index: int = 0) -> CarrierSchema:
    """Build a carrier schema for a return/output boundary site."""
    fields: Dict[str, TypeBase] = {
        "return_type": ANY_TYPE,
        "return_index": INT_TYPE,
    }
    return CarrierSchema(fields=fields, name=f"return_{return_index}")


def _ssa_schema(var_name: str, version: int = 0) -> CarrierSchema:
    """Build a carrier schema for an SSA value site."""
    fields: Dict[str, TypeBase] = {
        "var_name": STR_TYPE,
        "ssa_version": INT_TYPE,
        "value_type": ANY_TYPE,
    }
    constraints = (
        SchemaConstraint(
            f"SSA variable {var_name} version {version}",
            ("var_name", "ssa_version"),
        ),
    )
    return CarrierSchema(fields=fields, constraints=constraints, name=f"ssa_{var_name}_{version}")


def _branch_guard_schema(guard_id: str) -> CarrierSchema:
    """Build a carrier schema for a branch guard site."""
    fields: Dict[str, TypeBase] = {
        "guard_condition": ANY_TYPE,
        "branch_true_type": ANY_TYPE,
        "branch_false_type": ANY_TYPE,
    }
    return CarrierSchema(fields=fields, name=f"guard_{guard_id}")


def _call_result_schema(callee: str) -> CarrierSchema:
    """Build a carrier schema for a call result site."""
    fields: Dict[str, TypeBase] = {
        "callee_name": STR_TYPE,
        "return_type": ANY_TYPE,
        "arg_types": ANY_TYPE,
    }
    return CarrierSchema(fields=fields, name=f"call_{callee}")


def _tensor_shape_schema(tensor_name: str) -> CarrierSchema:
    """Build a carrier schema for a tensor shape site."""
    fields: Dict[str, TypeBase] = {
        "tensor_name": STR_TYPE,
        "shape": ANY_TYPE,
        "ndim": INT_TYPE,
        "dtype": STR_TYPE,
    }
    return CarrierSchema(fields=fields, name=f"tensor_shape_{tensor_name}")


def _tensor_order_schema(tensor_name: str) -> CarrierSchema:
    """Build a carrier schema for a tensor order site."""
    fields: Dict[str, TypeBase] = {
        "tensor_name": STR_TYPE,
        "layout_order": STR_TYPE,
        "contiguous": BOOL_TYPE,
    }
    return CarrierSchema(fields=fields, name=f"tensor_order_{tensor_name}")


def _tensor_indexing_schema(tensor_name: str) -> CarrierSchema:
    """Build a carrier schema for a tensor indexing site."""
    fields: Dict[str, TypeBase] = {
        "tensor_name": STR_TYPE,
        "index_expr": ANY_TYPE,
        "result_shape": ANY_TYPE,
        "bounds_checked": BOOL_TYPE,
    }
    return CarrierSchema(fields=fields, name=f"tensor_idx_{tensor_name}")


def _heap_protocol_schema(object_name: str) -> CarrierSchema:
    """Build a carrier schema for a heap protocol site."""
    fields: Dict[str, TypeBase] = {
        "object_name": STR_TYPE,
        "protocol": STR_TYPE,
        "state": STR_TYPE,
        "aliases": ANY_TYPE,
    }
    return CarrierSchema(fields=fields, name=f"heap_{object_name}")


def _error_schema(error_kind: str) -> CarrierSchema:
    """Build a carrier schema for an error site."""
    fields: Dict[str, TypeBase] = {
        "error_kind": STR_TYPE,
        "viability": STR_TYPE,
        "guarded": BOOL_TYPE,
        "source_op": STR_TYPE,
    }
    return CarrierSchema(fields=fields, name=f"error_{error_kind}")


def _loop_header_schema(loop_id: str) -> CarrierSchema:
    """Build a carrier schema for a loop header invariant site."""
    fields: Dict[str, TypeBase] = {
        "loop_variable": STR_TYPE,
        "invariant_type": ANY_TYPE,
        "iteration_bound": ANY_TYPE,
        "monotonic": BOOL_TYPE,
    }
    return CarrierSchema(fields=fields, name=f"loop_{loop_id}")


def _proof_schema(proof_name: str) -> CarrierSchema:
    """Build a carrier schema for a proof obligation site."""
    fields: Dict[str, TypeBase] = {
        "proposition": ANY_TYPE,
        "proof_status": STR_TYPE,
        "proof_term": ANY_TYPE,
    }
    return CarrierSchema(fields=fields, name=f"proof_{proof_name}")


def _trace_schema(trace_name: str) -> CarrierSchema:
    """Build a carrier schema for a trace instrumentation site."""
    fields: Dict[str, TypeBase] = {
        "trace_point": STR_TYPE,
        "observed_type": ANY_TYPE,
        "sample_count": INT_TYPE,
        "confidence": FLOAT_TYPE,
    }
    return CarrierSchema(fields=fields, name=f"trace_{trace_name}")


def _module_summary_schema(module_name: str) -> CarrierSchema:
    """Build a carrier schema for a module summary site."""
    fields: Dict[str, TypeBase] = {
        "module_name": STR_TYPE,
        "exports": ANY_TYPE,
        "import_deps": ANY_TYPE,
    }
    return CarrierSchema(fields=fields, name=f"module_{module_name}")


# ═══════════════════════════════════════════════════════════════════════════════
# Site factory
# ═══════════════════════════════════════════════════════════════════════════════


class SiteFactory:
    """Factory for creating observation sites with proper schemas and metadata.

    Provides both a generic ``create_site`` dispatcher and specialised
    factory methods for each of the 14 site families.
    """

    def __init__(self, file_path: str = "", default_source_line: int = 0) -> None:
        self._file_path = file_path
        self._default_source_line = default_source_line
        self._counter: Dict[SiteKind, int] = {}

    # ── Generic entry point ────────────────────────────────────────────────

    def create_site(
        self,
        kind: SiteKind,
        name: str,
        source_line: Optional[int] = None,
        source_col: int = 0,
        **kwargs: Any,
    ) -> ConcreteSite:
        """Create a site of the given kind using keyword arguments.

        Dispatches to the appropriate specialised factory method.
        """
        loc = self._make_location(source_line, source_col)

        dispatch = {
            SiteKind.ARGUMENT_BOUNDARY: self._create_argument_site_impl,
            SiteKind.RETURN_OUTPUT_BOUNDARY: self._create_return_site_impl,
            SiteKind.SSA_VALUE: self._create_ssa_site_impl,
            SiteKind.BRANCH_GUARD: self._create_branch_guard_site_impl,
            SiteKind.CALL_RESULT: self._create_call_site_impl,
            SiteKind.TENSOR_SHAPE: self._create_tensor_shape_site_impl,
            SiteKind.TENSOR_ORDER: self._create_tensor_order_site_impl,
            SiteKind.TENSOR_INDEXING: self._create_tensor_indexing_site_impl,
            SiteKind.HEAP_PROTOCOL: self._create_heap_site_impl,
            SiteKind.ERROR: self._create_error_site_impl,
            SiteKind.LOOP_HEADER_INVARIANT: self._create_loop_site_impl,
            SiteKind.PROOF: self._create_proof_site_impl,
            SiteKind.TRACE: self._create_trace_site_impl,
            SiteKind.MODULE_SUMMARY: self._create_module_summary_site_impl,
        }

        factory_fn = dispatch.get(kind)
        if factory_fn is None:
            raise ValueError(f"Unknown site kind: {kind}")

        return factory_fn(name, loc, **kwargs)

    # ── Specialised factory methods ────────────────────────────────────────

    def create_argument_site(
        self,
        param_name: str,
        param_index: int = 0,
        annotation: Optional[str] = None,
        has_default: bool = False,
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create an ARGUMENT_BOUNDARY site for a function parameter."""
        loc = self._make_location(source_line, source_col)
        schema = _argument_schema(param_name, annotation, has_default)
        site_id = SiteId(
            kind=SiteKind.ARGUMENT_BOUNDARY,
            name=f"arg_{param_name}",
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "param_name": param_name,
            "param_index": param_index,
            "annotation": annotation,
            "has_default": has_default,
        }
        self._increment_counter(SiteKind.ARGUMENT_BOUNDARY)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_return_site(
        self,
        return_index: int = 0,
        is_yield: bool = False,
        is_raise: bool = False,
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create a RETURN_OUTPUT_BOUNDARY site for a return/yield/raise."""
        loc = self._make_location(source_line, source_col)
        schema = _return_schema(return_index)
        suffix = "yield" if is_yield else ("raise" if is_raise else "return")
        name = f"{suffix}_{return_index}"
        site_id = SiteId(
            kind=SiteKind.RETURN_OUTPUT_BOUNDARY,
            name=name,
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "return_index": return_index,
            "is_yield": is_yield,
            "is_raise": is_raise,
        }
        self._increment_counter(SiteKind.RETURN_OUTPUT_BOUNDARY)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_ssa_site(
        self,
        var_name: str,
        ssa_version: int = 0,
        defining_op: str = "",
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create an SSA_VALUE site for an SSA variable definition."""
        loc = self._make_location(source_line, source_col)
        schema = _ssa_schema(var_name, ssa_version)
        site_id = SiteId(
            kind=SiteKind.SSA_VALUE,
            name=f"{var_name}_{ssa_version}",
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "var_name": var_name,
            "ssa_version": ssa_version,
            "defining_op": defining_op,
        }
        self._increment_counter(SiteKind.SSA_VALUE)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_branch_guard_site(
        self,
        guard_id: str,
        condition_text: str = "",
        narrowed_vars: Optional[List[str]] = None,
        is_true_branch: bool = True,
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create a BRANCH_GUARD site for a conditional branch."""
        loc = self._make_location(source_line, source_col)
        schema = _branch_guard_schema(guard_id)
        branch_tag = "T" if is_true_branch else "F"
        name = f"guard_{guard_id}_{branch_tag}"
        site_id = SiteId(
            kind=SiteKind.BRANCH_GUARD,
            name=name,
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "guard_id": guard_id,
            "condition_text": condition_text,
            "narrowed_vars": narrowed_vars or [],
            "is_true_branch": is_true_branch,
        }
        self._increment_counter(SiteKind.BRANCH_GUARD)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_call_site(
        self,
        callee_name: str,
        call_index: int = 0,
        is_method: bool = False,
        is_async: bool = False,
        arg_count: int = 0,
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create a CALL_RESULT site for a function/method call."""
        loc = self._make_location(source_line, source_col)
        schema = _call_result_schema(callee_name)
        name = f"call_{callee_name}_{call_index}"
        site_id = SiteId(
            kind=SiteKind.CALL_RESULT,
            name=name,
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "callee_name": callee_name,
            "call_index": call_index,
            "is_method": is_method,
            "is_async": is_async,
            "arg_count": arg_count,
        }
        self._increment_counter(SiteKind.CALL_RESULT)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_tensor_shape_site(
        self,
        tensor_name: str,
        ndim: Optional[int] = None,
        dtype: Optional[str] = None,
        framework: str = "torch",
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create a TENSOR_SHAPE site for tensor shape tracking."""
        loc = self._make_location(source_line, source_col)
        schema = _tensor_shape_schema(tensor_name)
        site_id = SiteId(
            kind=SiteKind.TENSOR_SHAPE,
            name=f"shape_{tensor_name}",
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "tensor_name": tensor_name,
            "ndim": ndim,
            "dtype": dtype,
            "framework": framework,
        }
        self._increment_counter(SiteKind.TENSOR_SHAPE)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_tensor_order_site(
        self,
        tensor_name: str,
        layout: str = "C",
        contiguous: bool = True,
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create a TENSOR_ORDER site for memory layout tracking."""
        loc = self._make_location(source_line, source_col)
        schema = _tensor_order_schema(tensor_name)
        site_id = SiteId(
            kind=SiteKind.TENSOR_ORDER,
            name=f"order_{tensor_name}",
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "tensor_name": tensor_name,
            "layout": layout,
            "contiguous": contiguous,
        }
        self._increment_counter(SiteKind.TENSOR_ORDER)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_tensor_indexing_site(
        self,
        tensor_name: str,
        index_expr: str = "",
        bounds_checked: bool = False,
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create a TENSOR_INDEXING site for index expression tracking."""
        loc = self._make_location(source_line, source_col)
        schema = _tensor_indexing_schema(tensor_name)
        site_id = SiteId(
            kind=SiteKind.TENSOR_INDEXING,
            name=f"idx_{tensor_name}",
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "tensor_name": tensor_name,
            "index_expr": index_expr,
            "bounds_checked": bounds_checked,
        }
        self._increment_counter(SiteKind.TENSOR_INDEXING)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_heap_site(
        self,
        object_name: str,
        protocol: str = "",
        state: str = "live",
        aliases: Optional[List[str]] = None,
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create a HEAP_PROTOCOL site for heap object protocol tracking."""
        loc = self._make_location(source_line, source_col)
        schema = _heap_protocol_schema(object_name)
        site_id = SiteId(
            kind=SiteKind.HEAP_PROTOCOL,
            name=f"heap_{object_name}",
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "object_name": object_name,
            "protocol": protocol,
            "state": state,
            "aliases": aliases or [],
        }
        self._increment_counter(SiteKind.HEAP_PROTOCOL)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_error_site(
        self,
        error_kind: str,
        error_index: int = 0,
        viability: str = "",
        guarded: bool = False,
        source_op: str = "",
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create an ERROR site for a potential error path."""
        loc = self._make_location(source_line, source_col)
        schema = _error_schema(error_kind)
        name = f"error_{error_kind}_{error_index}"
        site_id = SiteId(
            kind=SiteKind.ERROR,
            name=name,
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "error_kind": error_kind,
            "error_index": error_index,
            "viability": viability,
            "guarded": guarded,
            "source_op": source_op,
        }
        self._increment_counter(SiteKind.ERROR)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_loop_site(
        self,
        loop_id: str,
        loop_variable: str = "",
        iteration_bound: Optional[str] = None,
        is_while: bool = False,
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create a LOOP_HEADER_INVARIANT site for a loop header."""
        loc = self._make_location(source_line, source_col)
        schema = _loop_header_schema(loop_id)
        site_id = SiteId(
            kind=SiteKind.LOOP_HEADER_INVARIANT,
            name=f"loop_{loop_id}",
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "loop_id": loop_id,
            "loop_variable": loop_variable,
            "iteration_bound": iteration_bound,
            "is_while": is_while,
        }
        self._increment_counter(SiteKind.LOOP_HEADER_INVARIANT)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_proof_site(
        self,
        proof_name: str,
        proposition: str = "",
        status: str = "pending",
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create a PROOF site for a proof obligation."""
        loc = self._make_location(source_line, source_col)
        schema = _proof_schema(proof_name)
        site_id = SiteId(
            kind=SiteKind.PROOF,
            name=f"proof_{proof_name}",
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "proof_name": proof_name,
            "proposition": proposition,
            "status": status,
        }
        self._increment_counter(SiteKind.PROOF)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_trace_site(
        self,
        trace_name: str,
        trace_point: str = "",
        sample_count: int = 0,
        confidence: float = 0.0,
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create a TRACE site for runtime trace instrumentation."""
        loc = self._make_location(source_line, source_col)
        schema = _trace_schema(trace_name)
        site_id = SiteId(
            kind=SiteKind.TRACE,
            name=f"trace_{trace_name}",
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "trace_name": trace_name,
            "trace_point": trace_point,
            "sample_count": sample_count,
            "confidence": confidence,
        }
        self._increment_counter(SiteKind.TRACE)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    def create_module_summary_site(
        self,
        module_name: str,
        exports: Optional[List[str]] = None,
        import_deps: Optional[List[str]] = None,
        source_line: Optional[int] = None,
        source_col: int = 0,
    ) -> ConcreteSite:
        """Create a MODULE_SUMMARY site for a module-level summary."""
        loc = self._make_location(source_line, source_col)
        schema = _module_summary_schema(module_name)
        site_id = SiteId(
            kind=SiteKind.MODULE_SUMMARY,
            name=f"module_{module_name}",
            source_location=(self._file_path, loc[0], loc[1]) if self._file_path else None,
        )
        metadata = {
            "module_name": module_name,
            "exports": exports or [],
            "import_deps": import_deps or [],
        }
        self._increment_counter(SiteKind.MODULE_SUMMARY)
        return ConcreteSite(_site_id=site_id, _carrier_schema=schema, _metadata=metadata)

    # ── Internal dispatch implementations ──────────────────────────────────

    def _create_argument_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_argument_site(
            param_name=name,
            param_index=kwargs.get("param_index", 0),
            annotation=kwargs.get("annotation"),
            has_default=kwargs.get("has_default", False),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_return_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_return_site(
            return_index=kwargs.get("return_index", 0),
            is_yield=kwargs.get("is_yield", False),
            is_raise=kwargs.get("is_raise", False),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_ssa_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_ssa_site(
            var_name=name,
            ssa_version=kwargs.get("ssa_version", 0),
            defining_op=kwargs.get("defining_op", ""),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_branch_guard_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_branch_guard_site(
            guard_id=name,
            condition_text=kwargs.get("condition_text", ""),
            narrowed_vars=kwargs.get("narrowed_vars"),
            is_true_branch=kwargs.get("is_true_branch", True),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_call_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_call_site(
            callee_name=name,
            call_index=kwargs.get("call_index", 0),
            is_method=kwargs.get("is_method", False),
            is_async=kwargs.get("is_async", False),
            arg_count=kwargs.get("arg_count", 0),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_tensor_shape_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_tensor_shape_site(
            tensor_name=name,
            ndim=kwargs.get("ndim"),
            dtype=kwargs.get("dtype"),
            framework=kwargs.get("framework", "torch"),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_tensor_order_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_tensor_order_site(
            tensor_name=name,
            layout=kwargs.get("layout", "C"),
            contiguous=kwargs.get("contiguous", True),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_tensor_indexing_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_tensor_indexing_site(
            tensor_name=name,
            index_expr=kwargs.get("index_expr", ""),
            bounds_checked=kwargs.get("bounds_checked", False),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_heap_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_heap_site(
            object_name=name,
            protocol=kwargs.get("protocol", ""),
            state=kwargs.get("state", "live"),
            aliases=kwargs.get("aliases"),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_error_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_error_site(
            error_kind=name,
            error_index=kwargs.get("error_index", 0),
            viability=kwargs.get("viability", ""),
            guarded=kwargs.get("guarded", False),
            source_op=kwargs.get("source_op", ""),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_loop_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_loop_site(
            loop_id=name,
            loop_variable=kwargs.get("loop_variable", ""),
            iteration_bound=kwargs.get("iteration_bound"),
            is_while=kwargs.get("is_while", False),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_proof_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_proof_site(
            proof_name=name,
            proposition=kwargs.get("proposition", ""),
            status=kwargs.get("status", "pending"),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_trace_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_trace_site(
            trace_name=name,
            trace_point=kwargs.get("trace_point", ""),
            sample_count=kwargs.get("sample_count", 0),
            confidence=kwargs.get("confidence", 0.0),
            source_line=loc[0],
            source_col=loc[1],
        )

    def _create_module_summary_site_impl(
        self, name: str, loc: Tuple[int, int], **kwargs: Any
    ) -> ConcreteSite:
        return self.create_module_summary_site(
            module_name=name,
            exports=kwargs.get("exports"),
            import_deps=kwargs.get("import_deps"),
            source_line=loc[0],
            source_col=loc[1],
        )

    # ── Helpers ────────────────────────────────────────────────────────────

    def _make_location(
        self, line: Optional[int], col: int
    ) -> Tuple[int, int]:
        """Resolve a (line, col) tuple."""
        return (line if line is not None else self._default_source_line, col)

    def _increment_counter(self, kind: SiteKind) -> int:
        """Increment and return the counter for a site kind."""
        count = self._counter.get(kind, 0) + 1
        self._counter[kind] = count
        return count

    # ── Diagnostics ────────────────────────────────────────────────────────

    @property
    def creation_counts(self) -> Dict[SiteKind, int]:
        """Return how many sites of each kind have been created."""
        return dict(self._counter)

    @property
    def total_created(self) -> int:
        """Total number of sites created by this factory."""
        return sum(self._counter.values())

    def reset_counters(self) -> None:
        """Reset all creation counters."""
        self._counter.clear()

    def __repr__(self) -> str:
        return f"SiteFactory(file={self._file_path!r}, created={self.total_created})"
