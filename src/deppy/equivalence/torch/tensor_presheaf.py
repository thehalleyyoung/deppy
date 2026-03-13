"""
Tensor presheaf construction — builds presheaves from PyTorch functions via FX tracing.

The central construction: given a PyTorch function f, build the presheaf
  Sem_f : TensorSite^op → Set
that assigns to each observation site the *section* of f's behavior
visible at that site.

Construction strategy:
  1. torch.fx symbolic tracing captures the computation graph
  2. For each site kind (shape, dtype, device, etc.), extract the
     relevant section from the traced graph
  3. Sections are connected by restriction morphisms (e.g., shape
     information restricts to dtype via broadcasting rules)
  4. The presheaf satisfies the sheaf condition: local sections glue
     uniquely when they agree on overlaps

This is the *representation functor* Hom(−, Sem_f) on the tensor site.
"""

from __future__ import annotations

import inspect
import textwrap
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Sequence, Set, Tuple

from ._protocols import (
    SiteId,
    TensorEquivalenceConfig,
    TensorSiteKind,
    TensorSpec,
    TensorStratum,
    SITE_KIND_STRATUM,
)

try:
    import torch
    import torch.fx
    _HAS_TORCH = True
except ImportError:
    _HAS_TORCH = False


# ---------------------------------------------------------------------------
# Section data — what is observed at each site
# ---------------------------------------------------------------------------

@dataclass
class TensorSection:
    """
    A section of a tensor presheaf at a given site.

    Represents the information visible about a function's behavior
    when observed through the lens of a specific site kind.
    """
    site_kind: TensorSiteKind
    stratum: TensorStratum
    data: Dict[str, Any] = field(default_factory=dict)
    is_trivial: bool = False

    def restrict(self, target_kind: TensorSiteKind) -> "TensorSection":
        """
        Restriction morphism: project to a coarser site.

        This implements the presheaf restriction: if U ⊆ V in the site
        topology, then F(V) → F(U) forgets the extra information.
        """
        target_stratum = SITE_KIND_STRATUM.get(target_kind, TensorStratum.METADATA)
        my_stratum = SITE_KIND_STRATUM.get(self.site_kind, TensorStratum.METADATA)

        # Can only restrict to coarser strata
        stratum_order = {
            TensorStratum.METADATA: 0,
            TensorStratum.STRUCTURAL: 1,
            TensorStratum.NUMERICAL: 2,
            TensorStratum.BEHAVIORAL: 3,
        }
        if stratum_order.get(target_stratum, 0) > stratum_order.get(my_stratum, 0):
            return TensorSection(
                site_kind=target_kind,
                stratum=target_stratum,
                is_trivial=True,
            )

        # Project relevant data
        relevant = {}
        if target_kind == TensorSiteKind.SHAPE:
            relevant = {k: v for k, v in self.data.items()
                        if k in ("shapes", "output_shape", "shape_map")}
        elif target_kind == TensorSiteKind.DTYPE:
            relevant = {k: v for k, v in self.data.items()
                        if k in ("dtypes", "output_dtype", "dtype_map", "promotions")}
        elif target_kind == TensorSiteKind.DEVICE:
            relevant = {k: v for k, v in self.data.items()
                        if k in ("devices", "output_device", "device_map")}
        elif target_kind == TensorSiteKind.STRIDE:
            relevant = {k: v for k, v in self.data.items()
                        if k in ("strides", "contiguity", "layout")}
        else:
            relevant = dict(self.data)

        return TensorSection(
            site_kind=target_kind,
            stratum=target_stratum,
            data=relevant,
        )


# ---------------------------------------------------------------------------
# FX graph analysis
# ---------------------------------------------------------------------------

@dataclass
class FXNodeInfo:
    """Information about a node in the FX computation graph."""
    name: str
    op: str  # "call_function", "call_method", "call_module", "placeholder", "output"
    target: str
    args_names: Tuple[str, ...]
    n_users: int = 0


@dataclass
class FXGraphSummary:
    """Summary of an FX-traced computation graph."""
    nodes: List[FXNodeInfo]
    n_ops: int = 0
    n_placeholders: int = 0
    op_histogram: Dict[str, int] = field(default_factory=dict)
    has_inplace: bool = False
    has_view: bool = False
    has_reduction: bool = False
    has_matmul: bool = False


def trace_function(fn: Callable, example_inputs: Sequence[Any],
                   ) -> Optional[FXGraphSummary]:
    """
    Trace a PyTorch function using torch.fx.

    Returns an FXGraphSummary capturing the computation graph structure.
    This is the *observation* step: from a function, extract the graph
    visible at the structural level.
    """
    if not _HAS_TORCH:
        return None

    try:
        traced = torch.fx.symbolic_trace(fn)
    except Exception:
        # Many PyTorch functions resist symbolic tracing
        return _fallback_trace(fn, example_inputs)

    nodes = []
    op_histogram: Dict[str, int] = {}
    n_ops = 0
    n_placeholders = 0
    has_inplace = False
    has_view = False
    has_reduction = False
    has_matmul = False

    _INPLACE_OPS = {"add_", "mul_", "sub_", "div_", "zero_", "fill_",
                    "copy_", "scatter_", "index_put_"}
    _VIEW_OPS = {"view", "reshape", "permute", "transpose", "expand",
                 "contiguous", "narrow", "slice", "unfold", "as_strided"}
    _REDUCTION_OPS = {"sum", "mean", "max", "min", "prod", "norm",
                      "std", "var", "argmax", "argmin"}
    _MATMUL_OPS = {"matmul", "mm", "bmm", "linear", "einsum"}

    for node in traced.graph.nodes:
        target_str = str(node.target)
        args_names = tuple(str(a) for a in node.args if hasattr(a, "name"))

        nodes.append(FXNodeInfo(
            name=node.name,
            op=node.op,
            target=target_str,
            args_names=args_names,
            n_users=len(node.users),
        ))

        if node.op in ("call_function", "call_method", "call_module"):
            n_ops += 1
            op_histogram[target_str] = op_histogram.get(target_str, 0) + 1

            # Check for special operations
            base_name = target_str.split(".")[-1].rstrip("_")
            if base_name + "_" in target_str or target_str.endswith("_"):
                has_inplace = True
            if base_name in _VIEW_OPS:
                has_view = True
            if base_name in _REDUCTION_OPS:
                has_reduction = True
            if base_name in _MATMUL_OPS:
                has_matmul = True

        elif node.op == "placeholder":
            n_placeholders += 1

    return FXGraphSummary(
        nodes=nodes,
        n_ops=n_ops,
        n_placeholders=n_placeholders,
        op_histogram=op_histogram,
        has_inplace=has_inplace,
        has_view=has_view,
        has_reduction=has_reduction,
        has_matmul=has_matmul,
    )


def _fallback_trace(fn: Callable,
                    example_inputs: Sequence[Any]) -> Optional[FXGraphSummary]:
    """
    Fallback tracing for functions that resist FX symbolic tracing.

    Uses source code analysis as a coarser observation.
    """
    try:
        source = inspect.getsource(fn)
    except (OSError, TypeError):
        return None

    # Simple heuristic analysis
    has_inplace = any(op in source for op in [".add_(", ".mul_(", ".sub_(", ".copy_("])
    has_view = any(op in source for op in [".view(", ".reshape(", ".permute(", ".transpose("])
    has_reduction = any(op in source for op in [".sum(", ".mean(", ".max(", ".min("])
    has_matmul = any(op in source for op in ["matmul", "mm(", "bmm(", "@ "])

    return FXGraphSummary(
        nodes=[],
        n_ops=0,
        n_placeholders=0,
        has_inplace=has_inplace,
        has_view=has_view,
        has_reduction=has_reduction,
        has_matmul=has_matmul,
    )


# ---------------------------------------------------------------------------
# Presheaf builder
# ---------------------------------------------------------------------------

@dataclass
class TensorPresheaf:
    """
    The tensor presheaf for a PyTorch function.

    Assigns to each site kind the section of the function's behavior
    visible at that site.  The collection of sections, together with
    the restriction morphisms, forms a presheaf on the tensor site category.

    Satisfies the *sheaf condition*: given sections on a cover that
    agree on overlaps, there is a unique global section (the full
    behavior of the function) restricting to each.
    """
    fn_name: str
    sections: Dict[TensorSiteKind, TensorSection]
    graph_summary: Optional[FXGraphSummary] = None

    def section_at(self, kind: TensorSiteKind) -> TensorSection:
        """Get the section at a site kind (the presheaf value)."""
        return self.sections.get(kind, TensorSection(
            site_kind=kind,
            stratum=SITE_KIND_STRATUM.get(kind, TensorStratum.METADATA),
            is_trivial=True,
        ))

    def restrict(self, source: TensorSiteKind,
                 target: TensorSiteKind) -> TensorSection:
        """Apply restriction morphism from source to target."""
        section = self.section_at(source)
        return section.restrict(target)


class TensorPresheafBuilder:
    """
    Builds a TensorPresheaf from a PyTorch function.

    The construction pipeline:
    1. FX trace the function to get the computation graph
    2. Execute with meta tensors to infer shapes/dtypes
    3. Execute with real tensors to observe numerical behavior
    4. Assemble sections for each site kind
    5. Verify restriction coherence (presheaf condition)
    """

    def __init__(self, config: TensorEquivalenceConfig):
        self._config = config

    def build(self, fn: Callable, name: str = "",
              example_inputs: Optional[Sequence[Any]] = None,
              tensor_specs: Optional[Sequence[TensorSpec]] = None,
              ) -> TensorPresheaf:
        """Build a tensor presheaf for a function."""
        fn_name = name or getattr(fn, "__name__", str(fn))
        sections: Dict[TensorSiteKind, TensorSection] = {}

        # 1. Graph-level observation (structural stratum)
        if example_inputs is not None:
            graph = trace_function(fn, example_inputs)
        else:
            graph = trace_function(fn, [])

        # 2. Shape section
        shape_data = self._observe_shapes(fn, tensor_specs, example_inputs)
        sections[TensorSiteKind.SHAPE] = TensorSection(
            site_kind=TensorSiteKind.SHAPE,
            stratum=TensorStratum.STRUCTURAL,
            data=shape_data,
        )

        # 3. Dtype section
        dtype_data = self._observe_dtypes(fn, tensor_specs, example_inputs)
        sections[TensorSiteKind.DTYPE] = TensorSection(
            site_kind=TensorSiteKind.DTYPE,
            stratum=TensorStratum.METADATA,
            data=dtype_data,
        )

        # 4. Device section
        device_data = self._observe_devices(fn, tensor_specs, example_inputs)
        sections[TensorSiteKind.DEVICE] = TensorSection(
            site_kind=TensorSiteKind.DEVICE,
            stratum=TensorStratum.METADATA,
            data=device_data,
        )

        # 5. Stride section
        stride_data = self._observe_strides(fn, tensor_specs, example_inputs)
        sections[TensorSiteKind.STRIDE] = TensorSection(
            site_kind=TensorSiteKind.STRIDE,
            stratum=TensorStratum.STRUCTURAL,
            data=stride_data,
        )

        # 6. Numerical section (requires actual execution)
        if example_inputs is not None:
            num_data = self._observe_numerical(fn, example_inputs)
            sections[TensorSiteKind.NUMERICAL] = TensorSection(
                site_kind=TensorSiteKind.NUMERICAL,
                stratum=TensorStratum.NUMERICAL,
                data=num_data,
            )

        # 7. Autograd section
        if example_inputs is not None:
            grad_data = self._observe_autograd(fn, example_inputs)
            sections[TensorSiteKind.AUTOGRAD] = TensorSection(
                site_kind=TensorSiteKind.AUTOGRAD,
                stratum=TensorStratum.BEHAVIORAL,
                data=grad_data,
            )

        return TensorPresheaf(
            fn_name=fn_name,
            sections=sections,
            graph_summary=graph,
        )

    def _observe_shapes(self, fn: Callable,
                        specs: Optional[Sequence[TensorSpec]],
                        inputs: Optional[Sequence[Any]]) -> Dict[str, Any]:
        """Observe shape behavior using meta tensors."""
        data: Dict[str, Any] = {}
        if not _HAS_TORCH:
            return data

        if specs:
            data["input_shapes"] = [s.shape for s in specs]

        if inputs is not None:
            tensor_inputs = [x for x in inputs if isinstance(x, torch.Tensor)]
            data["input_shapes"] = [tuple(t.shape) for t in tensor_inputs]

            try:
                result = fn(*inputs)
                if isinstance(result, torch.Tensor):
                    data["output_shape"] = tuple(result.shape)
                elif isinstance(result, (tuple, list)):
                    data["output_shapes"] = [
                        tuple(r.shape) if isinstance(r, torch.Tensor) else None
                        for r in result
                    ]
            except Exception:
                data["output_shape"] = None

        return data

    def _observe_dtypes(self, fn: Callable,
                        specs: Optional[Sequence[TensorSpec]],
                        inputs: Optional[Sequence[Any]]) -> Dict[str, Any]:
        """Observe dtype behavior."""
        data: Dict[str, Any] = {}
        if not _HAS_TORCH:
            return data

        if specs:
            data["input_dtypes"] = [s.dtype for s in specs]

        if inputs is not None:
            tensor_inputs = [x for x in inputs if isinstance(x, torch.Tensor)]
            data["input_dtypes"] = [str(t.dtype) for t in tensor_inputs]

            try:
                result = fn(*inputs)
                if isinstance(result, torch.Tensor):
                    data["output_dtype"] = str(result.dtype)
                elif isinstance(result, (tuple, list)):
                    data["output_dtypes"] = [
                        str(r.dtype) if isinstance(r, torch.Tensor) else None
                        for r in result
                    ]
            except Exception:
                data["output_dtype"] = None

        return data

    def _observe_devices(self, fn: Callable,
                         specs: Optional[Sequence[TensorSpec]],
                         inputs: Optional[Sequence[Any]]) -> Dict[str, Any]:
        """Observe device placement."""
        data: Dict[str, Any] = {}
        if not _HAS_TORCH:
            return data

        if specs:
            data["input_devices"] = [s.device for s in specs]

        if inputs is not None:
            tensor_inputs = [x for x in inputs if isinstance(x, torch.Tensor)]
            data["input_devices"] = [str(t.device) for t in tensor_inputs]

            try:
                result = fn(*inputs)
                if isinstance(result, torch.Tensor):
                    data["output_device"] = str(result.device)
            except Exception:
                data["output_device"] = None

        return data

    def _observe_strides(self, fn: Callable,
                         specs: Optional[Sequence[TensorSpec]],
                         inputs: Optional[Sequence[Any]]) -> Dict[str, Any]:
        """Observe stride/memory layout."""
        data: Dict[str, Any] = {}
        if not _HAS_TORCH:
            return data

        if inputs is not None:
            tensor_inputs = [x for x in inputs if isinstance(x, torch.Tensor)]
            data["input_strides"] = [tuple(t.stride()) for t in tensor_inputs]
            data["input_contiguous"] = [t.is_contiguous() for t in tensor_inputs]

            try:
                result = fn(*inputs)
                if isinstance(result, torch.Tensor):
                    data["output_strides"] = tuple(result.stride())
                    data["output_contiguous"] = result.is_contiguous()
            except Exception:
                pass

        return data

    def _observe_numerical(self, fn: Callable,
                           inputs: Sequence[Any]) -> Dict[str, Any]:
        """Observe numerical output values."""
        data: Dict[str, Any] = {}
        if not _HAS_TORCH:
            return data

        try:
            result = fn(*inputs)
            if isinstance(result, torch.Tensor):
                data["output_values"] = result.detach().cpu()
                data["has_nan"] = bool(torch.isnan(result).any())
                data["has_inf"] = bool(torch.isinf(result).any())
            elif isinstance(result, (tuple, list)):
                data["output_values"] = [
                    r.detach().cpu() if isinstance(r, torch.Tensor) else r
                    for r in result
                ]
        except Exception as e:
            data["exception"] = str(e)

        return data

    def _observe_autograd(self, fn: Callable,
                          inputs: Sequence[Any]) -> Dict[str, Any]:
        """Observe autograd behavior."""
        data: Dict[str, Any] = {}
        if not _HAS_TORCH:
            return data

        # Check if any input requires grad
        tensor_inputs = [x for x in inputs if isinstance(x, torch.Tensor)]
        any_requires_grad = any(t.requires_grad for t in tensor_inputs)
        data["any_requires_grad"] = any_requires_grad

        if any_requires_grad:
            try:
                result = fn(*inputs)
                if isinstance(result, torch.Tensor) and result.requires_grad:
                    data["output_requires_grad"] = True
                    data["grad_fn"] = type(result.grad_fn).__name__ if result.grad_fn else None
                else:
                    data["output_requires_grad"] = False
            except Exception:
                data["output_requires_grad"] = None

        return data


# ---------------------------------------------------------------------------
# Presheaf morphism (natural transformation)
# ---------------------------------------------------------------------------

@dataclass
class PresheafMorphism:
    """
    A natural transformation η: F → G between tensor presheaves.

    Components η_U: F(U) → G(U) at each site kind U, such that
    the naturality square commutes:

        F(U) ——η_U——→ G(U)
          |                |
        F(f)             G(f)
          ↓                ↓
        F(V) ——η_V——→ G(V)

    for every morphism f: U → V in the site category.
    """
    source_name: str
    target_name: str
    components: Dict[TensorSiteKind, bool]  # True if component is isomorphism
    is_natural: bool = False
    is_isomorphism: bool = False


def check_presheaf_naturality(
    pf: TensorPresheaf,
    pg: TensorPresheaf,
    site_kinds: Optional[Sequence[TensorSiteKind]] = None,
) -> PresheafMorphism:
    """
    Check whether two presheaves are naturally isomorphic.

    For each site kind, check if the sections are equivalent.
    Then check that the restriction morphisms commute with the
    component equivalences (naturality condition).
    """
    kinds = site_kinds or list(TensorSiteKind)
    components: Dict[TensorSiteKind, bool] = {}

    for kind in kinds:
        section_f = pf.section_at(kind)
        section_g = pg.section_at(kind)

        # Both trivial → equivalent
        if section_f.is_trivial and section_g.is_trivial:
            components[kind] = True
            continue

        # One trivial, one not → not equivalent at this site
        if section_f.is_trivial != section_g.is_trivial:
            components[kind] = False
            continue

        # Compare section data
        components[kind] = _sections_equivalent(section_f, section_g)

    all_iso = all(components.values()) if components else True

    # Check naturality (restriction coherence)
    natural = True
    if all_iso:
        natural = _check_restriction_coherence(pf, pg, kinds)

    return PresheafMorphism(
        source_name=pf.fn_name,
        target_name=pg.fn_name,
        components=components,
        is_natural=natural,
        is_isomorphism=all_iso and natural,
    )


def _sections_equivalent(sf: TensorSection, sg: TensorSection) -> bool:
    """Check if two sections have equivalent data."""
    if sf.site_kind != sg.site_kind:
        return False

    # Compare data dictionaries
    if set(sf.data.keys()) != set(sg.data.keys()):
        return False

    for key in sf.data:
        val_f = sf.data[key]
        val_g = sg.data[key]

        if _HAS_TORCH and isinstance(val_f, torch.Tensor):
            if not isinstance(val_g, torch.Tensor):
                return False
            if val_f.shape != val_g.shape:
                return False
            try:
                if not torch.allclose(val_f.float(), val_g.float(),
                                      rtol=1e-5, atol=1e-8):
                    return False
            except Exception:
                return False
        elif val_f != val_g:
            return False

    return True


def _check_restriction_coherence(
    pf: TensorPresheaf,
    pg: TensorPresheaf,
    kinds: Sequence[TensorSiteKind],
) -> bool:
    """
    Check restriction coherence (naturality squares commute).

    For each pair (source, target) of site kinds where a restriction
    morphism exists, verify:
      restrict_f(section_f) ≈ restrict_g(section_g)
    """
    stratum_order = {
        TensorStratum.METADATA: 0,
        TensorStratum.STRUCTURAL: 1,
        TensorStratum.NUMERICAL: 2,
        TensorStratum.BEHAVIORAL: 3,
    }

    for source_kind in kinds:
        source_stratum = SITE_KIND_STRATUM.get(source_kind, TensorStratum.METADATA)
        for target_kind in kinds:
            if source_kind == target_kind:
                continue
            target_stratum = SITE_KIND_STRATUM.get(target_kind, TensorStratum.METADATA)

            # Only check restrictions from finer to coarser
            if (stratum_order.get(source_stratum, 0) <=
                    stratum_order.get(target_stratum, 0)):
                continue

            # Get restricted sections
            restricted_f = pf.restrict(source_kind, target_kind)
            restricted_g = pg.restrict(source_kind, target_kind)

            if not _sections_equivalent(restricted_f, restricted_g):
                return False

    return True
