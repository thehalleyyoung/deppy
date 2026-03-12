"""Theory Family 6: Tensor Order Theory.

Handles sort, argsort, topk, and permutation tracking.
Forward: track order properties (sorted, unique, permutation).
Backward: require sortedness/uniqueness.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism

from .theory_pack_base import (
    BoundaryClassification,
    SolverResult,
    SolverStatus,
    TheoryPackBase,
    merge_refinements,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Order properties
# ═══════════════════════════════════════════════════════════════════════════════


class OrderProperty(Enum):
    """Properties of tensor element ordering."""
    UNSORTED = "unsorted"
    SORTED_ASC = "sorted_ascending"
    SORTED_DESC = "sorted_descending"
    SORTED_STABLE_ASC = "sorted_stable_ascending"
    SORTED_STABLE_DESC = "sorted_stable_descending"
    UNIQUE = "unique"
    PERMUTATION = "permutation"
    ARGSORT = "argsort"
    TOPK = "topk"
    IDENTITY = "identity"
    REVERSED = "reversed"

    @property
    def is_sorted(self) -> bool:
        return self in (
            OrderProperty.SORTED_ASC, OrderProperty.SORTED_DESC,
            OrderProperty.SORTED_STABLE_ASC, OrderProperty.SORTED_STABLE_DESC,
        )

    @property
    def is_ascending(self) -> bool:
        return self in (OrderProperty.SORTED_ASC, OrderProperty.SORTED_STABLE_ASC)


@dataclass(frozen=True)
class OrderInfo:
    """Order-related information for a tensor or sequence."""
    properties: FrozenSet[OrderProperty] = frozenset()
    sort_dim: Optional[int] = None
    sort_stable: bool = False
    k_value: Optional[int] = None
    permutation_source: Optional[str] = None
    index_range: Optional[Tuple[int, int]] = None

    @property
    def is_sorted(self) -> bool:
        return any(p.is_sorted for p in self.properties)

    @property
    def is_unique(self) -> bool:
        return OrderProperty.UNIQUE in self.properties

    @property
    def is_permutation(self) -> bool:
        return OrderProperty.PERMUTATION in self.properties

    def with_property(self, prop: OrderProperty) -> OrderInfo:
        return OrderInfo(
            properties=self.properties | {prop},
            sort_dim=self.sort_dim, sort_stable=self.sort_stable,
            k_value=self.k_value, permutation_source=self.permutation_source,
            index_range=self.index_range,
        )

    def without_property(self, prop: OrderProperty) -> OrderInfo:
        return OrderInfo(
            properties=self.properties - {prop},
            sort_dim=self.sort_dim, sort_stable=self.sort_stable,
            k_value=self.k_value, permutation_source=self.permutation_source,
            index_range=self.index_range,
        )

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {}
        if self.properties:
            refs["order_properties"] = {p.value for p in self.properties}
        if self.sort_dim is not None:
            refs["sort_dim"] = self.sort_dim
        if self.sort_stable:
            refs["sort_stable"] = True
        if self.k_value is not None:
            refs["topk_k"] = self.k_value
        if self.permutation_source is not None:
            refs["permutation_source"] = self.permutation_source
        if self.index_range is not None:
            refs["index_range"] = self.index_range
        if self.is_sorted:
            refs["is_sorted"] = True
        if self.is_unique:
            refs["is_unique"] = True
        return refs

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> OrderInfo:
        props_raw = refs.get("order_properties", set())
        properties: Set[OrderProperty] = set()
        for p in props_raw:
            try:
                properties.add(OrderProperty(p))
            except ValueError:
                pass
        if refs.get("is_sorted"):
            properties.add(OrderProperty.SORTED_ASC)
        if refs.get("is_unique"):
            properties.add(OrderProperty.UNIQUE)
        return OrderInfo(
            properties=frozenset(properties),
            sort_dim=refs.get("sort_dim"),
            sort_stable=refs.get("sort_stable", False),
            k_value=refs.get("topk_k"),
            permutation_source=refs.get("permutation_source"),
            index_range=refs.get("index_range"),
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Order operation rules
# ═══════════════════════════════════════════════════════════════════════════════


def sort_output_order(
    input_info: OrderInfo,
    descending: bool = False,
    stable: bool = False,
    dim: int = -1,
) -> Tuple[OrderInfo, OrderInfo]:
    """Compute output order info for sort (returns values, indices)."""
    if descending:
        sort_prop = OrderProperty.SORTED_STABLE_DESC if stable else OrderProperty.SORTED_DESC
    else:
        sort_prop = OrderProperty.SORTED_STABLE_ASC if stable else OrderProperty.SORTED_ASC

    values_info = OrderInfo(
        properties=frozenset({sort_prop}),
        sort_dim=dim, sort_stable=stable,
    )
    indices_info = OrderInfo(
        properties=frozenset({OrderProperty.ARGSORT, OrderProperty.PERMUTATION}),
        sort_dim=dim, sort_stable=stable,
    )
    return values_info, indices_info


def argsort_output_order(
    input_info: OrderInfo,
    descending: bool = False,
    stable: bool = False,
    dim: int = -1,
) -> OrderInfo:
    """Compute output order info for argsort."""
    return OrderInfo(
        properties=frozenset({OrderProperty.ARGSORT, OrderProperty.PERMUTATION}),
        sort_dim=dim, sort_stable=stable,
    )


def topk_output_order(
    input_info: OrderInfo,
    k: int,
    largest: bool = True,
    sorted_out: bool = True,
    dim: int = -1,
) -> Tuple[OrderInfo, OrderInfo]:
    """Compute output order info for topk."""
    props: Set[OrderProperty] = {OrderProperty.TOPK}
    if sorted_out:
        props.add(OrderProperty.SORTED_DESC if largest else OrderProperty.SORTED_ASC)
    values_info = OrderInfo(
        properties=frozenset(props), sort_dim=dim, k_value=k,
    )
    indices_info = OrderInfo(
        properties=frozenset({OrderProperty.TOPK, OrderProperty.PERMUTATION}),
        sort_dim=dim, k_value=k,
    )
    return values_info, indices_info


def unique_output_order(input_info: OrderInfo, sorted_out: bool = True) -> OrderInfo:
    """Compute output order info for unique."""
    props: Set[OrderProperty] = {OrderProperty.UNIQUE}
    if sorted_out:
        props.add(OrderProperty.SORTED_ASC)
    return OrderInfo(properties=frozenset(props))


def gather_preserves_order(input_info: OrderInfo, index_info: OrderInfo) -> OrderInfo:
    """Determine what order properties survive a gather operation."""
    if index_info.is_sorted and input_info.is_sorted:
        return input_info
    return OrderInfo(properties=frozenset())


def index_select_order(input_info: OrderInfo, index_info: OrderInfo) -> OrderInfo:
    """Determine order after index_select."""
    if index_info.is_sorted:
        if input_info.is_sorted:
            return input_info
    return OrderInfo(properties=frozenset())


def reverse_order(input_info: OrderInfo) -> OrderInfo:
    """Order after reversal."""
    new_props: Set[OrderProperty] = set()
    for p in input_info.properties:
        if p == OrderProperty.SORTED_ASC:
            new_props.add(OrderProperty.SORTED_DESC)
        elif p == OrderProperty.SORTED_DESC:
            new_props.add(OrderProperty.SORTED_ASC)
        elif p == OrderProperty.SORTED_STABLE_ASC:
            new_props.add(OrderProperty.SORTED_STABLE_DESC)
        elif p == OrderProperty.SORTED_STABLE_DESC:
            new_props.add(OrderProperty.SORTED_STABLE_ASC)
        elif p == OrderProperty.UNIQUE:
            new_props.add(p)
    new_props.add(OrderProperty.REVERSED)
    return OrderInfo(properties=frozenset(new_props))


def elementwise_order(a_info: OrderInfo, b_info: OrderInfo) -> OrderInfo:
    """Order after elementwise operations (add, mul, etc.)."""
    return OrderInfo(properties=frozenset())


# ═══════════════════════════════════════════════════════════════════════════════
# TensorOrderTheoryPack
# ═══════════════════════════════════════════════════════════════════════════════


class TensorOrderTheoryPack(TheoryPackBase):
    """Theory Family 6: Tensor Order Theory.

    Handles TENSOR_ORDER sites for sort/argsort/topk/unique operations.
    """

    pack_name = "tensor_order"
    pack_priority = 35

    _APPLICABLE = frozenset({
        SiteKind.TENSOR_ORDER,
        SiteKind.SSA_VALUE,
        SiteKind.CALL_RESULT,
        SiteKind.ERROR,
    })

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._APPLICABLE

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        refs = section.refinements
        info = OrderInfo.from_refinements(refs)

        op_name = refs.get("order_op")
        if op_name is None:
            if info.properties:
                new_refs = dict(refs)
                new_refs.update(info.to_refinements())
                return SolverResult(
                    status=SolverStatus.REFINED,
                    section=LocalSection(
                        site_id=section.site_id,
                        carrier_type=section.carrier_type,
                        refinements=new_refs,
                        trust=section.trust,
                        provenance=f"order info: {info.properties}",
                        witnesses=dict(section.witnesses),
                    ),
                    explanation=f"order properties: {info.properties}",
                )
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation="no order information",
            )

        input_info = info
        params = refs.get("order_params", {})
        output_which = refs.get("output_which", "values")

        if op_name == "sort":
            desc = params.get("descending", False)
            stable = params.get("stable", False)
            dim = params.get("dim", -1)
            val_info, idx_info = sort_output_order(input_info, desc, stable, dim)
            result_info = val_info if output_which == "values" else idx_info
        elif op_name == "argsort":
            desc = params.get("descending", False)
            stable = params.get("stable", False)
            dim = params.get("dim", -1)
            result_info = argsort_output_order(input_info, desc, stable, dim)
        elif op_name == "topk":
            k = params.get("k", 1)
            largest = params.get("largest", True)
            sorted_out = params.get("sorted", True)
            dim = params.get("dim", -1)
            val_info, idx_info = topk_output_order(input_info, k, largest, sorted_out, dim)
            result_info = val_info if output_which == "values" else idx_info
        elif op_name == "unique":
            sorted_out = params.get("sorted", True)
            result_info = unique_output_order(input_info, sorted_out)
        elif op_name == "reverse" or op_name == "flip":
            result_info = reverse_order(input_info)
        elif op_name == "gather":
            idx_info_raw = OrderInfo.from_refinements(params.get("index_info", {}))
            result_info = gather_preserves_order(input_info, idx_info_raw)
        elif op_name == "index_select":
            idx_info_raw = OrderInfo.from_refinements(params.get("index_info", {}))
            result_info = index_select_order(input_info, idx_info_raw)
        else:
            result_info = OrderInfo(properties=frozenset())

        new_refs = dict(refs)
        new_refs.update(result_info.to_refinements())
        new_refs["_order_resolved"] = True

        return SolverResult(
            status=SolverStatus.SOLVED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=TrustLevel.BOUNDED_AUTO,
                provenance=f"order: {op_name} -> {result_info.properties}",
                witnesses=dict(section.witnesses),
            ),
            explanation=f"{op_name}: {result_info.properties}",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        restricted = morphism.restrict(section)
        info = OrderInfo.from_refinements(section.refinements)

        if not info.properties:
            return restricted

        op_name = None
        if morphism.metadata:
            op_name = morphism.metadata.get("order_op")

        if op_name is not None:
            params = morphism.metadata.get("order_params", {}) if morphism.metadata else {}
            if op_name in ("add", "sub", "mul", "div"):
                result_info = OrderInfo(properties=frozenset())
            elif op_name == "reverse" or op_name == "flip":
                result_info = reverse_order(info)
            elif op_name == "index_select":
                idx_info = OrderInfo.from_refinements(params.get("index_info", {}))
                result_info = index_select_order(info, idx_info)
            else:
                result_info = info
        else:
            result_info = info

        new_refs = merge_refinements(restricted.refinements, result_info.to_refinements(), "meet")
        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance=f"order forward: {result_info.properties}",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        refs = section.refinements
        required_refs: Dict[str, Any] = {}

        if refs.get("requires_sorted"):
            required_refs["is_sorted"] = True
        if refs.get("requires_unique"):
            required_refs["is_unique"] = True
        if refs.get("requires_permutation"):
            required_refs["order_properties"] = {"permutation"}

        op_name = None
        if morphism.metadata:
            op_name = morphism.metadata.get("order_op")
        if op_name == "sort":
            pass
        elif op_name == "argsort":
            pass

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required_refs,
            trust=TrustLevel.RESIDUAL,
            provenance="order pullback",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        name = error_site.name
        if "sort" in name.lower():
            return "input tensor is valid for sort"
        if "topk" in name.lower():
            return "k <= tensor.size(dim)"
        if "unique" in name.lower():
            return "input tensor is valid for unique"
        return f"order precondition for {name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        refs = section.refinements
        if refs.get("_order_resolved"):
            return BoundaryClassification.FULLY_PROVEN
        info = OrderInfo.from_refinements(refs)
        if info.properties:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        return BoundaryClassification.ASSUMED
