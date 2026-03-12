"""DepPy harvest package -- semantic hint extraction from Python AST.

This package provides harvesters that walk Python ASTs and extract local
semantic hints: guard predicates, type narrowings, None-check patterns,
arithmetic bounds, collection facts, tensor shape/dtype/device annotations,
exception-guarded regions, and protocol conformance evidence.

Sub-modules
-----------
- **guard_harvester**: Extract guards from if/assert/try/walrus.
- **type_guard_harvester**: isinstance/issubclass/hasattr/callable narrowing.
- **none_guard_harvester**: None-check pattern extraction.
- **arithmetic_harvester**: Arithmetic bound extraction from comparisons.
- **collection_harvester**: Length/membership/emptiness extraction.
- **tensor_harvester**: Shape/rank/dtype/device hints from torch calls.
- **exception_harvester**: Exception-guarded regions.
- **protocol_harvester**: Protocol conformance hints from usage patterns.
- **aggregator**: Merge all harvested predicates per site.
"""

from __future__ import annotations

# -- guard harvester -------------------------------------------------------
from deppy.harvest.guard_harvester import (
    GuardHarvester,
    GuardKind,
    HarvestedGuard,
    deduplicate_guards,
    filter_guards_by_function,
    filter_guards_by_kind,
    filter_guards_by_variable,
    harvest_guards,
    partition_by_polarity,
)

# -- type guard harvester --------------------------------------------------
from deppy.harvest.type_guard_harvester import (
    NarrowingKind,
    TypeGuardHarvester,
    TypeNarrowingFact,
    collect_narrowed_types,
    filter_by_kind as filter_type_narrowings_by_kind,
    filter_by_variable as filter_type_narrowings_by_variable,
    harvest_type_guards,
    narrowings_for_function,
    negative_narrowings,
    positive_narrowings,
)

# -- none guard harvester --------------------------------------------------
from deppy.harvest.none_guard_harvester import (
    NoneCheckKind,
    NoneGuard,
    NoneGuardHarvester,
    collect_guarded_variables,
    filter_is_none,
    filter_is_not_none,
    has_none_guard,
    harvest_none_guards,
)

# -- arithmetic harvester --------------------------------------------------
from deppy.harvest.arithmetic_harvester import (
    ArithmeticBound,
    ArithmeticHarvester,
    BoundOrigin,
    BoundType,
    exact_bounds,
    harvest_arithmetic_bounds,
    len_bounds,
    lower_bounds,
    range_bounds,
    to_int_range,
    upper_bounds,
)

# -- collection harvester --------------------------------------------------
from deppy.harvest.collection_harvester import (
    CollectionFact,
    CollectionFactKind,
    CollectionHarvester,
    FactOrigin,
    empty_collections,
    harvest_collection_facts,
    membership_facts,
    non_empty_collections,
)

# -- tensor harvester ------------------------------------------------------
from deppy.harvest.tensor_harvester import (
    TensorFact,
    TensorFactKind,
    TensorFactOrigin,
    TensorHarvester,
    device_facts,
    dtype_facts,
    harvest_tensor_facts,
    shape_facts,
)

# -- exception harvester ---------------------------------------------------
from deppy.harvest.exception_harvester import (
    ExceptionHarvester,
    ExceptionRegion,
    HandlerAction,
    RegionKind,
    bare_except_regions,
    harvest_exception_regions,
    regions_guarding_call,
    suppressing_regions,
)

# -- protocol harvester ----------------------------------------------------
from deppy.harvest.protocol_harvester import (
    ProtocolHarvester,
    ProtocolHint,
    ProtocolKind,
    deduplicate_hints,
    filter_hints_by_confidence,
    filter_hints_by_function,
    filter_hints_by_variable,
    harvest_protocols,
    hints_to_predicates,
)

# -- aggregator ------------------------------------------------------------
from deppy.harvest.aggregator import (
    HarvestResult,
    VariableHarvest,
    aggregate_harvests,
    apply_harvest_to_cover,
    harvest_all,
)

__all__ = [
    # guard harvester
    "GuardHarvester",
    "GuardKind",
    "HarvestedGuard",
    "deduplicate_guards",
    "filter_guards_by_function",
    "filter_guards_by_kind",
    "filter_guards_by_variable",
    "harvest_guards",
    "partition_by_polarity",
    # type guard harvester
    "NarrowingKind",
    "TypeGuardHarvester",
    "TypeNarrowingFact",
    "collect_narrowed_types",
    "harvest_type_guards",
    "narrowings_for_function",
    "negative_narrowings",
    "positive_narrowings",
    # none guard harvester
    "NoneCheckKind",
    "NoneGuard",
    "NoneGuardHarvester",
    "collect_guarded_variables",
    "filter_is_none",
    "filter_is_not_none",
    "has_none_guard",
    "harvest_none_guards",
    # arithmetic harvester
    "ArithmeticBound",
    "ArithmeticHarvester",
    "BoundOrigin",
    "BoundType",
    "exact_bounds",
    "harvest_arithmetic_bounds",
    "len_bounds",
    "lower_bounds",
    "range_bounds",
    "to_int_range",
    "upper_bounds",
    # collection harvester
    "CollectionFact",
    "CollectionFactKind",
    "CollectionHarvester",
    "FactOrigin",
    "empty_collections",
    "harvest_collection_facts",
    "membership_facts",
    "non_empty_collections",
    # tensor harvester
    "TensorFact",
    "TensorFactKind",
    "TensorFactOrigin",
    "TensorHarvester",
    "device_facts",
    "dtype_facts",
    "harvest_tensor_facts",
    "shape_facts",
    # exception harvester
    "ExceptionHarvester",
    "ExceptionRegion",
    "HandlerAction",
    "RegionKind",
    "bare_except_regions",
    "harvest_exception_regions",
    "regions_guarding_call",
    "suppressing_regions",
    # protocol harvester
    "ProtocolHarvester",
    "ProtocolHint",
    "ProtocolKind",
    "deduplicate_hints",
    "filter_hints_by_confidence",
    "filter_hints_by_function",
    "filter_hints_by_variable",
    "harvest_protocols",
    "hints_to_predicates",
    # aggregator
    "HarvestResult",
    "VariableHarvest",
    "aggregate_harvests",
    "apply_harvest_to_cover",
    "harvest_all",
]
