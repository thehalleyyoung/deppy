"""deppy.library_theories package.

Provides the theory pack system for sheaf-descent semantic typing.
Each theory pack encapsulates domain-specific logic for one or more
site families, implementing local solvers, forward refinement,
backward pullback, viability predicates, and proof-boundary classification.

Theory families:
  1.  ArithmeticTheoryPack       - integer/float interval arithmetic
  2.  BooleanGuardTheoryPack     - branch guard analysis
  3.  NullabilityTheoryPack      - None/Optional tracking
  4.  HeapProtocolTheoryPack     - protocol conformance & field state
  5.  TensorShapeTheoryPack      - tensor shape propagation
  6.  TensorOrderTheoryPack      - tensor ordering properties
  7.  TensorIndexingTheoryPack   - tensor index bounds
  8.  DeviceDtypeTheoryPack      - device/dtype compatibility
  9.  SequenceCollectionTheoryPack - collection length & membership
  10. ExceptionTheoryPack        - exception flow tracking
  11. WitnessTransportTheoryPack - proof obligation & transport
  12. LoopInvariantTheoryPack    - loop invariant & ranking functions

Subpackages:
  - pytorch: PyTorch-specific theory packs
  - builtin: Python built-in type theory packs
"""

# Infrastructure
from .theory_pack_base import (
    BoundaryClassification,
    SolverResult,
    SolverStatus,
    TheoryPackBase,
    make_section,
    merge_refinements,
    narrow_section,
    widen_section,
    replace_carrier,
    upgrade_trust,
    section_with_witness,
    sections_compatible,
    make_error_site_id,
    make_guard_site_id,
)

from .pack_registry import (
    PackRegistryImpl,
    ComposedPack,
    get_default_registry,
    reset_default_registry,
)

from .pack_composer import (
    CompositionStrategy,
    CompositionConflict,
    CompositionReport,
    PackComposer,
)

# Theory families
from .arithmetic_theory import ArithmeticTheoryPack
from .boolean_guard_theory import BooleanGuardTheoryPack
from .nullability_theory import NullabilityTheoryPack
from .heap_protocol_theory import HeapProtocolTheoryPack
from .tensor_shape_theory import TensorShapeTheoryPack
from .tensor_order_theory import TensorOrderTheoryPack
from .tensor_indexing_theory import TensorIndexingTheoryPack
from .device_dtype_theory import DeviceDtypeTheoryPack
from .sequence_collection_theory import SequenceCollectionTheoryPack
from .exception_theory import ExceptionTheoryPack
from .witness_transport_theory import WitnessTransportTheoryPack
from .loop_invariant_theory import LoopInvariantTheoryPack

__all__ = [
    # Infrastructure
    "BoundaryClassification",
    "SolverResult",
    "SolverStatus",
    "TheoryPackBase",
    "make_section",
    "merge_refinements",
    "narrow_section",
    "widen_section",
    "replace_carrier",
    "upgrade_trust",
    "section_with_witness",
    "sections_compatible",
    "make_error_site_id",
    "make_guard_site_id",
    "PackRegistryImpl",
    "ComposedPack",
    "get_default_registry",
    "reset_default_registry",
    "CompositionStrategy",
    "CompositionConflict",
    "CompositionReport",
    "PackComposer",
    # Theory families
    "ArithmeticTheoryPack",
    "BooleanGuardTheoryPack",
    "NullabilityTheoryPack",
    "HeapProtocolTheoryPack",
    "TensorShapeTheoryPack",
    "TensorOrderTheoryPack",
    "TensorIndexingTheoryPack",
    "DeviceDtypeTheoryPack",
    "SequenceCollectionTheoryPack",
    "ExceptionTheoryPack",
    "WitnessTransportTheoryPack",
    "LoopInvariantTheoryPack",
]
