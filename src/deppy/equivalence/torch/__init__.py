"""
deppy.equivalence.torch — Sheaf-theoretic equivalence checker for PyTorch,
Triton GPU kernels, and Triton-MLIR lowerings.

Extends the base equivalence checker with tensor-specific observation sites
organized into a canonical filtration:

  METADATA (dtype, device)  ≤  STRUCTURAL (shape, stride)
          ≤  NUMERICAL (values)  ≤  BEHAVIORAL (autograd)

Two PyTorch functions are equivalent iff their tensor presheaves are
naturally isomorphic across all strata.

Main API
--------
check_torch_equivalence(fn_f, fn_g, ...)
    Full equivalence check of two PyTorch functions.

check_triton_equivalence(source_f, source_g, ...)
    Structural equivalence of two Triton GPU kernels.

check_mlir_equivalence(text_f, text_g, ...)
    Dialect-level equivalence of two MLIR modules.

check_presheaf_equivalence(fn_f, fn_g, ...)
    Lightweight presheaf-level comparison.
"""

from ._protocols import (
    # Enums
    EquivalenceVerdict,
    EquivalenceStrength,
    MLIRDialect,
    TensorMorphismKind,
    TensorObstructionKind,
    TensorSiteKind,
    TensorStratum,
    # General analysis enums
    AnalysisMode,
    AnalysisVerdict,
    BugKind,
    # Data classes
    MLIRLoweringStep,
    MLIRModuleSpec,
    MLIROpSpec,
    NumericalToleranceSpec,
    TensorCohomologyClass,
    TensorDescentDatum,
    TensorEquivalenceConfig,
    TensorGlobalJudgment,
    TensorLocalJudgment,
    TensorObstruction,
    TensorPair,
    TensorSignature,
    TensorSiteCategory,
    TensorSiteMorphism,
    TensorSpec,
    TritonBlockSpec,
    TritonKernelSpec,
    TritonMemoryAccessPattern,
    TritonReductionSpec,
    # General analysis data classes
    Bug,
    SheafConditionResult,
    SpecificationSection,
    SpecificationPresheaf,
    AnalysisJudgment,
    CorrectnessJudgment,
    # Constants
    SITE_KIND_STRATUM,
    SiteId,
)

from .tensor_site import (
    TensorObservationSite,
    TensorCover,
    TensorSiteCategoryBuilder,
    CechSimplex,
    cech_nerve,
    common_refinement,
    filtration_covers,
    generate_test_input,
    generate_test_inputs,
)

from .numerical_equiv import NumericalEquivalenceChecker
from .shape_equiv import ShapeEquivalenceChecker
from .dtype_equiv import DtypeEquivalenceChecker
from .memory_equiv import MemoryEquivalenceChecker
from .autograd_equiv import AutogradEquivalenceChecker
from .dispatch_equiv import DispatchEquivalenceChecker

from .triton_ir import (
    TritonASTParser,
    TritonKernelAST,
    TilingTopology,
    KernelFingerprint,
    build_kernel_spec,
    compute_fingerprint,
    fingerprints_compatible,
    tiling_topologies_equivalent,
)

from .triton_equiv import (
    TritonStructuralChecker,
    TritonEquivalenceChecker,
    KernelComparisonResult,
    compare_memory_patterns,
)

from .triton_mlir import (
    MLIRTextParser,
    MLIRModule,
    MLIROperation,
    MLIRFunction,
    MLIREquivalenceChecker,
    build_mlir_module_spec,
    compute_mlir_fingerprint,
)

from .tensor_presheaf import (
    TensorSection,
    TensorPresheaf,
    TensorPresheafBuilder,
    PresheafMorphism,
    FXGraphSummary,
    trace_function,
    check_presheaf_naturality,
)

from .torch_local_checker import TorchLocalChecker, LocalCheckResult, AnalysisLocalResult
from .torch_global_checker import TorchGlobalChecker
from .torch_pipeline import (
    check_torch_equivalence,
    check_triton_equivalence,
    check_mlir_equivalence,
    check_presheaf_equivalence,
    default_config,
    # General analysis API
    analyze_torch,
    analyze_triton,
    analyze_mlir,
    check_correctness,
)

from .sheaf_condition import (
    TensorSheafConditionChecker,
    SectionConsistencyChecker,
    GluingChecker,
    DescentChecker,
)

from .specification import (
    SpecBuilder,
    SpecificationChecker,
    numerical_stability_spec,
    differentiability_spec,
    shape_preservation_spec,
    dtype_preservation_spec,
    triton_safety_spec,
    mlir_validity_spec,
)

from .base_bridge import (
    detect_python_bugs,
    compute_cohomology_via_base,
    verify_descent_via_base,
)

from .triton_counterexample import (
    CounterexampleSynthesizer,
    CounterexampleReport,
    EdgeCaseCounterexample,
    EdgeCaseCategory,
    InputStratum,
)

__all__ = [
    # Pipeline API — equivalence
    "check_torch_equivalence",
    "check_triton_equivalence",
    "check_mlir_equivalence",
    "check_presheaf_equivalence",
    "default_config",
    # Pipeline API — general analysis
    "analyze_torch",
    "analyze_triton",
    "analyze_mlir",
    "check_correctness",
    # Checkers — equivalence
    "TorchGlobalChecker",
    "TorchLocalChecker",
    "NumericalEquivalenceChecker",
    "ShapeEquivalenceChecker",
    "DtypeEquivalenceChecker",
    "MemoryEquivalenceChecker",
    "AutogradEquivalenceChecker",
    "DispatchEquivalenceChecker",
    "TritonEquivalenceChecker",
    "TritonStructuralChecker",
    "MLIREquivalenceChecker",
    # Checkers — general analysis
    "TensorSheafConditionChecker",
    "SectionConsistencyChecker",
    "GluingChecker",
    "DescentChecker",
    # Specification
    "SpecBuilder",
    "SpecificationChecker",
    "numerical_stability_spec",
    "differentiability_spec",
    "shape_preservation_spec",
    "dtype_preservation_spec",
    "triton_safety_spec",
    "mlir_validity_spec",
    # Presheaf
    "TensorPresheaf",
    "TensorPresheafBuilder",
    "TensorSection",
    "PresheafMorphism",
    "FXGraphSummary",
    "trace_function",
    "check_presheaf_naturality",
    # Site category
    "TensorObservationSite",
    "TensorCover",
    "TensorSiteCategoryBuilder",
    "CechSimplex",
    "cech_nerve",
    "common_refinement",
    "filtration_covers",
    "generate_test_input",
    "generate_test_inputs",
    # Triton IR
    "TritonASTParser",
    "TritonKernelAST",
    "TilingTopology",
    "KernelFingerprint",
    "build_kernel_spec",
    "compute_fingerprint",
    "fingerprints_compatible",
    "tiling_topologies_equivalent",
    "KernelComparisonResult",
    "compare_memory_patterns",
    # MLIR
    "MLIRTextParser",
    "MLIRModule",
    "MLIROperation",
    "MLIRFunction",
    "build_mlir_module_spec",
    "compute_mlir_fingerprint",
    # Protocols / types — equivalence
    "EquivalenceVerdict",
    "EquivalenceStrength",
    "MLIRDialect",
    "TensorMorphismKind",
    "TensorObstructionKind",
    "TensorSiteKind",
    "TensorStratum",
    "MLIRLoweringStep",
    "MLIRModuleSpec",
    "MLIROpSpec",
    "NumericalToleranceSpec",
    "TensorCohomologyClass",
    "TensorDescentDatum",
    "TensorEquivalenceConfig",
    "TensorGlobalJudgment",
    "TensorLocalJudgment",
    "TensorObstruction",
    "TensorPair",
    "TensorSignature",
    "TensorSiteCategory",
    "TensorSiteMorphism",
    "TensorSpec",
    "TritonBlockSpec",
    "TritonKernelSpec",
    "TritonMemoryAccessPattern",
    "TritonReductionSpec",
    "SITE_KIND_STRATUM",
    "SiteId",
    "LocalCheckResult",
    "AnalysisLocalResult",
    # Protocols / types — general analysis
    "AnalysisMode",
    "AnalysisVerdict",
    "BugKind",
    "Bug",
    "SheafConditionResult",
    "SpecificationSection",
    "SpecificationPresheaf",
    "AnalysisJudgment",
    "CorrectnessJudgment",
    # Base framework bridge
    "detect_python_bugs",
    "compute_cohomology_via_base",
    "verify_descent_via_base",
    # Counterexample synthesis
    "CounterexampleSynthesizer",
    "CounterexampleReport",
    "EdgeCaseCounterexample",
    "EdgeCaseCategory",
    "InputStratum",
]
