"""
End-to-end PyTorch equivalence pipeline.

Provides the top-level API:
  check_torch_equivalence(fn_f, fn_g, tensor_specs, ...)
  check_triton_equivalence(kernel_f, kernel_g, ...)
  check_mlir_equivalence(module_f, module_g, ...)

Orchestrates the full sheaf-theoretic pipeline:
  presheaf construction → local checking → descent → cohomology → verdict
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

from ._protocols import (
    EquivalenceVerdict,
    TensorEquivalenceConfig,
    TensorGlobalJudgment,
    TensorLocalJudgment,
    TensorObstruction,
    TensorSiteKind,
    TensorSpec,
    TensorStratum,
    TritonKernelSpec,
    MLIRModuleSpec,
    NumericalToleranceSpec,
)

from .tensor_site import generate_test_inputs
from .tensor_presheaf import TensorPresheafBuilder, check_presheaf_naturality
from .torch_global_checker import TorchGlobalChecker
from .triton_ir import build_kernel_spec
from .triton_mlir import build_mlir_module_spec

try:
    import torch
    _HAS_TORCH = True
except ImportError:
    _HAS_TORCH = False


# ---------------------------------------------------------------------------
# Default config factory
# ---------------------------------------------------------------------------

def default_config(**overrides: Any) -> TensorEquivalenceConfig:
    """Create a TensorEquivalenceConfig with sensible defaults."""
    kwargs = dict(
        tolerance=NumericalToleranceSpec(),
        check_shape=True,
        check_dtype=True,
        check_device=True,
        check_stride=False,
        check_numerical=True,
        check_autograd=True,
        check_memory_aliasing=False,
        check_triton_ir=False,
        check_triton_memory=False,
        check_triton_reductions=False,
        check_mlir_ops=False,
        check_mlir_lowering=False,
        use_solver=False,
        max_test_inputs=100,
        short_circuit_strata=True,
        test_shapes=((4,), (4, 4), (2, 3, 4)),
        test_dtypes=("float32",),
        test_devices=("cpu",),
    )
    # Map convenience overrides to actual config fields
    if "check_triton" in overrides:
        val = overrides.pop("check_triton")
        kwargs["check_triton_ir"] = val
        kwargs["check_triton_memory"] = val
        kwargs["check_triton_reductions"] = val
    if "check_mlir" in overrides:
        val = overrides.pop("check_mlir")
        kwargs["check_mlir_ops"] = val
        kwargs["check_mlir_lowering"] = val
    kwargs.update(overrides)
    return TensorEquivalenceConfig(**kwargs)


# ---------------------------------------------------------------------------
# Main API
# ---------------------------------------------------------------------------

def check_torch_equivalence(
    fn_f: Callable,
    fn_g: Callable,
    tensor_specs: Optional[Sequence[TensorSpec]] = None,
    test_inputs: Optional[Sequence[Sequence[Any]]] = None,
    config: Optional[TensorEquivalenceConfig] = None,
    triton_source_f: Optional[str] = None,
    triton_source_g: Optional[str] = None,
    mlir_text_f: Optional[str] = None,
    mlir_text_g: Optional[str] = None,
) -> TensorGlobalJudgment:
    """
    Check equivalence of two PyTorch functions.

    This is the main entry point for the tensor equivalence checker.

    Parameters
    ----------
    fn_f, fn_g : Callable
        The two PyTorch functions to compare.
    tensor_specs : sequence of TensorSpec, optional
        Specifications of the input tensors (shapes, dtypes, devices).
        If not provided, default specs are generated.
    test_inputs : sequence of input tuples, optional
        Concrete test inputs.  If not provided, generated from tensor_specs.
    config : TensorEquivalenceConfig, optional
        Configuration for the checker.
    triton_source_f, triton_source_g : str, optional
        Triton kernel source code for each function.
    mlir_text_f, mlir_text_g : str, optional
        MLIR assembly text for each function.

    Returns
    -------
    TensorGlobalJudgment
        The global equivalence judgment with full sheaf-theoretic analysis.
    """
    if config is None:
        config = default_config(
            check_triton=triton_source_f is not None,
            check_mlir=mlir_text_f is not None,
        )

    # Default tensor specs
    if tensor_specs is None:
        tensor_specs = _default_tensor_specs(fn_f, config)

    # Generate test inputs if needed
    if test_inputs is None:
        test_inputs = list(generate_test_inputs(
            tensor_specs,
            n_random=config.max_test_inputs,
        ))

    # Build Triton specs
    triton_f = None
    triton_g = None
    if triton_source_f and triton_source_g:
        triton_f = build_kernel_spec(triton_source_f, name="kernel_f")
        triton_g = build_kernel_spec(triton_source_g, name="kernel_g")

    # Build MLIR specs
    mlir_f = None
    mlir_g = None
    if mlir_text_f and mlir_text_g:
        mlir_f = build_mlir_module_spec(mlir_text_f, name="module_f")
        mlir_g = build_mlir_module_spec(mlir_text_g, name="module_g")

    # Run global checker
    checker = TorchGlobalChecker(config)
    return checker.check(
        fn_f, fn_g, tensor_specs, test_inputs,
        triton_f, triton_g,
        mlir_f, mlir_g,
    )


def check_triton_equivalence(
    source_f: str,
    source_g: str,
    config: Optional[TensorEquivalenceConfig] = None,
    grid_f: Optional[Tuple] = None,
    grid_g: Optional[Tuple] = None,
    num_warps_f: int = 4,
    num_warps_g: int = 4,
) -> TensorGlobalJudgment:
    """
    Check equivalence of two Triton kernels (source-level).

    Compares kernels at the structural level via AST analysis.
    Does not execute the kernels.
    """
    if config is None:
        config = default_config(check_triton=True)

    triton_f = build_kernel_spec(source_f, name="kernel_f",
                                 grid=grid_f, num_warps=num_warps_f)
    triton_g = build_kernel_spec(source_g, name="kernel_g",
                                 grid=grid_g, num_warps=num_warps_g)

    # Create dummy functions for the pipeline
    def _dummy_f(*args: Any) -> Any:
        return args[0] if args else None

    def _dummy_g(*args: Any) -> Any:
        return args[0] if args else None

    _dummy_f.__name__ = triton_f.name
    _dummy_g.__name__ = triton_g.name

    checker = TorchGlobalChecker(config)
    return checker.check(
        _dummy_f, _dummy_g,
        tensor_specs=[TensorSpec(shape=(1024,), dtype="float32", device="cpu")],
        test_inputs=None,
        triton_spec_f=triton_f,
        triton_spec_g=triton_g,
    )


def check_mlir_equivalence(
    text_f: str,
    text_g: str,
    config: Optional[TensorEquivalenceConfig] = None,
) -> TensorGlobalJudgment:
    """
    Check equivalence of two MLIR modules.

    Compares modules at the dialect operation level.
    """
    if config is None:
        config = default_config(check_mlir=True)

    mlir_f = build_mlir_module_spec(text_f, name="module_f")
    mlir_g = build_mlir_module_spec(text_g, name="module_g")

    def _dummy_f(*args: Any) -> Any:
        return args[0] if args else None

    def _dummy_g(*args: Any) -> Any:
        return args[0] if args else None

    _dummy_f.__name__ = mlir_f.name
    _dummy_g.__name__ = mlir_g.name

    checker = TorchGlobalChecker(config)
    return checker.check(
        _dummy_f, _dummy_g,
        tensor_specs=[TensorSpec(shape=(1,), dtype="float32", device="cpu")],
        test_inputs=None,
        mlir_spec_f=mlir_f,
        mlir_spec_g=mlir_g,
    )


# ---------------------------------------------------------------------------
# Presheaf-level comparison API
# ---------------------------------------------------------------------------

def check_presheaf_equivalence(
    fn_f: Callable,
    fn_g: Callable,
    tensor_specs: Optional[Sequence[TensorSpec]] = None,
    test_inputs: Optional[Sequence[Sequence[Any]]] = None,
    config: Optional[TensorEquivalenceConfig] = None,
) -> Dict[str, Any]:
    """
    Check equivalence at the presheaf level (without full global checking).

    Builds tensor presheaves for both functions and checks for a
    natural isomorphism.  This is a lighter-weight check that focuses
    on the categorical structure.
    """
    if config is None:
        config = default_config()

    if tensor_specs is None:
        tensor_specs = _default_tensor_specs(fn_f, config)

    builder = TensorPresheafBuilder(config)

    inputs = test_inputs[0] if test_inputs else None
    pf = builder.build(fn_f, example_inputs=inputs, tensor_specs=tensor_specs)
    pg = builder.build(fn_g, example_inputs=inputs, tensor_specs=tensor_specs)

    morphism = check_presheaf_naturality(pf, pg)

    return {
        "source": pf.fn_name,
        "target": pg.fn_name,
        "is_isomorphism": morphism.is_isomorphism,
        "is_natural": morphism.is_natural,
        "components": morphism.components,
    }


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _default_tensor_specs(fn: Callable,
                          config: TensorEquivalenceConfig) -> List[TensorSpec]:
    """Generate default tensor specs from function signature."""
    import inspect
    try:
        sig = inspect.signature(fn)
        n_params = len([
            p for p in sig.parameters.values()
            if p.default is inspect.Parameter.empty
        ])
    except (ValueError, TypeError):
        n_params = 1

    n_params = max(1, n_params)
    default_shape = config.test_shapes[1] if len(config.test_shapes) > 1 else (4, 4)
    default_dtype = config.test_dtypes[0] if config.test_dtypes else "float32"
    default_device = config.test_devices[0] if config.test_devices else "cpu"

    return [
        TensorSpec(
            shape=default_shape,
            dtype=default_dtype,
            device=default_device,
        )
        for _ in range(n_params)
    ]


# ---------------------------------------------------------------------------
# Single-program analysis API (general, not equivalence-specific)
# ---------------------------------------------------------------------------

def analyze_torch(
    fn: Callable,
    tensor_specs: Optional[Sequence[TensorSpec]] = None,
    test_inputs: Optional[Sequence[Sequence[Any]]] = None,
    config: Optional[TensorEquivalenceConfig] = None,
    triton_source: Optional[str] = None,
    mlir_text: Optional[str] = None,
) -> Any:
    """
    Analyze a single PyTorch function for bugs.

    Single-program counterpart to check_torch_equivalence().
    Checks if the function's tensor presheaf satisfies the sheaf
    condition — i.e., are observable behaviors internally consistent?

    Returns an AnalysisJudgment with bugs found.
    """
    from ._protocols import AnalysisMode
    if config is None:
        config = default_config(
            check_triton=triton_source is not None,
            check_mlir=mlir_text is not None,
        )

    if tensor_specs is None:
        tensor_specs = _default_tensor_specs(fn, config)

    triton_spec = None
    if triton_source:
        triton_spec = build_kernel_spec(triton_source, name="kernel")

    mlir_spec = None
    if mlir_text:
        mlir_spec = build_mlir_module_spec(mlir_text, name="module")

    checker = TorchGlobalChecker(config)
    return checker.analyze(fn, tensor_specs, test_inputs, triton_spec, mlir_spec)


def analyze_triton(
    source: str,
    name: str = "",
    grid: Optional[Tuple] = None,
    config: Optional[TensorEquivalenceConfig] = None,
) -> Any:
    """
    Analyze a single Triton kernel for bugs.

    Checks for unmasked boundary accesses, non-associative reductions,
    invalid block configurations, and structural issues.
    """
    from ._protocols import (
        AnalysisMode, AnalysisVerdict, AnalysisJudgment, BugKind, Bug,
        ProgramId, SiteId, SiteKind,
    )

    spec = build_kernel_spec(source, name=name, grid=grid)
    program = ProgramId(name=name or spec.name)
    bugs: List[Any] = []

    # Check for unmasked memory accesses
    for ma in spec.memory_accesses:
        if ma.mask_expr is None:
            bugs.append(Bug(
                kind=BugKind.UNMASKED_ACCESS,
                stratum=TensorStratum.STRUCTURAL,
                site_id=SiteId(kind=SiteKind.TENSOR_SHAPE,
                               name=f"triton_mem_{ma.pointer_name}"),
                description=(
                    f"Memory access to '{ma.pointer_name}' has no mask — "
                    "may cause out-of-bounds access at block boundaries"
                ),
                repair_hint="Add mask=offsets < n_elements to the load/store",
            ))

    # Check for non-associative reductions
    NON_ASSOC_OPS = {"sub", "div", "truediv", "floordiv"}
    for red in spec.reductions:
        if red.op in NON_ASSOC_OPS:
            bugs.append(Bug(
                kind=BugKind.REDUCTION_ORDER,
                stratum=TensorStratum.NUMERICAL,
                site_id=SiteId(kind=SiteKind.TENSOR_SHAPE,
                               name=f"triton_red_{red.op}"),
                description=(
                    f"Reduction '{red.op}' on axis {red.axis} is not associative — "
                    "parallel execution may produce non-deterministic results"
                ),
            ))

    verdict = AnalysisVerdict.INVALID if bugs else AnalysisVerdict.VALID
    return AnalysisJudgment(
        verdict=verdict,
        program=program,
        mode=AnalysisMode.BUG_FINDING,
        bugs=bugs,
        explanation=(f"Found {len(bugs)} issue(s) in Triton kernel {name}"
                     if bugs else f"No issues found in Triton kernel {name}"),
    )


def analyze_mlir(
    text: str,
    name: str = "",
    config: Optional[TensorEquivalenceConfig] = None,
) -> Any:
    """
    Analyze a single MLIR module for validity issues.

    Checks for valid lowering chain, well-formed operations.
    """
    from ._protocols import (
        AnalysisMode, AnalysisVerdict, AnalysisJudgment, BugKind, Bug,
        ProgramId, SiteId, SiteKind,
    )

    spec = build_mlir_module_spec(text, name=name)
    program = ProgramId(name=name or spec.name)
    bugs: List[Any] = []

    # Check lowering chain validity
    if spec.lowering_chain:
        for i in range(len(spec.lowering_chain) - 1):
            step_a = spec.lowering_chain[i]
            step_b = spec.lowering_chain[i + 1]
            if hasattr(step_a, 'target') and hasattr(step_b, 'source'):
                if step_a.target != step_b.source:
                    bugs.append(Bug(
                        kind=BugKind.INVALID_LOWERING,
                        stratum=TensorStratum.BEHAVIORAL,
                        site_id=SiteId(kind=SiteKind.TENSOR_SHAPE,
                                       name=f"mlir_lowering_{i}"),
                        description=(
                            f"Lowering chain gap at step {i}: "
                            f"target of step {i} doesn't match source of step {i+1}"
                        ),
                    ))

    # Check for empty module
    if not spec.dialect_ops:
        bugs.append(Bug(
            kind=BugKind.INVALID_LOWERING,
            stratum=TensorStratum.BEHAVIORAL,
            site_id=SiteId(kind=SiteKind.TENSOR_SHAPE, name="mlir_empty"),
            description="MLIR module has no dialect operations",
        ))

    verdict = AnalysisVerdict.INVALID if bugs else AnalysisVerdict.VALID
    return AnalysisJudgment(
        verdict=verdict,
        program=program,
        mode=AnalysisMode.BUG_FINDING,
        bugs=bugs,
        explanation=(f"Found {len(bugs)} issue(s) in MLIR module {name}"
                     if bugs else f"No issues found in MLIR module {name}"),
    )


def check_correctness(
    fn: Callable,
    spec: Any,
    tensor_specs: Optional[Sequence[TensorSpec]] = None,
    test_inputs: Optional[Sequence[Sequence[Any]]] = None,
    config: Optional[TensorEquivalenceConfig] = None,
) -> Any:
    """
    Check if a function conforms to a specification presheaf.

    Mathematically, this checks for existence of a morphism
    η: Spec → Sem_fn from the specification to the implementation.
    """
    from .specification import SpecificationChecker
    if config is None:
        config = default_config()
    if tensor_specs is None:
        tensor_specs = _default_tensor_specs(fn, config)
    checker = SpecificationChecker(config)
    return checker.check(fn, spec, tensor_specs, test_inputs)
