"""
General analysis pipeline for tensor programs.

Supports all analysis modes — bug-finding, correctness, refinement,
and equivalence — providing a unified API that dispatches to the
specialised checkers (sheaf condition, specification, global equivalence).

This is the single-program counterpart to ``torch_pipeline.py`` (which
only handles two-program equivalence).  The architecture is:

- **Bug-finding** uses domain-checker ``.analyze()`` methods and the
  sheaf-condition checker to detect internal inconsistencies.
- **Correctness** uses :class:`SpecificationChecker` to verify a morphism
  η : Spec → Sem_f.
- **Equivalence** delegates to :func:`check_torch_equivalence`.
- **Refinement** checks one-way behavioural inclusion via the existing
  equivalence pipeline with verdict reinterpretation.

Main API
--------
analyze(fn, mode, ...)
    Unified dispatch — the single entry point for all modes.

analyze_torch(fn, ...)
    Single PyTorch function analysis (bug-finding).

analyze_triton(source, ...)
    Single Triton kernel analysis.

analyze_mlir(text, ...)
    Single MLIR module analysis.

check_correctness(fn, spec, ...)
    Specification conformance checking.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

from ._protocols import (
    AnalysisMode,
    AnalysisVerdict,
    BugKind,
    Bug,
    SheafConditionResult,
    SpecificationPresheaf,
    AnalysisJudgment,
    CorrectnessJudgment,
    ProgramId,
    EquivalenceVerdict,
    TensorEquivalenceConfig,
    TensorGlobalJudgment,
    TensorSpec,
    TensorStratum,
    TritonKernelSpec,
    MLIRModuleSpec,
    NumericalToleranceSpec,
    SiteId,
    SiteKind,
)
from .tensor_site import generate_test_inputs
from .triton_ir import build_kernel_spec
from .triton_mlir import build_mlir_module_spec
from .base_bridge import detect_python_bugs

try:
    import torch
    _HAS_TORCH = True
except ImportError:
    _HAS_TORCH = False


# ---------------------------------------------------------------------------
# Lazy imports for modules that may be created concurrently
# ---------------------------------------------------------------------------

def _get_sheaf_checker():
    """Lazily import TensorSheafConditionChecker (sheaf_condition.py)."""
    from .sheaf_condition import TensorSheafConditionChecker
    return TensorSheafConditionChecker


def _get_spec_checker():
    """Lazily import SpecificationChecker (specification.py)."""
    from .specification import SpecificationChecker
    return SpecificationChecker


def _get_global_checker():
    """Lazily import TorchGlobalChecker."""
    from .torch_global_checker import TorchGlobalChecker
    return TorchGlobalChecker


def _get_domain_checkers():
    """Lazily import all domain-specific equivalence checkers."""
    from .numerical_equiv import NumericalEquivalenceChecker
    from .shape_equiv import ShapeEquivalenceChecker
    from .dtype_equiv import DtypeEquivalenceChecker
    from .memory_equiv import MemoryEquivalenceChecker
    from .autograd_equiv import AutogradEquivalenceChecker
    from .dispatch_equiv import DispatchEquivalenceChecker
    return {
        "numerical": NumericalEquivalenceChecker,
        "shape": ShapeEquivalenceChecker,
        "dtype": DtypeEquivalenceChecker,
        "memory": MemoryEquivalenceChecker,
        "autograd": AutogradEquivalenceChecker,
        "dispatch": DispatchEquivalenceChecker,
    }


# ---------------------------------------------------------------------------
# Filtration order (coarser strata checked first)
# ---------------------------------------------------------------------------

_STRATUM_ORDER: Tuple[TensorStratum, ...] = (
    TensorStratum.METADATA,
    TensorStratum.STRUCTURAL,
    TensorStratum.NUMERICAL,
    TensorStratum.BEHAVIORAL,
)


# ---------------------------------------------------------------------------
# Default config factory (analysis-aware)
# ---------------------------------------------------------------------------

def default_analysis_config(
    mode: AnalysisMode = AnalysisMode.BUG_FINDING,
    **overrides: Any,
) -> TensorEquivalenceConfig:
    """Create a :class:`TensorEquivalenceConfig` tuned for general analysis.

    Unlike :func:`torch_pipeline.default_config` which targets two-program
    equivalence, this factory adjusts defaults based on the *analysis mode*:

    - ``BUG_FINDING`` enables memory-aliasing checks and disables strata
      short-circuiting (we want *all* bugs, not just the first stratum).
    - ``EQUIVALENCE`` enables short-circuiting (early exit on shape mismatch).
    - ``CORRECTNESS`` behaves like bug-finding but with spec awareness.
    """
    kwargs: Dict[str, Any] = dict(
        analysis_mode=mode,
        tolerance=NumericalToleranceSpec(),
        check_shape=True,
        check_dtype=True,
        check_device=True,
        check_stride=False,
        check_numerical=True,
        check_autograd=True,
        check_memory_aliasing=mode == AnalysisMode.BUG_FINDING,
        check_triton_ir=False,
        check_triton_memory=False,
        check_triton_reductions=False,
        check_mlir_ops=False,
        check_mlir_lowering=False,
        max_test_inputs=50,
        short_circuit_strata=mode == AnalysisMode.EQUIVALENCE,
        test_shapes=((4,), (4, 4), (2, 3, 4)),
        test_dtypes=("float32",),
        test_devices=("cpu",),
    )

    # Convenience shortcuts
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
# Helpers
# ---------------------------------------------------------------------------

def _default_tensor_specs(
    fn: Callable,
    config: TensorEquivalenceConfig,
) -> List[TensorSpec]:
    """Generate default tensor specs from function signature.

    Mirrors the logic in ``torch_pipeline._default_tensor_specs``.
    """
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
    default_shape = (
        config.test_shapes[1]
        if len(config.test_shapes) > 1
        else (4, 4)
    )
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


def _make_program_id(fn: Any, fallback: str = "anonymous") -> ProgramId:
    """Build a ProgramId from a callable or string name."""
    if isinstance(fn, str):
        return ProgramId(name=fn)
    name = getattr(fn, "__name__", fallback)
    qualname = getattr(fn, "__qualname__", None)
    return ProgramId(name=name, function_name=qualname)


def _merge_bugs(
    *judgments: AnalysisJudgment,
) -> List[Bug]:
    """Collect bugs from multiple sub-judgments, deduplicating by identity."""
    seen: set = set()
    merged: List[Bug] = []
    for j in judgments:
        for bug in j.bugs:
            key = (bug.kind, bug.site_id, bug.description)
            if key not in seen:
                seen.add(key)
                merged.append(bug)
    return merged


def _verdict_from_bugs(bugs: List[Bug]) -> AnalysisVerdict:
    """Derive a top-level verdict from a bug list."""
    if not bugs:
        return AnalysisVerdict.VALID
    return AnalysisVerdict.INVALID


def _collect_stratum_results(
    bugs: List[Bug],
) -> Dict[TensorStratum, AnalysisVerdict]:
    """Build per-stratum verdict map from a flat bug list."""
    results: Dict[TensorStratum, AnalysisVerdict] = {}
    strata_with_bugs = {b.stratum for b in bugs}
    for s in _STRATUM_ORDER:
        if s in strata_with_bugs:
            results[s] = AnalysisVerdict.INVALID
        else:
            results[s] = AnalysisVerdict.VALID
    return results


# ---------------------------------------------------------------------------
# Domain-checker orchestration for single-program analysis
# ---------------------------------------------------------------------------

def _run_domain_checkers(
    fn: Callable,
    tensor_specs: Sequence[TensorSpec],
    test_inputs: List[List[Any]],
    config: TensorEquivalenceConfig,
) -> List[AnalysisJudgment]:
    """Run enabled domain checkers in filtration order.

    Returns a list of per-domain :class:`AnalysisJudgment` instances.
    If ``config.short_circuit_strata`` is *True*, stops at the first
    stratum that reports bugs.
    """
    checkers = _get_domain_checkers()
    sub_judgments: List[AnalysisJudgment] = []

    # Stratum → checker keys + call conventions
    stratum_plan: List[Tuple[TensorStratum, List[Tuple[str, bool]]]] = [
        (TensorStratum.METADATA, [
            ("dtype", config.check_dtype),
        ]),
        (TensorStratum.STRUCTURAL, [
            ("shape", config.check_shape),
        ]),
        (TensorStratum.NUMERICAL, [
            ("numerical", config.check_numerical),
        ]),
        (TensorStratum.BEHAVIORAL, [
            ("autograd", config.check_autograd),
            ("memory", config.check_memory_aliasing),
            ("dispatch", True),
        ]),
    ]

    for stratum, checker_flags in stratum_plan:
        stratum_bugs_found = False
        for key, enabled in checker_flags:
            if not enabled:
                continue
            cls = checkers.get(key)
            if cls is None:
                continue
            checker = cls()
            # Domain checkers have slightly different signatures:
            #   shape:  analyze(fn, input_specs, site_id)
            #   dtype:  analyze(fn, base_specs, site_id)
            #   others: analyze(fn, test_inputs, site_id)
            if key in ("shape", "dtype"):
                j = checker.analyze(fn, tensor_specs)
            else:
                j = checker.analyze(fn, test_inputs)
            sub_judgments.append(j)
            if j.bugs:
                stratum_bugs_found = True

        if stratum_bugs_found and config.short_circuit_strata:
            break

    return sub_judgments


# ═══════════════════════════════════════════════════════════════════════════════
# Main API: single-program analysis
# ═══════════════════════════════════════════════════════════════════════════════


def analyze_torch(
    fn: Callable,
    tensor_specs: Optional[Sequence[TensorSpec]] = None,
    test_inputs: Optional[Sequence[Sequence[Any]]] = None,
    config: Optional[TensorEquivalenceConfig] = None,
    triton_source: Optional[str] = None,
    mlir_text: Optional[str] = None,
) -> AnalysisJudgment:
    """Analyze a single PyTorch function for bugs and issues.

    This is the single-program counterpart to
    :func:`torch_pipeline.check_torch_equivalence`.  Instead of comparing two
    programs, it checks if a single program's presheaf satisfies the sheaf
    condition — i.e., are the program's observable behaviors (shape, dtype,
    numerical, autograd) internally consistent?

    Sheaf-theoretic interpretation
    ------------------------------
    A bug is a failure of the presheaf *F_fn* to satisfy the sheaf condition
    on the tensor site category.  Sections at different observation sites that
    should agree on overlaps (e.g., shape and numerical must be compatible)
    fail to glue.

    Parameters
    ----------
    fn : callable
        The PyTorch function to analyze.
    tensor_specs : sequence of TensorSpec, optional
        Specifications of each input tensor.  If *None*, defaults are
        inferred from the function signature.
    test_inputs : sequence of input-tuples, optional
        Concrete test inputs.  If *None*, synthesised from *tensor_specs*.
    config : TensorEquivalenceConfig, optional
        Analysis configuration.  If *None*, a bug-finding config is created.
    triton_source : str, optional
        Triton kernel source to include in the analysis.
    mlir_text : str, optional
        MLIR module text to include in the analysis.

    Returns
    -------
    AnalysisJudgment
    """
    if config is None:
        config = default_analysis_config(
            mode=AnalysisMode.BUG_FINDING,
            check_triton=triton_source is not None,
            check_mlir=mlir_text is not None,
        )

    if tensor_specs is None:
        tensor_specs = _default_tensor_specs(fn, config)

    if test_inputs is None:
        test_inputs = list(generate_test_inputs(
            tensor_specs,
            n_random=config.max_test_inputs,
        ))
    else:
        test_inputs = [list(inp) for inp in test_inputs]

    program = _make_program_id(fn)

    # 1. Sheaf-condition check (gluing + descent)
    SheafChecker = _get_sheaf_checker()
    sheaf_checker = SheafChecker()
    sheaf_result = sheaf_checker.check(fn, tensor_specs, test_inputs, config)

    # 2. Domain-checker bug finding
    domain_judgments = _run_domain_checkers(fn, tensor_specs, test_inputs, config)

    # 3. Triton-specific analysis (if source provided)
    triton_bugs: List[Bug] = []
    if triton_source and (config.check_triton_ir
                          or config.check_triton_memory
                          or config.check_triton_reductions):
        triton_judgment = analyze_triton(triton_source, config=config)
        triton_bugs = list(triton_judgment.bugs)

    # 4. MLIR-specific analysis (if text provided)
    mlir_bugs: List[Bug] = []
    if mlir_text and (config.check_mlir_ops or config.check_mlir_lowering):
        mlir_judgment = analyze_mlir(mlir_text, config=config)
        mlir_bugs = list(mlir_judgment.bugs)

    # 5. Sheaf-condition bugs (gluing/descent failures → Bug instances)
    sheaf_bugs: List[Bug] = []
    if not sheaf_result.satisfies_condition:
        for s_i, s_j in sheaf_result.gluing_failures:
            sheaf_bugs.append(Bug(
                kind=BugKind.SHEAF_GLUING_FAILURE,
                stratum=TensorStratum.NUMERICAL,
                site_id=s_i,
                description=(
                    f"Gluing failure: sections at {s_i} and {s_j} "
                    f"disagree on their overlap."
                ),
            ))
        for s_i, s_j, s_k in sheaf_result.descent_failures:
            sheaf_bugs.append(Bug(
                kind=BugKind.DESCENT_VIOLATION,
                stratum=TensorStratum.BEHAVIORAL,
                site_id=s_i,
                description=(
                    f"Descent/cocycle violation: triple overlap "
                    f"({s_i}, {s_j}, {s_k}) fails g_ij · g_jk = g_ik."
                ),
            ))

    # 6. Python-level bug detection via base sheaf bug detector.
    # Runs the full 6-phase pipeline from bug_detect.py: presheaf
    # construction → requirement extraction → section assignment →
    # guard recognition → obstruction resolution → Z3 discharge.
    # Catches Python bugs (div-zero, null-deref, key-error, data-race,
    # taint, etc.) that tensor-level analysis cannot see.
    python_bugs = detect_python_bugs(fn)

    # Merge all bugs
    all_bugs = (_merge_bugs(*domain_judgments)
                + sheaf_bugs + triton_bugs + mlir_bugs + python_bugs)
    verdict = _verdict_from_bugs(all_bugs)
    stratum_results = _collect_stratum_results(all_bugs)

    parts: List[str] = []
    if all_bugs:
        parts.append(f"{len(all_bugs)} bug(s) found")
    if not sheaf_result.satisfies_condition:
        parts.append("sheaf condition violated")
    explanation = (
        f"Analysis of '{program}': " + "; ".join(parts)
        if parts
        else f"Analysis of '{program}': no issues detected."
    )

    return AnalysisJudgment(
        verdict=verdict,
        program=program,
        mode=AnalysisMode.BUG_FINDING,
        bugs=all_bugs,
        sheaf_condition=sheaf_result,
        stratum_results=stratum_results,
        explanation=explanation,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Triton single-kernel analysis
# ═══════════════════════════════════════════════════════════════════════════════


def analyze_triton(
    source: str,
    name: str = "",
    grid: Optional[Tuple] = None,
    config: Optional[TensorEquivalenceConfig] = None,
) -> AnalysisJudgment:
    """Analyze a single Triton kernel for bugs.

    Checks for:

    - **Unmasked boundary accesses** (:attr:`BugKind.UNMASKED_ACCESS`):
      ``tl.load`` / ``tl.store`` without a mask when the data extent
      is not guaranteed to be a multiple of the block size.
    - **Non-associative reductions** (:attr:`BugKind.REDUCTION_ORDER`):
      floating-point reductions whose result depends on tree-reduction
      order (e.g. ``tl.sum`` on float32).
    - **Invalid block configurations**: block sizes that are not powers
      of two, or grids that would produce zero-element blocks.

    Parameters
    ----------
    source : str
        Triton kernel source code.
    name : str
        Human-readable kernel name.
    grid : tuple, optional
        Grid dimensions for the kernel launch.
    config : TensorEquivalenceConfig, optional
        Analysis configuration.

    Returns
    -------
    AnalysisJudgment
    """
    if config is None:
        config = default_analysis_config(
            mode=AnalysisMode.BUG_FINDING,
            check_triton=True,
        )

    kernel_spec = build_kernel_spec(source, name=name or "triton_kernel",
                                    grid=grid or ())
    program = ProgramId(name=kernel_spec.name)
    bugs: List[Bug] = []

    # --- Check for unmasked memory accesses ---
    if config.check_triton_memory or config.check_triton_ir:
        for access in kernel_spec.memory_accesses:
            if access.mask_expr is None:
                bugs.append(Bug(
                    kind=BugKind.UNMASKED_ACCESS,
                    stratum=TensorStratum.STRUCTURAL,
                    site_id=SiteId(
                        kind=SiteKind.TENSOR_INDEXING,
                        name=f"triton_access:{access.pointer_name}",
                    ),
                    description=(
                        f"Unmasked {access.kind} via pointer "
                        f"'{access.pointer_name}' (offset: {access.offsets_expr}). "
                        f"Without a mask, out-of-bounds accesses may occur when "
                        f"the tensor extent is not a multiple of the block size."
                    ),
                    repair_hint=(
                        f"Add mask=offsets < n_elements to tl.{access.kind}()."
                    ),
                ))

    # --- Check for non-associative reductions ---
    _NON_ASSOC_FLOAT_OPS = {"sum", "xor_sum"}
    if config.check_triton_reductions:
        for red in kernel_spec.reductions:
            if red.op in _NON_ASSOC_FLOAT_OPS and not red.is_atomic:
                bugs.append(Bug(
                    kind=BugKind.REDUCTION_ORDER,
                    stratum=TensorStratum.NUMERICAL,
                    site_id=SiteId(
                        kind=SiteKind.TENSOR_ORDER,
                        name=f"triton_reduction:{red.input_name}",
                    ),
                    description=(
                        f"Reduction '{red.op}' on '{red.input_name}' (axis={red.axis}) "
                        f"uses floating-point addition which is not associative. "
                        f"Different block sizes or warp counts may change the "
                        f"tree-reduction order, producing numerically different results."
                    ),
                    repair_hint=(
                        "Use compensated summation (Kahan) or increase precision "
                        "to float64 for the accumulator."
                    ),
                ))

    # --- Check block configuration ---
    if config.check_triton_ir:
        for block in kernel_spec.block_specs:
            if isinstance(block.size, int):
                if block.size <= 0:
                    bugs.append(Bug(
                        kind=BugKind.MEMORY_VIOLATION,
                        stratum=TensorStratum.STRUCTURAL,
                        site_id=SiteId(
                            kind=SiteKind.TENSOR_INDEXING,
                            name=f"triton_block:{block.name}",
                        ),
                        description=(
                            f"Block '{block.name}' has non-positive size "
                            f"{block.size}."
                        ),
                    ))
                elif (block.size & (block.size - 1)) != 0:
                    bugs.append(Bug(
                        kind=BugKind.MEMORY_VIOLATION,
                        stratum=TensorStratum.STRUCTURAL,
                        site_id=SiteId(
                            kind=SiteKind.TENSOR_INDEXING,
                            name=f"triton_block:{block.name}",
                        ),
                        description=(
                            f"Block '{block.name}' has size {block.size} which "
                            f"is not a power of two.  Triton requires power-of-two "
                            f"block sizes for correct tiling."
                        ),
                        repair_hint=(
                            f"Round up to the next power of two: "
                            f"{1 << (block.size - 1).bit_length()}."
                        ),
                    ))

    verdict = _verdict_from_bugs(bugs)
    stratum_results = _collect_stratum_results(bugs)

    return AnalysisJudgment(
        verdict=verdict,
        program=program,
        mode=AnalysisMode.BUG_FINDING,
        bugs=bugs,
        stratum_results=stratum_results,
        explanation=(
            f"Triton kernel '{kernel_spec.name}': "
            f"{len(bugs)} issue(s) found."
            if bugs
            else f"Triton kernel '{kernel_spec.name}': no issues detected."
        ),
    )


# ═══════════════════════════════════════════════════════════════════════════════
# MLIR single-module analysis
# ═══════════════════════════════════════════════════════════════════════════════


def analyze_mlir(
    text: str,
    name: str = "",
    config: Optional[TensorEquivalenceConfig] = None,
) -> AnalysisJudgment:
    """Analyze a single MLIR module for validity issues.

    Checks for:

    - **Empty lowering chain**: the module specifies no lowering steps,
      meaning it cannot be compiled further.
    - **Missing dialect operations**: the module references a dialect but
      contains zero operations in it (likely a lowering error).
    - **Invalid lowering**: successive lowering steps lose information
      (the restriction map is not injective).

    Parameters
    ----------
    text : str
        MLIR assembly text.
    name : str
        Human-readable module name.
    config : TensorEquivalenceConfig, optional
        Analysis configuration.

    Returns
    -------
    AnalysisJudgment
    """
    if config is None:
        config = default_analysis_config(
            mode=AnalysisMode.BUG_FINDING,
            check_mlir=True,
        )

    mlir_spec = build_mlir_module_spec(text, name=name or "mlir_module")
    program = ProgramId(name=mlir_spec.name)
    bugs: List[Bug] = []

    # --- Check for empty dialects (possible lowering loss) ---
    if config.check_mlir_ops:
        for dialect, ops in mlir_spec.dialect_ops.items():
            if not ops:
                bugs.append(Bug(
                    kind=BugKind.INVALID_LOWERING,
                    stratum=TensorStratum.STRUCTURAL,
                    site_id=SiteId(
                        kind=SiteKind.SSA_VALUE,
                        name=f"mlir_dialect:{dialect.value}",
                    ),
                    description=(
                        f"Dialect '{dialect.value}' is referenced but contains "
                        f"zero operations.  This may indicate a lowering error "
                        f"that eliminated all operations without replacement."
                    ),
                ))

    # --- Check lowering chain validity ---
    if config.check_mlir_lowering:
        chain = mlir_spec.lowering_chain
        if not chain and mlir_spec.dialect_ops:
            bugs.append(Bug(
                kind=BugKind.INVALID_LOWERING,
                stratum=TensorStratum.STRUCTURAL,
                site_id=SiteId(
                    kind=SiteKind.SSA_VALUE,
                    name="mlir_lowering_chain",
                ),
                description=(
                    "MLIR module has dialect operations but no lowering chain. "
                    "The module cannot be compiled to a lower-level representation."
                ),
            ))

        # Check that successive lowering steps don't drop all ops
        for i, step in enumerate(chain):
            if hasattr(step, "ops_before") and hasattr(step, "ops_after"):
                if step.ops_before > 0 and step.ops_after == 0:
                    bugs.append(Bug(
                        kind=BugKind.INVALID_LOWERING,
                        stratum=TensorStratum.STRUCTURAL,
                        site_id=SiteId(
                            kind=SiteKind.SSA_VALUE,
                            name=f"mlir_lowering_step:{i}",
                        ),
                        description=(
                            f"Lowering step {i} eliminated all {step.ops_before} "
                            f"operations without producing replacements.  "
                            f"Semantic information may have been lost."
                        ),
                    ))

    verdict = _verdict_from_bugs(bugs)
    stratum_results = _collect_stratum_results(bugs)

    return AnalysisJudgment(
        verdict=verdict,
        program=program,
        mode=AnalysisMode.BUG_FINDING,
        bugs=bugs,
        stratum_results=stratum_results,
        explanation=(
            f"MLIR module '{mlir_spec.name}': "
            f"{len(bugs)} issue(s) found."
            if bugs
            else f"MLIR module '{mlir_spec.name}': no issues detected."
        ),
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Correctness checking (spec conformance)
# ═══════════════════════════════════════════════════════════════════════════════


def check_correctness(
    fn: Callable,
    spec: SpecificationPresheaf,
    tensor_specs: Optional[Sequence[TensorSpec]] = None,
    test_inputs: Optional[Sequence[Sequence[Any]]] = None,
    config: Optional[TensorEquivalenceConfig] = None,
) -> CorrectnessJudgment:
    """Check if a function conforms to a specification presheaf.

    Mathematically, this checks for the existence of a morphism

        η : Spec → Sem_f

    from the specification presheaf to the semantic presheaf of the
    function.  The check is **one-way**: conformance does not imply
    equivalence, only that the implementation *refines* the specification.

    Parameters
    ----------
    fn : callable
        The function under test.
    spec : SpecificationPresheaf
        The specification presheaf to check against.
    tensor_specs : sequence of TensorSpec, optional
        Type-level descriptions of each input tensor.
    test_inputs : sequence of input-tuples, optional
        Concrete test inputs.  If *None*, synthesised from *tensor_specs*.
    config : TensorEquivalenceConfig, optional
        Analysis configuration.

    Returns
    -------
    CorrectnessJudgment
    """
    if config is None:
        config = default_analysis_config(mode=AnalysisMode.CORRECTNESS)

    if tensor_specs is None:
        tensor_specs = _default_tensor_specs(fn, config)

    SpecChecker = _get_spec_checker()
    checker = SpecChecker(config=config)
    return checker.check(fn, spec, tensor_specs, test_inputs)


# ═══════════════════════════════════════════════════════════════════════════════
# Refinement checking
# ═══════════════════════════════════════════════════════════════════════════════


def _check_refinement(
    fn_impl: Callable,
    fn_spec: Callable,
    tensor_specs: Optional[Sequence[TensorSpec]] = None,
    test_inputs: Optional[Sequence[Sequence[Any]]] = None,
    config: Optional[TensorEquivalenceConfig] = None,
) -> AnalysisJudgment:
    """Check if *fn_impl* refines *fn_spec* (one-way behavioural inclusion).

    Refinement means that for every observable behaviour of *fn_spec*,
    *fn_impl* produces a compatible result.  This is strictly weaker than
    equivalence: fn_impl may have additional behaviours (e.g., support
    more dtypes) that fn_spec does not.

    Implemented by running the equivalence pipeline and reinterpreting
    the verdict: EQUIVALENT → VALID, REFINED → VALID, else → INVALID.
    """
    if config is None:
        config = default_analysis_config(mode=AnalysisMode.REFINEMENT)

    if tensor_specs is None:
        tensor_specs = _default_tensor_specs(fn_impl, config)

    if test_inputs is None:
        test_inputs = list(generate_test_inputs(
            tensor_specs,
            n_random=config.max_test_inputs,
        ))

    # Run the two-program equivalence pipeline
    GlobalChecker = _get_global_checker()
    checker = GlobalChecker(config)
    global_judgment: TensorGlobalJudgment = checker.check(
        fn_impl, fn_spec, tensor_specs, test_inputs,
    )

    # Reinterpret the equivalence verdict as a refinement verdict
    impl_program = _make_program_id(fn_impl)
    if global_judgment.verdict in (
        EquivalenceVerdict.EQUIVALENT,
        EquivalenceVerdict.REFINED,
    ):
        verdict = AnalysisVerdict.VALID
        explanation = (
            f"'{impl_program}' refines the reference implementation: "
            f"equivalence verdict was {global_judgment.verdict.value}."
        )
    elif global_judgment.verdict == EquivalenceVerdict.UNKNOWN:
        verdict = AnalysisVerdict.UNKNOWN
        explanation = (
            f"Could not determine if '{impl_program}' refines the reference: "
            f"equivalence checker returned UNKNOWN."
        )
    else:
        verdict = AnalysisVerdict.INVALID
        explanation = (
            f"'{impl_program}' does NOT refine the reference: "
            f"equivalence verdict was {global_judgment.verdict.value}."
        )

    # Convert obstructions to bugs for the AnalysisJudgment format
    bugs: List[Bug] = []
    for obs in global_judgment.obstructions:
        bugs.append(Bug(
            kind=BugKind.SHEAF_GLUING_FAILURE,
            stratum=obs.stratum if hasattr(obs, "stratum") else TensorStratum.NUMERICAL,
            site_id=obs.site_id if hasattr(obs, "site_id") else SiteId(
                kind=SiteKind.RETURN_OUTPUT_BOUNDARY,
                name="refinement_obstruction",
            ),
            description=str(obs),
        ))

    return AnalysisJudgment(
        verdict=verdict,
        program=impl_program,
        mode=AnalysisMode.REFINEMENT,
        bugs=bugs,
        stratum_results=_collect_stratum_results(bugs),
        explanation=explanation,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Unified dispatch
# ═══════════════════════════════════════════════════════════════════════════════


def analyze(
    fn: Callable,
    mode: AnalysisMode = AnalysisMode.BUG_FINDING,
    tensor_specs: Optional[Sequence[TensorSpec]] = None,
    test_inputs: Optional[Sequence[Sequence[Any]]] = None,
    config: Optional[TensorEquivalenceConfig] = None,
    spec: Optional[SpecificationPresheaf] = None,
    fn_g: Optional[Callable] = None,
    triton_source: Optional[str] = None,
    mlir_text: Optional[str] = None,
) -> Any:
    """Unified analysis entry point — dispatches by mode.

    This is the top-level function that selects the appropriate analysis
    pipeline based on the requested :class:`AnalysisMode`:

    +--------------------------+----------------------------------------------+
    | Mode                     | Dispatches to                                |
    +==========================+==============================================+
    | ``BUG_FINDING``          | :func:`analyze_torch`                        |
    +--------------------------+----------------------------------------------+
    | ``CORRECTNESS``          | :func:`check_correctness` (requires *spec*)  |
    +--------------------------+----------------------------------------------+
    | ``EQUIVALENCE``          | :func:`check_torch_equivalence` (requires    |
    |                          | *fn_g*)                                      |
    +--------------------------+----------------------------------------------+
    | ``REFINEMENT``           | refinement check (*fn* refines *fn_g*)       |
    +--------------------------+----------------------------------------------+
    | ``OPTIMIZATION``         | equivalence modulo performance strata        |
    +--------------------------+----------------------------------------------+

    Parameters
    ----------
    fn : callable
        The primary function to analyze.
    mode : AnalysisMode
        Which analysis mode to use.
    tensor_specs : sequence of TensorSpec, optional
        Input tensor specifications.
    test_inputs : sequence of input-tuples, optional
        Concrete test inputs.
    config : TensorEquivalenceConfig, optional
        Analysis configuration.
    spec : SpecificationPresheaf, optional
        Required for ``CORRECTNESS`` mode.
    fn_g : callable, optional
        Required for ``EQUIVALENCE`` and ``REFINEMENT`` modes.
    triton_source : str, optional
        Triton kernel source for inclusion in analysis.
    mlir_text : str, optional
        MLIR text for inclusion in analysis.

    Returns
    -------
    AnalysisJudgment or CorrectnessJudgment or TensorGlobalJudgment
        The type depends on the mode:
        - BUG_FINDING / REFINEMENT → AnalysisJudgment
        - CORRECTNESS → CorrectnessJudgment
        - EQUIVALENCE / OPTIMIZATION → TensorGlobalJudgment
    """
    if config is None:
        config = default_analysis_config(mode=mode)

    # ── Bug-finding ───────────────────────────────────────────────────────
    if mode == AnalysisMode.BUG_FINDING:
        return analyze_torch(
            fn,
            tensor_specs=tensor_specs,
            test_inputs=test_inputs,
            config=config,
            triton_source=triton_source,
            mlir_text=mlir_text,
        )

    # ── Correctness ───────────────────────────────────────────────────────
    if mode == AnalysisMode.CORRECTNESS:
        if spec is None:
            raise ValueError(
                "AnalysisMode.CORRECTNESS requires a 'spec' argument "
                "(a SpecificationPresheaf)."
            )
        return check_correctness(
            fn,
            spec=spec,
            tensor_specs=tensor_specs,
            test_inputs=test_inputs,
            config=config,
        )

    # ── Equivalence ───────────────────────────────────────────────────────
    if mode == AnalysisMode.EQUIVALENCE:
        if fn_g is None:
            raise ValueError(
                "AnalysisMode.EQUIVALENCE requires a 'fn_g' argument "
                "(the second function to compare)."
            )
        from .torch_pipeline import check_torch_equivalence
        return check_torch_equivalence(
            fn_f=fn,
            fn_g=fn_g,
            tensor_specs=tensor_specs,
            test_inputs=test_inputs,
            config=config,
            triton_source_f=triton_source,
            mlir_text_f=mlir_text,
        )

    # ── Refinement ────────────────────────────────────────────────────────
    if mode == AnalysisMode.REFINEMENT:
        if fn_g is None:
            raise ValueError(
                "AnalysisMode.REFINEMENT requires a 'fn_g' argument "
                "(the reference implementation)."
            )
        return _check_refinement(
            fn_impl=fn,
            fn_spec=fn_g,
            tensor_specs=tensor_specs,
            test_inputs=test_inputs,
            config=config,
        )

    # ── Optimization ──────────────────────────────────────────────────────
    if mode == AnalysisMode.OPTIMIZATION:
        if fn_g is None:
            raise ValueError(
                "AnalysisMode.OPTIMIZATION requires a 'fn_g' argument "
                "(the optimised function to compare against the original)."
            )
        # Optimization equivalence ignores performance-irrelevant strata:
        # we only check METADATA + NUMERICAL, skipping STRUCTURAL/BEHAVIORAL
        # so that stride/layout changes are tolerated.
        opt_config = default_analysis_config(
            mode=AnalysisMode.OPTIMIZATION,
            check_stride=False,
            check_autograd=False,
            check_memory_aliasing=False,
            short_circuit_strata=True,
        )
        # Apply any user overrides on top
        if config is not None:
            for fld in ("tolerance", "max_test_inputs", "check_shape",
                        "check_dtype", "check_device", "check_numerical",
                        "test_shapes", "test_dtypes", "test_devices"):
                val = getattr(config, fld, None)
                if val is not None:
                    object.__setattr__(opt_config, fld, val)

        from .torch_pipeline import check_torch_equivalence
        return check_torch_equivalence(
            fn_f=fn,
            fn_g=fn_g,
            tensor_specs=tensor_specs,
            test_inputs=test_inputs,
            config=opt_config,
        )

    raise ValueError(f"Unsupported analysis mode: {mode!r}")
