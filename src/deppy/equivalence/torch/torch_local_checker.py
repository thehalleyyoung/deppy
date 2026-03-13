"""
PyTorch-specialized local checker — filtration-ordered site checking.

Checks local equivalence at each tensor observation site, proceeding
in the canonical filtration order:

  METADATA  (device, dtype)
  ↓
  STRUCTURAL  (shape, stride)
  ↓
  NUMERICAL  (values, tolerances)
  ↓
  BEHAVIORAL  (autograd, dispatch)

Lower strata are checked first as necessary conditions.  If a lower
stratum fails, higher strata are short-circuited (e.g., if shapes
differ, numerical comparison is meaningless).

Each site check produces a TensorLocalJudgment.  The collection of
local judgments forms the *sections* of the equivalence presheaf,
which the global checker will attempt to glue.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Set, Tuple

from ._protocols import (
    EquivalenceVerdict,
    SiteId,
    SiteKind,
    TensorEquivalenceConfig,
    TensorLocalJudgment,
    TensorObstruction,
    TensorObstructionKind,
    TensorSiteKind,
    TensorSpec,
    TensorStratum,
    TritonKernelSpec,
    MLIRModuleSpec,
    SITE_KIND_STRATUM,
)

from .tensor_site import (
    TensorObservationSite,
    TensorCover,
    TensorSiteCategoryBuilder,
    generate_test_inputs,
)

from .shape_equiv import ShapeEquivalenceChecker
from .dtype_equiv import DtypeEquivalenceChecker
from .memory_equiv import MemoryEquivalenceChecker
from .autograd_equiv import AutogradEquivalenceChecker
from .dispatch_equiv import DispatchEquivalenceChecker
from .numerical_equiv import NumericalEquivalenceChecker
from .triton_equiv import TritonEquivalenceChecker
from .triton_mlir import MLIREquivalenceChecker

try:
    import torch
    _HAS_TORCH = True
except ImportError:
    _HAS_TORCH = False


# ---------------------------------------------------------------------------
# Filtration ordering
# ---------------------------------------------------------------------------

_STRATUM_ORDER: Dict[TensorStratum, int] = {
    TensorStratum.METADATA: 0,
    TensorStratum.STRUCTURAL: 1,
    TensorStratum.NUMERICAL: 2,
    TensorStratum.BEHAVIORAL: 3,
}

# Which site kinds belong to each stratum
_STRATUM_SITES: Dict[TensorStratum, List[TensorSiteKind]] = {
    TensorStratum.METADATA: [
        TensorSiteKind.DTYPE,
        TensorSiteKind.DEVICE,
    ],
    TensorStratum.STRUCTURAL: [
        TensorSiteKind.SHAPE,
        TensorSiteKind.STRIDE,
        TensorSiteKind.KERNEL_CONFIG,
        TensorSiteKind.TRITON_BLOCK,
        TensorSiteKind.TRITON_MEMORY,
    ],
    TensorStratum.NUMERICAL: [
        TensorSiteKind.NUMERICAL,
        TensorSiteKind.TRITON_REDUCTION,
    ],
    TensorStratum.BEHAVIORAL: [
        TensorSiteKind.AUTOGRAD,
        TensorSiteKind.MLIR_OP,
    ],
}


# ---------------------------------------------------------------------------
# Local checker
# ---------------------------------------------------------------------------

@dataclass
class LocalCheckResult:
    """Result of local checking across all sites."""
    judgments: List[TensorLocalJudgment]
    short_circuited_at: Optional[TensorStratum] = None
    all_equivalent: bool = False


class TorchLocalChecker:
    """
    PyTorch-specialized local equivalence checker.

    Proceeds through the canonical filtration, checking each stratum
    in order.  If a lower stratum fails and short-circuit is enabled,
    higher strata are skipped.

    This is the *local* part of the sheaf condition: at each site,
    we check that the sections (behaviors) of f and g agree.
    """

    def __init__(self, config: TensorEquivalenceConfig):
        self._config = config
        self._shape_checker = ShapeEquivalenceChecker(config)
        self._dtype_checker = DtypeEquivalenceChecker(config)
        self._memory_checker = MemoryEquivalenceChecker(config)
        self._autograd_checker = AutogradEquivalenceChecker(config)
        self._dispatch_checker = DispatchEquivalenceChecker(config)
        self._numerical_checker = NumericalEquivalenceChecker(config)
        self._triton_checker = TritonEquivalenceChecker(config)
        self._mlir_checker = MLIREquivalenceChecker(config)

    def check_all_sites(
        self,
        fn_f: Callable,
        fn_g: Callable,
        tensor_specs: Sequence[TensorSpec],
        test_inputs: Optional[Sequence[Sequence[Any]]] = None,
        triton_spec_f: Optional[TritonKernelSpec] = None,
        triton_spec_g: Optional[TritonKernelSpec] = None,
        mlir_spec_f: Optional[MLIRModuleSpec] = None,
        mlir_spec_g: Optional[MLIRModuleSpec] = None,
    ) -> LocalCheckResult:
        """
        Check all tensor sites in filtration order.

        Returns local judgments for each site, possibly short-circuiting
        at a failed stratum.
        """
        if test_inputs is None:
            test_inputs = list(generate_test_inputs(
                tensor_specs,
                n_random=self._config.max_test_inputs,
            ))

        judgments: List[TensorLocalJudgment] = []
        short_circuited_at: Optional[TensorStratum] = None

        strata = sorted(_STRATUM_ORDER.keys(), key=lambda s: _STRATUM_ORDER[s])

        for stratum in strata:
            site_kinds = _STRATUM_SITES.get(stratum, [])

            # Filter to enabled site kinds
            enabled_kinds = [
                sk for sk in site_kinds
                if self._is_site_enabled(sk, triton_spec_f, triton_spec_g,
                                         mlir_spec_f, mlir_spec_g)
            ]

            stratum_judgments = []
            for kind in enabled_kinds:
                j = self._check_site_kind(
                    kind, fn_f, fn_g, tensor_specs, test_inputs,
                    triton_spec_f, triton_spec_g,
                    mlir_spec_f, mlir_spec_g,
                )
                stratum_judgments.append(j)

            judgments.extend(stratum_judgments)

            # Short-circuit check
            if self._config.short_circuit_strata:
                has_failure = any(
                    j.verdict == EquivalenceVerdict.INEQUIVALENT
                    for j in stratum_judgments
                )
                if has_failure:
                    short_circuited_at = stratum
                    break

        all_eq = all(
            j.verdict in (EquivalenceVerdict.EQUIVALENT, EquivalenceVerdict.REFINED)
            for j in judgments
        )

        return LocalCheckResult(
            judgments=judgments,
            short_circuited_at=short_circuited_at,
            all_equivalent=all_eq,
        )

    def _is_site_enabled(
        self,
        kind: TensorSiteKind,
        triton_f: Optional[TritonKernelSpec],
        triton_g: Optional[TritonKernelSpec],
        mlir_f: Optional[MLIRModuleSpec],
        mlir_g: Optional[MLIRModuleSpec],
    ) -> bool:
        """Check if a site kind should be checked."""
        triton_kinds = {
            TensorSiteKind.KERNEL_CONFIG,
            TensorSiteKind.TRITON_BLOCK,
            TensorSiteKind.TRITON_MEMORY,
            TensorSiteKind.TRITON_REDUCTION,
        }
        if kind in triton_kinds:
            return triton_f is not None and triton_g is not None

        if kind == TensorSiteKind.MLIR_OP:
            return mlir_f is not None and mlir_g is not None

        return True

    def _check_site_kind(
        self,
        kind: TensorSiteKind,
        fn_f: Callable,
        fn_g: Callable,
        tensor_specs: Sequence[TensorSpec],
        test_inputs: Sequence[Sequence[Any]],
        triton_f: Optional[TritonKernelSpec],
        triton_g: Optional[TritonKernelSpec],
        mlir_f: Optional[MLIRModuleSpec],
        mlir_g: Optional[MLIRModuleSpec],
    ) -> TensorLocalJudgment:
        """Check a single site kind."""
        site_id = SiteId(kind=SiteKind.TENSOR_SHAPE, name=f"tensor_{kind.name.lower()}")

        if kind == TensorSiteKind.SHAPE:
            return self._check_shape(fn_f, fn_g, tensor_specs, test_inputs, site_id)
        elif kind == TensorSiteKind.DTYPE:
            return self._check_dtype(fn_f, fn_g, tensor_specs, test_inputs, site_id)
        elif kind == TensorSiteKind.DEVICE:
            return self._check_device(fn_f, fn_g, tensor_specs, test_inputs, site_id)
        elif kind == TensorSiteKind.STRIDE:
            return self._check_stride(fn_f, fn_g, tensor_specs, test_inputs, site_id)
        elif kind == TensorSiteKind.NUMERICAL:
            return self._check_numerical(fn_f, fn_g, test_inputs, site_id)
        elif kind == TensorSiteKind.AUTOGRAD:
            return self._check_autograd(fn_f, fn_g, test_inputs, site_id)
        elif kind in (TensorSiteKind.KERNEL_CONFIG, TensorSiteKind.TRITON_BLOCK,
                      TensorSiteKind.TRITON_MEMORY):
            return self._check_triton(triton_f, triton_g, site_id)
        elif kind == TensorSiteKind.TRITON_REDUCTION:
            return self._check_triton_reduction(triton_f, triton_g, site_id)
        elif kind == TensorSiteKind.MLIR_OP:
            return self._check_mlir(mlir_f, mlir_g, site_id)
        else:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=SITE_KIND_STRATUM.get(kind, TensorStratum.METADATA),
                tensor_site_kind=kind,
                verdict=EquivalenceVerdict.UNKNOWN,
                explanation=f"No checker for {kind.name}",
            )

    # -----------------------------------------------------------------------
    # Per-kind checking methods
    # -----------------------------------------------------------------------

    def _check_shape(self, fn_f: Callable, fn_g: Callable,
                     specs: Sequence[TensorSpec],
                     test_inputs: Sequence[Sequence[Any]],
                     site_id: SiteId) -> TensorLocalJudgment:
        """Check shape equivalence."""
        return self._shape_checker.check_site(fn_f, fn_g, specs, site_id)

    def _check_dtype(self, fn_f: Callable, fn_g: Callable,
                     specs: Sequence[TensorSpec],
                     test_inputs: Sequence[Sequence[Any]],
                     site_id: SiteId) -> TensorLocalJudgment:
        """Check dtype equivalence."""
        return self._dtype_checker.check_site(fn_f, fn_g, specs, site_id)

    def _check_device(self, fn_f: Callable, fn_g: Callable,
                      specs: Sequence[TensorSpec],
                      test_inputs: Sequence[Sequence[Any]],
                      site_id: SiteId) -> TensorLocalJudgment:
        """Check device placement equivalence."""
        return self._dispatch_checker.check_site(fn_f, fn_g, list(test_inputs), site_id)

    def _check_stride(self, fn_f: Callable, fn_g: Callable,
                      specs: Sequence[TensorSpec],
                      test_inputs: Sequence[Sequence[Any]],
                      site_id: SiteId) -> TensorLocalJudgment:
        """Check stride/memory layout equivalence."""
        return self._memory_checker.check_site(fn_f, fn_g, list(test_inputs), site_id)

    def _check_numerical(self, fn_f: Callable, fn_g: Callable,
                         test_inputs: Sequence[Sequence[Any]],
                         site_id: SiteId) -> TensorLocalJudgment:
        """Check numerical equivalence across test inputs."""
        return self._numerical_checker.check_site(fn_f, fn_g, list(test_inputs), site_id)

    def _check_autograd(self, fn_f: Callable, fn_g: Callable,
                        test_inputs: Sequence[Sequence[Any]],
                        site_id: SiteId) -> TensorLocalJudgment:
        """Check autograd equivalence."""
        return self._autograd_checker.check_site(fn_f, fn_g, list(test_inputs), site_id)

    def _check_triton(self, triton_f: Optional[TritonKernelSpec],
                      triton_g: Optional[TritonKernelSpec],
                      site_id: SiteId) -> TensorLocalJudgment:
        """Check Triton kernel structural equivalence."""
        if triton_f is None or triton_g is None:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.STRUCTURAL,
                tensor_site_kind=TensorSiteKind.TRITON_BLOCK,
                verdict=EquivalenceVerdict.UNKNOWN,
                explanation="Triton specs not provided",
            )
        return self._triton_checker.check_site(triton_f, triton_g, site_id)

    def _check_triton_reduction(self, triton_f: Optional[TritonKernelSpec],
                                triton_g: Optional[TritonKernelSpec],
                                site_id: SiteId) -> TensorLocalJudgment:
        """Check Triton reduction equivalence."""
        if triton_f is None or triton_g is None:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.NUMERICAL,
                tensor_site_kind=TensorSiteKind.TRITON_REDUCTION,
                verdict=EquivalenceVerdict.UNKNOWN,
                explanation="Triton specs not provided",
            )
        return self._triton_checker.check_reduction_site(triton_f, triton_g, site_id)

    def _check_mlir(self, mlir_f: Optional[MLIRModuleSpec],
                    mlir_g: Optional[MLIRModuleSpec],
                    site_id: SiteId) -> TensorLocalJudgment:
        """Check MLIR module equivalence."""
        if mlir_f is None or mlir_g is None:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.BEHAVIORAL,
                tensor_site_kind=TensorSiteKind.MLIR_OP,
                verdict=EquivalenceVerdict.UNKNOWN,
                explanation="MLIR specs not provided",
            )
        return self._mlir_checker.check_site(mlir_f, mlir_g, site_id)

    # -------------------------------------------------------------------
    # Single-program analysis (general, not equivalence-specific)
    # -------------------------------------------------------------------

    def analyze_single(
        self,
        fn: Callable,
        tensor_specs: Sequence[TensorSpec],
        test_inputs: Optional[Sequence[Sequence[Any]]] = None,
        triton_spec: Optional[TritonKernelSpec] = None,
        mlir_spec: Optional[MLIRModuleSpec] = None,
    ) -> "AnalysisLocalResult":
        """
        Analyze a single function at all tensor sites.

        This is the single-program counterpart to check_all_sites().
        Instead of comparing two programs, it runs each domain checker's
        analyze() method to find bugs in one program.

        Sheaf-theoretic interpretation: check if the program's presheaf
        F_fn satisfies internal consistency at each observation site.
        """
        from ._protocols import (
            AnalysisVerdict, AnalysisJudgment, BugKind, Bug, ProgramId,
        )

        if test_inputs is None:
            test_inputs = list(generate_test_inputs(
                tensor_specs, n_random=self._config.max_test_inputs,
            ))

        all_bugs: List[Bug] = []
        stratum_results: Dict[TensorStratum, AnalysisVerdict] = {}
        fn_name = getattr(fn, "__name__", "fn")

        strata = sorted(_STRATUM_ORDER.keys(), key=lambda s: _STRATUM_ORDER[s])

        for stratum in strata:
            site_kinds = _STRATUM_SITES.get(stratum, [])
            stratum_bugs: List[Bug] = []

            for kind in site_kinds:
                # Skip triton/mlir if no spec provided
                triton_kinds = {
                    TensorSiteKind.KERNEL_CONFIG, TensorSiteKind.TRITON_BLOCK,
                    TensorSiteKind.TRITON_MEMORY, TensorSiteKind.TRITON_REDUCTION,
                }
                if kind in triton_kinds and triton_spec is None:
                    continue
                if kind == TensorSiteKind.MLIR_OP and mlir_spec is None:
                    continue

                bugs = self._analyze_site_kind(
                    kind, fn, tensor_specs, list(test_inputs),
                    triton_spec, mlir_spec,
                )
                stratum_bugs.extend(bugs)

            all_bugs.extend(stratum_bugs)
            if stratum_bugs:
                stratum_results[stratum] = AnalysisVerdict.INVALID
            else:
                stratum_results[stratum] = AnalysisVerdict.VALID

            # Short-circuit if configured
            if self._config.short_circuit_strata and stratum_bugs:
                break

        verdict = (AnalysisVerdict.INVALID if all_bugs
                   else AnalysisVerdict.VALID)

        return AnalysisLocalResult(
            bugs=all_bugs,
            stratum_results=stratum_results,
            verdict=verdict,
        )

    def _analyze_site_kind(
        self,
        kind: TensorSiteKind,
        fn: Callable,
        tensor_specs: Sequence[TensorSpec],
        test_inputs: List[List[Any]],
        triton_spec: Optional[TritonKernelSpec],
        mlir_spec: Optional[MLIRModuleSpec],
    ) -> "List[Bug]":
        """Analyze a single site kind for a single function."""
        from ._protocols import AnalysisJudgment, AnalysisVerdict, Bug

        site_id = SiteId(kind=SiteKind.TENSOR_SHAPE,
                         name=f"analyze_{kind.name.lower()}")

        # Delegate to domain checker's analyze() method if available
        checker_map = {
            TensorSiteKind.SHAPE: self._shape_checker,
            TensorSiteKind.DTYPE: self._dtype_checker,
            TensorSiteKind.DEVICE: self._dispatch_checker,
            TensorSiteKind.STRIDE: self._memory_checker,
            TensorSiteKind.NUMERICAL: self._numerical_checker,
            TensorSiteKind.AUTOGRAD: self._autograd_checker,
        }

        checker = checker_map.get(kind)
        if checker is not None and hasattr(checker, "analyze"):
            try:
                judgment = checker.analyze(fn, test_inputs, site_id)
                return judgment.bugs if hasattr(judgment, "bugs") else []
            except Exception:
                return []

        # Triton/MLIR single-program analysis
        if kind in (TensorSiteKind.KERNEL_CONFIG, TensorSiteKind.TRITON_BLOCK,
                    TensorSiteKind.TRITON_MEMORY, TensorSiteKind.TRITON_REDUCTION):
            if triton_spec and hasattr(self._triton_checker, "analyze"):
                try:
                    judgment = self._triton_checker.analyze(triton_spec, site_id)
                    return judgment.bugs if hasattr(judgment, "bugs") else []
                except Exception:
                    return []

        if kind == TensorSiteKind.MLIR_OP:
            if mlir_spec and hasattr(self._mlir_checker, "analyze"):
                try:
                    judgment = self._mlir_checker.analyze(mlir_spec, site_id)
                    return judgment.bugs if hasattr(judgment, "bugs") else []
                except Exception:
                    return []

        return []


@dataclass
class AnalysisLocalResult:
    """Result of single-program local analysis across all sites."""
    bugs: List["Bug"] = field(default_factory=list)
    stratum_results: Dict[TensorStratum, "AnalysisVerdict"] = field(
        default_factory=dict
    )
    verdict: "AnalysisVerdict" = None  # type: ignore[assignment]
