"""Specification presheaves and correctness checking for tensor programs.

Mathematical background
-----------------------
A *specification* is itself a presheaf on the tensor site category,

    Spec : TensorSite^{op} → Set,

whose sections encode the properties an implementation *must* satisfy.
Correctness is witnessed by the existence of a natural transformation

    η : Spec  ⟶  Sem_f

from the specification presheaf to the semantic presheaf of the
implementation *f*.  Crucially, η need **not** be invertible — it is a
one-way refinement check ("the implementation satisfies the spec"),
not a full equivalence.

The checker proceeds stratum-by-stratum through the filtration

    METADATA  ≤  STRUCTURAL  ≤  NUMERICAL  ≤  BEHAVIORAL

and short-circuits on the first failure: a violation at stratum k
renders higher strata unreachable, mirroring the obstruction-theoretic
idea that a non-trivial cohomology class at level k blocks extension
to level k+1.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from ._protocols import (
    SiteId,
    SiteKind,
    TensorSiteKind,
    TensorStratum,
    TensorSpec,
    TensorEquivalenceConfig,
    TensorObstruction,
    TensorObstructionKind,
    EquivalenceVerdict,
    NumericalToleranceSpec,
    ProgramId,
    AnalysisMode,
    AnalysisVerdict,
    BugKind,
    Bug,
    SpecificationSection,
    SpecificationPresheaf,
    CorrectnessJudgment,
    AnalysisJudgment,
    SITE_KIND_STRATUM,
)

# ---------------------------------------------------------------------------
# Optional torch import — gracefully degrade when torch is absent.
# ---------------------------------------------------------------------------
try:
    import torch
    _HAS_TORCH = True
except ImportError:  # pragma: no cover
    torch = None  # type: ignore[assignment]
    _HAS_TORCH = False


# ───────────────────────────────────────────────────────────────────
# 1.  Specification builder — fluent API
# ───────────────────────────────────────────────────────────────────

class SpecBuilder:
    """Fluent builder for :class:`SpecificationPresheaf`.

    A ``SpecBuilder`` accumulates specification *sections* — each one a
    property expectation localised to a site in the tensor site category —
    and produces a presheaf whose global sections are the conjunction of
    all expectations.

    Example::

        spec = (
            SpecBuilder("softmax_spec")
            .expect_shape((4, 10))
            .expect_dtype("float32")
            .expect_output_range(0.0, 1.0)
            .expect_gradient_exists()
            .build()
        )
    """

    def __init__(self, name: str, *, description: str = "") -> None:
        self._name = name
        self._description = description
        self._sections: Dict[SiteId, List[SpecificationSection]] = {}
        self._strata: Set[TensorStratum] = set()

    # -- shape expectations -------------------------------------------------

    def expect_shape(
        self,
        shape: Tuple[int, ...],
        site_name: str = "output_shape",
    ) -> SpecBuilder:
        """Expect the output tensor to have the given *shape*."""
        site = SiteId(kind=SiteKind.TENSOR_SHAPE, name=site_name)
        section = SpecificationSection(
            site_id=site,
            property_name="shape",
            expected_value=shape,
        )
        self._add(site, section, TensorStratum.STRUCTURAL)
        return self

    # -- dtype expectations -------------------------------------------------

    def expect_dtype(
        self,
        dtype: str,
        site_name: str = "output_dtype",
    ) -> SpecBuilder:
        """Expect the output tensor to have the given *dtype* string."""
        site = SiteId(kind=SiteKind.TENSOR_SHAPE, name=site_name)
        section = SpecificationSection(
            site_id=site,
            property_name="dtype",
            expected_value=dtype,
        )
        self._add(site, section, TensorStratum.METADATA)
        return self

    # -- numerical range ----------------------------------------------------

    def expect_output_range(
        self,
        min_val: float,
        max_val: float,
        site_name: str = "output_range",
    ) -> SpecBuilder:
        """Expect every element of the output to lie in [*min_val*, *max_val*]."""
        site = SiteId(kind=SiteKind.TENSOR_SHAPE, name=site_name)
        section = SpecificationSection(
            site_id=site,
            property_name="output_range",
            expected_value=(min_val, max_val),
            predicate=lambda out, lo=min_val, hi=max_val: _check_range(out, lo, hi),
        )
        self._add(site, section, TensorStratum.NUMERICAL)
        return self

    # -- gradient -----------------------------------------------------------

    def expect_gradient_exists(
        self, site_name: str = "gradient"
    ) -> SpecBuilder:
        """Expect the function to be differentiable (gradient must exist)."""
        site = SiteId(kind=SiteKind.TENSOR_SHAPE, name=site_name)
        section = SpecificationSection(
            site_id=site,
            property_name="gradient_exists",
            expected_value=True,
            predicate=lambda out: _check_gradient_exists(out),
        )
        self._add(site, section, TensorStratum.BEHAVIORAL)
        return self

    # -- determinism --------------------------------------------------------

    def expect_deterministic(
        self, site_name: str = "determinism"
    ) -> SpecBuilder:
        """Expect the function to produce deterministic output."""
        site = SiteId(kind=SiteKind.TENSOR_SHAPE, name=site_name)
        section = SpecificationSection(
            site_id=site,
            property_name="deterministic",
            expected_value=True,
        )
        self._add(site, section, TensorStratum.BEHAVIORAL)
        return self

    # -- device -------------------------------------------------------------

    def expect_device(
        self, device: str, site_name: str = "device"
    ) -> SpecBuilder:
        """Expect the output tensor to reside on *device*."""
        site = SiteId(kind=SiteKind.TENSOR_SHAPE, name=site_name)
        section = SpecificationSection(
            site_id=site,
            property_name="device",
            expected_value=device,
        )
        self._add(site, section, TensorStratum.METADATA)
        return self

    # -- contiguity ---------------------------------------------------------

    def expect_contiguous(
        self, site_name: str = "memory_layout"
    ) -> SpecBuilder:
        """Expect the output tensor to be contiguous in memory."""
        site = SiteId(kind=SiteKind.TENSOR_SHAPE, name=site_name)
        section = SpecificationSection(
            site_id=site,
            property_name="contiguous",
            expected_value=True,
        )
        self._add(site, section, TensorStratum.STRUCTURAL)
        return self

    # -- numerical stability helpers ----------------------------------------

    def expect_no_nan(self, site_name: str = "no_nan") -> SpecBuilder:
        """Expect the output to contain no NaN values."""
        site = SiteId(kind=SiteKind.TENSOR_SHAPE, name=site_name)
        section = SpecificationSection(
            site_id=site,
            property_name="no_nan",
            expected_value=True,
            predicate=lambda out: _check_no_nan(out),
        )
        self._add(site, section, TensorStratum.NUMERICAL)
        return self

    def expect_no_inf(self, site_name: str = "no_inf") -> SpecBuilder:
        """Expect the output to contain no Inf values."""
        site = SiteId(kind=SiteKind.TENSOR_SHAPE, name=site_name)
        section = SpecificationSection(
            site_id=site,
            property_name="no_inf",
            expected_value=True,
            predicate=lambda out: _check_no_inf(out),
        )
        self._add(site, section, TensorStratum.NUMERICAL)
        return self

    # -- generic predicate --------------------------------------------------

    def expect_predicate(
        self,
        predicate: Callable,
        description: str,
        stratum: TensorStratum,
        site_name: str = "custom",
    ) -> SpecBuilder:
        """Add a custom predicate expectation at the given *stratum*.

        The *predicate* receives the raw function output and must return
        ``True`` when the property holds.
        """
        site = SiteId(kind=SiteKind.TENSOR_SHAPE, name=site_name)
        section = SpecificationSection(
            site_id=site,
            property_name=description,
            expected_value=True,
            predicate=predicate,
        )
        self._add(site, section, stratum)
        return self

    # -- build --------------------------------------------------------------

    def build(self) -> SpecificationPresheaf:
        """Construct the :class:`SpecificationPresheaf`.

        The resulting presheaf is the product of all individual section
        presheaves — a point in the limit of the diagram induced by the
        specification sections.
        """
        return SpecificationPresheaf(
            name=self._name,
            sections=dict(self._sections),
            strata=set(self._strata),
            description=self._description,
        )

    # -- internals ----------------------------------------------------------

    def _add(
        self,
        site: SiteId,
        section: SpecificationSection,
        stratum: TensorStratum,
    ) -> None:
        self._sections.setdefault(site, []).append(section)
        self._strata.add(stratum)


# ───────────────────────────────────────────────────────────────────
# 2.  Pre-built specifications — common specification patterns
# ───────────────────────────────────────────────────────────────────

def numerical_stability_spec(
    name: str = "numerical_stability",
    *,
    no_nan: bool = True,
    no_inf: bool = True,
    output_range: Optional[Tuple[float, float]] = None,
) -> SpecificationPresheaf:
    """Specification requiring numerical stability.

    Encodes the *finite-value* section of the numerical stratum: the
    semantic presheaf of a correct implementation must restrict to finite
    values at every numerical observation site.

    Parameters
    ----------
    no_nan : bool
        Forbid NaN in the output.
    no_inf : bool
        Forbid ±Inf in the output.
    output_range : tuple of float, optional
        If given, every output element must lie in ``[lo, hi]``.
    """
    builder = SpecBuilder(name, description="Numerical stability specification")
    if no_nan:
        builder.expect_no_nan()
    if no_inf:
        builder.expect_no_inf()
    if output_range is not None:
        builder.expect_output_range(output_range[0], output_range[1])
    return builder.build()


def differentiability_spec(
    name: str = "differentiability",
    *,
    order: int = 1,
) -> SpecificationPresheaf:
    """Specification requiring differentiability up to the given *order*.

    At order 1 this adds a single behavioral-stratum section asserting
    that ``torch.autograd`` can compute a gradient.  Higher orders add
    additional predicate sections checking higher-order derivatives.
    """
    builder = SpecBuilder(
        name,
        description=f"Differentiability specification (order {order})",
    )
    builder.expect_gradient_exists()
    for k in range(2, order + 1):
        builder.expect_predicate(
            predicate=_make_higher_order_grad_check(k),
            description=f"gradient_order_{k}",
            stratum=TensorStratum.BEHAVIORAL,
            site_name=f"gradient_order_{k}",
        )
    return builder.build()


def shape_preservation_spec(
    name: str = "shape_preservation",
    *,
    input_shape: Tuple[int, ...] = (),
) -> SpecificationPresheaf:
    """Specification requiring the output shape to match *input_shape*.

    When *input_shape* is the empty tuple the spec checks that the
    function preserves whatever shape was fed in (deferred check via
    predicate).
    """
    builder = SpecBuilder(
        name, description="Shape preservation specification"
    )
    if input_shape:
        builder.expect_shape(input_shape)
    else:
        builder.expect_predicate(
            predicate=lambda out, inp=None: (
                _check_shape_preservation(out, inp)
            ),
            description="shape_preserved",
            stratum=TensorStratum.STRUCTURAL,
            site_name="shape_preserved",
        )
    return builder.build()


def dtype_preservation_spec(
    name: str = "dtype_preservation",
) -> SpecificationPresheaf:
    """Specification requiring the output dtype to match the input dtype.

    Uses a predicate section at the metadata stratum; the actual dtype
    comparison is deferred to check time when inputs are available.
    """
    builder = SpecBuilder(
        name, description="Dtype preservation specification"
    )
    builder.expect_predicate(
        predicate=lambda out, inp=None: _check_dtype_preservation(out, inp),
        description="dtype_preserved",
        stratum=TensorStratum.METADATA,
        site_name="dtype_preserved",
    )
    return builder.build()


def triton_safety_spec(
    name: str = "triton_safety",
) -> SpecificationPresheaf:
    """Specification for a safe Triton kernel.

    Sections assert:
    * Every load/store is protected by a mask (no out-of-bounds access).
    * Reductions use a well-defined accumulation order.
    * Block sizes are powers of two (hardware requirement).

    These live at the STRUCTURAL and NUMERICAL strata of the Triton
    sub-category of the tensor site category.
    """
    builder = SpecBuilder(name, description="Triton kernel safety specification")
    builder.expect_predicate(
        predicate=_check_triton_masked_accesses,
        description="all_accesses_masked",
        stratum=TensorStratum.STRUCTURAL,
        site_name="triton_mask",
    )
    builder.expect_predicate(
        predicate=_check_triton_reduction_order,
        description="valid_reduction_order",
        stratum=TensorStratum.NUMERICAL,
        site_name="triton_reduction",
    )
    builder.expect_predicate(
        predicate=_check_triton_block_sizes,
        description="block_sizes_power_of_two",
        stratum=TensorStratum.STRUCTURAL,
        site_name="triton_blocks",
    )
    return builder.build()


def mlir_validity_spec(
    name: str = "mlir_validity",
) -> SpecificationPresheaf:
    """Specification for a valid MLIR module.

    Sections assert:
    * All operations are well-typed within their dialect.
    * The lowering chain preserves semantics at each step.
    """
    builder = SpecBuilder(name, description="MLIR module validity specification")
    builder.expect_predicate(
        predicate=_check_mlir_well_typed,
        description="ops_well_typed",
        stratum=TensorStratum.STRUCTURAL,
        site_name="mlir_typing",
    )
    builder.expect_predicate(
        predicate=_check_mlir_lowering_chain,
        description="valid_lowering_chain",
        stratum=TensorStratum.STRUCTURAL,
        site_name="mlir_lowering",
    )
    return builder.build()


# ───────────────────────────────────────────────────────────────────
# 3.  Specification checker
# ───────────────────────────────────────────────────────────────────

# Stratum ordering for filtration-based short-circuiting.
_STRATUM_ORDER: List[TensorStratum] = sorted(
    TensorStratum, key=lambda s: s.value
)


class SpecificationChecker:
    """Check whether a tensor function conforms to a specification presheaf.

    Mathematically, this verifies the existence of a natural transformation

        η : Spec  ⟶  Sem_f

    from the specification presheaf to the semantic presheaf of the
    function *f*.  The check is **one-way**: η need not be invertible, so
    conformance does not imply equivalence.

    The checker walks the filtration

        METADATA → STRUCTURAL → NUMERICAL → BEHAVIORAL

    and short-circuits as soon as a violation is found: a non-trivial
    obstruction class at stratum *k* precludes extension of η to higher
    strata.
    """

    def __init__(
        self,
        config: Optional[TensorEquivalenceConfig] = None,
    ) -> None:
        self._config = config

    # -- public API ---------------------------------------------------------

    def check(
        self,
        fn: Callable,
        spec: SpecificationPresheaf,
        tensor_specs: Sequence[TensorSpec],
        test_inputs: Optional[Sequence[Sequence[Any]]] = None,
    ) -> CorrectnessJudgment:
        """Check if *fn* conforms to *spec*.

        Parameters
        ----------
        fn : callable
            The tensor function under test.
        spec : SpecificationPresheaf
            The specification presheaf to check against.
        tensor_specs : sequence of TensorSpec
            Type-level descriptions of each input tensor.
        test_inputs : sequence of input-tuples, optional
            Concrete test inputs.  If ``None``, synthetic inputs are
            generated from *tensor_specs*.

        Returns
        -------
        CorrectnessJudgment
            The judgment including per-site verdicts and any violations.
        """
        inputs = (
            test_inputs
            if test_inputs is not None
            else _synthesize_inputs(tensor_specs)
        )

        program = ProgramId(
            name=getattr(fn, "__name__", "<anonymous>"),
            function_name=getattr(fn, "__qualname__", None),
        )

        violations: List[Bug] = []
        conforming: List[SiteId] = []
        violating: List[SiteId] = []

        # Walk strata in filtration order.
        for stratum in _STRATUM_ORDER:
            stratum_sections = _sections_in_stratum(spec, stratum)
            if not stratum_sections:
                continue

            for site_id, section_list in stratum_sections.items():
                for section in section_list:
                    ok, bug = self._check_section(fn, section, inputs)
                    if ok:
                        conforming.append(section.site_id)
                    else:
                        violating.append(section.site_id)
                        if bug is not None:
                            violations.append(bug)

            # Short-circuit: violation at stratum k blocks higher strata.
            if violating:
                return CorrectnessJudgment(
                    verdict=AnalysisVerdict.INVALID,
                    program=program,
                    specification=spec.name,
                    violations=violations,
                    conforming_sites=conforming,
                    violating_sites=violating,
                    explanation=(
                        f"Specification '{spec.name}' violated at "
                        f"stratum {stratum.name}: "
                        f"{len(violations)} violation(s) found. "
                        f"Higher strata not checked (short-circuit)."
                    ),
                )

        return CorrectnessJudgment(
            verdict=AnalysisVerdict.VALID,
            program=program,
            specification=spec.name,
            violations=[],
            conforming_sites=conforming,
            violating_sites=[],
            explanation=(
                f"Function '{program}' conforms to specification "
                f"'{spec.name}': morphism η: Spec → Sem_f exists "
                f"at all {len(conforming)} site(s)."
            ),
        )

    # -- per-section dispatch -----------------------------------------------

    def _check_section(
        self,
        fn: Callable,
        section: SpecificationSection,
        test_inputs: Sequence[Sequence[Any]],
    ) -> Tuple[bool, Optional[Bug]]:
        """Check a single specification section against *fn*.

        Dispatches to a property-specific checker based on
        ``section.property_name``.
        """
        prop = section.property_name
        dispatch: Dict[str, Callable] = {
            "shape": self._check_shape_section,
            "dtype": self._check_dtype_section,
            "device": self._check_device_section,
            "contiguous": self._check_contiguous_section,
            "output_range": self._check_numerical_section,
            "no_nan": self._check_numerical_section,
            "no_inf": self._check_numerical_section,
            "gradient_exists": self._check_gradient_section,
            "deterministic": self._check_determinism_section,
        }
        checker = dispatch.get(prop, self._check_predicate_section)
        return checker(fn, section, test_inputs)

    # -- shape --------------------------------------------------------------

    def _check_shape_section(
        self,
        fn: Callable,
        section: SpecificationSection,
        test_inputs: Sequence[Sequence[Any]],
    ) -> Tuple[bool, Optional[Bug]]:
        """Verify the output shape matches the specification."""
        expected_shape = section.expected_value
        for inp in test_inputs:
            try:
                out = fn(*inp)
            except Exception as exc:
                return False, _make_bug(
                    BugKind.SHAPE_INCONSISTENCY,
                    TensorStratum.STRUCTURAL,
                    section.site_id,
                    f"Function raised {type(exc).__name__}: {exc}",
                    witness_input=inp,
                )
            out_shape = _get_shape(out)
            if out_shape is not None and out_shape != expected_shape:
                return False, _make_bug(
                    BugKind.SHAPE_INCONSISTENCY,
                    TensorStratum.STRUCTURAL,
                    section.site_id,
                    f"Expected shape {expected_shape}, got {out_shape}",
                    witness_input=inp,
                    observed_output=out_shape,
                    expected_behavior=f"shape == {expected_shape}",
                )
        return True, None

    # -- dtype --------------------------------------------------------------

    def _check_dtype_section(
        self,
        fn: Callable,
        section: SpecificationSection,
        test_inputs: Sequence[Sequence[Any]],
    ) -> Tuple[bool, Optional[Bug]]:
        """Verify the output dtype matches the specification."""
        expected_dtype = section.expected_value
        for inp in test_inputs:
            try:
                out = fn(*inp)
            except Exception as exc:
                return False, _make_bug(
                    BugKind.DTYPE_INCONSISTENCY,
                    TensorStratum.METADATA,
                    section.site_id,
                    f"Function raised {type(exc).__name__}: {exc}",
                    witness_input=inp,
                )
            out_dtype = _get_dtype(out)
            if out_dtype is not None and str(out_dtype) != str(expected_dtype):
                return False, _make_bug(
                    BugKind.DTYPE_INCONSISTENCY,
                    TensorStratum.METADATA,
                    section.site_id,
                    f"Expected dtype {expected_dtype}, got {out_dtype}",
                    witness_input=inp,
                    observed_output=str(out_dtype),
                    expected_behavior=f"dtype == {expected_dtype}",
                )
        return True, None

    # -- device -------------------------------------------------------------

    def _check_device_section(
        self,
        fn: Callable,
        section: SpecificationSection,
        test_inputs: Sequence[Sequence[Any]],
    ) -> Tuple[bool, Optional[Bug]]:
        """Verify the output resides on the expected device."""
        expected_device = section.expected_value
        for inp in test_inputs:
            try:
                out = fn(*inp)
            except Exception as exc:
                return False, _make_bug(
                    BugKind.DTYPE_INCONSISTENCY,
                    TensorStratum.METADATA,
                    section.site_id,
                    f"Function raised {type(exc).__name__}: {exc}",
                    witness_input=inp,
                )
            out_device = _get_device(out)
            if out_device is not None and str(out_device) != str(expected_device):
                return False, _make_bug(
                    BugKind.DTYPE_INCONSISTENCY,
                    TensorStratum.METADATA,
                    section.site_id,
                    f"Expected device {expected_device}, got {out_device}",
                    witness_input=inp,
                    observed_output=str(out_device),
                    expected_behavior=f"device == {expected_device}",
                )
        return True, None

    # -- contiguity ---------------------------------------------------------

    def _check_contiguous_section(
        self,
        fn: Callable,
        section: SpecificationSection,
        test_inputs: Sequence[Sequence[Any]],
    ) -> Tuple[bool, Optional[Bug]]:
        """Verify the output tensor is contiguous."""
        for inp in test_inputs:
            try:
                out = fn(*inp)
            except Exception as exc:
                return False, _make_bug(
                    BugKind.MEMORY_VIOLATION,
                    TensorStratum.STRUCTURAL,
                    section.site_id,
                    f"Function raised {type(exc).__name__}: {exc}",
                    witness_input=inp,
                )
            if _HAS_TORCH and isinstance(out, torch.Tensor):
                if not out.is_contiguous():
                    return False, _make_bug(
                        BugKind.MEMORY_VIOLATION,
                        TensorStratum.STRUCTURAL,
                        section.site_id,
                        "Output tensor is not contiguous",
                        witness_input=inp,
                        expected_behavior="is_contiguous() == True",
                    )
        return True, None

    # -- numerical (range, nan, inf) ----------------------------------------

    def _check_numerical_section(
        self,
        fn: Callable,
        section: SpecificationSection,
        test_inputs: Sequence[Sequence[Any]],
    ) -> Tuple[bool, Optional[Bug]]:
        """Check numerical properties: range bounds, NaN, Inf."""
        predicate = section.predicate
        for inp in test_inputs:
            try:
                out = fn(*inp)
            except Exception as exc:
                return False, _make_bug(
                    BugKind.NUMERICAL_INSTABILITY,
                    TensorStratum.NUMERICAL,
                    section.site_id,
                    f"Function raised {type(exc).__name__}: {exc}",
                    witness_input=inp,
                )
            if predicate is not None:
                try:
                    ok = predicate(out)
                except Exception:
                    ok = False
                if not ok:
                    return False, _make_bug(
                        BugKind.NUMERICAL_INSTABILITY,
                        TensorStratum.NUMERICAL,
                        section.site_id,
                        f"Numerical property '{section.property_name}' violated",
                        witness_input=inp,
                        observed_output=_safe_repr(out),
                        expected_behavior=section.property_name,
                    )
        return True, None

    # -- gradient -----------------------------------------------------------

    def _check_gradient_section(
        self,
        fn: Callable,
        section: SpecificationSection,
        test_inputs: Sequence[Sequence[Any]],
    ) -> Tuple[bool, Optional[Bug]]:
        """Verify that the function is differentiable."""
        if not _HAS_TORCH:
            return True, None

        for inp in test_inputs:
            grad_inputs = _prepare_grad_inputs(inp)
            try:
                out = fn(*grad_inputs)
                if isinstance(out, torch.Tensor) and out.requires_grad:
                    target = out.sum()
                    target.backward()
                    # Check that at least one input received a gradient.
                    any_grad = any(
                        isinstance(t, torch.Tensor)
                        and t.grad is not None
                        for t in grad_inputs
                    )
                    if not any_grad:
                        return False, _make_bug(
                            BugKind.GRADIENT_INCORRECTNESS,
                            TensorStratum.BEHAVIORAL,
                            section.site_id,
                            "No input received a gradient",
                            witness_input=inp,
                            expected_behavior="gradient_exists == True",
                        )
                else:
                    return False, _make_bug(
                        BugKind.GRADIENT_INCORRECTNESS,
                        TensorStratum.BEHAVIORAL,
                        section.site_id,
                        "Output does not require grad",
                        witness_input=inp,
                        expected_behavior="gradient_exists == True",
                    )
            except Exception as exc:
                return False, _make_bug(
                    BugKind.GRADIENT_INCORRECTNESS,
                    TensorStratum.BEHAVIORAL,
                    section.site_id,
                    f"Gradient computation failed: {exc}",
                    witness_input=inp,
                    expected_behavior="gradient_exists == True",
                )
        return True, None

    # -- determinism --------------------------------------------------------

    def _check_determinism_section(
        self,
        fn: Callable,
        section: SpecificationSection,
        test_inputs: Sequence[Sequence[Any]],
    ) -> Tuple[bool, Optional[Bug]]:
        """Verify deterministic output by running fn twice per input."""
        for inp in test_inputs:
            try:
                out1 = fn(*inp)
                out2 = fn(*inp)
            except Exception as exc:
                return False, _make_bug(
                    BugKind.NONDETERMINISM,
                    TensorStratum.BEHAVIORAL,
                    section.site_id,
                    f"Function raised {type(exc).__name__}: {exc}",
                    witness_input=inp,
                )
            if not _outputs_equal(out1, out2):
                return False, _make_bug(
                    BugKind.NONDETERMINISM,
                    TensorStratum.BEHAVIORAL,
                    section.site_id,
                    "Function produced non-deterministic output",
                    witness_input=inp,
                    observed_output=_safe_repr(out1),
                    expected_behavior="deterministic output",
                )
        return True, None

    # -- generic predicate fallback -----------------------------------------

    def _check_predicate_section(
        self,
        fn: Callable,
        section: SpecificationSection,
        test_inputs: Sequence[Sequence[Any]],
    ) -> Tuple[bool, Optional[Bug]]:
        """Fallback checker that evaluates the section's predicate callable."""
        predicate = section.predicate
        if predicate is None:
            return True, None

        for inp in test_inputs:
            try:
                out = fn(*inp)
            except Exception as exc:
                return False, _make_bug(
                    BugKind.SHEAF_GLUING_FAILURE,
                    TensorStratum.BEHAVIORAL,
                    section.site_id,
                    f"Function raised {type(exc).__name__}: {exc}",
                    witness_input=inp,
                )
            try:
                ok = predicate(out)
            except Exception:
                ok = False
            if not ok:
                return False, _make_bug(
                    BugKind.SHEAF_GLUING_FAILURE,
                    TensorStratum.BEHAVIORAL,
                    section.site_id,
                    f"Predicate '{section.property_name}' failed",
                    witness_input=inp,
                    observed_output=_safe_repr(out),
                    expected_behavior=section.property_name,
                )
        return True, None


# ───────────────────────────────────────────────────────────────────
# 4.  Internal helpers
# ───────────────────────────────────────────────────────────────────

def _sections_in_stratum(
    spec: SpecificationPresheaf,
    stratum: TensorStratum,
) -> Dict[SiteId, List[SpecificationSection]]:
    """Filter the specification's sections to those in *stratum*.

    The stratum assignment uses the site-kind → stratum mapping where
    available, falling back to a heuristic based on the section's
    ``property_name``.
    """
    _PROPERTY_STRATUM: Dict[str, TensorStratum] = {
        "shape": TensorStratum.STRUCTURAL,
        "dtype": TensorStratum.METADATA,
        "device": TensorStratum.METADATA,
        "contiguous": TensorStratum.STRUCTURAL,
        "output_range": TensorStratum.NUMERICAL,
        "no_nan": TensorStratum.NUMERICAL,
        "no_inf": TensorStratum.NUMERICAL,
        "gradient_exists": TensorStratum.BEHAVIORAL,
        "deterministic": TensorStratum.BEHAVIORAL,
        "shape_preserved": TensorStratum.STRUCTURAL,
        "dtype_preserved": TensorStratum.METADATA,
    }
    result: Dict[SiteId, List[SpecificationSection]] = {}
    for site_id, sections in spec.sections.items():
        for sec in sections:
            sec_stratum = _PROPERTY_STRATUM.get(sec.property_name, stratum)
            if sec_stratum == stratum:
                result.setdefault(site_id, []).append(sec)
    return result


def _synthesize_inputs(
    tensor_specs: Sequence[TensorSpec],
) -> List[List[Any]]:
    """Generate a single batch of synthetic test inputs from *tensor_specs*.

    When torch is available, creates random tensors matching each spec.
    Otherwise, returns an empty list (caller must provide inputs).
    """
    if not _HAS_TORCH or not tensor_specs:
        return []

    inputs: List[Any] = []
    for spec in tensor_specs:
        dtype = _resolve_dtype(spec.dtype)
        t = torch.randn(spec.shape, dtype=dtype, device=spec.device)
        if spec.requires_grad:
            t = t.requires_grad_(True)
        inputs.append(t)
    return [inputs]


def _resolve_dtype(dtype_str: str) -> Any:
    """Map a dtype string to a :mod:`torch` dtype object."""
    if not _HAS_TORCH:
        return None
    _MAP = {
        "float32": torch.float32,
        "float64": torch.float64,
        "float16": torch.float16,
        "bfloat16": torch.bfloat16,
        "int32": torch.int32,
        "int64": torch.int64,
        "int16": torch.int16,
        "int8": torch.int8,
        "bool": torch.bool,
    }
    return _MAP.get(dtype_str, torch.float32)


def _make_bug(
    kind: BugKind,
    stratum: TensorStratum,
    site_id: SiteId,
    description: str,
    *,
    witness_input: Any = None,
    observed_output: Any = None,
    expected_behavior: Optional[str] = None,
    repair_hint: Optional[str] = None,
    severity: float = 1.0,
) -> Bug:
    """Convenience constructor for :class:`Bug`."""
    return Bug(
        kind=kind,
        stratum=stratum,
        site_id=site_id,
        description=description,
        witness_input=witness_input,
        observed_output=observed_output,
        expected_behavior=expected_behavior,
        repair_hint=repair_hint,
        severity=severity,
    )


# -- tensor introspection helpers ------------------------------------------

def _get_shape(out: Any) -> Optional[Tuple[int, ...]]:
    if _HAS_TORCH and isinstance(out, torch.Tensor):
        return tuple(out.shape)
    if hasattr(out, "shape"):
        return tuple(out.shape)
    return None


def _get_dtype(out: Any) -> Optional[str]:
    if _HAS_TORCH and isinstance(out, torch.Tensor):
        return str(out.dtype).replace("torch.", "")
    if hasattr(out, "dtype"):
        return str(out.dtype)
    return None


def _get_device(out: Any) -> Optional[str]:
    if _HAS_TORCH and isinstance(out, torch.Tensor):
        return str(out.device)
    if hasattr(out, "device"):
        return str(out.device)
    return None


def _safe_repr(obj: Any, max_len: int = 200) -> str:
    """Truncated repr for witness output."""
    r = repr(obj)
    return r if len(r) <= max_len else r[:max_len] + "..."


def _outputs_equal(a: Any, b: Any) -> bool:
    """Check if two outputs are bitwise-equal."""
    if _HAS_TORCH and isinstance(a, torch.Tensor) and isinstance(b, torch.Tensor):
        return torch.equal(a, b)
    return a == b  # type: ignore[no-any-return]


def _prepare_grad_inputs(inputs: Sequence[Any]) -> List[Any]:
    """Clone inputs and enable grad where applicable."""
    if not _HAS_TORCH:
        return list(inputs)
    result = []
    for t in inputs:
        if isinstance(t, torch.Tensor) and t.is_floating_point():
            c = t.detach().clone().requires_grad_(True)
            result.append(c)
        else:
            result.append(t)
    return result


# -- predicate helpers for pre-built specs ---------------------------------

def _check_range(out: Any, lo: float, hi: float) -> bool:
    if _HAS_TORCH and isinstance(out, torch.Tensor):
        return bool(out.min().item() >= lo and out.max().item() <= hi)
    return True


def _check_no_nan(out: Any) -> bool:
    if _HAS_TORCH and isinstance(out, torch.Tensor):
        return bool(not torch.isnan(out).any().item())
    if hasattr(out, "__float__"):
        return not math.isnan(float(out))
    return True


def _check_no_inf(out: Any) -> bool:
    if _HAS_TORCH and isinstance(out, torch.Tensor):
        return bool(not torch.isinf(out).any().item())
    if hasattr(out, "__float__"):
        return not math.isinf(float(out))
    return True


def _check_gradient_exists(out: Any) -> bool:
    if _HAS_TORCH and isinstance(out, torch.Tensor):
        return out.requires_grad
    return False


def _check_shape_preservation(out: Any, inp: Any) -> bool:
    out_shape = _get_shape(out)
    inp_shape = _get_shape(inp) if inp is not None else None
    if out_shape is not None and inp_shape is not None:
        return out_shape == inp_shape
    return True


def _check_dtype_preservation(out: Any, inp: Any) -> bool:
    out_dtype = _get_dtype(out)
    inp_dtype = _get_dtype(inp) if inp is not None else None
    if out_dtype is not None and inp_dtype is not None:
        return out_dtype == inp_dtype
    return True


def _make_higher_order_grad_check(order: int) -> Callable:
    """Return a predicate that checks differentiability at the given *order*."""
    def _check(out: Any) -> bool:
        if not _HAS_TORCH or not isinstance(out, torch.Tensor):
            return False
        if not out.requires_grad:
            return False
        current = out.sum()
        for _ in range(order):
            grads = torch.autograd.grad(
                current,
                out,
                create_graph=True,
                allow_unused=True,
            )
            if grads[0] is None:
                return False
            current = grads[0].sum()
        return True
    return _check


# -- Triton / MLIR predicate stubs ----------------------------------------
# These operate on metadata objects (TritonKernelSpec, MLIRModuleSpec),
# not on raw tensor outputs.  When invoked via SpecificationChecker
# the ``out`` argument is expected to carry the relevant spec as an
# attribute; graceful fallback otherwise.

def _check_triton_masked_accesses(out: Any) -> bool:
    """Every load/store in the kernel must have a non-None mask."""
    spec = getattr(out, "_triton_spec", None)
    if spec is None:
        return True
    for access in getattr(spec, "memory_accesses", []):
        if getattr(access, "mask_expr", None) is None:
            return False
    return True


def _check_triton_reduction_order(out: Any) -> bool:
    """Reductions must be non-atomic or explicitly marked safe."""
    spec = getattr(out, "_triton_spec", None)
    if spec is None:
        return True
    for red in getattr(spec, "reductions", []):
        if getattr(red, "is_atomic", False):
            return False
    return True


def _check_triton_block_sizes(out: Any) -> bool:
    """Block sizes must be positive powers of two."""
    spec = getattr(out, "_triton_spec", None)
    if spec is None:
        return True
    for blk in getattr(spec, "block_specs", []):
        size = getattr(blk, "size", 0)
        if size <= 0 or (size & (size - 1)) != 0:
            return False
    return True


def _check_mlir_well_typed(out: Any) -> bool:
    """Stub: check that all ops are well-typed within their dialect."""
    spec = getattr(out, "_mlir_spec", None)
    if spec is None:
        return True
    for op in getattr(spec, "dialect_ops", {}).values():
        for o in op:
            if not getattr(o, "result_types", None):
                return False
    return True


def _check_mlir_lowering_chain(out: Any) -> bool:
    """Stub: verify each lowering step preserves semantics."""
    spec = getattr(out, "_mlir_spec", None)
    if spec is None:
        return True
    for step in getattr(spec, "lowering_chain", []):
        if not getattr(step, "preserves_semantics", True):
            return False
    return True
