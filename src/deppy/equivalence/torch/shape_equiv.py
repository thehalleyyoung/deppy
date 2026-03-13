"""
Shape equivalence checker — broadcasting presheaf, dynamic shapes, reshape.

Models shape equivalence as a presheaf on the shape site category:
  - Objects: concrete shape tuples (n₁, n₂, ..., nₖ)
  - Morphisms: broadcasting maps (np.broadcast_shapes) and reshape maps
  - Sections: output shape functions σ_f, σ_g: input_shapes → output_shapes
  - Equivalence: ∀ input shapes s, σ_f(s) = σ_g(s) up to broadcasting

The shape lattice is a meet-semilattice under broadcasting:
  shape_a ∧ shape_b = broadcast_shapes(shape_a, shape_b)
Broadcasting is the restriction map in the Grothendieck topology.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Set, Tuple

from ._protocols import (
    AnalysisJudgment,
    AnalysisMode,
    AnalysisVerdict,
    Bug,
    BugKind,
    EquivalenceVerdict,
    ProgramId,
    SheafConditionResult,
    SiteId,
    SiteKind,
    TensorEquivalenceConfig,
    TensorLocalJudgment,
    TensorObstruction,
    TensorObstructionKind,
    TensorSiteKind,
    TensorSpec,
    TensorStratum,
)


# ---------------------------------------------------------------------------
# Shape operations (the shape semilattice)
# ---------------------------------------------------------------------------

def broadcast_shapes(*shapes: Tuple[int, ...]) -> Optional[Tuple[int, ...]]:
    """
    Compute the broadcast shape of multiple shapes.

    This is the *join* in the broadcasting lattice: the smallest shape
    that all input shapes can broadcast to.
    """
    try:
        import torch
        return tuple(torch.broadcast_shapes(*shapes))
    except Exception:
        pass

    # Fallback: manual broadcasting
    if not shapes:
        return ()
    max_ndim = max(len(s) for s in shapes)
    result = []
    for i in range(max_ndim):
        dims = []
        for s in shapes:
            idx = i - (max_ndim - len(s))
            if idx >= 0:
                dims.append(s[idx])
            else:
                dims.append(1)
        max_dim = max(dims)
        if any(d != 1 and d != max_dim for d in dims):
            return None  # Not broadcastable
        result.append(max_dim)
    return tuple(result)


def shapes_broadcastable(a: Tuple[int, ...], b: Tuple[int, ...]) -> bool:
    """Check if two shapes are broadcastable."""
    return broadcast_shapes(a, b) is not None


def shape_contains(outer: Tuple[int, ...], inner: Tuple[int, ...]) -> bool:
    """Check if outer shape broadcasts from inner (inner ≤ outer)."""
    result = broadcast_shapes(inner, outer)
    return result is not None and result == outer


def reshape_compatible(source: Tuple[int, ...], target: Tuple[int, ...]) -> bool:
    """Check if source can be reshaped to target (same numel)."""
    import math
    s_numel = math.prod(source) if source else 1
    t_numel = math.prod(target) if target else 1
    return s_numel == t_numel


def numel(shape: Tuple[int, ...]) -> int:
    """Number of elements in a shape."""
    import math
    return math.prod(shape) if shape else 1


# ---------------------------------------------------------------------------
# Dynamic shape handling
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SymbolicDim:
    """A symbolic dimension (for dynamic shapes like batch_size)."""
    name: str
    min_val: int = 0
    max_val: int = 2**31 - 1


@dataclass(frozen=True)
class SymbolicShape:
    """A shape with potentially symbolic dimensions."""
    dims: Tuple[Any, ...]  # int or SymbolicDim

    @property
    def rank(self) -> int:
        return len(self.dims)

    @property
    def is_concrete(self) -> bool:
        return all(isinstance(d, int) for d in self.dims)

    def concretize(self, bindings: Dict[str, int]) -> Tuple[int, ...]:
        """Substitute symbolic dims with concrete values."""
        result = []
        for d in self.dims:
            if isinstance(d, int):
                result.append(d)
            elif isinstance(d, SymbolicDim):
                result.append(bindings.get(d.name, d.min_val))
            else:
                result.append(int(d))
        return tuple(result)


def symbolic_shapes_compatible(a: SymbolicShape, b: SymbolicShape) -> bool:
    """Check if two symbolic shapes could be equal under some binding."""
    if a.rank != b.rank:
        return False
    for da, db in zip(a.dims, b.dims):
        if isinstance(da, int) and isinstance(db, int):
            if da != db:
                return False
        # If either is symbolic, they could match
    return True


# ---------------------------------------------------------------------------
# Shape inference oracle
# ---------------------------------------------------------------------------

class ShapeInferenceOracle:
    """
    Infers output shapes from input shapes using torch's shape inference.

    This is the *presheaf section* at a shape site: given an input shape
    observation, the oracle produces the output shape observation by
    running shape inference through torch.fx or meta tensors.
    """

    @staticmethod
    def infer_shapes(fn: Any, input_specs: Sequence[TensorSpec]) -> Optional[List[Tuple[int, ...]]]:
        """Infer output shapes by running fn on meta tensors."""
        try:
            import torch
        except ImportError:
            return None

        meta_inputs = []
        for spec in input_specs:
            dtype = getattr(torch, spec.dtype, torch.float32)
            try:
                meta_t = torch.empty(spec.shape, dtype=dtype, device="meta")
            except Exception:
                meta_t = torch.empty(spec.shape, dtype=dtype, device="cpu")
            meta_inputs.append(meta_t)

        try:
            out = fn(*meta_inputs)
        except Exception:
            # Fallback: try with actual small tensors
            try:
                small_inputs = []
                for spec in input_specs:
                    dtype = getattr(torch, spec.dtype, torch.float32)
                    if dtype.is_floating_point:
                        t = torch.randn(spec.shape, dtype=dtype)
                    else:
                        t = torch.zeros(spec.shape, dtype=dtype)
                    small_inputs.append(t)
                out = fn(*small_inputs)
            except Exception:
                return None

        # Extract shapes from output
        if isinstance(out, (tuple, list)):
            shapes = []
            for o in out:
                if hasattr(o, "shape"):
                    shapes.append(tuple(o.shape))
            return shapes
        elif hasattr(out, "shape"):
            return [tuple(out.shape)]
        return None

    @staticmethod
    def infer_shapes_symbolic(fn: Any, symbolic_inputs: Sequence[SymbolicShape],
                              n_samples: int = 5) -> Optional[List[SymbolicShape]]:
        """
        Infer output shapes symbolically by sampling concrete instantiations.

        This is the *stalk* computation: we sample points in the symbolic
        shape space and observe how the output shape varies.
        """
        try:
            import torch
        except ImportError:
            return None

        observed_shapes: List[List[Tuple[int, ...]]] = []
        symbolic_dims: Set[str] = set()
        for s in symbolic_inputs:
            for d in s.dims:
                if isinstance(d, SymbolicDim):
                    symbolic_dims.add(d.name)

        for sample_idx in range(n_samples):
            # Generate concrete bindings
            gen = torch.Generator().manual_seed(sample_idx + 100)
            bindings = {}
            for dim_name in sorted(symbolic_dims):
                val = torch.randint(1, 32, (1,), generator=gen).item()
                bindings[dim_name] = val

            concrete_shapes = [s.concretize(bindings) for s in symbolic_inputs]
            specs = [TensorSpec(shape=cs, dtype="float32") for cs in concrete_shapes]

            shapes = ShapeInferenceOracle.infer_shapes(fn, specs)
            if shapes is not None:
                observed_shapes.append(shapes)

        if not observed_shapes:
            return None

        # Check if output shapes are consistent
        first = observed_shapes[0]
        n_outputs = len(first)
        result = []
        for out_idx in range(n_outputs):
            ranks = set(len(obs[out_idx]) for obs in observed_shapes if out_idx < len(obs))
            if len(ranks) != 1:
                return None  # Rank varies — truly dynamic
            rank = ranks.pop()
            dims: List[Any] = []
            for dim_idx in range(rank):
                values = set(obs[out_idx][dim_idx] for obs in observed_shapes
                             if out_idx < len(obs))
                if len(values) == 1:
                    dims.append(values.pop())
                else:
                    dims.append(SymbolicDim(
                        name=f"out{out_idx}_d{dim_idx}",
                        min_val=min(values),
                        max_val=max(values),
                    ))
            result.append(SymbolicShape(dims=tuple(dims)))
        return result


# ---------------------------------------------------------------------------
# Shape equivalence checker
# ---------------------------------------------------------------------------

class ShapeEquivalenceChecker:
    """
    Checks shape equivalence of two tensor functions.

    This implements the local section comparison at shape sites:
    for each input shape in the test suite, compare the output shapes
    of fn_f and fn_g.  Shape equivalence is the coarsest stratum check
    and a necessary condition for numerical equivalence.

    Sheaf-theoretically, shape equivalence means the two presheaves
    F, G assign the same shape sections at every shape site:
    Γ(U_shape, F) = Γ(U_shape, G).
    """

    def __init__(self, config: TensorEquivalenceConfig):
        self._config = config
        self._oracle = ShapeInferenceOracle()

    def check_site(
        self,
        fn_f: Any,
        fn_g: Any,
        input_specs: Sequence[TensorSpec],
        site_id: SiteId,
    ) -> TensorLocalJudgment:
        """Check shape equivalence at a single shape site."""
        shapes_f = self._oracle.infer_shapes(fn_f, input_specs)
        shapes_g = self._oracle.infer_shapes(fn_g, input_specs)

        if shapes_f is None and shapes_g is None:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.STRUCTURAL,
                tensor_site_kind=TensorSiteKind.SHAPE,
                verdict=EquivalenceVerdict.UNKNOWN,
                explanation="Could not infer shapes for either function",
            )

        if shapes_f is None or shapes_g is None:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.STRUCTURAL,
                tensor_site_kind=TensorSiteKind.SHAPE,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation=(f"Shape inference failed for "
                             f"{'f' if shapes_f is None else 'g'}"),
                obstructions=(TensorObstruction(
                    kind=TensorObstructionKind.SHAPE_MISMATCH,
                    stratum=TensorStratum.STRUCTURAL,
                    sites=(site_id,),
                    description="One function fails shape inference",
                ),),
            )

        if len(shapes_f) != len(shapes_g):
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.STRUCTURAL,
                tensor_site_kind=TensorSiteKind.SHAPE,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation=(f"Different number of outputs: "
                             f"{len(shapes_f)} vs {len(shapes_g)}"),
                obstructions=(TensorObstruction(
                    kind=TensorObstructionKind.SHAPE_MISMATCH,
                    stratum=TensorStratum.STRUCTURAL,
                    sites=(site_id,),
                    description=f"Output count: {len(shapes_f)} vs {len(shapes_g)}",
                ),),
            )

        obstructions: List[TensorObstruction] = []
        for i, (sf, sg) in enumerate(zip(shapes_f, shapes_g)):
            if sf != sg:
                # Check if broadcastable (refinement, not equivalence)
                if shapes_broadcastable(sf, sg):
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.SHAPE_MISMATCH,
                        stratum=TensorStratum.STRUCTURAL,
                        sites=(site_id,),
                        description=(f"Output {i}: shapes differ but broadcastable: "
                                     f"{sf} vs {sg}"),
                        repair_hint="Shapes may be equivalent up to broadcasting",
                    ))
                else:
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.SHAPE_MISMATCH,
                        stratum=TensorStratum.STRUCTURAL,
                        sites=(site_id,),
                        description=f"Output {i}: {sf} vs {sg}",
                    ))

        if obstructions:
            # Check if all mismatches are broadcasting-compatible
            all_broadcast = all(o.repair_hint for o in obstructions)
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.STRUCTURAL,
                tensor_site_kind=TensorSiteKind.SHAPE,
                verdict=(EquivalenceVerdict.REFINED if all_broadcast
                         else EquivalenceVerdict.INEQUIVALENT),
                explanation="; ".join(o.description for o in obstructions),
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.STRUCTURAL,
            tensor_site_kind=TensorSiteKind.SHAPE,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation=f"Shapes match: {shapes_f}",
        )

    def check_broadcasting_equivalence(
        self,
        fn_f: Any,
        fn_g: Any,
        input_spec_sets: Sequence[Sequence[TensorSpec]],
        site_id: SiteId,
    ) -> TensorLocalJudgment:
        """
        Check that f and g agree on broadcasting behavior.

        Broadcasting is the canonical restriction morphism in the shape
        site category.  This checks that both functions produce the same
        output shape after broadcasting their inputs.
        """
        obstructions: List[TensorObstruction] = []

        for specs in input_spec_sets:
            shapes_f = self._oracle.infer_shapes(fn_f, specs)
            shapes_g = self._oracle.infer_shapes(fn_g, specs)
            if shapes_f != shapes_g:
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.SHAPE_MISMATCH,
                    stratum=TensorStratum.STRUCTURAL,
                    sites=(site_id,),
                    description=(f"Broadcasting disagreement: "
                                 f"f→{shapes_f}, g→{shapes_g}"),
                ))

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.STRUCTURAL,
                tensor_site_kind=TensorSiteKind.SHAPE,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation="Broadcasting behavior differs",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.STRUCTURAL,
            tensor_site_kind=TensorSiteKind.SHAPE,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation="Broadcasting behavior matches",
        )

    def check_dynamic_shapes(
        self,
        fn_f: Any,
        fn_g: Any,
        symbolic_inputs: Sequence[SymbolicShape],
        site_id: SiteId,
        n_samples: int = 10,
    ) -> TensorLocalJudgment:
        """
        Check shape equivalence under dynamic (symbolic) input shapes.

        Samples concrete instantiations and checks that output shapes
        agree for all samples.  This is the *stalk comparison* at the
        generic point of the shape site.
        """
        try:
            import torch
        except ImportError:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.STRUCTURAL,
                tensor_site_kind=TensorSiteKind.SHAPE,
                verdict=EquivalenceVerdict.UNKNOWN,
                explanation="PyTorch not available",
            )

        obstructions: List[TensorObstruction] = []

        symbolic_dims: Set[str] = set()
        for s in symbolic_inputs:
            for d in s.dims:
                if isinstance(d, SymbolicDim):
                    symbolic_dims.add(d.name)

        for sample_idx in range(n_samples):
            gen = torch.Generator().manual_seed(sample_idx + 200)
            bindings = {}
            for dim_name in sorted(symbolic_dims):
                val = torch.randint(1, 64, (1,), generator=gen).item()
                bindings[dim_name] = val

            concrete = [s.concretize(bindings) for s in symbolic_inputs]
            specs = [TensorSpec(shape=c, dtype="float32") for c in concrete]

            shapes_f = self._oracle.infer_shapes(fn_f, specs)
            shapes_g = self._oracle.infer_shapes(fn_g, specs)

            if shapes_f != shapes_g:
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.SHAPE_MISMATCH,
                    stratum=TensorStratum.STRUCTURAL,
                    sites=(site_id,),
                    description=(f"Shape mismatch at bindings {bindings}: "
                                 f"f→{shapes_f}, g→{shapes_g}"),
                ))

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.STRUCTURAL,
                tensor_site_kind=TensorSiteKind.SHAPE,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation=f"Dynamic shape disagreement ({len(obstructions)} samples)",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.STRUCTURAL,
            tensor_site_kind=TensorSiteKind.SHAPE,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation=f"Dynamic shapes agree across {n_samples} samples",
        )

    # ------------------------------------------------------------------
    # Single-program analysis
    # ------------------------------------------------------------------

    def analyze(
        self,
        fn: Any,
        input_specs: Sequence[TensorSpec],
        site_id: Optional[SiteId] = None,
    ) -> AnalysisJudgment:
        """Analyze a single function's shape behavior for consistency.

        Checks that the function produces consistent output shapes across
        different input shape variations within the broadcast lattice.
        A bug means the shape presheaf has inconsistent sections —
        the output dimensionality is not a well-defined function of
        the input shape stratum.
        """
        if site_id is None:
            site_id = SiteId(kind=SiteKind.TENSOR_SHAPE, name="shape_analysis")
        program = ProgramId(name="fn", function_name=getattr(fn, "__name__", "anonymous"))
        bugs: List[Bug] = []

        # Collect baseline output shapes from original specs
        baseline = self._oracle.infer_shapes(fn, input_specs)
        if baseline is None:
            return AnalysisJudgment(
                verdict=AnalysisVerdict.UNKNOWN,
                program=program,
                mode=AnalysisMode.BUG_FINDING,
                explanation="Shape inference failed on baseline inputs",
            )

        baseline_ranks = [len(s) for s in baseline]

        # Generate broadcast-varied input specs and check consistency
        varied_specs_list = self._broadcast_variations(input_specs)
        for varied_specs in varied_specs_list:
            result = self._oracle.infer_shapes(fn, varied_specs)
            if result is None:
                bugs.append(Bug(
                    kind=BugKind.SHAPE_INCONSISTENCY,
                    stratum=TensorStratum.STRUCTURAL,
                    site_id=site_id,
                    description=(
                        f"Shape inference fails on broadcast-varied inputs "
                        f"{[s.shape for s in varied_specs]}"
                    ),
                    witness_input=[s.shape for s in varied_specs],
                    expected_behavior="Shape inference should succeed for broadcastable inputs",
                ))
                continue

            # Check rank consistency
            result_ranks = [len(s) for s in result]
            if result_ranks != baseline_ranks:
                bugs.append(Bug(
                    kind=BugKind.SHAPE_INCONSISTENCY,
                    stratum=TensorStratum.STRUCTURAL,
                    site_id=site_id,
                    description=(
                        f"Output rank varies: baseline {baseline_ranks} vs "
                        f"{result_ranks} for inputs {[s.shape for s in varied_specs]}"
                    ),
                    witness_input=[s.shape for s in varied_specs],
                    observed_output=result,
                    expected_behavior=f"Consistent output rank {baseline_ranks}",
                ))
                continue

            # Check number of outputs
            if len(result) != len(baseline):
                bugs.append(Bug(
                    kind=BugKind.SHAPE_INCONSISTENCY,
                    stratum=TensorStratum.STRUCTURAL,
                    site_id=site_id,
                    description=(
                        f"Output count varies: {len(baseline)} vs {len(result)}"
                    ),
                    witness_input=[s.shape for s in varied_specs],
                    observed_output=result,
                    expected_behavior=f"Consistent output count {len(baseline)}",
                ))

        verdict = AnalysisVerdict.INVALID if bugs else AnalysisVerdict.VALID
        return AnalysisJudgment(
            verdict=verdict,
            program=program,
            mode=AnalysisMode.BUG_FINDING,
            bugs=bugs,
            stratum_results={TensorStratum.STRUCTURAL: verdict},
            explanation=(
                f"Found {len(bugs)} shape inconsistencies"
                if bugs else
                f"Shape presheaf consistent across {len(varied_specs_list)} variations"
            ),
        )

    @staticmethod
    def _broadcast_variations(
        specs: Sequence[TensorSpec], n_variations: int = 5,
    ) -> List[List[TensorSpec]]:
        """Generate broadcast-compatible input shape variations.

        All inputs are scaled by the *same* factor per dimension so that
        broadcastability relationships are preserved.
        """
        import random
        rng = random.Random(42)
        variations: List[List[TensorSpec]] = []
        if not specs:
            return variations
        max_rank = max(len(s.shape) for s in specs)
        for _ in range(n_variations):
            # Choose a uniform scale factor per dimension position
            factors = [rng.choice([1, 2]) for _ in range(max_rank)]
            varied: List[TensorSpec] = []
            for spec in specs:
                pad = max_rank - len(spec.shape)
                new_shape = tuple(
                    d * factors[pad + i] if d > 0 else d
                    for i, d in enumerate(spec.shape)
                )
                varied.append(TensorSpec(
                    shape=new_shape,
                    dtype=spec.dtype,
                    device=spec.device,
                    requires_grad=spec.requires_grad,
                ))
            variations.append(varied)
        return variations
