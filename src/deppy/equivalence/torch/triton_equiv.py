"""
Triton kernel equivalence checker — block-level presheaf comparison.

Models Triton kernel equivalence as a presheaf on the tiling site:
  - Objects: tile indices (block offsets in the grid)
  - Morphisms: tile refinement, mask sieves
  - Sections: per-tile computations
  - Equivalence: natural isomorphism between per-tile section presheaves

Two Triton kernels are equivalent iff:
  1. Structural equivalence: same tiling topology (fingerprint match)
  2. Memory access equivalence: same load/store patterns
  3. Reduction equivalence: same reduction operations (up to commutativity)
  4. Numerical equivalence: same output values on test inputs
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Tuple

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
    TensorStratum,
    TritonKernelSpec,
    TritonMemoryAccessPattern,
)

from .triton_ir import (
    KernelFingerprint,
    TilingTopology,
    TritonASTParser,
    TritonKernelAST,
    build_kernel_spec,
    compute_fingerprint,
    fingerprints_compatible,
    tiling_topologies_equivalent,
)
from .triton_counterexample import (
    BinOp,
    Cond,
    Expr,
    FnCall,
    Neg,
    Var,
    _ExprExtractor,
    _compare,
)


# ---------------------------------------------------------------------------
# Kernel comparison result
# ---------------------------------------------------------------------------

@dataclass
class KernelComparisonResult:
    """Result of comparing two Triton kernels."""
    structural_match: bool = False
    memory_match: bool = False
    reduction_match: bool = False
    tiling_match: bool = False
    computation_match: bool = False
    fingerprint_f: Optional[KernelFingerprint] = None
    fingerprint_g: Optional[KernelFingerprint] = None
    explanation: str = ""


# ---------------------------------------------------------------------------
# Structural kernel comparison
# ---------------------------------------------------------------------------

class TritonStructuralChecker:
    """
    Checks structural equivalence of two Triton kernels.

    Structural equivalence means the kernels have the same tiling topology,
    the same number and type of memory accesses, and the same reduction
    operations.  This is the *combinatorial* level of the tiling presheaf.
    """

    def __init__(self):
        self._parser = TritonASTParser()

    def compare(self, source_f: str, source_g: str,
                name_f: str = "kernel_f",
                name_g: str = "kernel_g") -> KernelComparisonResult:
        """Compare two kernels structurally."""
        ast_f = self._parser.parse(source_f, name_f)
        ast_g = self._parser.parse(source_g, name_g)

        fp_f = compute_fingerprint(ast_f)
        fp_g = compute_fingerprint(ast_g)

        computation_match = self._compare_store_computation(source_f, source_g)
        structural = fingerprints_compatible(fp_f, fp_g) and computation_match

        # Memory pattern comparison
        memory_match = self._compare_memory(ast_f, ast_g)

        # Reduction comparison
        reduction_match = self._compare_reductions(ast_f, ast_g)

        # Tiling topology
        spec_f = build_kernel_spec(source_f, name_f)
        spec_g = build_kernel_spec(source_g, name_g)
        topo_f = TilingTopology.from_kernel_spec(spec_f)
        topo_g = TilingTopology.from_kernel_spec(spec_g)
        tiling_match = tiling_topologies_equivalent(topo_f, topo_g)

        explanation_parts = []
        if not structural:
            explanation_parts.append(f"Fingerprint mismatch: {fp_f} vs {fp_g}")
        if not computation_match:
            explanation_parts.append("Per-tile store computation differs")
        if not memory_match:
            explanation_parts.append("Memory access pattern differs")
        if not reduction_match:
            explanation_parts.append("Reduction operations differ")
        if not tiling_match:
            explanation_parts.append("Tiling topology differs")

        return KernelComparisonResult(
            structural_match=structural,
            memory_match=memory_match,
            reduction_match=reduction_match,
            tiling_match=tiling_match,
            computation_match=computation_match,
            fingerprint_f=fp_f,
            fingerprint_g=fp_g,
            explanation="; ".join(explanation_parts) if explanation_parts
            else "Structurally equivalent",
        )

    def _compare_store_computation(self, source_f: str, source_g: str) -> bool:
        extractor_f = _ExprExtractor()
        extractor_g = _ExprExtractor()
        extractor_f.extract(source_f)
        extractor_g.extract(source_g)
        exprs_f = extractor_f.resolved_store_exprs()
        exprs_g = extractor_g.resolved_store_exprs()
        if len(exprs_f) != len(exprs_g):
            return False
        normalized_f = _alpha_normalize_exprs(exprs_f)
        normalized_g = _alpha_normalize_exprs(exprs_g)
        return all(
            _compare(expr_f, expr_g) is not None
            for expr_f, expr_g in zip(normalized_f, normalized_g)
        )

    def _compare_memory(self, ast_f: TritonKernelAST,
                        ast_g: TritonKernelAST) -> bool:
        """Compare memory access patterns."""
        if len(ast_f.loads) != len(ast_g.loads):
            return False
        if len(ast_f.stores) != len(ast_g.stores):
            return False
        # Check that both have masks in the same positions
        f_load_masks = [l.mask_expr is not None for l in ast_f.loads]
        g_load_masks = [l.mask_expr is not None for l in ast_g.loads]
        if f_load_masks != g_load_masks:
            return False
        f_store_masks = [s.mask_expr is not None for s in ast_f.stores]
        g_store_masks = [s.mask_expr is not None for s in ast_g.stores]
        if f_store_masks != g_store_masks:
            return False
        # Check atomics
        f_atomics = sum(1 for s in ast_f.stores if s.is_atomic)
        g_atomics = sum(1 for s in ast_g.stores if s.is_atomic)
        return f_atomics == g_atomics

    def _compare_reductions(self, ast_f: TritonKernelAST,
                            ast_g: TritonKernelAST) -> bool:
        """Compare reduction operations."""
        if len(ast_f.reductions) != len(ast_g.reductions):
            return False
        ops_f = sorted(r.op for r in ast_f.reductions)
        ops_g = sorted(r.op for r in ast_g.reductions)
        return ops_f == ops_g

    # ------------------------------------------------------------------
    # Single-program analysis
    # ------------------------------------------------------------------

    def analyze(self, source: str, name: str = "") -> AnalysisJudgment:
        """Analyze a single Triton kernel source for structural issues.

        Checks for unmasked memory accesses, missing boundary guards,
        and suspicious structural patterns.  This is single-presheaf
        analysis: does the kernel's tiling presheaf satisfy the sheaf
        condition (sections on tile boundaries glue correctly)?
        """
        site_id = SiteId(kind=SiteKind.TENSOR_INDEXING, name=f"triton_structural:{name or 'kernel'}")
        program = ProgramId(name=name or "kernel", function_name=name or "kernel")
        bugs: List[Bug] = []

        ast = self._parser.parse(source, name)

        # Check loads for masks
        for i, load in enumerate(ast.loads):
            if load.mask_expr is None:
                bugs.append(Bug(
                    kind=BugKind.UNMASKED_ACCESS,
                    stratum=TensorStratum.STRUCTURAL,
                    site_id=site_id,
                    description=f"Load {i} has no mask — potential OOB read at block boundary",
                    repair_hint="Add mask=offsets < N to tl.load()",
                    severity=0.8,
                ))

        # Check stores for masks
        for i, store in enumerate(ast.stores):
            if store.mask_expr is None:
                bugs.append(Bug(
                    kind=BugKind.UNMASKED_ACCESS,
                    stratum=TensorStratum.STRUCTURAL,
                    site_id=site_id,
                    description=f"Store {i} has no mask — potential OOB write at block boundary",
                    repair_hint="Add mask=offsets < N to tl.store()",
                    severity=1.0,
                ))

        # Check reduction associativity
        _NON_ASSOCIATIVE_OPS = {"sub", "div", "truediv"}
        for i, red in enumerate(ast.reductions):
            if red.op in _NON_ASSOCIATIVE_OPS:
                bugs.append(Bug(
                    kind=BugKind.REDUCTION_ORDER,
                    stratum=TensorStratum.NUMERICAL,
                    site_id=site_id,
                    description=(
                        f"Reduction {i} uses non-associative op '{red.op}'; "
                        f"parallel reduction order is undefined"
                    ),
                    repair_hint="Use associative ops (add, max, min) for reductions",
                ))

        verdict = AnalysisVerdict.INVALID if bugs else AnalysisVerdict.VALID
        return AnalysisJudgment(
            verdict=verdict,
            program=program,
            mode=AnalysisMode.BUG_FINDING,
            bugs=bugs,
            stratum_results={TensorStratum.STRUCTURAL: verdict},
            explanation=(
                f"Found {len(bugs)} structural issues in kernel"
                if bugs else
                "Kernel tiling presheaf is structurally well-formed"
            ),
        )


# ---------------------------------------------------------------------------
# Memory access pattern comparison
# ---------------------------------------------------------------------------

@dataclass
class MemoryAccessComparison:
    """Detailed comparison of memory access patterns."""
    loads_match: bool
    stores_match: bool
    coalescing_match: bool
    mask_match: bool
    explanation: str = ""


def compare_memory_patterns(spec_f: TritonKernelSpec,
                            spec_g: TritonKernelSpec) -> MemoryAccessComparison:
    """
    Compare memory access patterns of two Triton kernels.

    Memory access patterns determine GPU memory bandwidth utilization.
    Two kernels with different access patterns may produce the same
    results but with different performance characteristics.

    The mask comparison is **per-access**: two kernels with the same
    number of loads/stores but different per-element mask patterns
    are structurally different (the mask sieves generate different
    sub-covers of the tiling topology).
    """
    f_loads = [ma for ma in spec_f.memory_accesses if ma.kind == "load"]
    g_loads = [ma for ma in spec_g.memory_accesses if ma.kind == "load"]
    f_stores = [ma for ma in spec_f.memory_accesses if ma.kind == "store"]
    g_stores = [ma for ma in spec_g.memory_accesses if ma.kind == "store"]

    loads_match = len(f_loads) == len(g_loads)
    stores_match = len(f_stores) == len(g_stores)

    # Coalescing comparison (contiguous offset pattern heuristic)
    def _likely_contiguous(ma: TritonMemoryAccessPattern) -> bool:
        return "offsets" in (ma.offsets_expr or "") or "arange" in (ma.offsets_expr or "")
    f_coalesced = all(_likely_contiguous(ma) for ma in spec_f.memory_accesses)
    g_coalesced = all(_likely_contiguous(ma) for ma in spec_g.memory_accesses)
    coalescing_match = f_coalesced == g_coalesced

    # Per-access mask comparison (position-aligned)
    mask_match = True
    if loads_match:
        f_load_masks = [l.mask_expr is not None for l in f_loads]
        g_load_masks = [l.mask_expr is not None for l in g_loads]
        if f_load_masks != g_load_masks:
            mask_match = False
    if stores_match:
        f_store_masks = [s.mask_expr is not None for s in f_stores]
        g_store_masks = [s.mask_expr is not None for s in g_stores]
        if f_store_masks != g_store_masks:
            mask_match = False

    parts = []
    if not loads_match:
        parts.append(f"Load count: {len(f_loads)} vs {len(g_loads)}")
    if not stores_match:
        parts.append(f"Store count: {len(f_stores)} vs {len(g_stores)}")
    if not coalescing_match:
        parts.append(f"Coalescing: f={f_coalesced}, g={g_coalesced}")
    if not mask_match:
        parts.append(f"Mask sieve mismatch: per-access mask patterns differ")

    return MemoryAccessComparison(
        loads_match=loads_match,
        stores_match=stores_match,
        coalescing_match=coalescing_match,
        mask_match=mask_match,
        explanation="; ".join(parts) if parts else "Memory patterns match",
    )


# ---------------------------------------------------------------------------
# Triton equivalence checker
# ---------------------------------------------------------------------------

class TritonEquivalenceChecker:
    """
    Checks equivalence of two Triton GPU kernels.

    This implements the presheaf comparison on the tiling site category:
    1. Parse both kernels into ASTs
    2. Compare structural fingerprints (combinatorial topology)
    3. Compare memory access patterns (coalescing, masking)
    4. Compare reduction operations (commutativity, associativity)
    5. Compare tiling topology (block sizes, grid shapes)

    Sheaf-theoretically, two kernels are equivalent iff their per-block
    section presheaves are naturally isomorphic.  This means:
    - At each tile, the computations are equivalent
    - On tile overlaps (boundary regions), the mask sieves agree
    - The reduction operations glue consistently across tiles
    """

    def __init__(self, config: TensorEquivalenceConfig):
        self._config = config
        self._structural = TritonStructuralChecker()

    def check_site(
        self,
        spec_f: TritonKernelSpec,
        spec_g: TritonKernelSpec,
        site_id: SiteId,
    ) -> TensorLocalJudgment:
        """Check Triton kernel equivalence at a site."""
        obstructions: List[TensorObstruction] = []

        # 1. Structural comparison
        if spec_f.source_code and spec_g.source_code:
            result = self._structural.compare(
                spec_f.source_code, spec_g.source_code,
                spec_f.name, spec_g.name,
            )

            if not result.structural_match:
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.TRITON_BLOCK_MISMATCH,
                    stratum=TensorStratum.STRUCTURAL,
                    sites=(site_id,),
                    description=f"Structural: {result.explanation}",
                ))

            if not result.memory_match:
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.TRITON_MASK_MISMATCH,
                    stratum=TensorStratum.STRUCTURAL,
                    sites=(site_id,),
                    description="Memory access patterns differ",
                ))

            if not result.reduction_match:
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.TRITON_REDUCTION_ORDER,
                    stratum=TensorStratum.NUMERICAL,
                    sites=(site_id,),
                    description="Reduction operations differ",
                ))

        # 2. Kernel config comparison
        config_obs = self._compare_configs(spec_f, spec_g, site_id)
        obstructions.extend(config_obs)

        # 3. Memory pattern comparison
        mem_result = compare_memory_patterns(spec_f, spec_g)
        if not (mem_result.loads_match and mem_result.stores_match
                and mem_result.mask_match):
            obstructions.append(TensorObstruction(
                kind=TensorObstructionKind.TRITON_MASK_MISMATCH,
                stratum=TensorStratum.STRUCTURAL,
                sites=(site_id,),
                description=f"Memory: {mem_result.explanation}",
            ))

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.STRUCTURAL,
                tensor_site_kind=TensorSiteKind.TRITON_BLOCK,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation=f"Triton kernel differs ({len(obstructions)} issues)",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.STRUCTURAL,
            tensor_site_kind=TensorSiteKind.TRITON_BLOCK,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation="Triton kernels structurally equivalent",
        )

    def check_reduction_site(
        self,
        spec_f: TritonKernelSpec,
        spec_g: TritonKernelSpec,
        site_id: SiteId,
    ) -> TensorLocalJudgment:
        """
        Check Triton reduction equivalence at a reduction site.

        Reduction operations are the key source of non-commutativity
        in GPU kernels.  Two kernels may use different reduction orders
        (e.g., tree reduction vs sequential) that produce different
        floating-point results.
        """
        obstructions: List[TensorObstruction] = []

        reds_f = list(spec_f.reductions)
        reds_g = list(spec_g.reductions)

        if len(reds_f) != len(reds_g):
            obstructions.append(TensorObstruction(
                kind=TensorObstructionKind.TRITON_REDUCTION_ORDER,
                stratum=TensorStratum.NUMERICAL,
                sites=(site_id,),
                description=(f"Different number of reductions: "
                             f"{len(reds_f)} vs {len(reds_g)}"),
            ))
        else:
            for i, (rf, rg) in enumerate(zip(reds_f, reds_g)):
                if rf.op != rg.op:
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.TRITON_REDUCTION_ORDER,
                        stratum=TensorStratum.NUMERICAL,
                        sites=(site_id,),
                        description=(f"Reduction {i}: op differs: "
                                     f"{rf.op} vs {rg.op}"),
                    ))
                if rf.axis != rg.axis:
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.TRITON_REDUCTION_ORDER,
                        stratum=TensorStratum.NUMERICAL,
                        sites=(site_id,),
                        description=(f"Reduction {i}: axis differs: "
                                     f"{rf.axis} vs {rg.axis}"),
                    ))

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.NUMERICAL,
                tensor_site_kind=TensorSiteKind.TRITON_REDUCTION,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation="Reduction operations differ",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.NUMERICAL,
            tensor_site_kind=TensorSiteKind.TRITON_REDUCTION,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation="Reduction operations match",
        )
    def _compare_configs(self, spec_f: TritonKernelSpec,
                         spec_g: TritonKernelSpec,
                         site_id: SiteId) -> List[TensorObstruction]:
        """Compare kernel launch configurations."""
        obs: List[TensorObstruction] = []

        if spec_f.num_warps != spec_g.num_warps:
            obs.append(TensorObstruction(
                kind=TensorObstructionKind.TRITON_BLOCK_MISMATCH,
                stratum=TensorStratum.STRUCTURAL,
                sites=(site_id,),
                description=(f"num_warps: {spec_f.num_warps} vs "
                             f"{spec_g.num_warps}"),
                repair_hint="Different warp counts may still be functionally equivalent",
            ))

        if spec_f.num_stages != spec_g.num_stages:
            obs.append(TensorObstruction(
                kind=TensorObstructionKind.TRITON_BLOCK_MISMATCH,
                stratum=TensorStratum.STRUCTURAL,
                sites=(site_id,),
                description=(f"num_stages: {spec_f.num_stages} vs "
                             f"{spec_g.num_stages}"),
                repair_hint="Different pipeline stages may still be functionally equivalent",
            ))

        # Compare block specs
        f_blocks = sorted(spec_f.block_specs, key=lambda b: b.name)
        g_blocks = sorted(spec_g.block_specs, key=lambda b: b.name)

        if len(f_blocks) != len(g_blocks):
            obs.append(TensorObstruction(
                kind=TensorObstructionKind.TRITON_BLOCK_MISMATCH,
                stratum=TensorStratum.STRUCTURAL,
                sites=(site_id,),
                description=(f"Block count: {len(f_blocks)} vs "
                             f"{len(g_blocks)}"),
            ))
        else:
            for bf, bg in zip(f_blocks, g_blocks):
                if bf.size != bg.size:
                    obs.append(TensorObstruction(
                        kind=TensorObstructionKind.TRITON_BLOCK_MISMATCH,
                        stratum=TensorStratum.STRUCTURAL,
                        sites=(site_id,),
                        description=(f"Block {bf.name}: size {bf.size} vs "
                                     f"{bg.name}: size {bg.size}"),
                        repair_hint="Different block sizes may tile equivalently",
                    ))

        return obs

    # ------------------------------------------------------------------
    # Single-program analysis
    # ------------------------------------------------------------------

    def analyze(
        self,
        spec: TritonKernelSpec,
        site_id: Optional[SiteId] = None,
    ) -> AnalysisJudgment:
        """Analyze a single Triton kernel for common bugs.

        Checks for unmasked boundary accesses, non-associative reductions,
        and structural issues.  This is single-program bug-finding: the
        kernel's tiling presheaf is checked for well-formedness without
        comparing to a second kernel.
        """
        if site_id is None:
            site_id = SiteId(kind=SiteKind.TENSOR_INDEXING, name=f"triton_analysis:{spec.name}")
        program = ProgramId(name=spec.name, function_name=spec.name)
        bugs: List[Bug] = []

        # Delegate structural analysis if source code is available
        if spec.source_code:
            structural = self._structural.analyze(spec.source_code, spec.name)
            bugs.extend(structural.bugs)

        # Check memory access patterns for unmasked accesses
        for i, ma in enumerate(spec.memory_accesses):
            if not ma.mask_expr:
                kind_label = ma.kind if hasattr(ma, 'kind') else "access"
                bugs.append(Bug(
                    kind=BugKind.UNMASKED_ACCESS,
                    stratum=TensorStratum.STRUCTURAL,
                    site_id=site_id,
                    description=(
                        f"Memory {kind_label} {i} at '{ma.offsets_expr}' "
                        f"has no mask — OOB access at block boundary"
                    ),
                    repair_hint="Add mask parameter to tl.load/tl.store",
                ))

        # Check block sizes are powers of two (required by Triton)
        for bs in spec.block_specs:
            if bs.size > 0 and (bs.size & (bs.size - 1)) != 0:
                bugs.append(Bug(
                    kind=BugKind.SHEAF_GLUING_FAILURE,
                    stratum=TensorStratum.STRUCTURAL,
                    site_id=site_id,
                    description=(
                        f"Block '{bs.name}' size {bs.size} is not a power of 2"
                    ),
                    repair_hint="Triton block sizes must be powers of 2",
                ))

        # Check reduction operations for non-associativity
        _NON_ASSOC = {"sub", "div", "truediv"}
        for i, red in enumerate(spec.reductions):
            if red.op in _NON_ASSOC:
                bugs.append(Bug(
                    kind=BugKind.REDUCTION_ORDER,
                    stratum=TensorStratum.NUMERICAL,
                    site_id=site_id,
                    description=(
                        f"Reduction {i} (op='{red.op}', axis={red.axis}) "
                        f"is non-associative; parallel execution order matters"
                    ),
                    repair_hint="Use associative operations for GPU reductions",
                ))

        verdict = AnalysisVerdict.INVALID if bugs else AnalysisVerdict.VALID
        return AnalysisJudgment(
            verdict=verdict,
            program=program,
            mode=AnalysisMode.BUG_FINDING,
            bugs=bugs,
            stratum_results={TensorStratum.STRUCTURAL: verdict},
            explanation=(
                f"Found {len(bugs)} issues in Triton kernel '{spec.name}'"
                if bugs else
                f"Triton kernel '{spec.name}' tiling presheaf is well-formed"
            ),
        )


def _alpha_normalize_exprs(exprs: Sequence[Expr]) -> List[Expr]:
    env: Dict[str, str] = {}
    next_index = [0]
    return [_alpha_normalize_expr(expr, env, next_index) for expr in exprs]


def _alpha_normalize_expr(
    expr: Expr,
    env: Dict[str, str],
    next_index: List[int],
) -> Expr:
    if isinstance(expr, Var):
        alias = env.get(expr.name)
        if alias is None:
            alias = f"v{next_index[0]}"
            env[expr.name] = alias
            next_index[0] += 1
        return Var(alias)
    if isinstance(expr, BinOp):
        return BinOp(
            expr.op,
            _alpha_normalize_expr(expr.left, env, next_index),
            _alpha_normalize_expr(expr.right, env, next_index),
        )
    if isinstance(expr, Neg):
        return Neg(_alpha_normalize_expr(expr.arg, env, next_index))
    if isinstance(expr, FnCall):
        return FnCall(
            expr.func,
            tuple(_alpha_normalize_expr(arg, env, next_index) for arg in expr.args),
            tuple(
                (name, _alpha_normalize_expr(arg, env, next_index))
                for name, arg in expr.kwargs
            ),
        )
    if isinstance(expr, Cond):
        return Cond(
            _alpha_normalize_expr(expr.test, env, next_index),
            _alpha_normalize_expr(expr.if_true, env, next_index),
            _alpha_normalize_expr(expr.if_false, env, next_index),
        )
    return expr
