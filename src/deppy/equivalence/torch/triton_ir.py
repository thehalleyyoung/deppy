"""
Triton IR analysis — kernel AST parsing, block structure, memory access patterns.

Models a Triton kernel as a presheaf on the tiling site category:
  - Objects: (block_name, block_size, axis) triples
  - Morphisms: tile refinement (subdividing blocks), mask sieves
  - Sections: per-block computations (the kernel body at each tile)
  - Equivalence: sections agree on all tiles (up to reordering)

Since Triton may not be installed, this module works via AST analysis
of the kernel source code, extracting structural information without
actually importing Triton.

The tiling topology is a Grothendieck topology: a cover is a complete
tiling of the input space; morphisms between covers are tile refinements.
Masks generate sieves (sub-covers that exclude boundary tiles).
"""

from __future__ import annotations

import ast
import hashlib
import re
import textwrap
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

from ._protocols import (
    TritonBlockSpec,
    TritonKernelSpec,
    TritonMemoryAccessPattern,
    TritonReductionSpec,
    TensorSiteKind,
)


# ---------------------------------------------------------------------------
# Triton AST analysis
# ---------------------------------------------------------------------------

@dataclass
class TritonLoadStore:
    """A load or store operation in a Triton kernel."""
    pointer_name: str
    is_load: bool
    mask_expr: Optional[str] = None
    other_expr: Optional[str] = None
    eviction_policy: Optional[str] = None
    is_atomic: bool = False


@dataclass
class TritonReduction:
    """A reduction operation in a Triton kernel."""
    op: str  # "sum", "max", "min", etc.
    axis: int
    input_expr: str


@dataclass
class TritonArange:
    """A tl.arange() call — defines block offsets."""
    start: int
    end: Any  # int or BLOCK_SIZE symbol


@dataclass
class TritonKernelAST:
    """Parsed AST of a Triton kernel."""
    name: str
    params: List[str]
    constexpr_params: List[str]
    block_sizes: Dict[str, Any]  # param_name → size or expression
    loads: List[TritonLoadStore]
    stores: List[TritonLoadStore]
    reductions: List[TritonReduction]
    aranges: List[TritonArange]
    conditionals: List[str]  # mask conditions
    n_statements: int = 0
    source_hash: str = ""


class TritonASTParser:
    """
    Parses Triton kernel source code into a TritonKernelAST.

    Works without importing Triton — purely syntactic analysis.
    This is the *observation functor*: from source code, we extract
    the structural information visible at each site kind (block,
    memory, reduction, etc.).
    """

    def parse(self, source: str, name: str = "") -> TritonKernelAST:
        """Parse a Triton kernel's source code."""
        source = textwrap.dedent(source)
        h = hashlib.sha256(source.encode()).hexdigest()[:16]

        try:
            tree = ast.parse(source)
        except SyntaxError:
            return TritonKernelAST(
                name=name, params=[], constexpr_params=[],
                block_sizes={}, loads=[], stores=[],
                reductions=[], aranges=[], conditionals=[],
                source_hash=h,
            )

        # Find the kernel function
        kernel_fn = None
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                # Check for @triton.jit or @jit decorator
                for dec in node.decorator_list:
                    dec_name = self._get_decorator_name(dec)
                    if dec_name and ("jit" in dec_name.lower() or "triton" in dec_name.lower()):
                        kernel_fn = node
                        break
                if kernel_fn is None:
                    kernel_fn = node  # Take the first function as fallback
                break

        if kernel_fn is None:
            return TritonKernelAST(
                name=name, params=[], constexpr_params=[],
                block_sizes={}, loads=[], stores=[],
                reductions=[], aranges=[], conditionals=[],
                source_hash=h,
            )

        # Extract parameters
        params = [arg.arg for arg in kernel_fn.args.args]

        # Identify constexpr params (annotated with tl.constexpr)
        constexpr_params = []
        for arg in kernel_fn.args.args:
            if arg.annotation:
                ann = ast.dump(arg.annotation)
                if "constexpr" in ann.lower():
                    constexpr_params.append(arg.arg)

        # Also identify BLOCK_SIZE-like params
        block_sizes: Dict[str, Any] = {}
        for p in params:
            upper = p.upper()
            if "BLOCK" in upper or "TILE" in upper:
                block_sizes[p] = None  # Size unknown without runtime info
                if p not in constexpr_params:
                    constexpr_params.append(p)

        # Walk body for loads, stores, reductions, aranges
        loads: List[TritonLoadStore] = []
        stores: List[TritonLoadStore] = []
        reductions: List[TritonReduction] = []
        aranges: List[TritonArange] = []
        conditionals: List[str] = []
        n_stmts = 0

        for node in ast.walk(kernel_fn):
            if isinstance(node, ast.Expr) or isinstance(node, ast.Assign):
                n_stmts += 1

            if isinstance(node, ast.Call):
                call_name = self._get_call_name(node)
                if call_name:
                    # tl.load / tl.store
                    if call_name in ("tl.load", "load"):
                        ls = self._parse_load_store(node, is_load=True)
                        if ls:
                            loads.append(ls)
                    elif call_name in ("tl.store", "store"):
                        ls = self._parse_load_store(node, is_load=False)
                        if ls:
                            stores.append(ls)
                    # tl.sum, tl.max, tl.min
                    elif call_name in ("tl.sum", "tl.max", "tl.min",
                                       "sum", "max", "min"):
                        red = self._parse_reduction(node, call_name)
                        if red:
                            reductions.append(red)
                    # tl.arange
                    elif call_name in ("tl.arange", "arange"):
                        ar = self._parse_arange(node)
                        if ar:
                            aranges.append(ar)
                    # Atomic operations
                    elif "atomic" in call_name:
                        ls = self._parse_load_store(node, is_load=False)
                        if ls:
                            ls.is_atomic = True
                            stores.append(ls)

            # Conditionals (mask conditions)
            if isinstance(node, ast.If):
                conditionals.append(ast.dump(node.test))

        return TritonKernelAST(
            name=name or kernel_fn.name,
            params=params,
            constexpr_params=constexpr_params,
            block_sizes=block_sizes,
            loads=loads,
            stores=stores,
            reductions=reductions,
            aranges=aranges,
            conditionals=conditionals,
            n_statements=n_stmts,
            source_hash=h,
        )

    def _get_decorator_name(self, node: ast.expr) -> Optional[str]:
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            return f"{self._get_decorator_name(node.value)}.{node.attr}"
        if isinstance(node, ast.Call):
            return self._get_decorator_name(node.func)
        return None

    def _get_call_name(self, node: ast.Call) -> Optional[str]:
        if isinstance(node.func, ast.Name):
            return node.func.id
        if isinstance(node.func, ast.Attribute):
            val = self._get_expr_name(node.func.value)
            if val:
                return f"{val}.{node.func.attr}"
            return node.func.attr
        return None

    def _get_expr_name(self, node: ast.expr) -> Optional[str]:
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            val = self._get_expr_name(node.value)
            if val:
                return f"{val}.{node.attr}"
        return None

    def _parse_load_store(self, node: ast.Call,
                          is_load: bool) -> Optional[TritonLoadStore]:
        if not node.args:
            return None
        ptr_name = self._get_expr_name(node.args[0]) or ast.dump(node.args[0])
        mask = None
        other = None
        for kw in node.keywords:
            if kw.arg == "mask":
                mask = ast.dump(kw.value)
            elif kw.arg == "other":
                other = ast.dump(kw.value)
        # Positional mask argument:
        #   tl.load(ptr, mask, other, ...)   → mask is args[1]
        #   tl.store(ptr, value, mask, ...)  → mask is args[2]
        if mask is None:
            mask_pos = 1 if is_load else 2
            if len(node.args) > mask_pos:
                mask = ast.dump(node.args[mask_pos])
        return TritonLoadStore(
            pointer_name=ptr_name,
            is_load=is_load,
            mask_expr=mask,
            other_expr=other,
        )

    def _parse_reduction(self, node: ast.Call,
                         call_name: str) -> Optional[TritonReduction]:
        op = call_name.split(".")[-1]
        axis = 0
        input_expr = ""
        if node.args:
            input_expr = ast.dump(node.args[0])
        for kw in node.keywords:
            if kw.arg == "axis":
                if isinstance(kw.value, ast.Constant):
                    axis = kw.value.value
        if len(node.args) > 1:
            if isinstance(node.args[1], ast.Constant):
                axis = node.args[1].value
        return TritonReduction(op=op, axis=axis, input_expr=input_expr)

    def _parse_arange(self, node: ast.Call) -> Optional[TritonArange]:
        if len(node.args) >= 2:
            start = 0
            end = None
            if isinstance(node.args[0], ast.Constant):
                start = node.args[0].value
            if isinstance(node.args[1], ast.Constant):
                end = node.args[1].value
            elif isinstance(node.args[1], ast.Name):
                end = node.args[1].id
            return TritonArange(start=start, end=end)
        return None


# ---------------------------------------------------------------------------
# Kernel spec builder
# ---------------------------------------------------------------------------

def build_kernel_spec(source: str, name: str = "",
                      grid: Optional[Tuple] = None,
                      num_warps: int = 4,
                      num_stages: int = 2) -> TritonKernelSpec:
    """
    Build a TritonKernelSpec from source code.

    This is the *observation map* from source code to the kernel site.
    """
    parser = TritonASTParser()
    kernel_ast = parser.parse(source, name=name)

    block_specs = []
    for bname, bsize in kernel_ast.block_sizes.items():
        block_specs.append(TritonBlockSpec(
            name=bname,
            size=bsize or 256,  # Default block size
            constexpr=bname in kernel_ast.constexpr_params,
            power_of_two=True,  # Triton convention
        ))

    memory_accesses = []
    for load in kernel_ast.loads:
        ptr_base = load.pointer_name.split("+")[0].split("[")[0].strip()
        # Remove AST dump artifacts from pointer base
        if "(" in ptr_base:
            ptr_base = load.pointer_name
        memory_accesses.append(TritonMemoryAccessPattern(
            kind="load",
            pointer_name=ptr_base,
            offsets_expr=load.pointer_name,
            mask_expr=load.mask_expr,
            eviction_policy=load.eviction_policy,
        ))
    for store in kernel_ast.stores:
        ptr_base = store.pointer_name.split("+")[0].split("[")[0].strip()
        if "(" in ptr_base:
            ptr_base = store.pointer_name
        memory_accesses.append(TritonMemoryAccessPattern(
            kind="store",
            pointer_name=ptr_base,
            offsets_expr=store.pointer_name,
            mask_expr=store.mask_expr,
            eviction_policy=store.eviction_policy,
        ))

    reductions = []
    for red in kernel_ast.reductions:
        reductions.append(TritonReductionSpec(
            op=red.op,
            axis=red.axis,
            input_name=red.input_expr,
            is_atomic=False,
        ))

    return TritonKernelSpec(
        name=kernel_ast.name or name,
        grid=grid or (1,),
        block_specs=tuple(block_specs),
        num_warps=num_warps,
        num_stages=num_stages,
        shared_memory_bytes=0,
        memory_accesses=tuple(memory_accesses),
        reductions=tuple(reductions),
        constexpr_params={p: None for p in kernel_ast.constexpr_params},
        source_code=source,
    )


# ---------------------------------------------------------------------------
# Kernel structural fingerprint
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class KernelFingerprint:
    """
    Structural fingerprint of a Triton kernel.

    Captures the essential structure visible at the block/memory/reduction
    sites, abstracting away variable names and minor syntactic differences.
    Two kernels with the same fingerprint are structurally equivalent
    (same tiling topology).
    """
    n_loads: int
    n_stores: int
    n_reductions: int
    n_blocks: int
    n_atomics: int
    reduction_ops: Tuple[str, ...]
    has_mask: bool
    n_conditionals: int
    source_hash: str


def compute_fingerprint(kernel_ast: Any) -> KernelFingerprint:
    """Compute structural fingerprint of a parsed kernel.

    Accepts both ``TritonKernelAST`` (parser output) and
    ``TritonKernelSpec`` (spec output).
    """
    n_atomics = sum(1 for s in kernel_ast.stores if getattr(s, 'is_volatile', False))
    has_mask = any(
        getattr(l, 'mask_expr', None) is not None
        for l in list(kernel_ast.loads) + list(kernel_ast.stores)
    )
    reduction_ops = tuple(sorted(set(r.op for r in kernel_ast.reductions)))

    if hasattr(kernel_ast, 'block_sizes'):
        n_blocks = len(kernel_ast.block_sizes)
    elif hasattr(kernel_ast, 'block_specs'):
        n_blocks = len(kernel_ast.block_specs)
    else:
        n_blocks = 0

    n_conditionals = len(kernel_ast.conditionals) if hasattr(kernel_ast, 'conditionals') else 0
    source_hash = getattr(kernel_ast, 'source_hash', '') or getattr(kernel_ast, 'source_code', '') or ''

    return KernelFingerprint(
        n_loads=len(kernel_ast.loads),
        n_stores=len(kernel_ast.stores),
        n_reductions=len(kernel_ast.reductions),
        n_blocks=n_blocks,
        n_atomics=n_atomics,
        reduction_ops=reduction_ops,
        has_mask=has_mask,
        n_conditionals=n_conditionals,
        source_hash=source_hash,
    )


def fingerprints_compatible(fp1: KernelFingerprint,
                            fp2: KernelFingerprint) -> bool:
    """
    Check if two kernel fingerprints are structurally compatible.

    Compatible fingerprints have the same number of loads/stores/reductions
    and use the same reduction operations — they tile the computation
    in the same way.
    """
    return (fp1.n_loads == fp2.n_loads and
            fp1.n_stores == fp2.n_stores and
            fp1.n_reductions == fp2.n_reductions and
            fp1.reduction_ops == fp2.reduction_ops and
            fp1.has_mask == fp2.has_mask)


# ---------------------------------------------------------------------------
# Block tiling topology
# ---------------------------------------------------------------------------

@dataclass
class TilingTopology:
    """
    The Grothendieck topology generated by a kernel's block tiling.

    Each tile is a cover element; the collection of tiles forms a cover
    of the input tensor.  Refinement morphisms correspond to subdividing
    tiles into smaller blocks.
    """
    block_dims: Dict[str, int]  # block_name → size
    n_tiles: Dict[str, int]  # block_name → number of tiles
    total_tiles: int = 1
    has_boundary_mask: bool = False

    @staticmethod
    def from_kernel_spec(spec: TritonKernelSpec,
                         input_size: int = 1024) -> "TilingTopology":
        block_dims = {}
        n_tiles_map = {}
        total = 1
        has_mask = any(ma.mask_expr is not None
                       for ma in spec.memory_accesses)

        for bs in spec.block_specs:
            block_dims[bs.name] = bs.size
            nt = (input_size + bs.size - 1) // bs.size
            n_tiles_map[bs.name] = nt
            total *= nt

        return TilingTopology(
            block_dims=block_dims,
            n_tiles=n_tiles_map,
            total_tiles=total,
            has_boundary_mask=has_mask,
        )


def tiling_topologies_equivalent(t1: TilingTopology,
                                 t2: TilingTopology) -> bool:
    """
    Check if two tiling topologies are equivalent.

    Equivalent topologies have the same block structure and generate
    the same cover of the input space.  We compare by sorted block sizes
    (not parameter names, which are α-equivalent).
    """
    if t1.has_boundary_mask != t2.has_boundary_mask:
        return False
    sizes_1 = sorted(t1.block_dims.values())
    sizes_2 = sorted(t2.block_dims.values())
    if sizes_1 != sizes_2:
        return False
    if t1.total_tiles != t2.total_tiles:
        return False
    return True
