"""
Memory equivalence checker — view/alias presheaf, contiguity, in-place mutation.

Models memory layout as a presheaf on the memory site category:
  - Objects: memory layout descriptors (strides, storage offset, aliasing)
  - Morphisms: contiguity coarsening (contiguous → strided → general)
  - Sections: memory behavior functions μ_f, μ_g: inputs → memory_layout
  - Equivalence: μ_f and μ_g produce isomorphic memory layouts

The storage aliasing relation generates a simplicial complex:
  - 0-simplices: individual tensors
  - 1-simplices: pairs of tensors sharing storage (aliases)
  - Higher simplices: mutual aliasing cliques
Equivalence requires the aliasing complexes to be isomorphic.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

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
# Memory layout descriptors
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class MemoryLayout:
    """Describes the memory layout of a tensor."""
    shape: Tuple[int, ...]
    strides: Tuple[int, ...]
    storage_offset: int = 0
    is_contiguous: bool = True
    is_view: bool = False
    storage_id: Optional[int] = None  # id of underlying storage

    @property
    def numel(self) -> int:
        import math
        return math.prod(self.shape) if self.shape else 1

    @property
    def is_c_contiguous(self) -> bool:
        """Check row-major (C) contiguity."""
        if not self.shape:
            return True
        expected_stride = 1
        for dim, stride in zip(reversed(self.shape), reversed(self.strides)):
            if dim > 1 and stride != expected_stride:
                return False
            expected_stride *= dim
        return True

    @property
    def is_f_contiguous(self) -> bool:
        """Check column-major (Fortran) contiguity."""
        if not self.shape:
            return True
        expected_stride = 1
        for dim, stride in zip(self.shape, self.strides):
            if dim > 1 and stride != expected_stride:
                return False
            expected_stride *= dim
        return True


def extract_layout(tensor: Any) -> Optional[MemoryLayout]:
    """Extract memory layout from a PyTorch tensor."""
    try:
        import torch
        if not isinstance(tensor, torch.Tensor):
            return None
        return MemoryLayout(
            shape=tuple(tensor.shape),
            strides=tuple(tensor.stride()),
            storage_offset=tensor.storage_offset(),
            is_contiguous=tensor.is_contiguous(),
            is_view=tensor._is_view(),
            storage_id=id(tensor.untyped_storage()),
        )
    except Exception:
        return None


# ---------------------------------------------------------------------------
# Aliasing analysis (the aliasing simplicial complex)
# ---------------------------------------------------------------------------

@dataclass
class AliasingGraph:
    """
    Graph of storage aliasing between tensors.

    Vertices are tensor indices, edges connect tensors sharing storage.
    This is the 1-skeleton of the aliasing simplicial complex.
    """
    n_tensors: int
    edges: Set[Tuple[int, int]] = field(default_factory=set)
    storage_groups: Dict[int, List[int]] = field(default_factory=dict)

    @property
    def has_aliasing(self) -> bool:
        return len(self.edges) > 0

    @property
    def n_components(self) -> int:
        """Number of connected components (via union-find)."""
        parent = list(range(self.n_tensors))

        def find(x: int) -> int:
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(x: int, y: int) -> None:
            px, py = find(x), find(y)
            if px != py:
                parent[px] = py

        for a, b in self.edges:
            union(a, b)

        roots = set(find(i) for i in range(self.n_tensors))
        return len(roots)


def build_aliasing_graph(tensors: Sequence[Any]) -> AliasingGraph:
    """Build the aliasing graph from a sequence of tensors."""
    try:
        import torch
    except ImportError:
        return AliasingGraph(n_tensors=len(tensors))

    graph = AliasingGraph(n_tensors=len(tensors))
    storage_to_indices: Dict[int, List[int]] = {}

    for i, t in enumerate(tensors):
        if isinstance(t, torch.Tensor):
            sid = id(t.untyped_storage())
            storage_to_indices.setdefault(sid, []).append(i)

    for sid, indices in storage_to_indices.items():
        graph.storage_groups[sid] = indices
        for i in range(len(indices)):
            for j in range(i + 1, len(indices)):
                graph.edges.add((indices[i], indices[j]))

    return graph


def aliasing_graphs_isomorphic(g1: AliasingGraph, g2: AliasingGraph) -> bool:
    """
    Check if two aliasing graphs are isomorphic.

    For small graphs (typical tensor programs), we use a direct comparison
    of the edge structure up to relabeling.  This is the key invariant:
    two functions preserve aliasing iff their aliasing graphs are isomorphic.
    """
    if g1.n_tensors != g2.n_tensors:
        return False
    if len(g1.edges) != len(g2.edges):
        return False
    if g1.n_components != g2.n_components:
        return False

    # Compare component sizes (sorted)
    def component_sizes(g: AliasingGraph) -> List[int]:
        parent = list(range(g.n_tensors))

        def find(x: int) -> int:
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(x: int, y: int) -> None:
            px, py = find(x), find(y)
            if px != py:
                parent[px] = py

        for a, b in g.edges:
            union(a, b)

        sizes: Dict[int, int] = {}
        for i in range(g.n_tensors):
            r = find(i)
            sizes[r] = sizes.get(r, 0) + 1
        return sorted(sizes.values())

    return component_sizes(g1) == component_sizes(g2)


# ---------------------------------------------------------------------------
# In-place mutation detection
# ---------------------------------------------------------------------------

def detect_inplace_mutation(fn: Any, inputs: List[Any]) -> List[int]:
    """
    Detect which input tensors are mutated in-place by fn.

    Returns indices of mutated inputs.  In-place mutation is an important
    semantic property: two functions that differ in mutation behavior
    are not equivalent (they have different side effects on the ambient
    tensor state).
    """
    try:
        import torch
    except ImportError:
        return []

    # Clone inputs and record storage data pointers
    cloned = []
    original_data = []
    for inp in inputs:
        if isinstance(inp, torch.Tensor):
            c = inp.clone()
            cloned.append(c)
            original_data.append(c.data_ptr())
        else:
            cloned.append(inp)
            original_data.append(None)

    # Run the function
    try:
        fn(*cloned)
    except Exception:
        return []

    # Check which tensors were mutated
    mutated = []
    for i, (inp, orig_ptr) in enumerate(zip(cloned, original_data)):
        if isinstance(inp, torch.Tensor) and orig_ptr is not None:
            # Check if data changed
            try:
                if not torch.equal(inp, inputs[i]):
                    mutated.append(i)
            except Exception:
                pass
    return mutated


# ---------------------------------------------------------------------------
# Memory equivalence checker
# ---------------------------------------------------------------------------

class MemoryEquivalenceChecker:
    """
    Checks memory layout equivalence of two tensor functions.

    This implements the local section comparison at stride/memory sites:
    1. Contiguity check: do both produce contiguous outputs?
    2. Stride check: do both produce the same output strides?
    3. View check: do both produce views vs copies?
    4. Aliasing check: do both preserve the same aliasing structure?
    5. In-place mutation check: do both mutate the same inputs?

    Sheaf-theoretically, memory layout is a presheaf on the contiguity
    lattice: contiguous ≤ strided ≤ general.  Restriction along this
    lattice forgets increasingly fine memory details.
    """

    def __init__(self, config: TensorEquivalenceConfig):
        self._config = config

    def check_site(
        self,
        fn_f: Any,
        fn_g: Any,
        test_inputs: List[List[Any]],
        site_id: SiteId,
    ) -> TensorLocalJudgment:
        """Check memory layout equivalence at a stride/memory site."""
        obstructions: List[TensorObstruction] = []

        for inputs in test_inputs:
            try:
                out_f = fn_f(*[i.clone() if hasattr(i, 'clone') else i
                               for i in inputs])
                out_g = fn_g(*[i.clone() if hasattr(i, 'clone') else i
                               for i in inputs])
            except Exception:
                continue

            # Compare output layouts
            layouts_f = self._extract_layouts(out_f)
            layouts_g = self._extract_layouts(out_g)

            if len(layouts_f) != len(layouts_g):
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.STRIDE_MISMATCH,
                    stratum=TensorStratum.STRUCTURAL,
                    sites=(site_id,),
                    description=(f"Different number of tensor outputs: "
                                 f"{len(layouts_f)} vs {len(layouts_g)}"),
                ))
                continue

            for i, (lf, lg) in enumerate(zip(layouts_f, layouts_g)):
                if lf is None or lg is None:
                    continue

                # Check contiguity
                if lf.is_contiguous != lg.is_contiguous:
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.STRIDE_MISMATCH,
                        stratum=TensorStratum.STRUCTURAL,
                        sites=(site_id,),
                        description=(f"Output {i}: contiguity differs: "
                                     f"f={lf.is_contiguous}, g={lg.is_contiguous}"),
                    ))

                # Check strides
                if self._config.check_stride and lf.strides != lg.strides:
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.STRIDE_MISMATCH,
                        stratum=TensorStratum.STRUCTURAL,
                        sites=(site_id,),
                        description=(f"Output {i}: strides differ: "
                                     f"f={lf.strides}, g={lg.strides}"),
                    ))

                # Check view vs copy
                if lf.is_view != lg.is_view:
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.MEMORY_ALIASING,
                        stratum=TensorStratum.BEHAVIORAL,
                        sites=(site_id,),
                        description=(f"Output {i}: view status differs: "
                                     f"f={'view' if lf.is_view else 'copy'}, "
                                     f"g={'view' if lg.is_view else 'copy'}"),
                    ))

        # Check in-place mutation
        if self._config.check_memory_aliasing:
            for inputs in test_inputs[:3]:
                cloned_inputs = [i.clone() if hasattr(i, 'clone') else i
                                 for i in inputs]
                mut_f = detect_inplace_mutation(fn_f, cloned_inputs)
                cloned_inputs2 = [i.clone() if hasattr(i, 'clone') else i
                                  for i in inputs]
                mut_g = detect_inplace_mutation(fn_g, cloned_inputs2)
                if set(mut_f) != set(mut_g):
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.INPLACE_MUTATION,
                        stratum=TensorStratum.BEHAVIORAL,
                        sites=(site_id,),
                        description=(f"In-place mutation differs: "
                                     f"f mutates {mut_f}, g mutates {mut_g}"),
                    ))

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.STRUCTURAL,
                tensor_site_kind=TensorSiteKind.STRIDE,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation=f"Memory layout differs ({len(obstructions)} issues)",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.STRUCTURAL,
            tensor_site_kind=TensorSiteKind.STRIDE,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation="Memory layouts match",
        )

    def check_aliasing_site(
        self,
        fn_f: Any,
        fn_g: Any,
        test_inputs: List[List[Any]],
        site_id: SiteId,
    ) -> TensorLocalJudgment:
        """
        Check that aliasing structure is preserved.

        The aliasing graph is the 1-skeleton of the aliasing simplicial
        complex.  Two functions are aliasing-equivalent iff their aliasing
        graphs are isomorphic for all test inputs.
        """
        try:
            import torch
        except ImportError:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.BEHAVIORAL,
                tensor_site_kind=TensorSiteKind.STRIDE,
                verdict=EquivalenceVerdict.UNKNOWN,
                explanation="PyTorch not available",
            )

        obstructions: List[TensorObstruction] = []

        for inputs in test_inputs:
            try:
                out_f = fn_f(*[i.clone() if hasattr(i, 'clone') else i
                               for i in inputs])
                out_g = fn_g(*[i.clone() if hasattr(i, 'clone') else i
                               for i in inputs])
            except Exception:
                continue

            tensors_f = self._collect_tensors(out_f)
            tensors_g = self._collect_tensors(out_g)

            graph_f = build_aliasing_graph(tensors_f)
            graph_g = build_aliasing_graph(tensors_g)

            if not aliasing_graphs_isomorphic(graph_f, graph_g):
                obstructions.append(TensorObstruction(
                    kind=TensorObstructionKind.MEMORY_ALIASING,
                    stratum=TensorStratum.BEHAVIORAL,
                    sites=(site_id,),
                    description=(f"Aliasing structure differs: "
                                 f"f has {len(graph_f.edges)} aliases, "
                                 f"g has {len(graph_g.edges)} aliases"),
                ))

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.BEHAVIORAL,
                tensor_site_kind=TensorSiteKind.STRIDE,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation="Aliasing structure differs",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.BEHAVIORAL,
            tensor_site_kind=TensorSiteKind.STRIDE,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation="Aliasing structure matches",
        )

    @staticmethod
    def _extract_layouts(out: Any) -> List[Optional[MemoryLayout]]:
        if isinstance(out, (tuple, list)):
            return [extract_layout(o) for o in out]
        return [extract_layout(out)]

    @staticmethod
    def _collect_tensors(out: Any) -> List[Any]:
        try:
            import torch
        except ImportError:
            return []
        if isinstance(out, torch.Tensor):
            return [out]
        if isinstance(out, (tuple, list)):
            result = []
            for o in out:
                if isinstance(o, torch.Tensor):
                    result.append(o)
            return result
        return []

    # ------------------------------------------------------------------
    # Single-program analysis
    # ------------------------------------------------------------------

    def analyze(
        self,
        fn: Any,
        test_inputs: List[List[Any]],
        site_id: Optional[SiteId] = None,
    ) -> AnalysisJudgment:
        """Analyze memory safety of a single function.

        Checks for in-place mutation of inputs, unexpected aliasing
        between inputs and outputs, and memory layout issues.
        A bug means the heap-protocol presheaf has ill-formed sections —
        the function's side-effects violate the expected purity contract.
        """
        try:
            import torch
        except ImportError:
            return AnalysisJudgment(
                verdict=AnalysisVerdict.UNKNOWN,
                program=ProgramId(name="fn"),
                mode=AnalysisMode.BUG_FINDING,
                explanation="PyTorch not available",
            )

        if site_id is None:
            site_id = SiteId(kind=SiteKind.HEAP_PROTOCOL, name="memory_analysis")
        program = ProgramId(name="fn", function_name=getattr(fn, "__name__", "anonymous"))
        bugs: List[Bug] = []

        for inputs in test_inputs:
            # --- In-place mutation detection --------------------------
            cloned = [t.clone() if isinstance(t, torch.Tensor) else t
                      for t in inputs]
            snapshots = [t.clone() if isinstance(t, torch.Tensor) else None
                         for t in cloned]
            try:
                out = fn(*cloned)
            except Exception:
                continue

            for i, (snap, cur) in enumerate(zip(snapshots, cloned)):
                if snap is not None and isinstance(cur, torch.Tensor):
                    if not torch.equal(snap, cur):
                        bugs.append(Bug(
                            kind=BugKind.MEMORY_VIOLATION,
                            stratum=TensorStratum.BEHAVIORAL,
                            site_id=site_id,
                            description=f"Input tensor {i} mutated in-place",
                            witness_input=repr(inputs)[:200],
                            repair_hint="Clone inputs before mutation or avoid in-place ops",
                        ))

            # --- Output-input aliasing detection ----------------------
            out_tensors = self._collect_tensors(out)
            in_storages = set()
            for t in inputs:
                if isinstance(t, torch.Tensor):
                    in_storages.add(t.untyped_storage().data_ptr())

            for j, ot in enumerate(out_tensors):
                if isinstance(ot, torch.Tensor):
                    if ot.untyped_storage().data_ptr() in in_storages:
                        bugs.append(Bug(
                            kind=BugKind.ALIASING_HAZARD,
                            stratum=TensorStratum.BEHAVIORAL,
                            site_id=site_id,
                            description=(
                                f"Output tensor {j} aliases input storage; "
                                f"mutations to input will corrupt output"
                            ),
                            witness_input=repr(inputs)[:200],
                            repair_hint="Return .clone() to break aliasing",
                        ))

            # --- Output-output aliasing detection ---------------------
            seen_storages: Dict[int, int] = {}
            for j, ot in enumerate(out_tensors):
                if isinstance(ot, torch.Tensor):
                    ptr = ot.untyped_storage().data_ptr()
                    if ptr in seen_storages:
                        bugs.append(Bug(
                            kind=BugKind.ALIASING_HAZARD,
                            stratum=TensorStratum.BEHAVIORAL,
                            site_id=site_id,
                            description=(
                                f"Output tensors {seen_storages[ptr]} and {j} "
                                f"share storage; mutating one corrupts the other"
                            ),
                            witness_input=repr(inputs)[:200],
                        ))
                    else:
                        seen_storages[ptr] = j

        verdict = AnalysisVerdict.INVALID if bugs else AnalysisVerdict.VALID
        return AnalysisJudgment(
            verdict=verdict,
            program=program,
            mode=AnalysisMode.BUG_FINDING,
            bugs=bugs,
            stratum_results={TensorStratum.BEHAVIORAL: verdict},
            explanation=(
                f"Found {len(bugs)} memory safety issues"
                if bugs else
                "Heap-protocol presheaf sections are well-formed"
            ),
        )
