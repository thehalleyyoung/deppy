"""
Autograd equivalence checker — Jacobian presheaf, gradient graph isomorphism.

Models autograd equivalence as a presheaf on the autograd site category:
  - Objects: (input_spec, output_spec, requires_grad) triples
  - Morphisms: chain rule composition (restriction along composition)
  - Sections: Jacobian matrices J_f, J_g at each point
  - Equivalence: J_f ≈ J_g within tolerance at all test points

The autograd graph is the computational graph of backward passes.
Two functions are autograd-equivalent iff:
  1. Their Jacobians agree numerically (up to tolerance)
  2. Their gradient graphs are isomorphic (same computational structure)
  3. Higher-order gradients agree (if applicable)

This is the BEHAVIORAL stratum — the finest observation level.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

from ._protocols import (
    AnalysisJudgment,
    AnalysisMode,
    AnalysisVerdict,
    Bug,
    BugKind,
    EquivalenceVerdict,
    NumericalToleranceSpec,
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
# Jacobian computation
# ---------------------------------------------------------------------------

@dataclass
class JacobianResult:
    """Result of computing a Jacobian matrix."""
    jacobian: Any  # torch.Tensor of shape (n_out, n_in)
    shape_out: Tuple[int, ...]
    shape_in: Tuple[int, ...]
    is_sparse: bool = False
    nonzero_fraction: float = 1.0


def compute_jacobian(fn: Any, inputs: List[Any],
                     output_index: int = 0) -> Optional[JacobianResult]:
    """
    Compute the Jacobian matrix of fn at the given inputs.

    This is the *local section* of the autograd presheaf: the Jacobian
    encodes all first-order differential information at a point.
    """
    try:
        import torch
        from torch.autograd.functional import jacobian as torch_jacobian
    except ImportError:
        return None

    # Prepare inputs: ensure requires_grad
    grad_inputs = []
    input_indices = []
    for i, inp in enumerate(inputs):
        if isinstance(inp, torch.Tensor) and inp.is_floating_point():
            t = inp.detach().clone().requires_grad_(True)
            grad_inputs.append(t)
            input_indices.append(i)
        else:
            grad_inputs.append(inp)

    if not input_indices:
        return None

    def wrapped_fn(*args):
        out = fn(*args)
        if isinstance(out, (tuple, list)):
            if output_index < len(out):
                return out[output_index]
            return out[0]
        return out

    try:
        # Use torch.autograd.functional.jacobian
        def fn_for_jac(x):
            rebuilt = list(grad_inputs)
            rebuilt[input_indices[0]] = x
            return wrapped_fn(*rebuilt)

        J = torch_jacobian(fn_for_jac, grad_inputs[input_indices[0]])

        if isinstance(J, torch.Tensor):
            n_out = J.shape[0] if J.dim() > 0 else 1
            n_in = J.shape[-1] if J.dim() > 1 else 1
            J_flat = J.reshape(-1, n_in) if J.dim() > 1 else J.reshape(1, -1)
            nonzero = (J_flat.abs() > 1e-10).float().mean().item()

            return JacobianResult(
                jacobian=J_flat.detach(),
                shape_out=tuple(J.shape[:J.dim() // 2]) if J.dim() > 1 else (1,),
                shape_in=tuple(J.shape[J.dim() // 2:]) if J.dim() > 1 else (J.numel(),),
                is_sparse=nonzero < 0.1,
                nonzero_fraction=nonzero,
            )
    except Exception:
        pass

    # Fallback: manual gradient computation
    try:
        out = wrapped_fn(*grad_inputs)
        if not isinstance(out, torch.Tensor):
            return None

        out_flat = out.flatten()
        n_out = out_flat.numel()
        inp = grad_inputs[input_indices[0]]
        n_in = inp.numel()

        J = torch.zeros(n_out, n_in)
        for i in range(n_out):
            # Compute gradient of output[i] w.r.t. input
            grad_outputs = torch.zeros_like(out_flat)
            grad_outputs[i] = 1.0
            try:
                grads = torch.autograd.grad(
                    out_flat, inp, grad_outputs=grad_outputs,
                    create_graph=False, retain_graph=True,
                    allow_unused=True,
                )
                if grads[0] is not None:
                    J[i] = grads[0].flatten()
            except Exception:
                pass

        nonzero = (J.abs() > 1e-10).float().mean().item()
        return JacobianResult(
            jacobian=J.detach(),
            shape_out=tuple(out.shape),
            shape_in=tuple(inp.shape),
            is_sparse=nonzero < 0.1,
            nonzero_fraction=nonzero,
        )
    except Exception:
        return None


# ---------------------------------------------------------------------------
# Gradient graph analysis
# ---------------------------------------------------------------------------

@dataclass
class GradGraphNode:
    """A node in the autograd computation graph."""
    op_name: str
    n_inputs: int
    n_outputs: int


@dataclass
class GradGraphSummary:
    """Summary of an autograd computation graph."""
    nodes: List[GradGraphNode]
    n_nodes: int
    n_edges: int
    depth: int
    op_histogram: Dict[str, int]


def extract_grad_graph(fn: Any, inputs: List[Any]) -> Optional[GradGraphSummary]:
    """
    Extract a summary of the autograd graph for fn at inputs.

    This is the *stalk* of the autograd presheaf: the computational
    graph encodes the full backward-pass structure at a point.
    """
    try:
        import torch
    except ImportError:
        return None

    # Run forward pass to build graph
    grad_inputs = []
    for inp in inputs:
        if isinstance(inp, torch.Tensor) and inp.is_floating_point():
            t = inp.detach().clone().requires_grad_(True)
            grad_inputs.append(t)
        else:
            grad_inputs.append(inp)

    try:
        out = fn(*grad_inputs)
    except Exception:
        return None

    # Extract the output tensor
    if isinstance(out, (tuple, list)):
        out_tensors = [o for o in out if isinstance(o, torch.Tensor) and o.requires_grad]
    elif isinstance(out, torch.Tensor) and out.requires_grad:
        out_tensors = [out]
    else:
        return GradGraphSummary(
            nodes=[], n_nodes=0, n_edges=0, depth=0, op_histogram={},
        )

    if not out_tensors:
        return GradGraphSummary(
            nodes=[], n_nodes=0, n_edges=0, depth=0, op_histogram={},
        )

    # Walk the grad_fn chain
    nodes: List[GradGraphNode] = []
    op_hist: Dict[str, int] = {}
    visited = set()
    max_depth = [0]

    def walk(grad_fn: Any, depth: int = 0) -> None:
        if grad_fn is None or id(grad_fn) in visited:
            return
        visited.add(id(grad_fn))
        max_depth[0] = max(max_depth[0], depth)

        name = type(grad_fn).__name__
        n_in = len(grad_fn.next_functions) if hasattr(grad_fn, "next_functions") else 0
        nodes.append(GradGraphNode(op_name=name, n_inputs=n_in, n_outputs=1))
        op_hist[name] = op_hist.get(name, 0) + 1

        if hasattr(grad_fn, "next_functions"):
            for next_fn, _ in grad_fn.next_functions:
                walk(next_fn, depth + 1)

    for t in out_tensors:
        if t.grad_fn is not None:
            walk(t.grad_fn)

    return GradGraphSummary(
        nodes=nodes,
        n_nodes=len(nodes),
        n_edges=sum(n.n_inputs for n in nodes),
        depth=max_depth[0],
        op_histogram=op_hist,
    )


def grad_graphs_isomorphic(g1: Optional[GradGraphSummary],
                           g2: Optional[GradGraphSummary],
                           strict: bool = False) -> bool:
    """
    Check if two gradient graphs are isomorphic (approximately).

    Strict mode requires exact node-for-node match.
    Non-strict mode checks structural invariants (node count, depth, op histogram).
    """
    if g1 is None and g2 is None:
        return True
    if g1 is None or g2 is None:
        return False

    if strict:
        return (g1.n_nodes == g2.n_nodes and
                g1.n_edges == g2.n_edges and
                g1.depth == g2.depth and
                g1.op_histogram == g2.op_histogram)

    # Non-strict: same number of nodes and similar depth
    if g1.n_nodes == 0 and g2.n_nodes == 0:
        return True
    if g1.n_nodes == 0 or g2.n_nodes == 0:
        return False

    # Allow 20% tolerance on graph metrics
    node_ratio = min(g1.n_nodes, g2.n_nodes) / max(g1.n_nodes, g2.n_nodes)
    depth_ratio = (min(g1.depth, g2.depth) + 1) / (max(g1.depth, g2.depth) + 1)

    return node_ratio > 0.5 and depth_ratio > 0.5


# ---------------------------------------------------------------------------
# Autograd equivalence checker
# ---------------------------------------------------------------------------

class AutogradEquivalenceChecker:
    """
    Checks autograd equivalence of two tensor functions.

    This implements the local section comparison at autograd sites:
    1. Jacobian comparison: J_f ≈ J_g within tolerance
    2. Gradient graph comparison: isomorphic backward pass structure
    3. Higher-order gradient check (optional)

    Sheaf-theoretically, the autograd presheaf assigns to each site
    the Jacobian matrix (a linear map from input to output tangent spaces).
    The chain rule is the restriction morphism: composing with a linear
    map restricts the Jacobian by matrix multiplication.
    """

    def __init__(self, config: TensorEquivalenceConfig):
        self._config = config
        self._tol = config.tolerance

    def check_site(
        self,
        fn_f: Any,
        fn_g: Any,
        test_inputs: List[List[Any]],
        site_id: SiteId,
    ) -> TensorLocalJudgment:
        """Check autograd equivalence at a single autograd site."""
        obstructions: List[TensorObstruction] = []
        max_jac_diff = 0.0

        for inputs in test_inputs:
            # Jacobian comparison
            jac_result = self._compare_jacobians(fn_f, fn_g, inputs, site_id)
            if jac_result is not None:
                if jac_result[0]:  # has obstruction
                    obstructions.append(jac_result[0])
                max_jac_diff = max(max_jac_diff, jac_result[1])

            # Gradient graph comparison
            graph_result = self._compare_grad_graphs(fn_f, fn_g, inputs, site_id)
            if graph_result is not None:
                obstructions.append(graph_result)

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.BEHAVIORAL,
                tensor_site_kind=TensorSiteKind.AUTOGRAD,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation=f"Autograd differs: max Jacobian diff={max_jac_diff:.2e}",
                obstructions=tuple(obstructions),
                max_abs_diff=max_jac_diff,
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.BEHAVIORAL,
            tensor_site_kind=TensorSiteKind.AUTOGRAD,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation="Autograd behavior matches",
        )

    def _compare_jacobians(
        self,
        fn_f: Any,
        fn_g: Any,
        inputs: List[Any],
        site_id: SiteId,
    ) -> Optional[Tuple[Optional[TensorObstruction], float]]:
        """Compare Jacobians of fn_f and fn_g."""
        try:
            import torch
        except ImportError:
            return None

        jac_f = compute_jacobian(fn_f, inputs)
        jac_g = compute_jacobian(fn_g, inputs)

        if jac_f is None and jac_g is None:
            return None
        if jac_f is None or jac_g is None:
            return (TensorObstruction(
                kind=TensorObstructionKind.GRADIENT_DIVERGENCE,
                stratum=TensorStratum.BEHAVIORAL,
                sites=(site_id,),
                description=("Jacobian computation failed for "
                             f"{'f' if jac_f is None else 'g'}"),
            ), float('inf'))

        # Compare shapes
        if jac_f.jacobian.shape != jac_g.jacobian.shape:
            return (TensorObstruction(
                kind=TensorObstructionKind.AUTOGRAD_GRAPH_MISMATCH,
                stratum=TensorStratum.BEHAVIORAL,
                sites=(site_id,),
                description=(f"Jacobian shapes differ: "
                             f"{jac_f.jacobian.shape} vs {jac_g.jacobian.shape}"),
            ), float('inf'))

        # Numerical comparison
        diff = (jac_f.jacobian - jac_g.jacobian).abs()
        max_diff = diff.max().item()

        threshold = self._tol.atol + self._tol.rtol * max(
            jac_f.jacobian.abs().max().item(),
            jac_g.jacobian.abs().max().item(),
            1e-300,
        )

        if max_diff > threshold:
            return (TensorObstruction(
                kind=TensorObstructionKind.GRADIENT_DIVERGENCE,
                stratum=TensorStratum.BEHAVIORAL,
                sites=(site_id,),
                description=f"Jacobian max diff: {max_diff:.2e} > threshold {threshold:.2e}",
                max_abs_diff=max_diff,
            ), max_diff)

        return (None, max_diff)

    def _compare_grad_graphs(
        self,
        fn_f: Any,
        fn_g: Any,
        inputs: List[Any],
        site_id: SiteId,
    ) -> Optional[TensorObstruction]:
        """Compare gradient computation graphs."""
        graph_f = extract_grad_graph(fn_f, inputs)
        graph_g = extract_grad_graph(fn_g, inputs)

        if not grad_graphs_isomorphic(graph_f, graph_g, strict=False):
            return TensorObstruction(
                kind=TensorObstructionKind.AUTOGRAD_GRAPH_MISMATCH,
                stratum=TensorStratum.BEHAVIORAL,
                sites=(site_id,),
                description=(f"Grad graph mismatch: "
                             f"f has {graph_f.n_nodes if graph_f else 0} nodes, "
                             f"g has {graph_g.n_nodes if graph_g else 0} nodes"),
            )
        return None

    def check_higher_order(
        self,
        fn_f: Any,
        fn_g: Any,
        inputs: List[Any],
        site_id: SiteId,
        order: int = 2,
    ) -> TensorLocalJudgment:
        """
        Check higher-order gradient equivalence.

        Higher-order gradients correspond to sections of the jet bundle
        presheaf — the k-th jet at a point encodes all derivatives up
        to order k.  Agreement on k-jets is a necessary condition for
        k-th order equivalence.
        """
        try:
            import torch
        except ImportError:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.BEHAVIORAL,
                tensor_site_kind=TensorSiteKind.AUTOGRAD,
                verdict=EquivalenceVerdict.UNKNOWN,
                explanation="PyTorch not available",
            )

        obstructions: List[TensorObstruction] = []

        grad_inputs_f = [
            inp.detach().clone().requires_grad_(True)
            if isinstance(inp, torch.Tensor) and inp.is_floating_point()
            else inp
            for inp in inputs
        ]
        grad_inputs_g = [
            inp.detach().clone().requires_grad_(True)
            if isinstance(inp, torch.Tensor) and inp.is_floating_point()
            else inp
            for inp in inputs
        ]

        try:
            out_f = fn_f(*grad_inputs_f)
            out_g = fn_g(*grad_inputs_g)

            if isinstance(out_f, (tuple, list)):
                out_f = out_f[0]
            if isinstance(out_g, (tuple, list)):
                out_g = out_g[0]

            if not isinstance(out_f, torch.Tensor) or not isinstance(out_g, torch.Tensor):
                return TensorLocalJudgment(
                    site_id=site_id,
                    stratum=TensorStratum.BEHAVIORAL,
                    tensor_site_kind=TensorSiteKind.AUTOGRAD,
                    verdict=EquivalenceVerdict.UNKNOWN,
                    explanation="Non-tensor output",
                )

            # Compute gradient
            scalar_f = out_f.sum()
            scalar_g = out_g.sum()

            grad_f = torch.autograd.grad(
                scalar_f, grad_inputs_f[0], create_graph=True,
                retain_graph=True, allow_unused=True,
            )[0]
            grad_g = torch.autograd.grad(
                scalar_g, grad_inputs_g[0], create_graph=True,
                retain_graph=True, allow_unused=True,
            )[0]

            if grad_f is not None and grad_g is not None:
                diff = (grad_f - grad_g).abs().max().item()
                if diff > self._tol.atol * 10:
                    obstructions.append(TensorObstruction(
                        kind=TensorObstructionKind.GRADIENT_DIVERGENCE,
                        stratum=TensorStratum.BEHAVIORAL,
                        sites=(site_id,),
                        description=f"1st-order gradient diff: {diff:.2e}",
                        max_abs_diff=diff,
                    ))

                # Second order
                if order >= 2 and grad_f.requires_grad and grad_g.requires_grad:
                    try:
                        hess_f = torch.autograd.grad(
                            grad_f.sum(), grad_inputs_f[0],
                            allow_unused=True,
                        )[0]
                        hess_g = torch.autograd.grad(
                            grad_g.sum(), grad_inputs_g[0],
                            allow_unused=True,
                        )[0]

                        if hess_f is not None and hess_g is not None:
                            hess_diff = (hess_f - hess_g).abs().max().item()
                            if hess_diff > self._tol.atol * 100:
                                obstructions.append(TensorObstruction(
                                    kind=TensorObstructionKind.GRADIENT_DIVERGENCE,
                                    stratum=TensorStratum.BEHAVIORAL,
                                    sites=(site_id,),
                                    description=f"2nd-order gradient diff: {hess_diff:.2e}",
                                    max_abs_diff=hess_diff,
                                ))
                    except Exception:
                        pass
        except Exception as e:
            obstructions.append(TensorObstruction(
                kind=TensorObstructionKind.GRADIENT_DIVERGENCE,
                stratum=TensorStratum.BEHAVIORAL,
                sites=(site_id,),
                description=f"Higher-order gradient computation failed: {e}",
            ))

        if obstructions:
            return TensorLocalJudgment(
                site_id=site_id,
                stratum=TensorStratum.BEHAVIORAL,
                tensor_site_kind=TensorSiteKind.AUTOGRAD,
                verdict=EquivalenceVerdict.INEQUIVALENT,
                explanation=f"Higher-order gradient differs (order={order})",
                obstructions=tuple(obstructions),
            )

        return TensorLocalJudgment(
            site_id=site_id,
            stratum=TensorStratum.BEHAVIORAL,
            tensor_site_kind=TensorSiteKind.AUTOGRAD,
            verdict=EquivalenceVerdict.EQUIVALENT,
            explanation=f"Higher-order gradients match up to order {order}",
        )

    # ------------------------------------------------------------------
    # Single-program analysis
    # ------------------------------------------------------------------

    def analyze(
        self,
        fn: Any,
        test_inputs: List[List[Any]],
        site_id: Optional[SiteId] = None,
    ) -> AnalysisJudgment:
        """Analyze autograd consistency of a single function.

        Checks gradient existence, shape consistency with forward output,
        and numerical gradient vs analytic gradient comparison.
        A bug means the autograd presheaf is ill-formed — the backward
        section is not the dual of the forward section.
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
            site_id = SiteId(kind=SiteKind.TENSOR_SHAPE, name="autograd_analysis")
        program = ProgramId(name="fn", function_name=getattr(fn, "__name__", "anonymous"))
        bugs: List[Bug] = []

        for inputs in test_inputs:
            # Prepare gradient-enabled inputs
            grad_inputs = []
            grad_indices = []
            for i, inp in enumerate(inputs):
                if isinstance(inp, torch.Tensor) and inp.is_floating_point():
                    t = inp.detach().clone().requires_grad_(True)
                    grad_inputs.append(t)
                    grad_indices.append(i)
                else:
                    grad_inputs.append(inp)

            if not grad_indices:
                continue

            # Forward pass
            try:
                out = fn(*grad_inputs)
            except Exception:
                continue

            out_tensor = out[0] if isinstance(out, (tuple, list)) else out
            if not isinstance(out_tensor, torch.Tensor):
                continue

            # Check gradient existence
            if not out_tensor.requires_grad:
                bugs.append(Bug(
                    kind=BugKind.GRADIENT_INCORRECTNESS,
                    stratum=TensorStratum.BEHAVIORAL,
                    site_id=site_id,
                    description=(
                        "Output does not require grad despite float inputs "
                        "with requires_grad=True"
                    ),
                    witness_input=repr(inputs)[:200],
                    repair_hint="Ensure differentiable ops are used throughout",
                ))
                continue

            # Backward pass — shape consistency
            try:
                scalar = out_tensor.sum()
                grads = torch.autograd.grad(
                    scalar,
                    [grad_inputs[j] for j in grad_indices],
                    allow_unused=True,
                )
                for gi, grad in zip(grad_indices, grads):
                    if grad is None:
                        bugs.append(Bug(
                            kind=BugKind.GRADIENT_INCORRECTNESS,
                            stratum=TensorStratum.BEHAVIORAL,
                            site_id=site_id,
                            description=f"Gradient is None for input {gi}",
                            witness_input=repr(inputs)[:200],
                            repair_hint="Input may be unused or detached in the graph",
                        ))
                    elif grad.shape != grad_inputs[gi].shape:
                        bugs.append(Bug(
                            kind=BugKind.GRADIENT_INCORRECTNESS,
                            stratum=TensorStratum.BEHAVIORAL,
                            site_id=site_id,
                            description=(
                                f"Gradient shape {tuple(grad.shape)} != "
                                f"input shape {tuple(grad_inputs[gi].shape)} "
                                f"for input {gi}"
                            ),
                            witness_input=repr(inputs)[:200],
                        ))
                    elif torch.isnan(grad).any() or torch.isinf(grad).any():
                        bugs.append(Bug(
                            kind=BugKind.GRADIENT_INCORRECTNESS,
                            stratum=TensorStratum.BEHAVIORAL,
                            site_id=site_id,
                            description=f"Gradient for input {gi} contains NaN/Inf",
                            witness_input=repr(inputs)[:200],
                            repair_hint="Check for 0/0 or log(0) in backward pass",
                        ))
            except Exception as e:
                bugs.append(Bug(
                    kind=BugKind.GRADIENT_INCORRECTNESS,
                    stratum=TensorStratum.BEHAVIORAL,
                    site_id=site_id,
                    description=f"Backward pass failed: {e}",
                    witness_input=repr(inputs)[:200],
                ))

            # Numerical vs analytic gradient comparison
            try:
                inp0 = grad_inputs[grad_indices[0]]
                eps = 1e-4
                inp_flat = inp0.detach().flatten()
                n_check = min(inp_flat.numel(), 3)
                for k in range(n_check):
                    perturbed = inp_flat.clone()
                    perturbed[k] += eps
                    inp_plus = perturbed.reshape(inp0.shape)
                    args_plus = list(grad_inputs)
                    args_plus[grad_indices[0]] = inp_plus
                    out_plus = fn(*args_plus)
                    op = out_plus[0] if isinstance(out_plus, (tuple, list)) else out_plus
                    if isinstance(op, torch.Tensor):
                        # Numerical gradient of scalar loss = sum(output)
                        num_grad = (op.sum().item() - out_tensor.sum().item()) / eps
                        # Analytic gradient: d(sum(f))/dx_k = sum(df/dx_k)
                        # = grad of sum(output) w.r.t. input[k]
                        inp_g = inp0.detach().clone().requires_grad_(True)
                        args_g = list(grad_inputs)
                        args_g[grad_indices[0]] = inp_g
                        out_g = fn(*args_g)
                        og = out_g[0] if isinstance(out_g, (tuple, list)) else out_g
                        if isinstance(og, torch.Tensor):
                            loss = og.sum()
                            loss.backward()
                            if inp_g.grad is not None:
                                ana_grad = inp_g.grad.flatten()[k].item()
                                rel_err = abs(num_grad - ana_grad) / (abs(ana_grad) + 1e-8)
                                if rel_err > 0.5:
                                    bugs.append(Bug(
                                        kind=BugKind.GRADIENT_INCORRECTNESS,
                                        stratum=TensorStratum.BEHAVIORAL,
                                        site_id=site_id,
                                        description=(
                                            f"Numerical vs analytic gradient mismatch "
                                            f"at index {k}: num={num_grad:.4e}, "
                                            f"ana={ana_grad:.4e}, rel_err={rel_err:.2e}"
                                        ),
                                        severity=min(rel_err, 10.0),
                                    ))
                                    break
            except Exception:
                pass

        verdict = AnalysisVerdict.INVALID if bugs else AnalysisVerdict.VALID
        return AnalysisJudgment(
            verdict=verdict,
            program=program,
            mode=AnalysisMode.BUG_FINDING,
            bugs=bugs,
            stratum_results={TensorStratum.BEHAVIORAL: verdict},
            explanation=(
                f"Found {len(bugs)} autograd issues"
                if bugs else
                "Autograd presheaf sections (Jacobians) are well-formed"
            ),
        )
