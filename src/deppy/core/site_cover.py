"""Full cover synthesis from Python AST / IR.

Implements **Algorithm 1** from the monograph: given a function's AST, produce
a :class:`Cover` populated with all 14 site families, restriction morphisms,
overlap edges, and boundary annotations.

The central class is :class:`SiteCoverSynthesizer`.  It orchestrates:

1. Parsing the source into an AST (if given a string).
2. Creating sites for each of the 14 families via :class:`SiteFactory`.
3. Building restriction morphisms between related sites.
4. Computing overlap edges via :class:`OverlapBuilder`.
5. Identifying input and output boundaries.
6. Registering error sites in :class:`ErrorSiteRegistry`.
7. Recording provenance in :class:`ProvenanceTracker`.

Usage::

    synth = SiteCoverSynthesizer()
    cover = synth.synthesize(source_code)
    # or
    cover = synth.synthesize(ast_node)
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import (
    Cover,
    Morphism,
    SiteId,
    SiteKind,
)
from deppy.core.site import (
    ConcreteMorphism,
    ConcreteSite,
    CoverBuilder as CoreCoverBuilder,
    SiteCategory,
)
from deppy.core.site_factory import SiteFactory
from deppy.core.overlap_builder import OverlapBuilder
from deppy.core.error_site_registry import (
    ErrorKind,
    ErrorSiteRegistry,
    OperationKind,
)
from deppy.core.boundary_synthesis import (
    BoundarySynthesizer,
    InputBoundaryExtractor,
    OutputBoundaryExtractor,
)
from deppy.core.provenance_tracker import (
    ASTNodeRef,
    DerivationReason,
    ProvenanceTracker,
)


# ═══════════════════════════════════════════════════════════════════════════════
# AST helpers
# ═══════════════════════════════════════════════════════════════════════════════


def _unparse_safe(node: Optional[ast.expr]) -> str:
    """Safely unparse an AST expression to a string."""
    if node is None:
        return ""
    try:
        return ast.unparse(node)
    except Exception:
        return "<unknown>"


def _node_line(node: ast.AST) -> int:
    """Extract the line number from an AST node."""
    return getattr(node, "lineno", 0)


def _node_col(node: ast.AST) -> int:
    """Extract the column offset from an AST node."""
    return getattr(node, "col_offset", 0)


def _callee_name(node: ast.expr) -> str:
    """Extract the callee name from a call expression."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        base = _callee_name(node.value)
        return f"{base}.{node.attr}" if base else node.attr
    return _unparse_safe(node)


def _exception_name(node: Optional[ast.expr]) -> str:
    """Extract exception class name from a raise expression."""
    if node is None:
        return "BaseException"
    if isinstance(node, ast.Call):
        return _exception_name(node.func)
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return _unparse_safe(node)


# ═══════════════════════════════════════════════════════════════════════════════
# SSA name counter
# ═══════════════════════════════════════════════════════════════════════════════


class _SSACounter:
    """Track SSA versions for variable names."""

    def __init__(self) -> None:
        self._versions: Dict[str, int] = {}

    def next_version(self, var_name: str) -> int:
        """Return the next SSA version for *var_name*."""
        v = self._versions.get(var_name, -1) + 1
        self._versions[var_name] = v
        return v

    def current_version(self, var_name: str) -> int:
        """Return the current (latest) SSA version."""
        return self._versions.get(var_name, 0)


# ═══════════════════════════════════════════════════════════════════════════════
# Tensor detector
# ═══════════════════════════════════════════════════════════════════════════════


_TENSOR_FRAMEWORKS = {
    "torch": {"Tensor", "tensor", "zeros", "ones", "randn", "rand", "empty",
              "zeros_like", "ones_like", "full", "arange", "linspace"},
    "numpy": {"array", "ndarray", "zeros", "ones", "empty", "full", "arange",
              "linspace", "reshape"},
    "jax": {"array", "zeros", "ones", "full", "arange", "DeviceArray"},
    "tensorflow": {"Tensor", "constant", "zeros", "ones", "Variable"},
}

_TENSOR_METHODS = {
    "reshape", "view", "permute", "transpose", "contiguous", "flatten",
    "squeeze", "unsqueeze", "expand", "repeat", "narrow", "index_select",
    "gather", "scatter", "matmul", "mm", "bmm", "conv1d", "conv2d",
    "cat", "stack", "split", "chunk",
}


def _is_tensor_call(node: ast.Call) -> Tuple[bool, str]:
    """Check if a call creates or manipulates a tensor.

    Returns (is_tensor, framework).
    """
    callee = _callee_name(node.func)
    for framework, names in _TENSOR_FRAMEWORKS.items():
        for name in names:
            if callee.endswith(name) or callee.endswith(f"{framework}.{name}"):
                return True, framework
    # Check for tensor method calls
    if isinstance(node.func, ast.Attribute) and node.func.attr in _TENSOR_METHODS:
        return True, "torch"
    return False, ""


# ═══════════════════════════════════════════════════════════════════════════════
# Error operation classifier
# ═══════════════════════════════════════════════════════════════════════════════


_OP_ERROR_MAP: Dict[str, List[Tuple[ErrorKind, OperationKind]]] = {
    "Subscript": [
        (ErrorKind.INDEX_ERROR, OperationKind.LIST_ACCESS),
        (ErrorKind.KEY_ERROR, OperationKind.DICT_LOOKUP),
        (ErrorKind.TYPE_ERROR, OperationKind.SUBSCRIPT),
    ],
    "Attribute": [
        (ErrorKind.ATTRIBUTE_ERROR, OperationKind.ATTRIBUTE_ACCESS),
    ],
    "Call": [
        (ErrorKind.TYPE_ERROR, OperationKind.CALL),
        (ErrorKind.VALUE_ERROR, OperationKind.CALL),
    ],
    "BinOp_Div": [
        (ErrorKind.ZERO_DIVISION_ERROR, OperationKind.DIVISION),
    ],
    "BinOp_Mod": [
        (ErrorKind.ZERO_DIVISION_ERROR, OperationKind.MODULO),
    ],
    "BinOp_Other": [
        (ErrorKind.TYPE_ERROR, OperationKind.BINARY_OP),
    ],
    "UnaryOp": [
        (ErrorKind.TYPE_ERROR, OperationKind.UNARY_OP),
    ],
    "For": [
        (ErrorKind.TYPE_ERROR, OperationKind.ITERATION),
    ],
    "Assert": [
        (ErrorKind.ASSERTION_ERROR, OperationKind.ASSERTION),
    ],
    "Import": [
        (ErrorKind.IMPORT_ERROR, OperationKind.IMPORT),
    ],
    "Starred": [
        (ErrorKind.VALUE_ERROR, OperationKind.UNPACKING),
    ],
}


# ═══════════════════════════════════════════════════════════════════════════════
# Cover synthesis result
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class CoverSynthesisResult:
    """Extended result from cover synthesis, including diagnostics."""

    cover: Cover
    provenance: ProvenanceTracker
    error_registry: ErrorSiteRegistry
    site_category: SiteCategory
    all_sites: Dict[SiteId, ConcreteSite] = field(default_factory=dict)
    warnings: List[str] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════════════════
# Site cover synthesizer
# ═══════════════════════════════════════════════════════════════════════════════


class SiteCoverSynthesizer:
    """Synthesize a Cover from Python source or AST.

    Implements Algorithm 1: given a function definition, produce a Cover
    with all 14 site families populated, restriction morphisms connecting
    related sites, overlap edges identifying where sites share information,
    and input/output boundary annotations.
    """

    def __init__(
        self,
        file_path: str = "",
        include_tensor_sites: bool = True,
        include_trace_sites: bool = True,
        include_proof_sites: bool = True,
        error_confidence_threshold: float = 0.3,
    ) -> None:
        self._file_path = file_path
        self._include_tensor = include_tensor_sites
        self._include_trace = include_trace_sites
        self._include_proof = include_proof_sites
        self._error_threshold = error_confidence_threshold

        # Sub-components
        self._factory = SiteFactory(file_path=file_path)
        self._overlap_builder = OverlapBuilder(
            confidence_threshold=error_confidence_threshold
        )
        self._error_registry = ErrorSiteRegistry()
        self._provenance = ProvenanceTracker()
        self._boundary_synth = BoundarySynthesizer(
            file_path=file_path, site_factory=self._factory
        )

        # Accumulated state during synthesis
        self._sites: Dict[SiteId, ConcreteSite] = {}
        self._morphisms: List[ConcreteMorphism] = []
        self._input_boundary: Set[SiteId] = set()
        self._output_boundary: Set[SiteId] = set()
        self._error_sites: Set[SiteId] = set()
        self._ssa = _SSACounter()
        self._category = SiteCategory()
        self._call_counter = 0
        self._error_counter = 0
        self._loop_counter = 0
        self._guard_counter = 0
        self._tensor_counter = 0
        self._try_depth = 0
        self._warnings: List[str] = []

    # ── Main entry point ───────────────────────────────────────────────────

    def synthesize(
        self, source_or_ast: Union[str, ast.FunctionDef, ast.AsyncFunctionDef, ast.Module]
    ) -> Cover:
        """Synthesize a complete Cover from source code or AST.

        Args:
            source_or_ast: Python source string, FunctionDef/AsyncFunctionDef,
                or Module AST.

        Returns:
            A fully populated :class:`Cover`.
        """
        self._reset()

        func_node = self._resolve_func(source_or_ast)
        if func_node is None:
            return Cover()

        # Phase 1: Create argument (input boundary) sites
        self._create_argument_sites(func_node)

        # Phase 2: Walk the function body creating all interior sites
        self._walk_body(func_node.body)

        # Phase 3: Create return/output boundary sites
        self._create_return_sites(func_node)

        # Phase 4: Create module summary site
        self._create_module_summary_sites(func_node)

        # Phase 5: Build restriction morphisms
        self._build_restriction_maps()

        # Phase 6: Compute overlaps
        overlaps = self._compute_overlaps()

        # Phase 7: Assemble the Cover
        builder = CoreCoverBuilder()
        for sid, site in self._sites.items():
            builder.add_site(site)
        for m in self._morphisms:
            builder.add_morphism(m)
        for a, b in overlaps:
            builder.add_overlap(a, b)
        for sid in self._error_sites:
            builder.mark_error(sid)
        for sid in self._input_boundary:
            builder.mark_input(sid)
        for sid in self._output_boundary:
            builder.mark_output(sid)

        return builder.build()

    def synthesize_full(
        self, source_or_ast: Union[str, ast.FunctionDef, ast.AsyncFunctionDef, ast.Module]
    ) -> CoverSynthesisResult:
        """Like synthesize but returns full diagnostics."""
        cover = self.synthesize(source_or_ast)
        return CoverSynthesisResult(
            cover=cover,
            provenance=self._provenance,
            error_registry=self._error_registry,
            site_category=self._category,
            all_sites=dict(self._sites),
            warnings=list(self._warnings),
        )

    # ── Phase 1: Argument sites ────────────────────────────────────────────

    def _create_argument_sites(
        self, func_node: Union[ast.FunctionDef, ast.AsyncFunctionDef]
    ) -> None:
        """Create ARGUMENT_BOUNDARY sites for each parameter."""
        extractor = InputBoundaryExtractor()
        params = extractor.extract(func_node)

        for param in params:
            site = self._factory.create_argument_site(
                param_name=param.name,
                param_index=param.index,
                annotation=param.annotation or None,
                has_default=param.has_default,
                source_line=func_node.lineno,
            )
            self._register_site(site, func_node, DerivationReason.ARGUMENT_SCAN,
                                f"parameter '{param.name}'")
            self._input_boundary.add(site.site_id)

            # Create initial SSA site for the parameter
            ver = self._ssa.next_version(param.name)
            ssa_site = self._factory.create_ssa_site(
                var_name=param.name,
                ssa_version=ver,
                defining_op="parameter",
                source_line=func_node.lineno,
            )
            self._register_site(ssa_site, func_node, DerivationReason.SSA_DEFINITION,
                                f"initial SSA for parameter '{param.name}'")

            # Morphism: argument -> SSA
            morph = ConcreteMorphism(
                _source=site.site_id,
                _target=ssa_site.site_id,
                projection=None,
                _metadata={"kind": "arg_to_ssa"},
            )
            self._register_morphism(morph)

    # ── Phase 2: Body walk ─────────────────────────────────────────────────

    def _walk_body(self, stmts: Sequence[ast.stmt]) -> None:
        """Recursively walk statements creating sites."""
        for stmt in stmts:
            self._visit_stmt(stmt)

    def _visit_stmt(self, node: ast.stmt) -> None:
        """Dispatch to the appropriate statement handler."""
        if isinstance(node, ast.Assign):
            self._visit_assign(node)
        elif isinstance(node, ast.AugAssign):
            self._visit_augassign(node)
        elif isinstance(node, ast.AnnAssign):
            self._visit_annassign(node)
        elif isinstance(node, ast.If):
            self._visit_if(node)
        elif isinstance(node, (ast.For, ast.AsyncFor)):
            self._visit_for(node)
        elif isinstance(node, ast.While):
            self._visit_while(node)
        elif isinstance(node, ast.Try):
            self._visit_try(node)
        elif isinstance(node, ast.With) or isinstance(node, ast.AsyncWith):
            self._visit_with(node)
        elif isinstance(node, ast.Expr):
            self._visit_expr_stmt(node)
        elif isinstance(node, ast.Assert):
            self._visit_assert(node)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            self._visit_import(node)
        elif isinstance(node, ast.Raise):
            self._visit_raise(node)
        elif isinstance(node, ast.Return):
            pass  # Handled in _create_return_sites
        elif hasattr(node, "body") and isinstance(getattr(node, "body", None), list):
            self._walk_body(node.body)

    # ── Assignment sites ───────────────────────────────────────────────────

    def _visit_assign(self, node: ast.Assign) -> None:
        """Create SSA and possibly call/tensor sites for an assignment."""
        # Analyze the RHS for call and tensor sites
        self._visit_value_expr(node.value, node)

        # Create SSA sites for each target
        for target in node.targets:
            self._create_ssa_sites_for_target(target, node)

    def _visit_augassign(self, node: ast.AugAssign) -> None:
        """Handle augmented assignment (e.g. x += 1)."""
        self._visit_value_expr(node.value, node)

        if isinstance(node.target, ast.Name):
            var_name = node.target.id
            ver = self._ssa.next_version(var_name)
            site = self._factory.create_ssa_site(
                var_name=var_name,
                ssa_version=ver,
                defining_op=f"augassign_{type(node.op).__name__}",
                source_line=_node_line(node),
                source_col=_node_col(node),
            )
            self._register_site(site, node, DerivationReason.SSA_DEFINITION,
                                f"augmented assignment to '{var_name}'")

        # Check for potential errors (division/modulo)
        if isinstance(node.op, (ast.Div, ast.FloorDiv)):
            self._create_error_for_op(node, "BinOp_Div", _unparse_safe(node.target))
        elif isinstance(node.op, ast.Mod):
            self._create_error_for_op(node, "BinOp_Mod", _unparse_safe(node.target))

    def _visit_annassign(self, node: ast.AnnAssign) -> None:
        """Handle annotated assignment (e.g. x: int = 5)."""
        if node.value is not None:
            self._visit_value_expr(node.value, node)

        if isinstance(node.target, ast.Name) and node.value is not None:
            var_name = node.target.id
            ver = self._ssa.next_version(var_name)
            site = self._factory.create_ssa_site(
                var_name=var_name,
                ssa_version=ver,
                defining_op="annassign",
                source_line=_node_line(node),
                source_col=_node_col(node),
            )
            self._register_site(site, node, DerivationReason.SSA_DEFINITION,
                                f"annotated assignment to '{var_name}'")

    def _create_ssa_sites_for_target(
        self, target: ast.expr, parent: ast.AST
    ) -> None:
        """Create SSA sites for assignment targets (handles unpacking)."""
        if isinstance(target, ast.Name):
            var_name = target.id
            ver = self._ssa.next_version(var_name)
            site = self._factory.create_ssa_site(
                var_name=var_name,
                ssa_version=ver,
                defining_op="assign",
                source_line=_node_line(target),
                source_col=_node_col(target),
            )
            self._register_site(site, parent, DerivationReason.SSA_DEFINITION,
                                f"assignment to '{var_name}'")
        elif isinstance(target, (ast.Tuple, ast.List)):
            for elt in target.elts:
                self._create_ssa_sites_for_target(elt, parent)
        elif isinstance(target, ast.Starred):
            if isinstance(target.value, ast.Name):
                var_name = target.value.id
                ver = self._ssa.next_version(var_name)
                site = self._factory.create_ssa_site(
                    var_name=var_name,
                    ssa_version=ver,
                    defining_op="starred_unpack",
                    source_line=_node_line(target),
                    source_col=_node_col(target),
                )
                self._register_site(site, parent, DerivationReason.SSA_DEFINITION,
                                    f"starred assignment to '{var_name}'")

    # ── Value expression analysis ──────────────────────────────────────────

    def _visit_value_expr(self, node: ast.expr, parent: ast.AST) -> None:
        """Analyze a value expression for calls, tensor ops, subscripts, etc."""
        if isinstance(node, ast.Call):
            self._create_call_sites(node, parent)
        elif isinstance(node, ast.Subscript):
            self._create_error_for_op(node, "Subscript", _unparse_safe(node))
        elif isinstance(node, ast.Attribute):
            self._create_error_for_op(node, "Attribute", _unparse_safe(node))
        elif isinstance(node, ast.BinOp):
            if isinstance(node.op, (ast.Div, ast.FloorDiv)):
                self._create_error_for_op(node, "BinOp_Div", _unparse_safe(node))
            elif isinstance(node.op, ast.Mod):
                self._create_error_for_op(node, "BinOp_Mod", _unparse_safe(node))
            self._visit_value_expr(node.left, parent)
            self._visit_value_expr(node.right, parent)
        elif isinstance(node, ast.UnaryOp):
            self._visit_value_expr(node.operand, parent)
        elif isinstance(node, ast.IfExp):
            self._visit_value_expr(node.body, parent)
            self._visit_value_expr(node.orelse, parent)
        elif isinstance(node, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
            pass  # Comprehensions are complex; skip deep analysis
        elif isinstance(node, ast.DictComp):
            pass

        # Recurse into sub-expressions
        if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
            for elt in node.elts:
                self._visit_value_expr(elt, parent)
        elif isinstance(node, ast.Dict):
            for v in node.values:
                if v is not None:
                    self._visit_value_expr(v, parent)

    # ── Call sites ─────────────────────────────────────────────────────────

    def _create_call_sites(self, node: ast.Call, parent: ast.AST) -> None:
        """Create CALL_RESULT and possibly TENSOR sites for a call."""
        callee = _callee_name(node.func)
        self._call_counter += 1

        site = self._factory.create_call_site(
            callee_name=callee,
            call_index=self._call_counter,
            is_method=isinstance(node.func, ast.Attribute),
            arg_count=len(node.args) + len(node.keywords),
            source_line=_node_line(node),
            source_col=_node_col(node),
        )
        self._register_site(site, node, DerivationReason.CALL_RETURN,
                            f"call to '{callee}'")

        # Check for call-site errors (TypeError, ValueError)
        self._create_error_for_op(node, "Call", callee)

        # Tensor detection
        if self._include_tensor:
            is_tensor, framework = _is_tensor_call(node)
            if is_tensor:
                self._create_tensor_sites(node, callee, framework)

        # Recurse into call arguments
        for arg in node.args:
            self._visit_value_expr(arg, parent)
        for kw in node.keywords:
            self._visit_value_expr(kw.value, parent)

    # ── Tensor sites ───────────────────────────────────────────────────────

    def _create_tensor_sites(
        self, node: ast.Call, tensor_name: str, framework: str
    ) -> None:
        """Create TENSOR_SHAPE, TENSOR_ORDER, TENSOR_INDEXING sites."""
        self._tensor_counter += 1
        label = f"{tensor_name}_{self._tensor_counter}"

        # Shape site
        shape_site = self._factory.create_tensor_shape_site(
            tensor_name=label,
            framework=framework,
            source_line=_node_line(node),
            source_col=_node_col(node),
        )
        self._register_site(shape_site, node, DerivationReason.TENSOR_SHAPE_INFERENCE,
                            f"tensor shape for '{tensor_name}'")

        # Order site
        order_site = self._factory.create_tensor_order_site(
            tensor_name=label,
            source_line=_node_line(node),
            source_col=_node_col(node),
        )
        self._register_site(order_site, node, DerivationReason.TENSOR_ORDER_INFERENCE,
                            f"tensor order for '{tensor_name}'")

        # Morphism: shape -> order (shape determines order constraints)
        morph = ConcreteMorphism(
            _source=shape_site.site_id,
            _target=order_site.site_id,
            _metadata={"kind": "tensor_shape_to_order"},
        )
        self._register_morphism(morph)

    # ── Branch guard sites ─────────────────────────────────────────────────

    def _visit_if(self, node: ast.If) -> None:
        """Create BRANCH_GUARD sites for an if statement."""
        self._guard_counter += 1
        guard_id = f"if_{self._guard_counter}"
        condition_text = _unparse_safe(node.test)

        # Detect narrowed variables from the condition
        narrowed_vars = self._extract_narrowed_vars(node.test)

        # True branch guard
        true_site = self._factory.create_branch_guard_site(
            guard_id=guard_id,
            condition_text=condition_text,
            narrowed_vars=narrowed_vars,
            is_true_branch=True,
            source_line=_node_line(node),
            source_col=_node_col(node),
        )
        self._register_site(true_site, node, DerivationReason.BRANCH_GUARD_EXTRACTION,
                            f"true branch of '{condition_text}'")

        # False branch guard
        false_site = self._factory.create_branch_guard_site(
            guard_id=guard_id,
            condition_text=condition_text,
            narrowed_vars=narrowed_vars,
            is_true_branch=False,
            source_line=_node_line(node),
            source_col=_node_col(node),
        )
        self._register_site(false_site, node, DerivationReason.BRANCH_GUARD_EXTRACTION,
                            f"false branch of '{condition_text}'")

        # Morphism: true -> false (complementary branches)
        morph = ConcreteMorphism(
            _source=true_site.site_id,
            _target=false_site.site_id,
            _metadata={"kind": "branch_complement"},
        )
        self._register_morphism(morph)

        # Walk the branches
        self._walk_body(node.body)
        if node.orelse:
            self._walk_body(node.orelse)

    def _extract_narrowed_vars(self, test: ast.expr) -> List[str]:
        """Extract variable names narrowed by a condition."""
        narrowed: List[str] = []

        if isinstance(test, ast.Compare):
            # isinstance(x, T) check
            if (len(test.ops) == 1 and isinstance(test.ops[0], ast.Is)):
                if isinstance(test.left, ast.Name):
                    narrowed.append(test.left.id)
            # x is None / x is not None
            for comparator in test.comparators:
                if isinstance(comparator, ast.Constant) and comparator.value is None:
                    if isinstance(test.left, ast.Name):
                        narrowed.append(test.left.id)
        elif isinstance(test, ast.Call):
            if isinstance(test.func, ast.Name) and test.func.id == "isinstance":
                if test.args and isinstance(test.args[0], ast.Name):
                    narrowed.append(test.args[0].id)
            elif isinstance(test.func, ast.Name) and test.func.id == "callable":
                if test.args and isinstance(test.args[0], ast.Name):
                    narrowed.append(test.args[0].id)
        elif isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
            narrowed.extend(self._extract_narrowed_vars(test.operand))
        elif isinstance(test, ast.BoolOp):
            for val in test.values:
                narrowed.extend(self._extract_narrowed_vars(val))
        elif isinstance(test, ast.Name):
            narrowed.append(test.id)

        return narrowed

    # ── Loop sites ─────────────────────────────────────────────────────────

    def _visit_for(self, node: Union[ast.For, ast.AsyncFor]) -> None:
        """Create LOOP_HEADER_INVARIANT site for a for loop."""
        self._loop_counter += 1
        loop_id = f"for_{self._loop_counter}"

        # Extract loop variable name
        loop_var = ""
        if isinstance(node.target, ast.Name):
            loop_var = node.target.id
        elif isinstance(node.target, (ast.Tuple, ast.List)):
            parts = []
            for elt in node.target.elts:
                if isinstance(elt, ast.Name):
                    parts.append(elt.id)
            loop_var = ",".join(parts)

        loop_site = self._factory.create_loop_site(
            loop_id=loop_id,
            loop_variable=loop_var,
            source_line=_node_line(node),
            source_col=_node_col(node),
        )
        self._register_site(loop_site, node, DerivationReason.LOOP_HEADER_EXTRACTION,
                            f"for loop over '{loop_var}'")

        # Create SSA site for loop variable
        if isinstance(node.target, ast.Name):
            ver = self._ssa.next_version(node.target.id)
            ssa_site = self._factory.create_ssa_site(
                var_name=node.target.id,
                ssa_version=ver,
                defining_op="for_target",
                source_line=_node_line(node.target),
                source_col=_node_col(node.target),
            )
            self._register_site(ssa_site, node, DerivationReason.SSA_DEFINITION,
                                f"loop variable '{node.target.id}'")

            # Morphism: loop header -> SSA
            morph = ConcreteMorphism(
                _source=loop_site.site_id,
                _target=ssa_site.site_id,
                _metadata={"kind": "loop_to_var"},
            )
            self._register_morphism(morph)

        # Iteration error
        self._create_error_for_op(node, "For", _unparse_safe(node.iter))

        # Visit iterable expression
        self._visit_value_expr(node.iter, node)

        self._walk_body(node.body)
        if node.orelse:
            self._walk_body(node.orelse)

    def _visit_while(self, node: ast.While) -> None:
        """Create LOOP_HEADER_INVARIANT site for a while loop."""
        self._loop_counter += 1
        loop_id = f"while_{self._loop_counter}"
        condition = _unparse_safe(node.test)

        loop_site = self._factory.create_loop_site(
            loop_id=loop_id,
            loop_variable=condition,
            is_while=True,
            source_line=_node_line(node),
            source_col=_node_col(node),
        )
        self._register_site(loop_site, node, DerivationReason.LOOP_HEADER_EXTRACTION,
                            f"while loop: {condition}")

        self._walk_body(node.body)
        if node.orelse:
            self._walk_body(node.orelse)

    # ── Try/except sites ───────────────────────────────────────────────────

    def _visit_try(self, node: ast.Try) -> None:
        """Walk try/except, marking error sites as guarded."""
        self._try_depth += 1
        self._walk_body(node.body)
        self._try_depth -= 1

        for handler in node.handlers:
            self._walk_body(handler.body)

        if node.orelse:
            self._walk_body(node.orelse)
        if node.finalbody:
            self._walk_body(node.finalbody)

    # ── With statement ─────────────────────────────────────────────────────

    def _visit_with(self, node: Union[ast.With, ast.AsyncWith]) -> None:
        """Handle with statement -- create SSA sites for 'as' targets."""
        for item in node.items:
            self._visit_value_expr(item.context_expr, node)
            if item.optional_vars is not None:
                self._create_ssa_sites_for_target(item.optional_vars, node)
        self._walk_body(node.body)

    # ── Expression statement ───────────────────────────────────────────────

    def _visit_expr_stmt(self, node: ast.Expr) -> None:
        """Handle expression statements (calls, yields)."""
        self._visit_value_expr(node.value, node)

    # ── Assert statement ───────────────────────────────────────────────────

    def _visit_assert(self, node: ast.Assert) -> None:
        """Create proof site and error site for assert."""
        self._create_error_for_op(node, "Assert", _unparse_safe(node.test))

        if self._include_proof:
            self._create_proof_sites(node)

    # ── Import statement ───────────────────────────────────────────────────

    def _visit_import(self, node: Union[ast.Import, ast.ImportFrom]) -> None:
        """Create error sites for imports that may fail."""
        self._create_error_for_op(node, "Import", "")

        # Create SSA sites for imported names
        if isinstance(node, ast.Import):
            for alias in node.names:
                name = alias.asname or alias.name.split(".")[0]
                ver = self._ssa.next_version(name)
                site = self._factory.create_ssa_site(
                    var_name=name,
                    ssa_version=ver,
                    defining_op="import",
                    source_line=_node_line(node),
                )
                self._register_site(site, node, DerivationReason.SSA_DEFINITION,
                                    f"import '{alias.name}'")
        elif isinstance(node, ast.ImportFrom):
            for alias in node.names:
                name = alias.asname or alias.name
                if name == "*":
                    continue
                ver = self._ssa.next_version(name)
                site = self._factory.create_ssa_site(
                    var_name=name,
                    ssa_version=ver,
                    defining_op="import_from",
                    source_line=_node_line(node),
                )
                self._register_site(site, node, DerivationReason.SSA_DEFINITION,
                                    f"from {node.module} import {alias.name}")

    # ── Raise statement ────────────────────────────────────────────────────

    def _visit_raise(self, node: ast.Raise) -> None:
        """Create error site for explicit raise."""
        exc_name = _exception_name(node.exc)
        self._error_counter += 1

        error_kind = ErrorKind.from_exception_name(exc_name)
        site = self._factory.create_error_site(
            error_kind=exc_name,
            error_index=self._error_counter,
            viability="explicit raise",
            guarded=self._try_depth > 0,
            source_op=f"raise {exc_name}",
            source_line=_node_line(node),
            source_col=_node_col(node),
        )
        self._register_site(site, node, DerivationReason.ERROR_PATH_ANALYSIS,
                            f"explicit raise {exc_name}")
        self._error_sites.add(site.site_id)

        self._error_registry.register_error_site(
            site_id=site.site_id,
            error_kind=error_kind,
            operation=OperationKind.CALL,
            source_operation=f"raise {exc_name}",
            source_line=_node_line(node),
            is_explicit_raise=True,
            guarded=self._try_depth > 0,
        )

    # ── Error site creation helper ─────────────────────────────────────────

    def _create_error_for_op(
        self, node: ast.AST, op_category: str, source_op: str
    ) -> None:
        """Create error sites for an operation category."""
        error_pairs = _OP_ERROR_MAP.get(op_category, [])
        if not error_pairs:
            return

        for error_kind, op_kind in error_pairs:
            self._error_counter += 1
            guarded = self._try_depth > 0

            site = self._factory.create_error_site(
                error_kind=error_kind.value,
                error_index=self._error_counter,
                guarded=guarded,
                source_op=source_op,
                source_line=_node_line(node),
                source_col=_node_col(node),
            )
            self._register_site(site, node, DerivationReason.ERROR_PATH_ANALYSIS,
                                f"{error_kind.value} from {op_category}")
            self._error_sites.add(site.site_id)

            self._error_registry.register_error_site(
                site_id=site.site_id,
                error_kind=error_kind,
                operation=op_kind,
                source_operation=source_op,
                source_line=_node_line(node),
                guarded=guarded,
            )

    # ── Proof sites ────────────────────────────────────────────────────────

    def _create_proof_sites(self, node: ast.Assert) -> None:
        """Create PROOF sites for assertions."""
        proposition = _unparse_safe(node.test)
        proof_name = f"assert_{_node_line(node)}"

        site = self._factory.create_proof_site(
            proof_name=proof_name,
            proposition=proposition,
            status="asserted",
            source_line=_node_line(node),
            source_col=_node_col(node),
        )
        self._register_site(site, node, DerivationReason.PROOF_OBLIGATION,
                            f"assertion: {proposition}")

    # ── Trace sites ────────────────────────────────────────────────────────

    def _create_trace_sites_for_call(
        self, node: ast.Call, callee: str
    ) -> None:
        """Create TRACE sites for calls to logging/tracing functions."""
        trace_funcs = {"print", "logging.info", "logging.debug",
                       "logging.warning", "logging.error", "logger.info",
                       "logger.debug", "logger.warning"}
        if callee not in trace_funcs:
            return

        if not self._include_trace:
            return

        trace_name = f"trace_{callee}_{_node_line(node)}"
        site = self._factory.create_trace_site(
            trace_name=trace_name,
            trace_point=callee,
            source_line=_node_line(node),
            source_col=_node_col(node),
        )
        self._register_site(site, node, DerivationReason.TRACE_INSTRUMENTATION,
                            f"trace at {callee}")

    # ── Heap sites ─────────────────────────────────────────────────────────

    def _create_heap_sites(self, node: ast.AST, object_name: str) -> None:
        """Create HEAP_PROTOCOL site for an object that uses heap protocol."""
        site = self._factory.create_heap_site(
            object_name=object_name,
            source_line=_node_line(node),
            source_col=_node_col(node),
        )
        self._register_site(site, node, DerivationReason.HEAP_PROTOCOL_DETECTION,
                            f"heap object '{object_name}'")

    # ── Phase 3: Return / output boundary sites ────────────────────────────

    def _create_return_sites(
        self, func_node: Union[ast.FunctionDef, ast.AsyncFunctionDef]
    ) -> None:
        """Create RETURN_OUTPUT_BOUNDARY sites."""
        extractor = OutputBoundaryExtractor()
        outputs = extractor.extract(func_node)

        for out in outputs:
            if out.kind == "return":
                site = self._factory.create_return_site(
                    return_index=out.index,
                    source_line=out.line,
                    source_col=out.col,
                )
            elif out.kind == "raise":
                site = self._factory.create_return_site(
                    return_index=out.index,
                    is_raise=True,
                    source_line=out.line,
                    source_col=out.col,
                )
            elif out.kind in ("yield", "yield_from"):
                site = self._factory.create_return_site(
                    return_index=out.index,
                    is_yield=True,
                    source_line=out.line,
                    source_col=out.col,
                )
            else:
                continue

            self._register_site(
                site, func_node, DerivationReason.RETURN_SITE_EXTRACTION,
                f"{out.kind} at line {out.line}"
            )
            self._output_boundary.add(site.site_id)

    # ── Phase 4: Module summary sites ──────────────────────────────────────

    def _create_module_summary_sites(
        self, func_node: Union[ast.FunctionDef, ast.AsyncFunctionDef]
    ) -> None:
        """Create MODULE_SUMMARY site for the function."""
        site = self._factory.create_module_summary_site(
            module_name=func_node.name,
            source_line=_node_line(func_node),
        )
        self._register_site(site, func_node, DerivationReason.MODULE_SUMMARY,
                            f"summary for function '{func_node.name}'")

    # ── Phase 5: Restriction morphisms ─────────────────────────────────────

    def _build_restriction_maps(self) -> None:
        """Build restriction morphisms between related sites.

        Creates morphisms for:
        - SSA lineage chains (v_n -> v_{n+1})
        - Branch guard -> narrowed SSA sites
        - Call result -> SSA sites receiving result
        - Loop header -> loop variable SSA
        """
        ssa_by_var: Dict[str, List[Tuple[int, SiteId]]] = {}
        guard_sites: List[Tuple[SiteId, Any]] = []
        call_sites: List[Tuple[SiteId, Any]] = []

        for sid, site in self._sites.items():
            meta = site.metadata or {}
            if sid.kind == SiteKind.SSA_VALUE:
                var_name = meta.get("var_name", "")
                version = meta.get("ssa_version", 0)
                ssa_by_var.setdefault(var_name, []).append((version, sid))
            elif sid.kind == SiteKind.BRANCH_GUARD:
                guard_sites.append((sid, meta))
            elif sid.kind == SiteKind.CALL_RESULT:
                call_sites.append((sid, meta))

        # SSA lineage chains: consecutive versions of same variable
        for var_name, versions in ssa_by_var.items():
            sorted_versions = sorted(versions, key=lambda x: x[0])
            for i in range(len(sorted_versions) - 1):
                _, src_sid = sorted_versions[i]
                _, tgt_sid = sorted_versions[i + 1]
                morph = ConcreteMorphism(
                    _source=src_sid,
                    _target=tgt_sid,
                    _metadata={"kind": "ssa_lineage", "var": var_name},
                )
                self._register_morphism(morph)

        # Guard -> SSA narrowing morphisms
        for guard_sid, meta in guard_sites:
            narrowed_vars = meta.get("narrowed_vars", [])
            if not isinstance(narrowed_vars, list):
                continue
            for var_name in narrowed_vars:
                if var_name in ssa_by_var:
                    # Connect guard to most recent SSA version
                    sorted_versions = sorted(ssa_by_var[var_name], key=lambda x: x[0])
                    _, latest_sid = sorted_versions[-1]
                    morph = ConcreteMorphism(
                        _source=guard_sid,
                        _target=latest_sid,
                        _metadata={"kind": "guard_narrows", "var": var_name},
                    )
                    self._register_morphism(morph)

    # ── Phase 6: Overlaps ──────────────────────────────────────────────────

    def _compute_overlaps(self) -> List[Tuple[SiteId, SiteId]]:
        """Compute all overlap pairs using the OverlapBuilder."""
        return self._overlap_builder.build_overlaps(
            self._sites, self._morphisms
        )

    # ── Registration helpers ───────────────────────────────────────────────

    def _register_site(
        self,
        site: ConcreteSite,
        ast_node: ast.AST,
        reason: DerivationReason,
        description: str = "",
    ) -> None:
        """Register a site in the accumulated state."""
        self._sites[site.site_id] = site
        self._category.add_site(site)
        self._provenance.record_site_creation(
            site_id=site.site_id,
            source_node=ast_node,
            reason=reason,
            description=description,
            file_path=self._file_path,
        )

    def _register_morphism(self, morph: ConcreteMorphism) -> None:
        """Register a morphism in the accumulated state."""
        self._morphisms.append(morph)
        self._category.add_morphism(morph)

    # ── AST resolution ─────────────────────────────────────────────────────

    def _resolve_func(
        self, source_or_ast: Union[str, ast.FunctionDef, ast.AsyncFunctionDef, ast.Module]
    ) -> Optional[Union[ast.FunctionDef, ast.AsyncFunctionDef]]:
        """Resolve input to a FunctionDef node."""
        if isinstance(source_or_ast, str):
            tree = ast.parse(source_or_ast)
            return self._find_func(tree)
        if isinstance(source_or_ast, ast.Module):
            return self._find_func(source_or_ast)
        return source_or_ast

    @staticmethod
    def _find_func(
        tree: ast.Module,
    ) -> Optional[Union[ast.FunctionDef, ast.AsyncFunctionDef]]:
        """Find the first function definition in a module."""
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                return node
        return None

    # ── Reset ──────────────────────────────────────────────────────────────

    def _reset(self) -> None:
        """Reset all accumulated state for a fresh synthesis."""
        self._sites.clear()
        self._morphisms.clear()
        self._input_boundary.clear()
        self._output_boundary.clear()
        self._error_sites.clear()
        self._ssa = _SSACounter()
        self._category = SiteCategory()
        self._factory.reset_counters()
        self._provenance.clear()
        self._error_registry.clear_sites()
        self._call_counter = 0
        self._error_counter = 0
        self._loop_counter = 0
        self._guard_counter = 0
        self._tensor_counter = 0
        self._try_depth = 0
        self._warnings.clear()

    # ── Diagnostics ────────────────────────────────────────────────────────

    @property
    def last_provenance(self) -> ProvenanceTracker:
        """Provenance from the last synthesis run."""
        return self._provenance

    @property
    def last_error_registry(self) -> ErrorSiteRegistry:
        """Error registry from the last synthesis run."""
        return self._error_registry

    def __repr__(self) -> str:
        return (
            f"SiteCoverSynthesizer(file={self._file_path!r}, "
            f"sites={len(self._sites)})"
        )
