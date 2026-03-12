"""Cover synthesis from Python AST — Algorithm 1 of the monograph.

This module implements the first stage of the sheaf-descent pipeline:
constructing the observation site cover from a Python AST.  The output
is a ``Cover`` object (from ``deppy.core._protocols``) containing sites,
morphisms, overlaps, and boundary classifications.

Algorithm 1 (Cover Synthesis):
1. Parse the module and lower every function to site nodes for arguments,
   returns, SSA values, branch guards, calls, library triggers, proof
   artifacts, traces, and error-sensitive operations.
2. Insert overlap edges whenever two sites share lineage, control
   provenance, or pack-declared transport structure.
3. Audit the resulting cover for sparsity so that low-value sites can be
   summarized before local solving begins.

The cover is a *durable artifact* — it is the first-class data structure
over which theory packs, local solvers, descent, and rendering operate.
"""

from __future__ import annotations

import ast
import itertools
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
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
    BoundarySection,
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite, SiteCategory

from deppy.static_analysis.observation_sites import (
    ErrorKind,
    SourceSpan,
    make_argument_boundary_site,
    make_branch_guard_site,
    make_call_result_site,
    make_error_site,
    make_heap_protocol_site,
    make_loop_invariant_site,
    make_module_summary_site,
    make_proof_site,
    make_return_boundary_site,
    make_ssa_value_site,
    make_tensor_indexing_site,
    make_tensor_order_site,
    make_tensor_shape_site,
    make_trace_site,
)
from deppy.static_analysis.restriction_maps import (
    RestrictionKind,
    find_overlaps,
    make_control_restriction,
    make_error_pullback_restriction,
    make_error_viability_restriction,
    make_input_projection,
    make_lineage_restriction,
    make_output_projection,
    make_phi_merge_restriction,
)


# ---------------------------------------------------------------------------
# Version counter for SSA-like naming without classical SSA infrastructure
# ---------------------------------------------------------------------------

class _VersionCounter:
    """Assign monotonically increasing versions to variable names."""

    def __init__(self) -> None:
        self._counts: Dict[str, int] = {}

    def next_version(self, name: str) -> int:
        v = self._counts.get(name, 0)
        self._counts[name] = v + 1
        return v

    def current_version(self, name: str) -> int:
        return self._counts.get(name, 0) - 1


# ---------------------------------------------------------------------------
# Cover builder
# ---------------------------------------------------------------------------

class CoverBuilder:
    """Incrementally builds a sheaf cover from Python AST fragments.

    Usage::

        builder = CoverBuilder("my_module.py")
        builder.add_function(func_ast, "my_func")
        cover = builder.build()

    The resulting ``Cover`` is a first-class artifact containing all sites,
    morphisms, overlaps, and boundary classifications.
    """

    def __init__(self, filename: str = "<unknown>") -> None:
        self._filename = filename
        self._sites: Dict[SiteId, ConcreteSite] = {}
        self._morphisms: List[ConcreteMorphism] = []
        self._error_sites: Set[SiteId] = set()
        self._input_boundary: Set[SiteId] = set()
        self._output_boundary: Set[SiteId] = set()
        self._versions = _VersionCounter()
        self._func_counter = 0

    # -- Site registration ---------------------------------------------------

    def _register_site(self, site: ConcreteSite) -> SiteId:
        self._sites[site.site_id] = site
        return site.site_id

    def _register_morphism(self, morphism: ConcreteMorphism) -> None:
        self._morphisms.append(morphism)

    # -- Function-level cover construction -----------------------------------

    def add_function(
        self,
        func_node: ast.FunctionDef,
        func_name: Optional[str] = None,
    ) -> None:
        """Add all sites and morphisms for a function definition."""
        name = func_name or func_node.name
        self._func_counter += 1

        # 1. Argument-boundary sites
        arg_sites = self._add_argument_sites(func_node, name)

        # 2. Walk the function body to create interior sites
        body_visitor = _FunctionBodyVisitor(
            builder=self,
            func_name=name,
            filename=self._filename,
            arg_site_ids=arg_sites,
        )
        for stmt in func_node.body:
            body_visitor.visit(stmt)

        # 3. Return / output-boundary sites
        return_sites = body_visitor.return_site_ids
        for sid in return_sites:
            self._output_boundary.add(sid)

        # 4. Connect arguments to interior via input projections
        for arg_sid in arg_sites.values():
            self._input_boundary.add(arg_sid)
            # Connect to any SSA site that references this argument
            for ssa_sid, ssa_site in list(self._sites.items()):
                if ssa_sid.kind == SiteKind.SSA_VALUE:
                    data = ssa_site.metadata.get("data") if ssa_site.metadata else None
                    if data and hasattr(data, "lineage_parent"):
                        if data.lineage_parent == arg_sid.name:
                            self._register_morphism(
                                make_lineage_restriction(arg_sid, ssa_sid)
                            )

    def _add_argument_sites(
        self,
        func_node: ast.FunctionDef,
        func_name: str,
    ) -> Dict[str, SiteId]:
        """Create argument-boundary sites for all parameters."""
        arg_sites: Dict[str, SiteId] = {}
        args = func_node.args

        # Positional args
        all_args = list(args.args)
        defaults_offset = len(all_args) - len(args.defaults)

        for i, arg in enumerate(all_args):
            span = SourceSpan.from_ast(arg, self._filename)
            default = None
            if i >= defaults_offset:
                default = args.defaults[i - defaults_offset]

            site = make_argument_boundary_site(
                func_name=func_name,
                param_name=arg.arg,
                param_index=i,
                span=span,
                annotation=arg.annotation,
                default_value=default,
                is_self=(i == 0 and arg.arg == "self"),
            )
            sid = self._register_site(site)
            arg_sites[arg.arg] = sid

        # *args
        if args.vararg:
            span = SourceSpan.from_ast(args.vararg, self._filename)
            site = make_argument_boundary_site(
                func_name=func_name,
                param_name=f"*{args.vararg.arg}",
                param_index=len(all_args),
                span=span,
                annotation=args.vararg.annotation,
            )
            sid = self._register_site(site)
            arg_sites[f"*{args.vararg.arg}"] = sid

        # **kwargs
        if args.kwarg:
            span = SourceSpan.from_ast(args.kwarg, self._filename)
            site = make_argument_boundary_site(
                func_name=func_name,
                param_name=f"**{args.kwarg.arg}",
                param_index=len(all_args) + (1 if args.vararg else 0),
                span=span,
                annotation=args.kwarg.annotation,
            )
            sid = self._register_site(site)
            arg_sites[f"**{args.kwarg.arg}"] = sid

        # Keyword-only
        for i, arg in enumerate(args.kwonlyargs):
            span = SourceSpan.from_ast(arg, self._filename)
            default = None
            if i < len(args.kw_defaults) and args.kw_defaults[i] is not None:
                default = args.kw_defaults[i]
            site = make_argument_boundary_site(
                func_name=func_name,
                param_name=arg.arg,
                param_index=len(all_args) + (1 if args.vararg else 0) +
                            (1 if args.kwarg else 0) + i,
                span=span,
                annotation=arg.annotation,
                default_value=default,
            )
            sid = self._register_site(site)
            arg_sites[arg.arg] = sid

        return arg_sites

    # -- Module-level cover construction -------------------------------------

    def add_module(self, module_node: ast.Module, module_name: str = "<module>") -> None:
        """Add sites for an entire module."""
        exported_funcs: List[str] = []
        exported_classes: List[str] = []

        for node in ast.iter_child_nodes(module_node):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                self.add_function(node, node.name)
                exported_funcs.append(node.name)
            elif isinstance(node, ast.ClassDef):
                self._add_class(node)
                exported_classes.append(node.name)

        # Module-summary site
        span = SourceSpan(self._filename, 1, 0)
        summary = make_module_summary_site(
            module_name=module_name,
            span=span,
            exported_functions=exported_funcs,
            exported_classes=exported_classes,
        )
        self._register_site(summary)

    def _add_class(self, class_node: ast.ClassDef) -> None:
        """Add sites for a class definition."""
        for node in class_node.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                self.add_function(node, f"{class_node.name}.{node.name}")

    # -- Build the final Cover -----------------------------------------------

    def build(self) -> Cover:
        """Finalize and return the Cover artifact.

        This computes overlaps from the morphism structure and returns
        the complete cover ready for local solving and descent.
        """
        site_ids = list(self._sites.keys())
        overlaps = find_overlaps(site_ids, self._morphisms)

        cover = Cover(
            sites={sid: site for sid, site in self._sites.items()},
            morphisms=list(self._morphisms),
            overlaps=overlaps,
            error_sites=set(self._error_sites),
            input_boundary=set(self._input_boundary),
            output_boundary=set(self._output_boundary),
        )
        return cover

    # -- Source-level cover construction from string -------------------------

    @classmethod
    def from_source(cls, source: str, filename: str = "<string>") -> Cover:
        """Build a cover from Python source code string."""
        tree = ast.parse(source, filename=filename)
        builder = cls(filename)
        builder.add_module(tree, module_name=filename)
        return builder.build()

    @classmethod
    def from_file(cls, filepath: str) -> Cover:
        """Build a cover from a Python source file."""
        with open(filepath, "r") as f:
            source = f.read()
        return cls.from_source(source, filename=filepath)


# ---------------------------------------------------------------------------
# Function body visitor — creates interior sites from AST statements
# ---------------------------------------------------------------------------

class _FunctionBodyVisitor(ast.NodeVisitor):
    """Walk a function body and create observation sites for each statement."""

    def __init__(
        self,
        builder: CoverBuilder,
        func_name: str,
        filename: str,
        arg_site_ids: Dict[str, SiteId],
    ) -> None:
        self._builder = builder
        self._func_name = func_name
        self._filename = filename
        self._arg_sites = arg_site_ids
        self._versions = _VersionCounter()
        self._label_counter = 0
        self.return_site_ids: List[SiteId] = []
        # Track last SSA site per variable for lineage
        self._var_sites: Dict[str, SiteId] = {}
        # Seed var_sites from arguments
        for arg_name, arg_sid in arg_site_ids.items():
            clean = arg_name.lstrip("*")
            self._var_sites[clean] = arg_sid

    def _next_label(self, prefix: str = "") -> str:
        self._label_counter += 1
        return f"{prefix}{self._label_counter}"

    def _span(self, node: ast.AST) -> SourceSpan:
        return SourceSpan.from_ast(node, self._filename)

    # -- Assignments: create SSA-value sites ---------------------------------

    def visit_Assign(self, node: ast.Assign) -> None:
        for target in node.targets:
            self._create_assignment_sites(target, node.value)
        self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if node.target and node.value:
            self._create_assignment_sites(node.target, node.value)
        self.generic_visit(node)

    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        self._create_assignment_sites(node.target, node.value)
        self.generic_visit(node)

    def _create_assignment_sites(
        self, target: ast.AST, value: Optional[ast.AST]
    ) -> None:
        if isinstance(target, ast.Name):
            version = self._versions.next_version(target.id)
            lineage = self._detect_lineage(value) if value else None

            site = make_ssa_value_site(
                func_name=self._func_name,
                variable_name=target.id,
                version=version,
                span=self._span(target),
                lineage_parent=lineage,
                defining_ast_node_type=type(value).__name__ if value else None,
            )
            sid = self._builder._register_site(site)

            # Lineage morphism from parent
            if lineage and lineage in self._var_sites:
                self._builder._register_morphism(
                    make_lineage_restriction(self._var_sites[lineage], sid)
                )

            self._var_sites[target.id] = sid

            # Check for error-sensitive operations in value
            if value:
                self._check_error_sites(value, sid)
                self._check_call_sites(value, sid)

        elif isinstance(target, ast.Tuple):
            for elt in target.elts:
                self._create_assignment_sites(elt, value)

    def _detect_lineage(self, value: ast.AST) -> Optional[str]:
        """Detect the lineage parent of a value expression."""
        if isinstance(value, ast.Name):
            return value.id
        if isinstance(value, ast.Attribute) and isinstance(value.value, ast.Name):
            return value.value.id
        if isinstance(value, ast.Call) and isinstance(value.func, ast.Attribute):
            if isinstance(value.func.value, ast.Name):
                return value.func.value.id
        return None

    # -- Control flow: branch-guard sites ------------------------------------

    def visit_If(self, node: ast.If) -> None:
        guard_label = self._next_label("if_")
        guard_expr = ast.dump(node.test) if node.test else ""

        # Detect narrowed variables
        narrowed = self._extract_narrowed_vars(node.test)

        guard_site = make_branch_guard_site(
            func_name=self._func_name,
            guard_label=guard_label,
            span=self._span(node),
            guard_expression=guard_expr,
            polarity=True,
            narrowed_variables=narrowed,
        )
        guard_sid = self._builder._register_site(guard_site)

        # Visit true and false arms
        for stmt in node.body:
            self.visit(stmt)
        for stmt in node.orelse:
            self.visit(stmt)

    def visit_Assert(self, node: ast.Assert) -> None:
        guard_label = self._next_label("assert_")
        guard_site = make_branch_guard_site(
            func_name=self._func_name,
            guard_label=guard_label,
            span=self._span(node),
            guard_expression=ast.dump(node.test) if node.test else "",
            is_assertion=True,
            narrowed_variables=self._extract_narrowed_vars(node.test),
        )
        self._builder._register_site(guard_site)
        self.generic_visit(node)

    def _extract_narrowed_vars(self, test: Optional[ast.AST]) -> List[str]:
        """Extract variable names narrowed by a guard expression."""
        if test is None:
            return []
        names: List[str] = []
        for node in ast.walk(test):
            if isinstance(node, ast.Name):
                names.append(node.id)
        return names

    # -- Loops: loop-invariant sites -----------------------------------------

    def visit_For(self, node: ast.For) -> None:
        loop_label = self._next_label("for_")
        loop_var = None
        if isinstance(node.target, ast.Name):
            loop_var = node.target.id

        site = make_loop_invariant_site(
            func_name=self._func_name,
            loop_label=loop_label,
            span=self._span(node),
            loop_variable=loop_var,
            is_for_loop=True,
        )
        self._builder._register_site(site)

        for stmt in node.body:
            self.visit(stmt)
        for stmt in node.orelse:
            self.visit(stmt)

    def visit_While(self, node: ast.While) -> None:
        loop_label = self._next_label("while_")
        site = make_loop_invariant_site(
            func_name=self._func_name,
            loop_label=loop_label,
            span=self._span(node),
            is_while_loop=True,
        )
        self._builder._register_site(site)

        for stmt in node.body:
            self.visit(stmt)
        for stmt in node.orelse:
            self.visit(stmt)

    # -- Returns: output-boundary sites --------------------------------------

    def visit_Return(self, node: ast.Return) -> None:
        return_idx = len(self.return_site_ids)
        site = make_return_boundary_site(
            func_name=self._func_name,
            span=self._span(node),
            return_index=return_idx,
        )
        sid = self._builder._register_site(site)
        self.return_site_ids.append(sid)

        # Lineage from returned value to output boundary
        if node.value:
            if isinstance(node.value, ast.Name):
                if node.value.id in self._var_sites:
                    self._builder._register_morphism(
                        make_output_projection(self._var_sites[node.value.id], sid)
                    )
            # Check for error-sensitive operations in the return expression
            self._check_error_sites(node.value, sid)
            self._check_call_sites(node.value, sid)
        self.generic_visit(node)

    # -- Raise: error / exceptional output sites -----------------------------

    def visit_Raise(self, node: ast.Raise) -> None:
        exc_type = None
        if node.exc:
            if isinstance(node.exc, ast.Call) and isinstance(node.exc.func, ast.Name):
                exc_type = node.exc.func.id
            elif isinstance(node.exc, ast.Name):
                exc_type = node.exc.id

        # Exceptional output boundary
        site = make_return_boundary_site(
            func_name=self._func_name,
            span=self._span(node),
            return_index=len(self.return_site_ids),
            is_exceptional=True,
            exception_type=exc_type,
        )
        sid = self._builder._register_site(site)
        self._builder._output_boundary.add(sid)
        self.generic_visit(node)

    # -- Try/Except: exception flow sites ------------------------------------

    def visit_Try(self, node: ast.Try) -> None:
        for stmt in node.body:
            self.visit(stmt)
        for handler in node.handlers:
            self.visit(handler)
        for stmt in node.finalbody:
            self.visit(stmt)
        for stmt in node.orelse:
            self.visit(stmt)

    # -- Calls: check for library triggers and error sites -------------------

    def _check_call_sites(self, value: ast.AST, result_sid: SiteId) -> None:
        """Create call-result sites for function/method calls."""
        if not isinstance(value, ast.Call):
            return

        callee_name = self._resolve_callee_name(value.func)
        if not callee_name:
            return

        call_label = self._next_label("call_")
        arg_names = []
        for arg in value.args:
            if isinstance(arg, ast.Name):
                arg_names.append(arg.id)

        site = make_call_result_site(
            func_name=self._func_name,
            call_label=call_label,
            callee_name=callee_name,
            span=self._span(value),
            arguments=arg_names,
            is_method_call=isinstance(value.func, ast.Attribute),
            receiver_variable=(
                value.func.value.id
                if isinstance(value.func, ast.Attribute) and
                   isinstance(value.func.value, ast.Name)
                else None
            ),
        )
        call_sid = self._builder._register_site(site)

        # Lineage from call result to assignment target
        self._builder._register_morphism(
            make_lineage_restriction(call_sid, result_sid)
        )

        # Library-specific sites (torch operations)
        self._check_torch_sites(callee_name, value, call_sid)

    def _resolve_callee_name(self, func: ast.AST) -> Optional[str]:
        if isinstance(func, ast.Name):
            return func.id
        if isinstance(func, ast.Attribute):
            if isinstance(func.value, ast.Name):
                return f"{func.value.id}.{func.attr}"
            return func.attr
        return None

    def _check_torch_sites(
        self,
        callee_name: str,
        call_node: ast.Call,
        call_sid: SiteId,
    ) -> None:
        """Create tensor-specific sites for PyTorch operations."""
        span = self._span(call_node)

        # Sort operations
        if callee_name in ("torch.sort", "torch.argsort", "torch.topk"):
            order_label = self._next_label("order_")
            operation = callee_name.split(".")[-1]
            source_var = None
            if call_node.args and isinstance(call_node.args[0], ast.Name):
                source_var = call_node.args[0].id

            site = make_tensor_order_site(
                func_name=self._func_name,
                order_label=order_label,
                operation=operation,
                span=span,
                source_variable=source_var,
            )
            order_sid = self._builder._register_site(site)
            self._builder._register_morphism(
                make_lineage_restriction(call_sid, order_sid)
            )

        # Reshape / view operations
        if callee_name in ("torch.reshape", "torch.view") or \
           callee_name.endswith(".reshape") or callee_name.endswith(".view"):
            shape_label = self._next_label("shape_")
            source_var = None
            if call_node.args and isinstance(call_node.args[0], ast.Name):
                source_var = call_node.args[0].id
            elif isinstance(call_node.func, ast.Attribute) and \
                 isinstance(call_node.func.value, ast.Name):
                source_var = call_node.func.value.id

            site = make_tensor_shape_site(
                func_name=self._func_name,
                shape_label=shape_label,
                operation="reshape",
                span=span,
                source_variable=source_var,
            )
            shape_sid = self._builder._register_site(site)
            self._builder._register_morphism(
                make_lineage_restriction(call_sid, shape_sid)
            )

            # Error site for invalid reshape
            error_label = self._next_label("err_reshape_")
            error = make_error_site(
                func_name=self._func_name,
                error_label=error_label,
                error_kind=ErrorKind.INVALID_RESHAPE,
                span=span,
                operand_names=(source_var,) if source_var else (),
                viability_description="source and target cardinality must match",
            )
            err_sid = self._builder._register_site(error)
            self._builder._error_sites.add(err_sid)
            self._builder._register_morphism(
                make_error_viability_restriction(shape_sid, err_sid)
            )

        # Gather / index_select
        if callee_name in ("torch.gather", "torch.index_select") or \
           callee_name.endswith(".gather") or callee_name.endswith(".index_select"):
            idx_label = self._next_label("idx_")
            source_var = None
            index_var = None
            if len(call_node.args) >= 2:
                if isinstance(call_node.args[0], ast.Name):
                    source_var = call_node.args[0].id
                if isinstance(call_node.args[-1], ast.Name):
                    index_var = call_node.args[-1].id

            site = make_tensor_indexing_site(
                func_name=self._func_name,
                index_label=idx_label,
                operation=callee_name.split(".")[-1],
                span=span,
                source_variable=source_var,
                index_variable=index_var,
            )
            idx_sid = self._builder._register_site(site)
            self._builder._register_morphism(
                make_lineage_restriction(call_sid, idx_sid)
            )

            # Error site for out-of-range index
            error_label = self._next_label("err_index_")
            error = make_error_site(
                func_name=self._func_name,
                error_label=error_label,
                error_kind=ErrorKind.OUT_OF_RANGE_INDEX,
                span=span,
                operand_names=tuple(filter(None, (source_var, index_var))),
                viability_description="selector domain must lie within source extent",
            )
            err_sid = self._builder._register_site(error)
            self._builder._error_sites.add(err_sid)
            self._builder._register_morphism(
                make_error_viability_restriction(idx_sid, err_sid)
            )

    # -- Error-sensitive operations ------------------------------------------

    def _check_error_sites(self, value: ast.AST, result_sid: SiteId) -> None:
        """Create error sites for potentially dangerous operations."""
        span = self._span(value)

        # Subscript → IndexError / KeyError
        if isinstance(value, ast.Subscript):
            source_var = None
            if isinstance(value.value, ast.Name):
                source_var = value.value.id
            error_label = self._next_label("err_sub_")
            error = make_error_site(
                func_name=self._func_name,
                error_label=error_label,
                error_kind=ErrorKind.INDEX_ERROR,
                span=span,
                operand_names=(source_var,) if source_var else (),
                viability_description="index must be within sequence bounds",
            )
            err_sid = self._builder._register_site(error)
            self._builder._error_sites.add(err_sid)
            self._builder._register_morphism(
                make_error_viability_restriction(result_sid, err_sid)
            )

        # Division → ZeroDivisionError
        if isinstance(value, ast.BinOp) and isinstance(value.op, (ast.Div, ast.FloorDiv, ast.Mod)):
            error_label = self._next_label("err_div_")
            error = make_error_site(
                func_name=self._func_name,
                error_label=error_label,
                error_kind=ErrorKind.ZERO_DIVISION,
                span=span,
                viability_description="denominator must not be zero",
            )
            err_sid = self._builder._register_site(error)
            self._builder._error_sites.add(err_sid)
            self._builder._register_morphism(
                make_error_viability_restriction(result_sid, err_sid)
            )

        # Attribute access → AttributeError
        if isinstance(value, ast.Attribute):
            receiver = None
            if isinstance(value.value, ast.Name):
                receiver = value.value.id
            # Create heap/protocol site
            heap_label = self._next_label("heap_")
            heap_site = make_heap_protocol_site(
                func_name=self._func_name,
                heap_label=heap_label,
                span=span,
                field_name=value.attr,
                is_read=True,
            )
            heap_sid = self._builder._register_site(heap_site)

            # Potential AttributeError
            error_label = self._next_label("err_attr_")
            error = make_error_site(
                func_name=self._func_name,
                error_label=error_label,
                error_kind=ErrorKind.ATTRIBUTE_ERROR,
                span=span,
                operand_names=(receiver,) if receiver else (),
                viability_description=f"receiver must have attribute '{value.attr}'",
            )
            err_sid = self._builder._register_site(error)
            self._builder._error_sites.add(err_sid)
            self._builder._register_morphism(
                make_error_viability_restriction(heap_sid, err_sid)
            )

    # -- Attribute access: heap/protocol sites (on expressions) --------------

    def visit_Expr(self, node: ast.Expr) -> None:
        """Visit standalone expressions (e.g., method calls)."""
        if isinstance(node.value, ast.Call):
            callee_name = self._resolve_callee_name(node.value.func)
            if callee_name:
                call_label = self._next_label("call_")
                arg_names = [
                    a.id for a in node.value.args if isinstance(a, ast.Name)
                ]
                site = make_call_result_site(
                    func_name=self._func_name,
                    call_label=call_label,
                    callee_name=callee_name,
                    span=self._span(node),
                    arguments=arg_names,
                    is_method_call=isinstance(node.value.func, ast.Attribute),
                )
                self._builder._register_site(site)
        self.generic_visit(node)


# ---------------------------------------------------------------------------
# Convenience: build cover from source string
# ---------------------------------------------------------------------------

def build_cover(source: str, filename: str = "<string>") -> Cover:
    """Build a sheaf cover from Python source code.

    This is the main entry point for Algorithm 1 (Cover Synthesis).
    """
    return CoverBuilder.from_source(source, filename)


def build_cover_from_file(filepath: str) -> Cover:
    """Build a sheaf cover from a Python source file."""
    return CoverBuilder.from_file(filepath)
