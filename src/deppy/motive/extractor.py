"""MotiveExtractor — abstract interpreter that builds M(f) from an AST.

Walks the AST and extracts the computational motive by:
1. Inferring sorts for each expression (type fiber at each point)
2. Extracting typed operations (morphisms in the Lawvere theory)
3. Building the data flow category
4. Computing all invariants (cohomology, K-theory, tropical, π₁, etc.)

The extractor delegates to python_semantics_motive for the interpretation
of Python's builtin semantics (types, functions, methods, operators).
"""

from __future__ import annotations

import ast
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from deppy.motive.sorts import Sort
from deppy.motive.operations import (
    TypedOp, FlowEdge, Effect, Refinement,
    OP_ABSTRACTION, OP_REFINEMENTS, AUGOP_ABSTRACTION, ACCUM_REFINEMENTS,
)
from deppy.motive.fiber import TypeFiber
from deppy.motive.category import DataFlowCategory
from deppy.motive.cohomology import CechCohomology
from deppy.motive.invariants import (
    KTheoryInvariant, TropicalInvariant, FundamentalGroupoid,
    GaloisInvariant, RepresentationCharacter, EFDepth,
)
from deppy.motive.motive import Motive


class MotiveExtractor(ast.NodeVisitor):
    """Extract the computational motive from a Python function AST.

    This is the abstract interpreter that builds M(f).  It delegates
    sort inference and operation abstraction to the python_semantics_motive
    package when available, falling back to built-in tables otherwise.
    """

    def __init__(self) -> None:
        self._ops: List[TypedOp] = []
        self._edges: List[FlowEdge] = []
        self._category = DataFlowCategory()
        self._block: int = 0
        self._num_blocks: int = 0
        self._var_sorts: Dict[str, Sort] = {}
        self._param_sorts: List[Sort] = []
        self._return_sort: Sort = Sort.TOP
        self._global_refinements: Set[Refinement] = set()
        self._has_recursion: bool = False
        self._has_iteration: bool = False
        self._loop_depth: int = 0
        self._current_loop_depth: int = 0
        self._num_branches: int = 0
        self._func_name: str = ""
        self._block_reads: Dict[int, Set[str]] = {}
        self._block_writes: Dict[int, Set[str]] = {}
        self._block_ops: Dict[int, List[TypedOp]] = {}
        # Concrete content fingerprints
        self._constants: List[Tuple] = []          # (sort, hash(value))
        self._attributes: List[str] = []           # ordered attribute accesses
        self._name_references: Set[str] = set()    # external name references
        self._param_names: List[str] = []          # parameter names (for flow tracking)
        self._arg_order_events: List[Tuple] = []   # how params flow to call args
        # Try to load the full Python semantics interpretation
        self._semantics = _load_semantics()

    def extract(self, func_node: ast.FunctionDef) -> Motive:
        """Extract the computational motive from a function."""
        self._func_name = func_node.name

        # Parameters → Σ-type domain
        for arg in func_node.args.args:
            sort = self._infer_param_sort(arg, func_node)
            self._param_sorts.append(sort)
            self._var_sorts[arg.arg] = sort
            self._param_names.append(arg.arg)

        # Initialize first block
        self._init_block(0)
        self._num_blocks = 1

        # Walk body
        for stmt in func_node.body:
            if (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant)
                    and isinstance(stmt.value.value, str)):
                continue
            self._visit_stmt(stmt)

        # Build category objects from blocks
        self._build_category()

        # Compute all invariants
        cohomology = CechCohomology().compute(self._category)
        k_theory = KTheoryInvariant.from_operations(self._ops)
        tropical = TropicalInvariant.from_category(
            self._category, self._ops,
            self._loop_depth, self._has_recursion, self._num_branches,
        )
        groupoid = FundamentalGroupoid.from_category(
            self._category, self._has_recursion, self._loop_depth,
        )
        galois = GaloisInvariant.from_category(self._category)
        character = RepresentationCharacter.from_operations(self._ops)
        ef = EFDepth.from_category(self._category)

        # Collect global refinements
        for op in self._ops:
            self._global_refinements.update(op.refinements)

        return Motive(
            operations=list(self._ops),
            flow_edges=list(self._edges),
            num_blocks=self._num_blocks,
            category=self._category,
            cohomology=cohomology,
            k_theory=k_theory,
            tropical=tropical,
            groupoid=groupoid,
            galois=galois,
            character=character,
            ef_depth=ef,
            input_sorts=tuple(self._param_sorts),
            output_sort=self._return_sort,
            global_refinements=frozenset(self._global_refinements),
            has_recursion=self._has_recursion,
            has_iteration=self._has_iteration,
            loop_depth=self._loop_depth,
            num_branches=self._num_branches,
            constant_fingerprint=frozenset(self._constants),
            attribute_fingerprint=tuple(self._attributes),
            name_reference_fingerprint=frozenset(self._name_references),
            argument_order_fingerprint=tuple(self._arg_order_events),
        )

    # ── Block management ────────────────────────────────────────

    def _init_block(self, idx: int) -> None:
        self._block_reads[idx] = set()
        self._block_writes[idx] = set()
        self._block_ops[idx] = []

    def _new_block(self) -> int:
        self._num_blocks += 1
        b = self._num_blocks - 1
        self._init_block(b)
        return b

    def _build_category(self) -> None:
        """Build the DataFlowCategory from extracted blocks and edges."""
        for b in range(self._num_blocks):
            ops_in_block = tuple(self._block_ops.get(b, []))
            scope_items = frozenset(
                (v, s) for v, s in self._var_sorts.items()
            )
            fiber = TypeFiber(
                sort=Sort.TOP,
                refinements=frozenset(),
                scope=scope_items,
                reads=frozenset(self._block_reads.get(b, set())),
                writes=frozenset(self._block_writes.get(b, set())),
                operations=ops_in_block,
            )
            self._category.add_object(b, dict(self._var_sorts), fiber)

        for edge in self._edges:
            if (edge.source_block < len(self._category.objects) and
                    edge.target_block < len(self._category.objects)):
                op_idx = edge.op_index
                op = self._ops[op_idx] if 0 <= op_idx < len(self._ops) else TypedOp(
                    name='Id', input_sorts=(), output_sort=Sort.TOP,
                    refinements=frozenset(), effect=Effect.PURE,
                )
                self._category.add_morphism(
                    edge.source_block, edge.target_block, op, edge,
                )

    # ── Operation recording ─────────────────────────────────────

    def _add_op(self, name: str, inputs: Tuple[Sort, ...], output: Sort,
                refinements: FrozenSet[Refinement] = frozenset(),
                effect: Effect = Effect.PURE) -> int:
        op = TypedOp(name=name, input_sorts=inputs, output_sort=output,
                     refinements=refinements, effect=effect)
        idx = len(self._ops)
        self._ops.append(op)
        self._block_ops.setdefault(self._block, []).append(op)
        return idx

    def _add_flow_edge(self, src: int, tgt: int,
                       ss: Sort, ts: Sort, op_idx: int) -> None:
        self._edges.append(FlowEdge(src, tgt, ss, ts, op_idx))

    # ── Statement visitors ──────────────────────────────────────

    def _visit_stmt(self, node: ast.stmt) -> None:
        if isinstance(node, ast.Assign):
            self._visit_assign(node)
        elif isinstance(node, ast.AugAssign):
            self._visit_aug_assign(node)
        elif isinstance(node, ast.Return):
            self._visit_return(node)
        elif isinstance(node, ast.If):
            self._visit_if(node)
        elif isinstance(node, ast.For):
            self._visit_for(node)
        elif isinstance(node, ast.While):
            self._visit_while(node)
        elif isinstance(node, ast.Expr):
            if isinstance(node.value, ast.Call):
                self._extract_expr_ops(node.value)
        elif isinstance(node, ast.Try):
            for h in getattr(node, 'handlers', []):
                for s in h.body:
                    self._visit_stmt(s)
            for s in getattr(node, 'body', []):
                self._visit_stmt(s)
        elif isinstance(node, ast.With):
            for s in node.body:
                self._visit_stmt(s)
        elif isinstance(node, ast.FunctionDef):
            self._add_op('Func.define', (), Sort.FUNC, effect=Effect.ALLOCATE)
            inner = MotiveExtractor()
            inner_motive = inner.extract(node)
            for op in inner_motive.operations:
                self._ops.append(op)
        elif isinstance(node, ast.Delete):
            for t in node.targets:
                s = self._infer_sort(t)
                self._add_op('Mem.free', (s,), Sort.NONE, effect=Effect.MUTATE)

    def _visit_assign(self, node: ast.Assign) -> None:
        sort = self._infer_sort(node.value)
        for target in node.targets:
            if isinstance(target, ast.Name):
                old = self._var_sorts.get(target.id, Sort.BOT)
                self._var_sorts[target.id] = sort
                self._block_writes.setdefault(self._block, set()).add(target.id)
                if old != Sort.BOT and old != sort:
                    self._add_op('Assign.rebind', (old,), sort)
                else:
                    self._add_op('Assign.bind', (), sort)
            elif isinstance(target, ast.Subscript):
                cs = self._infer_sort(target.value)
                self._add_op('Container.store', (cs, sort), cs, effect=Effect.MUTATE)
            elif isinstance(target, (ast.Tuple, ast.List)):
                self._add_op('Destructure.unpack', (sort,), Sort.TOP)
                for elt in target.elts:
                    if isinstance(elt, ast.Name):
                        self._var_sorts[elt.id] = Sort.TOP
                        self._block_writes.setdefault(self._block, set()).add(elt.id)
        self._extract_expr_ops(node.value)

    def _visit_aug_assign(self, node: ast.AugAssign) -> None:
        ts = Sort.TOP
        if isinstance(node.target, ast.Name):
            ts = self._var_sorts.get(node.target.id, Sort.TOP)
            self._block_writes.setdefault(self._block, set()).add(node.target.id)
            self._block_reads.setdefault(self._block, set()).add(node.target.id)
        vs = self._infer_sort(node.value)
        op_name = AUGOP_ABSTRACTION.get(type(node.op).__name__, 'Accum.generic')
        refs = ACCUM_REFINEMENTS.get(op_name, frozenset())
        self._add_op(op_name, (ts, vs), ts, refinements=refs, effect=Effect.MUTATE)
        self._extract_expr_ops(node.value)

    def _visit_return(self, node: ast.Return) -> None:
        if node.value is not None:
            sort = self._infer_sort(node.value)
            self._return_sort = sort
            self._add_op('Return', (sort,), sort)
            self._extract_expr_ops(node.value)
            if self._contains_self_call(node.value):
                self._has_recursion = True
                self._add_op('Recurse.return', (sort,), sort, effect=Effect.RECURSE)

    def _visit_if(self, node: ast.If) -> None:
        self._num_branches += 1
        self._add_op('Branch.test', (self._infer_sort(node.test),), Sort.BOOL)
        self._extract_expr_ops(node.test)
        prev = self._block
        tb = self._new_block()
        self._block = tb
        self._add_flow_edge(prev, tb, Sort.BOOL, Sort.TOP, len(self._ops) - 1)
        for s in node.body:
            self._visit_stmt(s)
        fb = None
        if node.orelse:
            fb = self._new_block()
            self._block = fb
            self._add_flow_edge(prev, fb, Sort.BOOL, Sort.TOP, len(self._ops) - 1)
            for s in node.orelse:
                self._visit_stmt(s)
        merge = self._new_block()
        op_ref = len(self._ops) - 1 if self._ops else 0
        self._add_flow_edge(tb, merge, Sort.TOP, Sort.TOP, op_ref)
        if fb is not None:
            self._add_flow_edge(fb, merge, Sort.TOP, Sort.TOP, op_ref)
        self._block = merge

    def _visit_for(self, node: ast.For) -> None:
        self._has_iteration = True
        self._current_loop_depth += 1
        self._loop_depth = max(self._loop_depth, self._current_loop_depth)
        it_sort = self._infer_sort(node.iter)
        self._add_op('Loop.iterate', (it_sort,), Sort.TOP, effect=Effect.ITERATE)
        self._extract_expr_ops(node.iter)
        if isinstance(node.target, ast.Name):
            self._var_sorts[node.target.id] = Sort.TOP
            self._block_writes.setdefault(self._block, set()).add(node.target.id)
        elif isinstance(node.target, ast.Tuple):
            for elt in node.target.elts:
                if isinstance(elt, ast.Name):
                    self._var_sorts[elt.id] = Sort.TOP
                    self._block_writes.setdefault(self._block, set()).add(elt.id)
        prev = self._block
        lb = self._new_block()
        self._block = lb
        self._add_flow_edge(prev, lb, it_sort, Sort.TOP, len(self._ops) - 1)
        for s in node.body:
            self._visit_stmt(s)
        op_ref = len(self._ops) - 1 if self._ops else 0
        self._add_flow_edge(lb, lb, Sort.TOP, Sort.TOP, op_ref)
        post = self._new_block()
        self._add_flow_edge(lb, post, Sort.TOP, Sort.TOP, op_ref)
        self._block = post
        self._current_loop_depth -= 1

    def _visit_while(self, node: ast.While) -> None:
        self._has_iteration = True
        self._current_loop_depth += 1
        self._loop_depth = max(self._loop_depth, self._current_loop_depth)
        cs = self._infer_sort(node.test)
        self._add_op('Loop.while', (cs,), Sort.BOOL, effect=Effect.ITERATE)
        self._extract_expr_ops(node.test)
        prev = self._block
        lb = self._new_block()
        self._block = lb
        self._add_flow_edge(prev, lb, Sort.BOOL, Sort.TOP, len(self._ops) - 1)
        for s in node.body:
            self._visit_stmt(s)
        op_ref = len(self._ops) - 1 if self._ops else 0
        self._add_flow_edge(lb, lb, Sort.TOP, Sort.TOP, op_ref)
        post = self._new_block()
        self._add_flow_edge(lb, post, Sort.TOP, Sort.TOP, op_ref)
        self._block = post
        self._current_loop_depth -= 1

    # ── Sort inference ──────────────────────────────────────────

    def _infer_sort(self, node: ast.expr) -> Sort:
        """Infer the abstract sort of an expression.

        Delegates to python_semantics_motive when available.
        """
        if self._semantics:
            result = self._semantics.infer_sort(node, self._var_sorts, self._func_name)
            if result is not None:
                return result
        return self._builtin_infer_sort(node)

    def _infer_param_sort(self, arg: ast.arg, func: ast.FunctionDef) -> Sort:
        if self._semantics:
            result = self._semantics.infer_param_sort(arg, func)
            if result is not None:
                return result
        return self._builtin_infer_param_sort(arg, func)

    def _builtin_infer_sort(self, node: ast.expr) -> Sort:
        """Built-in sort inference (fallback when semantics not loaded)."""
        if isinstance(node, ast.Constant):
            v = node.value
            if isinstance(v, bool): return Sort.BOOL
            if isinstance(v, (int, float, complex)): return Sort.NUM
            if isinstance(v, str): return Sort.STR
            if isinstance(v, bytes): return Sort.STR
            if v is None: return Sort.NONE
            return Sort.TOP
        if isinstance(node, ast.Name):
            if node.id in self._var_sorts:
                self._block_reads.setdefault(self._block, set()).add(node.id)
                return self._var_sorts[node.id]
            from deppy.python_semantics_motive.builtin_types import BUILTIN_NAME_SORTS
            return BUILTIN_NAME_SORTS.get(node.id, Sort.TOP)
        if isinstance(node, (ast.List, ast.ListComp)): return Sort.SEQ
        if isinstance(node, ast.Tuple): return Sort.SEQ
        if isinstance(node, (ast.Dict, ast.DictComp)): return Sort.MAP
        if isinstance(node, (ast.Set, ast.SetComp)): return Sort.SET
        if isinstance(node, ast.GeneratorExp): return Sort.ITER
        if isinstance(node, ast.BinOp):
            ls = self._infer_sort(node.left)
            rs = self._infer_sort(node.right)
            if isinstance(node.op, ast.Add):
                if ls == Sort.STR or rs == Sort.STR: return Sort.STR
                if ls == Sort.SEQ or rs == Sort.SEQ: return Sort.SEQ
                return Sort.NUM
            if isinstance(node.op, ast.Mult):
                if ls == Sort.STR or rs == Sort.STR: return Sort.STR
                if ls == Sort.SEQ or rs == Sort.SEQ: return Sort.SEQ
                return Sort.NUM
            return Sort.NUM
        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.Not): return Sort.BOOL
            return Sort.NUM
        if isinstance(node, ast.BoolOp): return Sort.BOOL
        if isinstance(node, ast.Compare): return Sort.BOOL
        if isinstance(node, ast.IfExp):
            ts = self._infer_sort(node.body)
            fs = self._infer_sort(node.orelse)
            return ts if ts == fs else Sort.TOP
        if isinstance(node, ast.Call):
            return self._infer_call_sort(node)
        if isinstance(node, ast.Subscript):
            cs = self._infer_sort(node.value)
            if cs == Sort.STR: return Sort.STR
            if cs == Sort.SEQ:
                return Sort.SEQ if isinstance(node.slice, ast.Slice) else Sort.TOP
            if cs == Sort.MAP: return Sort.TOP
            return Sort.TOP
        if isinstance(node, ast.Attribute):
            from deppy.python_semantics_motive.builtin_types import METHOD_RESULT_SORTS
            return METHOD_RESULT_SORTS.get(node.attr, Sort.TOP)
        if isinstance(node, ast.Lambda): return Sort.FUNC
        if isinstance(node, ast.JoinedStr): return Sort.STR
        if isinstance(node, ast.Starred): return Sort.SEQ
        return Sort.TOP

    def _infer_call_sort(self, node: ast.Call) -> Sort:
        if isinstance(node.func, ast.Name):
            name = node.func.id
            if name == self._func_name:
                self._has_recursion = True
                return self._return_sort
            from deppy.python_semantics_motive.builtin_funcs import BUILTIN_FUNC_SORTS
            return BUILTIN_FUNC_SORTS.get(name, Sort.TOP)
        if isinstance(node.func, ast.Attribute):
            from deppy.python_semantics_motive.builtin_types import METHOD_RESULT_SORTS
            return METHOD_RESULT_SORTS.get(node.func.attr, Sort.TOP)
        return Sort.TOP

    def _builtin_infer_param_sort(self, arg: ast.arg, func: ast.FunctionDef) -> Sort:
        name = arg.arg
        if arg.annotation:
            return self._sort_from_annotation(arg.annotation)
        for node in ast.walk(func):
            if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and node.value.id == name:
                return Sort.SEQ
            if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                    and node.func.id == 'len' and node.args
                    and isinstance(node.args[0], ast.Name) and node.args[0].id == name):
                return Sort.SEQ
            if isinstance(node, ast.For) and isinstance(node.iter, ast.Name) and node.iter.id == name:
                return Sort.SEQ
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                if isinstance(node.func.value, ast.Name) and node.func.value.id == name:
                    m = node.func.attr
                    if m in ('append', 'extend', 'insert', 'pop', 'sort', 'reverse', 'index'):
                        return Sort.SEQ
                    if m in ('get', 'keys', 'values', 'items', 'setdefault', 'update'):
                        return Sort.MAP
                    if m in ('add', 'discard', 'union', 'intersection', 'difference'):
                        return Sort.SET
                    if m in ('join', 'split', 'strip', 'replace', 'find', 'lower', 'upper'):
                        return Sort.STR
            if isinstance(node, ast.BinOp):
                if isinstance(node.left, ast.Name) and node.left.id == name:
                    if isinstance(node.op, (ast.Sub, ast.Div, ast.FloorDiv, ast.Mod, ast.Pow)):
                        return Sort.NUM
                if isinstance(node.right, ast.Name) and node.right.id == name:
                    if isinstance(node.op, (ast.Sub, ast.Div, ast.FloorDiv, ast.Mod, ast.Pow)):
                        return Sort.NUM
            if isinstance(node, ast.Compare) and isinstance(node.left, ast.Name) and node.left.id == name:
                for op in node.ops:
                    if isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                        return Sort.NUM
        return Sort.TOP

    def _sort_from_annotation(self, ann: ast.expr) -> Sort:
        if isinstance(ann, ast.Name):
            from deppy.python_semantics_motive.builtin_types import BUILTIN_NAME_SORTS
            return BUILTIN_NAME_SORTS.get(ann.id, Sort.TOP)
        if isinstance(ann, ast.Subscript) and isinstance(ann.value, ast.Name):
            c = ann.value.id
            if c in ('list', 'List', 'Sequence', 'Iterable'): return Sort.SEQ
            if c in ('dict', 'Dict', 'Mapping'): return Sort.MAP
            if c in ('set', 'Set', 'FrozenSet'): return Sort.SET
            if c in ('Tuple', 'tuple'): return Sort.SEQ
        return Sort.TOP

    # ── Expression operation extraction ─────────────────────────

    def _extract_expr_ops(self, node: ast.expr) -> None:
        """Extract typed operations from expressions.

        Delegates operator/call interpretation to python_semantics_motive.
        """
        # Collect concrete fingerprints
        self._collect_fingerprints(node)

        if isinstance(node, ast.BinOp):
            self._extract_binop(node)
        elif isinstance(node, ast.UnaryOp):
            os = self._infer_sort(node.operand)
            self._add_op(f'Unary.{type(node.op).__name__}', (os,),
                         Sort.BOOL if isinstance(node.op, ast.Not) else Sort.NUM)
            self._extract_expr_ops(node.operand)
        elif isinstance(node, ast.Compare):
            self._extract_compare(node)
        elif isinstance(node, ast.BoolOp):
            for v in node.values:
                self._extract_expr_ops(v)
            name = 'Logic.And' if isinstance(node.op, ast.And) else 'Logic.Or'
            self._add_op(name, tuple(Sort.BOOL for _ in node.values), Sort.BOOL,
                         refinements=frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}))
        elif isinstance(node, ast.Call):
            self._extract_call(node)
        elif isinstance(node, ast.IfExp):
            self._add_op('Branch.ternary', (Sort.BOOL,), self._infer_sort(node))
            self._extract_expr_ops(node.test)
            self._extract_expr_ops(node.body)
            self._extract_expr_ops(node.orelse)
        elif isinstance(node, ast.Subscript):
            cs = self._infer_sort(node.value)
            rs = self._infer_sort(node)
            if isinstance(node.slice, ast.Slice):
                self._add_op('Container.slice', (cs,), rs)
            else:
                self._add_op('Container.index', (cs, Sort.NUM), rs)
            self._extract_expr_ops(node.value)
        elif isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            self._extract_comprehension(node)
        elif isinstance(node, ast.Lambda):
            self._add_op('Func.lambda', (), Sort.FUNC, effect=Effect.ALLOCATE)
            # Extract lambda body for fingerprinting
            if hasattr(node, 'body'):
                self._extract_expr_ops(node.body)
        elif isinstance(node, ast.Starred):
            self._add_op('Destructure.splat', (self._infer_sort(node.value),), Sort.SEQ)
            self._extract_expr_ops(node.value)
        elif isinstance(node, ast.Dict):
            # Track dict display with possible **unpacking
            for i, (k, v) in enumerate(zip(node.keys, node.values)):
                if k is None:
                    # **expr unpacking — order matters!
                    self._add_op('Destructure.dict_splat', (self._infer_sort(v),), Sort.MAP)
                    self._extract_expr_ops(v)
                else:
                    self._extract_expr_ops(v)
                    if k is not None:
                        self._extract_expr_ops(k)
        elif isinstance(node, (ast.List, ast.Tuple)):
            for elt in node.elts:
                self._extract_expr_ops(elt)
        elif isinstance(node, ast.JoinedStr):
            for val in node.values:
                if isinstance(val, ast.FormattedValue):
                    self._extract_expr_ops(val.value)

    def _extract_binop(self, node: ast.BinOp) -> None:
        ls = self._infer_sort(node.left)
        rs = self._infer_sort(node.right)
        result = self._infer_sort(node)
        from deppy.python_semantics_motive.operators import binop_to_typed_op
        op_name, refs = binop_to_typed_op(node.op, ls, rs)
        self._add_op(op_name, (ls, rs), result, refinements=refs)
        self._extract_expr_ops(node.left)
        self._extract_expr_ops(node.right)

    def _extract_compare(self, node: ast.Compare) -> None:
        from deppy.python_semantics_motive.operators import cmpop_to_name
        ls = self._infer_sort(node.left)
        for op, comp in zip(node.ops, node.comparators):
            rs = self._infer_sort(comp)
            name = cmpop_to_name(op)
            self._add_op(name, (ls, rs), Sort.BOOL)
            self._extract_expr_ops(comp)
            ls = rs
        self._extract_expr_ops(node.left)

    def _extract_call(self, node: ast.Call) -> None:
        if isinstance(node.func, ast.Name):
            from deppy.python_semantics_motive.builtin_funcs import (
                builtin_func_to_typed_op,
            )
            name = node.func.id
            arg_sorts = tuple(self._infer_sort(a) for a in node.args)
            result_sort = self._infer_call_sort(node)
            if name == self._func_name:
                self._add_op('Recurse.call', arg_sorts, result_sort, effect=Effect.RECURSE)
            else:
                op_name, refs, eff = builtin_func_to_typed_op(name, arg_sorts)
                self._add_op(op_name, arg_sorts, result_sort, refinements=refs, effect=eff)
                for kw in node.keywords:
                    if kw.arg == 'reverse' and isinstance(kw.value, ast.Constant) and kw.value.value:
                        self._global_refinements.add(Refinement.REVERSED)
        elif isinstance(node.func, ast.Attribute):
            from deppy.python_semantics_motive.methods import (
                method_to_typed_op,
            )
            method = node.func.attr
            obj_sort = self._infer_sort(node.func.value)
            arg_sorts = tuple(self._infer_sort(a) for a in node.args)
            from deppy.python_semantics_motive.builtin_types import METHOD_RESULT_SORTS
            result_sort = METHOD_RESULT_SORTS.get(method, Sort.TOP)
            op_name, refs, eff = method_to_typed_op(method, obj_sort, arg_sorts)
            self._add_op(op_name, (obj_sort,) + arg_sorts, result_sort,
                         refinements=refs, effect=eff)

        for arg in node.args:
            self._extract_expr_ops(arg)
        for kw in node.keywords:
            if kw.value:
                self._extract_expr_ops(kw.value)

    def _extract_comprehension(self, node: ast.expr) -> None:
        rs = self._infer_sort(node)
        refs: Set[Refinement] = set()
        for gen in getattr(node, 'generators', []):
            it_sort = self._infer_sort(gen.iter)
            self._add_op('Comprehension.iterate', (it_sort,), Sort.TOP, effect=Effect.ITERATE)
            for if_clause in gen.ifs:
                self._add_op('Comprehension.filter', (Sort.BOOL,), Sort.BOOL)
                refs.add(Refinement.FILTERED)
                self._extract_expr_ops(if_clause)
            self._extract_expr_ops(gen.iter)
        if isinstance(node, ast.ListComp):
            self._add_op('Comprehension.collect', (), Sort.SEQ,
                         refinements=frozenset(refs) | frozenset({Refinement.MAPPED}))
            if hasattr(node, 'elt'): self._extract_expr_ops(node.elt)
        elif isinstance(node, ast.SetComp):
            self._add_op('Comprehension.collect_set', (), Sort.SET, refinements=frozenset(refs))
            if hasattr(node, 'elt'): self._extract_expr_ops(node.elt)
        elif isinstance(node, ast.DictComp):
            self._add_op('Comprehension.collect_map', (), Sort.MAP, refinements=frozenset(refs))
        elif isinstance(node, ast.GeneratorExp):
            self._add_op('Comprehension.lazy', (), Sort.ITER, refinements=frozenset(refs))
            if hasattr(node, 'elt'): self._extract_expr_ops(node.elt)

    def _collect_fingerprints(self, node: ast.expr) -> None:
        """Collect concrete content fingerprints from an expression.

        These capture semantically distinguishing details that the abstract
        operation structure doesn't: constant values, attribute names,
        external name references, and argument ordering.
        """
        if isinstance(node, ast.Constant):
            v = node.value
            s = self._infer_sort(node)
            try:
                self._constants.append((s, hash(v)))
            except TypeError:
                self._constants.append((s, id(type(v))))
        elif isinstance(node, ast.Attribute):
            self._attributes.append(node.attr)
        elif isinstance(node, ast.Name):
            if node.id not in self._var_sorts and node.id != self._func_name:
                self._name_references.add(node.id)
            # Track parameter flow: which param index is being referenced
            if node.id in self._param_names:
                pidx = self._param_names.index(node.id)
                self._arg_order_events.append(('param_ref', pidx))
        elif isinstance(node, ast.Call):
            # Track argument ordering for calls with param references
            for i, arg in enumerate(node.args):
                if isinstance(arg, ast.Name) and arg.id in self._param_names:
                    pidx = self._param_names.index(arg.id)
                    func_name = ''
                    if isinstance(node.func, ast.Name):
                        func_name = node.func.id
                    elif isinstance(node.func, ast.Attribute):
                        func_name = node.func.attr
                    self._arg_order_events.append(('call_arg', func_name, i, pidx))
            # Track keyword arguments
            for kw in node.keywords:
                if kw.arg and isinstance(kw.value, ast.Constant):
                    try:
                        self._constants.append((Sort.TOP, hash((kw.arg, kw.value.value))))
                    except TypeError:
                        pass
        elif isinstance(node, ast.Starred):
            # Track starred expression contents for {**d1, **d2} vs {**d2, **d1}
            if isinstance(node.value, ast.Name) and node.value.id in self._param_names:
                pidx = self._param_names.index(node.value.id)
                self._arg_order_events.append(('splat', pidx))
        elif isinstance(node, ast.Dict):
            # For dict displays with starred unpacking, track the key order
            for i, v in enumerate(node.values):
                if v is None:  # **expr
                    continue
                if isinstance(v, ast.Name) and v.id in self._param_names:
                    pidx = self._param_names.index(v.id)
                    self._arg_order_events.append(('dict_val', i, pidx))

    def _contains_self_call(self, node: ast.expr) -> bool:
        for child in ast.walk(node):
            if (isinstance(child, ast.Call) and isinstance(child.func, ast.Name)
                    and child.func.id == self._func_name):
                return True
        return False


# ─── Convenience function ──────────────────────────────────────────

def motive_of(source: str, func_name: Optional[str] = None) -> Optional[Motive]:
    """Extract the computational motive from Python source code.

    Usage:
        m = motive_of("def f(x): return x + 1")
        print(m.h0, m.h1, m.operations)
    """
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return None

    funcs = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
    if not funcs:
        return None

    if func_name:
        func = next((f for f in funcs if f.name == func_name), None)
    else:
        func = funcs[-1]

    if func is None:
        return None

    try:
        return MotiveExtractor().extract(func)
    except Exception:
        return None


# ─── Semantics loader ─────────────────────────────────────────────

def _load_semantics():
    """Try to load the python_semantics_motive package."""
    try:
        from deppy.python_semantics_motive import PythonSemantics
        return PythonSemantics()
    except (ImportError, Exception):
        return None
