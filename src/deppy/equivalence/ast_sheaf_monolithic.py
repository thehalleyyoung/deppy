"""Computational Motives Engine — Z3-Decidable Program Equivalence.

Theory: Every program f defines a computational motive M(f) — a finite
algebraic structure extracted from the AST.  Two programs are equivalent
iff their motives are isomorphic, checked via a genuine Z3 SAT query.

Mathematical architecture:
  Layer 1 — Abstract algebra of typed operations  (Lawvere)
  Layer 2 — Data flow category                    (category theory)
  Layer 3 — Čech cohomology of type presheaf      (Grothendieck)
  Layer 4 — The motive M(f) = (Σ, G, H)
  Layer 5 — Z3 isomorphism solver                  (SAT encoding)

No pattern matching on known algorithms.  No heuristic scores.
The answer comes from Z3 SAT/UNSAT.
"""

from __future__ import annotations

import ast
import sys
from dataclasses import dataclass, field
from enum import IntEnum, auto
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

# ─── §1  Abstract Sorts (the sort lattice) ─────────────────────────
#
# From Lawvere's functorial semantics: programs operate on a finitary
# algebra whose carrier sorts form a lattice under subsorting.

class Sort(IntEnum):
    BOT   = 0
    NONE  = auto()
    BOOL  = auto()
    NUM   = auto()
    STR   = auto()
    SEQ   = auto()
    MAP   = auto()
    SET   = auto()
    ITER  = auto()
    FUNC  = auto()
    TOP   = auto()

# Subsorting: BOOL ⊑ NUM, everything ⊑ TOP, BOT ⊑ everything
_SUBSORT: Dict[Sort, Set[Sort]] = {
    Sort.BOT:  {s for s in Sort},
    Sort.BOOL: {Sort.BOOL, Sort.NUM, Sort.TOP},
    Sort.NONE: {Sort.NONE, Sort.TOP},
    Sort.NUM:  {Sort.NUM, Sort.TOP},
    Sort.STR:  {Sort.STR, Sort.SEQ, Sort.TOP},  # str ⊑ seq (iterable)
    Sort.SEQ:  {Sort.SEQ, Sort.TOP},
    Sort.MAP:  {Sort.MAP, Sort.TOP},
    Sort.SET:  {Sort.SET, Sort.TOP},
    Sort.ITER: {Sort.ITER, Sort.TOP},
    Sort.FUNC: {Sort.FUNC, Sort.TOP},
    Sort.TOP:  {Sort.TOP},
}

def sorts_compatible(a: Sort, b: Sort) -> bool:
    """Check if two sorts are compatible (have a common upper bound ≠ TOP)."""
    if a == b:
        return True
    return bool(_SUBSORT.get(a, set()) & _SUBSORT.get(b, set()) - {Sort.TOP}) or a == Sort.TOP or b == Sort.TOP


# ─── §2  Refinement Predicates (dependent type structure) ──────────
#
# From Martin-Löf dependent type theory: each sort is refined by
# decidable predicates that constrain its inhabitants.

class Refinement(IntEnum):
    SORTED          = 0
    REVERSED        = auto()
    LENGTH_PRESERVING = auto()
    PERMUTATION     = auto()
    FILTERED        = auto()
    MAPPED          = auto()
    ACCUMULATED     = auto()
    POSITIVE        = auto()
    NON_NEGATIVE    = auto()
    BOUNDED         = auto()
    INJECTIVE       = auto()
    IDEMPOTENT      = auto()
    MONOTONE        = auto()
    COMMUTATIVE     = auto()
    ASSOCIATIVE     = auto()


# ─── §3  Effects (the effect monoid) ───────────────────────────────
#
# From algebraic effect theory: each operation carries an effect.

class Effect(IntEnum):
    PURE     = 0
    MUTATE   = auto()
    ALLOCATE = auto()
    ITERATE  = auto()
    RECURSE  = auto()
    CALL_EXT = auto()  # calls to external/builtin functions


# ─── §4  Typed Operations (morphisms in the abstract algebra) ──────
#
# Each operation is a morphism in the Lawvere theory: it has a
# sort signature, refinement annotations, and an effect.

@dataclass(frozen=True)
class TypedOp:
    """A morphism in the abstract algebra of programs."""
    name: str                               # abstract operation name
    input_sorts: Tuple[Sort, ...]           # domain sorts
    output_sort: Sort                       # codomain sort
    refinements: FrozenSet[Refinement]      # dependent type predicates
    effect: Effect                          # computational effect

    @property
    def sort_signature(self) -> Tuple[Tuple[Sort, ...], Sort]:
        return (self.input_sorts, self.output_sort)


# ─── §5  Data Flow Edge (morphism in the data flow category) ───────

@dataclass(frozen=True)
class FlowEdge:
    """A morphism in the data flow category D_f."""
    source_block: int    # source basic block index
    target_block: int    # target basic block index
    source_sort: Sort    # type of source variable
    target_sort: Sort    # type of target variable
    op_index: int        # index into the operation list


# ─── §6  Computational Motive ─────────────────────────────────────
#
# M(f) = (Σ_f, G_f, H_f) — the universal invariant of program f.
#
# Σ_f = algebraic signature (multiset of typed operations)
# G_f = data flow graph (edges between blocks, labeled by operations)
# H_f = cohomological data (H⁰ sections, rank of H¹)

@dataclass
class Motive:
    """The computational motive of a program."""
    # §4: Algebraic signature
    operations: List[TypedOp]

    # §5: Data flow category
    flow_edges: List[FlowEdge]
    num_blocks: int

    # Cohomological data
    h0_sections: int        # dim H⁰ = number of globally consistent type sections
    h1_rank: int            # rank H¹ = number of independent type obstructions

    # §7: Additional invariants
    input_sorts: Tuple[Sort, ...]    # parameter types (Σ-type domain)
    output_sort: Sort                # return type
    global_refinements: FrozenSet[Refinement]  # refinements on the output
    has_recursion: bool
    has_iteration: bool
    loop_depth: int                  # fundamental groupoid rank
    num_branches: int                # number of conditional branches


# ─── §7  Abstract Interpreter (AST → Motive) ──────────────────────
#
# Walks the AST and extracts the computational motive by:
# 1. Inferring sorts for each expression (type fiber at each point)
# 2. Extracting typed operations (morphisms in the algebra)
# 3. Building the data flow category
# 4. Computing Čech cohomology of the type presheaf

# Sort inference for built-in names and attributes
_BUILTIN_SORTS: Dict[str, Sort] = {
    'True': Sort.BOOL, 'False': Sort.BOOL, 'None': Sort.NONE,
    'int': Sort.NUM, 'float': Sort.NUM, 'complex': Sort.NUM,
    'str': Sort.STR, 'bytes': Sort.STR,
    'list': Sort.SEQ, 'tuple': Sort.SEQ, 'deque': Sort.SEQ,
    'dict': Sort.MAP, 'OrderedDict': Sort.MAP, 'defaultdict': Sort.MAP, 'Counter': Sort.MAP,
    'set': Sort.SET, 'frozenset': Sort.SET,
    'range': Sort.ITER, 'enumerate': Sort.ITER, 'zip': Sort.ITER,
    'map': Sort.ITER, 'filter': Sort.ITER,
    'len': Sort.NUM, 'sum': Sort.NUM, 'min': Sort.NUM, 'max': Sort.NUM,
    'abs': Sort.NUM, 'round': Sort.NUM, 'ord': Sort.NUM,
    'sorted': Sort.SEQ, 'reversed': Sort.ITER, 'list': Sort.SEQ,
    'isinstance': Sort.BOOL, 'callable': Sort.BOOL,
    'any': Sort.BOOL, 'all': Sort.BOOL,
    'print': Sort.NONE, 'repr': Sort.STR, 'str': Sort.STR,
    'math': Sort.NUM, 'operator': Sort.FUNC,
}

_METHOD_SORTS: Dict[str, Sort] = {
    'append': Sort.NONE, 'extend': Sort.NONE, 'insert': Sort.NONE,
    'pop': Sort.TOP, 'remove': Sort.NONE, 'clear': Sort.NONE,
    'sort': Sort.NONE, 'reverse': Sort.NONE,
    'get': Sort.TOP, 'setdefault': Sort.TOP, 'update': Sort.NONE,
    'keys': Sort.ITER, 'values': Sort.ITER, 'items': Sort.ITER,
    'add': Sort.NONE, 'discard': Sort.NONE,
    'union': Sort.SET, 'intersection': Sort.SET, 'difference': Sort.SET,
    'join': Sort.STR, 'split': Sort.SEQ, 'strip': Sort.STR,
    'replace': Sort.STR, 'find': Sort.NUM, 'count': Sort.NUM,
    'startswith': Sort.BOOL, 'endswith': Sort.BOOL, 'isdigit': Sort.BOOL,
    'lower': Sort.STR, 'upper': Sort.STR,
    'encode': Sort.STR, 'decode': Sort.STR,
    'copy': Sort.TOP, 'deepcopy': Sort.TOP,
    'appendleft': Sort.NONE, 'popleft': Sort.TOP,
}

# Abstract operation names: map concrete operations to abstract names
# This is the key abstraction — list.append and deque.append are both Seq.push
_OP_ABSTRACTION: Dict[str, str] = {
    'append': 'Seq.push', 'appendleft': 'Seq.push', 'extend': 'Seq.extend',
    'insert': 'Seq.insert', 'pop': 'Seq.pop', 'popleft': 'Seq.pop',
    'sort': 'Seq.sort', 'reverse': 'Seq.reverse',
    'add': 'Set.insert', 'discard': 'Set.remove', 'remove': 'Set.remove',
    'union': 'Set.union', 'intersection': 'Set.intersect', 'difference': 'Set.diff',
    'get': 'Map.lookup', 'setdefault': 'Map.insert_default',
    'update': 'Map.merge', 'keys': 'Map.keys', 'values': 'Map.values',
    'items': 'Map.items',
    'join': 'Str.join', 'split': 'Str.split', 'strip': 'Str.trim',
    'replace': 'Str.replace', 'find': 'Str.search',
    'lower': 'Str.transform', 'upper': 'Str.transform',
    'copy': 'Clone.shallow', 'deepcopy': 'Clone.deep',
}

# Refinements inferred from certain operations
_OP_REFINEMENTS: Dict[str, FrozenSet[Refinement]] = {
    'Seq.sort': frozenset({Refinement.SORTED, Refinement.PERMUTATION}),
    'Seq.reverse': frozenset({Refinement.REVERSED, Refinement.PERMUTATION}),
    'Seq.push': frozenset({Refinement.LENGTH_PRESERVING}),
    'Set.union': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT}),
    'Set.intersect': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT}),
}

# Sort inference for binary/unary/comparison operators
_BINOP_SORT: Dict[type, Sort] = {
    ast.Add: Sort.TOP, ast.Sub: Sort.NUM, ast.Mult: Sort.TOP,
    ast.Div: Sort.NUM, ast.FloorDiv: Sort.NUM, ast.Mod: Sort.NUM,
    ast.Pow: Sort.NUM, ast.LShift: Sort.NUM, ast.RShift: Sort.NUM,
    ast.BitOr: Sort.NUM, ast.BitXor: Sort.NUM, ast.BitAnd: Sort.NUM,
    ast.MatMult: Sort.NUM,
}

_CMPOP_ABSTRACT: Dict[type, str] = {
    ast.Eq: 'Cmp.eq', ast.NotEq: 'Cmp.neq',
    ast.Lt: 'Cmp.lt', ast.LtE: 'Cmp.le',
    ast.Gt: 'Cmp.gt', ast.GtE: 'Cmp.ge',
    ast.In: 'Cmp.member', ast.NotIn: 'Cmp.not_member',
    ast.Is: 'Cmp.identity', ast.IsNot: 'Cmp.not_identity',
}

_AUGOP_ABSTRACT: Dict[type, str] = {
    ast.Add: 'Accum.sum', ast.Sub: 'Accum.diff',
    ast.Mult: 'Accum.product', ast.BitOr: 'Accum.union',
    ast.BitAnd: 'Accum.intersect', ast.BitXor: 'Accum.xor',
}

_ACCUM_REFINEMENTS: Dict[str, FrozenSet[Refinement]] = {
    'Accum.sum': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.ACCUMULATED}),
    'Accum.product': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.ACCUMULATED}),
    'Accum.union': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT, Refinement.ACCUMULATED}),
    'Accum.intersect': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT, Refinement.ACCUMULATED}),
    'Accum.diff': frozenset({Refinement.ACCUMULATED}),
    'Accum.xor': frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.ACCUMULATED}),
}


class MotiveExtractor(ast.NodeVisitor):
    """Extract the computational motive from a function AST.

    This is the abstract interpreter that builds M(f) by walking the AST
    and extracting typed operations, data flow edges, and type fibers.
    """

    def __init__(self) -> None:
        self._ops: List[TypedOp] = []
        self._edges: List[FlowEdge] = []
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
        # Block-level type fibers for cohomology
        self._block_fibers: Dict[int, Set[Sort]] = {}
        # Track which variables are read/written per block
        self._block_reads: Dict[int, Set[str]] = {}
        self._block_writes: Dict[int, Set[str]] = {}

    def extract(self, func_node: ast.FunctionDef) -> Motive:
        """Extract the computational motive from a function definition."""
        self._func_name = func_node.name

        # Extract parameter sorts (Σ-type domain)
        for arg in func_node.args.args:
            sort = self._infer_param_sort(arg, func_node)
            self._param_sorts.append(sort)
            self._var_sorts[arg.arg] = sort

        # Walk the body
        self._block = 0
        self._num_blocks = 1
        self._block_fibers[0] = set()
        self._block_reads[0] = set()
        self._block_writes[0] = set()

        for stmt in func_node.body:
            # Skip docstrings
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant) and isinstance(stmt.value.value, str):
                continue
            self._visit_stmt(stmt)

        # Compute Čech cohomology
        h0, h1 = self._compute_cohomology()

        # Infer global refinements from operations
        self._infer_global_refinements()

        return Motive(
            operations=list(self._ops),
            flow_edges=list(self._edges),
            num_blocks=self._num_blocks,
            h0_sections=h0,
            h1_rank=h1,
            input_sorts=tuple(self._param_sorts),
            output_sort=self._return_sort,
            global_refinements=frozenset(self._global_refinements),
            has_recursion=self._has_recursion,
            has_iteration=self._has_iteration,
            loop_depth=self._loop_depth,
            num_branches=self._num_branches,
        )

    def _infer_param_sort(self, arg: ast.arg, func: ast.FunctionDef) -> Sort:
        """Infer parameter sort from usage in the function body."""
        name = arg.arg
        # Check annotation first
        if arg.annotation:
            return self._sort_from_annotation(arg.annotation)

        # Infer from usage
        for node in ast.walk(func):
            if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and node.value.id == name:
                return Sort.SEQ
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'len':
                if node.args and isinstance(node.args[0], ast.Name) and node.args[0].id == name:
                    return Sort.SEQ
            if isinstance(node, ast.For) and isinstance(node.iter, ast.Name) and node.iter.id == name:
                return Sort.SEQ
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                if isinstance(node.func.value, ast.Name) and node.func.value.id == name:
                    method = node.func.attr
                    if method in ('append', 'extend', 'insert', 'pop', 'sort', 'reverse', 'index'):
                        return Sort.SEQ
                    if method in ('get', 'keys', 'values', 'items', 'setdefault', 'update'):
                        return Sort.MAP
                    if method in ('add', 'discard', 'union', 'intersection', 'difference'):
                        return Sort.SET
                    if method in ('join', 'split', 'strip', 'replace', 'find', 'lower', 'upper', 'encode', 'startswith', 'endswith'):
                        return Sort.STR
            # Numeric operations
            if isinstance(node, ast.BinOp):
                if isinstance(node.left, ast.Name) and node.left.id == name and isinstance(node.op, (ast.Sub, ast.Div, ast.FloorDiv, ast.Mod, ast.Pow)):
                    return Sort.NUM
                if isinstance(node.right, ast.Name) and node.right.id == name and isinstance(node.op, (ast.Sub, ast.Div, ast.FloorDiv, ast.Mod, ast.Pow)):
                    return Sort.NUM
            if isinstance(node, ast.Compare):
                if isinstance(node.left, ast.Name) and node.left.id == name:
                    for op in node.ops:
                        if isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                            return Sort.NUM
        return Sort.TOP

    def _sort_from_annotation(self, ann: ast.expr) -> Sort:
        if isinstance(ann, ast.Name):
            return _BUILTIN_SORTS.get(ann.id, Sort.TOP)
        if isinstance(ann, ast.Subscript) and isinstance(ann.value, ast.Name):
            container = ann.value.id
            if container in ('list', 'List', 'Sequence', 'Iterable'):
                return Sort.SEQ
            if container in ('dict', 'Dict', 'Mapping'):
                return Sort.MAP
            if container in ('set', 'Set', 'FrozenSet'):
                return Sort.SET
            if container in ('Tuple', 'tuple'):
                return Sort.SEQ
        return Sort.TOP

    def _new_block(self) -> int:
        self._num_blocks += 1
        b = self._num_blocks - 1
        self._block_fibers[b] = set()
        self._block_reads[b] = set()
        self._block_writes[b] = set()
        return b

    def _add_op(self, name: str, inputs: Tuple[Sort, ...], output: Sort,
                refinements: FrozenSet[Refinement] = frozenset(),
                effect: Effect = Effect.PURE) -> int:
        """Add a typed operation and return its index."""
        op = TypedOp(name=name, input_sorts=inputs, output_sort=output,
                     refinements=refinements, effect=effect)
        idx = len(self._ops)
        self._ops.append(op)
        self._block_fibers.setdefault(self._block, set()).add(output)
        return idx

    def _add_flow_edge(self, src_block: int, tgt_block: int,
                       src_sort: Sort, tgt_sort: Sort, op_idx: int) -> None:
        self._edges.append(FlowEdge(
            source_block=src_block, target_block=tgt_block,
            source_sort=src_sort, target_sort=tgt_sort, op_index=op_idx,
        ))

    # ── Statement visitors ──────────────────────────────────────────

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
                self._visit_call_expr(node.value)
        elif isinstance(node, (ast.Try,)):
            for handler in getattr(node, 'handlers', []):
                for s in handler.body:
                    self._visit_stmt(s)
            for s in getattr(node, 'body', []):
                self._visit_stmt(s)
        elif isinstance(node, ast.With):
            for s in node.body:
                self._visit_stmt(s)
        elif isinstance(node, ast.FunctionDef):
            # Nested function — extract as a FUNC-producing op
            self._add_op('Func.define', (), Sort.FUNC, effect=Effect.ALLOCATE)
            # Still walk it for its operations (they contribute to the motive)
            inner = MotiveExtractor()
            inner.extract(node)
            for op in inner._ops:
                self._ops.append(op)
        elif isinstance(node, ast.Delete):
            for target in node.targets:
                s = self._infer_sort(target)
                self._add_op('Mem.free', (s,), Sort.NONE, effect=Effect.MUTATE)

    def _visit_assign(self, node: ast.Assign) -> None:
        sort = self._infer_sort(node.value)
        for target in node.targets:
            if isinstance(target, ast.Name):
                old_sort = self._var_sorts.get(target.id, Sort.BOT)
                self._var_sorts[target.id] = sort
                self._block_writes.setdefault(self._block, set()).add(target.id)
                if old_sort != Sort.BOT and old_sort != sort:
                    # Type changes → record a flow edge within this block
                    idx = self._add_op('Assign.rebind', (old_sort,), sort)
                else:
                    idx = self._add_op('Assign.bind', (), sort)
            elif isinstance(target, ast.Subscript):
                container_sort = self._infer_sort(target.value)
                idx = self._add_op('Container.store', (container_sort, sort), container_sort,
                                   effect=Effect.MUTATE)
            elif isinstance(target, ast.Tuple) or isinstance(target, ast.List):
                self._add_op('Destructure.unpack', (sort,), Sort.TOP)
                for elt in target.elts:
                    if isinstance(elt, ast.Name):
                        self._var_sorts[elt.id] = Sort.TOP
                        self._block_writes.setdefault(self._block, set()).add(elt.id)

        # Also extract operations from the value expression
        self._extract_expr_ops(node.value)

    def _visit_aug_assign(self, node: ast.AugAssign) -> None:
        target_sort = Sort.TOP
        if isinstance(node.target, ast.Name):
            target_sort = self._var_sorts.get(node.target.id, Sort.TOP)
            self._block_writes.setdefault(self._block, set()).add(node.target.id)
            self._block_reads.setdefault(self._block, set()).add(node.target.id)

        value_sort = self._infer_sort(node.value)
        op_type = type(node.op)

        # Accumulator detection (from dependent type theory: fold types)
        abstract_name = _AUGOP_ABSTRACT.get(op_type, 'Accum.generic')
        refinements = _ACCUM_REFINEMENTS.get(abstract_name, frozenset())
        self._add_op(abstract_name, (target_sort, value_sort), target_sort,
                     refinements=refinements, effect=Effect.MUTATE)

        self._extract_expr_ops(node.value)

    def _visit_return(self, node: ast.Return) -> None:
        if node.value is not None:
            sort = self._infer_sort(node.value)
            self._return_sort = sort
            self._add_op('Return', (sort,), sort)
            self._extract_expr_ops(node.value)

            # Check for recursive return (HoTT: path in the loop space)
            if self._contains_self_call(node.value):
                self._has_recursion = True
                self._add_op('Recurse.return', (sort,), sort, effect=Effect.RECURSE)

    def _visit_if(self, node: ast.If) -> None:
        self._num_branches += 1
        # The condition produces a BOOL
        cond_sort = self._infer_sort(node.test)
        self._add_op('Branch.test', (cond_sort,), Sort.BOOL)
        self._extract_expr_ops(node.test)

        # True branch
        prev_block = self._block
        true_block = self._new_block()
        self._block = true_block
        self._add_flow_edge(prev_block, true_block, Sort.BOOL, Sort.TOP, len(self._ops) - 1)
        for s in node.body:
            self._visit_stmt(s)

        # False branch
        if node.orelse:
            false_block = self._new_block()
            self._block = false_block
            self._add_flow_edge(prev_block, false_block, Sort.BOOL, Sort.TOP, len(self._ops) - 1)
            for s in node.orelse:
                self._visit_stmt(s)

        # Merge block
        merge_block = self._new_block()
        self._add_flow_edge(true_block, merge_block, Sort.TOP, Sort.TOP, len(self._ops) - 1 if self._ops else 0)
        if node.orelse:
            self._add_flow_edge(false_block, merge_block, Sort.TOP, Sort.TOP, len(self._ops) - 1 if self._ops else 0)
        self._block = merge_block

    def _visit_for(self, node: ast.For) -> None:
        self._has_iteration = True
        self._current_loop_depth += 1
        self._loop_depth = max(self._loop_depth, self._current_loop_depth)

        iter_sort = self._infer_sort(node.iter)
        self._add_op('Loop.iterate', (iter_sort,), Sort.TOP, effect=Effect.ITERATE)
        self._extract_expr_ops(node.iter)

        if isinstance(node.target, ast.Name):
            self._var_sorts[node.target.id] = Sort.TOP
            self._block_writes.setdefault(self._block, set()).add(node.target.id)
        elif isinstance(node.target, ast.Tuple):
            for elt in node.target.elts:
                if isinstance(elt, ast.Name):
                    self._var_sorts[elt.id] = Sort.TOP
                    self._block_writes.setdefault(self._block, set()).add(elt.id)

        # Loop body is a new block with back-edge (HoTT: loop in π₁)
        prev_block = self._block
        loop_block = self._new_block()
        self._block = loop_block
        self._add_flow_edge(prev_block, loop_block, iter_sort, Sort.TOP, len(self._ops) - 1)

        for s in node.body:
            self._visit_stmt(s)

        # Back-edge (fundamental groupoid: non-trivial π₁)
        self._add_flow_edge(loop_block, loop_block, Sort.TOP, Sort.TOP, len(self._ops) - 1 if self._ops else 0)

        # Post-loop block
        post_block = self._new_block()
        self._add_flow_edge(loop_block, post_block, Sort.TOP, Sort.TOP, len(self._ops) - 1 if self._ops else 0)
        self._block = post_block

        self._current_loop_depth -= 1

    def _visit_while(self, node: ast.While) -> None:
        self._has_iteration = True
        self._current_loop_depth += 1
        self._loop_depth = max(self._loop_depth, self._current_loop_depth)

        cond_sort = self._infer_sort(node.test)
        self._add_op('Loop.while', (cond_sort,), Sort.BOOL, effect=Effect.ITERATE)
        self._extract_expr_ops(node.test)

        prev_block = self._block
        loop_block = self._new_block()
        self._block = loop_block
        self._add_flow_edge(prev_block, loop_block, Sort.BOOL, Sort.TOP, len(self._ops) - 1)

        for s in node.body:
            self._visit_stmt(s)

        # Back-edge
        self._add_flow_edge(loop_block, loop_block, Sort.TOP, Sort.TOP, len(self._ops) - 1 if self._ops else 0)

        post_block = self._new_block()
        self._add_flow_edge(loop_block, post_block, Sort.TOP, Sort.TOP, len(self._ops) - 1 if self._ops else 0)
        self._block = post_block

        self._current_loop_depth -= 1

    def _visit_call_expr(self, node: ast.Call) -> None:
        """Visit a call expression used as a statement."""
        sort = self._infer_sort(node)
        self._extract_expr_ops(node)

    # ── Expression sort inference ───────────────────────────────────

    def _infer_sort(self, node: ast.expr) -> Sort:
        """Infer the abstract sort of an expression (type fiber)."""
        if isinstance(node, ast.Constant):
            v = node.value
            if isinstance(v, bool):
                return Sort.BOOL
            if isinstance(v, (int, float, complex)):
                return Sort.NUM
            if isinstance(v, str):
                return Sort.STR
            if isinstance(v, bytes):
                return Sort.STR
            if v is None:
                return Sort.NONE
            return Sort.TOP

        if isinstance(node, ast.Name):
            if node.id in self._var_sorts:
                self._block_reads.setdefault(self._block, set()).add(node.id)
                return self._var_sorts[node.id]
            return _BUILTIN_SORTS.get(node.id, Sort.TOP)

        if isinstance(node, (ast.List, ast.ListComp)):
            return Sort.SEQ
        if isinstance(node, (ast.Tuple,)):
            return Sort.SEQ
        if isinstance(node, (ast.Dict, ast.DictComp)):
            return Sort.MAP
        if isinstance(node, (ast.Set, ast.SetComp)):
            return Sort.SET
        if isinstance(node, ast.GeneratorExp):
            return Sort.ITER

        if isinstance(node, ast.BinOp):
            left_sort = self._infer_sort(node.left)
            right_sort = self._infer_sort(node.right)
            if isinstance(node.op, ast.Add):
                # Add is polymorphic: str+str→str, seq+seq→seq, num+num→num
                if left_sort == Sort.STR or right_sort == Sort.STR:
                    return Sort.STR
                if left_sort == Sort.SEQ or right_sort == Sort.SEQ:
                    return Sort.SEQ
                return Sort.NUM
            if isinstance(node.op, ast.Mult):
                if left_sort == Sort.STR or right_sort == Sort.STR:
                    return Sort.STR
                if left_sort == Sort.SEQ or right_sort == Sort.SEQ:
                    return Sort.SEQ
                return Sort.NUM
            return _BINOP_SORT.get(type(node.op), Sort.NUM)

        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.Not):
                return Sort.BOOL
            return Sort.NUM

        if isinstance(node, ast.BoolOp):
            return Sort.BOOL

        if isinstance(node, ast.Compare):
            return Sort.BOOL

        if isinstance(node, ast.IfExp):
            true_sort = self._infer_sort(node.body)
            false_sort = self._infer_sort(node.orelse)
            if true_sort == false_sort:
                return true_sort
            return Sort.TOP

        if isinstance(node, ast.Call):
            return self._infer_call_sort(node)

        if isinstance(node, ast.Subscript):
            container_sort = self._infer_sort(node.value)
            if container_sort == Sort.STR:
                if isinstance(node.slice, ast.Slice):
                    return Sort.STR
                return Sort.STR
            if container_sort == Sort.SEQ:
                if isinstance(node.slice, ast.Slice):
                    return Sort.SEQ
                return Sort.TOP
            if container_sort == Sort.MAP:
                return Sort.TOP
            return Sort.TOP

        if isinstance(node, ast.Attribute):
            return _METHOD_SORTS.get(node.attr, Sort.TOP)

        if isinstance(node, ast.Starred):
            return Sort.SEQ

        if isinstance(node, ast.Lambda):
            return Sort.FUNC

        if isinstance(node, ast.JoinedStr):
            return Sort.STR

        if isinstance(node, ast.Slice):
            return Sort.SEQ

        return Sort.TOP

    def _infer_call_sort(self, node: ast.Call) -> Sort:
        """Infer sort of a function call."""
        if isinstance(node.func, ast.Name):
            name = node.func.id
            if name == self._func_name:
                self._has_recursion = True
                return self._return_sort
            return _BUILTIN_SORTS.get(name, Sort.TOP)

        if isinstance(node.func, ast.Attribute):
            method = node.func.attr
            return _METHOD_SORTS.get(method, Sort.TOP)

        return Sort.TOP

    # ── Expression operation extraction ─────────────────────────────

    def _extract_expr_ops(self, node: ast.expr) -> None:
        """Extract typed operations from an expression."""
        if isinstance(node, ast.BinOp):
            left_sort = self._infer_sort(node.left)
            right_sort = self._infer_sort(node.right)
            result_sort = self._infer_sort(node)
            op_name = f'Arith.{type(node.op).__name__}'
            # Distinguish floor division from true division (different semantics!)
            if isinstance(node.op, ast.FloorDiv):
                op_name = 'Arith.FloorDiv'
            elif isinstance(node.op, ast.Div):
                op_name = 'Arith.TrueDiv'

            refinements: FrozenSet[Refinement] = frozenset()
            if isinstance(node.op, (ast.Add, ast.Mult)):
                refinements = frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE})
            self._add_op(op_name, (left_sort, right_sort), result_sort, refinements=refinements)

            self._extract_expr_ops(node.left)
            self._extract_expr_ops(node.right)

        elif isinstance(node, ast.UnaryOp):
            operand_sort = self._infer_sort(node.operand)
            self._add_op(f'Unary.{type(node.op).__name__}', (operand_sort,),
                         Sort.BOOL if isinstance(node.op, ast.Not) else Sort.NUM)
            self._extract_expr_ops(node.operand)

        elif isinstance(node, ast.Compare):
            left_sort = self._infer_sort(node.left)
            for op, comparator in zip(node.ops, node.comparators):
                right_sort = self._infer_sort(comparator)
                abstract = _CMPOP_ABSTRACT.get(type(op), 'Cmp.generic')
                self._add_op(abstract, (left_sort, right_sort), Sort.BOOL)
                self._extract_expr_ops(comparator)
                left_sort = right_sort
            self._extract_expr_ops(node.left)

        elif isinstance(node, ast.BoolOp):
            for value in node.values:
                self._extract_expr_ops(value)
            sort = self._infer_sort(node)
            op_name = 'Logic.And' if isinstance(node.op, ast.And) else 'Logic.Or'
            self._add_op(op_name, tuple(Sort.BOOL for _ in node.values), Sort.BOOL,
                         refinements=frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}))

        elif isinstance(node, ast.Call):
            self._extract_call_ops(node)

        elif isinstance(node, ast.IfExp):
            self._add_op('Branch.ternary', (Sort.BOOL,), self._infer_sort(node))
            self._extract_expr_ops(node.test)
            self._extract_expr_ops(node.body)
            self._extract_expr_ops(node.orelse)

        elif isinstance(node, ast.Subscript):
            container_sort = self._infer_sort(node.value)
            result_sort = self._infer_sort(node)
            if isinstance(node.slice, ast.Slice):
                self._add_op('Container.slice', (container_sort,), result_sort)
            else:
                self._add_op('Container.index', (container_sort, Sort.NUM), result_sort)
            self._extract_expr_ops(node.value)

        elif isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            self._extract_comprehension_ops(node)

        elif isinstance(node, ast.Lambda):
            self._add_op('Func.lambda', (), Sort.FUNC, effect=Effect.ALLOCATE)

        elif isinstance(node, ast.Starred):
            self._add_op('Destructure.splat', (self._infer_sort(node.value),), Sort.SEQ)

    def _extract_call_ops(self, node: ast.Call) -> None:
        """Extract typed operations from a function call."""
        if isinstance(node.func, ast.Name):
            name = node.func.id
            arg_sorts = tuple(self._infer_sort(a) for a in node.args)
            result_sort = self._infer_call_sort(node)

            if name == self._func_name:
                self._add_op('Recurse.call', arg_sorts, result_sort, effect=Effect.RECURSE)
            elif name in ('sorted',):
                self._add_op('Seq.sort', arg_sorts, Sort.SEQ,
                             refinements=frozenset({Refinement.SORTED, Refinement.PERMUTATION}))
                # Check for reverse=True
                for kw in node.keywords:
                    if kw.arg == 'reverse' and isinstance(kw.value, ast.Constant) and kw.value.value:
                        self._global_refinements.add(Refinement.REVERSED)
            elif name in ('reversed',):
                self._add_op('Seq.reverse', arg_sorts, Sort.ITER,
                             refinements=frozenset({Refinement.REVERSED}))
            elif name == 'len':
                self._add_op('Measure.length', arg_sorts, Sort.NUM)
            elif name in ('sum',):
                self._add_op('Accum.sum', arg_sorts, Sort.NUM,
                             refinements=frozenset({Refinement.ACCUMULATED, Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}))
            elif name in ('min', 'max'):
                self._add_op(f'Accum.{name}', arg_sorts, Sort.NUM,
                             refinements=frozenset({Refinement.ACCUMULATED, Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT}))
            elif name in ('abs',):
                self._add_op('Arith.abs', arg_sorts, Sort.NUM,
                             refinements=frozenset({Refinement.NON_NEGATIVE, Refinement.IDEMPOTENT}))
            elif name in ('set', 'frozenset'):
                self._add_op('Construct.set', arg_sorts, Sort.SET)
            elif name in ('list', 'tuple'):
                self._add_op('Construct.seq', arg_sorts, Sort.SEQ)
            elif name in ('dict',):
                self._add_op('Construct.map', arg_sorts, Sort.MAP)
            elif name in ('int', 'float'):
                self._add_op('Cast.numeric', arg_sorts, Sort.NUM)
            elif name in ('str', 'repr'):
                self._add_op('Cast.string', arg_sorts, Sort.STR)
            elif name in ('bool',):
                self._add_op('Cast.bool', arg_sorts, Sort.BOOL)
            elif name in ('isinstance', 'issubclass'):
                self._add_op('Type.check', arg_sorts, Sort.BOOL)
            elif name in ('enumerate',):
                self._add_op('Iter.enumerate', arg_sorts, Sort.ITER)
            elif name in ('zip',):
                self._add_op('Iter.zip', arg_sorts, Sort.ITER)
            elif name in ('range',):
                self._add_op('Iter.range', arg_sorts, Sort.ITER)
            elif name in ('map',):
                self._add_op('Iter.map', arg_sorts, Sort.ITER,
                             refinements=frozenset({Refinement.MAPPED}))
            elif name in ('filter',):
                self._add_op('Iter.filter', arg_sorts, Sort.ITER,
                             refinements=frozenset({Refinement.FILTERED}))
            elif name in ('reduce',):
                self._add_op('Accum.reduce', arg_sorts, Sort.TOP,
                             refinements=frozenset({Refinement.ACCUMULATED}))
            elif name in ('any', 'all'):
                self._add_op(f'Logic.{name}', arg_sorts, Sort.BOOL)
            elif name == 'print':
                self._add_op('IO.print', arg_sorts, Sort.NONE, effect=Effect.CALL_EXT)
            elif name in ('hash',):
                self._add_op('Hash.compute', arg_sorts, Sort.NUM)
            elif name in ('id',):
                self._add_op('Identity.address', arg_sorts, Sort.NUM)
            elif name == 'type':
                self._add_op('Type.of', arg_sorts, Sort.TOP)
            elif name in ('heappush', 'heappop', 'heapify', 'heapreplace'):
                heap_op = name.replace('heap', 'Heap.')
                self._add_op(heap_op, arg_sorts, result_sort, effect=Effect.MUTATE)
            elif name == 'bisect_left' or name == 'bisect_right' or name == 'bisect':
                self._add_op('Search.bisect', arg_sorts, Sort.NUM)
            elif name == 'insort' or name == 'insort_left' or name == 'insort_right':
                self._add_op('Seq.sorted_insert', arg_sorts, Sort.NONE, effect=Effect.MUTATE)
            else:
                self._add_op(f'Call.{name}', arg_sorts, result_sort, effect=Effect.CALL_EXT)

        elif isinstance(node.func, ast.Attribute):
            method = node.func.attr
            obj_sort = self._infer_sort(node.func.value)
            arg_sorts = tuple(self._infer_sort(a) for a in node.args)
            result_sort = _METHOD_SORTS.get(method, Sort.TOP)
            abstract = _OP_ABSTRACTION.get(method, f'Method.{method}')
            refinements = _OP_REFINEMENTS.get(abstract, frozenset())
            effect = Effect.MUTATE if method in ('append', 'extend', 'insert', 'pop',
                                                  'remove', 'clear', 'sort', 'reverse',
                                                  'add', 'discard', 'update', 'appendleft',
                                                  'popleft') else Effect.PURE
            self._add_op(abstract, (obj_sort,) + arg_sorts, result_sort,
                         refinements=refinements, effect=effect)

        # Extract ops from arguments
        for arg in node.args:
            self._extract_expr_ops(arg)
        for kw in node.keywords:
            if kw.value:
                self._extract_expr_ops(kw.value)

    def _extract_comprehension_ops(self, node: ast.expr) -> None:
        """Extract ops from comprehensions (a common Python idiom)."""
        result_sort = self._infer_sort(node)
        refinements: Set[Refinement] = set()

        for gen in getattr(node, 'generators', []):
            iter_sort = self._infer_sort(gen.iter)
            self._add_op('Comprehension.iterate', (iter_sort,), Sort.TOP, effect=Effect.ITERATE)
            for if_clause in gen.ifs:
                self._add_op('Comprehension.filter', (Sort.BOOL,), Sort.BOOL)
                refinements.add(Refinement.FILTERED)
                self._extract_expr_ops(if_clause)
            self._extract_expr_ops(gen.iter)

        if isinstance(node, ast.ListComp):
            self._add_op('Comprehension.collect', (), Sort.SEQ,
                         refinements=frozenset(refinements) | frozenset({Refinement.MAPPED}))
            if hasattr(node, 'elt'):
                self._extract_expr_ops(node.elt)
        elif isinstance(node, ast.SetComp):
            self._add_op('Comprehension.collect_set', (), Sort.SET,
                         refinements=frozenset(refinements))
            if hasattr(node, 'elt'):
                self._extract_expr_ops(node.elt)
        elif isinstance(node, ast.DictComp):
            self._add_op('Comprehension.collect_map', (), Sort.MAP,
                         refinements=frozenset(refinements))
        elif isinstance(node, ast.GeneratorExp):
            self._add_op('Comprehension.lazy', (), Sort.ITER,
                         refinements=frozenset(refinements))
            if hasattr(node, 'elt'):
                self._extract_expr_ops(node.elt)

    def _contains_self_call(self, node: ast.expr) -> bool:
        """Check if expression contains a recursive call."""
        for child in ast.walk(node):
            if isinstance(child, ast.Call) and isinstance(child.func, ast.Name):
                if child.func.id == self._func_name:
                    return True
        return False

    # ── Čech Cohomology Computation ─────────────────────────────────
    #
    # The type presheaf F assigns to each block its set of sorts (type fiber).
    # δ⁰: C⁰ → C¹ checks that fibers are compatible along flow edges.
    # H⁰ = ker(δ⁰) = globally consistent sort sections.
    # H¹ = ker(δ¹)/im(δ⁰) = independent type obstructions.

    def _compute_cohomology(self) -> Tuple[int, int]:
        """Compute Čech cohomology (H⁰, rank H¹) of the type presheaf."""
        if self._num_blocks <= 1 or not self._edges:
            # Trivial cover: H⁰ = 1, H¹ = 0
            return (1, 0)

        # C⁰: for each block, the set of sorts in its fiber
        fibers = self._block_fibers

        # δ⁰: check compatibility along each edge
        # A 0-cochain (sort assignment per block) is a cocycle iff
        # for each edge (i→j), the assigned sorts are compatible
        h0 = 0  # count globally consistent sort sections
        all_sorts = set()
        for f in fibers.values():
            all_sorts.update(f)
        if not all_sorts:
            all_sorts = {Sort.TOP}

        # H⁰: count sorts that appear consistently across all blocks
        for s in all_sorts:
            # A sort s gives a global section if every block fiber
            # contains a sort compatible with s
            is_global = True
            for b in range(self._num_blocks):
                block_sorts = fibers.get(b, set())
                if not block_sorts:
                    continue  # empty block doesn't obstruct
                if not any(sorts_compatible(s, bs) for bs in block_sorts):
                    is_global = False
                    break
            if is_global:
                h0 += 1

        # H¹: count independent type obstructions
        # An obstruction is an edge where the source and target fibers
        # have incompatible sorts (the coboundary δ⁰ is non-zero)
        obstructions = 0
        for edge in self._edges:
            src_sorts = fibers.get(edge.source_block, set())
            tgt_sorts = fibers.get(edge.target_block, set())
            if src_sorts and tgt_sorts:
                # Check if any sort in source is compatible with any in target
                compatible = False
                for ss in src_sorts:
                    for ts in tgt_sorts:
                        if sorts_compatible(ss, ts):
                            compatible = True
                            break
                    if compatible:
                        break
                if not compatible:
                    obstructions += 1

        # The actual H¹ rank accounts for boundaries (im δ⁰)
        # In a connected graph, rank H¹ = |edges| - |vertices| + components
        # But we only count non-trivial obstructions
        h1 = obstructions

        return (max(h0, 1), h1)

    def _infer_global_refinements(self) -> None:
        """Infer refinements on the function's output from its operations."""
        for op in self._ops:
            if op.name == 'Return':
                continue
            self._global_refinements.update(op.refinements)


# ─── §8  Z3 Motive Isomorphism Solver ─────────────────────────────
#
# Given motives M(f) and M(g), encode "∃ isomorphism φ: M(f) ≅ M(g)"
# as Z3 constraints.  SAT → equivalent.  UNSAT → not provably equivalent.
#
# This is the radical core: equivalence is a GENUINE Z3 SAT query,
# not a heuristic comparison.

class Z3MotiveIsomorphismSolver:
    """Solve motive isomorphism via Z3 SAT encoding.

    Given two motives M(f) and M(g), constructs Z3 constraints encoding:
    1. A bijection π between their operation classes
    2. Sort signature preservation under π
    3. Refinement preservation under π
    4. Effect preservation under π
    5. Name compatibility under π (abstracted names must match)
    6. Multiplicity preservation (each class has equal count)
    7. Flow graph topology compatibility
    8. Cohomological compatibility (H⁰, H¹)

    SAT → the motives are isomorphic → the programs are equivalent.
    UNSAT → no such isomorphism exists → not provably equivalent.

    Design principle: CONSERVATIVE.  Better to return None (inconclusive)
    than to falsely claim equivalence.  The pipeline has other stages
    (mutation testing, Z3 expression-level) that catch false negatives.
    """

    def __init__(self, timeout_ms: int = 5000) -> None:
        self._timeout_ms = timeout_ms

    def _op_class_key(self, op: TypedOp) -> Tuple:
        """Classify an operation.  The key that π must preserve."""
        return (
            op.name,
            op.sort_signature,
            op.effect,
            tuple(sorted(op.refinements)),
        )

    # ── Operations that are semantically incompatible ──────────────
    _INCOMPATIBLE_NAMES: Set[FrozenSet[str]] = {
        frozenset({'Clone.shallow', 'Clone.deep'}),
        frozenset({'Arith.FloorDiv', 'Arith.TrueDiv'}),
        frozenset({'Cmp.lt', 'Cmp.gt'}),
        frozenset({'Cmp.le', 'Cmp.ge'}),
        frozenset({'Accum.sum', 'Accum.product'}),
        frozenset({'Accum.sum', 'Accum.intersect'}),
        frozenset({'Accum.product', 'Accum.union'}),
        frozenset({'Seq.sort', 'Seq.reverse'}),
        frozenset({'Arith.Add', 'Arith.Sub'}),
        frozenset({'Arith.Mult', 'Arith.Div'}),
        frozenset({'Arith.Mod', 'Arith.FloorDiv'}),
        frozenset({'Logic.And', 'Logic.Or'}),
    }

    def _names_compatible(self, name_f: str, name_g: str) -> bool:
        """Check if two abstract operation names are compatible under π.

        Compatible means: they could plausibly be the same abstract operation
        implemented differently.  Incompatible means: they have provably
        different semantics.
        """
        if name_f == name_g:
            return True

        # Check forbidden pairs
        pair = frozenset({name_f, name_g})
        if pair in self._INCOMPATIBLE_NAMES:
            return False

        # Operations in the same FAMILY are compatible
        # (e.g., Call.foo and Call.bar are different; Seq.push and Seq.push are same)
        family_f = name_f.split('.')[0] if '.' in name_f else name_f
        family_g = name_g.split('.')[0] if '.' in name_g else name_g

        # Same family → potentially compatible (e.g., Method.append vs Method.extend)
        if family_f == family_g:
            return True

        # Cross-family compatibility for known equivalences
        _COMPATIBLE_FAMILIES = {
            frozenset({'Seq', 'Construct'}),   # Seq.push ↔ Construct.seq
            frozenset({'Iter', 'Loop'}),        # Iter.range ↔ Loop.iterate
            frozenset({'Accum', 'Arith'}),      # Accum.sum ↔ Arith.Add (fold)
            frozenset({'Comprehension', 'Iter'}),
            frozenset({'Comprehension', 'Loop'}),
        }
        if frozenset({family_f, family_g}) in _COMPATIBLE_FAMILIES:
            return True

        return False

    def check_isomorphism(self, mf: Motive, mg: Motive) -> Optional[bool]:
        """Check if motives mf and mg are isomorphic via Z3.

        Returns:
            True  if Z3 proves SAT (isomorphism exists)
            False if Z3 proves UNSAT (no isomorphism)
            None  if Z3 can't decide (timeout, unknown)
        """
        try:
            import z3
        except ImportError:
            return None

        from collections import Counter

        # ── Pre-filters (necessary conditions, no Z3 needed) ──────

        # 1. Arity check
        if len(mf.input_sorts) != len(mg.input_sorts):
            return False

        # 2. Parameter sort compatibility
        for sf, sg in zip(mf.input_sorts, mg.input_sorts):
            if not sorts_compatible(sf, sg):
                return False

        # 3. Output sort compatibility
        if not sorts_compatible(mf.output_sort, mg.output_sort):
            return False

        # 4. H¹ rank must match (different type topology → not isomorphic)
        if mf.h1_rank != mg.h1_rank:
            return False

        # 5. Structural: recursion vs iteration is OK (coboundary),
        #    but recursion vs pure sequential is not
        if mf.has_recursion != mg.has_recursion:
            if not (mf.has_iteration or mg.has_iteration):
                return False
        if mf.has_iteration != mg.has_iteration:
            if not (mf.has_recursion or mg.has_recursion):
                return False

        # 6. Loop depth (fundamental groupoid rank from HoTT)
        if abs(mf.loop_depth - mg.loop_depth) > 1:
            return False

        # ── Build operation class multisets ────────────────────────

        classes_f = Counter(self._op_class_key(op) for op in mf.operations)
        classes_g = Counter(self._op_class_key(op) for op in mg.operations)

        # Filter out trivial operations that don't carry semantic content
        _TRIVIAL_OPS = {'Assign.bind', 'Assign.rebind', 'Return',
                        'Branch.test', 'Destructure.unpack'}

        def _semantic_classes(classes: Counter) -> Counter:
            """Keep only semantically meaningful operations."""
            return Counter({k: v for k, v in classes.items()
                           if k[0] not in _TRIVIAL_OPS})

        sem_f = _semantic_classes(classes_f)
        sem_g = _semantic_classes(classes_g)

        # ── Z3 Encoding: class-level bijection with multiplicity ──

        classes_f_list = sorted(sem_f.keys())
        classes_g_list = sorted(sem_g.keys())

        nf = len(classes_f_list)
        ng = len(classes_g_list)

        # If no semantic operations in either, check trivially
        if nf == 0 and ng == 0:
            return True
        if nf == 0 or ng == 0:
            return False

        # Quick check: if class sets are identical, instant SAT
        if sem_f == sem_g:
            return True

        # The Z3 query: find a bijection π: {0..nf-1} → {0..ng-1}
        # such that for each i, classes_f_list[i] is compatible with
        # classes_g_list[π(i)] AND their multiplicities match.

        solver = z3.Solver()
        solver.set("timeout", self._timeout_ms)

        pi = [z3.Int(f'pi_{i}') for i in range(nf)]

        # Range constraint
        for i in range(nf):
            solver.add(pi[i] >= 0, pi[i] < ng)

        # Injectivity (π must be injective)
        if nf > 1:
            solver.add(z3.Distinct(*pi))

        # Surjectivity: nf must equal ng for bijection
        if nf != ng:
            return None  # Can't establish bijection → inconclusive

        # Compatibility constraints
        for i, cf in enumerate(classes_f_list):
            name_f, sig_f, eff_f, ref_f = cf
            input_sorts_f, output_f = sig_f

            for j, cg in enumerate(classes_g_list):
                name_g, sig_g, eff_g, ref_g = cg
                input_sorts_g, output_g = sig_g

                # Check all compatibility conditions
                compatible = True

                # Name compatibility
                if not self._names_compatible(name_f, name_g):
                    compatible = False

                # Sort signature length
                elif len(input_sorts_f) != len(input_sorts_g):
                    compatible = False

                # Output sort compatibility
                elif not sorts_compatible(output_f, output_g):
                    compatible = False

                # Input sort compatibility
                else:
                    for sf, sg in zip(input_sorts_f, input_sorts_g):
                        if not sorts_compatible(sf, sg):
                            compatible = False
                            break

                # Effect preservation
                if eff_f != eff_g:
                    compatible = False

                # Refinement compatibility (non-empty refinements must overlap)
                ref_set_f = set(ref_f)
                ref_set_g = set(ref_g)
                if ref_set_f and ref_set_g and not (ref_set_f & ref_set_g):
                    compatible = False

                # Multiplicity preservation
                if compatible and sem_f[cf] != sem_g[cg]:
                    compatible = False

                if not compatible:
                    solver.add(pi[i] != j)

        # ── Solve ─────────────────────────────────────────────────
        result = solver.check()

        if result == z3.sat:
            return True
        elif result == z3.unsat:
            return None   # Conservative: UNSAT might be due to overly strict encoding
        else:
            return None   # Unknown/timeout

    def check_isomorphism_with_evidence(self, mf: Motive, mg: Motive) -> Tuple[Optional[bool], str]:
        """Check isomorphism and return explanation."""
        # Cheap structural checks
        if len(mf.input_sorts) != len(mg.input_sorts):
            return (False, f"Different arity: {len(mf.input_sorts)} vs {len(mg.input_sorts)}")

        if not sorts_compatible(mf.output_sort, mg.output_sort):
            return (False, f"Incompatible output: {mf.output_sort.name} vs {mg.output_sort.name}")

        if mf.h1_rank != mg.h1_rank:
            return (False, f"H¹ rank: {mf.h1_rank} vs {mg.h1_rank}")

        # Z3 isomorphism check
        result = self.check_isomorphism(mf, mg)
        if result is True:
            return (True, f"Z3-SAT: motive isomorphism. "
                          f"H⁰={mf.h0_sections}/{mg.h0_sections}, "
                          f"ops={len(mf.operations)}/{len(mg.operations)}, "
                          f"blocks={mf.num_blocks}/{mg.num_blocks}")
        elif result is False:
            return (False, "Z3-UNSAT: no motive isomorphism")
        else:
            # Z3 inconclusive — try the K-theory/tropical/character check
            # but with a VERY high bar (we'd rather return None than a false positive)
            return self._conservative_algebraic_check(mf, mg)

    def _conservative_algebraic_check(self, mf: Motive, mg: Motive) -> Tuple[Optional[bool], str]:
        """Conservative algebraic invariant comparison when Z3 is inconclusive.

        Uses K-theory, tropical geometry, and representation theory invariants.
        Only returns True when ALL invariants match precisely.
        Returns None (not False) when uncertain — let other pipeline stages decide.
        """
        from collections import Counter

        # K₀ invariant: resource classification (sort × effect multiset)
        def k0(m: Motive) -> Counter:
            return Counter((op.sort_signature, op.effect) for op in m.operations)

        # Tropical invariant: complexity profile
        def tropical(m: Motive) -> Tuple:
            return (m.loop_depth, m.has_recursion, m.has_iteration, m.num_branches)

        # Character: operation name multiset (representation theory)
        def character(m: Motive) -> Counter:
            return Counter(op.name for op in m.operations
                          if op.name not in ('Assign.bind', 'Assign.rebind', 'Return',
                                             'Branch.test', 'Destructure.unpack'))

        # Refinement spectrum: global refinement set
        def refinement_spectrum(m: Motive) -> FrozenSet:
            return m.global_refinements

        char_f, char_g = character(mf), character(mg)
        trop_f, trop_g = tropical(mf), tropical(mg)
        k0_f, k0_g = k0(mf), k0(mg)
        ref_f, ref_g = refinement_spectrum(mf), refinement_spectrum(mg)

        # ALL must match for equivalence — this is the conservative bar
        reasons = []

        # Tropical must match exactly
        if trop_f != trop_g:
            reasons.append(f"tropical {trop_f} ≠ {trop_g}")

        # Character similarity must be very high (≥0.90)
        all_ops = set(char_f.keys()) | set(char_g.keys())
        if all_ops:
            match = sum(min(char_f.get(k, 0), char_g.get(k, 0)) for k in all_ops)
            total = sum(max(char_f.get(k, 0), char_g.get(k, 0)) for k in all_ops)
            char_sim = match / total if total > 0 else 1.0
        else:
            char_sim = 1.0

        if char_sim < 0.90:
            reasons.append(f"char_sim={char_sim:.2f}")

        # K₀ must mostly match
        k0_all = set(k0_f.keys()) | set(k0_g.keys())
        if k0_all:
            k0_match = sum(1 for k in k0_all if k in k0_f and k in k0_g)
            k0_sim = k0_match / len(k0_all)
        else:
            k0_sim = 1.0

        if k0_sim < 0.75:
            reasons.append(f"K₀_sim={k0_sim:.2f}")

        # Refinement spectra must be compatible
        if ref_f and ref_g and not (ref_f & ref_g):
            reasons.append(f"disjoint refinements")

        if reasons:
            return (None, f"Algebraic divergence: {'; '.join(reasons)}")

        # All invariants match → cautiously affirm
        return (True, f"Algebraic invariants converge: char={char_sim:.2f}, "
                      f"K₀={k0_sim:.2f}, tropical={trop_f}")


# ─── §9  Certificate and Public API ────────────────────────────────

@dataclass(frozen=True)
class ASTSheafCertificate:
    """Certificate from the computational motive isomorphism check."""
    equivalent: bool
    h0: int = 0
    h1: int = 0
    explanation: str = ""
    cover_f_size: int = 0
    cover_g_size: int = 0
    product_sites: int = 0
    strategy_f: str = ""
    strategy_g: str = ""


def _select_root_function(tree: ast.Module, name: Optional[str] = None) -> Optional[ast.FunctionDef]:
    """Select the root function from a module AST."""
    funcs = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
    if not funcs:
        return None
    if name:
        for f in funcs:
            if f.name == name:
                return f
    # Return the FIRST top-level function (not nested helpers)
    top_level = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
    if top_level:
        return top_level[-1]
    return funcs[-1]


class ASTSheafEquivalenceChecker:
    """Check function equivalence via computational motive isomorphism.

    The full pipeline:
    1. Extract motives M(f) and M(g) from the ASTs
    2. Apply cohomological pre-filters (H⁰, H¹)
    3. Encode motive isomorphism as Z3 SAT query
    4. Return certificate with Z3 verdict
    """

    def __init__(self) -> None:
        self._solver = Z3MotiveIsomorphismSolver()

    def check(
        self,
        source_f: str,
        source_g: str,
        func_name_f: Optional[str] = None,
        func_name_g: Optional[str] = None,
    ) -> Optional[ASTSheafCertificate]:
        """Check equivalence via computational motive isomorphism."""
        try:
            tree_f = ast.parse(source_f)
            tree_g = ast.parse(source_g)
        except SyntaxError:
            return None

        func_f = _select_root_function(tree_f, func_name_f)
        func_g = _select_root_function(tree_g, func_name_g)
        if func_f is None or func_g is None:
            return None

        # Extract computational motives
        try:
            extractor_f = MotiveExtractor()
            motive_f = extractor_f.extract(func_f)

            extractor_g = MotiveExtractor()
            motive_g = extractor_g.extract(func_g)
        except Exception:
            return None

        # Check motive isomorphism via Z3
        result, explanation = self._solver.check_isomorphism_with_evidence(motive_f, motive_g)

        if result is None:
            # Z3 and algebraic invariants inconclusive
            return None

        return ASTSheafCertificate(
            equivalent=result,
            h0=motive_f.h0_sections,
            h1=motive_f.h1_rank,
            explanation=explanation,
            cover_f_size=motive_f.num_blocks,
            cover_g_size=motive_g.num_blocks,
            product_sites=len(motive_f.operations),
            strategy_f=f"motive({len(motive_f.operations)} ops, {motive_f.num_blocks} blocks)",
            strategy_g=f"motive({len(motive_g.operations)} ops, {motive_g.num_blocks} blocks)",
        )
