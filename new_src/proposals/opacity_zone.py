"""Opacity Zone — classification, analysis, reduction, and pipeline routing.

Implements the full opacity framework from the CCTT monograph chapter
"The Uninterpreted Opacity Zone".  Every Python builtin compiled to
Z3 falls into one of three interpretation levels; this module
classifies terms, finds opacity boundaries, estimates completeness,
applies reduction strategies, and routes pairs through the pipeline.
"""
from __future__ import annotations

import ast
import math
import textwrap
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any, Callable, Dict, FrozenSet, List, Optional, Set, Sequence, Tuple,
)

try:
    import z3 as _z3
    from z3 import (
        And, BoolSort, BoolVal, Const, ForAll, Function,
        Int, IntSort, IntVal, Not, Or, Solver, sat, unsat,
    )
    _HAS_Z3 = True
except ImportError:
    _z3 = None  # type: ignore
    _HAS_Z3 = False


class OpacityLevel(Enum):
    FULLY_INTERPRETED = 1
    PARTIALLY_INTERPRETED = 2
    UNINTERPRETED = 3

    def __lt__(self, other: OpacityLevel) -> bool:
        if not isinstance(other, OpacityLevel):
            return NotImplemented
        return self.value < other.value

    def __le__(self, other: OpacityLevel) -> bool:
        if not isinstance(other, OpacityLevel):
            return NotImplemented
        return self.value <= other.value

    def __gt__(self, other: OpacityLevel) -> bool:
        if not isinstance(other, OpacityLevel):
            return NotImplemented
        return self.value > other.value

    def __ge__(self, other: OpacityLevel) -> bool:
        if not isinstance(other, OpacityLevel):
            return NotImplemented
        return self.value >= other.value

    @staticmethod
    def meet(a: OpacityLevel, b: OpacityLevel) -> OpacityLevel:
        return OpacityLevel(min(a.value, b.value))

    @staticmethod
    def join(a: OpacityLevel, b: OpacityLevel) -> OpacityLevel:
        return OpacityLevel(max(a.value, b.value))


FULLY_INTERPRETED_OPS: FrozenSet[str] = frozenset({
    'Add', 'Sub', 'Mult', 'FloorDiv', 'Mod', 'Pow',
    'LShift', 'RShift', 'BitOr', 'BitAnd', 'BitXor',
    'Lt', 'LtE', 'Gt', 'GtE', 'Eq', 'NotEq',
    'And', 'Or', 'Not',
    'Concat', 'Length',
    'IntVal', 'BoolVal', 'StringVal',
})

PARTIALLY_INTERPRETED_OPS: FrozenSet[str] = frozenset({
    'binop', 'unop', 'truthy', 'fold', 'tag',
    'mklist', 'mkint', 'mkbool', 'mkstr', 'mknone', 'mkref',
    'GETITEM',
})

AXIOMATISED_UNINTERPRETED_OPS: FrozenSet[str] = frozenset({
    'sorted', 'reversed', 'list', 'tuple', 'set', 'frozenset',
    'len', 'sum', 'mut_sort', 'mut_reverse',
})

BARE_UNINTERPRETED_OPS: FrozenSet[str] = frozenset({
    'dict', 'any', 'all', 'enumerate', 'zip', 'map', 'filter',
    'Counter', 'defaultdict', 'deque', 'type', 'hash', 'id',
    'repr', 'str', 'iter', 'next', 'print', 'input', 'open',
    'ord', 'chr', 'float', 'complex', 'bytes', 'bytearray',
    'memoryview', 'object', 'super', 'property', 'classmethod',
    'staticmethod', 'isinstance', 'issubclass', 'callable',
    'getattr', 'setattr', 'hasattr', 'delattr', 'vars', 'dir',
    'range', 'slice',
})


BUILTIN_OPACITY_CATALOG: Dict[str, OpacityLevel] = {}
for _op in FULLY_INTERPRETED_OPS:
    BUILTIN_OPACITY_CATALOG[_op] = OpacityLevel.FULLY_INTERPRETED
for _op in PARTIALLY_INTERPRETED_OPS:
    BUILTIN_OPACITY_CATALOG[_op] = OpacityLevel.PARTIALLY_INTERPRETED
for _op in AXIOMATISED_UNINTERPRETED_OPS:
    BUILTIN_OPACITY_CATALOG[_op] = OpacityLevel.UNINTERPRETED
for _op in BARE_UNINTERPRETED_OPS:
    BUILTIN_OPACITY_CATALOG[_op] = OpacityLevel.UNINTERPRETED


AXIOM_REGISTRY: Dict[str, List[str]] = {
    'sorted': [
        'S4_idempotent',
        'S9_absorbs_reversed',
        'sorted_absorbs_list',
        'sorted_absorbs_tuple',
    ],
    'reversed': ['S7_involution'],
    'list': ['I_idempotent'],
    'tuple': ['I_idempotent'],
    'set': [
        'I_idempotent',
        'set_absorbs_sorted',
        'set_absorbs_reversed',
        'set_absorbs_list',
        'set_absorbs_tuple',
    ],
    'frozenset': ['I_idempotent'],
    'len': [
        'len_preserved_by_sorted',
        'len_preserved_by_reversed',
        'len_preserved_by_list',
        'len_preserved_by_tuple',
    ],
    'sum': ['sum_permutation_invariant'],
    'mut_sort': ['mut_sort_eq_sorted'],
    'mut_reverse': ['mut_reverse_eq_reversed'],
}


Z3_THEORY_MAP: Dict[str, str] = {
    'Add': 'QF_LIA', 'Sub': 'QF_LIA', 'Mult': 'QF_LIA',
    'FloorDiv': 'QF_LIA', 'Mod': 'QF_LIA', 'Pow': 'QF_NIA',
    'Lt': 'QF_LIA', 'LtE': 'QF_LIA', 'Gt': 'QF_LIA',
    'GtE': 'QF_LIA', 'Eq': 'QF_UF', 'NotEq': 'QF_UF',
    'And': 'QF_BOOL', 'Or': 'QF_BOOL', 'Not': 'QF_BOOL',
    'Concat': 'QF_S', 'Length': 'QF_S',
    'LShift': 'QF_BV', 'RShift': 'QF_BV',
    'BitOr': 'QF_BV', 'BitAnd': 'QF_BV', 'BitXor': 'QF_BV',
    'binop': 'QF_DT+LIA', 'unop': 'QF_DT+LIA',
    'truthy': 'QF_DT', 'fold': 'QF_DT+LIA', 'tag': 'QF_DT',
}


ABSORPTION_RULES: Dict[Tuple[str, str], str] = {
    ('sorted', 'list'): 'sorted',
    ('sorted', 'tuple'): 'sorted',
    ('sorted', 'reversed'): 'sorted',
    ('sorted', 'sorted'): 'sorted',
    ('reversed', 'reversed'): '',
    ('list', 'list'): 'list',
    ('tuple', 'tuple'): 'tuple',
    ('set', 'set'): 'set',
    ('set', 'sorted'): 'set',
    ('set', 'reversed'): 'set',
    ('set', 'list'): 'set',
    ('set', 'tuple'): 'set',
    ('frozenset', 'frozenset'): 'frozenset',
}


@dataclass
class NodeOpacity:
    node_id: int
    node_repr: str
    level: OpacityLevel
    symbol_name: str
    children: List[NodeOpacity] = field(default_factory=list)


@dataclass
class OpacityReport:
    term_repr: str
    overall_level: OpacityLevel
    node_classifications: List[NodeOpacity]
    opacity_score: float
    opacity_depth: int
    max_opaque_chain: int
    blind_spots: List[str]
    total_nodes: int
    uninterpreted_nodes: int
    partially_interpreted_nodes: int
    fully_interpreted_nodes: int

    @property
    def completeness_estimate(self) -> float:
        return (1.0 - self.opacity_score) ** 2

    def summary(self) -> str:
        lines = [
            f'Term: {self.term_repr}',
            f'Overall opacity: {self.overall_level.name}',
            f'Score: {self.opacity_score:.3f}',
            f'Depth: {self.opacity_depth}',
            f'Max opaque chain: {self.max_opaque_chain}',
            f'Nodes: {self.total_nodes} '
            f'(F={self.fully_interpreted_nodes} '
            f'P={self.partially_interpreted_nodes} '
            f'U={self.uninterpreted_nodes})',
            f'Blind spots: {len(self.blind_spots)}',
            f'Z3 success estimate: {self.completeness_estimate:.3f}',
        ]
        return '\n'.join(lines)


def _classify_symbol(name: str) -> OpacityLevel:
    if name in BUILTIN_OPACITY_CATALOG:
        return BUILTIN_OPACITY_CATALOG[name]
    if name.startswith('py_'):
        return OpacityLevel.UNINTERPRETED
    if name.startswith('rec_') or name.startswith('fold_'):
        return OpacityLevel.PARTIALLY_INTERPRETED
    if name.startswith('binop_') or name.startswith('unop_'):
        return OpacityLevel.PARTIALLY_INTERPRETED
    if name.startswith('truthy_') or name.startswith('tag_'):
        return OpacityLevel.PARTIALLY_INTERPRETED
    return OpacityLevel.UNINTERPRETED


class OpacityClassifier:
    _next_id: int = 0

    @classmethod
    def _alloc_id(cls) -> int:
        cls._next_id += 1
        return cls._next_id

    @classmethod
    def classify_op(cls, name: str) -> OpacityLevel:
        return _classify_symbol(name)

    @classmethod
    def classify_z3_term(cls, term: Any) -> OpacityReport:
        if not _HAS_Z3:
            return cls._empty_report(str(term))
        root_node, counters = cls._walk_z3(term)
        overall = cls._compute_overall([root_node])
        score = (counters['U'] / counters['total']) if counters['total'] > 0 else 0.0
        depth = cls._compute_depth(root_node)
        chain = cls._max_chain(root_node)
        blind = cls._find_blind_spots(root_node)
        return OpacityReport(
            term_repr=str(term),
            overall_level=overall,
            node_classifications=[root_node],
            opacity_score=score,
            opacity_depth=depth,
            max_opaque_chain=chain,
            blind_spots=blind,
            total_nodes=counters['total'],
            uninterpreted_nodes=counters['U'],
            partially_interpreted_nodes=counters['P'],
            fully_interpreted_nodes=counters['F'],
        )

    @classmethod
    def classify_ast(cls, node: ast.AST) -> OpacityReport:
        root_node, counters = cls._walk_ast(node)
        overall = cls._compute_overall([root_node])
        score = (counters['U'] / counters['total']) if counters['total'] > 0 else 0.0
        depth = cls._compute_depth(root_node)
        chain = cls._max_chain(root_node)
        blind = cls._find_blind_spots(root_node)
        return OpacityReport(
            term_repr=ast.dump(node),
            overall_level=overall,
            node_classifications=[root_node],
            opacity_score=score,
            opacity_depth=depth,
            max_opaque_chain=chain,
            blind_spots=blind,
            total_nodes=counters['total'],
            uninterpreted_nodes=counters['U'],
            partially_interpreted_nodes=counters['P'],
            fully_interpreted_nodes=counters['F'],
        )

    @classmethod
    def _walk_z3(cls, term: Any) -> Tuple[NodeOpacity, Dict[str, int]]:
        counters: Dict[str, int] = {'F': 0, 'P': 0, 'U': 0, 'total': 0}
        root = cls._z3_node(term, counters)
        return root, counters

    @classmethod
    def _z3_node(cls, term: Any, counters: Dict[str, int]) -> NodeOpacity:
        counters['total'] += 1
        nid = cls._alloc_id()
        decl = term.decl() if hasattr(term, 'decl') else None
        name = decl.name() if decl is not None else str(term)
        level = _classify_symbol(name)
        children: List[NodeOpacity] = []
        if hasattr(term, 'num_args'):
            for i in range(term.num_args()):
                child = cls._z3_node(term.arg(i), counters)
                children.append(child)
                level = OpacityLevel.join(level, child.level)
        if level == OpacityLevel.FULLY_INTERPRETED:
            counters['F'] += 1
        elif level == OpacityLevel.PARTIALLY_INTERPRETED:
            counters['P'] += 1
        else:
            counters['U'] += 1
        return NodeOpacity(nid, str(term), level, name, children)

    @classmethod
    def _walk_ast(cls, node: ast.AST) -> Tuple[NodeOpacity, Dict[str, int]]:
        counters: Dict[str, int] = {'F': 0, 'P': 0, 'U': 0, 'total': 0}
        root = cls._ast_node(node, counters)
        return root, counters

    @classmethod
    def _ast_node(cls, node: ast.AST, counters: Dict[str, int]) -> NodeOpacity:
        counters['total'] += 1
        nid = cls._alloc_id()
        name = type(node).__name__
        level = OpacityLevel.FULLY_INTERPRETED

        if isinstance(node, ast.Call):
            fname = cls._extract_call_name(node)
            level = _classify_symbol(fname) if fname else OpacityLevel.UNINTERPRETED
            name = fname or name

        if isinstance(node, ast.BinOp):
            name = type(node.op).__name__
            level = _classify_symbol(name)

        if isinstance(node, ast.UnaryOp):
            name = type(node.op).__name__
            if name == 'USub':
                name = 'Sub'
            elif name == 'UAdd':
                name = 'Add'
            level = _classify_symbol(name)

        if isinstance(node, ast.Compare):
            for op in node.ops:
                op_name = type(op).__name__
                level = OpacityLevel.join(level, _classify_symbol(op_name))

        children: List[NodeOpacity] = []
        for child_node in ast.iter_child_nodes(node):
            child = cls._ast_node(child_node, counters)
            children.append(child)
            level = OpacityLevel.join(level, child.level)

        if level == OpacityLevel.FULLY_INTERPRETED:
            counters['F'] += 1
        elif level == OpacityLevel.PARTIALLY_INTERPRETED:
            counters['P'] += 1
        else:
            counters['U'] += 1
        return NodeOpacity(nid, ast.dump(node), level, name, children)

    @staticmethod
    def _extract_call_name(node: ast.Call) -> Optional[str]:
        if isinstance(node.func, ast.Name):
            return node.func.id
        if isinstance(node.func, ast.Attribute):
            if isinstance(node.func.value, ast.Name):
                return f'{node.func.value.id}.{node.func.attr}'
            return node.func.attr
        return None

    @classmethod
    def _compute_overall(cls, nodes: List[NodeOpacity]) -> OpacityLevel:
        level = OpacityLevel.FULLY_INTERPRETED
        for n in nodes:
            level = OpacityLevel.join(level, n.level)
        return level

    @classmethod
    def _compute_depth(cls, node: NodeOpacity) -> int:
        if not node.children:
            return 1 if node.level == OpacityLevel.UNINTERPRETED else 0
        child_depths = [cls._compute_depth(c) for c in node.children]
        mx = max(child_depths) if child_depths else 0
        if node.level == OpacityLevel.UNINTERPRETED:
            return 1 + mx
        return mx

    @classmethod
    def _max_chain(cls, node: NodeOpacity) -> int:
        if not node.children:
            return 1 if node.level == OpacityLevel.UNINTERPRETED else 0
        child_chains = [cls._max_chain(c) for c in node.children]
        mx = max(child_chains) if child_chains else 0
        if node.level == OpacityLevel.UNINTERPRETED and mx > 0:
            return 1 + mx
        if node.level == OpacityLevel.UNINTERPRETED:
            return 1
        return mx

    @classmethod
    def _find_blind_spots(cls, node: NodeOpacity) -> List[str]:
        spots: List[str] = []
        cls._blind_walk(node, OpacityLevel.FULLY_INTERPRETED, spots)
        return spots

    @classmethod
    def _blind_walk(
        cls,
        node: NodeOpacity,
        parent_level: OpacityLevel,
        spots: List[str],
    ) -> None:
        if (node.level == OpacityLevel.UNINTERPRETED
                and parent_level < OpacityLevel.UNINTERPRETED):
            spots.append(node.symbol_name)
        for c in node.children:
            cls._blind_walk(c, node.level, spots)

    @classmethod
    def _empty_report(cls, repr_str: str) -> OpacityReport:
        return OpacityReport(
            term_repr=repr_str,
            overall_level=OpacityLevel.FULLY_INTERPRETED,
            node_classifications=[],
            opacity_score=0.0,
            opacity_depth=0,
            max_opaque_chain=0,
            blind_spots=[],
            total_nodes=0,
            uninterpreted_nodes=0,
            partially_interpreted_nodes=0,
            fully_interpreted_nodes=0,
        )


@dataclass
class BoundaryNode:
    node_repr: str
    symbol_name: str
    level: OpacityLevel
    child_levels: List[OpacityLevel]

    @property
    def is_boundary(self) -> bool:
        return (self.level == OpacityLevel.UNINTERPRETED
                and any(c < OpacityLevel.UNINTERPRETED for c in self.child_levels))


class OpacityBoundaryFinder:
    @classmethod
    def find_boundaries(cls, report: OpacityReport) -> List[BoundaryNode]:
        boundaries: List[BoundaryNode] = []
        for root in report.node_classifications:
            cls._walk(root, boundaries)
        return boundaries

    @classmethod
    def _walk(cls, node: NodeOpacity, acc: List[BoundaryNode]) -> None:
        if node.level == OpacityLevel.UNINTERPRETED:
            child_levels = [c.level for c in node.children]
            if any(cl < OpacityLevel.UNINTERPRETED for cl in child_levels):
                acc.append(BoundaryNode(
                    node_repr=node.node_repr,
                    symbol_name=node.symbol_name,
                    level=node.level,
                    child_levels=child_levels,
                ))
        for c in node.children:
            cls._walk(c, acc)

    @classmethod
    def find_in_z3_term(cls, term: Any) -> List[BoundaryNode]:
        report = OpacityClassifier.classify_z3_term(term)
        return cls.find_boundaries(report)

    @classmethod
    def find_in_ast(cls, node: ast.AST) -> List[BoundaryNode]:
        report = OpacityClassifier.classify_ast(node)
        return cls.find_boundaries(report)


class CompletenessEstimator:
    @staticmethod
    def estimate_from_score(score: float) -> float:
        return max(0.0, (1.0 - score) ** 2)

    @staticmethod
    def estimate_from_levels(
        level_f: OpacityLevel,
        level_g: OpacityLevel,
    ) -> float:
        combined = OpacityLevel.join(level_f, level_g)
        if combined == OpacityLevel.FULLY_INTERPRETED:
            return 1.0
        if combined == OpacityLevel.PARTIALLY_INTERPRETED:
            return 0.7
        return 0.15

    @staticmethod
    def estimate_from_reports(
        report_f: OpacityReport,
        report_g: OpacityReport,
    ) -> float:
        combined_score = max(report_f.opacity_score, report_g.opacity_score)
        base = (1.0 - combined_score) ** 2
        axiom_bonus = 0.0
        for spot in report_f.blind_spots + report_g.blind_spots:
            if spot in AXIOM_REGISTRY:
                axiom_bonus += 0.05 * len(AXIOM_REGISTRY[spot])
        return min(1.0, base + axiom_bonus)

    @staticmethod
    def estimate_pair(
        term_f: Any,
        term_g: Any,
    ) -> float:
        if not _HAS_Z3:
            return 0.0
        rf = OpacityClassifier.classify_z3_term(term_f)
        rg = OpacityClassifier.classify_z3_term(term_g)
        return CompletenessEstimator.estimate_from_reports(rf, rg)


@dataclass
class ReductionResult:
    strategy: str
    success: bool
    original: str
    reduced: str
    detail: str = ''


class OpacityReducer:
    @staticmethod
    def try_ground_eval(
        term: Any,
        eval_fn: Optional[Callable] = None,
    ) -> ReductionResult:
        original = str(term) if term is not None else '(none)'
        if not _HAS_Z3 or term is None:
            return ReductionResult('ground_eval', False, original, original)
        if not hasattr(term, 'num_args'):
            return ReductionResult('ground_eval', False, original, original)
        has_vars = _term_has_variables(term)
        if has_vars:
            return ReductionResult(
                'ground_eval', False, original, original,
                'term contains free variables',
            )
        if eval_fn is not None:
            try:
                result = eval_fn(term)
                return ReductionResult(
                    'ground_eval', True, original, str(result),
                    'evaluated via provided function',
                )
            except Exception as exc:
                return ReductionResult(
                    'ground_eval', False, original, original,
                    f'eval_fn raised: {exc}',
                )
        s = Solver()
        s.set('timeout', 2000)
        v = Const('_ge_v', term.sort())
        s.add(v == term)
        if s.check() == sat:
            val = s.model().eval(v, model_completion=True)
            return ReductionResult(
                'ground_eval', True, original, str(val),
                'evaluated via Z3 model',
            )
        return ReductionResult('ground_eval', False, original, original)

    @staticmethod
    def try_spec_match(
        fn_names: Sequence[str],
        specs: Optional[Dict[Tuple[str, ...], List[str]]] = None,
    ) -> ReductionResult:
        original = ' -> '.join(fn_names)
        if specs is None:
            specs = _DEFAULT_SPECS
        key = tuple(fn_names)
        if key in specs:
            reduced = ' -> '.join(specs[key])
            return ReductionResult(
                'spec_match', True, original, reduced,
                f'matched spec: {key} -> {specs[key]}',
            )
        for i in range(len(fn_names)):
            for j in range(i + 2, len(fn_names) + 1):
                sub = tuple(fn_names[i:j])
                if sub in specs:
                    new_names = list(fn_names[:i]) + specs[sub] + list(fn_names[j:])
                    return ReductionResult(
                        'spec_match', True, original,
                        ' -> '.join(new_names),
                        f'matched sub-spec at [{i}:{j}]: {sub} -> {specs[sub]}',
                    )
        return ReductionResult('spec_match', False, original, original)

    @staticmethod
    def try_axiomatize(
        fn_names: Sequence[str],
        T: Any = None,
    ) -> ReductionResult:
        original = ' -> '.join(fn_names)
        reduced_list = list(fn_names)
        changed = True
        while changed:
            changed = False
            new: List[str] = []
            i = 0
            while i < len(reduced_list):
                if i + 1 < len(reduced_list):
                    pair = (reduced_list[i + 1], reduced_list[i])
                    if pair in ABSORPTION_RULES:
                        replacement = ABSORPTION_RULES[pair]
                        if replacement:
                            new.append(replacement)
                        i += 2
                        changed = True
                        continue
                new.append(reduced_list[i])
                i += 1
            reduced_list = new
        if reduced_list != list(fn_names):
            return ReductionResult(
                'axiomatize', True, original,
                ' -> '.join(reduced_list),
                'applied absorption rules',
            )
        return ReductionResult('axiomatize', False, original, original)

    @staticmethod
    def try_normalize_away(fn_names: Sequence[str]) -> ReductionResult:
        original = ' -> '.join(fn_names)
        rules: List[Tuple[Tuple[str, ...], Tuple[str, ...]]] = [
            (('sorted', 'list'), ('sorted',)),
            (('sorted', 'tuple'), ('sorted',)),
            (('reversed', 'reversed'), ()),
            (('list', 'list'), ('list',)),
            (('set', 'sorted'), ('set',)),
            (('set', 'reversed'), ('set',)),
            (('set', 'list'), ('set',)),
            (('frozenset', 'frozenset'), ('frozenset',)),
        ]
        names = list(fn_names)
        did_change = False
        changed = True
        while changed:
            changed = False
            for lhs, rhs in rules:
                k = len(lhs)
                for i in range(len(names) - k + 1):
                    if tuple(names[i:i + k]) == lhs:
                        names = names[:i] + list(rhs) + names[i + k:]
                        changed = True
                        did_change = True
                        break
                if changed:
                    break
        if did_change:
            return ReductionResult(
                'normalize', True, original,
                ' -> '.join(names) if names else '(identity)',
                'applied normalisation rules',
            )
        return ReductionResult('normalize', False, original, original)

    @classmethod
    def reduce_all(
        cls,
        fn_names: Sequence[str],
        term: Any = None,
        eval_fn: Optional[Callable] = None,
        T: Any = None,
    ) -> List[ReductionResult]:
        results: List[ReductionResult] = []
        r1 = cls.try_normalize_away(fn_names)
        results.append(r1)
        if r1.success:
            fn_names = r1.reduced.split(' -> ') if r1.reduced != '(identity)' else []
        r2 = cls.try_axiomatize(fn_names, T)
        results.append(r2)
        r3 = cls.try_spec_match(fn_names)
        results.append(r3)
        r4 = cls.try_ground_eval(term, eval_fn)
        results.append(r4)
        return results


_DEFAULT_SPECS: Dict[Tuple[str, ...], List[str]] = {
    ('sorted', 'list', 'set'): ['sorted', 'set'],
    ('list', 'set'): ['list', 'set'],
    ('sorted', 'list'): ['sorted'],
    ('sorted', 'tuple'): ['sorted'],
    ('list', 'reversed'): ['list', 'reversed'],
}


def _term_has_variables(term: Any) -> bool:
    if not _HAS_Z3:
        return True
    if _z3.is_const(term):
        return term.decl().kind() == _z3.Z3_OP_UNINTERPRETED
    if hasattr(term, 'num_args'):
        for i in range(term.num_args()):
            if _term_has_variables(term.arg(i)):
                return True
    return False


class PipelineRoute(Enum):
    Z3_DIRECT = auto()
    Z3_PLUS_PATH = auto()
    PATH_PLUS_SPEC = auto()


@dataclass
class PipelineDecision:
    route: PipelineRoute
    pair_opacity: OpacityLevel
    report_f: Optional[OpacityReport]
    report_g: Optional[OpacityReport]
    completeness_estimate: float
    detail: str = ''


class OpacityAwarePipeline:
    def __init__(
        self,
        z3_timeout_ms: int = 5000,
        path_search_fn: Optional[Callable] = None,
        spec_match_fn: Optional[Callable] = None,
    ):
        self.z3_timeout_ms = z3_timeout_ms
        self.path_search_fn = path_search_fn
        self.spec_match_fn = spec_match_fn

    def decide_route(
        self,
        term_f: Any,
        term_g: Any,
    ) -> PipelineDecision:
        if not _HAS_Z3:
            return PipelineDecision(
                route=PipelineRoute.PATH_PLUS_SPEC,
                pair_opacity=OpacityLevel.UNINTERPRETED,
                report_f=None,
                report_g=None,
                completeness_estimate=0.0,
                detail='Z3 not available',
            )
        rf = OpacityClassifier.classify_z3_term(term_f)
        rg = OpacityClassifier.classify_z3_term(term_g)
        alpha = OpacityLevel.join(rf.overall_level, rg.overall_level)
        est = CompletenessEstimator.estimate_from_reports(rf, rg)
        if alpha == OpacityLevel.FULLY_INTERPRETED:
            route = PipelineRoute.Z3_DIRECT
        elif alpha == OpacityLevel.PARTIALLY_INTERPRETED:
            route = PipelineRoute.Z3_PLUS_PATH
        else:
            route = PipelineRoute.PATH_PLUS_SPEC
        return PipelineDecision(
            route=route,
            pair_opacity=alpha,
            report_f=rf,
            report_g=rg,
            completeness_estimate=est,
            detail=f'opacity={alpha.name} score_f={rf.opacity_score:.2f} score_g={rg.opacity_score:.2f}',
        )

    def execute(
        self,
        term_f: Any,
        term_g: Any,
        axiom_adder: Optional[Callable] = None,
    ) -> Dict[str, Any]:
        decision = self.decide_route(term_f, term_g)
        result: Dict[str, Any] = {
            'decision': decision,
            'equivalent': None,
            'method': None,
            'detail': '',
        }

        if decision.route == PipelineRoute.Z3_DIRECT:
            eq = self._z3_decide(term_f, term_g, axiom_adder)
            result['equivalent'] = eq
            result['method'] = 'z3_direct'
            return result

        if decision.route == PipelineRoute.Z3_PLUS_PATH:
            eq = self._z3_decide(term_f, term_g, axiom_adder)
            if eq is not None:
                result['equivalent'] = eq
                result['method'] = 'z3'
                return result
            if self.path_search_fn is not None:
                eq = self.path_search_fn(term_f, term_g)
                result['equivalent'] = eq
                result['method'] = 'path_search'
                return result
            result['method'] = 'z3_timeout_no_path'
            return result

        cex = self._z3_counterexample(term_f, term_g)
        if cex is not None:
            result['equivalent'] = False
            result['method'] = 'z3_counterexample'
            result['detail'] = str(cex)
            return result
        if self.path_search_fn is not None:
            eq = self.path_search_fn(term_f, term_g)
            if eq is not None:
                result['equivalent'] = eq
                result['method'] = 'path_search'
                return result
        if self.spec_match_fn is not None:
            eq = self.spec_match_fn(term_f, term_g)
            if eq is not None:
                result['equivalent'] = eq
                result['method'] = 'spec_match'
                return result
        result['method'] = 'inconclusive'
        return result

    def _z3_decide(
        self,
        term_f: Any,
        term_g: Any,
        axiom_adder: Optional[Callable] = None,
    ) -> Optional[bool]:
        if not _HAS_Z3:
            return None
        s = Solver()
        s.set('timeout', self.z3_timeout_ms)
        if axiom_adder is not None:
            axiom_adder(s)
        s.add(term_f != term_g)
        r = s.check()
        if r == unsat:
            return True
        if r == sat:
            return False
        return None

    def _z3_counterexample(
        self,
        term_f: Any,
        term_g: Any,
    ) -> Optional[Any]:
        if not _HAS_Z3:
            return None
        s = Solver()
        s.set('timeout', self.z3_timeout_ms)
        s.add(term_f != term_g)
        if s.check() == sat:
            return s.model()
        return None


def opacity_score(fn_names: Sequence[str]) -> float:
    total = len(fn_names)
    if total == 0:
        return 0.0
    u_count = sum(
        1 for n in fn_names
        if _classify_symbol(n) == OpacityLevel.UNINTERPRETED
    )
    return u_count / total


def opacity_depth(fn_names: Sequence[str]) -> int:
    depth = 0
    current = 0
    for n in fn_names:
        if _classify_symbol(n) == OpacityLevel.UNINTERPRETED:
            current += 1
            depth = max(depth, current)
        else:
            current = 0
    return depth


def max_opaque_chain_length(fn_names: Sequence[str]) -> int:
    best = 0
    current = 0
    for n in fn_names:
        if _classify_symbol(n) == OpacityLevel.UNINTERPRETED:
            current += 1
            best = max(best, current)
        else:
            current = 0
    return best


def terms_same_opacity(term_f: Any, term_g: Any) -> bool:
    if not _HAS_Z3:
        return False
    rf = OpacityClassifier.classify_z3_term(term_f)
    rg = OpacityClassifier.classify_z3_term(term_g)
    return (rf.overall_level == rg.overall_level
            and rf.overall_level != OpacityLevel.UNINTERPRETED)


def _print_catalog_table() -> None:
    header = f'{"Builtin":<25} {"Level":<25} {"Axioms":<6} {"Z3 Theory":<12}'
    print(header)
    print('-' * len(header))
    for name in sorted(BUILTIN_OPACITY_CATALOG):
        level = BUILTIN_OPACITY_CATALOG[name]
        has_ax = name in AXIOM_REGISTRY
        theory = Z3_THEORY_MAP.get(name, 'QF_UF')
        print(f'{name:<25} {level.name:<25} {"yes" if has_ax else "no":<6} {theory:<12}')


if __name__ == '__main__':
    print('=' * 60)
    print('Opacity Zone Self-Test')
    print('=' * 60)

    print('\n--- Builtin Opacity Catalog ---')
    _print_catalog_table()

    print('\n--- OpacityLevel lattice ---')
    for a in OpacityLevel:
        for b in OpacityLevel:
            m = OpacityLevel.meet(a, b)
            j = OpacityLevel.join(a, b)
            print(f'  meet({a.name}, {b.name}) = {m.name}   '
                  f'join({a.name}, {b.name}) = {j.name}')

    print('\n--- classify_op ---')
    test_ops = [
        'Add', 'Sub', 'Mult', 'Lt', 'And', 'Concat',
        'binop', 'unop', 'truthy', 'fold', 'tag',
        'sorted', 'reversed', 'list', 'set', 'len', 'sum',
        'dict', 'map', 'filter', 'Counter', 'zip',
    ]
    for op in test_ops:
        level = OpacityClassifier.classify_op(op)
        ax = AXIOM_REGISTRY.get(op, [])
        ax_str = f' axioms={ax}' if ax else ''
        print(f'  {op:<20} -> {level.name}{ax_str}')

    print('\n--- AST classification ---')
    test_exprs = [
        'x + 0',
        'sorted(list(set(x)))',
        'sum(range(n))',
        'n * (n - 1) // 2',
        'len(sorted(x))',
        'reversed(reversed(x))',
    ]
    for expr_str in test_exprs:
        try:
            tree = ast.parse(expr_str, mode='eval')
            report = OpacityClassifier.classify_ast(tree.body)
            print(f'\n  Expression: {expr_str}')
            print(f'    Overall: {report.overall_level.name}')
            print(f'    Score: {report.opacity_score:.3f}')
            print(f'    Depth: {report.opacity_depth}')
            print(f'    Max chain: {report.max_opaque_chain}')
            print(f'    Blind spots: {report.blind_spots}')
            print(f'    Z3 estimate: {report.completeness_estimate:.3f}')
        except SyntaxError:
            print(f'  {expr_str}: parse error')

    print('\n--- Opacity boundary finding ---')
    for expr_str in test_exprs:
        try:
            tree = ast.parse(expr_str, mode='eval')
            boundaries = OpacityBoundaryFinder.find_in_ast(tree.body)
            if boundaries:
                print(f'  {expr_str}: {len(boundaries)} boundary node(s)')
                for b in boundaries:
                    print(f'    symbol={b.symbol_name} children={[c.name for c in b.child_levels]}')
            else:
                print(f'  {expr_str}: no boundary')
        except SyntaxError:
            pass

    print('\n--- CompletenessEstimator ---')
    for lf in OpacityLevel:
        for lg in OpacityLevel:
            est = CompletenessEstimator.estimate_from_levels(lf, lg)
            print(f'  ({lf.name}, {lg.name}) -> {est:.2f}')

    print('\n--- OpacityReducer ---')
    chains = [
        ['set', 'list', 'sorted'],
        ['reversed', 'reversed'],
        ['list', 'list', 'list'],
        ['sorted', 'reversed', 'list', 'set'],
        ['frozenset', 'frozenset'],
        ['dict', 'Counter'],
    ]
    for chain in chains:
        print(f'\n  Chain: {" -> ".join(chain)}')
        r1 = OpacityReducer.try_normalize_away(chain)
        print(f'    normalize:  {"OK" if r1.success else "no"} -> {r1.reduced}')
        r2 = OpacityReducer.try_axiomatize(chain)
        print(f'    axiomatize: {"OK" if r2.success else "no"} -> {r2.reduced}')
        r3 = OpacityReducer.try_spec_match(chain)
        print(f'    spec_match: {"OK" if r3.success else "no"} -> {r3.reduced}')

    print('\n--- Opacity metrics ---')
    for chain in chains:
        s = opacity_score(chain)
        d = opacity_depth(chain)
        mc = max_opaque_chain_length(chain)
        print(f'  {" -> ".join(chain)}: score={s:.2f} depth={d} max_chain={mc}')

    if _HAS_Z3:
        print('\n--- Z3 integration test ---')
        from new_src.cctt.theory import Theory
        T = Theory()
        S = T.S
        p0 = Const('p0_test', S)

        sf = T.shared_fn('sorted', 1)
        lf = T.shared_fn('list', 1)
        setf = T.shared_fn('set', 1)

        t_chain = sf(lf(setf(p0)))
        t_direct = sf(p0)

        report_chain = OpacityClassifier.classify_z3_term(t_chain)
        report_direct = OpacityClassifier.classify_z3_term(t_direct)
        print(f'  sorted(list(set(x))): {report_chain.summary()}')
        print(f'  sorted(x): {report_direct.summary()}')

        pipeline = OpacityAwarePipeline()
        decision = pipeline.decide_route(t_chain, t_direct)
        print(f'  Route: {decision.route.name}')
        print(f'  Pair opacity: {decision.pair_opacity.name}')
        print(f'  Completeness: {decision.completeness_estimate:.3f}')

        result = pipeline.execute(
            t_chain, t_direct,
            axiom_adder=lambda s: T.semantic_axioms(s),
        )
        print(f'  Result: equivalent={result["equivalent"]} method={result["method"]}')

        boundaries = OpacityBoundaryFinder.find_in_z3_term(t_chain)
        print(f'  Boundaries: {len(boundaries)}')
        for b in boundaries:
            print(f'    {b.symbol_name} is_boundary={b.is_boundary}')

        est = CompletenessEstimator.estimate_pair(t_chain, t_direct)
        print(f'  Pair completeness estimate: {est:.3f}')

        print('\n  Terms same opacity checks:')
        t_arith1 = T.binop(1, T.mkint(3), T.mkint(4))
        t_arith2 = T.mkint(7)
        print(f'    binop(ADD,3,4) vs mkint(7): {terms_same_opacity(t_arith1, t_arith2)}')
        print(f'    sorted(x) vs sorted(x): {terms_same_opacity(t_direct, t_direct)}')
    else:
        print('\n--- Z3 not available, skipping integration tests ---')

    print('\n' + '=' * 60)
    print('Self-test complete.')
    print('=' * 60)
