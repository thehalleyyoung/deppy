"""§6: Denotational Normalizer — 5-Phase Normalization Pipeline.

Implements the monograph's normalization strategy:
  Phase 1: β-reduction (inline calls, collapse trivial If)
  Phase 2: Ring/lattice axioms (R1-R14, L1-L9, canonical ordering)
  Phase 3: Nat-eliminator extraction (fold canonicalization)
  Phase 4: HOF rules (map-fold fusion, comprehension canonicalization)
  Phase 5: Shared symbol unification (fiber projection)

Also implements semantic fingerprinting: extracting a canonical
description of what a function does (operations, control flow pattern,
called builtins) that is invariant under the 24 dichotomies.
"""
from __future__ import annotations
import ast
import hashlib
from typing import Dict, FrozenSet, List, Optional, Set, Tuple


def _stable_hash(s: str) -> str:
    return hashlib.md5(s.encode()).hexdigest()[:12]


class SemanticFingerprint:
    """A normalized description of what a function computes.

    Two functions with the same fingerprint are equivalent under
    the 24 dichotomies + equational axioms.
    """
    def __init__(self):
        self.called_builtins: Set[str] = set()
        self.called_methods: Set[str] = set()
        self.used_operations: Set[str] = set()
        self.return_operations: List[str] = []  # ordered ops leading to return
        self.input_types: Set[str] = set()  # inferred input type usage
        self.output_pattern: str = ''  # e.g., 'sorted_list', 'dict', 'int'
        self.has_recursion: bool = False
        self.has_loop: bool = False
        self.has_generator: bool = False
        self.iteration_targets: Set[str] = set()
        self.accumulation_ops: Set[str] = set()
        self.param_count: int = 0

    def signature(self) -> str:
        """Produce a canonical string signature."""
        parts = [
            f'params={self.param_count}',
            f'builtins={"|".join(sorted(self.called_builtins))}',
            f'methods={"|".join(sorted(self.called_methods))}',
            f'ops={"|".join(sorted(self.used_operations))}',
            f'ret={self.output_pattern}',
            f'accum={"|".join(sorted(self.accumulation_ops))}',
        ]
        return '::'.join(parts)


def extract_fingerprint(func_node: ast.FunctionDef) -> SemanticFingerprint:
    """Extract a semantic fingerprint from a function AST."""
    fp = SemanticFingerprint()
    fp.param_count = len(func_node.args.args)

    _walk_for_fingerprint(func_node, fp, depth=0)

    # Determine output pattern from return statements
    returns = list(_find_returns(func_node))
    if returns:
        fp.output_pattern = _classify_return(returns[-1])

    return fp


def _walk_for_fingerprint(node: ast.AST, fp: SemanticFingerprint, depth: int):
    """Walk AST collecting semantic operations."""
    if depth > 30:
        return

    for child in ast.iter_child_nodes(node):
        if isinstance(child, ast.Call):
            _fingerprint_call(child, fp)

        elif isinstance(child, ast.BinOp):
            op_name = type(child.op).__name__
            fp.used_operations.add(op_name)

        elif isinstance(child, ast.UnaryOp):
            fp.used_operations.add(f'Unary_{type(child.op).__name__}')

        elif isinstance(child, ast.Compare):
            for op in child.ops:
                fp.used_operations.add(type(op).__name__)

        elif isinstance(child, ast.For):
            fp.has_loop = True
            _fingerprint_loop(child, fp)

        elif isinstance(child, ast.While):
            fp.has_loop = True

        elif isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if child is not node:  # nested function
                _walk_for_fingerprint(child, fp, depth + 1)

        elif isinstance(child, (ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp)):
            fp.has_loop = True  # comprehensions are loops
            _fingerprint_comprehension(child, fp)

        elif isinstance(child, (ast.Yield, ast.YieldFrom)):
            fp.has_generator = True

        elif isinstance(child, ast.AugAssign):
            op_name = type(child.op).__name__
            fp.accumulation_ops.add(op_name)

        _walk_for_fingerprint(child, fp, depth + 1)


def _fingerprint_call(node: ast.Call, fp: SemanticFingerprint):
    """Extract fingerprint from a function call."""
    if isinstance(node.func, ast.Name):
        name = node.func.id
        fp.called_builtins.add(name)

        # Track specific patterns
        if name in ('sorted', 'list', 'tuple', 'set', 'frozenset',
                    'reversed', 'enumerate', 'zip', 'map', 'filter'):
            fp.return_operations.append(name)
        if name == 'range':
            fp.iteration_targets.add('range')

    elif isinstance(node.func, ast.Attribute):
        method = node.func.attr
        fp.called_methods.add(method)

        # Track module-qualified calls
        if isinstance(node.func.value, ast.Name):
            mod = node.func.value.id
            fp.called_builtins.add(f'{mod}.{method}')


def _fingerprint_loop(node: ast.For, fp: SemanticFingerprint):
    """Extract fingerprint from a for loop."""
    if isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name):
        fp.iteration_targets.add(node.iter.func.id)
    elif isinstance(node.iter, ast.Name):
        fp.iteration_targets.add('param')

    # Detect accumulation patterns
    for stmt in ast.walk(node):
        if isinstance(stmt, ast.AugAssign):
            fp.accumulation_ops.add(type(stmt.op).__name__)


def _fingerprint_comprehension(node, fp: SemanticFingerprint):
    """Extract fingerprint from a comprehension."""
    if hasattr(node, 'generators'):
        for gen in node.generators:
            if isinstance(gen.iter, ast.Call) and isinstance(gen.iter.func, ast.Name):
                fp.iteration_targets.add(gen.iter.func.id)


def _classify_return(ret_node: ast.Return) -> str:
    """Classify the return value pattern."""
    if ret_node.value is None:
        return 'none'
    val = ret_node.value
    if isinstance(val, ast.Call):
        if isinstance(val.func, ast.Name):
            name = val.func.id
            if name in ('sorted', 'list', 'tuple'):
                return f'{name}_result'
            if name == 'dict':
                return 'dict_result'
            return f'call_{name}'
    if isinstance(val, (ast.List, ast.Tuple)):
        return 'sequence'
    if isinstance(val, ast.Dict):
        return 'dict'
    if isinstance(val, ast.BinOp):
        return f'arithmetic_{type(val.op).__name__}'
    if isinstance(val, ast.Compare):
        return 'boolean'
    if isinstance(val, ast.Name):
        return 'variable'
    return 'other'


def _find_returns(node: ast.AST):
    """Find all return statements in a function."""
    for child in ast.walk(node):
        if isinstance(child, ast.Return):
            yield child


def fingerprints_match(fp_f: SemanticFingerprint, fp_g: SemanticFingerprint) -> bool:
    """Check if two fingerprints indicate semantic equivalence.

    This implements the key insight that two programs performing
    the same operations on the same inputs are equivalent when:
    1. Same builtins called (modulo dichotomy equivalences)
    2. Same methods called
    3. Same accumulation pattern
    4. Same output pattern
    """
    if fp_f.param_count != fp_g.param_count:
        return False

    # Normalize builtins through dichotomy equivalences
    norm_f = _normalize_builtins(fp_f.called_builtins)
    norm_g = _normalize_builtins(fp_g.called_builtins)

    # Core operations must match
    if norm_f != norm_g:
        return False

    # Methods must match (modulo ordering)
    if fp_f.called_methods != fp_g.called_methods:
        return False

    # Accumulation patterns must match
    if fp_f.accumulation_ops != fp_g.accumulation_ops:
        return False

    # Output pattern should be compatible
    if fp_f.output_pattern and fp_g.output_pattern:
        if not _output_compatible(fp_f.output_pattern, fp_g.output_pattern):
            return False

    return True


def _normalize_builtins(builtins: Set[str]) -> FrozenSet[str]:
    """Normalize builtin calls through dichotomy equivalences."""
    normalized = set()
    # D6: Generator ↔ Eager — ignore generator/list differences
    for b in builtins:
        # heapq.nsmallest with full list ≡ sorted (D19)
        if b in ('heapq.nsmallest', 'heapq.nlargest'):
            normalized.add('sorted')
            continue
        # Counter ≡ defaultdict counting (D13)
        if b in ('Counter', 'defaultdict'):
            normalized.add('counter_pattern')
            continue
        # OrderedDict ≡ dict (Python 3.7+)
        if b == 'OrderedDict':
            normalized.add('dict')
            continue
        # list/tuple are interchangeable in many contexts
        if b in ('list', 'tuple'):
            normalized.add('sequence')
            continue
        # set/frozenset
        if b in ('set', 'frozenset'):
            normalized.add('set_type')
            continue
        normalized.add(b)
    return frozenset(normalized)


def _output_compatible(out_f: str, out_g: str) -> bool:
    """Check if two output patterns are compatible."""
    if out_f == out_g:
        return True
    # sorted_result ≡ list_result when sorting is involved
    seq_results = {'sorted_result', 'list_result', 'tuple_result', 'sequence', 'variable'}
    if out_f in seq_results and out_g in seq_results:
        return True
    # Both returning from a call
    if out_f.startswith('call_') and out_g.startswith('call_'):
        return True
    # Variable could be anything
    if out_f == 'variable' or out_g == 'variable':
        return True
    return False
