"""§3: Duck Type Inference — Fiber Narrowing.

Analyzes both programs' ASTs to determine which type fibers are
relevant for each parameter.  Narrower fibers = faster Z3 checks.
Enhanced with deeper analysis of function calls, comprehensions,
and method chains.
"""
from __future__ import annotations
import ast
from typing import Set, Tuple


def extract_duck_ops(func_node, param: str) -> Set[str]:
    """Extract the set of operations used on a parameter."""
    ops: Set[str] = set()
    _walk_ops(func_node, param, ops, depth=0)
    return ops


def _walk_ops(node, param: str, ops: Set[str], depth: int):
    """Recursively walk AST to extract operations on param."""
    if depth > 20:
        return

    for child in ast.walk(node):
        if isinstance(child, ast.BinOp):
            for side in (child.left, child.right):
                if _refers_to(side, param):
                    op_map = {
                        ast.Add: 'add', ast.Sub: 'sub', ast.Mult: 'mul',
                        ast.FloorDiv: 'floordiv', ast.Mod: 'mod',
                        ast.Pow: 'pow', ast.LShift: 'lshift',
                        ast.RShift: 'rshift', ast.BitOr: 'bitor',
                        ast.BitAnd: 'bitand', ast.BitXor: 'bitxor',
                        ast.Div: 'truediv',
                    }
                    o = op_map.get(type(child.op))
                    if o:
                        ops.add(o)

        if isinstance(child, ast.Compare):
            names_in = set()
            if _refers_to(child.left, param):
                names_in.add(param)
            for c in child.comparators:
                if _refers_to(c, param):
                    names_in.add(param)
            if param in names_in:
                for op in child.ops:
                    op_map = {ast.Lt: 'lt', ast.LtE: 'le', ast.Gt: 'gt',
                              ast.GtE: 'ge', ast.Eq: 'eq', ast.NotEq: 'ne',
                              ast.Is: 'is', ast.IsNot: 'isnot',
                              ast.In: 'in', ast.NotIn: 'notin'}
                    o = op_map.get(type(op))
                    if o:
                        ops.add(o)

        if isinstance(child, ast.UnaryOp):
            if _refers_to(child.operand, param):
                op_map = {ast.USub: 'neg', ast.Not: 'not', ast.Invert: 'invert'}
                o = op_map.get(type(child.op))
                if o:
                    ops.add(o)

        if isinstance(child, ast.Subscript):
            if _refers_to(child.value, param):
                ops.add('getitem')
            if _refers_to(child.slice, param):
                ops.add('used_as_index')

        if isinstance(child, ast.Call):
            if isinstance(child.func, ast.Attribute):
                if _refers_to(child.func.value, param):
                    ops.add(f'method_{child.func.attr}')
            if isinstance(child.func, ast.Name):
                for arg in child.args:
                    if _refers_to(arg, param):
                        ops.add(f'call_{child.func.id}')

        if isinstance(child, ast.For):
            if _refers_to(child.iter, param):
                ops.add('iter')

        if isinstance(child, ast.AugAssign):
            if isinstance(child.value, ast.Name) and child.value.id == param:
                op_map = {ast.Add: 'iadd', ast.Mult: 'imul', ast.Sub: 'sub',
                          ast.FloorDiv: 'floordiv', ast.Mod: 'mod'}
                o = op_map.get(type(child.op))
                if o:
                    ops.add(o)
            if isinstance(child.target, ast.Name) and child.target.id == param:
                ops.add('mutated')

        # isinstance check
        if (isinstance(child, ast.Call) and isinstance(child.func, ast.Name)
                and child.func.id == 'isinstance'):
            if child.args and _refers_to(child.args[0], param):
                ops.add('isinstance_check')
                # Extract tested types
                if len(child.args) >= 2:
                    type_arg = child.args[1]
                    if isinstance(type_arg, ast.Name):
                        ops.add(f'isinstance_{type_arg.id}')
                    elif isinstance(type_arg, ast.Tuple):
                        for elt in type_arg.elts:
                            if isinstance(elt, ast.Name):
                                ops.add(f'isinstance_{elt.id}')

        # Starred iteration
        if isinstance(child, ast.Starred) and _refers_to(child.value, param):
            ops.add('iter')

        # Comprehension iteration
        if isinstance(child, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
            for gen in child.generators:
                if _refers_to(gen.iter, param):
                    ops.add('iter')


def _refers_to(node, param: str) -> bool:
    """Check if a node refers to the parameter (directly or transitively).

    Handles expressions like (a + b) where a is a parameter — the BinOp
    result transitively depends on the parameter.
    """
    if isinstance(node, ast.Name) and node.id == param:
        return True
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == param:
        return True
    if isinstance(node, ast.Call):
        if isinstance(node.func, ast.Name):
            for arg in node.args:
                if isinstance(arg, ast.Name) and arg.id == param:
                    return True
    # Transitive: if param appears inside a sub-expression
    if isinstance(node, ast.BinOp):
        return _refers_to(node.left, param) or _refers_to(node.right, param)
    if isinstance(node, ast.UnaryOp):
        return _refers_to(node.operand, param)
    if isinstance(node, ast.Subscript):
        return _refers_to(node.value, param) or _refers_to(node.slice, param)
    if isinstance(node, ast.Call):
        if any(_refers_to(a, param) for a in node.args):
            return True
        if isinstance(node.func, ast.Attribute) and _refers_to(node.func.value, param):
            return True
    return False


def infer_duck_type(func_f, func_g, pname: str) -> Tuple[str, bool]:
    """Infer duck type for parameter pname from both programs."""
    ops_f = extract_duck_ops(func_f, pname)
    ops_g = extract_duck_ops(func_g, pname)
    ops = ops_f | ops_g

    # If isinstance checks are present, narrow by tested types
    isinstance_types = {o.replace('isinstance_', '') for o in ops if o.startswith('isinstance_')}
    if isinstance_types:
        # Multiple isinstance types suggest polymorphic parameter
        type_map = {
            'int': 'int', 'float': 'int', 'bool': 'bool',
            'str': 'str', 'list': 'list', 'tuple': 'list',
            'dict': 'ref', 'set': 'ref',
        }
        duck_types = {type_map.get(t, 'unknown') for t in isinstance_types}
        if duck_types == {'int'}:
            return 'int', True
        if duck_types == {'str'}:
            return 'str', True
        # Mixed types → treat as 'any' with isinstance dispatch
        return 'any', True

    numeric_only = {'sub', 'mul', 'imul', 'floordiv', 'mod', 'pow',
                    'neg', 'lshift', 'rshift', 'bitor', 'bitand', 'bitxor',
                    'invert', 'call_range', 'used_as_index', 'truediv'}
    if ops & numeric_only:
        return 'int', True
    if ops & {'lt', 'le', 'gt', 'ge'}:
        return 'int', True

    str_methods = {'method_upper', 'method_lower', 'method_strip', 'method_split',
                   'method_replace', 'method_find', 'method_startswith',
                   'method_endswith', 'method_join', 'method_encode', 'method_format',
                   'method_lstrip', 'method_rstrip', 'method_center', 'method_ljust',
                   'method_rjust', 'method_zfill', 'method_count', 'method_index',
                   'method_isdigit', 'method_isalpha', 'method_isspace',
                   'method_capitalize', 'method_title', 'method_swapcase'}
    if ops & str_methods:
        return 'str', True

    dict_methods = {'method_get', 'method_keys', 'method_values', 'method_items',
                    'method_update', 'method_setdefault', 'method_pop',
                    'method_popitem', 'method_clear',
                    'call_defaultdict', 'call_Counter', 'call_OrderedDict'}
    if ops & dict_methods:
        return 'ref', True

    list_methods = {'method_append', 'method_extend', 'method_sort', 'method_reverse',
                    'method_insert', 'method_remove', 'method_index', 'method_count',
                    'method_pop', 'method_clear', 'method_copy'}
    if ops & list_methods:
        return 'list', True

    set_methods = {'method_add', 'method_discard', 'method_union',
                   'method_intersection', 'method_difference',
                   'method_symmetric_difference', 'method_issubset',
                   'method_issuperset', 'method_update'}
    if ops & set_methods:
        return 'ref', True

    collection_ops = {'iter', 'getitem', 'call_len', 'call_sorted', 'call_list',
                      'call_set', 'call_reversed', 'call_enumerate', 'call_sum',
                      'call_zip', 'call_map', 'call_filter', 'call_min', 'call_max',
                      'call_any', 'call_all', 'call_tuple', 'call_frozenset',
                      'call_dict', 'call_Counter', 'call_chain',
                      'call_groupby', 'call_accumulate'}
    if ops & collection_ops:
        return 'collection', True

    if ops & {'eq', 'ne', 'is', 'isnot'} and not (ops - {'eq', 'ne', 'is', 'isnot', 'isinstance_check'}):
        return 'any', True

    if ops & {'add', 'iadd'} and not (ops & numeric_only - {'add', 'iadd'}):
        # add could be int or str or list — ambiguous without further evidence
        if ops & str_methods:
            return 'str', True
        if ops & collection_ops:
            return 'collection', True
        # No disambiguating evidence → 'any' (conservative for soundness)
        return 'any', False

    return 'unknown', False
