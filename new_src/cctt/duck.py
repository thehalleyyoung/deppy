"""§3: Duck Type Inference — Fiber Narrowing.

Analyzes both programs' ASTs to determine which type fibers are
relevant for each parameter.  Narrower fibers = faster Z3 checks.
"""
from __future__ import annotations
import ast
from typing import Set, Tuple


def extract_duck_ops(func_node, param: str) -> Set[str]:
    """Extract the set of operations used on a parameter."""
    ops: Set[str] = set()
    for node in ast.walk(func_node):
        if isinstance(node, ast.BinOp):
            for side in (node.left, node.right):
                if isinstance(side, ast.Name) and side.id == param:
                    op_map = {
                        ast.Add: 'add', ast.Sub: 'sub', ast.Mult: 'mul',
                        ast.FloorDiv: 'floordiv', ast.Mod: 'mod',
                        ast.Pow: 'pow', ast.LShift: 'lshift',
                        ast.RShift: 'rshift', ast.BitOr: 'bitor',
                        ast.BitAnd: 'bitand', ast.BitXor: 'bitxor',
                    }
                    o = op_map.get(type(node.op))
                    if o: ops.add(o)
        if isinstance(node, ast.Compare):
            names_in = set()
            if isinstance(node.left, ast.Name): names_in.add(node.left.id)
            for c in node.comparators:
                if isinstance(c, ast.Name): names_in.add(c.id)
            if param in names_in:
                for op in node.ops:
                    op_map = {ast.Lt: 'lt', ast.LtE: 'le', ast.Gt: 'gt',
                              ast.GtE: 'ge', ast.Eq: 'eq', ast.NotEq: 'ne'}
                    o = op_map.get(type(op))
                    if o: ops.add(o)
        if isinstance(node, ast.UnaryOp) and isinstance(node.operand, ast.Name) and node.operand.id == param:
            op_map = {ast.USub: 'neg', ast.Not: 'not'}
            o = op_map.get(type(node.op))
            if o: ops.add(o)
        if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and node.value.id == param:
            ops.add('getitem')
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Name) and node.func.value.id == param):
            ops.add(f'method_{node.func.attr}')
        if isinstance(node, ast.For) and isinstance(node.iter, ast.Name) and node.iter.id == param:
            ops.add('iter')
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            for arg in node.args:
                if isinstance(arg, ast.Name) and arg.id == param:
                    ops.add(f'call_{node.func.id}')
        if isinstance(node, ast.AugAssign) and isinstance(node.value, ast.Name) and node.value.id == param:
            op_map = {ast.Add: 'iadd', ast.Mult: 'imul', ast.Sub: 'sub'}
            o = op_map.get(type(node.op))
            if o: ops.add(o)
    return ops


def infer_duck_type(func_f, func_g, pname: str) -> Tuple[str, bool]:
    """Infer duck type for parameter pname from both programs."""
    ops_f = extract_duck_ops(func_f, pname)
    ops_g = extract_duck_ops(func_g, pname)
    ops = ops_f | ops_g

    numeric_only = {'sub', 'mul', 'imul', 'floordiv', 'mod', 'pow',
                    'neg', 'lshift', 'rshift', 'bitor', 'bitand', 'bitxor',
                    'call_range'}
    if ops & numeric_only: return 'int', True
    if ops & {'lt', 'le', 'gt', 'ge'}: return 'int', True

    str_methods = {'method_upper', 'method_lower', 'method_strip', 'method_split',
                   'method_replace', 'method_find', 'method_startswith',
                   'method_endswith', 'method_join', 'method_encode', 'method_format'}
    if ops & str_methods: return 'str', True

    dict_methods = {'method_get', 'method_keys', 'method_values', 'method_items',
                    'method_update', 'method_setdefault', 'method_pop',
                    'call_defaultdict', 'call_Counter', 'call_OrderedDict'}
    if ops & dict_methods: return 'ref', True

    list_methods = {'method_append', 'method_extend', 'method_sort', 'method_reverse',
                    'method_insert', 'method_remove', 'method_index', 'method_count'}
    if ops & list_methods: return 'list', True

    set_methods = {'method_add', 'method_discard', 'method_union',
                   'method_intersection', 'method_difference'}
    if ops & set_methods: return 'ref', True

    collection_ops = {'iter', 'getitem', 'call_len', 'call_sorted', 'call_list',
                      'call_set', 'call_reversed', 'call_enumerate', 'call_sum',
                      'call_zip', 'call_map', 'call_filter', 'call_min', 'call_max'}
    if ops & collection_ops: return 'collection', True

    if ops & {'eq', 'ne'} and not (ops - {'eq', 'ne'}): return 'any', True
    return 'unknown', False
