from __future__ import annotations

import ast
from dataclasses import dataclass
from typing import Any, Dict, Iterable, Optional, Set, Tuple


@dataclass(frozen=True)
class LoweredExpr:
    term: Any
    guard: Any


def true_guard(z3: Any) -> Any:
    return z3.BoolVal(True)


def and_guards(z3: Any, *guards: Any) -> Any:
    usable = [g for g in guards if g is not None]
    if not usable:
        return true_guard(z3)
    if len(usable) == 1:
        return usable[0]
    return z3.And(*usable)


def infer_collection_params(func_node: ast.FunctionDef, params: Iterable[str]) -> Set[str]:
    param_set = set(params)
    collection_params: Set[str] = set()
    for node in ast.walk(func_node):
        if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name):
            if node.value.id in param_set:
                collection_params.add(node.value.id)
        elif (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "len"
            and len(node.args) == 1
            and isinstance(node.args[0], ast.Name)
            and node.args[0].id in param_set
        ):
            collection_params.add(node.args[0].id)
    return collection_params


def infer_string_params(func_node: ast.FunctionDef, params: Iterable[str]) -> Set[str]:
    param_set = set(params)
    string_params: Set[str] = set()
    for node in ast.walk(func_node):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            continue
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            names = []
            if isinstance(node.left, ast.Name) and node.left.id in param_set:
                names.append(node.left.id)
            if isinstance(node.right, ast.Name) and node.right.id in param_set:
                names.append(node.right.id)
            if names:
                if (
                    isinstance(node.left, ast.Constant) and isinstance(node.left.value, str)
                ) or (
                    isinstance(node.right, ast.Constant) and isinstance(node.right.value, str)
                ):
                    string_params.update(names)
        if (
            isinstance(node, ast.Compare)
            and len(node.comparators) == 1
            and isinstance(node.left, ast.Name)
            and node.left.id in param_set
            and isinstance(node.comparators[0], ast.Constant)
            and isinstance(node.comparators[0].value, str)
        ):
            string_params.add(node.left.id)
    return string_params


def infer_numeric_params(func_node: ast.FunctionDef, params: Iterable[str]) -> Set[str]:
    param_set = set(params)
    numeric_params: Set[str] = set()
    arithmetic_ops = (ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod, ast.Pow)
    ordered_cmp = (ast.Gt, ast.GtE, ast.Lt, ast.LtE)

    for node in ast.walk(func_node):
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub) and isinstance(node.operand, ast.Name):
            if node.operand.id in param_set:
                numeric_params.add(node.operand.id)
        elif isinstance(node, ast.BinOp):
            for side in (node.left, node.right):
                if isinstance(side, ast.Name) and side.id in param_set:
                    if isinstance(node.op, arithmetic_ops):
                        numeric_params.add(side.id)
                    elif isinstance(node.op, ast.Add):
                        other = node.right if side is node.left else node.left
                        if isinstance(other, ast.Constant) and isinstance(other.value, (int, float, bool)):
                            numeric_params.add(side.id)
        elif (
            isinstance(node, ast.Compare)
            and len(node.ops) == 1
            and len(node.comparators) == 1
            and isinstance(node.left, ast.Name)
            and node.left.id in param_set
            and isinstance(node.ops[0], ordered_cmp)
        ):
            numeric_params.add(node.left.id)
        elif (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "range"
        ):
            for arg in node.args:
                if isinstance(arg, ast.Name) and arg.id in param_set:
                    numeric_params.add(arg.id)
        elif (
            isinstance(node, ast.AugAssign)
            and isinstance(node.value, ast.Name)
            and node.value.id in param_set
            and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod, ast.Pow))
        ):
            numeric_params.add(node.value.id)
        elif isinstance(node, ast.Subscript):
            if isinstance(node.slice, ast.Name) and node.slice.id in param_set:
                numeric_params.add(node.slice.id)
            elif isinstance(node.slice, ast.Slice):
                for bound in (node.slice.lower, node.slice.upper, node.slice.step):
                    if isinstance(bound, ast.Name) and bound.id in param_set:
                        numeric_params.add(bound.id)
    return numeric_params


def build_param_vars(
    func_node: ast.FunctionDef,
    params: list[str],
    z3: Any,
    collection_params: Optional[Set[str]] = None,
) -> Dict[str, Any]:
    collections = (
        infer_collection_params(func_node, params)
        if collection_params is None
        else set(collection_params)
    )
    numeric_params = infer_numeric_params(func_node, params)
    string_params = infer_string_params(func_node, params)
    seq_params = infer_seq_params(func_node, params)
    dict_params = infer_dict_params(func_node, params)
    set_params = infer_set_params(func_node, params)
    unknown_sort = z3.DeclareSort("PyObject")
    z3_params: Dict[str, Any] = {}
    for i, name in enumerate(params):
        if name in seq_params:
            # Use Z3 Sequence theory for list parameters
            z3_params[name] = z3.Const(f"p{i}", z3.SeqSort(z3.IntSort()))
            z3_params[f"__len_{name}"] = z3.Length(z3_params[name])
            z3_params[f"__is_seq_{name}"] = True
        elif name in dict_params:
            z3_params[name] = z3.Array(f"p{i}", z3.IntSort(), z3.IntSort())
            z3_params[f"__len_{name}"] = z3.Int(f"len_p{i}")
            z3_params[f"__is_dict_{name}"] = True
        elif name in set_params:
            z3_params[name] = z3.Array(f"p{i}", z3.IntSort(), z3.BoolSort())
            z3_params[f"__is_set_{name}"] = True
        elif name in collections:
            z3_params[name] = z3.Array(f"p{i}", z3.IntSort(), z3.IntSort())
            z3_params[f"__len_{name}"] = z3.Int(f"len_p{i}")
        elif name in numeric_params:
            z3_params[name] = z3.Int(f"p{i}")
        elif name in string_params:
            z3_params[name] = z3.String(f"p{i}")
        else:
            z3_params[name] = z3.Const(f"p{i}", unknown_sort)
    z3_params["__unknown_add"] = z3.Function(
        "__py_add_object", unknown_sort, unknown_sort, unknown_sort,
    )
    return z3_params


def infer_seq_params(func_node: ast.FunctionDef, params: Iterable[str]) -> Set[str]:
    """Infer which parameters are sequences (lists).

    A parameter is a sequence if it's used with:
    - len(p), p[i], p[i:j], p + other_list
    - for x in p, sorted(p), reversed(p), list(p)
    - p.append(), p.extend(), p.sort(), p.pop()
    """
    param_set = set(params)
    seq_params: Set[str] = set()
    for node in ast.walk(func_node):
        # for x in p  →  p is a sequence
        if isinstance(node, ast.For) and isinstance(node.iter, ast.Name):
            if node.iter.id in param_set:
                seq_params.add(node.iter.id)
        # sorted(p), list(p), reversed(p), sum(p), min(p), max(p)
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id in {'sorted', 'list', 'reversed', 'sum', 'min', 'max', 'enumerate'}
                and node.args and isinstance(node.args[0], ast.Name)
                and node.args[0].id in param_set):
            seq_params.add(node.args[0].id)
        # p.append(), p.extend(), p.sort(), p.pop(), p.insert(), p.remove()
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id in param_set
                and node.func.attr in {'append', 'extend', 'sort', 'pop', 'insert',
                                       'remove', 'reverse', 'index', 'count'}):
            seq_params.add(node.func.value.id)
        # Subscript with integer index or slice
        if (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name)
                and node.value.id in param_set):
            if isinstance(node.slice, ast.Slice):
                seq_params.add(node.value.id)
    return seq_params


def infer_dict_params(func_node: ast.FunctionDef, params: Iterable[str]) -> Set[str]:
    """Infer which parameters are dicts."""
    param_set = set(params)
    dict_params: Set[str] = set()
    for node in ast.walk(func_node):
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id in param_set
                and node.func.attr in {'keys', 'values', 'items', 'get', 'update',
                                       'pop', 'setdefault'}):
            dict_params.add(node.func.value.id)
    return dict_params


def infer_set_params(func_node: ast.FunctionDef, params: Iterable[str]) -> Set[str]:
    """Infer which parameters are sets."""
    param_set = set(params)
    set_params: Set[str] = set()
    for node in ast.walk(func_node):
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id in param_set
                and node.func.attr in {'add', 'remove', 'discard', 'union',
                                       'intersection', 'difference', 'issubset',
                                       'issuperset'}):
            set_params.add(node.func.value.id)
    return set_params


def _as_lowered(value: Any, z3: Any) -> LoweredExpr:
    if isinstance(value, LoweredExpr):
        return value
    return LoweredExpr(term=value, guard=true_guard(z3))


def _is_product(term: Any) -> bool:
    return isinstance(term, tuple)


def semantic_equal(lhs: Any, rhs: Any, z3: Any) -> Any:
    if _is_product(lhs) or _is_product(rhs):
        if not (_is_product(lhs) and _is_product(rhs) and len(lhs) == len(rhs)):
            return z3.BoolVal(False)
        parts = [semantic_equal(l_item, r_item, z3) for l_item, r_item in zip(lhs, rhs)]
        return z3.And(*parts) if parts else z3.BoolVal(True)
    try:
        return lhs == rhs
    except Exception:
        return z3.BoolVal(False)


def semantic_not_equal(lhs: Any, rhs: Any, z3: Any) -> Any:
    if _is_product(lhs) or _is_product(rhs):
        if not (_is_product(lhs) and _is_product(rhs) and len(lhs) == len(rhs)):
            return z3.BoolVal(True)
        parts = [semantic_not_equal(l_item, r_item, z3) for l_item, r_item in zip(lhs, rhs)]
        return z3.Or(*parts) if parts else z3.BoolVal(False)
    try:
        return lhs != rhs
    except Exception:
        return z3.BoolVal(True)


def semantic_ite(cond: Any, when_true: Any, when_false: Any, z3: Any) -> Any:
    if _is_product(when_true) or _is_product(when_false):
        if not (_is_product(when_true) and _is_product(when_false) and len(when_true) == len(when_false)):
            return None
        return tuple(
            semantic_ite(cond, t_item, f_item, z3)
            for t_item, f_item in zip(when_true, when_false)
        )
    return z3.If(cond, when_true, when_false)


def lower_expr(expr: ast.expr, z3_vars: Dict[str, Any], env: Dict[str, Any], z3: Any) -> Optional[LoweredExpr]:
    if isinstance(expr, ast.Name):
        if expr.id in env:
            return _as_lowered(env[expr.id], z3)
        if expr.id in z3_vars:
            return LoweredExpr(term=z3_vars[expr.id], guard=true_guard(z3))
        return None

    if isinstance(expr, ast.Constant):
        if isinstance(expr.value, bool):
            return LoweredExpr(term=z3.BoolVal(expr.value), guard=true_guard(z3))
        if isinstance(expr.value, int):
            return LoweredExpr(term=z3.IntVal(expr.value), guard=true_guard(z3))
        if isinstance(expr.value, float):
            return LoweredExpr(term=z3.RealVal(expr.value), guard=true_guard(z3))
        if isinstance(expr.value, str):
            return LoweredExpr(term=z3.StringVal(expr.value), guard=true_guard(z3))
        return None

    if isinstance(expr, (ast.Tuple, ast.List)):
        lowered_items = [lower_expr(item, z3_vars, env, z3) for item in expr.elts]
        if any(item is None for item in lowered_items):
            return None
        items = [item for item in lowered_items if item is not None]
        # For ast.List, try to build a Z3 Sequence if all items are integers
        if isinstance(expr, ast.List) and items:
            all_int = all(not _is_product(it.term) and _is_int_sort(it.term, z3) for it in items)
            if all_int:
                seq = z3.Empty(z3.SeqSort(z3.IntSort()))
                for it in items:
                    seq = z3.Concat(seq, z3.Unit(it.term))
                return LoweredExpr(
                    term=seq,
                    guard=and_guards(z3, *(it.guard for it in items)),
                )
        return LoweredExpr(
            term=tuple(item.term for item in items),
            guard=and_guards(z3, *(item.guard for item in items)),
        )

    if isinstance(expr, ast.Subscript):
        index_expr = expr.slice
        if isinstance(index_expr, ast.Slice):
            lowered_base = lower_expr(expr.value, z3_vars, env, z3)
            if lowered_base is None:
                return None
            lower_node = index_expr.lower
            upper_node = index_expr.upper
            lower_idx = lower_expr(lower_node, z3_vars, env, z3) if lower_node is not None else LoweredExpr(term=z3.IntVal(0), guard=true_guard(z3))
            if lower_idx is None or _is_product(lower_idx.term):
                return None
            if lowered_base.term.sort() == z3.StringSort():
                length = z3.Length(lowered_base.term)
                if upper_node is None:
                    span = length - lower_idx.term
                    upper_guard = true_guard(z3)
                else:
                    upper_idx = lower_expr(upper_node, z3_vars, env, z3)
                    if upper_idx is None or _is_product(upper_idx.term):
                        return None
                    span = upper_idx.term - lower_idx.term
                    upper_guard = upper_idx.guard
                guard = and_guards(
                    z3,
                    lowered_base.guard,
                    lower_idx.guard,
                    upper_guard,
                    lower_idx.term >= 0,
                    span >= 0,
                )
                return LoweredExpr(term=z3.SubString(lowered_base.term, lower_idx.term, span), guard=guard)
            if _is_product(lowered_base.term):
                if upper_node is not None and isinstance(upper_node, ast.Constant) and isinstance(lower_node, ast.Constant) and isinstance(upper_node.value, int) and isinstance(lower_node.value, int):
                    return LoweredExpr(term=tuple(lowered_base.term[lower_node.value:upper_node.value]), guard=lowered_base.guard)
            return None
        lowered_index = lower_expr(index_expr, z3_vars, env, z3)
        if lowered_index is None or _is_product(lowered_index.term):
            return None
        if isinstance(expr.value, ast.Name):
            base_name = expr.value.id
            if base_name in env:
                lowered_base = _as_lowered(env[base_name], z3)
            elif base_name in z3_vars:
                base_term = z3_vars[base_name]
                if isinstance(base_term, bool):
                    return None
                len_term = z3_vars.get(f"__len_{base_name}")
                guard = lowered_index.guard
                if _is_seq_sort(base_term, z3):
                    length = z3.Length(base_term)
                    guard = and_guards(z3, guard, lowered_index.term >= 0, lowered_index.term < length)
                    return LoweredExpr(term=base_term[lowered_index.term], guard=guard)
                if len_term is not None:
                    guard = and_guards(z3, guard, lowered_index.term >= 0, lowered_index.term < len_term)
                return LoweredExpr(term=z3.Select(base_term, lowered_index.term), guard=guard)
            else:
                return None
        else:
            lowered_base = lower_expr(expr.value, z3_vars, env, z3)
            if lowered_base is None:
                return None

        if _is_product(lowered_base.term):
            if not isinstance(index_expr, ast.Constant) or not isinstance(index_expr.value, int):
                return None
            idx = index_expr.value
            if idx < 0 or idx >= len(lowered_base.term):
                return None
            return LoweredExpr(
                term=lowered_base.term[idx],
                guard=and_guards(z3, lowered_base.guard, lowered_index.guard),
            )
        if lowered_base.term.sort() == z3.StringSort():
            length = z3.Length(lowered_base.term)
            return LoweredExpr(
                term=z3.SubString(lowered_base.term, lowered_index.term, 1),
                guard=and_guards(
                    z3,
                    lowered_base.guard,
                    lowered_index.guard,
                    lowered_index.term >= 0,
                    lowered_index.term < length,
                ),
            )
        if _is_seq_sort(lowered_base.term, z3):
            length = z3.Length(lowered_base.term)
            return LoweredExpr(
                term=lowered_base.term[lowered_index.term],
                guard=and_guards(
                    z3,
                    lowered_base.guard,
                    lowered_index.guard,
                    lowered_index.term >= 0,
                    lowered_index.term < length,
                ),
            )
        return None

    if isinstance(expr, ast.BinOp):
        left = lower_expr(expr.left, z3_vars, env, z3)
        right = lower_expr(expr.right, z3_vars, env, z3)
        if left is None or right is None:
            return None
        if _is_product(left.term) or _is_product(right.term):
            return None
        try:
            if isinstance(expr.op, ast.Add):
                if left.term.sort() == z3.StringSort() and right.term.sort() == z3.StringSort():
                    term = z3.Concat(left.term, right.term)
                elif _is_seq_sort(left.term, z3) and _is_seq_sort(right.term, z3):
                    term = z3.Concat(left.term, right.term)
                elif left.term.sort() == right.term.sort() and left.term.sort().kind() == z3.Z3_UNINTERPRETED_SORT:
                    add_fn = z3_vars.get("__unknown_add")
                    if add_fn is None:
                        return None
                    term = add_fn(left.term, right.term)
                else:
                    term = left.term + right.term
            elif isinstance(expr.op, ast.Sub):
                term = left.term - right.term
            elif isinstance(expr.op, ast.Mult):
                term = left.term * right.term
            elif isinstance(expr.op, ast.FloorDiv):
                term = left.term / right.term
            elif isinstance(expr.op, ast.Mod):
                term = left.term % right.term
            else:
                return None
        except Exception:
            return None
        return LoweredExpr(term=term, guard=and_guards(z3, left.guard, right.guard))

    if isinstance(expr, ast.UnaryOp):
        operand = lower_expr(expr.operand, z3_vars, env, z3)
        if operand is None or _is_product(operand.term):
            return None
        if isinstance(expr.op, ast.USub):
            return LoweredExpr(term=-operand.term, guard=operand.guard)
        if isinstance(expr.op, ast.UAdd):
            return operand
        if isinstance(expr.op, ast.Not):
            if not z3.is_bool(operand.term):
                return None
            try:
                return LoweredExpr(term=z3.Not(operand.term), guard=operand.guard)
            except Exception:
                return None
        return None

    if isinstance(expr, ast.Compare) and len(expr.ops) == 1 and len(expr.comparators) == 1:
        left = lower_expr(expr.left, z3_vars, env, z3)
        right = lower_expr(expr.comparators[0], z3_vars, env, z3)
        if left is None or right is None:
            return None
        op = expr.ops[0]
        if isinstance(op, ast.Eq):
            term = semantic_equal(left.term, right.term, z3)
        elif isinstance(op, ast.NotEq):
            term = semantic_not_equal(left.term, right.term, z3)
        else:
            if _is_product(left.term) or _is_product(right.term):
                return None
            try:
                term = {
                    ast.Gt: left.term > right.term,
                    ast.GtE: left.term >= right.term,
                    ast.Lt: left.term < right.term,
                    ast.LtE: left.term <= right.term,
                }.get(type(op))
            except Exception:
                return None
        if term is None:
            return None
        return LoweredExpr(term=term, guard=and_guards(z3, left.guard, right.guard))

    if isinstance(expr, ast.BoolOp):
        lowered_values = [lower_expr(v, z3_vars, env, z3) for v in expr.values]
        if any(v is None or _is_product(v.term) or not z3.is_bool(v.term) for v in lowered_values):
            return None
        values = [v for v in lowered_values if v is not None]
        try:
            if isinstance(expr.op, ast.And):
                term = z3.And(*(v.term for v in values))
            elif isinstance(expr.op, ast.Or):
                term = z3.Or(*(v.term for v in values))
            else:
                return None
        except Exception:
            return None
        return LoweredExpr(term=term, guard=and_guards(z3, *(v.guard for v in values)))

    if isinstance(expr, ast.IfExp):
        test = lower_expr(expr.test, z3_vars, env, z3)
        body = lower_expr(expr.body, z3_vars, env, z3)
        orelse = lower_expr(expr.orelse, z3_vars, env, z3)
        if (
            test is None
            or body is None
            or orelse is None
            or _is_product(test.term)
            or not z3.is_bool(test.term)
        ):
            return None
        term = semantic_ite(test.term, body.term, orelse.term, z3)
        if term is None:
            return None
        return LoweredExpr(term=term, guard=and_guards(z3, test.guard, body.guard, orelse.guard))

    if isinstance(expr, ast.Call) and isinstance(expr.func, ast.Name):
        name = expr.func.id
        if name == "len" and len(expr.args) == 1:
            arg = expr.args[0]
            if isinstance(arg, ast.Name):
                len_term = z3_vars.get(f"__len_{arg.id}")
                if len_term is not None:
                    return LoweredExpr(term=len_term, guard=true_guard(z3))
            lowered_arg = lower_expr(arg, z3_vars, env, z3)
            if lowered_arg is None:
                return None
            if _is_product(lowered_arg.term):
                return LoweredExpr(term=z3.IntVal(len(lowered_arg.term)), guard=lowered_arg.guard)
            if lowered_arg.term.sort() == z3.StringSort():
                return LoweredExpr(term=z3.Length(lowered_arg.term), guard=lowered_arg.guard)
            if _is_seq_sort(lowered_arg.term, z3):
                return LoweredExpr(term=z3.Length(lowered_arg.term), guard=lowered_arg.guard)
            return None
        if name in {"max", "min"} and len(expr.args) == 2:
            left = lower_expr(expr.args[0], z3_vars, env, z3)
            right = lower_expr(expr.args[1], z3_vars, env, z3)
            if left is None or right is None or _is_product(left.term) or _is_product(right.term):
                return None
            cmp = left.term >= right.term if name == "max" else left.term <= right.term
            term = z3.If(cmp, left.term, right.term)
            return LoweredExpr(term=term, guard=and_guards(z3, left.guard, right.guard))
        if name == "abs" and len(expr.args) == 1:
            value = lower_expr(expr.args[0], z3_vars, env, z3)
            if value is None or _is_product(value.term):
                return None
            return LoweredExpr(term=z3.If(value.term >= 0, value.term, -value.term), guard=value.guard)
        if name == "sum" and len(expr.args) == 1:
            arg = lower_expr(expr.args[0], z3_vars, env, z3)
            if arg is not None and _is_seq_sort(arg.term, z3):
                return _lower_seq_sum(arg, z3)
            if arg is not None and _is_product(arg.term):
                terms = arg.term
                if all(not _is_product(t) for t in terms):
                    total = z3.IntVal(0)
                    for t in terms:
                        total = total + t
                    return LoweredExpr(term=total, guard=arg.guard)
            return None
        if name == "sorted" and len(expr.args) >= 1:
            arg = lower_expr(expr.args[0], z3_vars, env, z3)
            if arg is not None and _is_seq_sort(arg.term, z3):
                return _lower_sorted(arg, z3)
            return None

    # Method calls on sequences/dicts/sets
    if isinstance(expr, ast.Call) and isinstance(expr.func, ast.Attribute):
        obj = lower_expr(expr.func.value, z3_vars, env, z3)
        if obj is not None and _is_seq_sort(obj.term, z3):
            return _lower_seq_method(expr.func.attr, obj, expr.args, z3_vars, env, z3)

    return None


# ═══════════════════════════════════════════════════════════════
# Z3 Sequence / Array / Set theory helpers
# ═══════════════════════════════════════════════════════════════

def _is_seq_sort(term: Any, z3: Any) -> bool:
    """Check if a Z3 term has Sequence sort."""
    try:
        return term.sort().kind() == z3.Z3_SEQ_SORT
    except Exception:
        return False


def _is_int_sort(term: Any, z3: Any) -> bool:
    """Check if a Z3 term has Int sort."""
    try:
        return z3.is_int(term)
    except Exception:
        return False


_FOLD_CTR = [0]


def _lower_seq_sum(arg: LoweredExpr, z3: Any) -> Optional[LoweredExpr]:
    """Lower sum(seq) to a Z3 RecFunction fold."""
    _FOLD_CTR[0] += 1
    uid = _FOLD_CTR[0]
    seq_sort = arg.term.sort()
    fold = z3.RecFunction(
        f'__seq_sum_{uid}', seq_sort, z3.IntSort(), z3.IntSort())
    s = z3.FreshConst(seq_sort, f'ss_{uid}')
    i = z3.FreshInt(f'si_{uid}')
    z3.RecAddDefinition(fold, [s, i],
        z3.If(i >= z3.Length(s), z3.IntVal(0),
              s[i] + fold(s, i + 1)))
    return LoweredExpr(term=fold(arg.term, z3.IntVal(0)), guard=arg.guard)


def _lower_sorted(arg: LoweredExpr, z3: Any) -> Optional[LoweredExpr]:
    """Lower sorted(seq) via Z3 axiomatization.

    Introduces a fresh sequence `result` with axioms:
      1. len(result) = len(input)
      2. ∀i. result[i] ≤ result[i+1]  (sorted)
      3. ∀v. count(v, result) = count(v, input)  (permutation)

    This lets Z3 prove: sorted(xs) == sorted(ys) iff xs, ys have
    the same multiset — exactly what's needed for equivalence of
    different sorting/dedup implementations.
    """
    _FOLD_CTR[0] += 1
    uid = _FOLD_CTR[0]
    seq_sort = arg.term.sort()
    result = z3.FreshConst(seq_sort, f'sorted_{uid}')

    ax_len = z3.Length(result) == z3.Length(arg.term)

    idx = z3.FreshInt(f'sort_i_{uid}')
    ax_sorted = z3.ForAll([idx],
        z3.Implies(
            z3.And(idx >= 0, idx < z3.Length(result) - 1),
            result[idx] <= result[idx + 1]))

    count_fn = z3.RecFunction(
        f'__count_{uid}', seq_sort, z3.IntSort(), z3.IntSort(), z3.IntSort())
    cs = z3.FreshConst(seq_sort, f'cs_{uid}')
    ci = z3.FreshInt(f'ci_{uid}')
    cv = z3.FreshInt(f'cv_{uid}')
    z3.RecAddDefinition(count_fn, [cs, ci, cv],
        z3.If(ci >= z3.Length(cs), z3.IntVal(0),
              z3.If(cs[ci] == cv, 1 + count_fn(cs, ci + 1, cv),
                    count_fn(cs, ci + 1, cv))))

    val = z3.FreshInt(f'perm_v_{uid}')
    ax_perm = z3.ForAll([val],
        count_fn(result, z3.IntVal(0), val) ==
        count_fn(arg.term, z3.IntVal(0), val))

    guard = and_guards(z3, arg.guard, ax_len, ax_sorted, ax_perm)
    return LoweredExpr(term=result, guard=guard)


def _lower_seq_method(
    method: str,
    obj: LoweredExpr,
    args: list,
    z3_vars: Dict[str, Any],
    env: Dict[str, Any],
    z3: Any,
) -> Optional[LoweredExpr]:
    """Lower method calls on Z3 Seq terms."""
    if method == 'append' and len(args) == 1:
        arg = lower_expr(args[0], z3_vars, env, z3)
        if arg is None or _is_product(arg.term):
            return None
        result = z3.Concat(obj.term, z3.Unit(arg.term))
        return LoweredExpr(
            term=result,
            guard=and_guards(z3, obj.guard, arg.guard))

    if method == 'count' and len(args) == 1:
        arg = lower_expr(args[0], z3_vars, env, z3)
        if arg is None or _is_product(arg.term):
            return None
        _FOLD_CTR[0] += 1
        uid = _FOLD_CTR[0]
        seq_sort = obj.term.sort()
        count_fn = z3.RecFunction(
            f'__seq_count_{uid}', seq_sort, z3.IntSort(),
            z3.IntSort(), z3.IntSort())
        s = z3.FreshConst(seq_sort, f'sc_{uid}')
        i = z3.FreshInt(f'sci_{uid}')
        v = z3.FreshInt(f'scv_{uid}')
        z3.RecAddDefinition(count_fn, [s, i, v],
            z3.If(i >= z3.Length(s), z3.IntVal(0),
                  z3.If(s[i] == v, 1 + count_fn(s, i + 1, v),
                        count_fn(s, i + 1, v))))
        return LoweredExpr(
            term=count_fn(obj.term, z3.IntVal(0), arg.term),
            guard=and_guards(z3, obj.guard, arg.guard))

    return None
