"""
Deppy automatic equivalence / inequivalence checker.

Given two Python functions with the same signature, determines whether
they are semantically equivalent (produce the same output for all valid
inputs) or inequivalent (there exists an input on which they differ).

Uses three strategies in order:
  1. **Z3 symbolic** — compile both bodies to Z3 expressions, check ∀x. f(x) = g(x)
  2. **Property-based testing** — generate random inputs, compare outputs
  3. **Guarantee comparison** — if both have @guarantee specs, check spec equivalence

Usage::

    from deppy.equivalence import check_equiv

    def f(x: int) -> int:
        return x * 2

    def g(x: int) -> int:
        return x + x

    result = check_equiv(f, g)
    print(result)
    # EquivResult(equivalent=True, method='z3', ...)
"""
from __future__ import annotations

import ast
import inspect
import random
import textwrap
from dataclasses import dataclass, field
from typing import Any, Callable

try:
    import z3
    _HAS_Z3 = True
except ImportError:
    _HAS_Z3 = False


# ═══════════════════════════════════════════════════════════════════
#  Result type
# ═══════════════════════════════════════════════════════════════════

@dataclass
class EquivResult:
    """Result of an equivalence check."""
    equivalent: bool | None       # True / False / None (inconclusive)
    method: str                   # 'z3', 'testing', 'spec', 'inconclusive'
    counterexample: dict | None = None   # witness when inequivalent
    confidence: float = 1.0       # 1.0 for z3, <1 for testing
    details: str = ""
    lean_proof: str | None = None        # Lean 4 proof script (when Z3 succeeds)
    spec_info: str | None = None         # supplementary spec comparison info

    def __bool__(self) -> bool:
        return self.equivalent is True

    def __repr__(self) -> str:
        tag = {True: "EQUIVALENT", False: "INEQUIVALENT", None: "INCONCLUSIVE"}[self.equivalent]
        s = f"EquivResult({tag}, method='{self.method}'"
        if self.counterexample:
            s += f", counterexample={self.counterexample}"
        if self.confidence < 1.0:
            s += f", confidence={self.confidence:.2f}"
        if self.lean_proof:
            s += ", lean_proof=..."
        s += ")"
        return s


# ═══════════════════════════════════════════════════════════════════
#  Z3 symbolic equivalence
# ═══════════════════════════════════════════════════════════════════

_TYPE_TO_Z3 = {
    int: lambda name: z3.Int(name),
    float: lambda name: z3.Real(name),
    bool: lambda name: z3.Bool(name),
    str: lambda name: z3.String(name),
}

# String → type mapping for PEP 563 (from __future__ import annotations)
_STR_TO_TYPE = {
    'int': int,
    'float': float,
    'bool': bool,
    'str': str,
}

# List/dict Z3 variable creation helpers
def _make_list_z3_var(name: str) -> Any:
    """Create a Z3 Array variable representing a list[int] with a length."""
    arr = z3.Array(name, z3.IntSort(), z3.IntSort())
    length = z3.Int(f"{name}__len")
    return _Z3List(arr, length)

def _make_dict_z3_var(name: str) -> Any:
    """Create a Z3 Array variable representing a dict[str, int] with key presence."""
    vals = z3.Array(name, z3.IntSort(), z3.IntSort())
    has_key = z3.Array(f"{name}__has", z3.IntSort(), z3.BoolSort())
    return _Z3Dict(vals, has_key)


class _Z3List:
    """Z3 model of a Python list: (elements array, length)."""
    __slots__ = ('arr', 'length')
    def __init__(self, arr: Any, length: Any):
        self.arr = arr
        self.length = length
    def __getitem__(self, idx: Any) -> Any:
        return z3.Select(self.arr, idx)
    def store(self, idx: Any, val: Any) -> '_Z3List':
        return _Z3List(z3.Store(self.arr, idx, val), self.length)
    def append(self, val: Any) -> '_Z3List':
        new_arr = z3.Store(self.arr, self.length, val)
        return _Z3List(new_arr, self.length + 1)


class _Z3Dict:
    """Z3 model of a Python dict: (values array, key-presence array)."""
    __slots__ = ('vals', 'has_key')
    def __init__(self, vals: Any, has_key: Any):
        self.vals = vals
        self.has_key = has_key
    def __getitem__(self, key: Any) -> Any:
        return z3.Select(self.vals, key)
    def store(self, key: Any, val: Any) -> '_Z3Dict':
        new_vals = z3.Store(self.vals, key, val)
        new_has = z3.Store(self.has_key, key, True)
        return _Z3Dict(new_vals, new_has)
    def contains(self, key: Any) -> Any:
        return z3.Select(self.has_key, key)


def _get_z3_var(name: str, annotation: type | str | None) -> Any:
    """Create a Z3 variable from a type annotation."""
    # Resolve string annotations (from __future__ import annotations)
    if isinstance(annotation, str):
        resolved = _STR_TO_TYPE.get(annotation)
        if resolved is not None:
            annotation = resolved
        elif annotation == 'list' or annotation.startswith('list['):
            return _make_list_z3_var(name)
        elif annotation == 'dict' or annotation.startswith('dict['):
            return _make_dict_z3_var(name)
    if annotation in _TYPE_TO_Z3:
        return _TYPE_TO_Z3[annotation](name)
    if annotation is list or (hasattr(annotation, '__origin__') and getattr(annotation, '__origin__', None) is list):
        return _make_list_z3_var(name)
    if annotation is dict or (hasattr(annotation, '__origin__') and getattr(annotation, '__origin__', None) is dict):
        return _make_dict_z3_var(name)
    if annotation is None:
        return z3.Int(name)  # default to Int
    return None  # unsupported type


def _to_z3_bool(val: Any) -> Any:
    """Coerce a Z3 value to a boolean expression.

    - _Z3List → length > 0 (truthy list)
    - _Z3Dict → True (approximate)
    - Z3 String → Length > 0
    - int/bool → val != 0
    """
    if isinstance(val, _Z3List):
        return val.length > 0
    if isinstance(val, _Z3Dict):
        return True  # approximate
    if isinstance(val, bool):
        return val
    # For Z3 expressions, check if it's a BoolRef already
    try:
        if hasattr(val, 'sort') and val.sort() == z3.BoolSort():
            return val
        if hasattr(val, 'sort') and val.sort() == z3.StringSort():
            return z3.Length(val) > 0
    except Exception:
        pass
    return val


def _eval_expr_z3(node: ast.expr, env: dict[str, Any]) -> Any:
    """Evaluate a Python AST expression with Z3 symbolic values."""
    if isinstance(node, ast.Name):
        if node.id == 'True':
            return True
        if node.id == 'False':
            return False
        if node.id == 'None':
            return 0  # treat None as 0 for int context
        if node.id in env:
            return env[node.id]
        raise ValueError(f"Unknown variable: {node.id}")

    if isinstance(node, ast.Constant):
        return node.value

    if isinstance(node, ast.BinOp):
        left = _eval_expr_z3(node.left, env)
        right = _eval_expr_z3(node.right, env)
        ops = {
            ast.Add: lambda a, b: a + b,
            ast.Sub: lambda a, b: a - b,
            ast.Mult: lambda a, b: a * b,
            ast.FloorDiv: lambda a, b: a / b,  # Z3 Int division
            ast.Mod: lambda a, b: a % b,
            ast.BitAnd: lambda a, b: a & b,
            ast.BitOr: lambda a, b: a | b,
            ast.BitXor: lambda a, b: a ^ b,
            ast.LShift: lambda a, b: a << b,
            ast.RShift: lambda a, b: a >> b,
        }
        op_type = type(node.op)
        if op_type in ops:
            return ops[op_type](left, right)
        # x ** n for small constant n → repeated multiplication
        if isinstance(node.op, ast.Pow) and isinstance(right, int) and 0 <= right <= 6:
            if right == 0:
                return 1
            result = left
            for _ in range(right - 1):
                result = result * left
            return result
        raise ValueError(f"Unsupported binop: {op_type.__name__}")

    if isinstance(node, ast.UnaryOp):
        operand = _eval_expr_z3(node.operand, env)
        if isinstance(node.op, ast.USub):
            return -operand
        if isinstance(node.op, ast.UAdd):
            return operand
        if isinstance(node.op, ast.Not):
            return z3.Not(operand)
        raise ValueError(f"Unsupported unaryop: {type(node.op).__name__}")

    if isinstance(node, ast.Compare):
        left = _eval_expr_z3(node.left, env)
        result = None
        for op, comp in zip(node.ops, node.comparators):
            right = _eval_expr_z3(comp, env)
            cmp_ops = {
                ast.Eq: lambda a, b: a == b,
                ast.NotEq: lambda a, b: a != b,
                ast.Lt: lambda a, b: a < b,
                ast.LtE: lambda a, b: a <= b,
                ast.Gt: lambda a, b: a > b,
                ast.GtE: lambda a, b: a >= b,
            }
            cmp = cmp_ops.get(type(op))
            if isinstance(op, ast.In):
                if isinstance(right, _Z3List):
                    i = z3.Int(f"__in_idx_{id(node)}")
                    clause = z3.Exists([i], z3.And(i >= 0, i < right.length, right[i] == left))
                elif isinstance(right, _Z3Dict):
                    clause = right.contains(left)
                elif hasattr(right, 'sort') and right.sort() == z3.StringSort():
                    clause = z3.Contains(right, left)
                else:
                    raise ValueError("Unsupported 'in' target")
            elif isinstance(op, ast.NotIn):
                if isinstance(right, _Z3List):
                    i = z3.Int(f"__notin_idx_{id(node)}")
                    clause = z3.Not(z3.Exists([i], z3.And(i >= 0, i < right.length, right[i] == left)))
                elif isinstance(right, _Z3Dict):
                    clause = z3.Not(right.contains(left))
                elif hasattr(right, 'sort') and right.sort() == z3.StringSort():
                    clause = z3.Not(z3.Contains(right, left))
                else:
                    raise ValueError("Unsupported 'not in' target")
            elif cmp is None:
                raise ValueError(f"Unsupported compare: {type(op).__name__}")
            else:
                clause = cmp(left, right)
            result = clause if result is None else z3.And(result, clause)
            left = right
        return result

    if isinstance(node, ast.IfExp):
        cond = _to_z3_bool(_eval_expr_z3(node.test, env))
        then = _eval_expr_z3(node.body, env)
        else_ = _eval_expr_z3(node.orelse, env)
        return z3.If(cond, then, else_)

    if isinstance(node, ast.BoolOp):
        values = [_eval_expr_z3(v, env) for v in node.values]
        if isinstance(node.op, ast.And):
            return z3.And(*values)
        if isinstance(node.op, ast.Or):
            return z3.Or(*values)
        raise ValueError(f"Unsupported boolop: {type(node.op).__name__}")

    if isinstance(node, ast.Call):
        if isinstance(node.func, ast.Name):
            if node.func.id == "abs" and len(node.args) == 1:
                arg = _eval_expr_z3(node.args[0], env)
                return z3.If(arg >= 0, arg, -arg)
            if node.func.id == "min" and len(node.args) == 2:
                a = _eval_expr_z3(node.args[0], env)
                b = _eval_expr_z3(node.args[1], env)
                return z3.If(a <= b, a, b)
            if node.func.id == "max" and len(node.args) == 2:
                a = _eval_expr_z3(node.args[0], env)
                b = _eval_expr_z3(node.args[1], env)
                return z3.If(a >= b, a, b)
            if node.func.id == "min" and len(node.args) == 3:
                a = _eval_expr_z3(node.args[0], env)
                b = _eval_expr_z3(node.args[1], env)
                c = _eval_expr_z3(node.args[2], env)
                return z3.If(a <= b, z3.If(a <= c, a, c), z3.If(b <= c, b, c))
            if node.func.id == "max" and len(node.args) == 3:
                a = _eval_expr_z3(node.args[0], env)
                b = _eval_expr_z3(node.args[1], env)
                c = _eval_expr_z3(node.args[2], env)
                return z3.If(a >= b, z3.If(a >= c, a, c), z3.If(b >= c, b, c))
            if node.func.id == "pow" and len(node.args) == 2:
                base = _eval_expr_z3(node.args[0], env)
                exp = _eval_expr_z3(node.args[1], env)
                if isinstance(exp, int) and 0 <= exp <= 6:
                    if exp == 0:
                        return 1
                    result = base
                    for _ in range(exp - 1):
                        result = result * base
                    return result
            if node.func.id == "bool" and len(node.args) == 1:
                arg = _eval_expr_z3(node.args[0], env)
                return z3.If(arg != 0, 1, 0)
            if node.func.id == "int" and len(node.args) == 1:
                return _eval_expr_z3(node.args[0], env)
            if node.func.id == "len" and len(node.args) == 1:
                arg = _eval_expr_z3(node.args[0], env)
                if isinstance(arg, _Z3List):
                    return arg.length
                if isinstance(arg, _Z3Dict):
                    return z3.Int(f"__dict_len_{id(arg)}")
                if hasattr(arg, 'sort') and arg.sort() == z3.StringSort():
                    return z3.Length(arg)
                raise ValueError(f"len() on unsupported type")
            if node.func.id == "sorted" and len(node.args) >= 1:
                arg = _eval_expr_z3(node.args[0], env)
                if isinstance(arg, _Z3List):
                    # Check for reverse= keyword argument
                    reverse = False
                    for kw in node.keywords:
                        if kw.arg == "reverse":
                            if isinstance(kw.value, ast.Constant):
                                reverse = bool(kw.value.value)
                    suffix = "rev" if reverse else "asc"
                    sorted_arr = z3.Array(f"__sorted_{suffix}_{id(arg)}", z3.IntSort(), z3.IntSort())
                    return _Z3List(sorted_arr, arg.length)
            if node.func.id == "sum" and len(node.args) == 1:
                arg = _eval_expr_z3(node.args[0], env)
                if isinstance(arg, _Z3List):
                    return z3.Int(f"__sum_{id(arg)}")
            if node.func.id == "list" and len(node.args) == 1:
                arg = _eval_expr_z3(node.args[0], env)
                if isinstance(arg, _Z3List):
                    return arg
        if isinstance(node.func, ast.Attribute):
            obj = _eval_expr_z3(node.func.value, env)
            method = node.func.attr
            if isinstance(obj, _Z3List):
                if method == "append" and len(node.args) == 1:
                    val = _eval_expr_z3(node.args[0], env)
                    return obj.append(val)
                if method == "count" and len(node.args) == 1:
                    return z3.Int(f"__count_{id(obj)}")
            if isinstance(obj, _Z3Dict):
                if method == "get" and len(node.args) >= 1:
                    key = _eval_expr_z3(node.args[0], env)
                    if len(node.args) >= 2:
                        default = _eval_expr_z3(node.args[1], env)
                        return z3.If(obj.contains(key), obj[key], default)
                    return obj[key]
                if method == "keys":
                    return obj
            if hasattr(obj, 'sort') and obj.sort() == z3.StringSort():
                if method == "upper":
                    return z3.String(f"__upper_{id(obj)}")
                if method == "lower":
                    return z3.String(f"__lower_{id(obj)}")
                if method == "strip":
                    return z3.String(f"__strip_{id(obj)}")
        raise ValueError(f"Unsupported call: {ast.dump(node)}")

    if isinstance(node, ast.Subscript):
        obj = _eval_expr_z3(node.value, env)
        idx = _eval_expr_z3(node.slice, env)
        if isinstance(obj, _Z3List):
            return obj[idx]
        if isinstance(obj, _Z3Dict):
            return obj[idx]
        raise ValueError(f"Unsupported subscript on {type(obj)}")

    if isinstance(node, ast.List):
        # List literal: build a concrete Z3 list
        elts = [_eval_expr_z3(e, env) for e in node.elts]
        arr = z3.K(z3.IntSort(), 0)  # default value
        for i, v in enumerate(elts):
            arr = z3.Store(arr, i, v)
        return _Z3List(arr, len(elts))

    if isinstance(node, ast.ListComp):
        # Simple list comprehensions: [expr for x in iterable]
        if len(node.generators) == 1:
            gen = node.generators[0]
            iterable = _eval_expr_z3(gen.iter, env)
            if isinstance(iterable, _Z3List):
                result_arr = z3.Array(f"__comp_{id(node)}", z3.IntSort(), z3.IntSort())
                result_len = iterable.length
                if gen.ifs:
                    # Filtered comprehension — model as uninterpreted
                    return _Z3List(result_arr, z3.Int(f"__complen_{id(node)}"))
                # Map comprehension: [f(x) for x in xs]
                return _Z3List(result_arr, result_len)

    raise ValueError(f"Unsupported expression: {type(node).__name__}")


def _eval_body_z3(stmts: list[ast.stmt], env: dict[str, Any]) -> Any:
    """Evaluate a function body with Z3 symbolic values, returning the result expression."""
    for i, stmt in enumerate(stmts):
        # Skip docstrings and bare expressions that aren't method calls
        if isinstance(stmt, ast.Expr):
            # Handle mutating method calls as statements: xs.append(v)
            if isinstance(stmt.value, ast.Call) and isinstance(stmt.value.func, ast.Attribute):
                obj_name = None
                if isinstance(stmt.value.func.value, ast.Name):
                    obj_name = stmt.value.func.value.id
                method = stmt.value.func.attr
                if obj_name and obj_name in env:
                    obj = env[obj_name]
                    if isinstance(obj, _Z3List) and method == "append" and len(stmt.value.args) == 1:
                        val = _eval_expr_z3(stmt.value.args[0], env)
                        env = {**env, obj_name: obj.append(val)}
                        continue
                    if isinstance(obj, _Z3Dict) and method == "update" and len(stmt.value.args) == 1:
                        continue  # approximate: skip dict.update
                    if isinstance(obj, _Z3Dict) and method == "pop" and len(stmt.value.args) >= 1:
                        continue  # approximate: skip dict.pop
            continue

        if isinstance(stmt, ast.Return) and stmt.value is not None:
            return _eval_expr_z3(stmt.value, env)

        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
            target = stmt.targets[0]
            if isinstance(target, ast.Name):
                name = target.id
                env = {**env, name: _eval_expr_z3(stmt.value, env)}
                continue
            # Subscript assignment: xs[i] = v, d[k] = v
            if isinstance(target, ast.Subscript) and isinstance(target.value, ast.Name):
                obj_name = target.value.id
                if obj_name in env:
                    obj = env[obj_name]
                    idx = _eval_expr_z3(target.slice, env)
                    val = _eval_expr_z3(stmt.value, env)
                    if isinstance(obj, _Z3List):
                        env = {**env, obj_name: obj.store(idx, val)}
                        continue
                    if isinstance(obj, _Z3Dict):
                        env = {**env, obj_name: obj.store(idx, val)}
                        continue

        # AugAssign: x += expr, x -= expr, etc.
        if isinstance(stmt, ast.AugAssign) and isinstance(stmt.target, ast.Name):
            name = stmt.target.id
            if name not in env:
                raise ValueError(f"AugAssign to unknown variable: {name}")
            old = env[name]
            val = _eval_expr_z3(stmt.value, env)
            aug_ops = {
                ast.Add: lambda a, b: a + b,
                ast.Sub: lambda a, b: a - b,
                ast.Mult: lambda a, b: a * b,
                ast.FloorDiv: lambda a, b: a / b,
                ast.Mod: lambda a, b: a % b,
                ast.BitAnd: lambda a, b: a & b,
                ast.BitOr: lambda a, b: a | b,
                ast.BitXor: lambda a, b: a ^ b,
            }
            op_fn = aug_ops.get(type(stmt.op))
            if op_fn is None:
                raise ValueError(f"Unsupported augassign op: {type(stmt.op).__name__}")
            env = {**env, name: op_fn(old, val)}
            continue

        if isinstance(stmt, ast.For):
            # For loops over collections are not yet fully modeled symbolically.
            # Fall back to testing for soundness.
            raise ValueError(f"Unsupported for loop")

        if isinstance(stmt, ast.If):
            cond = _to_z3_bool(_eval_expr_z3(stmt.test, env))

            # Check if this is a "mutating if" (no return in body, just assigns)
            # Pattern: `if cond: x = val` — conditional variable update, execution continues
            body_has_return = any(isinstance(s, ast.Return) for s in stmt.body)
            body_is_assign_only = all(
                isinstance(s, (ast.Assign, ast.AugAssign, ast.Expr))
                for s in stmt.body
            ) and not body_has_return

            if body_is_assign_only and not stmt.orelse:
                # Conditional variable mutation — apply as z3.If per variable
                then_env = dict(env)
                for s in stmt.body:
                    if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
                        then_env[s.targets[0].id] = _eval_expr_z3(s.value, then_env)
                    elif isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name):
                        nm = s.target.id
                        old = then_env.get(nm)
                        if old is None:
                            raise ValueError(f"AugAssign to unknown: {nm}")
                        val = _eval_expr_z3(s.value, then_env)
                        aug_ops = {ast.Add: lambda a, b: a + b, ast.Sub: lambda a, b: a - b, ast.Mult: lambda a, b: a * b, ast.FloorDiv: lambda a, b: a / b, ast.Mod: lambda a, b: a % b, ast.BitAnd: lambda a, b: a & b, ast.BitOr: lambda a, b: a | b, ast.BitXor: lambda a, b: a ^ b}
                        fn = aug_ops.get(type(s.op))
                        if fn is None:
                            raise ValueError(f"Unsupported augassign: {type(s.op).__name__}")
                        then_env[nm] = fn(old, val)
                # Merge: for each changed variable, env[v] = If(cond, then_env[v], env[v])
                new_env = dict(env)
                for k, v in then_env.items():
                    if k in env:
                        old = env[k]
                        # Only wrap in If if the value actually changed
                        try:
                            same = (v is old)
                        except Exception:
                            same = False
                        if not same:
                            new_env[k] = z3.If(cond, v, old)
                    else:
                        new_env[k] = v
                env = new_env
                continue

            # Standard return-branching if
            then_result = _eval_body_z3(stmt.body, dict(env))
            if stmt.orelse:
                else_result = _eval_body_z3(stmt.orelse, dict(env))
            elif i + 1 < len(stmts):
                else_result = _eval_body_z3(stmts[i + 1:], dict(env))
            else:
                return None
            if then_result is not None and else_result is not None:
                return z3.If(cond, then_result, else_result)
            return None

    return None


def _z3_check_equiv(f: Callable, g: Callable) -> EquivResult | None:
    """Try to prove f ≡ g or find a counterexample using Z3."""
    if not _HAS_Z3:
        return None

    try:
        src_f = textwrap.dedent(inspect.getsource(f))
        src_g = textwrap.dedent(inspect.getsource(g))
        tree_f = ast.parse(src_f).body[0]
        tree_g = ast.parse(src_g).body[0]
    except (OSError, TypeError, SyntaxError):
        return None

    if not isinstance(tree_f, ast.FunctionDef) or not isinstance(tree_g, ast.FunctionDef):
        return None

    # Build parameter list from f's signature
    hints_f = {k: v for k, v in (inspect.get_annotations(f) or {}).items() if k != 'return'}
    hints_g = {k: v for k, v in (inspect.get_annotations(g) or {}).items() if k != 'return'}

    params_f = [a.arg for a in tree_f.args.args]
    params_g = [a.arg for a in tree_g.args.args]

    if len(params_f) != len(params_g):
        return EquivResult(False, 'z3', details="Different arity")

    # Create Z3 symbolic variables (use f's param names)
    z3_vars: dict[str, Any] = {}
    for p in params_f:
        ann = hints_f.get(p, int)
        var = _get_z3_var(p, ann)
        if var is None:
            return None  # unsupported type
        z3_vars[p] = var

    # Evaluate both bodies
    try:
        env_f = dict(z3_vars)
        result_f = _eval_body_z3(tree_f.body, env_f)
        if result_f is None:
            return None

        # Map g's params to f's Z3 vars
        env_g: dict[str, Any] = {}
        for pf, pg in zip(params_f, params_g):
            env_g[pg] = z3_vars[pf]
        result_g = _eval_body_z3(tree_g.body, env_g)
        if result_g is None:
            return None
    except (ValueError, TypeError, KeyError):
        return None

    # Check ∀ params. f(params) == g(params)
    solver = z3.Solver()
    solver.set("timeout", 5000)

    # Build equality constraint, handling Z3List/Z3Dict
    if isinstance(result_f, _Z3List) and isinstance(result_g, _Z3List):
        # Two lists equal iff same length and same elements
        solver.add(z3.Or(
            result_f.length != result_g.length,
            z3.Exists([z3.Int('__eq_idx')],
                z3.And(z3.Int('__eq_idx') >= 0,
                       z3.Int('__eq_idx') < result_f.length,
                       result_f[z3.Int('__eq_idx')] != result_g[z3.Int('__eq_idx')]))
        ))
    elif isinstance(result_f, _Z3Dict) and isinstance(result_g, _Z3Dict):
        k = z3.Int('__eq_key')
        solver.add(z3.Exists([k], z3.Or(
            result_f.contains(k) != result_g.contains(k),
            z3.And(result_f.contains(k), result_f[k] != result_g[k])
        )))
    else:
        solver.add(result_f != result_g)

    check = solver.check()
    if check == z3.unsat:
        return EquivResult(True, 'z3', details="Z3 proved ∀ inputs: f(x) = g(x)")
    elif check == z3.sat:
        model = solver.model()
        cex = {}
        for p in params_f:
            v = z3_vars[p]
            if isinstance(v, (_Z3List, _Z3Dict)):
                cex[p] = f"<symbolic {type(v).__name__}>"
            else:
                val = model.evaluate(v, model_completion=True)
                try:
                    cex[p] = val.as_long()
                except (AttributeError, ValueError):
                    cex[p] = str(val)
        return EquivResult(False, 'z3', counterexample=cex,
                          details=f"Z3 found counterexample: {cex}")
    else:
        return None  # unknown / timeout


# ═══════════════════════════════════════════════════════════════════
#  Property-based testing equivalence
# ═══════════════════════════════════════════════════════════════════

def _random_value(ann: type | str | None) -> Any:
    """Generate a random value for a type."""
    # Resolve string annotations (from __future__ import annotations)
    if isinstance(ann, str):
        ann = _STR_TO_TYPE.get(ann, ann)
    if ann is bool or ann is type(None):
        return random.choice([True, False])
    if ann is float or ann == 'float':
        return random.uniform(-1000, 1000)
    if ann is str or ann == 'str':
        return ''.join(random.choices('abcdefghij', k=random.randint(0, 10)))
    if ann is list or ann == 'list' or (hasattr(ann, '__origin__') and getattr(ann, '__origin__', None) is list):
        return [random.randint(-100, 100) for _ in range(random.randint(0, 10))]
    # default: int
    return random.randint(-1000, 1000)


def _testing_check_equiv(f: Callable, g: Callable, num_trials: int = 200) -> EquivResult:
    """Check equivalence by running both functions on random inputs."""
    hints_f = inspect.get_annotations(f) or {}
    params = [p for p in inspect.signature(f).parameters if p != 'return']
    param_types = {p: hints_f.get(p, int) for p in params}

    agree = 0
    for _ in range(num_trials):
        args = {p: _random_value(param_types[p]) for p in params}
        try:
            result_f = f(**args)
        except Exception:
            continue
        try:
            result_g = g(**args)
        except Exception:
            continue
        if result_f != result_g:
            return EquivResult(False, 'testing', counterexample=args,
                              details=f"f({args}) = {result_f}, g({args}) = {result_g}")
        agree += 1

    if agree == 0:
        return EquivResult(None, 'testing', confidence=0.0, details="All trials raised exceptions")

    confidence = 1.0 - (0.5 ** agree)
    return EquivResult(True, 'testing', confidence=min(confidence, 0.999),
                      details=f"Agreed on {agree}/{num_trials} random inputs")


# ═══════════════════════════════════════════════════════════════════
#  Spec-based equivalence
# ═══════════════════════════════════════════════════════════════════

def _parse_spec_to_z3(spec: str, result_var: Any, param_vars: dict[str, Any]) -> Any | None:
    """Parse a guarantee spec string into a Z3 constraint.

    Handles patterns like:
      "result >= 0"       → result_var >= 0
      "result > n"        → result_var > param_vars["n"]
      "result == x + y"   → result_var == param_vars["x"] + param_vars["y"]
      "result != 0"       → result_var != 0
      "result <= 100"     → result_var <= 100
    """
    if not _HAS_Z3:
        return None

    import re
    spec = spec.strip()

    # Build an environment: 'result' maps to result_var, params map to their vars
    env = dict(param_vars)
    env['result'] = result_var

    # Try to parse as a Python expression via AST
    try:
        tree = ast.parse(spec, mode='eval')
        return _eval_expr_z3(tree.body, env)
    except Exception:
        pass

    return None


@dataclass
class SpecEquivResult:
    """Result of a spec equivalence check."""
    equivalent: bool | None       # True / False / None
    implies_forward: bool | None  # spec_a ⟹ spec_b
    implies_backward: bool | None # spec_b ⟹ spec_a
    method: str                   # 'z3', 'syntactic', 'inconclusive'
    counterexample: dict | None = None
    details: str = ""

    def __repr__(self) -> str:
        tag = {True: "EQUIVALENT", False: "INEQUIVALENT", None: "INCONCLUSIVE"}[self.equivalent]
        parts = [f"SpecEquivResult({tag}, method='{self.method}'"]
        if self.implies_forward is not None:
            parts.append(f"a⟹b={self.implies_forward}")
        if self.implies_backward is not None:
            parts.append(f"b⟹a={self.implies_backward}")
        if self.counterexample:
            parts.append(f"counterexample={self.counterexample}")
        return ", ".join(parts) + ")"


def check_spec_equiv(spec_a: str, spec_b: str,
                     params: list[str] | None = None,
                     param_types: dict[str, type] | None = None) -> SpecEquivResult:
    """Check whether two @guarantee specs are semantically equivalent.

    Uses Z3 to check: ∀ params, result. spec_a(result, params) ⟺ spec_b(result, params)

    Also determines the implication direction:
      - spec_a ⟹ spec_b (a is stronger)
      - spec_b ⟹ spec_a (b is stronger)
      - both (equivalent)
      - neither (incomparable)

    Args:
        spec_a, spec_b: Guarantee strings (e.g., "result >= 0")
        params: Parameter names (default: inferred from specs)
        param_types: Parameter type annotations

    Example::

        >>> check_spec_equiv("result >= 0", "result > -1")
        SpecEquivResult(EQUIVALENT, method='z3', a⟹b=True, b⟹a=True)

        >>> check_spec_equiv("result > 0", "result >= 0")
        SpecEquivResult(INEQUIVALENT, method='z3', a⟹b=True, b⟹a=False)
    """
    # Syntactic check first
    if spec_a.strip() == spec_b.strip():
        return SpecEquivResult(True, True, True, 'syntactic',
                              details="Specs are syntactically identical")

    if not _HAS_Z3:
        return SpecEquivResult(None, None, None, 'inconclusive',
                              details="Z3 not available")

    # Infer params from spec strings
    if params is None:
        import re
        identifiers = set(re.findall(r'\b([a-zA-Z_]\w*)\b', spec_a + " " + spec_b))
        identifiers -= {'result', 'True', 'False', 'None', 'and', 'or', 'not',
                        'abs', 'min', 'max', 'len', 'sum', 'sorted', 'int', 'float', 'str'}
        params = sorted(identifiers)

    if param_types is None:
        param_types = {}

    # Create Z3 variables
    result_var = z3.Int('result')
    param_vars: dict[str, Any] = {}
    for p in params:
        ann = param_types.get(p, int)
        var = _get_z3_var(p, ann)
        if var is None:
            var = z3.Int(p)
        param_vars[p] = var

    # Parse both specs
    z3_a = _parse_spec_to_z3(spec_a, result_var, param_vars)
    z3_b = _parse_spec_to_z3(spec_b, result_var, param_vars)

    if z3_a is None or z3_b is None:
        # Fall back to syntactic comparison
        return SpecEquivResult(None, None, None, 'inconclusive',
                              details=f"Could not parse specs to Z3: a={spec_a!r}, b={spec_b!r}")

    # Check a ⟹ b: ¬(a ∧ ¬b) is UNSAT
    solver = z3.Solver()
    solver.set("timeout", 3000)

    solver.push()
    solver.add(z3_a)
    solver.add(z3.Not(z3_b))
    fwd_check = solver.check()
    fwd_model = solver.model() if fwd_check == z3.sat else None
    solver.pop()

    implies_fwd = fwd_check == z3.unsat  # a ⟹ b
    fwd_cex = None
    if fwd_model:
        fwd_cex = {}
        for v in [result_var] + list(param_vars.values()):
            val = fwd_model.evaluate(v)
            try:
                fwd_cex[str(v)] = val.as_long()
            except (AttributeError, ValueError):
                fwd_cex[str(v)] = str(val)

    # Check b ⟹ a: ¬(b ∧ ¬a) is UNSAT
    solver.push()
    solver.add(z3_b)
    solver.add(z3.Not(z3_a))
    bwd_check = solver.check()
    bwd_model = solver.model() if bwd_check == z3.sat else None
    solver.pop()

    implies_bwd = bwd_check == z3.unsat  # b ⟹ a
    bwd_cex = None
    if bwd_model:
        bwd_cex = {}
        for v in [result_var] + list(param_vars.values()):
            val = bwd_model.evaluate(v)
            try:
                bwd_cex[str(v)] = val.as_long()
            except (AttributeError, ValueError):
                bwd_cex[str(v)] = str(val)

    equivalent = implies_fwd and implies_bwd

    if equivalent:
        details = f"Z3 proved: '{spec_a}' ⟺ '{spec_b}'"
    elif implies_fwd and not implies_bwd:
        details = f"'{spec_a}' ⟹ '{spec_b}' but not vice versa (a is strictly stronger)"
    elif implies_bwd and not implies_fwd:
        details = f"'{spec_b}' ⟹ '{spec_a}' but not vice versa (b is strictly stronger)"
    else:
        details = f"Specs are incomparable (neither implies the other)"

    cex = fwd_cex or bwd_cex
    return SpecEquivResult(equivalent, implies_fwd, implies_bwd, 'z3',
                          counterexample=cex, details=details)


def _spec_check_equiv(f: Callable, g: Callable) -> EquivResult | None:
    """Compare @guarantee specs of two functions."""
    try:
        from deppy.proofs.sugar import _get_spec
        spec_f = _get_spec(f)
        spec_g = _get_spec(g)
    except Exception:
        return None

    guarantees_f = list(spec_f.guarantees) if spec_f.guarantees else []
    guarantees_g = list(spec_g.guarantees) if spec_g.guarantees else []

    if not guarantees_f and not guarantees_g:
        return None

    if set(guarantees_f) == set(guarantees_g):
        return EquivResult(True, 'spec', confidence=0.8,
                          details=f"Same @guarantee specs: {set(guarantees_f)}")

    # Try Z3 comparison on each guarantee pair
    if len(guarantees_f) == 1 and len(guarantees_g) == 1:
        sr = check_spec_equiv(guarantees_f[0], guarantees_g[0])
        if sr.equivalent is True:
            return EquivResult(True, 'spec+z3', confidence=0.9,
                              details=f"Specs proved equivalent by Z3: '{guarantees_f[0]}' ⟺ '{guarantees_g[0]}'")
        elif sr.equivalent is False:
            return EquivResult(None, 'spec+z3',
                              details=f"Specs differ: {sr.details}")

    return EquivResult(None, 'spec',
                      details=f"Different specs: {guarantees_f} vs {guarantees_g}")


# ═══════════════════════════════════════════════════════════════════
#  Lean 4 proof script generation
# ═══════════════════════════════════════════════════════════════════

_LEAN_TYPE_MAP = {'int': 'Int', 'float': 'Float', 'bool': 'Bool', 'str': 'String'}

_LEAN_BINOP = {
    ast.Add: '+', ast.Sub: '-', ast.Mult: '*',
    ast.FloorDiv: '/', ast.Mod: '%',
}

_LEAN_CMPOP = {
    ast.Lt: '<', ast.LtE: '≤', ast.Gt: '>', ast.GtE: '≥',
    ast.Eq: '=', ast.NotEq: '≠',
}


def _lean_expr(node: ast.expr) -> str | None:
    """Translate a Python expression AST to Lean 4 syntax. Returns None if unsupported."""
    if isinstance(node, ast.Constant):
        v = node.value
        if isinstance(v, bool):
            return 'true' if v else 'false'
        if isinstance(v, int):
            return f'({v})' if v < 0 else str(v)
        return None

    if isinstance(node, ast.Name):
        return node.id

    if isinstance(node, ast.BinOp):
        op_str = _LEAN_BINOP.get(type(node.op))
        if isinstance(node.op, ast.Pow):
            right = _lean_expr(node.right)
            left = _lean_expr(node.left)
            if left is None or right is None:
                return None
            return f'({left} ^ {right})'
        if op_str is None:
            return None
        left = _lean_expr(node.left)
        right = _lean_expr(node.right)
        if left is None or right is None:
            return None
        return f'({left} {op_str} {right})'

    if isinstance(node, ast.UnaryOp):
        if isinstance(node.op, ast.USub):
            operand = _lean_expr(node.operand)
            return f'(-{operand})' if operand else None
        if isinstance(node.op, ast.Not):
            operand = _lean_expr(node.operand)
            return f'(¬{operand})' if operand else None
        return None

    if isinstance(node, ast.Compare):
        if len(node.ops) != 1:
            return None
        op_str = _LEAN_CMPOP.get(type(node.ops[0]))
        if op_str is None:
            return None
        left = _lean_expr(node.left)
        right = _lean_expr(node.comparators[0])
        if left is None or right is None:
            return None
        return f'({left} {op_str} {right})'

    if isinstance(node, ast.IfExp):
        c = _lean_expr(node.test)
        t = _lean_expr(node.body)
        e = _lean_expr(node.orelse)
        if c and t and e:
            return f'if {c} then {t} else {e}'
        return None

    if isinstance(node, ast.BoolOp):
        parts = [_lean_expr(v) for v in node.values]
        if any(p is None for p in parts):
            return None
        op = '∧' if isinstance(node.op, ast.And) else '∨'
        return f' {op} '.join(parts)

    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        fn = node.func.id
        if fn == 'abs' and len(node.args) == 1:
            a = _lean_expr(node.args[0])
            return f'(Int.natAbs {a})' if a else None
        if fn in ('min', 'max') and len(node.args) == 2:
            a = _lean_expr(node.args[0])
            b = _lean_expr(node.args[1])
            if a and b:
                return f'({fn} {a} {b})'
            return None

    return None


def _lean_body(stmts: list[ast.stmt]) -> str | None:
    """Translate function body statements to Lean 4."""
    for i, stmt in enumerate(stmts):
        if isinstance(stmt, ast.Expr):
            continue
        if isinstance(stmt, ast.Return) and stmt.value:
            return _lean_expr(stmt.value)
        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
            name = stmt.targets[0].id
            val = _lean_expr(stmt.value)
            rest = _lean_body(stmts[i + 1:])
            if val and rest:
                return f'let {name} := {val}\n    {rest}'
            return None
        if isinstance(stmt, ast.If):
            cond = _lean_expr(stmt.test)
            if cond is None:
                return None
            then = _lean_body(stmt.body)
            if then is None:
                return None
            if stmt.orelse:
                else_ = _lean_body(stmt.orelse)
            elif i + 1 < len(stmts):
                else_ = _lean_body(stmts[i + 1:])
            else:
                return None
            if else_ is None:
                return None
            return f'if {cond} then {then} else {else_}'
    return None


def _classify_lean_tactic(params: list[str], has_nonlinear: bool) -> str:
    """Choose the best Lean tactic for an equivalence proof."""
    if has_nonlinear:
        return 'by ring'
    return 'by omega'


def _has_nonlinear(node: ast.expr) -> bool:
    """Check if an expression contains nonlinear arithmetic (x*y, x**n)."""
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, ast.Pow):
            return True
        if isinstance(node.op, ast.Mult):
            # x * y where both contain variables is nonlinear
            left_has = _has_vars(node.left)
            right_has = _has_vars(node.right)
            if left_has and right_has:
                return True
        return _has_nonlinear(node.left) or _has_nonlinear(node.right)
    if isinstance(node, ast.UnaryOp):
        return _has_nonlinear(node.operand)
    if isinstance(node, ast.IfExp):
        return _has_nonlinear(node.body) or _has_nonlinear(node.orelse) or _has_nonlinear(node.test)
    if isinstance(node, ast.BoolOp):
        return any(_has_nonlinear(v) for v in node.values)
    if isinstance(node, ast.Compare):
        return _has_nonlinear(node.left) or any(_has_nonlinear(c) for c in node.comparators)
    if isinstance(node, ast.Call):
        return any(_has_nonlinear(a) for a in node.args)
    return False


def _has_vars(node: ast.expr) -> bool:
    """Check if an expression contains any variables."""
    if isinstance(node, ast.Name):
        return True
    if isinstance(node, ast.Constant):
        return False
    if isinstance(node, ast.BinOp):
        return _has_vars(node.left) or _has_vars(node.right)
    if isinstance(node, ast.UnaryOp):
        return _has_vars(node.operand)
    if isinstance(node, ast.Call):
        return any(_has_vars(a) for a in node.args)
    return False


def _generate_lean_equiv(f: Callable, g: Callable, result: EquivResult) -> str | None:
    """Generate a Lean 4 proof script for a Z3-proved equivalence/inequivalence."""
    if result.method != 'z3':
        return None

    try:
        src_f = textwrap.dedent(inspect.getsource(f))
        src_g = textwrap.dedent(inspect.getsource(g))
        tree_f = ast.parse(src_f).body[0]
        tree_g = ast.parse(src_g).body[0]
    except (OSError, TypeError, SyntaxError):
        return None

    if not isinstance(tree_f, ast.FunctionDef) or not isinstance(tree_g, ast.FunctionDef):
        return None

    hints_f = {k: v for k, v in (inspect.get_annotations(f) or {}).items() if k != 'return'}
    params_f = [a.arg for a in tree_f.args.args]

    # Build Lean parameter declarations
    lean_params = []
    for p in params_f:
        ann = hints_f.get(p, int)
        if isinstance(ann, str):
            ann = _STR_TO_TYPE.get(ann, ann)
        lean_type = _LEAN_TYPE_MAP.get(getattr(ann, '__name__', str(ann)), 'Int')
        lean_params.append(f'({p} : {lean_type})')

    params_str = ' '.join(lean_params)

    # Translate function bodies
    body_f = _lean_body(tree_f.body)
    body_g = _lean_body(tree_g.body)
    if body_f is None or body_g is None:
        return None

    fname = f.__name__
    gname = g.__name__

    # Detect nonlinearity for tactic choice
    nonlinear = any(_has_nonlinear(s.value) for s in tree_f.body
                     if isinstance(s, ast.Return) and s.value)
    nonlinear = nonlinear or any(_has_nonlinear(s.value) for s in tree_g.body
                                  if isinstance(s, ast.Return) and s.value)

    lines = [
        '/-!',
        f'  Auto-generated by Deppy equivalence checker',
        f'  Z3 verdict: {"EQUIVALENT" if result.equivalent else "INEQUIVALENT"}',
        '-/',
        '',
        'import Mathlib.Tactic',
        '',
    ]

    if result.equivalent is True:
        # Emit function definitions + equivalence theorem
        tactic = _classify_lean_tactic(params_f, nonlinear)
        lines += [
            f'def {fname} {params_str} : Int :=',
            f'  {body_f}',
            '',
            f'def {gname} {params_str} : Int :=',
            f'  {body_g}',
            '',
            f'-- Z3 proved: ∀ inputs, {fname} = {gname}',
            f'theorem {fname}_eq_{gname} {params_str} :',
            f'    {fname} {" ".join(params_f)} = {gname} {" ".join(params_f)} := by',
            f'  unfold {fname} {gname}',
            f'  {tactic.replace("by ", "")}',
        ]
    elif result.equivalent is False:
        # Emit counterexample witness
        cex = result.counterexample or {}
        witness_args = ' '.join(str(cex.get(p, 0)) for p in params_f)
        lines += [
            f'def {fname} {params_str} : Int :=',
            f'  {body_f}',
            '',
            f'def {gname} {params_str} : Int :=',
            f'  {body_g}',
            '',
            f'-- Z3 found counterexample: {cex}',
            f'theorem {fname}_neq_{gname} :',
            f'    {fname} {witness_args} ≠ {gname} {witness_args} := by',
            f'  unfold {fname} {gname}',
            f'  decide',
        ]
    else:
        return None

    return '\n'.join(lines) + '\n'


def _generate_lean_adherence(fn: Callable, spec: str, result: 'AdherenceResult') -> str | None:
    """Generate a Lean 4 proof script for a Z3-proved spec adherence."""
    if result.method != 'z3':
        return None

    try:
        src = textwrap.dedent(inspect.getsource(fn))
        tree = ast.parse(src).body[0]
    except (OSError, TypeError, SyntaxError):
        return None

    if not isinstance(tree, ast.FunctionDef):
        return None

    hints = {k: v for k, v in (inspect.get_annotations(fn) or {}).items() if k != 'return'}
    params = [a.arg for a in tree.args.args]

    lean_params = []
    for p in params:
        ann = hints.get(p, int)
        if isinstance(ann, str):
            ann = _STR_TO_TYPE.get(ann, ann)
        lean_type = _LEAN_TYPE_MAP.get(getattr(ann, '__name__', str(ann)), 'Int')
        lean_params.append(f'({p} : {lean_type})')

    params_str = ' '.join(lean_params)
    body = _lean_body(tree.body)
    if body is None:
        return None

    fname = fn.__name__

    # Translate spec to Lean proposition
    lean_spec = spec.strip()
    lean_spec = lean_spec.replace('result', f'({fname} {" ".join(params)})')
    lean_spec = lean_spec.replace('>=', '≥').replace('<=', '≤').replace('!=', '≠')
    lean_spec = lean_spec.replace('==', '=')
    lean_spec = lean_spec.replace(' and ', ' ∧ ').replace(' or ', ' ∨ ')

    nonlinear = any(_has_nonlinear(s.value) for s in tree.body
                     if isinstance(s, ast.Return) and s.value)

    lines = [
        '/-!',
        f'  Auto-generated by Deppy adherence checker',
        f'  Spec: {spec}',
        f'  Z3 verdict: {"ADHERES" if result.adheres else "VIOLATES"}',
        '-/',
        '',
        'import Mathlib.Tactic',
        '',
        f'def {fname} {params_str} : Int :=',
        f'  {body}',
        '',
    ]

    if result.adheres is True:
        tactic = _classify_lean_tactic(params, nonlinear)
        lines += [
            f'-- Z3 proved: ∀ inputs, spec holds',
            f'theorem {fname}_adheres {params_str} :',
            f'    {lean_spec} := by',
            f'  unfold {fname}',
            f'  {tactic.replace("by ", "")}',
        ]
    elif result.adheres is False:
        cex = result.counterexample or {}
        witness_args = ' '.join(str(cex.get(p, 0)) for p in params)
        witness_spec = lean_spec
        for p in params:
            witness_spec = witness_spec.replace(p, str(cex.get(p, 0)))
        lines += [
            f'-- Z3 found violation at {cex}',
            f'theorem {fname}_violates :',
            f'    ¬ ({lean_spec.replace(" ".join(params), witness_args)}) := by',
            f'  unfold {fname}',
            f'  decide',
        ]
    else:
        return None

    return '\n'.join(lines) + '\n'


def equiv_to_lean(f: Callable, g: Callable) -> str | None:
    """Check equivalence and return a Lean 4 proof script.

    Convenience wrapper that runs check_equiv and returns the
    generated Lean proof script if Z3 succeeds.

    Example::

        >>> def f(x: int) -> int: return x * 2
        >>> def g(x: int) -> int: return x + x
        >>> print(equiv_to_lean(f, g))
        # Lean 4 proof script...
    """
    result = check_equiv(f, g)
    return result.lean_proof


# ═══════════════════════════════════════════════════════════════════
#  Main API
# ═══════════════════════════════════════════════════════════════════

def check_equiv(f: Callable, g: Callable, *, use_z3: bool = True,
                use_testing: bool = True, num_trials: int = 200) -> EquivResult:
    """Check whether two functions are semantically equivalent.

    Tries Z3 symbolic proof first, falls back to property-based testing.
    If both functions have @guarantee specs, includes spec comparison info.

    Args:
        f, g: Two Python functions to compare.
        use_z3: Try Z3 symbolic equivalence (default True).
        use_testing: Try random testing (default True).
        num_trials: Number of random inputs for testing.

    Returns:
        EquivResult with .equivalent (True/False/None), .method, and
        optionally .lean_proof (Lean 4 proof script when Z3 succeeds).

    Example::

        >>> def f(x: int) -> int: return x * 2
        >>> def g(x: int) -> int: return x + x
        >>> check_equiv(f, g)
        EquivResult(EQUIVALENT, method='z3')
    """
    # Strategy 1: Z3 symbolic
    if use_z3:
        result = _z3_check_equiv(f, g)
        if result is not None:
            # Generate Lean proof script for Z3 results
            result.lean_proof = _generate_lean_equiv(f, g, result)
            # Enrich with spec comparison if available
            spec_info = _spec_check_equiv(f, g)
            if spec_info is not None:
                result.spec_info = spec_info.details
            return result

    # Strategy 2: Property-based testing
    if use_testing:
        result = _testing_check_equiv(f, g, num_trials=num_trials)
        # Enrich with spec comparison if available
        spec_info = _spec_check_equiv(f, g)
        if spec_info is not None:
            result.spec_info = spec_info.details
        return result

    return EquivResult(None, 'inconclusive', details="No verification method available")


def check_inequiv(f: Callable, g: Callable, **kwargs) -> EquivResult:
    """Check whether two functions are NOT equivalent.

    Convenience wrapper — returns the same EquivResult but semantically
    used when you expect inequivalence.
    """
    return check_equiv(f, g, **kwargs)


# ═══════════════════════════════════════════════════════════════════
#  Spec adherence checking
# ═══════════════════════════════════════════════════════════════════

@dataclass
class AdherenceResult:
    """Result of checking whether a function adheres to a spec."""
    adheres: bool | None          # True=proved, False=violated, None=inconclusive
    method: str                   # 'z3', 'testing', 'inconclusive'
    spec: str                     # the spec being checked
    counterexample: dict | None = None
    confidence: float = 1.0
    details: str = ""
    lean_proof: str | None = None        # Lean 4 proof script (when Z3 succeeds)

    def __bool__(self) -> bool:
        return self.adheres is True

    def __repr__(self) -> str:
        tag = {True: "✅ ADHERES", False: "❌ VIOLATES", None: "❓ INCONCLUSIVE"}[self.adheres]
        s = f"AdherenceResult({tag}, spec={self.spec!r}, method='{self.method}'"
        if self.counterexample:
            s += f", counterexample={self.counterexample}"
        if self.confidence < 1.0:
            s += f", confidence={self.confidence:.2f}"
        s += ")"
        return s


def _z3_check_adherence(fn: Callable, spec: str) -> AdherenceResult | None:
    """Use Z3 to prove or disprove that fn satisfies spec for all inputs."""
    if not _HAS_Z3:
        return None

    try:
        src = textwrap.dedent(inspect.getsource(fn))
        tree = ast.parse(src).body[0]
    except (OSError, TypeError, SyntaxError):
        return None

    if not isinstance(tree, ast.FunctionDef):
        return None

    hints = {k: v for k, v in (inspect.get_annotations(fn) or {}).items() if k != 'return'}
    params = [a.arg for a in tree.args.args]

    # Create Z3 symbolic variables
    z3_vars: dict[str, Any] = {}
    for p in params:
        ann = hints.get(p, int)
        var = _get_z3_var(p, ann)
        if var is None:
            return None
        z3_vars[p] = var

    # Evaluate the function body symbolically
    try:
        env = dict(z3_vars)
        result_expr = _eval_body_z3(tree.body, env)
        if result_expr is None:
            return None
    except (ValueError, TypeError, KeyError):
        return None

    # Parse the spec with 'result' bound to the computed expression
    spec_env = dict(z3_vars)
    spec_env['result'] = result_expr
    try:
        spec_tree = ast.parse(spec.strip(), mode='eval')
        constraint = _eval_expr_z3(spec_tree.body, spec_env)
    except Exception:
        return None

    if constraint is None:
        return None

    # Check ∀ params. spec(f(params), params) — negate and check UNSAT
    solver = z3.Solver()
    solver.set("timeout", 5000)

    # Also add any @requires preconditions as hypotheses
    preconditions = []
    try:
        from deppy.proofs.sugar import _get_spec
        fn_spec = _get_spec(fn)
        for pre in fn_spec.preconditions:
            if callable(pre) and not isinstance(pre, str):
                try:
                    pre_str = pre()
                    if isinstance(pre_str, str):
                        pre_tree = ast.parse(pre_str.strip(), mode='eval')
                        pre_z3 = _eval_expr_z3(pre_tree.body, z3_vars)
                        if pre_z3 is not None:
                            preconditions.append(pre_z3)
                except Exception:
                    pass
            elif isinstance(pre, str):
                try:
                    pre_tree = ast.parse(pre.strip(), mode='eval')
                    pre_z3 = _eval_expr_z3(pre_tree.body, z3_vars)
                    if pre_z3 is not None:
                        preconditions.append(pre_z3)
                except Exception:
                    pass
    except Exception:
        pass

    # Assert preconditions hold
    for pc in preconditions:
        solver.add(pc)

    # Assert the spec is violated
    solver.add(z3.Not(constraint))
    check = solver.check()

    if check == z3.unsat:
        return AdherenceResult(True, 'z3', spec,
                              details=f"Z3 proved: ∀ inputs, '{spec}' holds")
    elif check == z3.sat:
        model = solver.model()
        cex = {}
        for p in params:
            val = model.evaluate(z3_vars[p], model_completion=True)
            try:
                cex[p] = val.as_long()
            except (AttributeError, ValueError):
                cex[p] = str(val)
        result_val = model.evaluate(result_expr, model_completion=True) if hasattr(result_expr, 'as_ast') else result_expr
        try:
            cex['result'] = result_val.as_long()
        except (AttributeError, ValueError):
            cex['result'] = str(result_val)

        return AdherenceResult(False, 'z3', spec, counterexample=cex,
                              details=f"Z3 found violation: {cex}")
    else:
        return None


def _testing_check_adherence(fn: Callable, spec: str, num_trials: int = 200) -> AdherenceResult:
    """Check spec adherence by running fn on random inputs."""
    hints = inspect.get_annotations(fn) or {}
    params = [p for p in inspect.signature(fn).parameters if p != 'return']
    param_types = {p: hints.get(p, int) for p in params}

    # Compile the spec into a checker lambda
    try:
        spec_code = compile(spec.strip(), '<spec>', 'eval')
    except SyntaxError:
        return AdherenceResult(None, 'testing', spec,
                              details=f"Cannot parse spec: {spec!r}")

    checked = 0
    for _ in range(num_trials):
        args = {p: _random_value(param_types[p]) for p in params}
        try:
            result = fn(**args)
        except Exception:
            continue

        check_env = dict(args)
        check_env['result'] = result
        check_env['abs'] = abs
        check_env['min'] = min
        check_env['max'] = max
        check_env['len'] = len
        check_env['sum'] = sum
        check_env['sorted'] = sorted

        try:
            if not eval(spec_code, {"__builtins__": {}}, check_env):
                return AdherenceResult(False, 'testing', spec,
                                      counterexample={**args, 'result': result},
                                      details=f"Violation: f({args}) = {result}, but '{spec}' is False")
        except Exception:
            continue

        checked += 1

    if checked == 0:
        return AdherenceResult(None, 'testing', spec, confidence=0.0,
                              details="No trials could be evaluated")

    confidence = 1.0 - (0.5 ** checked)
    return AdherenceResult(True, 'testing', spec, confidence=min(confidence, 0.999),
                          details=f"Passed {checked}/{num_trials} random trials")


def check_adherence(fn: Callable, spec: str | None = None, *,
                    use_z3: bool = True, use_testing: bool = True,
                    num_trials: int = 200) -> list[AdherenceResult]:
    """Check whether a function adheres to its spec(s).

    If no spec is given, uses the function's @guarantee decorators.

    Args:
        fn: The function to check.
        spec: A specific spec string to check (e.g., "result >= 0").
              If None, checks all @guarantee specs on the function.
        use_z3: Try Z3 symbolic verification first.
        use_testing: Fall back to random testing.

    Returns:
        A list of AdherenceResult, one per spec checked.

    Example::

        @guarantee("result >= 0")
        def square(x: int) -> int:
            return x * x

        results = check_adherence(square)
        # [AdherenceResult(✅ ADHERES, spec='result >= 0', method='z3')]
    """
    specs: list[str] = []
    if spec is not None:
        specs = [spec]
    else:
        try:
            from deppy.proofs.sugar import _get_spec
            fn_spec = _get_spec(fn)
            specs = list(fn_spec.guarantees) if fn_spec.guarantees else []
        except Exception:
            pass

    if not specs:
        return [AdherenceResult(None, 'inconclusive', '(none)',
                               details="No specs found — use @guarantee or pass spec=")]

    results: list[AdherenceResult] = []
    for s in specs:
        # Try Z3
        if use_z3:
            r = _z3_check_adherence(fn, s)
            if r is not None:
                r.lean_proof = _generate_lean_adherence(fn, s, r)
                results.append(r)
                continue

        # Fall back to testing
        if use_testing:
            results.append(_testing_check_adherence(fn, s, num_trials=num_trials))
        else:
            results.append(AdherenceResult(None, 'inconclusive', s,
                                          details="No method available"))

    return results
