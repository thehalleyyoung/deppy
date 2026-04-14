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
            # Only count getitem when the subscript target is a DIRECT
            # reference to the parameter, not a derived value.
            # e.g., nums[i] → getitem (nums is subscripted directly)
            #        bin(n)[2:] → skip (bin(n) is derived from n)
            if _is_direct_ref(child.value, param):
                ops.add('getitem')
            if _refers_to(child.slice, param):
                ops.add('used_as_index')

        if isinstance(child, ast.Call):
            if isinstance(child.func, ast.Attribute):
                # Only add method_xxx when the receiver is a DIRECT reference
                # to the parameter, not a derived value.
                # e.g., s.count('x') → method_count (s is the receiver directly)
                #        bin(n).count('1') → skip (bin(n) is derived from n)
                if _is_direct_ref(child.func.value, param):
                    ops.add(f'method_{child.func.attr}')
                # Detect math.func(param) calls — signals numeric/float usage
                if (isinstance(child.func.value, ast.Name)
                        and child.func.value.id == 'math'
                        and any(_refers_to(a, param) for a in child.args)):
                    ops.add(f'math_{child.func.attr}')
            if isinstance(child.func, ast.Name):
                for arg in child.args:
                    # Only add call_xxx when param is a DIRECT argument,
                    # not wrapped in another function call.
                    # e.g., len(n) → call_len (n is collection)
                    #        len(str(n)) → call_str only (n is int, str(n) is string)
                    if _is_direct_ref(arg, param):
                        ops.add(f'call_{child.func.id}')
                    elif _refers_to(arg, param):
                        # Param is used indirectly — add the call tag but also
                        # record the wrapping function to help disambiguation.
                        # Don't add collection-inferring tags for indirect use.
                        pass

        if isinstance(child, ast.For):
            # Only mark as 'iter' if param IS the iterable directly,
            # not if param is an argument inside a function call that
            # produces the iterable (e.g., range(n) — n is int, not collection)
            iter_node = child.iter
            if isinstance(iter_node, ast.Name) and iter_node.id == param:
                ops.add('iter')
            elif isinstance(iter_node, ast.Attribute) and _refers_to(iter_node.value, param):
                ops.add('iter')  # e.g., for x in param.items()
            # If iter is a call like range(param), sorted(param), etc.,
            # the call_xxx tag from the Call handler is more accurate

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

        # Comprehension iteration — same logic as for-loops
        if isinstance(child, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
            for gen in child.generators:
                iter_node = gen.iter
                if isinstance(iter_node, ast.Name) and iter_node.id == param:
                    ops.add('iter')
                elif isinstance(iter_node, ast.Attribute) and _refers_to(iter_node.value, param):
                    ops.add('iter')


def _is_direct_ref(node, param: str) -> bool:
    """Check if a node is a DIRECT reference to the parameter.

    Unlike _refers_to, this does NOT follow transitive chains through
    function calls. Only returns True for:
    - ast.Name with id == param
    - ast.Attribute on the parameter (e.g., param.items)
    - Subscript/slice of the parameter (e.g., param[0], param[1:])
    """
    if isinstance(node, ast.Name) and node.id == param:
        return True
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == param:
        return True
    if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and node.value.id == param:
        return True
    if isinstance(node, ast.Starred) and isinstance(node.value, ast.Name) and node.value.id == param:
        return True
    return False


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


def _extract_element_ops(func_node, param: str) -> Set[str]:
    """Extract operations performed on elements of a collection parameter.

    Detects:
    - `for x in param: ... x + ... ` → element used arithmetically
    - `param[i] + ...` → subscript result used arithmetically
    - `sum(param)`, `max(param)` → numeric reduction
    """
    elem_ops: Set[str] = set()
    arith_ops = {ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv,
                 ast.Mod, ast.Pow, ast.LShift, ast.RShift,
                 ast.BitOr, ast.BitAnd, ast.BitXor}
    cmp_ops = {ast.Lt, ast.LtE, ast.Gt, ast.GtE}

    # 1. Direct numeric reductions on param
    for child in ast.walk(func_node):
        if isinstance(child, ast.Call) and isinstance(child.func, ast.Name):
            if child.func.id in ('sum', 'min', 'max') and child.args:
                if isinstance(child.args[0], ast.Name) and child.args[0].id == param:
                    elem_ops.add('numeric_reduction')

    # 2. Find loop variables iterating over param
    loop_vars = set()
    for child in ast.walk(func_node):
        if isinstance(child, ast.For):
            iter_node = child.iter
            # Direct: for x in param
            is_param_iter = isinstance(iter_node, ast.Name) and iter_node.id == param
            # Subscript/slice: for x in param[1:] or param[::2]
            if not is_param_iter and isinstance(iter_node, ast.Subscript):
                is_param_iter = isinstance(iter_node.value, ast.Name) and iter_node.value.id == param
            # Call wrapping: for x in reversed(param), sorted(param), etc.
            if not is_param_iter and isinstance(iter_node, ast.Call):
                if isinstance(iter_node.func, ast.Name) and iter_node.args:
                    arg0 = iter_node.args[0]
                    if isinstance(arg0, ast.Name) and arg0.id == param:
                        is_param_iter = True
                    elif isinstance(arg0, ast.Subscript) and isinstance(arg0.value, ast.Name) and arg0.value.id == param:
                        is_param_iter = True
            if is_param_iter:
                if isinstance(child.target, ast.Name):
                    loop_vars.add(child.target.id)
                elif isinstance(child.target, ast.Tuple):
                    for elt in child.target.elts:
                        if isinstance(elt, ast.Name):
                            loop_vars.add(elt.id)
            # enumerate(param) → for i, x in enumerate(param)
            if (isinstance(child.iter, ast.Call) and isinstance(child.iter.func, ast.Name)
                    and child.iter.func.id == 'enumerate' and child.iter.args):
                arg = child.iter.args[0]
                if isinstance(arg, ast.Name) and arg.id == param:
                    if isinstance(child.target, ast.Tuple):
                        for elt in child.target.elts:
                            if isinstance(elt, ast.Name):
                                loop_vars.add(elt.id)
        # Comprehension generators
        if isinstance(child, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
            for gen in child.generators:
                iter_node = gen.iter
                is_param_iter = isinstance(iter_node, ast.Name) and iter_node.id == param
                if not is_param_iter and isinstance(iter_node, ast.Subscript):
                    is_param_iter = isinstance(iter_node.value, ast.Name) and iter_node.value.id == param
                if is_param_iter:
                    if isinstance(gen.target, ast.Name):
                        loop_vars.add(gen.target.id)

    # Check if loop vars are used with arithmetic/comparison
    if loop_vars:
        for child in ast.walk(func_node):
            if isinstance(child, ast.BinOp):
                for side in (child.left, child.right):
                    if isinstance(side, ast.Name) and side.id in loop_vars:
                        if type(child.op) in arith_ops:
                            elem_ops.add('elem_arith')
            # Augmented assignment: result ^= n, total += x, etc.
            if isinstance(child, ast.AugAssign):
                if isinstance(child.value, ast.Name) and child.value.id in loop_vars:
                    if type(child.op) in arith_ops:
                        elem_ops.add('elem_arith')
            if isinstance(child, ast.Compare):
                refs = set()
                if isinstance(child.left, ast.Name) and child.left.id in loop_vars:
                    refs.add(child.left.id)
                for c in child.comparators:
                    if isinstance(c, ast.Name) and c.id in loop_vars:
                        refs.add(c.id)
                if refs and any(type(op) in cmp_ops for op in child.ops):
                    elem_ops.add('elem_compare')
            if isinstance(child, ast.UnaryOp) and isinstance(child.op, (ast.USub, ast.Invert)):
                if isinstance(child.operand, ast.Name) and child.operand.id in loop_vars:
                    elem_ops.add('elem_arith')
            # Function calls: max(x, ...), min(x, ...), abs(x), etc.
            if isinstance(child, ast.Call) and isinstance(child.func, ast.Name):
                fname = child.func.id
                if fname in ('abs', 'int', 'float', 'round') and child.args:
                    if isinstance(child.args[0], ast.Name) and child.args[0].id in loop_vars:
                        elem_ops.add('elem_arith')
                if fname in ('max', 'min') and len(child.args) >= 2:
                    if any(isinstance(a, ast.Name) and a.id in loop_vars for a in child.args):
                        elem_ops.add('elem_compare')

    # 3. Subscript result used arithmetically: param[i] + ...
    # NOTE: This uses 'elem_subscript_arith' instead of 'elem_arith' because
    # subscript arithmetic (p[0] + p[1]) is common for fixed-size containers
    # like coordinates/points, which should NOT be classified as numeric_list.
    for child in ast.walk(func_node):
        if isinstance(child, ast.BinOp):
            for side in (child.left, child.right):
                if (isinstance(side, ast.Subscript)
                        and isinstance(side.value, ast.Name)
                        and side.value.id == param
                        and type(child.op) in arith_ops):
                    elem_ops.add('elem_subscript_arith')
        if isinstance(child, ast.Compare):
            all_nodes = [child.left] + child.comparators
            has_subscript = False
            for n in all_nodes:
                if (isinstance(n, ast.Subscript)
                        and isinstance(n.value, ast.Name)
                        and n.value.id == param):
                    has_subscript = True
            if has_subscript and any(type(op) in cmp_ops for op in child.ops):
                elem_ops.add('elem_subscript_compare')

    return elem_ops


def _detect_double_subscript(func_node, param: str) -> bool:
    """Detect param[i][j] pattern indicating a 2D list (matrix)."""
    for child in ast.walk(func_node):
        if isinstance(child, ast.Subscript):
            # Check if the value is also a subscript of param
            inner = child.value
            if isinstance(inner, ast.Subscript) and _refers_to(inner.value, param):
                return True
            # Also check param[0][0]-style and len(param[0])
        if isinstance(child, ast.Call):
            if isinstance(child.func, ast.Name) and child.func.id == 'len':
                if child.args and isinstance(child.args[0], ast.Subscript):
                    if _refers_to(child.args[0].value, param):
                        return True  # len(param[0]) → matrix
    return False


def _detect_positive_int_domain(func_node, param: str) -> bool:
    """Detect if the function guards against non-positive param values.

    Looks for patterns like:
      if param < 2: return ...
      if param <= 0: return ...
      while param > 0: ...
      range(1, param + 1) or range(param)
    """
    for child in ast.walk(func_node):
        # if param < N: return ... (where N is small positive)
        if isinstance(child, ast.If):
            test = child.test
            if isinstance(test, ast.Compare) and len(test.ops) == 1:
                left = test.left
                op = test.ops[0]
                comparator = test.comparators[0]
                # param < N or param <= N
                if (_refers_to(left, param) and
                    isinstance(op, (ast.Lt, ast.LtE)) and
                    isinstance(comparator, ast.Constant) and
                    isinstance(comparator.value, (int, float)) and
                    0 <= comparator.value <= 3):
                    # Check if body contains return
                    if any(isinstance(s, ast.Return) for s in child.body):
                        return True
                # N > param or N >= param
                if (_refers_to(comparator, param) and
                    isinstance(op, (ast.Gt, ast.GtE)) and
                    isinstance(left, ast.Constant) and
                    isinstance(left.value, (int, float)) and
                    0 <= left.value <= 3):
                    if any(isinstance(s, ast.Return) for s in child.body):
                        return True
        # range(1, param + 1) or range(param) — implies positive int domain
        if isinstance(child, ast.Call):
            fn = child.func
            if isinstance(fn, ast.Name) and fn.id == 'range' and len(child.args) >= 2:
                # range(1, param + 1) or range(1, param)
                first_arg = child.args[0]
                second_arg = child.args[1]
                if (isinstance(first_arg, ast.Constant) and first_arg.value == 1 and
                    _refers_to_expr(second_arg, param)):
                    return True
    return False


def _refers_to_expr(node, param: str) -> bool:
    """Check if an expression references param (possibly with arithmetic)."""
    if isinstance(node, ast.Name) and node.id == param:
        return True
    if isinstance(node, ast.BinOp):
        return _refers_to_expr(node.left, param) or _refers_to_expr(node.right, param)
    return False


def infer_duck_type(func_f, func_g, pname: str) -> Tuple[str, bool]:
    """Infer duck type for parameter pname from both programs."""
    ops_f = extract_duck_ops(func_f, pname)
    ops_g = extract_duck_ops(func_g, pname)
    ops = ops_f | ops_g

    # Detect numeric list: collection whose elements are used arithmetically
    elem_ops_f = _extract_element_ops(func_f, pname)
    elem_ops_g = _extract_element_ops(func_g, pname)
    elem_ops = elem_ops_f | elem_ops_g

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

    collection_ops = {'iter', 'getitem', 'call_len', 'call_sorted', 'call_list',
                      'call_set', 'call_reversed', 'call_enumerate', 'call_sum',
                      'call_zip', 'call_map', 'call_filter', 'call_min', 'call_max',
                      'call_any', 'call_all', 'call_tuple', 'call_frozenset',
                      'call_dict', 'call_Counter', 'call_chain',
                      'call_groupby', 'call_accumulate'}

    numeric_only = {'sub', 'mul', 'imul', 'floordiv', 'mod', 'pow',
                    'neg', 'lshift', 'rshift', 'bitor', 'bitand', 'bitxor',
                    'invert', 'call_range', 'used_as_index', 'truediv',
                    'call_gcd', 'call_lcm'}

    # Check specific types BEFORE generic collection to avoid
    # mis-classifying list parameters as collection.
    str_methods = {'method_upper', 'method_lower', 'method_strip', 'method_split',
                   'method_replace', 'method_find', 'method_startswith',
                   'method_endswith', 'method_join', 'method_encode', 'method_format',
                   'method_lstrip', 'method_rstrip', 'method_center', 'method_ljust',
                   'method_rjust', 'method_zfill',
                   'method_isdigit', 'method_isalpha', 'method_isspace',
                   'method_capitalize', 'method_title', 'method_swapcase'}
    # Note: method_count and method_index are shared between str and list,
    # so they are NOT included here (handled in list_methods below)
    if ops & str_methods:
        return 'str', True

    # Detect parameters passed to stdlib functions that expect bytes
    # (e.g., base64.b64encode(data), hashlib.sha256(data))
    bytes_calls = {'call_b64encode', 'call_b64decode', 'call_urlsafe_b64encode',
                   'call_sha256', 'call_sha1', 'call_md5', 'call_sha512',
                   'call_sha384', 'call_sha224',
                   'method_decode'}
    # Also detect module-qualified calls like base64.b64encode(data)
    bytes_module_calls = set()
    for child in ast.walk(func_f):
        if isinstance(child, ast.Call) and isinstance(child.func, ast.Attribute):
            if isinstance(child.func.value, ast.Name):
                mod = child.func.value.id
                method = child.func.attr
                if mod in ('base64', 'hashlib') and any(
                    isinstance(a, ast.Name) and a.id == pname for a in child.args):
                    bytes_module_calls.add(f'{mod}_{method}')
            # Detect chained calls like hashlib.sha256(data).hexdigest()
            if isinstance(child.func.value, ast.Call):
                inner = child.func.value
                if isinstance(inner.func, ast.Attribute) and isinstance(inner.func.value, ast.Name):
                    mod = inner.func.value.id
                    method = inner.func.attr
                    if mod == 'hashlib' and any(
                        isinstance(a, ast.Name) and a.id == pname for a in inner.args):
                        bytes_module_calls.add(f'{mod}_{method}')
    for child in ast.walk(func_g):
        if isinstance(child, ast.Call) and isinstance(child.func, ast.Attribute):
            if isinstance(child.func.value, ast.Name):
                mod = child.func.value.id
                method = child.func.attr
                if mod in ('base64', 'hashlib') and any(
                    isinstance(a, ast.Name) and a.id == pname for a in child.args):
                    bytes_module_calls.add(f'{mod}_{method}')
            if isinstance(child.func.value, ast.Call):
                inner = child.func.value
                if isinstance(inner.func, ast.Attribute) and isinstance(inner.func.value, ast.Name):
                    mod = inner.func.value.id
                    method = inner.func.attr
                    if mod == 'hashlib' and any(
                        isinstance(a, ast.Name) and a.id == pname for a in inner.args):
                        bytes_module_calls.add(f'{mod}_{method}')
    if (ops & bytes_calls) or bytes_module_calls:
        return 'bytes', True

    # Dict-specific methods (not shared with list/set)
    dict_specific = {'method_get', 'method_keys', 'method_values', 'method_items',
                     'method_setdefault', 'method_popitem'}
    # method_pop, method_clear, method_update are shared (dict+list or dict+set).
    # Only classify as dict if dict-specific methods are present,
    # to avoid misclassifying list.pop() as dict.pop().
    dict_shared = {'method_pop', 'method_clear', 'method_update'}
    if ops & dict_specific:
        return 'dict', True
    if ops & dict_shared and not (ops & collection_ops):
        return 'dict', True

    # Check for matrix (2D list) BEFORE list methods, because matrix params
    # often use list.pop() on rows but should still be classified as matrix.
    if (ops & collection_ops and
        (_detect_double_subscript(func_f, pname) or
         _detect_double_subscript(func_g, pname))):
        return 'matrix', True

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

    # math module functions (math.copysign, math.sqrt, etc.) -> numeric
    math_ops = {o for o in ops if o.startswith('math_')}
    if math_ops and not (ops & collection_ops):
        return 'numeric', True

    # Numeric-only ops -> integer parameter
    # BUT only if there are no collection ops (getitem, iter, len, etc.)
    # Distinguish int-specific ops (mod, floordiv, bitops) from float-compatible
    # ops (sub, mul, truediv) to catch float precision differences.
    int_specific = {'floordiv', 'mod', 'lshift', 'rshift', 'bitor', 'bitand',
                    'bitxor', 'invert', 'call_range', 'used_as_index',
                    'call_gcd', 'call_lcm'}
    if ops & numeric_only and not (ops & collection_ops):
        # Check for positive-int domain guards or used-as-index pattern
        if (_detect_positive_int_domain(func_f, pname) or
            _detect_positive_int_domain(func_g, pname) or
            'used_as_index' in ops):
            return 'positive_int', True
        # If no int-specific ops, classify as 'numeric' (int+float)
        if not (ops & int_specific):
            return 'numeric', True
        return 'int', True
    if ops & {'lt', 'le', 'gt', 'ge'} and not (ops & collection_ops):
        if (_detect_positive_int_domain(func_f, pname) or
            _detect_positive_int_domain(func_g, pname) or
            'used_as_index' in ops):
            return 'positive_int', True
        # If only comparisons + float-compatible ops, use numeric
        if not (ops & int_specific):
            return 'numeric', True
        return 'int', True

    # Generic collection (iter, getitem, len, etc.)
    if ops & collection_ops:
        # Check if elements are used arithmetically via ITERATION
        numeric_elem_loop = {'elem_arith', 'elem_compare', 'numeric_reduction'}
        if elem_ops & numeric_elem_loop:
            return 'numeric_list', True
        return 'collection', True

    if ops & {'eq', 'ne', 'is', 'isnot'} and not (ops - {'eq', 'ne', 'is', 'isnot', 'isinstance_check'}):
        return 'any', True

    if ops & {'add', 'iadd'} and not (ops & numeric_only - {'add', 'iadd'}):
        # add could be int or str or list — but for pure arithmetic
        # (no string/list methods or collection ops), use int + float fibers
        # to catch float precision differences.
        if ops & str_methods:
            return 'str', True
        if ops & collection_ops:
            return 'collection', True
        return 'numeric', True

    return 'unknown', False


# ─── Duck type lattice (Proposal 4) ───────────────────────

ALL_FIBERS = frozenset(['int', 'bool', 'str', 'pair', 'ref', 'none'])

DUCK_TYPE_FIBERS: dict[str, frozenset[str]] = {
    'int': frozenset(['int']),
    'bool': frozenset(['bool']),
    'str': frozenset(['str']),
    'ref': frozenset(['ref']),
    'list': frozenset(['pair', 'ref']),
    'collection': frozenset(['pair', 'ref', 'str']),
    'numeric_list': frozenset(['pair', 'ref']),
    'bytes': frozenset(['str']),  # bytes shares string fiber but uses bytes samples
    'numeric': frozenset(['int']),
    'any': ALL_FIBERS,
    'unknown': ALL_FIBERS,
}


def duck_type_leq(t1: str, t2: str) -> bool:
    """Check if duck type t1 ⊑ t2 in the lattice (F(t1) ⊆ F(t2))."""
    f1 = DUCK_TYPE_FIBERS.get(t1, frozenset())
    f2 = DUCK_TYPE_FIBERS.get(t2, frozenset())
    return f1 <= f2


def duck_type_meet(t1: str, t2: str) -> str:
    """Greatest lower bound — narrowest type containing F(t1) ∪ F(t2)."""
    f1 = DUCK_TYPE_FIBERS.get(t1, frozenset())
    f2 = DUCK_TYPE_FIBERS.get(t2, frozenset())
    union = f1 | f2
    best = 'any'
    best_size = len(DUCK_TYPE_FIBERS['any'])
    for name, fibers in DUCK_TYPE_FIBERS.items():
        if union <= fibers and len(fibers) < best_size:
            best = name
            best_size = len(fibers)
    return best


def duck_type_join(t1: str, t2: str) -> str:
    """Least upper bound — widest type whose fibers are in F(t1) ∩ F(t2).

    Returns 'bottom' if the intersection is empty.
    """
    f1 = DUCK_TYPE_FIBERS.get(t1, frozenset())
    f2 = DUCK_TYPE_FIBERS.get(t2, frozenset())
    inter = f1 & f2
    if not inter:
        return 'bottom'
    best = 'bottom'
    best_size = 0
    for name, fibers in DUCK_TYPE_FIBERS.items():
        if fibers <= inter and len(fibers) > best_size:
            best = name
            best_size = len(fibers)
    return best


def galois_connection_alpha(concrete_fibers: frozenset[str]) -> str:
    """α map: concrete fiber set → narrowest abstract duck type containing it."""
    best = 'any'
    best_size = len(ALL_FIBERS)
    for name, fibers in DUCK_TYPE_FIBERS.items():
        if concrete_fibers <= fibers and len(fibers) < best_size:
            best = name
            best_size = len(fibers)
    return best


def galois_connection_gamma(duck_type: str) -> frozenset[str]:
    """γ map: abstract duck type → concrete fiber set."""
    return DUCK_TYPE_FIBERS.get(duck_type, ALL_FIBERS)


class HasseDiagram:
    """Hasse diagram of the duck type lattice."""

    def __init__(self, nodes: list, edges: list):
        self.nodes = nodes
        self.edges = edges

    def render_ascii(self) -> str:
        from collections import defaultdict
        levels: dict[str, int] = {}
        for n in self.nodes:
            levels[n] = len(DUCK_TYPE_FIBERS.get(n, frozenset()))
        by_level: dict[int, list] = defaultdict(list)
        for n, lvl in sorted(levels.items(), key=lambda x: x[1]):
            by_level[lvl].append(n)
        lines: list[str] = []
        for lvl in sorted(by_level.keys(), reverse=True):
            row = "  ".join(by_level[lvl])
            lines.append(f"  level {lvl}: {row}")
        lines.append("")
        lines.append("  Edges (⊑):")
        for a, b in self.edges:
            lines.append(f"    {a} ⊑ {b}")
        return "\n".join(lines)


def build_hasse_diagram() -> HasseDiagram:
    """Build the Hasse diagram — edges are immediate ⊑ relations only."""
    names = list(DUCK_TYPE_FIBERS.keys())
    all_edges = [(a, b) for a in names for b in names
                 if a != b and duck_type_leq(a, b)]
    hasse_edges = []
    for a, b in all_edges:
        is_immediate = True
        for c in names:
            if c != a and c != b and duck_type_leq(a, c) and duck_type_leq(c, b):
                is_immediate = False
                break
        if is_immediate:
            hasse_edges.append((a, b))
    return HasseDiagram(nodes=names, edges=hasse_edges)
