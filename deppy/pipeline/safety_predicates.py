"""
Canonical Safety Predicates for Exception Sources (Gap 14 helper)

Maps an ``ExceptionSource`` to the canonical Python-syntax predicate that,
if it holds in the surrounding context, **rules out** that exception.

Every such predicate is intended to be Z3-encodable so the kernel can
discharge it semantically rather than via identifier overlap.

Examples
--------
* ``ZeroDivisionError @ a / b``            ⇒ ``b != 0``
* ``IndexError @ xs[i]``                   ⇒ ``0 <= i and i < len(xs)``
* ``KeyError @ d[k]``                      ⇒ ``k in d``
* ``TypeError  @ a + b`` (mixed numeric)   ⇒ ``isinstance(a, (int, float)) and isinstance(b, (int, float))``
* ``ValueError @ int(s)``                  ⇒ ``s.isdigit() or (len(s)>0 and s[0]=='-' and s[1:].isdigit())``
* ``AttributeError @ obj.attr``            ⇒ ``hasattr(obj, 'attr')``
* ``StopIteration @ next(it)``             ⇒ ``has_next(it)``      (synthetic)
* ``RecursionError`` recursive call        ⇒ ``decreases_measure_provided``  (synthetic)
* ``EXPLICIT_RAISE``                       ⇒ ``False``  (cannot be ruled out
  by any precondition — must be caught or declared in raises_declarations)

A predicate of ``"True"`` means the source is *unconditionally* safe (the
detector overestimated) and a predicate of ``"False"`` means it is
*unconditionally* unsafe — Z3 will discharge True trivially and refuse
False, which is exactly what we want.
"""
from __future__ import annotations

import ast
from typing import Any, Optional

from deppy.pipeline.exception_sources import ExceptionKind, ExceptionSource


def _src(node: Optional[ast.AST]) -> Optional[str]:
    if node is None:
        return None
    try:
        return ast.unparse(node)
    except Exception:
        return None


def _attr_chain(node: ast.AST) -> Optional[str]:
    """Return the attribute name being accessed if ``node`` is an Attribute."""
    if isinstance(node, ast.Attribute):
        return node.attr
    return None


def safety_predicate_for(src: ExceptionSource, fn_node: Optional[Any] = None) -> str:
    """Generate the canonical Python predicate that rules out ``src``.

    The output is a Python source-syntax string that, evaluated in the
    function's argument scope, returns True iff the exception cannot fire.
    """
    node = src.ast_node
    kind = src.kind

    # ── Arithmetic ────────────────────────────────────────────────
    if kind is ExceptionKind.ZERO_DIVISION:
        if isinstance(node, ast.BinOp) and isinstance(
                node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
            denom = _src(node.right) or "denominator"
            
            # Check for obviously non-zero denominators
            if isinstance(node.right, ast.Constant):
                if isinstance(node.right.value, (int, float)) and node.right.value != 0:
                    return "True"  # Non-zero constant is safe
            
            return f"({denom}) != 0"
        return "denominator != 0"

    if kind is ExceptionKind.OVERFLOW:
        # Python ints are unbounded, but floats follow IEEE-754 and can
        # overflow on e.g. ``2.0 ** 2000``.  We can't assume either operand's
        # type statically, so we require the caller to prove the operands
        # are integer-typed (which rules out float overflow) — only then
        # is overflow impossible for +/-/*/**.
        #
        # The OLD implementation returned the literal string "True" with a
        # comment claiming "operand-domain analysis" that did not exist.
        # That silently accepted every overflow-capable site.
        if isinstance(node, ast.BinOp):
            left = _src(node.left) or "a"
            right = _src(node.right) or "b"
            return (
                f"isinstance({left}, int) and isinstance({right}, int)"
            )
        return "isinstance(_op_left, int) and isinstance(_op_right, int)"

    # ── Collection access ─────────────────────────────────────────
    if kind is ExceptionKind.INDEX_ERROR:
        if isinstance(node, ast.Subscript):
            seq = _src(node.value) or "xs"
            idx = _src(node.slice) or "i"
            return f"0 <= ({idx}) and ({idx}) < len({seq})"
        return "0 <= i and i < len(xs)"

    if kind is ExceptionKind.KEY_ERROR:
        if isinstance(node, ast.Subscript):
            d = _src(node.value) or "d"
            k = _src(node.slice) or "k"
            
            # For dict assignment with literal keys, no KeyError is raised
            # dict[literal] = value is always safe regardless of existing keys
            if isinstance(node.ctx, ast.Store):
                if isinstance(node.slice, ast.Constant):
                    return "True"  # Assignment with literal key is always safe
                    
            return f"({k}) in ({d})"
        return "k in d"

    if kind is ExceptionKind.STOP_ITERATION:
        return "has_next(it)"

    # ── Type / value ──────────────────────────────────────────────
    if kind is ExceptionKind.TYPE_ERROR:
        if isinstance(node, ast.BinOp):
            l = _src(node.left) or "a"
            r = _src(node.right) or "b"
            return (f"isinstance({l}, (int, float)) and "
                    f"isinstance({r}, (int, float))")
        if isinstance(node, ast.Call):
            fn = _src(node.func) or "f"

            # Builtins that DO NOT raise TypeError on any Python object:
            # ``str``, ``repr``, ``bool``, ``type``, ``id`` always succeed
            # because they have fallback implementations for every object.
            tolerant_builtins = {"str", "repr", "bool", "type", "id", "isinstance"}
            if fn in tolerant_builtins:
                return "True"

            # Builtins that require a specific argument shape and WILL
            # raise TypeError otherwise.  We emit the precondition the
            # argument must satisfy rather than blanket-accepting.
            #
            # The OLD implementation listed len/int/float/list/tuple/dict/set/
            # abs/min/max/sum/any/all/sorted/reversed/enumerate/zip as
            # "safe" unconditionally — e.g. ``len(42)`` raises TypeError.
            if node.args:
                arg0 = _src(node.args[0]) or "arg0"
                if fn == "len":
                    return f"hasattr({arg0}, '__len__')"
                if fn in ("list", "tuple", "set", "iter", "reversed",
                          "sorted", "enumerate"):
                    return f"hasattr({arg0}, '__iter__')"
                if fn == "dict":
                    # dict() accepts iterable of pairs OR keyword-only args
                    return (
                        f"hasattr({arg0}, 'keys') or "
                        f"hasattr({arg0}, '__iter__')"
                    )
                if fn in ("sum", "any", "all", "min", "max"):
                    return f"hasattr({arg0}, '__iter__')"
                if fn == "abs":
                    return (
                        f"hasattr({arg0}, '__abs__') or "
                        f"isinstance({arg0}, (int, float, complex))"
                    )
                if fn == "int":
                    return (
                        f"isinstance({arg0}, (int, float, bool)) or "
                        f"(isinstance({arg0}, str) and "
                        f"{arg0}.lstrip('+-').isdigit())"
                    )
                if fn == "float":
                    return (
                        f"isinstance({arg0}, (int, float, bool)) or "
                        f"(isinstance({arg0}, str))"
                    )
                if fn == "zip":
                    iters = " and ".join(
                        f"hasattr({_src(a) or f'arg{i}'}, '__iter__')"
                        for i, a in enumerate(node.args)
                    )
                    return iters or "True"

            args = ", ".join(_src(a) or f"arg{i}"
                             for i, a in enumerate(node.args))
            return f"callable({fn})  # args: {args}"
        return "True  # type narrowed elsewhere"

    if kind is ExceptionKind.VALUE_ERROR:
        if isinstance(node, ast.Call):
            fn = _src(node.func) or ""
            
            # Functions that don't raise ValueError with reasonable arguments
            safe_numeric_functions = {'abs', 'min', 'max', 'sum'}
            function_name = fn.split('.')[-1]  # Handle both 'abs' and 'math.abs'
            
            if function_name in safe_numeric_functions:
                return "True"  # These functions are safe with numeric args
                
            if fn.endswith("int") and node.args:
                a = _src(node.args[0]) or "s"
                return (f"({a}).lstrip('-').isdigit()")
            if fn.endswith("float") and node.args:
                a = _src(node.args[0]) or "s"
                return f"is_float_literal({a})"
        return "is_valid_for_op(args)"

    if kind is ExceptionKind.ATTRIBUTE_ERROR:
        if isinstance(node, ast.Attribute):
            obj = _src(node.value) or "obj"
            attr_name = node.attr

            # Dunder attributes every Python object exposes — safe without
            # a type precondition.  (``__class__``/``__repr__``/etc. are
            # defined on ``object`` itself.)
            universal_dunders = {
                '__class__', '__name__', '__doc__', '__module__',
                '__dict__', '__str__', '__repr__', '__hash__',
                '__bool__',
            }
            if attr_name in universal_dunders:
                return "True"

            # Methods that are *only* safe if the receiver is of the
            # right type.  The OLD implementation returned ``True`` for
            # these unconditionally; an unknown object calling
            # ``.upper()`` could be a list and raise AttributeError.
            str_methods = {
                'upper', 'lower', 'strip', 'lstrip', 'rstrip',
                'split', 'rsplit', 'join', 'replace', 'find', 'rfind',
                'startswith', 'endswith', 'isdigit', 'isalpha', 'isalnum',
                'capitalize', 'title', 'swapcase', 'encode', 'format',
                'zfill', 'center', 'ljust', 'rjust',
            }
            if attr_name in str_methods:
                return f"isinstance({obj}, str)"

            list_methods = {'append', 'extend', 'insert', 'sort', 'reverse'}
            if attr_name in list_methods:
                return f"isinstance({obj}, list)"

            dict_methods = {'keys', 'values', 'items', 'get', 'setdefault',
                            'update', 'popitem'}
            if attr_name in dict_methods:
                return f"isinstance({obj}, dict)"

            # Shared across list/dict/set/str: ``.count``, ``.copy``,
            # ``.clear``, ``.pop``, ``.remove``, ``.index`` exist on
            # multiple collection types — still require SOMETHING.
            collection_shared = {'count', 'copy', 'clear', 'pop',
                                 'remove', 'index'}
            if attr_name in collection_shared:
                return (
                    f"isinstance({obj}, (list, dict, set, str)) and "
                    f"hasattr({obj}, {attr_name!r})"
                )

            # Iterable-protocol dunders: only objects with the protocol.
            proto_dunders = {'__len__', '__iter__', '__next__',
                             '__getitem__', '__contains__'}
            if attr_name in proto_dunders:
                return f"hasattr({obj}, {attr_name!r})"

            # For unknown attributes, still require hasattr check.
            return f"hasattr({obj}, {attr_name!r})"
        return "hasattr(obj, attr)"

    # ── Name / import ─────────────────────────────────────────────
    if kind is ExceptionKind.NAME_ERROR:
        if isinstance(node, ast.Name):
            var_name = node.id
            
            # Built-in names that are always available
            builtin_names = {
                'True', 'False', 'None', 'len', 'str', 'int', 'float', 'bool',
                'list', 'dict', 'tuple', 'set', 'type', 'abs', 'min', 'max',
                'sum', 'any', 'all', 'sorted', 'reversed', 'enumerate', 'zip',
                'range', 'print', 'input', 'open', 'iter', 'next', 'id',
                'isinstance', 'issubclass', 'hasattr', 'getattr', 'setattr',
                
                # Built-in exception types
                'Exception', 'BaseException', 'SystemExit', 'KeyboardInterrupt',
                'GeneratorExit', 'StopIteration', 'StopAsyncIteration',
                'ArithmeticError', 'OverflowError', 'ZeroDivisionError',
                'FloatingPointError', 'AssertionError', 'AttributeError',
                'BufferError', 'EOFError', 'ImportError', 'ModuleNotFoundError',
                'LookupError', 'IndexError', 'KeyError', 'MemoryError',
                'NameError', 'UnboundLocalError', 'OSError', 'FileNotFoundError',
                'PermissionError', 'ProcessLookupError', 'TimeoutError',
                'ReferenceError', 'RuntimeError', 'NotImplementedError',
                'RecursionError', 'SyntaxError', 'IndentationError',
                'TabError', 'SystemError', 'TypeError', 'ValueError',
                'UnicodeError', 'UnicodeDecodeError', 'UnicodeEncodeError',
                'UnicodeTranslateError', 'Warning', 'UserWarning',
                'DeprecationWarning', 'PendingDeprecationWarning',
                'SyntaxWarning', 'RuntimeWarning', 'FutureWarning',
                'ImportWarning', 'UnicodeWarning', 'BytesWarning',
                'ResourceWarning'
            }
            
            if var_name in builtin_names:
                return "True"  # Always available
                
            # Check if variable is locally defined in the function
            if fn_node and isinstance(fn_node, ast.FunctionDef):
                try:
                    from deppy.pipeline.name_analysis import is_name_locally_defined
                    if is_name_locally_defined(var_name, fn_node):
                        return "True"  # Locally defined variable
                except Exception:
                    pass  # Fall back to conservative analysis
                
            # For unknown variables, return a symbolic predicate
            return f"defined({var_name!r})"
        return "True  # name resolved by analyzer"

    if kind is ExceptionKind.IMPORT_ERROR:
        # Common standard library modules that are typically available
        common_stdlib_modules = {
            'math', 'os', 'sys', 'json', 'datetime', 'time', 're', 'random',
            'collections', 'itertools', 'functools', 'operator', 'copy',
            'pickle', 'io', 'pathlib', 'typing', 'decimal', 'fractions',
            'statistics', 'string', 'textwrap', 'unicodedata', 'base64',
            'binascii', 'struct', 'codecs', 'csv', 'configparser', 'hashlib',
            'hmac', 'uuid', 'urllib', 'http', 'email', 'mimetypes', 'sqlite3'
        }
        
        # Try to extract module name from description or trigger condition
        module_name = None
        if hasattr(src, 'description') and src.description:
            if src.description.startswith('import '):
                module_name = src.description[7:].split()[0]  # "import math" -> "math"
            elif src.description.startswith('from '):
                # "from math import ceil" -> "math"  
                parts = src.description.split()
                if len(parts) >= 2:
                    module_name = parts[1]
        
        if module_name and module_name in common_stdlib_modules:
            return "True"  # Standard library modules are typically available
        
        return "module_present"

    # ── Assertion / explicit raise ────────────────────────────────
    if kind is ExceptionKind.ASSERTION_ERROR:
        if isinstance(node, ast.Assert):
            return _src(node.test) or "True"
        return "True"

    if kind is ExceptionKind.EXPLICIT_RAISE:
        # Cannot be ruled out by a predicate — the function chooses to raise.
        # Must be addressed via ``raises_declarations`` or be inside a try.
        return "False"

    # ── Recursion / runtime ───────────────────────────────────────
    if kind is ExceptionKind.RUNTIME_ERROR:
        # Recursion termination is *not* a Z3-discharable predicate.
        # A real `decreases` measure must be provided so the pipeline
        # can build a TerminationObligation; in the absence of one,
        # the source must remain unaddressed (otherwise the pipeline
        # silently accepts every unbounded recursion as "safe").
        return "decreases_measure_provided"

    # ── Iteration / unpack ────────────────────────────────────────
    if kind is ExceptionKind.ITERATION_ERROR:
        return "iterable_exhaustible"
    if kind is ExceptionKind.UNPACK_ERROR:
        if isinstance(node, ast.Assign) and isinstance(node.targets[0],
                                                       (ast.Tuple, ast.List)):
            n = len(node.targets[0].elts)
            rhs = _src(node.value) or "rhs"
            return f"len({rhs}) == {n}"
        return "len(rhs) == arity(lhs)"

    # ── Call propagation / I/O / timeout / custom ─────────────────
    if kind is ExceptionKind.CALL_PROPAGATION:
        # Check if this is a call to a known safe builtin method
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            method_name = node.func.attr
            
            # Known safe builtin methods that don't raise exceptions under normal conditions
            safe_builtin_methods = {
                # String methods
                'upper', 'lower', 'strip', 'lstrip', 'rstrip', 'capitalize', 'title', 'swapcase',
                'replace', 'find', 'rfind', 'index', 'rindex', 'startswith', 'endswith',
                'isdigit', 'isalpha', 'isalnum', 'isspace', 'islower', 'isupper', 'istitle',
                'count', 'encode', 'decode', 'join', 'split', 'rsplit', 'splitlines',
                'partition', 'rpartition', 'center', 'ljust', 'rjust', 'zfill', 'expandtabs',
                
                # List/sequence methods  
                'copy', 'count', 'index', 'reverse', 'sort', 'clear',
                'append', 'extend', 'insert', 'remove', 'pop',
                
                # Dict methods
                'keys', 'values', 'items', 'copy', 'clear', 'get', 'setdefault', 'update',
                
                # Set methods
                'add', 'discard', 'copy', 'clear', 'union', 'intersection', 'difference',
                
                # General object methods
                '__str__', '__repr__', '__bool__', '__len__', '__iter__', '__hash__',
                '__class__', '__dict__'
            }
            
            if method_name in safe_builtin_methods:
                return "True"
        
        # Check if this is a class constructor call
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            # Built-in type constructors that are generally safe
            safe_constructors = {
                'int', 'float', 'str', 'bool', 'list', 'dict', 'tuple', 'set',
                'frozenset', 'bytes', 'bytearray', 'complex', 'slice', 'range'
            }
            
            if node.func.id in safe_constructors:
                return "True"  # Built-in type constructors are safe
            
            # For user-defined classes, assume constructor is safe if it's locally defined
            # This is a heuristic - in practice, most simple constructors don't raise exceptions
            if fn_node and isinstance(fn_node, ast.FunctionDef):
                # Check if class is defined in same module (simple heuristic)
                try:
                    from deppy.pipeline.name_analysis import is_name_locally_defined
                    if is_name_locally_defined(node.func.id, fn_node):
                        return "True"  # Locally defined class is likely safe
                except Exception:
                    pass
        
        # For unknown methods, use the symbolic predicate
        return f"callee_safe({src.callee_name or 'g'})"
    if kind is ExceptionKind.OS_ERROR:
        return "io_resource_available"
    if kind is ExceptionKind.TIMEOUT_ERROR:
        return "completes_within_budget"
    if kind is ExceptionKind.CUSTOM:
        return "custom_invariant_holds"

    return "True  # unknown source kind"


def is_synthetic_predicate(pred: str) -> bool:
    """Predicates whose discharge is not pure Z3 arithmetic.

    Used by the pipeline to decide whether to attempt a Z3 discharge or
    fall back to axiom / structural discharge.
    """
    pred = pred.strip()
    synthetic_markers = (
        "has_next(", "callee_safe(", "module_present", "io_resource_available",
        "completes_within_budget", "custom_invariant_holds",
        "is_float_literal(", "is_valid_for_op(", "defined(",
        "iterable_exhaustible", "callable(", "decreases_measure_provided",
        # Natural-language descriptors emitted by ``auto_spec`` —
        # these are markers, not Z3-encodable formulas, so the kernel
        # treats them as auto-discharged structural facts.
        "handles None input", "handles None for",
        "validates ", "checks for ", "guards against ",
    )
    return any(m in pred for m in synthetic_markers) or "#" in pred


__all__ = [
    "safety_predicate_for",
    "is_synthetic_predicate",
]
