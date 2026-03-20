"""
Python operational semantics modeled as a formal IR suitable for translation to Lean 4.

This module provides a complete intermediate representation of Python programs,
covering types, values, expressions, statements, functions, classes, and modules.
Each IR node can render itself as Lean 4 syntax, enabling automated translation
of Python programs into formally verifiable Lean 4 code.
"""
from __future__ import annotations

import ast
import enum
import textwrap
from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Optional, Set, Tuple, Union


# ---------------------------------------------------------------------------
# Section 1: PyLiteral & PyType  (~200 lines)
# ---------------------------------------------------------------------------


# --- Integration with existing deppy codebase ---
try:
    from deppy.types.base import TypeBase, PrimitiveType, type_from_python
    from deppy.types.dependent import PiType, SigmaType
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

class PyLiteral(enum.Enum):
    """Primitive literal kinds recognised by the IR."""
    INT = "Int"
    FLOAT = "Float"
    BOOL = "Bool"
    STR = "String"
    NONE = "Unit"
    BYTES = "ByteArray"

    def to_lean(self) -> str:
        return self.value


class PyType:
    """Base class for all IR types."""

    def to_lean(self) -> str:
        raise NotImplementedError

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, PyType):
            return NotImplemented
        return type(self) is type(other) and self.__dict__ == other.__dict__

    def __hash__(self) -> int:
        return hash(repr(self))

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.to_lean()})"

    def is_numeric(self) -> bool:
        return False

    def is_bool(self) -> bool:
        return False

    def is_string(self) -> bool:
        return False

    def is_none(self) -> bool:
        return False

    def is_optional(self) -> bool:
        return isinstance(self, PyOptionalType)

    def is_function(self) -> bool:
        return isinstance(self, PyFunctionType)

    def is_collection(self) -> bool:
        return isinstance(self, (PyListType, PyDictType, PyTupleType, PySetType))


@dataclass(frozen=True)
class PyPrimitiveType(PyType):
    """Wraps a PyLiteral as a type."""
    literal: PyLiteral

    def to_lean(self) -> str:
        return self.literal.to_lean()

    def is_numeric(self) -> bool:
        return self.literal in (PyLiteral.INT, PyLiteral.FLOAT)

    def is_bool(self) -> bool:
        return self.literal is PyLiteral.BOOL

    def is_string(self) -> bool:
        return self.literal is PyLiteral.STR

    def is_none(self) -> bool:
        return self.literal is PyLiteral.NONE


@dataclass(frozen=True)
class PyListType(PyType):
    """Homogeneous list type."""
    element: PyType

    def to_lean(self) -> str:
        return f"List {self.element.to_lean()}"


@dataclass(frozen=True)
class PyDictType(PyType):
    """Dictionary / mapping type."""
    key: PyType
    value: PyType

    def to_lean(self) -> str:
        return f"Std.HashMap {self.key.to_lean()} {self.value.to_lean()}"


@dataclass(frozen=True)
class PyTupleType(PyType):
    """Fixed-length product type."""
    elements: Tuple[PyType, ...]

    def to_lean(self) -> str:
        if not self.elements:
            return "Unit"
        if len(self.elements) == 1:
            return self.elements[0].to_lean()
        inner = " × ".join(e.to_lean() for e in self.elements)
        return f"({inner})"


@dataclass(frozen=True)
class PySetType(PyType):
    """Homogeneous set type."""
    element: PyType

    def to_lean(self) -> str:
        return f"Std.HashSet {self.element.to_lean()}"


@dataclass(frozen=True)
class PyOptionalType(PyType):
    """Optional wrapper — translates to Option in Lean."""
    inner: PyType

    def to_lean(self) -> str:
        return f"Option {self.inner.to_lean()}"


@dataclass(frozen=True)
class PyUnionType(PyType):
    """Tagged union — encoded as a Lean sum type."""
    alternatives: Tuple[PyType, ...]

    def to_lean(self) -> str:
        if not self.alternatives:
            return "Empty"
        if len(self.alternatives) == 1:
            return self.alternatives[0].to_lean()
        parts = " ⊕ ".join(a.to_lean() for a in self.alternatives)
        return f"({parts})"


@dataclass(frozen=True)
class PyFunctionType(PyType):
    """Arrow type for callables."""
    params: Tuple[PyType, ...]
    return_type: PyType

    def to_lean(self) -> str:
        if not self.params:
            return f"Unit → {self.return_type.to_lean()}"
        parts = " → ".join(p.to_lean() for p in self.params)
        return f"{parts} → {self.return_type.to_lean()}"


@dataclass(frozen=True)
class PyClassType(PyType):
    """Structural class type — maps to a Lean structure."""
    name: str
    fields: Dict[str, PyType]
    methods: Dict[str, PyFunctionType]

    def __hash__(self) -> int:
        return hash(self.name)

    def to_lean(self) -> str:
        return self.name


@dataclass(frozen=True)
class PyRefinedType(PyType):
    """Refinement type for hybrid verification integration."""
    base: PyType
    predicate: str

    def to_lean(self) -> str:
        return f"{{ x : {self.base.to_lean()} // {self.predicate} }}"


# Convenience singletons
PY_INT = PyPrimitiveType(PyLiteral.INT)
PY_FLOAT = PyPrimitiveType(PyLiteral.FLOAT)
PY_BOOL = PyPrimitiveType(PyLiteral.BOOL)
PY_STR = PyPrimitiveType(PyLiteral.STR)
PY_NONE = PyPrimitiveType(PyLiteral.NONE)
PY_BYTES = PyPrimitiveType(PyLiteral.BYTES)

_BUILTIN_NAME_TO_TYPE: Dict[str, PyType] = {
    "int": PY_INT,
    "float": PY_FLOAT,
    "bool": PY_BOOL,
    "str": PY_STR,
    "None": PY_NONE,
    "bytes": PY_BYTES,
    "NoneType": PY_NONE,
}


def _annotation_to_type(node: Optional[ast.expr]) -> Optional[PyType]:
    """Best-effort conversion of an AST annotation node to a PyType."""
    if node is None:
        return None
    if isinstance(node, ast.Constant):
        if node.value is None:
            return PY_NONE
        return _BUILTIN_NAME_TO_TYPE.get(str(node.value))
    if isinstance(node, ast.Name):
        return _BUILTIN_NAME_TO_TYPE.get(node.id, PyClassType(node.id, {}, {}))
    if isinstance(node, ast.Attribute):
        return PyClassType(ast.dump(node), {}, {})
    if isinstance(node, ast.Subscript):
        base = node.value
        if isinstance(base, ast.Name):
            if base.id == "List":
                inner = _annotation_to_type(node.slice)
                return PyListType(inner or PY_NONE)
            if base.id == "Dict":
                if isinstance(node.slice, ast.Tuple) and len(node.slice.elts) == 2:
                    kt = _annotation_to_type(node.slice.elts[0]) or PY_STR
                    vt = _annotation_to_type(node.slice.elts[1]) or PY_NONE
                    return PyDictType(kt, vt)
                return PyDictType(PY_STR, PY_NONE)
            if base.id == "Set":
                inner = _annotation_to_type(node.slice)
                return PySetType(inner or PY_NONE)
            if base.id == "Tuple":
                if isinstance(node.slice, ast.Tuple):
                    elts = tuple(
                        _annotation_to_type(e) or PY_NONE for e in node.slice.elts
                    )
                    return PyTupleType(elts)
                inner = _annotation_to_type(node.slice)
                return PyTupleType((inner or PY_NONE,))
            if base.id == "Optional":
                inner = _annotation_to_type(node.slice)
                return PyOptionalType(inner or PY_NONE)
            if base.id == "Union":
                if isinstance(node.slice, ast.Tuple):
                    alts = tuple(
                        _annotation_to_type(e) or PY_NONE for e in node.slice.elts
                    )
                    return PyUnionType(alts)
                inner = _annotation_to_type(node.slice)
                return PyUnionType((inner or PY_NONE,))
    return None


# ---------------------------------------------------------------------------
# Section 2: PyValue  (~300 lines)
# ---------------------------------------------------------------------------

class PyValue:
    """Base class for runtime IR values."""

    def to_lean_term(self) -> str:
        raise NotImplementedError

    def typeof(self) -> PyType:
        raise NotImplementedError

    def to_python_literal(self) -> str:
        raise NotImplementedError

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, PyValue):
            return NotImplemented
        return type(self) is type(other) and self.__dict__ == other.__dict__

    def __hash__(self) -> int:
        return hash(repr(self))

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.to_python_literal()})"

    def is_truthy(self) -> bool:
        """Python truthiness semantics."""
        return True


@dataclass(frozen=True)
class PyIntVal(PyValue):
    value: int

    def to_lean_term(self) -> str:
        if self.value < 0:
            return f"({self.value})"
        return str(self.value)

    def typeof(self) -> PyType:
        return PY_INT

    def to_python_literal(self) -> str:
        return str(self.value)

    def is_truthy(self) -> bool:
        return self.value != 0


@dataclass(frozen=True)
class PyFloatVal(PyValue):
    value: float

    def to_lean_term(self) -> str:
        s = repr(self.value)
        if "." not in s and "e" not in s and "E" not in s and s not in ("inf", "-inf", "nan"):
            s += ".0"
        if self.value < 0:
            return f"({s})"
        return s

    def typeof(self) -> PyType:
        return PY_FLOAT

    def to_python_literal(self) -> str:
        return repr(self.value)

    def is_truthy(self) -> bool:
        return self.value != 0.0


@dataclass(frozen=True)
class PyBoolVal(PyValue):
    value: bool

    def to_lean_term(self) -> str:
        return "true" if self.value else "false"

    def typeof(self) -> PyType:
        return PY_BOOL

    def to_python_literal(self) -> str:
        return "True" if self.value else "False"

    def is_truthy(self) -> bool:
        return self.value


@dataclass(frozen=True)
class PyStrVal(PyValue):
    value: str

    def to_lean_term(self) -> str:
        escaped = self.value.replace("\\", "\\\\").replace('"', '\\"')
        return f'"{escaped}"'

    def typeof(self) -> PyType:
        return PY_STR

    def to_python_literal(self) -> str:
        return repr(self.value)

    def is_truthy(self) -> bool:
        return len(self.value) > 0


@dataclass(frozen=True)
class PyNoneVal(PyValue):
    def to_lean_term(self) -> str:
        return "()"

    def typeof(self) -> PyType:
        return PY_NONE

    def to_python_literal(self) -> str:
        return "None"

    def is_truthy(self) -> bool:
        return False


@dataclass(frozen=True)
class PyBytesVal(PyValue):
    value: bytes

    def to_lean_term(self) -> str:
        elems = ", ".join(str(b) for b in self.value)
        return f"#[{elems}]"

    def typeof(self) -> PyType:
        return PY_BYTES

    def to_python_literal(self) -> str:
        return repr(self.value)

    def is_truthy(self) -> bool:
        return len(self.value) > 0


@dataclass
class PyListVal(PyValue):
    elements: List[PyValue]

    def to_lean_term(self) -> str:
        elems = ", ".join(e.to_lean_term() for e in self.elements)
        return f"[{elems}]"

    def typeof(self) -> PyType:
        if not self.elements:
            return PyListType(PY_NONE)
        return PyListType(self.elements[0].typeof())

    def to_python_literal(self) -> str:
        elems = ", ".join(e.to_python_literal() for e in self.elements)
        return f"[{elems}]"

    def is_truthy(self) -> bool:
        return len(self.elements) > 0

    def __hash__(self) -> int:
        return hash(("list", tuple(self.elements)))


@dataclass
class PyDictVal(PyValue):
    entries: Dict[PyValue, PyValue]

    def to_lean_term(self) -> str:
        if not self.entries:
            return "Std.HashMap.empty"
        pairs = ", ".join(
            f"({k.to_lean_term()}, {v.to_lean_term()})" for k, v in self.entries.items()
        )
        return f"Std.HashMap.ofList [{pairs}]"

    def typeof(self) -> PyType:
        if not self.entries:
            return PyDictType(PY_STR, PY_NONE)
        k0 = next(iter(self.entries.keys()))
        v0 = next(iter(self.entries.values()))
        return PyDictType(k0.typeof(), v0.typeof())

    def to_python_literal(self) -> str:
        pairs = ", ".join(
            f"{k.to_python_literal()}: {v.to_python_literal()}"
            for k, v in self.entries.items()
        )
        return "{" + pairs + "}"

    def is_truthy(self) -> bool:
        return len(self.entries) > 0

    def __hash__(self) -> int:
        return hash(("dict", tuple(self.entries.items())))


@dataclass
class PyTupleVal(PyValue):
    elements: List[PyValue]

    def to_lean_term(self) -> str:
        if not self.elements:
            return "()"
        if len(self.elements) == 1:
            return self.elements[0].to_lean_term()
        inner = ", ".join(e.to_lean_term() for e in self.elements)
        return f"({inner})"

    def typeof(self) -> PyType:
        return PyTupleType(tuple(e.typeof() for e in self.elements))

    def to_python_literal(self) -> str:
        if len(self.elements) == 1:
            return f"({self.elements[0].to_python_literal()},)"
        inner = ", ".join(e.to_python_literal() for e in self.elements)
        return f"({inner})"

    def is_truthy(self) -> bool:
        return len(self.elements) > 0

    def __hash__(self) -> int:
        return hash(("tuple", tuple(self.elements)))


@dataclass
class PySetVal(PyValue):
    elements: FrozenSet[PyValue]

    def to_lean_term(self) -> str:
        if not self.elements:
            return "Std.HashSet.empty"
        elems = ", ".join(e.to_lean_term() for e in sorted(self.elements, key=repr))
        return f"Std.HashSet.ofList [{elems}]"

    def typeof(self) -> PyType:
        if not self.elements:
            return PySetType(PY_NONE)
        return PySetType(next(iter(self.elements)).typeof())

    def to_python_literal(self) -> str:
        if not self.elements:
            return "set()"
        elems = ", ".join(
            e.to_python_literal() for e in sorted(self.elements, key=repr)
        )
        return "{" + elems + "}"

    def is_truthy(self) -> bool:
        return len(self.elements) > 0

    def __hash__(self) -> int:
        return hash(("set", self.elements))


@dataclass
class PyObjectVal(PyValue):
    class_name: str
    fields: Dict[str, PyValue]

    def to_lean_term(self) -> str:
        if not self.fields:
            return f"{self.class_name}.mk"
        assigns = " ".join(
            f"({k} := {v.to_lean_term()})" for k, v in self.fields.items()
        )
        return f"{{ {assigns} }}"

    def typeof(self) -> PyType:
        ftypes = {k: v.typeof() for k, v in self.fields.items()}
        return PyClassType(self.class_name, ftypes, {})

    def to_python_literal(self) -> str:
        args = ", ".join(
            f"{k}={v.to_python_literal()}" for k, v in self.fields.items()
        )
        return f"{self.class_name}({args})"

    def __hash__(self) -> int:
        return hash(("obj", self.class_name, tuple(sorted(self.fields.items()))))


# Forward reference: PyStmt is used inside PyFuncVal but defined later.
# We use a string annotation with TYPE_CHECKING to avoid circular issues at runtime.

@dataclass
class PyFuncVal(PyValue):
    name: str
    params: List[str]
    body: PyStmt  # type: ignore[forward-ref]

    def to_lean_term(self) -> str:
        param_str = " ".join(self.params) if self.params else "()"
        return f"fun {param_str} => {self.body.to_lean()}"

    def typeof(self) -> PyType:
        ptypes = tuple(PY_NONE for _ in self.params)
        return PyFunctionType(ptypes, PY_NONE)

    def to_python_literal(self) -> str:
        return f"<function {self.name}>"

    def __hash__(self) -> int:
        return hash(("func", self.name, tuple(self.params)))


# ---------------------------------------------------------------------------
# Section 3: PyExpr  (~500 lines)
# ---------------------------------------------------------------------------

class BinOp(enum.Enum):
    ADD = "+"
    SUB = "-"
    MUL = "*"
    DIV = "/"
    FLOORDIV = "//"
    MOD = "%"
    POW = "**"
    LSHIFT = "<<"
    RSHIFT = ">>"
    BITOR = "|"
    BITXOR = "^"
    BITAND = "&"
    MATMUL = "@"

    def to_lean(self) -> str:
        _map: Dict[str, str] = {
            "+": "+", "-": "-", "*": "*", "/": "/",
            "//": "/", "%": "%", "**": "^",
            "<<": "<<<", ">>": ">>>",
            "|": "|||", "^": "^^^", "&": "&&&",
            "@": "⬝",
        }
        return _map.get(self.value, self.value)

    def to_python(self) -> str:
        return self.value


class UnaryOp(enum.Enum):
    UADD = "+"
    USUB = "-"
    NOT = "not"
    INVERT = "~"

    def to_lean(self) -> str:
        _map = {"+": "+", "-": "-", "not": "¬", "~": "~~~"}
        return _map.get(self.value, self.value)

    def to_python(self) -> str:
        return self.value


class CmpOp(enum.Enum):
    EQ = "=="
    NE = "!="
    LT = "<"
    LE = "<="
    GT = ">"
    GE = ">="
    IS = "is"
    ISNOT = "is not"
    IN = "in"
    NOTIN = "not in"

    def to_lean(self) -> str:
        _map: Dict[str, str] = {
            "==": "==", "!=": "!=", "<": "<", "<=": "<=",
            ">": ">", ">=": ">=",
            "is": "==", "is not": "!=",
            "in": "∈", "not in": "∉",
        }
        return _map.get(self.value, self.value)

    def to_python(self) -> str:
        return self.value


@dataclass
class Comprehension:
    """Represents a single `for ... in ... if ...` clause."""
    target: str
    iter_expr: PyExpr
    conditions: List[PyExpr]

    def to_lean(self) -> str:
        base = f"for {self.target} in {self.iter_expr.to_lean()}"
        for c in self.conditions:
            base += f" if {c.to_lean()}"
        return base

    def free_vars(self) -> Set[str]:
        result = self.iter_expr.free_vars()
        for c in self.conditions:
            result |= c.free_vars()
        result.discard(self.target)
        return result


class PyExpr:
    """Base class for all expression IR nodes."""

    def to_lean(self) -> str:
        raise NotImplementedError

    def typeof(self, env: TypeEnv) -> PyType:
        return PY_NONE

    def free_vars(self) -> Set[str]:
        return set()

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, PyExpr):
            return NotImplemented
        return type(self) is type(other) and self.__dict__ == other.__dict__

    def __hash__(self) -> int:
        return hash(repr(self))

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}(...)"

    def is_constant(self) -> bool:
        return False

    def is_pure(self) -> bool:
        """Conservative purity check — no side effects."""
        return False


@dataclass
class PyVar(PyExpr):
    name: str

    def to_lean(self) -> str:
        return _lean_ident(self.name)

    def typeof(self, env: TypeEnv) -> PyType:
        return env.lookup(self.name) or PY_NONE

    def free_vars(self) -> Set[str]:
        return {self.name}

    def is_pure(self) -> bool:
        return True


@dataclass
class PyLit(PyExpr):
    value: PyValue

    def to_lean(self) -> str:
        return self.value.to_lean_term()

    def typeof(self, env: TypeEnv) -> PyType:
        return self.value.typeof()

    def free_vars(self) -> Set[str]:
        return set()

    def is_constant(self) -> bool:
        return True

    def is_pure(self) -> bool:
        return True


@dataclass
class PyBinOp(PyExpr):
    op: BinOp
    left: PyExpr
    right: PyExpr

    def to_lean(self) -> str:
        return f"({self.left.to_lean()} {self.op.to_lean()} {self.right.to_lean()})"

    def typeof(self, env: TypeEnv) -> PyType:
        lt = self.left.typeof(env)
        rt = self.right.typeof(env)
        if self.op is BinOp.DIV:
            return PY_FLOAT
        if isinstance(lt, PyPrimitiveType) and isinstance(rt, PyPrimitiveType):
            if lt.literal is PyLiteral.FLOAT or rt.literal is PyLiteral.FLOAT:
                return PY_FLOAT
            if lt.literal is PyLiteral.INT and rt.literal is PyLiteral.INT:
                return PY_INT
        if self.op is BinOp.ADD:
            if isinstance(lt, PyPrimitiveType) and lt.literal is PyLiteral.STR:
                return PY_STR
            if isinstance(lt, PyListType):
                return lt
        return PY_NONE

    def free_vars(self) -> Set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def is_pure(self) -> bool:
        return self.left.is_pure() and self.right.is_pure()


@dataclass
class PyUnaryOp(PyExpr):
    op: UnaryOp
    operand: PyExpr

    def to_lean(self) -> str:
        return f"({self.op.to_lean()} {self.operand.to_lean()})"

    def typeof(self, env: TypeEnv) -> PyType:
        if self.op is UnaryOp.NOT:
            return PY_BOOL
        return self.operand.typeof(env)

    def free_vars(self) -> Set[str]:
        return self.operand.free_vars()

    def is_pure(self) -> bool:
        return self.operand.is_pure()


@dataclass
class PyCompare(PyExpr):
    ops: List[CmpOp]
    left: PyExpr
    comparators: List[PyExpr]

    def to_lean(self) -> str:
        parts = [self.left.to_lean()]
        for op, comp in zip(self.ops, self.comparators):
            parts.append(op.to_lean())
            parts.append(comp.to_lean())
        return f"({' '.join(parts)})"

    def typeof(self, env: TypeEnv) -> PyType:
        return PY_BOOL

    def free_vars(self) -> Set[str]:
        result = self.left.free_vars()
        for c in self.comparators:
            result |= c.free_vars()
        return result

    def is_pure(self) -> bool:
        return self.left.is_pure() and all(c.is_pure() for c in self.comparators)


@dataclass
class PyCall(PyExpr):
    func: PyExpr
    args: List[PyExpr]
    kwargs: Dict[str, PyExpr]

    def to_lean(self) -> str:
        arg_strs = [a.to_lean() for a in self.args]
        for k, v in self.kwargs.items():
            arg_strs.append(f"({k} := {v.to_lean()})")
        args_joined = " ".join(arg_strs) if arg_strs else "()"
        return f"{self.func.to_lean()} {args_joined}"

    def typeof(self, env: TypeEnv) -> PyType:
        ft = self.func.typeof(env)
        if isinstance(ft, PyFunctionType):
            return ft.return_type
        return PY_NONE

    def free_vars(self) -> Set[str]:
        result = self.func.free_vars()
        for a in self.args:
            result |= a.free_vars()
        for v in self.kwargs.values():
            result |= v.free_vars()
        return result


@dataclass
class PyMethodCall(PyExpr):
    obj: PyExpr
    method: str
    args: List[PyExpr]

    def to_lean(self) -> str:
        arg_strs = " ".join(a.to_lean() for a in self.args)
        call = f"{self.obj.to_lean()}.{_lean_ident(self.method)}"
        if arg_strs:
            call += f" {arg_strs}"
        return call

    def typeof(self, env: TypeEnv) -> PyType:
        ot = self.obj.typeof(env)
        if isinstance(ot, PyClassType) and self.method in ot.methods:
            return ot.methods[self.method].return_type
        if isinstance(ot, PyListType) and self.method == "append":
            return PY_NONE
        if isinstance(ot, PyPrimitiveType) and ot.literal is PyLiteral.STR:
            return PY_STR
        return PY_NONE

    def free_vars(self) -> Set[str]:
        result = self.obj.free_vars()
        for a in self.args:
            result |= a.free_vars()
        return result


@dataclass
class PySubscript(PyExpr):
    obj: PyExpr
    index: PyExpr

    def to_lean(self) -> str:
        return f"{self.obj.to_lean()}[{self.index.to_lean()}]"

    def typeof(self, env: TypeEnv) -> PyType:
        ot = self.obj.typeof(env)
        if isinstance(ot, PyListType):
            return ot.element
        if isinstance(ot, PyDictType):
            return ot.value
        if isinstance(ot, PyTupleType) and ot.elements:
            return ot.elements[0]
        if isinstance(ot, PyPrimitiveType) and ot.literal is PyLiteral.STR:
            return PY_STR
        return PY_NONE

    def free_vars(self) -> Set[str]:
        return self.obj.free_vars() | self.index.free_vars()


@dataclass
class PySlice(PyExpr):
    obj: PyExpr
    lower: Optional[PyExpr]
    upper: Optional[PyExpr]
    step: Optional[PyExpr]

    def to_lean(self) -> str:
        lo = self.lower.to_lean() if self.lower else "0"
        hi = self.upper.to_lean() if self.upper else "none"
        if self.step:
            return f"List.slice {self.obj.to_lean()} {lo} {hi} {self.step.to_lean()}"
        return f"List.slice {self.obj.to_lean()} {lo} {hi}"

    def typeof(self, env: TypeEnv) -> PyType:
        return self.obj.typeof(env)

    def free_vars(self) -> Set[str]:
        result = self.obj.free_vars()
        if self.lower:
            result |= self.lower.free_vars()
        if self.upper:
            result |= self.upper.free_vars()
        if self.step:
            result |= self.step.free_vars()
        return result


@dataclass
class PyAttribute(PyExpr):
    obj: PyExpr
    attr: str

    def to_lean(self) -> str:
        return f"{self.obj.to_lean()}.{_lean_ident(self.attr)}"

    def typeof(self, env: TypeEnv) -> PyType:
        ot = self.obj.typeof(env)
        if isinstance(ot, PyClassType) and self.attr in ot.fields:
            return ot.fields[self.attr]
        return PY_NONE

    def free_vars(self) -> Set[str]:
        return self.obj.free_vars()

    def is_pure(self) -> bool:
        return self.obj.is_pure()


@dataclass
class PyTernary(PyExpr):
    test: PyExpr
    body: PyExpr
    orelse: PyExpr

    def to_lean(self) -> str:
        return (
            f"if {self.test.to_lean()} then {self.body.to_lean()} "
            f"else {self.orelse.to_lean()}"
        )

    def typeof(self, env: TypeEnv) -> PyType:
        return self.body.typeof(env)

    def free_vars(self) -> Set[str]:
        return self.test.free_vars() | self.body.free_vars() | self.orelse.free_vars()

    def is_pure(self) -> bool:
        return self.test.is_pure() and self.body.is_pure() and self.orelse.is_pure()


@dataclass
class PyListComp(PyExpr):
    elt: PyExpr
    generators: List[Comprehension]

    def to_lean(self) -> str:
        result = "do\n"
        for gen in self.generators:
            result += f"  let mut __acc := []\n"
            result += f"  for {gen.target} in {gen.iter_expr.to_lean()} do\n"
            for cond in gen.conditions:
                result += f"    if {cond.to_lean()} then\n"
            result += f"      __acc := __acc ++ [{self.elt.to_lean()}]\n"
        result += "  __acc"
        return result

    def typeof(self, env: TypeEnv) -> PyType:
        child = env.child()
        for gen in self.generators:
            iter_type = gen.iter_expr.typeof(env)
            if isinstance(iter_type, PyListType):
                child.bind(gen.target, iter_type.element)
            else:
                child.bind(gen.target, PY_NONE)
        return PyListType(self.elt.typeof(child))

    def free_vars(self) -> Set[str]:
        result: Set[str] = set()
        bound: Set[str] = set()
        for gen in self.generators:
            result |= gen.free_vars() - bound
            bound.add(gen.target)
        result |= self.elt.free_vars() - bound
        return result


@dataclass
class PyDictComp(PyExpr):
    key: PyExpr
    value: PyExpr
    generators: List[Comprehension]

    def to_lean(self) -> str:
        result = "do\n"
        for gen in self.generators:
            result += f"  let mut __acc := Std.HashMap.empty\n"
            result += f"  for {gen.target} in {gen.iter_expr.to_lean()} do\n"
            for cond in gen.conditions:
                result += f"    if {cond.to_lean()} then\n"
            result += (
                f"      __acc := __acc.insert "
                f"{self.key.to_lean()} {self.value.to_lean()}\n"
            )
        result += "  __acc"
        return result

    def typeof(self, env: TypeEnv) -> PyType:
        child = env.child()
        for gen in self.generators:
            iter_type = gen.iter_expr.typeof(env)
            if isinstance(iter_type, PyListType):
                child.bind(gen.target, iter_type.element)
            else:
                child.bind(gen.target, PY_NONE)
        return PyDictType(self.key.typeof(child), self.value.typeof(child))

    def free_vars(self) -> Set[str]:
        result: Set[str] = set()
        bound: Set[str] = set()
        for gen in self.generators:
            result |= gen.free_vars() - bound
            bound.add(gen.target)
        result |= self.key.free_vars() - bound
        result |= self.value.free_vars() - bound
        return result


@dataclass
class PyLambda(PyExpr):
    args: List[str]
    body: PyExpr

    def to_lean(self) -> str:
        params = " ".join(self.args) if self.args else "()"
        return f"fun {params} => {self.body.to_lean()}"

    def typeof(self, env: TypeEnv) -> PyType:
        child = env.child()
        for a in self.args:
            child.bind(a, PY_NONE)
        ret = self.body.typeof(child)
        return PyFunctionType(tuple(PY_NONE for _ in self.args), ret)

    def free_vars(self) -> Set[str]:
        return self.body.free_vars() - set(self.args)

    def is_pure(self) -> bool:
        return self.body.is_pure()


@dataclass
class PyFString(PyExpr):
    parts: List[Union[str, PyExpr]]

    def to_lean(self) -> str:
        pieces: List[str] = []
        for part in self.parts:
            if isinstance(part, str):
                pieces.append(part.replace("{", "{{").replace("}", "}}"))
            else:
                pieces.append(f"s!\"{{{part.to_lean()}}}\"")
        return 's!"' + "".join(
            p if isinstance(p, str) else f"{{{p.to_lean()}}}"
            for p in self.parts
        ) + '"'

    def typeof(self, env: TypeEnv) -> PyType:
        return PY_STR

    def free_vars(self) -> Set[str]:
        result: Set[str] = set()
        for part in self.parts:
            if isinstance(part, PyExpr):
                result |= part.free_vars()
        return result


@dataclass
class PyStarExpr(PyExpr):
    value: PyExpr

    def to_lean(self) -> str:
        return f"(List.join [{self.value.to_lean()}])"

    def typeof(self, env: TypeEnv) -> PyType:
        return self.value.typeof(env)

    def free_vars(self) -> Set[str]:
        return self.value.free_vars()


# ---------------------------------------------------------------------------
# Lean identifier escaping
# ---------------------------------------------------------------------------

_LEAN_KEYWORDS: FrozenSet[str] = frozenset({
    "def", "let", "do", "if", "then", "else", "match", "with", "where",
    "have", "show", "fun", "return", "for", "in", "open", "import",
    "namespace", "section", "end", "class", "instance", "structure",
    "inductive", "theorem", "lemma", "example", "set_option",
    "variable", "axiom", "noncomputable", "partial", "unsafe",
    "private", "protected", "mutual", "macro", "syntax", "notation",
    "attribute", "derive", "extends", "true", "false", "Type", "Prop",
    "Sort", "by", "at", "try", "catch", "throw", "break", "continue",
})


def _lean_ident(name: str) -> str:
    """Escape a Python identifier for use in Lean 4."""
    if name in _LEAN_KEYWORDS:
        return f"«{name}»"
    if not name.isidentifier():
        return f"«{name}»"
    return name


# ---------------------------------------------------------------------------
# Section 4: PyStmt  (~400 lines)
# ---------------------------------------------------------------------------

@dataclass
class ExceptHandler:
    """A single except clause."""
    exc_type: Optional[str]
    name: Optional[str]
    body: List[PyStmt]

    def to_lean(self, indent: int = 2) -> str:
        pad = " " * indent
        exc = self.exc_type or "Exception"
        name = self.name or "_"
        lines = [f"{pad}| {exc}.mk {name} =>"]
        for s in self.body:
            lines.append(f"{pad}  {s.to_lean()}")
        return "\n".join(lines)

    def defined_vars(self) -> Set[str]:
        result: Set[str] = set()
        if self.name:
            result.add(self.name)
        for s in self.body:
            result |= s.defined_vars()
        return result

    def used_vars(self) -> Set[str]:
        result: Set[str] = set()
        for s in self.body:
            result |= s.used_vars()
        return result


@dataclass
class WithItem:
    """A single item in a `with` statement."""
    context_expr: PyExpr
    optional_var: Optional[str]

    def to_lean(self) -> str:
        expr = self.context_expr.to_lean()
        if self.optional_var:
            return f"let {_lean_ident(self.optional_var)} ← {expr}"
        return expr


class PyStmt:
    """Base class for all statement IR nodes."""

    def to_lean(self) -> str:
        raise NotImplementedError

    def defined_vars(self) -> Set[str]:
        return set()

    def used_vars(self) -> Set[str]:
        return set()

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, PyStmt):
            return NotImplemented
        return type(self) is type(other) and self.__dict__ == other.__dict__

    def __hash__(self) -> int:
        return hash(repr(self))

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}(...)"

    def is_terminator(self) -> bool:
        return False


@dataclass
class PyAssign(PyStmt):
    target: str
    value: PyExpr
    type_annotation: Optional[PyType] = None

    def to_lean(self) -> str:
        name = _lean_ident(self.target)
        if self.type_annotation:
            return f"let {name} : {self.type_annotation.to_lean()} := {self.value.to_lean()}"
        return f"let {name} := {self.value.to_lean()}"

    def defined_vars(self) -> Set[str]:
        return {self.target}

    def used_vars(self) -> Set[str]:
        return self.value.free_vars()


@dataclass
class PyAugAssign(PyStmt):
    target: str
    op: BinOp
    value: PyExpr

    def to_lean(self) -> str:
        name = _lean_ident(self.target)
        return f"let {name} := {name} {self.op.to_lean()} {self.value.to_lean()}"

    def defined_vars(self) -> Set[str]:
        return {self.target}

    def used_vars(self) -> Set[str]:
        return {self.target} | self.value.free_vars()


@dataclass
class PyReturn(PyStmt):
    value: Optional[PyExpr] = None

    def to_lean(self) -> str:
        if self.value:
            return f"return {self.value.to_lean()}"
        return "return ()"

    def is_terminator(self) -> bool:
        return True

    def used_vars(self) -> Set[str]:
        if self.value:
            return self.value.free_vars()
        return set()


@dataclass
class PyRaise(PyStmt):
    exc: Optional[PyExpr] = None

    def to_lean(self) -> str:
        if self.exc:
            return f"throw {self.exc.to_lean()}"
        return "throw default"

    def is_terminator(self) -> bool:
        return True

    def used_vars(self) -> Set[str]:
        if self.exc:
            return self.exc.free_vars()
        return set()


@dataclass
class PyIf(PyStmt):
    test: PyExpr
    body: List[PyStmt]
    orelse: List[PyStmt]

    def to_lean(self) -> str:
        lines = [f"if {self.test.to_lean()} then"]
        for s in self.body:
            lines.append(f"  {s.to_lean()}")
        if self.orelse:
            lines.append("else")
            for s in self.orelse:
                lines.append(f"  {s.to_lean()}")
        return "\n".join(lines)

    def defined_vars(self) -> Set[str]:
        body_defs = set()
        for s in self.body:
            body_defs |= s.defined_vars()
        else_defs = set()
        for s in self.orelse:
            else_defs |= s.defined_vars()
        return body_defs & else_defs

    def used_vars(self) -> Set[str]:
        result = self.test.free_vars()
        for s in self.body:
            result |= s.used_vars()
        for s in self.orelse:
            result |= s.used_vars()
        return result


@dataclass
class PyWhile(PyStmt):
    test: PyExpr
    body: List[PyStmt]
    orelse: List[PyStmt]

    def to_lean(self) -> str:
        lines = [f"while {self.test.to_lean()} do"]
        for s in self.body:
            lines.append(f"  {s.to_lean()}")
        if self.orelse:
            lines.append("-- else branch (while/else)")
            for s in self.orelse:
                lines.append(f"  {s.to_lean()}")
        return "\n".join(lines)

    def defined_vars(self) -> Set[str]:
        result: Set[str] = set()
        for s in self.body:
            result |= s.defined_vars()
        return result

    def used_vars(self) -> Set[str]:
        result = self.test.free_vars()
        for s in self.body:
            result |= s.used_vars()
        for s in self.orelse:
            result |= s.used_vars()
        return result


@dataclass
class PyFor(PyStmt):
    target: str
    iter_expr: PyExpr
    body: List[PyStmt]
    orelse: List[PyStmt]

    def to_lean(self) -> str:
        lines = [f"for {_lean_ident(self.target)} in {self.iter_expr.to_lean()} do"]
        for s in self.body:
            lines.append(f"  {s.to_lean()}")
        if self.orelse:
            lines.append("-- else branch (for/else)")
            for s in self.orelse:
                lines.append(f"  {s.to_lean()}")
        return "\n".join(lines)

    def defined_vars(self) -> Set[str]:
        result: Set[str] = {self.target}
        for s in self.body:
            result |= s.defined_vars()
        return result

    def used_vars(self) -> Set[str]:
        result = self.iter_expr.free_vars()
        for s in self.body:
            result |= s.used_vars()
        for s in self.orelse:
            result |= s.used_vars()
        return result


@dataclass
class PyTry(PyStmt):
    body: List[PyStmt]
    handlers: List[ExceptHandler]
    orelse: List[PyStmt]
    finalbody: List[PyStmt]

    def to_lean(self) -> str:
        lines = ["try"]
        for s in self.body:
            lines.append(f"  {s.to_lean()}")
        if self.handlers:
            lines.append("catch")
            for h in self.handlers:
                lines.append(h.to_lean(indent=2))
        if self.orelse:
            lines.append("-- else (try/else)")
            for s in self.orelse:
                lines.append(f"  {s.to_lean()}")
        if self.finalbody:
            lines.append("finally")
            for s in self.finalbody:
                lines.append(f"  {s.to_lean()}")
        return "\n".join(lines)

    def defined_vars(self) -> Set[str]:
        result: Set[str] = set()
        for s in self.body:
            result |= s.defined_vars()
        for h in self.handlers:
            result |= h.defined_vars()
        for s in self.orelse:
            result |= s.defined_vars()
        for s in self.finalbody:
            result |= s.defined_vars()
        return result

    def used_vars(self) -> Set[str]:
        result: Set[str] = set()
        for s in self.body:
            result |= s.used_vars()
        for h in self.handlers:
            result |= h.used_vars()
        for s in self.orelse:
            result |= s.used_vars()
        for s in self.finalbody:
            result |= s.used_vars()
        return result


@dataclass
class PyWith(PyStmt):
    items: List[WithItem]
    body: List[PyStmt]

    def to_lean(self) -> str:
        lines = ["do"]
        for item in self.items:
            lines.append(f"  {item.to_lean()}")
        for s in self.body:
            lines.append(f"  {s.to_lean()}")
        return "\n".join(lines)

    def defined_vars(self) -> Set[str]:
        result: Set[str] = set()
        for item in self.items:
            if item.optional_var:
                result.add(item.optional_var)
        for s in self.body:
            result |= s.defined_vars()
        return result

    def used_vars(self) -> Set[str]:
        result: Set[str] = set()
        for item in self.items:
            result |= item.context_expr.free_vars()
        for s in self.body:
            result |= s.used_vars()
        return result


@dataclass
class PyAssert(PyStmt):
    test: PyExpr
    msg: Optional[PyExpr] = None

    def to_lean(self) -> str:
        if self.msg:
            return f"assert ({self.test.to_lean()}) ({self.msg.to_lean()})"
        return f"assert ({self.test.to_lean()})"

    def used_vars(self) -> Set[str]:
        result = self.test.free_vars()
        if self.msg:
            result |= self.msg.free_vars()
        return result


@dataclass
class PyPass(PyStmt):
    def to_lean(self) -> str:
        return "pure ()"

    def defined_vars(self) -> Set[str]:
        return set()

    def used_vars(self) -> Set[str]:
        return set()


@dataclass
class PyBreak(PyStmt):
    def to_lean(self) -> str:
        return "break"

    def is_terminator(self) -> bool:
        return True


@dataclass
class PyContinue(PyStmt):
    def to_lean(self) -> str:
        return "continue"

    def is_terminator(self) -> bool:
        return True


@dataclass
class PyExprStmt(PyStmt):
    value: PyExpr

    def to_lean(self) -> str:
        return self.value.to_lean()

    def used_vars(self) -> Set[str]:
        return self.value.free_vars()


@dataclass
class PyDelete(PyStmt):
    targets: List[str]

    def to_lean(self) -> str:
        # Lean doesn't have deletion; model as rebinding to default
        lines = [f"let {_lean_ident(t)} := default" for t in self.targets]
        return "\n".join(lines)

    def defined_vars(self) -> Set[str]:
        return set(self.targets)

    def used_vars(self) -> Set[str]:
        return set()


# ---------------------------------------------------------------------------
# Section 5: PyFunc, PyClass, PyModule  (~300 lines)
# ---------------------------------------------------------------------------

@dataclass
class PyParam:
    """A single function parameter."""
    name: str
    type: Optional[PyType] = None
    default: Optional[PyExpr] = None

    def to_lean_param(self) -> str:
        n = _lean_ident(self.name)
        if self.type:
            return f"({n} : {self.type.to_lean()})"
        return f"({n} : _)"

    def to_lean_with_default(self) -> str:
        n = _lean_ident(self.name)
        if self.type and self.default:
            return (
                f"({n} : {self.type.to_lean()} := {self.default.to_lean()})"
            )
        if self.default:
            return f"({n} := {self.default.to_lean()})"
        return self.to_lean_param()


@dataclass
class PyFunc:
    """Function definition IR node."""
    name: str
    params: List[PyParam]
    return_type: Optional[PyType]
    body: List[PyStmt]
    decorators: List[str] = field(default_factory=list)
    docstring: Optional[str] = None

    def signature(self) -> PyFunctionType:
        ptypes = tuple(p.type or PY_NONE for p in self.params)
        ret = self.return_type or PY_NONE
        return PyFunctionType(ptypes, ret)

    def to_lean_def(self) -> str:
        """Render as a complete Lean 4 definition."""
        lines: List[str] = []
        # Decorators as attributes
        for dec in self.decorators:
            lines.append(f"@[{dec}]")
        # Docstring
        if self.docstring:
            for docline in self.docstring.strip().splitlines():
                lines.append(f"/-- {docline.strip()} -/")
        # Signature
        param_strs = " ".join(p.to_lean_with_default() for p in self.params)
        if not param_strs:
            param_strs = "()"
        ret_str = self.return_type.to_lean() if self.return_type else "_"
        lines.append(f"def {_lean_ident(self.name)} {param_strs} : {ret_str} :=")
        # Body
        if not self.body:
            lines.append("  sorry")
        elif len(self.body) == 1 and not isinstance(self.body[0], (PyIf, PyWhile, PyFor, PyTry, PyWith)):
            lines.append(f"  {self.body[0].to_lean()}")
        else:
            lines.append("  do")
            for stmt in self.body:
                for sl in stmt.to_lean().splitlines():
                    lines.append(f"    {sl}")
        return "\n".join(lines)

    def defined_names(self) -> Set[str]:
        result: Set[str] = set()
        for s in self.body:
            result |= s.defined_vars()
        return result

    def used_names(self) -> Set[str]:
        result: Set[str] = set()
        for s in self.body:
            result |= s.used_vars()
        return result

    def free_names(self) -> Set[str]:
        param_names = {p.name for p in self.params}
        return self.used_names() - param_names - self.defined_names()


@dataclass
class PyClass:
    """Class definition IR node."""
    name: str
    bases: List[str]
    fields: Dict[str, PyType]
    methods: List[PyFunc]
    class_vars: Dict[str, PyExpr] = field(default_factory=dict)

    def to_lean_structure(self) -> str:
        """Render as a Lean 4 structure definition."""
        lines: List[str] = []
        extends = ""
        if self.bases:
            extends = " extends " + ", ".join(_lean_ident(b) for b in self.bases)
        lines.append(f"structure {_lean_ident(self.name)}{extends} where")
        # Fields
        if not self.fields and not self.class_vars:
            lines.append("  mk ::")
        for fname, ftype in self.fields.items():
            lines.append(f"  {_lean_ident(fname)} : {ftype.to_lean()}")
        # Class-level variables as default fields
        for cname, cexpr in self.class_vars.items():
            lines.append(f"  {_lean_ident(cname)} : _ := {cexpr.to_lean()}")
        lines.append("")
        # Methods in a namespace
        if self.methods:
            lines.append(f"namespace {_lean_ident(self.name)}")
            lines.append("")
            for method in self.methods:
                lines.append(method.to_lean_def())
                lines.append("")
            lines.append(f"end {_lean_ident(self.name)}")
        return "\n".join(lines)

    def to_type(self) -> PyClassType:
        method_types: Dict[str, PyFunctionType] = {}
        for m in self.methods:
            method_types[m.name] = m.signature()
        return PyClassType(self.name, dict(self.fields), method_types)


@dataclass
class PyImport:
    """Import declaration."""
    module: str
    names: List[str] = field(default_factory=list)
    alias: Optional[str] = None

    def to_lean(self) -> str:
        mod = self.module.replace(".", ".")
        if self.alias:
            return f"-- import {mod} as {self.alias}"
        if self.names:
            opens = ", ".join(self.names)
            return f"-- from {mod} import {opens}"
        return f"-- import {mod}"

    def to_lean_import(self) -> str:
        parts = self.module.split(".")
        lean_mod = ".".join(_lean_ident(p) for p in parts)
        return f"import {lean_mod}"


@dataclass
class PyModule:
    """Top-level module — the root of the IR tree."""
    name: str
    imports: List[PyImport] = field(default_factory=list)
    classes: List[PyClass] = field(default_factory=list)
    functions: List[PyFunc] = field(default_factory=list)
    statements: List[PyStmt] = field(default_factory=list)

    def to_lean_file(self) -> str:
        """Render a complete .lean file."""
        lines: List[str] = []
        lines.append(f"/-! # Module: {self.name} -/")
        lines.append("")
        # Imports
        for imp in self.imports:
            lines.append(imp.to_lean())
        if self.imports:
            lines.append("")
        # Classes
        for cls in self.classes:
            lines.append(cls.to_lean_structure())
            lines.append("")
        # Functions
        for func in self.functions:
            lines.append(func.to_lean_def())
            lines.append("")
        # Top-level statements
        if self.statements:
            lines.append("def main : IO Unit := do")
            for stmt in self.statements:
                for sl in stmt.to_lean().splitlines():
                    lines.append(f"  {sl}")
            lines.append("")
        return "\n".join(lines)

    def all_defined_names(self) -> Set[str]:
        result: Set[str] = set()
        for cls in self.classes:
            result.add(cls.name)
        for func in self.functions:
            result.add(func.name)
        for stmt in self.statements:
            result |= stmt.defined_vars()
        return result

    def all_imported_names(self) -> Set[str]:
        result: Set[str] = set()
        for imp in self.imports:
            if imp.alias:
                result.add(imp.alias)
            result.update(imp.names)
        return result


# ---------------------------------------------------------------------------
# Section 6: PythonToIR — AST → IR conversion  (~300 lines)
# ---------------------------------------------------------------------------

_AST_BINOP_MAP: Dict[type, BinOp] = {
    ast.Add: BinOp.ADD,
    ast.Sub: BinOp.SUB,
    ast.Mult: BinOp.MUL,
    ast.Div: BinOp.DIV,
    ast.FloorDiv: BinOp.FLOORDIV,
    ast.Mod: BinOp.MOD,
    ast.Pow: BinOp.POW,
    ast.LShift: BinOp.LSHIFT,
    ast.RShift: BinOp.RSHIFT,
    ast.BitOr: BinOp.BITOR,
    ast.BitXor: BinOp.BITXOR,
    ast.BitAnd: BinOp.BITAND,
    ast.MatMult: BinOp.MATMUL,
}

_AST_UNARYOP_MAP: Dict[type, UnaryOp] = {
    ast.UAdd: UnaryOp.UADD,
    ast.USub: UnaryOp.USUB,
    ast.Not: UnaryOp.NOT,
    ast.Invert: UnaryOp.INVERT,
}

_AST_CMPOP_MAP: Dict[type, CmpOp] = {
    ast.Eq: CmpOp.EQ,
    ast.NotEq: CmpOp.NE,
    ast.Lt: CmpOp.LT,
    ast.LtE: CmpOp.LE,
    ast.Gt: CmpOp.GT,
    ast.GtE: CmpOp.GE,
    ast.Is: CmpOp.IS,
    ast.IsNot: CmpOp.ISNOT,
    ast.In: CmpOp.IN,
    ast.NotIn: CmpOp.NOTIN,
}


class PythonToIR:
    """Converts Python source code to the IR via the ast module."""

    def __init__(self, source: str, module_name: str = "__main__") -> None:
        self.source = source
        self.module_name = module_name
        self._tree: Optional[ast.Module] = None

    def convert(self) -> PyModule:
        self._tree = ast.parse(self.source)
        imports: List[PyImport] = []
        classes: List[PyClass] = []
        functions: List[PyFunc] = []
        statements: List[PyStmt] = []

        for node in self._tree.body:
            if isinstance(node, ast.Import):
                for alias in node.names:
                    imports.append(
                        PyImport(
                            module=alias.name,
                            names=[],
                            alias=alias.asname,
                        )
                    )
            elif isinstance(node, ast.ImportFrom):
                mod = node.module or ""
                names = [a.name for a in node.names]
                imports.append(PyImport(module=mod, names=names))
            elif isinstance(node, ast.FunctionDef) or isinstance(node, ast.AsyncFunctionDef):
                functions.append(self.convert_func(node))
            elif isinstance(node, ast.ClassDef):
                classes.append(self.convert_class(node))
            else:
                statements.append(self.convert_stmt(node))

        return PyModule(
            name=self.module_name,
            imports=imports,
            classes=classes,
            functions=functions,
            statements=statements,
        )

    # ---- Expression conversion ----

    def convert_expr(self, node: ast.expr) -> PyExpr:
        if isinstance(node, ast.Constant):
            return PyLit(self._constant_to_value(node.value))

        if isinstance(node, ast.Name):
            return PyVar(node.id)

        if isinstance(node, ast.BinOp):
            op = _AST_BINOP_MAP.get(type(node.op))
            if op is None:
                return PyVar("__unknown_binop__")
            return PyBinOp(
                op=op,
                left=self.convert_expr(node.left),
                right=self.convert_expr(node.right),
            )

        if isinstance(node, ast.UnaryOp):
            op = _AST_UNARYOP_MAP.get(type(node.op))
            if op is None:
                return PyVar("__unknown_unaryop__")
            return PyUnaryOp(op=op, operand=self.convert_expr(node.operand))

        if isinstance(node, ast.BoolOp):
            # Desugar `a and b and c` as nested binary
            values = [self.convert_expr(v) for v in node.values]
            if isinstance(node.op, ast.And):
                result = values[0]
                for v in values[1:]:
                    result = PyBinOp(BinOp.BITAND, result, v)
                return result
            else:
                result = values[0]
                for v in values[1:]:
                    result = PyBinOp(BinOp.BITOR, result, v)
                return result

        if isinstance(node, ast.Compare):
            ops = [_AST_CMPOP_MAP.get(type(o), CmpOp.EQ) for o in node.ops]
            comps = [self.convert_expr(c) for c in node.comparators]
            return PyCompare(
                ops=ops,
                left=self.convert_expr(node.left),
                comparators=comps,
            )

        if isinstance(node, ast.Call):
            func_expr = self.convert_expr(node.func)
            args = [self.convert_expr(a) for a in node.args]
            kwargs: Dict[str, PyExpr] = {}
            for kw in node.keywords:
                if kw.arg is not None:
                    kwargs[kw.arg] = self.convert_expr(kw.value)
            # Detect method calls: obj.method(args)
            if isinstance(node.func, ast.Attribute):
                return PyMethodCall(
                    obj=self.convert_expr(node.func.value),
                    method=node.func.attr,
                    args=args,
                )
            return PyCall(func=func_expr, args=args, kwargs=kwargs)

        if isinstance(node, ast.Attribute):
            return PyAttribute(
                obj=self.convert_expr(node.value),
                attr=node.attr,
            )

        if isinstance(node, ast.Subscript):
            obj = self.convert_expr(node.value)
            if isinstance(node.slice, ast.Slice):
                lower = self.convert_expr(node.slice.lower) if node.slice.lower else None
                upper = self.convert_expr(node.slice.upper) if node.slice.upper else None
                step = self.convert_expr(node.slice.step) if node.slice.step else None
                return PySlice(obj=obj, lower=lower, upper=upper, step=step)
            index = self.convert_expr(node.slice)
            return PySubscript(obj=obj, index=index)

        if isinstance(node, ast.IfExp):
            return PyTernary(
                test=self.convert_expr(node.test),
                body=self.convert_expr(node.body),
                orelse=self.convert_expr(node.orelse),
            )

        if isinstance(node, ast.ListComp):
            elt = self.convert_expr(node.elt)
            gens = [self._convert_comprehension(g) for g in node.generators]
            return PyListComp(elt=elt, generators=gens)

        if isinstance(node, ast.DictComp):
            key = self.convert_expr(node.key)
            value = self.convert_expr(node.value)
            gens = [self._convert_comprehension(g) for g in node.generators]
            return PyDictComp(key=key, value=value, generators=gens)

        if isinstance(node, ast.Lambda):
            arg_names = [a.arg for a in node.args.args]
            body = self.convert_expr(node.body)
            return PyLambda(args=arg_names, body=body)

        if isinstance(node, ast.List):
            elements = [self.convert_expr(e) for e in node.elts]
            list_val = PyListVal(elements=[])
            # Build as a list expression via literal
            return PyCall(
                func=PyVar("List.mk"),
                args=elements,
                kwargs={},
            ) if elements else PyLit(PyListVal([]))

        if isinstance(node, ast.Tuple):
            elements = [self.convert_expr(e) for e in node.elts]
            if not elements:
                return PyLit(PyTupleVal([]))
            if len(elements) == 1:
                return elements[0]
            # Model as nested pair construction
            return PyCall(
                func=PyVar("Prod.mk"),
                args=elements,
                kwargs={},
            )

        if isinstance(node, ast.Dict):
            keys = node.keys
            values = node.values
            entries: Dict[PyValue, PyValue] = {}
            for k, v in zip(keys, values):
                if k is not None:
                    kv = self._try_constant(k)
                    vv = self._try_constant(v)
                    if kv is not None and vv is not None:
                        entries[kv] = vv
            if entries or not keys:
                return PyLit(PyDictVal(entries))
            # Non-constant dict — build dynamically
            return PyCall(
                func=PyVar("Dict.mk"),
                args=[self.convert_expr(v) for v in values if v is not None],
                kwargs={},
            )

        if isinstance(node, ast.Set):
            elements = [self.convert_expr(e) for e in node.elts]
            return PyCall(
                func=PyVar("Set.mk"),
                args=elements,
                kwargs={},
            )

        if isinstance(node, ast.JoinedStr):
            parts: List[Union[str, PyExpr]] = []
            for val in node.values:
                if isinstance(val, ast.Constant) and isinstance(val.value, str):
                    parts.append(val.value)
                elif isinstance(val, ast.FormattedValue):
                    parts.append(self.convert_expr(val.value))
                else:
                    parts.append(self.convert_expr(val))
            return PyFString(parts=parts)

        if isinstance(node, ast.Starred):
            return PyStarExpr(value=self.convert_expr(node.value))

        if isinstance(node, ast.NamedExpr):
            # Walrus operator: (x := expr)
            return PyBinOp(
                op=BinOp.ADD,
                left=PyVar(node.target.id),
                right=self.convert_expr(node.value),
            )

        # Fallback for unrecognised expressions
        return PyVar(f"__unsupported_{type(node).__name__}__")

    def _convert_comprehension(self, gen: ast.comprehension) -> Comprehension:
        target_name = self._target_name(gen.target)
        iter_expr = self.convert_expr(gen.iter)
        conditions = [self.convert_expr(c) for c in gen.ifs]
        return Comprehension(
            target=target_name,
            iter_expr=iter_expr,
            conditions=conditions,
        )

    def _target_name(self, node: ast.expr) -> str:
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Tuple):
            return "(" + ", ".join(self._target_name(e) for e in node.elts) + ")"
        return "_"

    def _constant_to_value(self, value: object) -> PyValue:
        if value is None:
            return PyNoneVal()
        if isinstance(value, bool):
            return PyBoolVal(value)
        if isinstance(value, int):
            return PyIntVal(value)
        if isinstance(value, float):
            return PyFloatVal(value)
        if isinstance(value, str):
            return PyStrVal(value)
        if isinstance(value, bytes):
            return PyBytesVal(value)
        return PyNoneVal()

    def _try_constant(self, node: ast.expr) -> Optional[PyValue]:
        if isinstance(node, ast.Constant):
            return self._constant_to_value(node.value)
        return None

    # ---- Statement conversion ----

    def convert_stmt(self, node: ast.stmt) -> PyStmt:
        if isinstance(node, ast.Assign):
            target = self._target_name(node.targets[0])
            value = self.convert_expr(node.value)
            return PyAssign(target=target, value=value)

        if isinstance(node, ast.AnnAssign):
            target = self._target_name(node.target) if isinstance(node.target, (ast.Name, ast.Tuple)) else "_"
            ann_type = _annotation_to_type(node.annotation)
            value = self.convert_expr(node.value) if node.value else PyLit(PyNoneVal())
            return PyAssign(target=target, value=value, type_annotation=ann_type)

        if isinstance(node, ast.AugAssign):
            target = self._target_name(node.target) if isinstance(node.target, ast.Name) else "_"
            op = _AST_BINOP_MAP.get(type(node.op), BinOp.ADD)
            value = self.convert_expr(node.value)
            return PyAugAssign(target=target, op=op, value=value)

        if isinstance(node, ast.Return):
            value = self.convert_expr(node.value) if node.value else None
            return PyReturn(value=value)

        if isinstance(node, ast.Raise):
            exc = self.convert_expr(node.exc) if node.exc else None
            return PyRaise(exc=exc)

        if isinstance(node, ast.If):
            test = self.convert_expr(node.test)
            body = [self.convert_stmt(s) for s in node.body]
            orelse = [self.convert_stmt(s) for s in node.orelse]
            return PyIf(test=test, body=body, orelse=orelse)

        if isinstance(node, ast.While):
            test = self.convert_expr(node.test)
            body = [self.convert_stmt(s) for s in node.body]
            orelse = [self.convert_stmt(s) for s in node.orelse]
            return PyWhile(test=test, body=body, orelse=orelse)

        if isinstance(node, ast.For):
            target = self._target_name(node.target)
            iter_expr = self.convert_expr(node.iter)
            body = [self.convert_stmt(s) for s in node.body]
            orelse = [self.convert_stmt(s) for s in node.orelse]
            return PyFor(target=target, iter_expr=iter_expr, body=body, orelse=orelse)

        if isinstance(node, ast.Try):
            body = [self.convert_stmt(s) for s in node.body]
            handlers = []
            for h in node.handlers:
                exc_type = None
                if h.type is not None:
                    if isinstance(h.type, ast.Name):
                        exc_type = h.type.id
                    else:
                        exc_type = ast.dump(h.type)
                handler_body = [self.convert_stmt(s) for s in h.body]
                handlers.append(
                    ExceptHandler(
                        exc_type=exc_type,
                        name=h.name,
                        body=handler_body,
                    )
                )
            orelse = [self.convert_stmt(s) for s in node.orelse]
            finalbody = [self.convert_stmt(s) for s in node.finalbody]
            return PyTry(
                body=body,
                handlers=handlers,
                orelse=orelse,
                finalbody=finalbody,
            )

        if isinstance(node, ast.With):
            items = []
            for item in node.items:
                ctx = self.convert_expr(item.context_expr)
                opt_var = None
                if item.optional_vars is not None:
                    opt_var = self._target_name(item.optional_vars)
                items.append(WithItem(context_expr=ctx, optional_var=opt_var))
            body = [self.convert_stmt(s) for s in node.body]
            return PyWith(items=items, body=body)

        if isinstance(node, ast.Assert):
            test = self.convert_expr(node.test)
            msg = self.convert_expr(node.msg) if node.msg else None
            return PyAssert(test=test, msg=msg)

        if isinstance(node, ast.Pass):
            return PyPass()

        if isinstance(node, ast.Break):
            return PyBreak()

        if isinstance(node, ast.Continue):
            return PyContinue()

        if isinstance(node, ast.Expr):
            return PyExprStmt(value=self.convert_expr(node.value))

        if isinstance(node, ast.Delete):
            targets = []
            for t in node.targets:
                targets.append(self._target_name(t))
            return PyDelete(targets=targets)

        if isinstance(node, ast.Global) or isinstance(node, ast.Nonlocal):
            return PyPass()

        # Handle TryStar (Python 3.11+)
        if hasattr(ast, "TryStar") and isinstance(node, ast.TryStar):  # type: ignore[attr-defined]
            body = [self.convert_stmt(s) for s in node.body]
            handlers = []
            for h in node.handlers:
                exc_type = None
                if h.type is not None:
                    exc_type = ast.dump(h.type) if not isinstance(h.type, ast.Name) else h.type.id
                handler_body = [self.convert_stmt(s) for s in h.body]
                handlers.append(ExceptHandler(exc_type=exc_type, name=h.name, body=handler_body))
            orelse = [self.convert_stmt(s) for s in node.orelse]
            finalbody = [self.convert_stmt(s) for s in node.finalbody]
            return PyTry(body=body, handlers=handlers, orelse=orelse, finalbody=finalbody)

        # Fallback
        return PyExprStmt(value=PyVar(f"__unsupported_stmt_{type(node).__name__}__"))

    # ---- Function / class conversion ----

    def convert_func(self, node: Union[ast.FunctionDef, ast.AsyncFunctionDef]) -> PyFunc:
        params: List[PyParam] = []
        defaults_offset = len(node.args.args) - len(node.args.defaults)
        for i, arg in enumerate(node.args.args):
            ann = _annotation_to_type(arg.annotation)
            default_idx = i - defaults_offset
            default = None
            if default_idx >= 0:
                default = self.convert_expr(node.args.defaults[default_idx])
            params.append(PyParam(name=arg.arg, type=ann, default=default))

        # *args
        if node.args.vararg:
            va = node.args.vararg
            ann = _annotation_to_type(va.annotation)
            params.append(PyParam(name=f"*{va.arg}", type=ann))

        # **kwargs
        if node.args.kwarg:
            kwa = node.args.kwarg
            ann = _annotation_to_type(kwa.annotation)
            params.append(PyParam(name=f"**{kwa.arg}", type=ann))

        return_type = _annotation_to_type(node.returns)
        body = [self.convert_stmt(s) for s in node.body]
        decorators = []
        for dec in node.decorator_list:
            if isinstance(dec, ast.Name):
                decorators.append(dec.id)
            elif isinstance(dec, ast.Attribute):
                decorators.append(ast.dump(dec))
            else:
                decorators.append("unknown")

        docstring: Optional[str] = None
        if (
            body
            and isinstance(body[0], PyExprStmt)
            and isinstance(body[0].value, PyLit)
            and isinstance(body[0].value.value, PyStrVal)
        ):
            docstring = body[0].value.value.value
            body = body[1:]

        return PyFunc(
            name=node.name,
            params=params,
            return_type=return_type,
            body=body,
            decorators=decorators,
            docstring=docstring,
        )

    def convert_class(self, node: ast.ClassDef) -> PyClass:
        bases = []
        for base in node.bases:
            if isinstance(base, ast.Name):
                bases.append(base.id)
            elif isinstance(base, ast.Attribute):
                bases.append(ast.dump(base))
            else:
                bases.append("object")

        fields: Dict[str, PyType] = {}
        methods: List[PyFunc] = []
        class_vars: Dict[str, PyExpr] = {}

        for item in node.body:
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                methods.append(self.convert_func(item))
            elif isinstance(item, ast.AnnAssign):
                if isinstance(item.target, ast.Name):
                    ftype = _annotation_to_type(item.annotation) or PY_NONE
                    fields[item.target.id] = ftype
                    if item.value:
                        class_vars[item.target.id] = self.convert_expr(item.value)
            elif isinstance(item, ast.Assign):
                for t in item.targets:
                    if isinstance(t, ast.Name):
                        class_vars[t.id] = self.convert_expr(item.value)
            # Skip other class-level constructs

        return PyClass(
            name=node.name,
            bases=bases,
            fields=fields,
            methods=methods,
            class_vars=class_vars,
        )


# ---------------------------------------------------------------------------
# Section 7: TypeEnv — Type environment for inference  (~200 lines)
# ---------------------------------------------------------------------------

class TypeEnv:
    """
    Hierarchical type environment with simple type inference.

    Supports lexical scoping via parent pointers and a simple
    forward-propagation inference strategy.
    """

    def __init__(
        self,
        bindings: Optional[Dict[str, PyType]] = None,
        parent: Optional[TypeEnv] = None,
    ) -> None:
        self.bindings: Dict[str, PyType] = dict(bindings) if bindings else {}
        self.parent: Optional[TypeEnv] = parent

    def lookup(self, name: str) -> Optional[PyType]:
        """Look up a name in the current scope or any ancestor."""
        if name in self.bindings:
            return self.bindings[name]
        if self.parent is not None:
            return self.parent.lookup(name)
        return None

    def bind(self, name: str, typ: PyType) -> None:
        """Bind a name in the current scope."""
        self.bindings[name] = typ

    def child(self) -> TypeEnv:
        """Create a child scope."""
        return TypeEnv(parent=self)

    def merge(self, other: TypeEnv) -> TypeEnv:
        """Create a new environment containing bindings from both."""
        merged = TypeEnv(parent=self.parent)
        merged.bindings.update(self.bindings)
        merged.bindings.update(other.bindings)
        return merged

    def all_bindings(self) -> Dict[str, PyType]:
        """Collect all bindings from this scope up to root."""
        result: Dict[str, PyType] = {}
        if self.parent is not None:
            result.update(self.parent.all_bindings())
        result.update(self.bindings)
        return result

    def infer(self, expr: PyExpr) -> PyType:
        """
        Simple type inference for an expression.

        This implements a basic forward-propagation strategy:
        - Literals have known types
        - Variables are looked up in the environment
        - Operators follow Python's promotion rules
        - Function calls use the return type
        """
        if isinstance(expr, PyLit):
            return expr.value.typeof()

        if isinstance(expr, PyVar):
            return self.lookup(expr.name) or PY_NONE

        if isinstance(expr, PyBinOp):
            lt = self.infer(expr.left)
            rt = self.infer(expr.right)
            return self._infer_binop(expr.op, lt, rt)

        if isinstance(expr, PyUnaryOp):
            if expr.op is UnaryOp.NOT:
                return PY_BOOL
            return self.infer(expr.operand)

        if isinstance(expr, PyCompare):
            return PY_BOOL

        if isinstance(expr, PyCall):
            ft = self.infer(expr.func)
            if isinstance(ft, PyFunctionType):
                return ft.return_type
            # Builtins
            if isinstance(expr.func, PyVar):
                name = expr.func.name
                if name == "len":
                    return PY_INT
                if name == "str":
                    return PY_STR
                if name == "int":
                    return PY_INT
                if name == "float":
                    return PY_FLOAT
                if name == "bool":
                    return PY_BOOL
                if name == "list":
                    return PyListType(PY_NONE)
                if name == "dict":
                    return PyDictType(PY_STR, PY_NONE)
                if name == "set":
                    return PySetType(PY_NONE)
                if name == "tuple":
                    return PyTupleType(())
                if name == "range":
                    return PyListType(PY_INT)
                if name == "sorted":
                    if expr.args:
                        return self.infer(expr.args[0])
                    return PyListType(PY_NONE)
                if name == "reversed":
                    if expr.args:
                        return self.infer(expr.args[0])
                    return PyListType(PY_NONE)
                if name == "enumerate":
                    return PyListType(PyTupleType((PY_INT, PY_NONE)))
                if name == "zip":
                    return PyListType(PyTupleType(()))
                if name == "map":
                    return PyListType(PY_NONE)
                if name == "filter":
                    return PyListType(PY_NONE)
                if name == "isinstance":
                    return PY_BOOL
                if name == "type":
                    return PY_STR
                if name == "print":
                    return PY_NONE
                if name == "input":
                    return PY_STR
                if name == "abs":
                    if expr.args:
                        return self.infer(expr.args[0])
                    return PY_INT
                if name == "max" or name == "min":
                    if expr.args:
                        return self.infer(expr.args[0])
                    return PY_INT
                if name == "sum":
                    return PY_INT
                if name == "round":
                    return PY_INT
                if name == "ord":
                    return PY_INT
                if name == "chr":
                    return PY_STR
                if name == "hex":
                    return PY_STR
                if name == "oct":
                    return PY_STR
                if name == "bin":
                    return PY_STR
            return PY_NONE

        if isinstance(expr, PyMethodCall):
            return self._infer_method(expr)

        if isinstance(expr, PySubscript):
            ot = self.infer(expr.obj)
            if isinstance(ot, PyListType):
                return ot.element
            if isinstance(ot, PyDictType):
                return ot.value
            if isinstance(ot, PyTupleType) and ot.elements:
                return ot.elements[0]
            if isinstance(ot, PyPrimitiveType) and ot.literal is PyLiteral.STR:
                return PY_STR
            return PY_NONE

        if isinstance(expr, PySlice):
            return self.infer(expr.obj)

        if isinstance(expr, PyAttribute):
            ot = self.infer(expr.obj)
            if isinstance(ot, PyClassType) and expr.attr in ot.fields:
                return ot.fields[expr.attr]
            return PY_NONE

        if isinstance(expr, PyTernary):
            return self.infer(expr.body)

        if isinstance(expr, PyListComp):
            child = self.child()
            for gen in expr.generators:
                iter_t = self.infer(gen.iter_expr)
                if isinstance(iter_t, PyListType):
                    child.bind(gen.target, iter_t.element)
                else:
                    child.bind(gen.target, PY_NONE)
            return PyListType(child.infer(expr.elt))

        if isinstance(expr, PyDictComp):
            child = self.child()
            for gen in expr.generators:
                iter_t = self.infer(gen.iter_expr)
                if isinstance(iter_t, PyListType):
                    child.bind(gen.target, iter_t.element)
                else:
                    child.bind(gen.target, PY_NONE)
            return PyDictType(child.infer(expr.key), child.infer(expr.value))

        if isinstance(expr, PyLambda):
            child = self.child()
            for a in expr.args:
                child.bind(a, PY_NONE)
            ret = child.infer(expr.body)
            return PyFunctionType(tuple(PY_NONE for _ in expr.args), ret)

        if isinstance(expr, PyFString):
            return PY_STR

        if isinstance(expr, PyStarExpr):
            return self.infer(expr.value)

        return PY_NONE

    def _infer_binop(self, op: BinOp, left: PyType, right: PyType) -> PyType:
        """Infer result type for a binary operation."""
        if op is BinOp.DIV:
            return PY_FLOAT

        if isinstance(left, PyPrimitiveType) and isinstance(right, PyPrimitiveType):
            if left.literal is PyLiteral.FLOAT or right.literal is PyLiteral.FLOAT:
                return PY_FLOAT
            if left.literal is PyLiteral.INT and right.literal is PyLiteral.INT:
                return PY_INT
            if left.literal is PyLiteral.BOOL and right.literal is PyLiteral.BOOL:
                if op in (BinOp.BITOR, BinOp.BITAND, BinOp.BITXOR):
                    return PY_BOOL
                return PY_INT
            if left.literal is PyLiteral.STR and op is BinOp.ADD:
                return PY_STR
            if left.literal is PyLiteral.STR and op is BinOp.MUL:
                return PY_STR

        if isinstance(left, PyListType) and op is BinOp.ADD:
            return left
        if isinstance(left, PyListType) and op is BinOp.MUL:
            return left

        if isinstance(left, PyTupleType) and op is BinOp.ADD and isinstance(right, PyTupleType):
            return PyTupleType(left.elements + right.elements)

        return PY_NONE

    def _infer_method(self, expr: PyMethodCall) -> PyType:
        """Infer return type for a method call."""
        ot = self.infer(expr.obj)

        if isinstance(ot, PyListType):
            if expr.method in ("append", "extend", "insert", "remove", "clear", "reverse", "sort"):
                return PY_NONE
            if expr.method == "pop":
                return ot.element
            if expr.method == "copy":
                return ot
            if expr.method == "count":
                return PY_INT
            if expr.method == "index":
                return PY_INT

        if isinstance(ot, PyDictType):
            if expr.method in ("get", "pop", "setdefault"):
                return PyOptionalType(ot.value)
            if expr.method == "keys":
                return PyListType(ot.key)
            if expr.method == "values":
                return PyListType(ot.value)
            if expr.method == "items":
                return PyListType(PyTupleType((ot.key, ot.value)))
            if expr.method in ("update", "clear"):
                return PY_NONE
            if expr.method == "copy":
                return ot

        if isinstance(ot, PyPrimitiveType) and ot.literal is PyLiteral.STR:
            if expr.method in (
                "upper", "lower", "strip", "lstrip", "rstrip",
                "title", "capitalize", "swapcase", "center",
                "ljust", "rjust", "zfill", "replace", "format",
                "join", "encode",
            ):
                return PY_STR
            if expr.method in ("split", "rsplit", "splitlines"):
                return PyListType(PY_STR)
            if expr.method in ("find", "rfind", "index", "rindex", "count"):
                return PY_INT
            if expr.method in (
                "startswith", "endswith", "isalpha", "isdigit",
                "isalnum", "isspace", "isupper", "islower",
            ):
                return PY_BOOL

        if isinstance(ot, PySetType):
            if expr.method in ("add", "remove", "discard", "clear", "update"):
                return PY_NONE
            if expr.method in ("union", "intersection", "difference", "symmetric_difference", "copy"):
                return ot
            if expr.method in ("issubset", "issuperset", "isdisjoint"):
                return PY_BOOL
            if expr.method == "pop":
                return ot.element

        if isinstance(ot, PyClassType) and expr.method in ot.methods:
            return ot.methods[expr.method].return_type

        return PY_NONE

    def infer_stmt(self, stmt: PyStmt) -> TypeEnv:
        """
        Process a statement and return an updated environment.
        """
        if isinstance(stmt, PyAssign):
            if stmt.type_annotation:
                self.bind(stmt.target, stmt.type_annotation)
            else:
                self.bind(stmt.target, self.infer(stmt.value))
            return self

        if isinstance(stmt, PyAugAssign):
            existing = self.lookup(stmt.target)
            val_t = self.infer(stmt.value)
            if existing:
                self.bind(stmt.target, self._infer_binop(stmt.op, existing, val_t))
            else:
                self.bind(stmt.target, val_t)
            return self

        if isinstance(stmt, PyFor):
            iter_t = self.infer(stmt.iter_expr)
            if isinstance(iter_t, PyListType):
                self.bind(stmt.target, iter_t.element)
            elif isinstance(iter_t, PyDictType):
                self.bind(stmt.target, iter_t.key)
            elif isinstance(iter_t, PySetType):
                self.bind(stmt.target, iter_t.element)
            else:
                self.bind(stmt.target, PY_NONE)
            child = self.child()
            for s in stmt.body:
                child.infer_stmt(s)
            return self

        if isinstance(stmt, PyIf):
            then_env = self.child()
            for s in stmt.body:
                then_env.infer_stmt(s)
            else_env = self.child()
            for s in stmt.orelse:
                else_env.infer_stmt(s)
            return self

        if isinstance(stmt, PyWhile):
            child = self.child()
            for s in stmt.body:
                child.infer_stmt(s)
            return self

        return self

    def __repr__(self) -> str:
        entries = ", ".join(f"{k}: {v.to_lean()}" for k, v in self.bindings.items())
        parent_info = " (has parent)" if self.parent else ""
        return f"TypeEnv({{{entries}}}{parent_info})"

    def __contains__(self, name: str) -> bool:
        return self.lookup(name) is not None

    def depth(self) -> int:
        """Return nesting depth of this scope."""
        if self.parent is None:
            return 0
        return 1 + self.parent.depth()

    def flatten(self) -> Dict[str, PyType]:
        """Same as all_bindings — flattened view."""
        return self.all_bindings()


# ---------------------------------------------------------------------------
# Convenience factory for building default global environments
# ---------------------------------------------------------------------------

def make_builtin_env() -> TypeEnv:
    """
    Create a TypeEnv pre-populated with Python's built-in names.
    """
    builtins: Dict[str, PyType] = {
        "int": PyFunctionType((PY_NONE,), PY_INT),
        "float": PyFunctionType((PY_NONE,), PY_FLOAT),
        "str": PyFunctionType((PY_NONE,), PY_STR),
        "bool": PyFunctionType((PY_NONE,), PY_BOOL),
        "bytes": PyFunctionType((PY_NONE,), PY_BYTES),
        "list": PyFunctionType((PY_NONE,), PyListType(PY_NONE)),
        "dict": PyFunctionType((), PyDictType(PY_STR, PY_NONE)),
        "set": PyFunctionType((PY_NONE,), PySetType(PY_NONE)),
        "tuple": PyFunctionType((PY_NONE,), PyTupleType(())),
        "len": PyFunctionType((PY_NONE,), PY_INT),
        "range": PyFunctionType((PY_INT,), PyListType(PY_INT)),
        "enumerate": PyFunctionType(
            (PyListType(PY_NONE),),
            PyListType(PyTupleType((PY_INT, PY_NONE))),
        ),
        "zip": PyFunctionType(
            (PyListType(PY_NONE), PyListType(PY_NONE)),
            PyListType(PyTupleType(())),
        ),
        "map": PyFunctionType(
            (PyFunctionType((PY_NONE,), PY_NONE), PyListType(PY_NONE)),
            PyListType(PY_NONE),
        ),
        "filter": PyFunctionType(
            (PyFunctionType((PY_NONE,), PY_BOOL), PyListType(PY_NONE)),
            PyListType(PY_NONE),
        ),
        "sorted": PyFunctionType((PyListType(PY_NONE),), PyListType(PY_NONE)),
        "reversed": PyFunctionType((PyListType(PY_NONE),), PyListType(PY_NONE)),
        "print": PyFunctionType((PY_NONE,), PY_NONE),
        "input": PyFunctionType((PY_STR,), PY_STR),
        "isinstance": PyFunctionType((PY_NONE, PY_NONE), PY_BOOL),
        "type": PyFunctionType((PY_NONE,), PY_STR),
        "abs": PyFunctionType((PY_INT,), PY_INT),
        "max": PyFunctionType((PY_NONE,), PY_INT),
        "min": PyFunctionType((PY_NONE,), PY_INT),
        "sum": PyFunctionType((PyListType(PY_INT),), PY_INT),
        "round": PyFunctionType((PY_FLOAT,), PY_INT),
        "ord": PyFunctionType((PY_STR,), PY_INT),
        "chr": PyFunctionType((PY_INT,), PY_STR),
        "hex": PyFunctionType((PY_INT,), PY_STR),
        "oct": PyFunctionType((PY_INT,), PY_STR),
        "bin": PyFunctionType((PY_INT,), PY_STR),
        "id": PyFunctionType((PY_NONE,), PY_INT),
        "hash": PyFunctionType((PY_NONE,), PY_INT),
        "repr": PyFunctionType((PY_NONE,), PY_STR),
        "open": PyFunctionType((PY_STR,), PY_NONE),
        "hasattr": PyFunctionType((PY_NONE, PY_STR), PY_BOOL),
        "getattr": PyFunctionType((PY_NONE, PY_STR), PY_NONE),
        "setattr": PyFunctionType((PY_NONE, PY_STR, PY_NONE), PY_NONE),
        "delattr": PyFunctionType((PY_NONE, PY_STR), PY_NONE),
        "callable": PyFunctionType((PY_NONE,), PY_BOOL),
        "iter": PyFunctionType((PY_NONE,), PY_NONE),
        "next": PyFunctionType((PY_NONE,), PY_NONE),
        "super": PyFunctionType((), PY_NONE),
        "True": PY_BOOL,
        "False": PY_BOOL,
        "None": PY_NONE,
        "NotImplemented": PY_NONE,
        "Ellipsis": PY_NONE,
        "Exception": PyClassType("Exception", {"args": PyTupleType(())}, {}),
        "ValueError": PyClassType("ValueError", {"args": PyTupleType(())}, {}),
        "TypeError": PyClassType("TypeError", {"args": PyTupleType(())}, {}),
        "KeyError": PyClassType("KeyError", {"args": PyTupleType(())}, {}),
        "IndexError": PyClassType("IndexError", {"args": PyTupleType(())}, {}),
        "AttributeError": PyClassType("AttributeError", {"args": PyTupleType(())}, {}),
        "RuntimeError": PyClassType("RuntimeError", {"args": PyTupleType(())}, {}),
        "StopIteration": PyClassType("StopIteration", {"args": PyTupleType(())}, {}),
        "AssertionError": PyClassType("AssertionError", {"args": PyTupleType(())}, {}),
    }
    return TypeEnv(bindings=builtins)


# ---------------------------------------------------------------------------
# Module-level quick-access helpers
# ---------------------------------------------------------------------------

def parse_python(source: str, module_name: str = "__main__") -> PyModule:
    """Parse Python source code and return the IR module."""
    converter = PythonToIR(source, module_name)
    return converter.convert()


def python_to_lean(source: str, module_name: str = "__main__") -> str:
    """Parse Python source code and return equivalent Lean 4 code."""
    module = parse_python(source, module_name)
    return module.to_lean_file()
