"""Constructor analysis, field initialization, and protocol conformance.

Analyzes Python class definitions to determine:
- Which fields are initialized in __init__ and their types
- Method signatures for protocol conformance checking
- Protocol detection from class body
- HEAP_PROTOCOL site creation for field access patterns

In the sheaf-descent framework, a class definition produces sites in the
HEAP_PROTOCOL family.  Each field initialization creates a site, and
protocol conformance is checked by comparing the class's method set
against known protocol definitions.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteSite


# ---------------------------------------------------------------------------
# Field information
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class FieldInfo:
    """Information about a class field.

    Attributes:
        _name: Field name.
        _annotation: Type annotation AST node (if present).
        _default_value: Default value AST node (if present).
        _init_line: Line number of initialization.
        _is_class_var: Whether this is a class variable (not instance).
        _is_private: Whether the field name starts with underscore.
        _assigned_from: Expression description of the assigned value.
    """

    _name: str
    _annotation: Optional[str] = None
    _default_value: Optional[str] = None
    _init_line: int = 0
    _is_class_var: bool = False
    _is_private: bool = False
    _assigned_from: Optional[str] = None

    @property
    def name(self) -> str:
        return self._name

    @property
    def annotation(self) -> Optional[str]:
        return self._annotation

    @property
    def default_value(self) -> Optional[str]:
        return self._default_value

    @property
    def init_line(self) -> int:
        return self._init_line

    @property
    def is_class_var(self) -> bool:
        return self._is_class_var

    @property
    def is_private(self) -> bool:
        return self._is_private

    @property
    def assigned_from(self) -> Optional[str]:
        return self._assigned_from


# ---------------------------------------------------------------------------
# Method information
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class MethodInfo:
    """Information about a class method.

    Attributes:
        _name: Method name.
        _params: Parameter names (excluding self/cls).
        _return_annotation: Return type annotation string.
        _is_static: Whether this is a static method.
        _is_classmethod: Whether this is a class method.
        _is_property: Whether this is a property.
        _is_abstract: Whether this is an abstract method.
        _is_async: Whether this is an async method.
        _decorators: Names of decorators applied.
        _line: Source line number.
    """

    _name: str
    _params: Tuple[str, ...] = ()
    _return_annotation: Optional[str] = None
    _is_static: bool = False
    _is_classmethod: bool = False
    _is_property: bool = False
    _is_abstract: bool = False
    _is_async: bool = False
    _decorators: Tuple[str, ...] = ()
    _line: int = 0

    @property
    def name(self) -> str:
        return self._name

    @property
    def params(self) -> Tuple[str, ...]:
        return self._params

    @property
    def return_annotation(self) -> Optional[str]:
        return self._return_annotation

    @property
    def is_static(self) -> bool:
        return self._is_static

    @property
    def is_classmethod(self) -> bool:
        return self._is_classmethod

    @property
    def is_property(self) -> bool:
        return self._is_property

    @property
    def is_abstract(self) -> bool:
        return self._is_abstract

    @property
    def is_async(self) -> bool:
        return self._is_async

    @property
    def is_dunder(self) -> bool:
        return self._name.startswith("__") and self._name.endswith("__")

    @property
    def is_private(self) -> bool:
        return self._name.startswith("_") and not self.is_dunder


# ---------------------------------------------------------------------------
# Protocol conformance
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ProtocolConformance:
    """Result of checking protocol conformance for a class.

    Attributes:
        _protocol_name: Name of the protocol being checked.
        _conforms: Whether the class fully conforms.
        _present_methods: Methods the class implements.
        _missing_methods: Methods the protocol requires but class lacks.
        _extra_methods: Methods the class has beyond protocol requirements.
    """

    _protocol_name: str
    _conforms: bool = False
    _present_methods: FrozenSet[str] = frozenset()
    _missing_methods: FrozenSet[str] = frozenset()
    _extra_methods: FrozenSet[str] = frozenset()

    @property
    def protocol_name(self) -> str:
        return self._protocol_name

    @property
    def conforms(self) -> bool:
        return self._conforms

    @property
    def present_methods(self) -> FrozenSet[str]:
        return self._present_methods

    @property
    def missing_methods(self) -> FrozenSet[str]:
        return self._missing_methods


# Known protocols and their required methods
_KNOWN_PROTOCOLS: Dict[str, FrozenSet[str]] = {
    "Iterator": frozenset({"__iter__", "__next__"}),
    "Iterable": frozenset({"__iter__"}),
    "Sized": frozenset({"__len__"}),
    "Container": frozenset({"__contains__"}),
    "Hashable": frozenset({"__hash__"}),
    "Reversible": frozenset({"__reversed__"}),
    "Sequence": frozenset({"__getitem__", "__len__"}),
    "MutableSequence": frozenset({
        "__getitem__", "__setitem__", "__delitem__",
        "__len__", "insert",
    }),
    "Mapping": frozenset({"__getitem__", "__len__", "__iter__"}),
    "MutableMapping": frozenset({
        "__getitem__", "__setitem__", "__delitem__",
        "__len__", "__iter__",
    }),
    "Set": frozenset({
        "__contains__", "__iter__", "__len__",
    }),
    "Callable": frozenset({"__call__"}),
    "ContextManager": frozenset({"__enter__", "__exit__"}),
    "AsyncContextManager": frozenset({"__aenter__", "__aexit__"}),
    "AsyncIterator": frozenset({"__aiter__", "__anext__"}),
    "SupportsInt": frozenset({"__int__"}),
    "SupportsFloat": frozenset({"__float__"}),
    "SupportsComplex": frozenset({"__complex__"}),
    "SupportsBytes": frozenset({"__bytes__"}),
    "SupportsAbs": frozenset({"__abs__"}),
    "SupportsRound": frozenset({"__round__"}),
    "SupportsIndex": frozenset({"__index__"}),
    "Buffer": frozenset({"__buffer__"}),
}


# ---------------------------------------------------------------------------
# Class analysis result
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ClassAnalysisResult:
    """Complete analysis result for a class definition.

    Attributes:
        _class_name: Name of the analyzed class.
        _base_classes: Names of base classes.
        _fields: All discovered fields.
        _methods: All discovered methods.
        _class_variables: Class-level variable assignments.
        _protocol_conformances: Protocol conformance results.
        _has_init: Whether the class defines __init__.
        _has_slots: Whether the class uses __slots__.
        _is_dataclass: Whether the class uses @dataclass.
        _is_abstract: Whether the class has abstract methods.
        _decorators: Class-level decorators.
    """

    _class_name: str
    _base_classes: Tuple[str, ...] = ()
    _fields: Dict[str, FieldInfo] = field(default_factory=dict)
    _methods: Dict[str, MethodInfo] = field(default_factory=dict)
    _class_variables: Dict[str, str] = field(default_factory=dict)
    _protocol_conformances: Dict[str, ProtocolConformance] = field(
        default_factory=dict
    )
    _has_init: bool = False
    _has_slots: bool = False
    _is_dataclass: bool = False
    _is_abstract: bool = False
    _decorators: Tuple[str, ...] = ()

    @property
    def class_name(self) -> str:
        return self._class_name

    @property
    def base_classes(self) -> Tuple[str, ...]:
        return self._base_classes

    @property
    def fields(self) -> Dict[str, FieldInfo]:
        return dict(self._fields)

    @property
    def methods(self) -> Dict[str, MethodInfo]:
        return dict(self._methods)

    @property
    def protocol_conformances(self) -> Dict[str, ProtocolConformance]:
        return dict(self._protocol_conformances)

    @property
    def has_init(self) -> bool:
        return self._has_init

    @property
    def is_dataclass(self) -> bool:
        return self._is_dataclass

    @property
    def is_abstract(self) -> bool:
        return self._is_abstract

    @property
    def public_methods(self) -> Dict[str, MethodInfo]:
        return {
            n: m for n, m in self._methods.items()
            if not m.is_private and not m.is_dunder
        }

    @property
    def dunder_methods(self) -> Dict[str, MethodInfo]:
        return {
            n: m for n, m in self._methods.items() if m.is_dunder
        }

    @property
    def instance_fields(self) -> Dict[str, FieldInfo]:
        return {
            n: f for n, f in self._fields.items() if not f.is_class_var
        }


# ---------------------------------------------------------------------------
# AST helpers
# ---------------------------------------------------------------------------

def _annotation_to_str(node: Optional[ast.expr]) -> Optional[str]:
    """Convert an annotation AST node to a string."""
    if node is None:
        return None
    return ast.unparse(node)


def _decorator_name(node: ast.expr) -> str:
    """Extract decorator name from AST node."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return ast.unparse(node)
    if isinstance(node, ast.Call):
        return _decorator_name(node.func)
    return ast.unparse(node)


def _get_base_names(class_node: ast.ClassDef) -> Tuple[str, ...]:
    """Extract base class names from a class definition."""
    names: List[str] = []
    for base in class_node.bases:
        if isinstance(base, ast.Name):
            names.append(base.id)
        elif isinstance(base, ast.Attribute):
            names.append(ast.unparse(base))
        elif isinstance(base, ast.Subscript):
            if isinstance(base.value, ast.Name):
                names.append(base.value.id)
            else:
                names.append(ast.unparse(base))
        else:
            names.append(ast.unparse(base))
    return tuple(names)


# ---------------------------------------------------------------------------
# Field initialization analysis
# ---------------------------------------------------------------------------

class _InitFieldCollector(ast.NodeVisitor):
    """Collect field initializations from __init__."""

    def __init__(self, class_name: str) -> None:
        self._class_name = class_name
        self._fields: Dict[str, FieldInfo] = {}
        self._current_line = 0

    @property
    def fields(self) -> Dict[str, FieldInfo]:
        return dict(self._fields)

    def visit_Assign(self, node: ast.Assign) -> None:
        self._current_line = getattr(node, "lineno", 0)
        for target in node.targets:
            self._check_self_assign(target, node.value)
        self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        self._current_line = getattr(node, "lineno", 0)
        if node.target is not None:
            annotation = _annotation_to_str(node.annotation)
            self._check_self_assign(
                node.target, node.value, annotation=annotation
            )
        self.generic_visit(node)

    def _check_self_assign(
        self,
        target: ast.expr,
        value: Optional[ast.expr],
        annotation: Optional[str] = None,
    ) -> None:
        """Check if an assignment is self.field = value."""
        if isinstance(target, ast.Attribute):
            if isinstance(target.value, ast.Name) and target.value.id == "self":
                field_name = target.attr
                value_str = ast.unparse(value) if value is not None else None
                is_private = field_name.startswith("_")

                self._fields[field_name] = FieldInfo(
                    _name=field_name,
                    _annotation=annotation,
                    _default_value=value_str,
                    _init_line=self._current_line,
                    _is_class_var=False,
                    _is_private=is_private,
                    _assigned_from=value_str,
                )


# ---------------------------------------------------------------------------
# Class-level field collector
# ---------------------------------------------------------------------------

class _ClassFieldCollector(ast.NodeVisitor):
    """Collect class-level variable assignments and annotations."""

    def __init__(self) -> None:
        self._fields: Dict[str, FieldInfo] = {}
        self._class_vars: Dict[str, str] = {}
        self._in_method = False

    @property
    def fields(self) -> Dict[str, FieldInfo]:
        return dict(self._fields)

    @property
    def class_vars(self) -> Dict[str, str]:
        return dict(self._class_vars)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        pass  # Don't descend into methods

    visit_AsyncFunctionDef = visit_FunctionDef

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if isinstance(node.target, ast.Name):
            name = node.target.id
            annotation = _annotation_to_str(node.annotation)
            value_str = ast.unparse(node.value) if node.value is not None else None
            line = getattr(node, "lineno", 0)

            # Check if ClassVar
            is_class_var = False
            if annotation and "ClassVar" in annotation:
                is_class_var = True

            self._fields[name] = FieldInfo(
                _name=name,
                _annotation=annotation,
                _default_value=value_str,
                _init_line=line,
                _is_class_var=is_class_var,
                _is_private=name.startswith("_"),
            )
            if is_class_var and value_str:
                self._class_vars[name] = value_str

    def visit_Assign(self, node: ast.Assign) -> None:
        for target in node.targets:
            if isinstance(target, ast.Name):
                name = target.id
                value_str = ast.unparse(node.value)
                line = getattr(node, "lineno", 0)

                self._class_vars[name] = value_str
                self._fields[name] = FieldInfo(
                    _name=name,
                    _default_value=value_str,
                    _init_line=line,
                    _is_class_var=True,
                    _is_private=name.startswith("_"),
                )


# ---------------------------------------------------------------------------
# ClassAnalyzer
# ---------------------------------------------------------------------------

class ClassAnalyzer:
    """Analyze Python class definitions for the sheaf-descent type system.

    Extracts field initialization patterns, method signatures, protocol
    conformance, and creates HEAP_PROTOCOL sites for each class.
    """

    def __init__(self) -> None:
        self._analysis_cache: Dict[str, ClassAnalysisResult] = {}

    # -- Core analysis ------------------------------------------------------

    def analyze_class(
        self,
        class_ast: ast.ClassDef,
    ) -> ClassAnalysisResult:
        """Perform full analysis of a class definition.

        Returns a ClassAnalysisResult with field, method, and protocol info.
        """
        class_name = class_ast.name

        # Check cache
        if class_name in self._analysis_cache:
            return self._analysis_cache[class_name]

        # Extract base classes
        bases = _get_base_names(class_ast)

        # Extract class-level decorators
        decorators = tuple(
            _decorator_name(d) for d in class_ast.decorator_list
        )
        is_dataclass = any(
            d in ("dataclass", "dataclasses.dataclass") for d in decorators
        )

        # Extract methods
        methods = self.get_methods(class_ast)

        # Extract fields from __init__
        init_fields: Dict[str, FieldInfo] = {}
        has_init = False
        for item in class_ast.body:
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if item.name == "__init__":
                    has_init = True
                    init_fields = self.get_initialized_fields(item)
                    break

        # Extract class-level fields
        class_collector = _ClassFieldCollector()
        for stmt in class_ast.body:
            class_collector.visit(stmt)

        # Merge fields: init fields override class-level fields
        all_fields: Dict[str, FieldInfo] = {}
        all_fields.update(class_collector.fields)
        all_fields.update(init_fields)

        # Check for __slots__
        has_slots = "__slots__" in class_collector.class_vars

        # Check for abstract methods
        is_abstract = any(m.is_abstract for m in methods.values())

        # Check protocol conformance
        method_names = frozenset(methods.keys())
        conformances: Dict[str, ProtocolConformance] = {}
        for proto_name, required in _KNOWN_PROTOCOLS.items():
            present = method_names & required
            missing = required - method_names
            extra = method_names - required
            conforms = len(missing) == 0

            conformances[proto_name] = ProtocolConformance(
                _protocol_name=proto_name,
                _conforms=conforms,
                _present_methods=frozenset(present),
                _missing_methods=frozenset(missing),
                _extra_methods=frozenset(extra),
            )

        result = ClassAnalysisResult(
            _class_name=class_name,
            _base_classes=bases,
            _fields=all_fields,
            _methods=methods,
            _class_variables=class_collector.class_vars,
            _protocol_conformances=conformances,
            _has_init=has_init,
            _has_slots=has_slots,
            _is_dataclass=is_dataclass,
            _is_abstract=is_abstract,
            _decorators=decorators,
        )
        self._analysis_cache[class_name] = result
        return result

    # -- Field extraction ---------------------------------------------------

    def get_initialized_fields(
        self,
        init_ast: ast.FunctionDef,
    ) -> Dict[str, FieldInfo]:
        """Extract field initializations from an __init__ method.

        Looks for ``self.field = value`` patterns in the __init__ body.
        """
        collector = _InitFieldCollector(
            class_name=init_ast.name if hasattr(init_ast, "name") else "<init>"
        )
        for stmt in init_ast.body:
            collector.visit(stmt)
        return collector.fields

    # -- Method extraction --------------------------------------------------

    def get_methods(
        self,
        class_ast: ast.ClassDef,
    ) -> Dict[str, MethodInfo]:
        """Extract all methods from a class body."""
        methods: Dict[str, MethodInfo] = {}

        for item in class_ast.body:
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                method_info = self._analyze_method(item)
                methods[item.name] = method_info

        return methods

    def _analyze_method(
        self,
        func_node: ast.FunctionDef,
    ) -> MethodInfo:
        """Analyze a single method definition."""
        name = func_node.name
        is_async = isinstance(func_node, ast.AsyncFunctionDef)

        # Extract decorators
        dec_names: List[str] = []
        is_static = False
        is_classmethod = False
        is_property = False
        is_abstract = False

        for dec in func_node.decorator_list:
            dec_name = _decorator_name(dec)
            dec_names.append(dec_name)
            if dec_name == "staticmethod":
                is_static = True
            elif dec_name == "classmethod":
                is_classmethod = True
            elif dec_name in ("property", "abc.abstractproperty"):
                is_property = True
            elif dec_name in (
                "abstractmethod", "abc.abstractmethod",
                "abstractproperty", "abc.abstractproperty",
            ):
                is_abstract = True

        # Extract parameters (skip self/cls)
        params: List[str] = []
        for arg in func_node.args.args:
            if arg.arg in ("self", "cls"):
                continue
            params.append(arg.arg)

        # Extract return annotation
        return_ann = _annotation_to_str(func_node.returns)

        line = getattr(func_node, "lineno", 0)

        return MethodInfo(
            _name=name,
            _params=tuple(params),
            _return_annotation=return_ann,
            _is_static=is_static,
            _is_classmethod=is_classmethod,
            _is_property=is_property,
            _is_abstract=is_abstract,
            _is_async=is_async,
            _decorators=tuple(dec_names),
            _line=line,
        )

    # -- Protocol conformance -----------------------------------------------

    def check_protocol(
        self,
        class_ast: ast.ClassDef,
        protocol_name: str,
        required_methods: Optional[FrozenSet[str]] = None,
    ) -> ProtocolConformance:
        """Check if a class conforms to a specific protocol."""
        if required_methods is None:
            required_methods = _KNOWN_PROTOCOLS.get(protocol_name, frozenset())

        methods = self.get_methods(class_ast)
        method_names = frozenset(methods.keys())

        present = method_names & required_methods
        missing = required_methods - method_names
        extra = method_names - required_methods

        return ProtocolConformance(
            _protocol_name=protocol_name,
            _conforms=len(missing) == 0,
            _present_methods=frozenset(present),
            _missing_methods=frozenset(missing),
            _extra_methods=frozenset(extra),
        )

    def detect_protocols(
        self,
        class_ast: ast.ClassDef,
    ) -> List[str]:
        """Detect which known protocols a class conforms to."""
        methods = self.get_methods(class_ast)
        method_names = frozenset(methods.keys())

        conforming: List[str] = []
        for proto_name, required in _KNOWN_PROTOCOLS.items():
            if required <= method_names:
                conforming.append(proto_name)

        return conforming

    # -- Site creation ------------------------------------------------------

    def create_heap_sites(
        self,
        class_ast: ast.ClassDef,
        file_path: str = "<unknown>",
    ) -> List[SiteId]:
        """Create HEAP_PROTOCOL site IDs for a class's fields and methods."""
        result = self.analyze_class(class_ast)
        sites: List[SiteId] = []

        # Constructor site
        if result.has_init:
            sites.append(SiteId(
                kind=SiteKind.HEAP_PROTOCOL,
                name=f"{result.class_name}.__init__",
                source_location=(file_path, 0, 0),
            ))

        # Field sites
        for field_name, info in result.fields.items():
            sites.append(SiteId(
                kind=SiteKind.HEAP_PROTOCOL,
                name=f"{result.class_name}.{field_name}",
                source_location=(file_path, info.init_line, 0),
            ))

        # Protocol conformance sites
        for proto_name, conformance in result.protocol_conformances.items():
            if conformance.conforms:
                sites.append(SiteId(
                    kind=SiteKind.HEAP_PROTOCOL,
                    name=f"{result.class_name}.protocol_{proto_name}",
                    source_location=(file_path, 0, 0),
                ))

        return sites

    def clear_cache(self) -> None:
        """Clear the analysis cache."""
        self._analysis_cache.clear()
