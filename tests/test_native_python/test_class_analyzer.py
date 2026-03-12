"""Tests for class analyzer: field/method/protocol analysis.

Covers FieldInfo, MethodInfo, ProtocolConformance, ClassAnalysisResult,
ClassAnalyzer.analyze_class, get_methods, get_initialized_fields,
check_protocol, detect_protocols, create_heap_sites.
"""

from __future__ import annotations

import ast
import textwrap

import pytest

from deppy.core._protocols import SiteKind
from deppy.native_python.class_analyzer import (
    ClassAnalysisResult,
    ClassAnalyzer,
    FieldInfo,
    MethodInfo,
    ProtocolConformance,
    _KNOWN_PROTOCOLS,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _parse_class(source: str) -> ast.ClassDef:
    """Parse a class definition from source and return the ClassDef node."""
    tree = ast.parse(textwrap.dedent(source))
    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef):
            return node
    raise ValueError("No class definition found in source")


# ===================================================================
#  FieldInfo
# ===================================================================


class TestFieldInfo:
    """Tests for FieldInfo dataclass."""

    def test_basic_properties(self):
        fi = FieldInfo(_name="x", _annotation="int", _init_line=5)
        assert fi.name == "x"
        assert fi.annotation == "int"
        assert fi.init_line == 5
        assert not fi.is_class_var
        assert not fi.is_private

    def test_private_field(self):
        fi = FieldInfo(_name="_secret", _is_private=True)
        assert fi.is_private

    def test_class_var(self):
        fi = FieldInfo(_name="COUNT", _is_class_var=True)
        assert fi.is_class_var

    def test_default_value(self):
        fi = FieldInfo(_name="x", _default_value="0")
        assert fi.default_value == "0"

    def test_assigned_from(self):
        fi = FieldInfo(_name="x", _assigned_from="some_expr")
        assert fi.assigned_from == "some_expr"


# ===================================================================
#  MethodInfo
# ===================================================================


class TestMethodInfo:
    """Tests for MethodInfo dataclass."""

    def test_basic(self):
        mi = MethodInfo(_name="foo", _params=("x", "y"), _return_annotation="int")
        assert mi.name == "foo"
        assert mi.params == ("x", "y")
        assert mi.return_annotation == "int"

    def test_is_dunder(self):
        mi = MethodInfo(_name="__init__")
        assert mi.is_dunder
        assert not mi.is_private

    def test_is_private(self):
        mi = MethodInfo(_name="_helper")
        assert mi.is_private
        assert not mi.is_dunder

    def test_static_method(self):
        mi = MethodInfo(_name="create", _is_static=True)
        assert mi.is_static

    def test_class_method(self):
        mi = MethodInfo(_name="from_dict", _is_classmethod=True)
        assert mi.is_classmethod

    def test_property(self):
        mi = MethodInfo(_name="value", _is_property=True)
        assert mi.is_property

    def test_abstract(self):
        mi = MethodInfo(_name="compute", _is_abstract=True)
        assert mi.is_abstract

    def test_async(self):
        mi = MethodInfo(_name="fetch", _is_async=True)
        assert mi.is_async

    def test_decorators(self):
        mi = MethodInfo(_name="f", _decorators=("staticmethod", "cache"))
        assert "staticmethod" in mi._decorators


# ===================================================================
#  ProtocolConformance
# ===================================================================


class TestProtocolConformance:
    """Tests for ProtocolConformance."""

    def test_conforms(self):
        pc = ProtocolConformance(
            _protocol_name="Iterator",
            _conforms=True,
            _present_methods=frozenset({"__iter__", "__next__"}),
            _missing_methods=frozenset(),
        )
        assert pc.conforms
        assert pc.protocol_name == "Iterator"
        assert len(pc.missing_methods) == 0

    def test_does_not_conform(self):
        pc = ProtocolConformance(
            _protocol_name="Iterator",
            _conforms=False,
            _present_methods=frozenset({"__iter__"}),
            _missing_methods=frozenset({"__next__"}),
        )
        assert not pc.conforms
        assert "__next__" in pc.missing_methods


# ===================================================================
#  ClassAnalyzer - field extraction
# ===================================================================


class TestClassAnalyzerFields:
    """Tests for ClassAnalyzer field extraction."""

    def setup_method(self):
        self.analyzer = ClassAnalyzer()

    def test_init_fields(self):
        cls = _parse_class("""\
        class Point:
            def __init__(self, x: int, y: int):
                self.x = x
                self.y = y
        """)
        result = self.analyzer.analyze_class(cls)
        assert "x" in result.fields
        assert "y" in result.fields
        assert result.has_init

    def test_init_field_annotations(self):
        cls = _parse_class("""\
        class MyClass:
            def __init__(self):
                self.name: str = "default"
        """)
        result = self.analyzer.analyze_class(cls)
        fi = result.fields.get("name")
        assert fi is not None
        assert fi.annotation == "str"

    def test_class_level_fields(self):
        cls = _parse_class("""\
        class Config:
            MAX_SIZE: int = 100
            debug = False
        """)
        result = self.analyzer.analyze_class(cls)
        assert "MAX_SIZE" in result.fields
        # Annotated class-level assignments are treated as instance fields
        # (like dataclass fields). Only bare assignments (without type
        # annotations) are classified as class variables.
        assert result.fields["debug"].is_class_var

    def test_instance_fields_property(self):
        cls = _parse_class("""\
        class Foo:
            class_var = 10
            def __init__(self):
                self.instance_var = 20
        """)
        result = self.analyzer.analyze_class(cls)
        inst = result.instance_fields
        assert "instance_var" in inst
        assert "class_var" not in inst

    def test_private_fields(self):
        cls = _parse_class("""\
        class Secured:
            def __init__(self):
                self._token = "abc"
                self.public = "xyz"
        """)
        result = self.analyzer.analyze_class(cls)
        assert result.fields["_token"].is_private
        assert not result.fields["public"].is_private


# ===================================================================
#  ClassAnalyzer - method extraction
# ===================================================================


class TestClassAnalyzerMethods:
    """Tests for ClassAnalyzer method extraction."""

    def setup_method(self):
        self.analyzer = ClassAnalyzer()

    def test_regular_methods(self):
        cls = _parse_class("""\
        class Calc:
            def add(self, a, b):
                return a + b
            def sub(self, a, b):
                return a - b
        """)
        result = self.analyzer.analyze_class(cls)
        assert "add" in result.methods
        assert "sub" in result.methods
        assert result.methods["add"].params == ("a", "b")

    def test_static_method(self):
        cls = _parse_class("""\
        class Factory:
            @staticmethod
            def create(data):
                return Factory()
        """)
        result = self.analyzer.analyze_class(cls)
        assert result.methods["create"].is_static

    def test_classmethod(self):
        cls = _parse_class("""\
        class Builder:
            @classmethod
            def from_dict(cls, d):
                return Builder()
        """)
        result = self.analyzer.analyze_class(cls)
        assert result.methods["from_dict"].is_classmethod

    def test_property_method(self):
        cls = _parse_class("""\
        class Box:
            @property
            def width(self):
                return self._width
        """)
        result = self.analyzer.analyze_class(cls)
        assert result.methods["width"].is_property

    def test_abstract_method(self):
        cls = _parse_class("""\
        class Shape:
            @abstractmethod
            def area(self):
                pass
        """)
        result = self.analyzer.analyze_class(cls)
        assert result.methods["area"].is_abstract
        assert result.is_abstract

    def test_public_methods(self):
        cls = _parse_class("""\
        class Obj:
            def __init__(self): pass
            def public(self): pass
            def _private(self): pass
        """)
        result = self.analyzer.analyze_class(cls)
        pub = result.public_methods
        assert "public" in pub
        assert "_private" not in pub
        assert "__init__" not in pub

    def test_dunder_methods(self):
        cls = _parse_class("""\
        class Container:
            def __init__(self): pass
            def __len__(self): return 0
            def __getitem__(self, idx): pass
        """)
        result = self.analyzer.analyze_class(cls)
        dunders = result.dunder_methods
        assert "__init__" in dunders
        assert "__len__" in dunders
        assert "__getitem__" in dunders


# ===================================================================
#  ClassAnalyzer - protocol detection
# ===================================================================


class TestClassAnalyzerProtocols:
    """Tests for protocol conformance detection."""

    def setup_method(self):
        self.analyzer = ClassAnalyzer()

    def test_iterable_protocol(self):
        cls = _parse_class("""\
        class MyIter:
            def __iter__(self): return self
            def __next__(self): return 1
        """)
        protocols = self.analyzer.detect_protocols(cls)
        assert "Iterator" in protocols
        assert "Iterable" in protocols

    def test_sized_protocol(self):
        cls = _parse_class("""\
        class MySized:
            def __len__(self): return 0
        """)
        protocols = self.analyzer.detect_protocols(cls)
        assert "Sized" in protocols

    def test_callable_protocol(self):
        cls = _parse_class("""\
        class Functor:
            def __call__(self, x): return x
        """)
        protocols = self.analyzer.detect_protocols(cls)
        assert "Callable" in protocols

    def test_context_manager_protocol(self):
        cls = _parse_class("""\
        class CM:
            def __enter__(self): return self
            def __exit__(self, *args): pass
        """)
        protocols = self.analyzer.detect_protocols(cls)
        assert "ContextManager" in protocols

    def test_check_protocol_explicit(self):
        cls = _parse_class("""\
        class Partial:
            def __getitem__(self, key): pass
        """)
        result = self.analyzer.check_protocol(cls, "Sequence")
        assert not result.conforms
        assert "__len__" in result.missing_methods

    def test_check_protocol_custom(self):
        cls = _parse_class("""\
        class MyObj:
            def serialize(self): pass
            def deserialize(self, data): pass
        """)
        result = self.analyzer.check_protocol(
            cls, "Serializable",
            required_methods=frozenset({"serialize", "deserialize"}),
        )
        assert result.conforms

    def test_no_conformance(self):
        cls = _parse_class("""\
        class Empty:
            pass
        """)
        protocols = self.analyzer.detect_protocols(cls)
        # Hashable might match if no __hash__ override, but the analyzer
        # only checks explicit definitions
        # The empty class has no methods, so no protocol should match
        assert "Iterator" not in protocols
        assert "Sized" not in protocols


# ===================================================================
#  ClassAnalyzer - other features
# ===================================================================


class TestClassAnalyzerMisc:
    """Tests for base classes, dataclass detection, slots, heap sites, cache."""

    def setup_method(self):
        self.analyzer = ClassAnalyzer()

    def test_base_classes(self):
        cls = _parse_class("""\
        class Child(Parent, Mixin):
            pass
        """)
        result = self.analyzer.analyze_class(cls)
        assert "Parent" in result.base_classes
        assert "Mixin" in result.base_classes

    def test_dataclass_detection(self):
        cls = _parse_class("""\
        @dataclass
        class Point:
            x: int = 0
            y: int = 0
        """)
        result = self.analyzer.analyze_class(cls)
        assert result.is_dataclass

    def test_slots_detection(self):
        cls = _parse_class("""\
        class Compact:
            __slots__ = ('x', 'y')
            def __init__(self):
                self.x = 0
                self.y = 0
        """)
        result = self.analyzer.analyze_class(cls)
        assert result._has_slots

    def test_create_heap_sites(self):
        cls = _parse_class("""\
        class Demo:
            def __init__(self):
                self.a = 1
                self.b = 2
            def __len__(self):
                return 2
        """)
        sites = self.analyzer.create_heap_sites(cls, file_path="test.py")
        kinds = {s.kind for s in sites}
        assert SiteKind.HEAP_PROTOCOL in kinds
        names = {s.name for s in sites}
        assert "Demo.__init__" in names
        assert "Demo.a" in names
        assert "Demo.b" in names

    def test_cache(self):
        cls = _parse_class("""\
        class Cached:
            def method(self): pass
        """)
        r1 = self.analyzer.analyze_class(cls)
        r2 = self.analyzer.analyze_class(cls)
        assert r1 is r2  # Same object from cache

    def test_clear_cache(self):
        cls = _parse_class("""\
        class Cached:
            def method(self): pass
        """)
        r1 = self.analyzer.analyze_class(cls)
        self.analyzer.clear_cache()
        r2 = self.analyzer.analyze_class(cls)
        assert r1 is not r2  # Different object after cache clear

    def test_async_method(self):
        cls = _parse_class("""\
        class AsyncService:
            async def fetch(self, url):
                pass
        """)
        result = self.analyzer.analyze_class(cls)
        assert result.methods["fetch"].is_async
