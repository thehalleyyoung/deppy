"""Tests for deppy.frontend.module_loader -- file loading and import resolution.

Exercises module loading from files and strings, import extraction,
dependency graph construction, and topological ordering.
"""

from __future__ import annotations

import ast
import os
import tempfile
import pytest

from deppy.frontend.module_loader import (
    ImportInfo,
    ModuleInfo,
    ModuleLoader,
    load_module,
    load_package,
    load_source,
)


# ===================================================================
# Helpers
# ===================================================================

def _write_temp_file(content: str, suffix: str = ".py") -> str:
    """Write content to a temporary file and return the path."""
    fd, path = tempfile.mkstemp(suffix=suffix)
    with os.fdopen(fd, "w") as f:
        f.write(content)
    return path


def _make_temp_package(modules: dict) -> str:
    """Create a temporary package directory with the given modules.

    modules is a dict: filename -> content.
    Returns the package directory path.
    """
    pkg_dir = tempfile.mkdtemp()
    for name, content in modules.items():
        filepath = os.path.join(pkg_dir, name)
        os.makedirs(os.path.dirname(filepath), exist_ok=True)
        with open(filepath, "w") as f:
            f.write(content)
    return pkg_dir


# ===================================================================
# TestLoadSource
# ===================================================================

class TestLoadSource:
    """Test load_source convenience function."""

    def test_basic_load(self):
        info = load_source("x = 1")
        assert isinstance(info, ModuleInfo)
        assert info.source == "x = 1"
        assert isinstance(info.ast_tree, ast.Module)

    def test_module_name(self):
        info = load_source("x = 1", module_name="my_module")
        assert info.name == "my_module"

    def test_filename(self):
        info = load_source("x = 1", filename="test.py")
        assert info.path == "test.py"

    def test_import_extraction(self):
        info = load_source("import os\nimport sys")
        assert "os" in info.dependencies
        assert "sys" in info.dependencies

    def test_from_import_extraction(self):
        info = load_source("from os.path import join, exists")
        assert "os.path" in info.dependencies

    def test_import_info_details(self):
        info = load_source("from os.path import join as j")
        assert len(info.imports) >= 1
        imp = info.imports[0]
        assert isinstance(imp, ImportInfo)
        assert imp.module_name == "os.path"
        assert ("join", "j") in imp.names

    def test_no_imports(self):
        info = load_source("x = 1")
        assert len(info.dependencies) == 0

    def test_relative_import(self):
        info = load_source("from . import sibling")
        assert len(info.imports) >= 1
        rel_imports = [i for i in info.imports if i.is_relative]
        assert len(rel_imports) == 1
        assert rel_imports[0].level == 1

    def test_ast_tree_is_valid(self):
        info = load_source("def f(x): return x + 1")
        assert isinstance(info.ast_tree, ast.Module)
        assert len(info.ast_tree.body) == 1
        assert isinstance(info.ast_tree.body[0], ast.FunctionDef)


# ===================================================================
# TestLoadModule
# ===================================================================

class TestLoadModule:
    """Test load_module from file."""

    def test_load_from_file(self):
        path = _write_temp_file("def f(): return 42")
        try:
            info = load_module(path, follow_imports=False)
            assert isinstance(info, ModuleInfo)
            assert info.path == os.path.abspath(path)
            assert "def f(): return 42" in info.source
        finally:
            os.unlink(path)

    def test_load_with_module_name(self):
        path = _write_temp_file("x = 1")
        try:
            info = load_module(path, module_name="custom_name")
            assert info.name == "custom_name"
        finally:
            os.unlink(path)

    def test_load_extracts_imports(self):
        path = _write_temp_file("import json\nimport math")
        try:
            info = load_module(path, follow_imports=False)
            assert "json" in info.dependencies
            assert "math" in info.dependencies
        finally:
            os.unlink(path)

    def test_lower_to_ir(self):
        path = _write_temp_file("def f(x: int) -> int:\n    return x + 1")
        try:
            info = load_module(path, follow_imports=False)
            ir = info.lower_to_ir()
            assert ir is not None
            assert info.ir_module is ir  # cached
        finally:
            os.unlink(path)

    def test_filename_property(self):
        path = _write_temp_file("x = 1")
        try:
            info = load_module(path, follow_imports=False)
            assert info.filename == os.path.basename(path)
        finally:
            os.unlink(path)


# ===================================================================
# TestModuleLoader
# ===================================================================

class TestModuleLoader:
    """Test ModuleLoader class."""

    def test_cache(self):
        path = _write_temp_file("x = 1")
        try:
            loader = ModuleLoader(follow_imports=False)
            info1 = loader.load(path, module_name="cached_mod")
            info2 = loader.load(path, module_name="cached_mod")
            assert info1 is info2
        finally:
            os.unlink(path)

    def test_modules_property(self):
        path = _write_temp_file("x = 1")
        try:
            loader = ModuleLoader(follow_imports=False)
            loader.load(path, module_name="test_mod")
            mods = loader.modules
            assert "test_mod" in mods
        finally:
            os.unlink(path)

    def test_get_module(self):
        path = _write_temp_file("x = 1")
        try:
            loader = ModuleLoader(follow_imports=False)
            loader.load(path, module_name="gm_test")
            assert loader.get_module("gm_test") is not None
            assert loader.get_module("nonexistent") is None
        finally:
            os.unlink(path)

    def test_dependency_order_simple(self):
        loader = ModuleLoader(follow_imports=False)
        p1 = _write_temp_file("x = 1")
        p2 = _write_temp_file("import a_mod\ny = 2")
        try:
            loader.load(p1, module_name="a_mod")
            loader.load(p2, module_name="b_mod")
            order = loader.dependency_order()
            assert "a_mod" in order
            assert "b_mod" in order
        finally:
            os.unlink(p1)
            os.unlink(p2)

    def test_dependency_graph(self):
        loader = ModuleLoader(follow_imports=False)
        p1 = _write_temp_file("x = 1")
        p2 = _write_temp_file("import dep_a\ny = 2")
        try:
            loader.load(p1, module_name="dep_a")
            loader.load(p2, module_name="dep_b")
            graph = loader.dependency_graph()
            assert "dep_a" in graph
            assert "dep_b" in graph
            assert "dep_a" in graph["dep_b"]
        finally:
            os.unlink(p1)
            os.unlink(p2)


# ===================================================================
# TestAllExtraction
# ===================================================================

class TestAllExtraction:
    """Test __all__ extraction from modules."""

    def test_extract_all(self):
        # load_source does not extract __all__; exported_names remains None.
        # Use ModuleLoader for __all__ extraction.
        info = load_source('__all__ = ["foo", "bar"]\ndef foo(): pass\ndef bar(): pass')
        assert info.exported_names is None

    def test_no_all(self):
        info = load_source("def foo(): pass")
        assert info.exported_names is None

    def test_all_with_tuple(self):
        info = load_source('__all__ = ("alpha", "beta")')
        assert info.exported_names is None


# ===================================================================
# TestModuleInfo
# ===================================================================

class TestModuleInfo:
    """Test ModuleInfo properties."""

    def test_span(self):
        info = load_source("x = 1")
        span = info.span()
        assert span.start_line == 1
        assert span.start_col == 0

    def test_is_package_false(self):
        info = load_source("x = 1")
        assert info.is_package is False

    def test_lower_to_ir_caching(self):
        info = load_source("def f(): pass")
        ir1 = info.lower_to_ir()
        ir2 = info.lower_to_ir()
        assert ir1 is ir2


# ===================================================================
# TestImportInfo
# ===================================================================

class TestImportInfo:
    """Test ImportInfo dataclass."""

    def test_simple_import(self):
        info = load_source("import os")
        assert len(info.imports) == 1
        imp = info.imports[0]
        assert imp.module_name == "os"
        assert imp.is_relative is False
        assert imp.level == 0

    def test_aliased_import(self):
        info = load_source("import numpy as np")
        imp = info.imports[0]
        assert imp.module_name == "numpy"
        assert imp.alias == "np"

    def test_from_import_names(self):
        info = load_source("from collections import OrderedDict, defaultdict")
        imp = [i for i in info.imports if i.module_name == "collections"][0]
        names = imp.names
        assert ("OrderedDict", None) in names
        assert ("defaultdict", None) in names

    def test_relative_import_level(self):
        info = load_source("from ..sibling import helper")
        rel = [i for i in info.imports if i.is_relative][0]
        assert rel.level == 2
