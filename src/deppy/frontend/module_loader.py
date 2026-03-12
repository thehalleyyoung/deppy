"""Module loading and import resolution for the sheaf-theoretic frontend.

This module handles reading Python source files, parsing them into ASTs,
resolving imports (including relative imports), and building a module
dependency graph.  The dependency graph is used by the interprocedural
analysis stages to determine processing order and identify module-summary
observation sites.

In the sheaf view, each loaded module becomes a module-summary site whose
boundary sections describe the module's public API.  Import resolution
creates actual-to-formal reindexing morphisms between the importer's
sites and the imported module's export boundary.

Key classes:
- ``ModuleInfo``: dataclass holding a module's path, name, AST, and dependencies
- ``ModuleLoader``: loads Python files, resolves imports, builds dependency graph

Convenience functions:
- ``load_module(path)`` -> ``ModuleInfo``
- ``load_package(directory)`` -> ``Dict[str, ModuleInfo]``
"""

from __future__ import annotations

import ast
import os
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import (
    Any,
    Dict,
    FrozenSet,
    Iterator,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.static_analysis.observation_sites import SourceSpan
from deppy.frontend.ir.core_term import IRModule
from deppy.frontend.ast_visitor import IRLowering


# ═══════════════════════════════════════════════════════════════════════════════
# Module info
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class ImportInfo:
    """A single import declaration found in a module.

    Attributes:
        module_name: The fully-qualified module name being imported.
        names: Specific names imported (for ``from X import Y``).
        alias: Optional alias (``import X as Y``).
        is_relative: Whether this is a relative import.
        level: Relative import level (number of dots).
        span: Source location of the import statement.
    """
    module_name: Optional[str]
    names: Tuple[Tuple[str, Optional[str]], ...] = ()
    alias: Optional[str] = None
    is_relative: bool = False
    level: int = 0
    span: SourceSpan = field(default_factory=lambda: SourceSpan("<unknown>", 0, 0))


@dataclass
class ModuleInfo:
    """Information about a loaded Python module.

    This is the primary data structure produced by the module loader.
    It holds everything needed for the frontend IR lowering and cover
    synthesis stages.

    Attributes:
        path: Absolute filesystem path to the source file.
        name: Fully-qualified module name (e.g., ``mypackage.mymodule``).
        source: The raw Python source text.
        ast_tree: The parsed AST tree.
        dependencies: Set of fully-qualified module names this module imports.
        imports: List of import declarations found in the module.
        is_package: Whether this module is a package ``__init__.py``.
        package_name: The package this module belongs to (if any).
        ir_module: The lowered IR module (populated on demand).
        exported_names: Names explicitly exported (from ``__all__`` if present).
    """
    path: str
    name: str
    source: str
    ast_tree: ast.Module
    dependencies: Set[str] = field(default_factory=set)
    imports: List[ImportInfo] = field(default_factory=list)
    is_package: bool = False
    package_name: Optional[str] = None
    ir_module: Optional[IRModule] = None
    exported_names: Optional[List[str]] = None

    @property
    def filename(self) -> str:
        """Basename of the source file."""
        return os.path.basename(self.path)

    def lower_to_ir(self) -> IRModule:
        """Lower the AST to IR on demand and cache the result."""
        if self.ir_module is None:
            lowering = IRLowering(filename=self.path)
            self.ir_module = lowering.lower_module(self.ast_tree, module_name=self.name)
        return self.ir_module

    def span(self) -> SourceSpan:
        """Return a SourceSpan for the entire module."""
        return SourceSpan(file=self.path, start_line=1, start_col=0)


# ═══════════════════════════════════════════════════════════════════════════════
# Module loader
# ═══════════════════════════════════════════════════════════════════════════════


class ModuleLoader:
    """Loads Python source files, resolves imports, and builds a dependency graph.

    The loader maintains a cache of loaded modules and resolves relative
    imports using package structure.  It can operate in two modes:

    1. Single-file mode: load a single module via ``load(path)``.
    2. Package mode: load an entire package via ``load_package(dir)``.

    Usage::

        loader = ModuleLoader()
        info = loader.load("path/to/my_module.py")
        # info.ast_tree is the parsed AST
        # info.dependencies is the set of imported module names

        # Or load a whole package:
        loader.load_package("path/to/mypackage/")
        for name, info in loader.modules.items():
            ir = info.lower_to_ir()
    """

    def __init__(
        self,
        *,
        search_paths: Optional[List[str]] = None,
        follow_imports: bool = True,
        max_depth: int = 10,
    ) -> None:
        self._search_paths: List[str] = search_paths or []
        self._follow_imports = follow_imports
        self._max_depth = max_depth
        self._modules: Dict[str, ModuleInfo] = {}
        self._loading: Set[str] = set()  # Cycle detection

    @property
    def modules(self) -> Dict[str, ModuleInfo]:
        """All loaded modules, keyed by fully-qualified name."""
        return dict(self._modules)

    def load(
        self,
        path: str,
        *,
        module_name: Optional[str] = None,
        package_name: Optional[str] = None,
    ) -> ModuleInfo:
        """Load a single Python source file.

        Args:
            path: Path to the .py file.
            module_name: Optional explicit module name. If not given,
                derived from the filename.
            package_name: Optional package context for relative import resolution.

        Returns:
            A ``ModuleInfo`` dataclass with the parsed AST and dependency info.
        """
        abs_path = os.path.abspath(path)

        # Check cache
        if module_name and module_name in self._modules:
            return self._modules[module_name]

        # Derive module name from path if not given
        if module_name is None:
            module_name = self._path_to_module_name(abs_path)

        # Detect cycles
        if module_name in self._loading:
            # Return a stub for circular imports
            return self._create_stub(abs_path, module_name)

        self._loading.add(module_name)

        try:
            # Read and parse
            source = self._read_source(abs_path)
            tree = ast.parse(source, filename=abs_path)

            # Determine if this is a package __init__
            is_package = os.path.basename(abs_path) == "__init__.py"

            # Extract imports
            imports = self._extract_imports(tree, abs_path, module_name, package_name)
            dependencies = self._compute_dependencies(imports, module_name, package_name)

            # Extract __all__ if present
            exported_names = self._extract_all(tree)

            info = ModuleInfo(
                path=abs_path,
                name=module_name,
                source=source,
                ast_tree=tree,
                dependencies=dependencies,
                imports=imports,
                is_package=is_package,
                package_name=package_name,
                exported_names=exported_names,
            )

            self._modules[module_name] = info

            # Optionally follow imports
            if self._follow_imports:
                self._follow_module_imports(info, depth=0)

            return info

        finally:
            self._loading.discard(module_name)

    def load_package(
        self,
        directory: str,
        *,
        package_name: Optional[str] = None,
    ) -> Dict[str, ModuleInfo]:
        """Load all Python modules in a package directory.

        Recursively discovers ``.py`` files and ``__init__.py`` packages
        within the given directory.

        Args:
            directory: Path to the package root directory.
            package_name: Optional explicit package name. If not given,
                derived from the directory name.

        Returns:
            Dictionary mapping module names to ModuleInfo objects.
        """
        abs_dir = os.path.abspath(directory)
        if package_name is None:
            package_name = os.path.basename(abs_dir)

        # Add directory to search paths
        parent_dir = os.path.dirname(abs_dir)
        if parent_dir not in self._search_paths:
            self._search_paths.append(parent_dir)

        # Load __init__.py if present
        init_path = os.path.join(abs_dir, "__init__.py")
        if os.path.isfile(init_path):
            self.load(
                init_path,
                module_name=package_name,
                package_name=package_name,
            )

        # Walk directory for .py files
        for entry in sorted(os.listdir(abs_dir)):
            full_path = os.path.join(abs_dir, entry)

            if os.path.isfile(full_path) and entry.endswith(".py"):
                if entry == "__init__.py":
                    continue  # Already loaded above
                stem = entry[:-3]
                mod_name = f"{package_name}.{stem}"
                self.load(full_path, module_name=mod_name, package_name=package_name)

            elif os.path.isdir(full_path):
                sub_init = os.path.join(full_path, "__init__.py")
                if os.path.isfile(sub_init):
                    sub_pkg = f"{package_name}.{entry}"
                    self.load_package(full_path, package_name=sub_pkg)

        return {k: v for k, v in self._modules.items() if k.startswith(package_name)}

    def get_module(self, name: str) -> Optional[ModuleInfo]:
        """Look up a loaded module by name."""
        return self._modules.get(name)

    def dependency_order(self) -> List[str]:
        """Return module names in topological (dependency) order.

        Modules with no dependencies come first, and modules that depend
        on others come after their dependencies.
        """
        visited: Set[str] = set()
        order: List[str] = []

        def dfs(name: str) -> None:
            if name in visited:
                return
            visited.add(name)
            info = self._modules.get(name)
            if info is not None:
                for dep in info.dependencies:
                    if dep in self._modules:
                        dfs(dep)
            order.append(name)

        for name in self._modules:
            dfs(name)

        return order

    def dependency_graph(self) -> Dict[str, Set[str]]:
        """Return the dependency graph as an adjacency dict.

        Each key is a module name; its value is the set of module names
        it depends on (imports from).
        """
        return {
            name: info.dependencies & set(self._modules.keys())
            for name, info in self._modules.items()
        }

    # ── Internal helpers ──────────────────────────────────────────────────

    def _read_source(self, path: str) -> str:
        """Read a Python source file."""
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            return f.read()

    def _path_to_module_name(self, path: str) -> str:
        """Derive a module name from a file path."""
        # Try to find a package root
        parts: List[str] = []
        current = path

        if current.endswith(".py"):
            stem = os.path.basename(current)[:-3]
            if stem == "__init__":
                current = os.path.dirname(current)
                stem = os.path.basename(current)
            parts.append(stem)
            current = os.path.dirname(current)

        # Walk up looking for __init__.py
        for _ in range(self._max_depth):
            init_path = os.path.join(current, "__init__.py")
            if os.path.isfile(init_path):
                parts.append(os.path.basename(current))
                current = os.path.dirname(current)
            else:
                break

        parts.reverse()
        if parts:
            return ".".join(parts)
        return os.path.basename(path).replace(".py", "")

    def _extract_imports(
        self,
        tree: ast.Module,
        filepath: str,
        module_name: str,
        package_name: Optional[str],
    ) -> List[ImportInfo]:
        """Extract all import declarations from an AST."""
        imports: List[ImportInfo] = []

        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    imports.append(ImportInfo(
                        module_name=alias.name,
                        alias=alias.asname,
                        span=SourceSpan.from_ast(node, filepath),
                    ))

            elif isinstance(node, ast.ImportFrom):
                names = tuple(
                    (alias.name, alias.asname) for alias in node.names
                )
                level = node.level or 0
                imports.append(ImportInfo(
                    module_name=node.module,
                    names=names,
                    is_relative=level > 0,
                    level=level,
                    span=SourceSpan.from_ast(node, filepath),
                ))

        return imports

    def _compute_dependencies(
        self,
        imports: List[ImportInfo],
        module_name: str,
        package_name: Optional[str],
    ) -> Set[str]:
        """Compute the set of module names this module depends on."""
        deps: Set[str] = set()

        for imp in imports:
            if imp.is_relative:
                resolved = self._resolve_relative_import(
                    imp.module_name, imp.level, module_name, package_name,
                )
                if resolved:
                    deps.add(resolved)
            elif imp.module_name:
                # Top-level module name for regular imports
                top = imp.module_name.split(".")[0]
                deps.add(imp.module_name)

        return deps

    def _resolve_relative_import(
        self,
        module_name: Optional[str],
        level: int,
        current_module: str,
        package_name: Optional[str],
    ) -> Optional[str]:
        """Resolve a relative import to an absolute module name.

        A relative import like ``from ..sibling import foo`` with
        level=2 from ``pkg.sub.module`` resolves to ``pkg.sibling``.
        """
        if package_name is None:
            return module_name

        # Split the current module into parts
        parts = current_module.split(".")

        # Remove 'level' parts from the end to get the base
        if level > len(parts):
            return module_name  # Cannot resolve

        base_parts = parts[:max(0, len(parts) - level)]
        base = ".".join(base_parts)

        if module_name:
            if base:
                return f"{base}.{module_name}"
            return module_name
        return base or None

    def _extract_all(self, tree: ast.Module) -> Optional[List[str]]:
        """Extract __all__ from the module AST, if present."""
        for node in tree.body:
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name) and target.id == "__all__":
                        if isinstance(node.value, (ast.List, ast.Tuple)):
                            names: List[str] = []
                            for elt in node.value.elts:
                                if isinstance(elt, ast.Constant) and isinstance(elt.value, str):
                                    names.append(elt.value)
                            return names
        return None

    def _follow_module_imports(self, info: ModuleInfo, depth: int) -> None:
        """Recursively load imported modules (up to max_depth)."""
        if depth >= self._max_depth:
            return

        for dep_name in info.dependencies:
            if dep_name in self._modules:
                continue
            if dep_name in self._loading:
                continue

            # Try to find the module file
            dep_path = self._find_module_path(dep_name)
            if dep_path is not None:
                try:
                    pkg = dep_name.rsplit(".", 1)[0] if "." in dep_name else None
                    dep_info = self.load(
                        dep_path,
                        module_name=dep_name,
                        package_name=pkg,
                    )
                except Exception:
                    # Skip modules that can't be loaded
                    pass

    def _find_module_path(self, module_name: str) -> Optional[str]:
        """Find the filesystem path for a module name."""
        parts = module_name.split(".")
        relative_path = os.path.join(*parts)

        for search_path in self._search_paths:
            # Try as a package
            pkg_init = os.path.join(search_path, relative_path, "__init__.py")
            if os.path.isfile(pkg_init):
                return pkg_init

            # Try as a module
            mod_file = os.path.join(search_path, relative_path + ".py")
            if os.path.isfile(mod_file):
                return mod_file

        return None

    def _create_stub(self, path: str, module_name: str) -> ModuleInfo:
        """Create a stub ModuleInfo for circular import breaking."""
        stub_tree = ast.parse("", filename=path)
        return ModuleInfo(
            path=path,
            name=module_name,
            source="",
            ast_tree=stub_tree,
            dependencies=set(),
            imports=[],
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Convenience functions
# ═══════════════════════════════════════════════════════════════════════════════


def load_module(
    path: str,
    *,
    module_name: Optional[str] = None,
    follow_imports: bool = False,
) -> ModuleInfo:
    """Load a single Python module and return its ModuleInfo.

    This is the simplest entry point for the module loader.  It reads
    the file, parses it, extracts imports, and optionally follows them.

    Args:
        path: Path to the .py file.
        module_name: Optional explicit module name.
        follow_imports: Whether to recursively load imported modules.

    Returns:
        A ``ModuleInfo`` with the parsed AST and dependency information.
    """
    loader = ModuleLoader(follow_imports=follow_imports)
    return loader.load(path, module_name=module_name)


def load_package(
    directory: str,
    *,
    package_name: Optional[str] = None,
    follow_imports: bool = False,
) -> Dict[str, ModuleInfo]:
    """Load all Python modules in a package directory.

    Recursively discovers ``.py`` files and subpackages, returning
    a dictionary mapping fully-qualified module names to ModuleInfo objects.

    Args:
        directory: Path to the package root.
        package_name: Optional explicit package name.
        follow_imports: Whether to follow external imports.

    Returns:
        Dictionary of module name -> ModuleInfo.
    """
    loader = ModuleLoader(follow_imports=follow_imports)
    return loader.load_package(directory, package_name=package_name)


def load_source(
    source: str,
    *,
    filename: str = "<string>",
    module_name: str = "<module>",
) -> ModuleInfo:
    """Load a module from a source string.

    This is useful for testing and for analysing code fragments.

    Args:
        source: Python source text.
        filename: Virtual filename for source span tracking.
        module_name: Module name for the loaded module.

    Returns:
        A ``ModuleInfo`` with the parsed AST.
    """
    tree = ast.parse(source, filename=filename)
    imports = _extract_imports_from_tree(tree, filename)
    deps = {
        imp.module_name
        for imp in imports
        if imp.module_name is not None
    }

    return ModuleInfo(
        path=filename,
        name=module_name,
        source=source,
        ast_tree=tree,
        dependencies=deps,
        imports=imports,
    )


def _extract_imports_from_tree(
    tree: ast.Module,
    filename: str,
) -> List[ImportInfo]:
    """Extract imports from an AST for the convenience functions."""
    imports: List[ImportInfo] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                imports.append(ImportInfo(
                    module_name=alias.name,
                    alias=alias.asname,
                    span=SourceSpan.from_ast(node, filename),
                ))
        elif isinstance(node, ast.ImportFrom):
            names = tuple(
                (alias.name, alias.asname) for alias in node.names
            )
            imports.append(ImportInfo(
                module_name=node.module,
                names=names,
                is_relative=(node.level or 0) > 0,
                level=node.level or 0,
                span=SourceSpan.from_ast(node, filename),
            ))
    return imports
