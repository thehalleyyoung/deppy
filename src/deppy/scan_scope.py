from __future__ import annotations

from pathlib import Path
from typing import List

DEFAULT_EXCLUDED_DIR_NAMES = frozenset(
    {
        "__pycache__",
        ".git",
        ".tox",
        ".venv",
        "venv",
        "env",
        ".mypy_cache",
        ".pytest_cache",
        "node_modules",
        ".lake",
        "vendor",
        "vendors",
        "third_party",
        "site-packages",
        "tests",
        "test",
        "testing",
        "examples",
        "example",
        "benchmarks",
        "benchmark",
        "fixtures",
        "fixture",
    }
)


def iter_default_python_files(root: Path) -> List[Path]:
    """Return Python files for the default repository-health scan."""
    resolved_root = root.resolve()
    candidates = [
        path.resolve()
        for path in sorted(resolved_root.rglob("*.py"))
        if path.is_file() and is_default_scannable_python_file(resolved_root, path)
    ]
    package_like = [
        path for path in candidates if _is_package_like_member(resolved_root, path)
    ]
    return package_like or candidates


def is_default_scannable_python_file(root: Path, path: Path) -> bool:
    """Return whether *path* belongs in the default directory scan."""
    resolved_root = root.resolve()
    resolved_path = path.resolve()
    try:
        relative_parts = resolved_path.relative_to(resolved_root).parts
    except ValueError:
        return True

    if not relative_parts:
        return False

    for part in relative_parts[:-1]:
        if part.startswith(".") or part in DEFAULT_EXCLUDED_DIR_NAMES:
            return False

    name = relative_parts[-1]
    if name.startswith("."):
        return False
    if name.startswith("test_") or name.endswith("_test.py"):
        return False
    return True


def _is_package_like_member(root: Path, path: Path) -> bool:
    """Return True for files under ``src/`` or within a Python package tree."""
    resolved_root = root.resolve()
    resolved_path = path.resolve()
    try:
        relative_parts = resolved_path.relative_to(resolved_root).parts
    except ValueError:
        return True

    if relative_parts and relative_parts[0] == "src":
        return True

    current = resolved_path.parent
    while True:
        if (current / "__init__.py").exists():
            return True
        if current == resolved_root:
            break
        current = current.parent
    return False
