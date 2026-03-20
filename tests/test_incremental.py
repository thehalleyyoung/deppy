from __future__ import annotations

from pathlib import Path

from deppy.incremental import Workspace


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _normalize_report(report) -> dict:
    return {
        "updated_modules": tuple(sorted(report.updated_modules)),
        "reused_modules": tuple(sorted(report.reused_modules)),
        "warnings": tuple(sorted(report.warnings)),
        "errors": tuple(sorted(report.errors)),
        "diagnostics": tuple(sorted(d.pretty() for d in report.diagnostics)),
        "snapshots": {
            snapshot.relative_path: {
                "module_name": snapshot.module_name,
                "source_hash": snapshot.source_hash,
                "imports": snapshot.imports,
                "sections": snapshot.section_ids,
                "diagnostics": snapshot.diagnostics,
                "success": snapshot.success,
            }
            for snapshot in report.module_snapshots.values()
        },
    }


def test_workspace_incremental_matches_full_reanalysis(tmp_path: Path):
    _write(
        tmp_path / "pkg" / "__init__.py",
        "",
    )
    _write(
        tmp_path / "pkg" / "a.py",
        """
def make_number() -> int:
    return 1
""".strip()
        + "\n",
    )
    _write(
        tmp_path / "pkg" / "b.py",
        """
from pkg.a import make_number

def use_number() -> int:
    return make_number()
""".strip()
        + "\n",
    )
    _write(
        tmp_path / "pkg" / "c.py",
        """
def untouched(value: int) -> int:
    return value + 1
""".strip()
        + "\n",
    )

    workspace = Workspace(tmp_path)
    initial = workspace.analyze()

    assert sorted(initial.updated_modules) == [
        "pkg/__init__.py",
        "pkg/a.py",
        "pkg/b.py",
        "pkg/c.py",
    ]

    _write(
        tmp_path / "pkg" / "a.py",
        """
def make_number() -> int:
    value = 2
    return value
""".strip()
        + "\n",
    )

    workspace.notify_change(tmp_path / "pkg" / "a.py", changed_lines=[2, 3])
    incremental = workspace.reanalyze()

    fresh_workspace = Workspace(tmp_path)
    fresh_full = fresh_workspace.analyze()

    assert sorted(incremental.updated_modules) == ["pkg/a.py", "pkg/b.py"]
    assert "pkg/c.py" in incremental.reused_modules
    assert "pkg/__init__.py" in incremental.reused_modules
    assert _normalize_report(incremental)["snapshots"] == _normalize_report(fresh_full)["snapshots"]


def test_workspace_persistence_reuses_cached_modules(tmp_path: Path):
    cache_dir = tmp_path / ".cache"
    _write(
        tmp_path / "main.py",
        """
def answer() -> int:
    return 42
""".strip()
        + "\n",
    )

    first = Workspace(tmp_path, persist_cache=True, cache_dir=str(cache_dir))
    first_report = first.analyze()
    assert first_report.updated_modules == ("main.py",)

    second = Workspace(tmp_path, persist_cache=True, cache_dir=str(cache_dir))
    second_report = second.analyze()

    assert second_report.updated_modules == ()
    assert second_report.reused_modules == ("main.py",)
    assert _normalize_report(first_report)["snapshots"] == _normalize_report(second_report)["snapshots"]
