from __future__ import annotations

import importlib
from types import SimpleNamespace

from deppy.cli.commands import CheckCommand
from deppy.cli import commands as command_module
from deppy.hybrid.diagnostics.localization import (
    CheckResult,
    Diagnostic,
    DiagnosticSeverity,
)

cli_main_module = importlib.import_module("deppy.cli.main")


def test_main_delegates_freeform_prompt_to_agent_cli(monkeypatch) -> None:
    called: dict[str, list[str]] = {}

    def fake_agent(argv: list[str]) -> int:
        called["argv"] = argv
        return 7

    monkeypatch.setattr(cli_main_module, "_run_agent_cli", fake_agent)

    exit_code = cli_main_module.main(["build a verified trading system"])

    assert exit_code == 7
    assert called["argv"] == ["build a verified trading system"]


def test_main_normalizes_path_to_check(monkeypatch, tmp_path) -> None:
    sample = tmp_path / "sample.py"
    sample.write_text("def f(x):\n    return x\n", encoding="utf-8")

    captured: dict[str, object] = {}

    class FakeCommand:
        def run(self, cli_config):  # type: ignore[no-untyped-def]
            captured["subcommand"] = cli_config.subcommand
            captured["source_paths"] = cli_config.source_paths
            return 0

    monkeypatch.setattr(cli_main_module, "get_command", lambda _name: FakeCommand())
    monkeypatch.setattr(cli_main_module, "find_config_file", lambda: None)

    exit_code = cli_main_module.main([str(sample)])

    assert exit_code == 0
    assert captured["subcommand"] == "check"
    assert captured["source_paths"] == (str(sample),)


def test_main_delegates_prompt_with_leading_agent_flags(monkeypatch) -> None:
    called: dict[str, list[str]] = {}

    def fake_agent(argv: list[str]) -> int:
        called["argv"] = argv
        return 5

    monkeypatch.setattr(cli_main_module, "_run_agent_cli", fake_agent)

    exit_code = cli_main_module.main(
        [
            "--ideation",
            "--orchestration",
            "--lean",
            "--strict",
            "--verbose",
            "build a verified trading system",
        ]
    )

    assert exit_code == 5
    assert called["argv"][-1] == "build a verified trading system"


def test_main_normalizes_path_with_leading_global_flags(
    monkeypatch, tmp_path
) -> None:
    sample = tmp_path / "sample.py"
    sample.write_text("def f(x):\n    return x\n", encoding="utf-8")

    captured: dict[str, object] = {}

    class FakeCommand:
        def run(self, cli_config):  # type: ignore[no-untyped-def]
            captured["subcommand"] = cli_config.subcommand
            captured["source_paths"] = cli_config.source_paths
            return 0

    monkeypatch.setattr(cli_main_module, "get_command", lambda _name: FakeCommand())
    monkeypatch.setattr(cli_main_module, "find_config_file", lambda: None)

    exit_code = cli_main_module.main(["--verbose", str(sample)])

    assert exit_code == 0
    assert captured["subcommand"] == "check"
    assert captured["source_paths"] == (str(sample),)


def test_check_command_prefers_hybrid_existing_code_checker(
    monkeypatch, tmp_path, capsys
) -> None:
    sample = tmp_path / "sample.py"
    sample.write_text("def f(x):\n    return x\n", encoding="utf-8")

    class FakeResult:
        def __init__(self, file_path: str) -> None:
            self.file_path = file_path
            self.diagnostics = []
            self.h1_dimension = 0

        def has_errors(self) -> bool:
            return False

        def summary(self) -> str:
            return f"{self.file_path}: ✔ no issues (H¹ dim = 0)"

        def to_dict(self) -> dict[str, object]:
            return {"file_path": self.file_path}

    class FakeChecker:
        def __init__(self, **_kwargs) -> None:
            pass

        def check_file(self, path: str) -> FakeResult:
            return FakeResult(path)

    class FakeFormatter:
        def __init__(self, **_kwargs) -> None:
            pass

        def format_terminal(self, _diagnostics) -> str:
            return "✔ No issues found.\n"

        def format_sarif(self, _diagnostics) -> dict[str, object]:
            return {"version": "2.1.0"}

    monkeypatch.setattr(command_module, "_HybridExistingCodeChecker", FakeChecker)
    monkeypatch.setattr(command_module, "_HybridDiagnosticFormatter", FakeFormatter)

    cli_config = SimpleNamespace(
        source_paths=(str(sample),),
        verbosity=1,
        output_format="plain",
        color=False,
    )

    exit_code = CheckCommand().run(cli_config)
    captured = capsys.readouterr()

    assert exit_code == 0
    assert "no issues" in captured.out.lower()
    assert str(sample) in captured.out


def test_check_command_filters_default_repo_health_scope(tmp_path) -> None:
    repo = tmp_path / "repo"
    pkg = repo / "src" / "pkg"
    tests_dir = repo / "tests"
    examples_dir = repo / "examples"
    vendor_dir = repo / "vendor"
    pkg.mkdir(parents=True)
    tests_dir.mkdir(parents=True)
    examples_dir.mkdir(parents=True)
    vendor_dir.mkdir(parents=True)

    (pkg / "__init__.py").write_text("", encoding="utf-8")
    (pkg / "core.py").write_text("def core():\n    return 1\n", encoding="utf-8")
    (tests_dir / "test_core.py").write_text(
        "def test_core():\n    return None\n",
        encoding="utf-8",
    )
    (examples_dir / "demo.py").write_text("def demo():\n    return 1\n", encoding="utf-8")
    (vendor_dir / "helper.py").write_text("def helper():\n    return 1\n", encoding="utf-8")
    (repo / "tool.py").write_text("def tool():\n    return 1\n", encoding="utf-8")

    cli_config = SimpleNamespace(source_paths=(str(repo),))

    files = CheckCommand()._resolve_source_files(cli_config)

    assert str((pkg / "core.py").resolve()) in files
    assert str((pkg / "__init__.py").resolve()) in files
    assert str((tests_dir / "test_core.py").resolve()) not in files
    assert str((examples_dir / "demo.py").resolve()) not in files
    assert str((vendor_dir / "helper.py").resolve()) not in files
    assert str((repo / "tool.py").resolve()) not in files


def test_check_command_keeps_root_scripts_when_no_package_like_code(tmp_path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()
    script = repo / "tool.py"
    script.write_text("def tool():\n    return 1\n", encoding="utf-8")
    (repo / "tests").mkdir()
    (repo / "tests" / "test_tool.py").write_text(
        "def test_tool():\n    return None\n",
        encoding="utf-8",
    )

    cli_config = SimpleNamespace(source_paths=(str(repo),))

    files = CheckCommand()._resolve_source_files(cli_config)

    assert str(script.resolve()) in files


def test_main_accepts_html_report_arguments(monkeypatch, tmp_path) -> None:
    sample = tmp_path / "sample.py"
    sample.write_text("def f(x):\n    return x\n", encoding="utf-8")
    report = tmp_path / "report.html"

    captured: dict[str, object] = {}

    class FakeCommand:
        def run(self, cli_config):  # type: ignore[no-untyped-def]
            captured["output_format"] = cli_config.output_format
            captured["generate_output"] = cli_config.generate_output
            return 0

    monkeypatch.setattr(cli_main_module, "get_command", lambda _name: FakeCommand())
    monkeypatch.setattr(cli_main_module, "find_config_file", lambda: None)

    exit_code = cli_main_module.main(
        ["--format", "html", "check", str(sample), "--output", str(report)]
    )

    assert exit_code == 0
    assert captured["output_format"] == "html"
    assert captured["generate_output"] == str(report)


def test_check_command_writes_hybrid_html_report(
    monkeypatch, tmp_path, capsys
) -> None:
    sample = tmp_path / "sample.py"
    sample.write_text("def f(x):\n    return x\n", encoding="utf-8")
    report = tmp_path / "deppy-report.html"

    class FakeChecker:
        def __init__(self, **_kwargs) -> None:
            pass

        def check_file(self, path: str) -> CheckResult:
            return CheckResult(
                file_path=path,
                h1_dimension=1,
                diagnostics=[
                    Diagnostic(
                        file_path=path,
                        line_start=1,
                        line_end=1,
                        col_start=0,
                        col_end=10,
                        severity=DiagnosticSeverity.WARNING,
                        code="DEPPY-IS-001",
                        message="Unenforced intent",
                        detail="The docstring claims behavior that is not enforced structurally.",
                        intent_fragment="Return a normalized value.",
                        code_fragment="def f(x):\n    return x\n",
                        trust_level="LLM_JUDGED",
                    )
                ],
                trust_summary={"LLM_JUDGED": 1},
            )

    class FakeFormatter:
        def __init__(self, **_kwargs) -> None:
            pass

    monkeypatch.setattr(command_module, "_HybridExistingCodeChecker", FakeChecker)
    monkeypatch.setattr(command_module, "_HybridDiagnosticFormatter", FakeFormatter)

    cli_config = SimpleNamespace(
        source_paths=(str(sample),),
        verbosity=1,
        output_format="html",
        color=False,
        generate_output=str(report),
    )

    exit_code = CheckCommand().run(cli_config)
    captured = capsys.readouterr()

    assert exit_code == 0
    assert report.exists()
    html = report.read_text(encoding="utf-8")
    assert "<html" in html.lower()
    assert "Signal quality" in html
    assert "Independent issue groups" in html
    assert "H¹" not in html
    assert "Unenforced intent" in html
    assert "Wrote HTML report to" in captured.out


def test_check_command_html_report_prioritizes_issues_and_hides_clean_files(
    monkeypatch, tmp_path, capsys
) -> None:
    clean = tmp_path / "clean.py"
    clean.write_text("def ok(x):\n    return x\n", encoding="utf-8")
    noisy = tmp_path / "noisy.py"
    noisy.write_text("def bad(x):\n    return x\n", encoding="utf-8")
    report = tmp_path / "ranked-report.html"

    class FakeChecker:
        def __init__(self, **_kwargs) -> None:
            pass

        def check_file(self, path: str) -> CheckResult:
            if path.endswith("clean.py"):
                return CheckResult(file_path=path, diagnostics=[], h1_dimension=0, trust_summary={})
            return CheckResult(
                file_path=path,
                h1_dimension=2,
                diagnostics=[
                    Diagnostic(
                        file_path=path,
                        line_start=2,
                        line_end=2,
                        col_start=4,
                        col_end=10,
                        severity=DiagnosticSeverity.WARNING,
                        code="DEPPY-IS-001",
                        message="Unenforced intent",
                        detail="Heuristic warning only.",
                        trust_level="LLM_JUDGED",
                    ),
                    Diagnostic(
                        file_path=path,
                        line_start=1,
                        line_end=1,
                        col_start=0,
                        col_end=12,
                        severity=DiagnosticSeverity.ERROR,
                        code="DEPPY-SC-001",
                        message="Type–code mismatch",
                        detail="Strong structural mismatch.",
                        trust_level="Z3_PROVEN",
                    ),
                ],
                trust_summary={"LLM_JUDGED": 1, "Z3_PROVEN": 1},
            )

    class FakeFormatter:
        def __init__(self, **_kwargs) -> None:
            pass

    monkeypatch.setattr(command_module, "_HybridExistingCodeChecker", FakeChecker)
    monkeypatch.setattr(command_module, "_HybridDiagnosticFormatter", FakeFormatter)

    cli_config = SimpleNamespace(
        source_paths=(str(clean), str(noisy)),
        verbosity=1,
        output_format="html",
        color=False,
        generate_output=str(report),
    )

    exit_code = CheckCommand().run(cli_config)
    captured = capsys.readouterr()

    assert exit_code == 1
    assert "Wrote HTML report to" in captured.out
    html = report.read_text(encoding="utf-8")
    assert str(clean) not in html
    assert str(noisy) in html
    assert "Most likely issues" in html
    assert html.index("Type–code mismatch") < html.index("Unenforced intent")
