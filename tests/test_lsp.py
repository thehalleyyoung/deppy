from __future__ import annotations

import importlib
import sys
import types
from pathlib import Path
from types import SimpleNamespace

import pytest

from deppy.core._protocols import LocalSection, SiteId, SiteKind, TrustLevel
from deppy.lsp.compat import lsp_types
from deppy.lsp.diagnostics import diagnostic_to_lsp
from deppy.lsp.hover import build_hover_payload
from deppy.lsp.models import DocumentAnalysisState, LspConfig
from deppy.pipeline.pipeline import PipelineResult
from deppy.pipeline.stages.render_stage import (
    ContractAnnotation,
    Diagnostic,
    DiagnosticLocation,
    DiagnosticSeverity,
)


def _reload_server_module() -> object:
    module = importlib.import_module("deppy.lsp.server")
    return importlib.reload(module)


def test_diagnostic_to_lsp_maps_core_fields(tmp_path: Path) -> None:
    path = tmp_path / "sample.py"
    diagnostic = Diagnostic(
        _severity=DiagnosticSeverity.ERROR,
        _message="Type incompatibility detected",
        _location=DiagnosticLocation(
            _file=str(path),
            _line=4,
            _col=2,
            _end_line=4,
            _end_col=8,
        ),
        _code="SHEAF001",
        _suggestion="Add a contract",
        _related=(
            DiagnosticLocation(_file=str(path), _line=9, _col=1),
        ),
    )

    converted = diagnostic_to_lsp(diagnostic)

    assert converted.message.endswith("Suggestion: Add a contract")
    assert converted.code == "SHEAF001"
    assert converted.source == "deppy"
    assert converted.severity == lsp_types.DiagnosticSeverity.Error
    assert converted.range.start.line == 3
    assert converted.range.start.character == 1
    assert converted.range.end.line == 3
    assert converted.range.end.character == 7
    assert converted.related_information is not None
    assert converted.related_information[0].location.uri.endswith("/sample.py")


def test_diagnostic_to_lsp_sanitizes_missing_location() -> None:
    diagnostic = Diagnostic(
        _severity=DiagnosticSeverity.WARNING,
        _message="Analysis incomplete",
        _location=None,
        _code="SHEAF002",
    )

    converted = diagnostic_to_lsp(diagnostic, default_uri="file:///virtual.py")

    assert converted.severity == lsp_types.DiagnosticSeverity.Warning
    assert converted.range.start.line == 0
    assert converted.range.start.character == 0
    assert converted.range.end.character == 1


def test_build_hover_payload_for_contract(tmp_path: Path) -> None:
    path = tmp_path / "hover.py"
    site = SiteId(
        kind=SiteKind.ARGUMENT_BOUNDARY,
        name="x",
        source_location=(str(path), 3, 5),
    )
    contract = ContractAnnotation(
        _scope_name="identity",
        _kind="requires",
        _predicate_text="x: '>= 0'",
        _variable="x",
        _trust=TrustLevel.PROOF_BACKED,
        _source_sites=(site,),
    )
    section = LocalSection(
        site_id=site,
        carrier_type="int",
        refinements={"lower_bound": 0},
        trust=TrustLevel.PROOF_BACKED,
    )
    state = DocumentAnalysisState(
        uri=path.as_uri(),
        path=str(path),
        version=1,
        source_text="def identity(x):\n    return x\n",
        pipeline_result=PipelineResult(
            _sections={site: section},
            _contracts=(contract,),
        ),
        diagnostics=(),
        contracts=(contract,),
        warnings=(),
    )

    payload = build_hover_payload(state, 2, 4)

    assert payload is not None
    assert payload.title == "requires contract"
    assert "proof-backed contract" in payload.markdown
    assert "@requires(lambda x: x: '>= 0')" in payload.markdown
    assert "`int`" in payload.markdown
    assert "lower_bound" in payload.markdown


def test_build_hover_payload_for_diagnostic(tmp_path: Path) -> None:
    path = tmp_path / "hover.py"
    diagnostic = Diagnostic(
        _severity=DiagnosticSeverity.INFO,
        _message="Residual trust remains",
        _location=DiagnosticLocation(_file=str(path), _line=2, _col=1),
        _code="SHEAF003",
        _suggestion="Add an annotation",
    )
    state = DocumentAnalysisState(
        uri=path.as_uri(),
        path=str(path),
        version=1,
        source_text="def f(x):\n    return x\n",
        pipeline_result=None,
        diagnostics=(diagnostic,),
        contracts=(),
        warnings=(),
    )

    payload = build_hover_payload(state, 1, 0)

    assert payload is not None
    assert payload.title == "analysis diagnostic"
    assert "Residual trust remains" in payload.markdown
    assert "Add an annotation" in payload.markdown


def test_main_reports_missing_pygls_when_unavailable(capsys: pytest.CaptureFixture[str]) -> None:
    server_module = _reload_server_module()
    if server_module.PYGLS_AVAILABLE:
        pytest.skip("pygls is installed in this environment")

    exit_code = server_module.main(["--stdio"])

    captured = capsys.readouterr()
    assert exit_code == 1
    assert "pygls" in captured.err


def test_create_server_with_fake_pygls(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    class FakeLanguageServer:
        def __init__(self, name: str, version: str) -> None:
            self.name = name
            self.version = version
            self.features: dict[str, object] = {}
            self.published: list[tuple[str, list[object], int | None]] = []
            self.logs: list[tuple[str, object]] = []
            self.started = False

        def feature(self, method: str):
            def decorator(func):
                self.features[method] = func
                return func

            return decorator

        def publish_diagnostics(self, uri: str, diagnostics: list[object], version: int | None = None) -> None:
            self.published.append((uri, diagnostics, version))

        def show_message_log(self, message: str, message_type: object) -> None:
            self.logs.append((message, message_type))

        def start_io(self) -> None:
            self.started = True

    fake_pygls = types.ModuleType("pygls")
    fake_server_module = types.ModuleType("pygls.server")
    fake_server_module.LanguageServer = FakeLanguageServer
    fake_pygls.server = fake_server_module
    monkeypatch.setitem(sys.modules, "pygls", fake_pygls)
    monkeypatch.setitem(sys.modules, "pygls.server", fake_server_module)

    server_module = _reload_server_module()

    path = tmp_path / "sample.py"
    uri = path.as_uri()
    site = SiteId(
        kind=SiteKind.ARGUMENT_BOUNDARY,
        name="x",
        source_location=(str(path), 1, 5),
    )
    contract = ContractAnnotation(
        _scope_name="f",
        _kind="requires",
        _predicate_text="x: '>= 0'",
        _variable="x",
        _trust=TrustLevel.TRUSTED_AUTO,
        _source_sites=(site,),
    )
    diagnostic = Diagnostic(
        _severity=DiagnosticSeverity.WARNING,
        _message="Analysis did not converge",
        _location=DiagnosticLocation(_file=str(path), _line=1, _col=1),
        _code="SHEAF002",
    )

    class FakePipeline:
        def _execute_pipeline(self, context: dict[str, object]) -> PipelineResult:
            assert context["source_path"] == str(path)
            return PipelineResult(
                _sections={
                    site: LocalSection(
                        site_id=site,
                        carrier_type="int",
                        refinements={"lower_bound": 0},
                        trust=TrustLevel.TRUSTED_AUTO,
                    )
                },
                _diagnostics=(diagnostic,),
                _contracts=(contract,),
            )

    server = server_module.create_server(
        LspConfig(),
        pipeline_factory=FakePipeline,
    )

    assert "textDocument/didOpen" in server.features
    assert "textDocument/hover" in server.features

    did_open = server.features["textDocument/didOpen"]
    hover = server.features["textDocument/hover"]
    did_open(
        server,
        SimpleNamespace(
            text_document=SimpleNamespace(
                uri=uri,
                text="def f(x):\n    return x\n",
                version=7,
            )
        ),
    )

    assert server.published
    published_uri, published_diagnostics, version = server.published[-1]
    assert published_uri == uri
    assert version == 7
    assert published_diagnostics[0].code == "SHEAF002"

    hover_response = hover(
        server,
        SimpleNamespace(
            text_document=SimpleNamespace(uri=uri),
            position=SimpleNamespace(line=0, character=4),
        ),
    )

    assert hover_response is not None
    assert "requires" in hover_response.contents.value

    assert server_module.main(["--stdio"]) == 0
