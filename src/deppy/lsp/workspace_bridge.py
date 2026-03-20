"""Workspace bridge for LSP document analysis."""

from __future__ import annotations

from typing import Callable, Dict, Optional
from urllib.parse import unquote, urlparse

from deppy.pipeline import AnalysisPipeline, PipelineResult
from deppy.pipeline.stages.render_stage import (
    ContractAnnotation,
    Diagnostic,
    DiagnosticLocation,
    DiagnosticSeverity,
)

from deppy.lsp.diagnostics import diagnostics_to_lsp
from deppy.lsp.hover import build_hover_payload, hover_to_lsp
from deppy.lsp.models import DocumentAnalysisState, LspConfig


class LspWorkspaceBridge:
    """Owns in-memory state for open documents and their analysis results."""

    def __init__(
        self,
        config: Optional[LspConfig] = None,
        *,
        pipeline_factory: Optional[Callable[[], AnalysisPipeline]] = None,
    ) -> None:
        self._config = (config or LspConfig()).validate()
        self._documents: Dict[str, DocumentAnalysisState] = {}
        self._pipeline_factory = pipeline_factory or AnalysisPipeline

    @property
    def config(self) -> LspConfig:
        return self._config

    def open_document(
        self,
        uri: str,
        source_text: str,
        *,
        version: Optional[int] = None,
    ) -> DocumentAnalysisState:
        return self.analyze_document(uri, source_text, version=version)

    def update_document(
        self,
        uri: str,
        source_text: str,
        *,
        version: Optional[int] = None,
    ) -> DocumentAnalysisState:
        return self.analyze_document(uri, source_text, version=version)

    def close_document(self, uri: str) -> None:
        self._documents.pop(uri, None)

    def get_state(self, uri: str) -> Optional[DocumentAnalysisState]:
        return self._documents.get(uri)

    def analyze_document(
        self,
        uri: str,
        source_text: str,
        *,
        version: Optional[int] = None,
    ) -> DocumentAnalysisState:
        path = self.uri_to_path(uri)
        try:
            pipeline = self._pipeline_factory()
            result = self._run_pipeline(pipeline, source_text, path)
            state = DocumentAnalysisState(
                uri=uri,
                path=path,
                version=version,
                source_text=source_text,
                pipeline_result=result,
                diagnostics=result.diagnostics,
                contracts=result.contracts,
                warnings=result.warnings,
            )
        except Exception as exc:
            state = DocumentAnalysisState(
                uri=uri,
                path=path,
                version=version,
                source_text=source_text,
                pipeline_result=None,
                diagnostics=(self._analysis_failure_diagnostic(path, exc),),
                contracts=(),
                warnings=(str(exc),),
            )

        self._documents[uri] = state
        return state

    def publish_diagnostics(self, server: object, uri: str) -> tuple[object, ...]:
        state = self._documents.get(uri)
        diagnostics = diagnostics_to_lsp(
            state.diagnostics if state is not None else (),
            default_uri=uri,
        )
        publisher = getattr(server, "publish_diagnostics", None)
        if callable(publisher):
            version = state.version if state is not None else None
            publisher(uri, list(diagnostics), version=version)
        return diagnostics

    def hover(self, uri: str, line: int, character: int) -> object | None:
        state = self._documents.get(uri)
        if state is None:
            return None
        payload = build_hover_payload(state, line, character)
        if payload is None:
            return None
        return hover_to_lsp(payload)

    @staticmethod
    def uri_to_path(uri: str) -> Optional[str]:
        parsed = urlparse(uri)
        if parsed.scheme == "file":
            return unquote(parsed.path)
        if not parsed.scheme:
            return uri
        return None

    @staticmethod
    def _run_pipeline(
        pipeline: AnalysisPipeline,
        source_text: str,
        path: Optional[str],
    ) -> PipelineResult:
        if path and hasattr(pipeline, "_execute_pipeline"):
            return pipeline._execute_pipeline(  # type: ignore[attr-defined]
                {"source_text": source_text, "source_path": path}
            )
        return pipeline.run_source(source_text)

    @staticmethod
    def _analysis_failure_diagnostic(path: Optional[str], exc: Exception) -> Diagnostic:
        location = None
        if path:
            location = DiagnosticLocation(_file=path, _line=1, _col=1)
        return Diagnostic(
            _severity=DiagnosticSeverity.ERROR,
            _message=f"LSP analysis failed: {exc}",
            _location=location,
            _code="DEPPY-LSP",
        )
