"""pygls-backed server wiring for DepPy diagnostics and hover."""

from __future__ import annotations

import argparse
import sys
from typing import Callable, Optional

from deppy import __version__
from deppy.pipeline import AnalysisPipeline

from deppy.lsp.compat import lsp_types
from deppy.lsp.models import LspConfig
from deppy.lsp.workspace_bridge import LspWorkspaceBridge

try:  # pragma: no cover - optional dependency
    from pygls.server import LanguageServer as _LanguageServer

    PYGLS_AVAILABLE = True
except ImportError:  # pragma: no cover - exercised in tests
    _LanguageServer = object
    PYGLS_AVAILABLE = False


class LspError(RuntimeError):
    """Base error for the DepPy LSP package."""


class LspConfigurationError(LspError):
    """Raised when the server is configured incorrectly."""


class LspDependencyError(LspError):
    """Raised when optional LSP runtime dependencies are unavailable."""


def _dependency_message() -> str:
    return (
        "pygls is required to start deppy.lsp. "
        "Install pygls and lsprotocol to enable `deppy-lsp --stdio`."
    )


class DeppyLanguageServer(_LanguageServer):
    """Language-server wrapper that publishes DepPy analysis results."""

    def __init__(
        self,
        config: Optional[LspConfig] = None,
        *,
        pipeline_factory: Optional[Callable[[], AnalysisPipeline]] = None,
    ) -> None:
        if not PYGLS_AVAILABLE:
            raise LspDependencyError(_dependency_message())

        self._config = _validate_config(config)
        super().__init__("deppy-lsp", __version__)
        self._bridge = LspWorkspaceBridge(
            self._config,
            pipeline_factory=pipeline_factory,
        )
        self._register_features()

    @property
    def config(self) -> LspConfig:
        return self._config

    @property
    def bridge(self) -> LspWorkspaceBridge:
        return self._bridge

    def _register_features(self) -> None:
        if getattr(self, "_deppy_features_registered", False):
            return

        @self.feature("textDocument/didOpen")
        def did_open(ls: DeppyLanguageServer, params: object) -> None:
            def _action() -> None:
                text_document = getattr(params, "text_document")
                ls.bridge.open_document(
                    text_document.uri,
                    text_document.text,
                    version=getattr(text_document, "version", None),
                )
                ls.bridge.publish_diagnostics(ls, text_document.uri)

            ls._guard("didOpen", _action)

        @self.feature("textDocument/didChange")
        def did_change(ls: DeppyLanguageServer, params: object) -> None:
            def _action() -> None:
                text_document = getattr(params, "text_document")
                changes = list(getattr(params, "content_changes", []))
                source_text = changes[-1].text if changes else ""
                ls.bridge.update_document(
                    text_document.uri,
                    source_text,
                    version=getattr(text_document, "version", None),
                )
                ls.bridge.publish_diagnostics(ls, text_document.uri)

            ls._guard("didChange", _action)

        @self.feature("textDocument/didClose")
        def did_close(ls: DeppyLanguageServer, params: object) -> None:
            def _action() -> None:
                text_document = getattr(params, "text_document")
                ls.bridge.close_document(text_document.uri)
                ls.bridge.publish_diagnostics(ls, text_document.uri)

            ls._guard("didClose", _action)

        @self.feature("textDocument/hover")
        def hover(ls: DeppyLanguageServer, params: object) -> object | None:
            return ls._guard(
                "hover",
                lambda: ls.bridge.hover(
                    getattr(params, "text_document").uri,
                    getattr(params, "position").line,
                    getattr(params, "position").character,
                ),
                default=None,
            )

        self._deppy_features_registered = True

    def _guard(self, operation: str, callback: Callable[[], object], *, default: object = None) -> object:
        try:
            return callback()
        except Exception as exc:
            logger = getattr(self, "show_message_log", None)
            if callable(logger):
                logger(
                    f"DepPy LSP {operation} failed: {exc}",
                    lsp_types.MessageType.Error,
                )
            return default


def _validate_config(config: Optional[LspConfig]) -> LspConfig:
    candidate = config or LspConfig()
    try:
        return candidate.validate()
    except ValueError as exc:
        raise LspConfigurationError(str(exc)) from exc


def create_server(
    config: Optional[LspConfig] = None,
    *,
    pipeline_factory: Optional[Callable[[], AnalysisPipeline]] = None,
) -> DeppyLanguageServer:
    """Create a configured DepPy language server instance."""

    validated = _validate_config(config)
    if not PYGLS_AVAILABLE:
        raise LspDependencyError(_dependency_message())
    return DeppyLanguageServer(validated, pipeline_factory=pipeline_factory)


def main(argv: Optional[list[str]] = None) -> int:
    """CLI entrypoint for future `deppy-lsp --stdio` wiring."""

    parser = argparse.ArgumentParser(prog="deppy-lsp")
    parser.add_argument("--stdio", action="store_true", help="run the server over stdio")
    args = parser.parse_args(argv)

    try:
        server = create_server()
    except LspDependencyError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    except LspConfigurationError as exc:
        print(str(exc), file=sys.stderr)
        return 2

    if args.stdio or not argv:
        server.start_io()
    return 0
