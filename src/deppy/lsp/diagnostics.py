"""Conversion helpers from DepPy diagnostics to LSP diagnostics."""

from __future__ import annotations

from pathlib import Path
from typing import Iterable, Optional, Tuple
from urllib.parse import urlparse

from deppy.pipeline.stages.render_stage import (
    Diagnostic,
    DiagnosticLocation,
    DiagnosticSeverity,
)

from deppy.lsp.compat import lsp_types


def _path_to_uri(path: str) -> str:
    parsed = urlparse(path)
    if parsed.scheme:
        return path
    return Path(path).expanduser().resolve().as_uri()


def _position(line: int, character: int) -> object:
    return lsp_types.Position(
        line=max(line - 1, 0),
        character=max(character - 1, 0),
    )


def _range(location: Optional[DiagnosticLocation]) -> object:
    if location is None:
        return lsp_types.Range(
            start=lsp_types.Position(line=0, character=0),
            end=lsp_types.Position(line=0, character=1),
        )

    start = _position(location.line, location.col)
    end_line = location.end_line if location.end_line is not None else location.line
    end_col = location.end_col if location.end_col is not None else max(location.col + 1, 1)
    end = _position(max(end_line, location.line), end_col)
    if getattr(end, "line") < getattr(start, "line"):
        end = start
    elif (
        getattr(end, "line") == getattr(start, "line")
        and getattr(end, "character") <= getattr(start, "character")
    ):
        end = lsp_types.Position(
            line=getattr(start, "line"),
            character=getattr(start, "character") + 1,
        )
    return lsp_types.Range(start=start, end=end)


def _severity(severity: DiagnosticSeverity) -> int:
    mapping = {
        DiagnosticSeverity.ERROR: lsp_types.DiagnosticSeverity.Error,
        DiagnosticSeverity.WARNING: lsp_types.DiagnosticSeverity.Warning,
        DiagnosticSeverity.INFO: lsp_types.DiagnosticSeverity.Information,
        DiagnosticSeverity.HINT: lsp_types.DiagnosticSeverity.Hint,
    }
    return mapping[severity]


def _related_information(related: Tuple[DiagnosticLocation, ...]) -> list[object] | None:
    if not related:
        return None
    items: list[object] = []
    for location in related:
        try:
            uri = _path_to_uri(location.file)
            info = lsp_types.DiagnosticRelatedInformation(
                location=lsp_types.Location(uri=uri, range=_range(location)),
                message="Related location",
            )
            items.append(info)
        except Exception:
            continue
    return items or None


def diagnostic_to_lsp(
    diagnostic: Diagnostic,
    *,
    default_uri: Optional[str] = None,
) -> object:
    """Convert a DepPy diagnostic into an LSP Diagnostic object."""

    location = diagnostic.location
    uri = default_uri
    if location is not None:
        try:
            uri = _path_to_uri(location.file)
        except Exception:
            uri = default_uri

    message = diagnostic.message
    if diagnostic.suggestion:
        message = f"{message}\nSuggestion: {diagnostic.suggestion}"

    return lsp_types.Diagnostic(
        range=_range(location),
        severity=_severity(diagnostic.severity),
        code=diagnostic.code or None,
        source="deppy",
        message=message,
        related_information=_related_information(diagnostic.related),
    )


def diagnostics_to_lsp(
    diagnostics: Iterable[Diagnostic],
    *,
    default_uri: Optional[str] = None,
) -> tuple[object, ...]:
    """Convert a sequence of DepPy diagnostics into LSP diagnostics."""

    return tuple(
        diagnostic_to_lsp(diagnostic, default_uri=default_uri)
        for diagnostic in diagnostics
    )
