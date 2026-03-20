"""Compatibility helpers for optional LSP dependencies."""

from __future__ import annotations

from dataclasses import dataclass, field
from types import SimpleNamespace
from typing import Any, Sequence

try:  # pragma: no cover - exercised when lsprotocol is installed
    from lsprotocol import types as lsp_types

    LSP_TYPES_AVAILABLE = True
except ImportError:  # pragma: no cover - covered by tests via fallback objects
    LSP_TYPES_AVAILABLE = False

    class _DiagnosticSeverity:
        Error = 1
        Warning = 2
        Information = 3
        Hint = 4

    class _MarkupKind:
        Markdown = "markdown"
        PlainText = "plaintext"

    class _MessageType:
        Error = 1
        Warning = 2
        Info = 3
        Log = 4

    @dataclass(frozen=True)
    class Position:
        line: int
        character: int

    @dataclass(frozen=True)
    class Range:
        start: Position
        end: Position

    @dataclass(frozen=True)
    class Location:
        uri: str
        range: Range

    @dataclass(frozen=True)
    class DiagnosticRelatedInformation:
        location: Location
        message: str

    @dataclass(frozen=True)
    class Diagnostic:
        range: Range
        message: str
        severity: int | None = None
        code: str | None = None
        source: str | None = None
        related_information: Sequence[DiagnosticRelatedInformation] | None = None

    @dataclass(frozen=True)
    class MarkupContent:
        kind: str
        value: str

    @dataclass(frozen=True)
    class Hover:
        contents: MarkupContent
        range: Range | None = None

    lsp_types = SimpleNamespace(
        Diagnostic=Diagnostic,
        DiagnosticRelatedInformation=DiagnosticRelatedInformation,
        DiagnosticSeverity=_DiagnosticSeverity,
        Hover=Hover,
        Location=Location,
        MarkupContent=MarkupContent,
        MarkupKind=_MarkupKind,
        MessageType=_MessageType,
        Position=Position,
        Range=Range,
    )


def getattr_lsp(name: str) -> Any:
    """Return an LSP type/enum from the optional lsprotocol namespace."""

    return getattr(lsp_types, name)
