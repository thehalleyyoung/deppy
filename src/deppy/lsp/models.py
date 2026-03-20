"""Models for the DepPy language server."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional, Tuple

from deppy.pipeline.pipeline import PipelineResult
from deppy.pipeline.stages.render_stage import ContractAnnotation, Diagnostic


@dataclass(frozen=True)
class LspConfig:
    """Configuration for the language-server facade."""

    _debounce_ms: int = 150
    _max_workers: int = 1
    _workspace_root: Optional[str] = None

    @property
    def debounce_ms(self) -> int:
        return self._debounce_ms

    @property
    def max_workers(self) -> int:
        return self._max_workers

    @property
    def workspace_root(self) -> Optional[str]:
        return self._workspace_root

    def validate(self) -> LspConfig:
        if self._debounce_ms < 0:
            raise ValueError("debounce_ms must be >= 0")
        if self._max_workers < 1:
            raise ValueError("max_workers must be >= 1")
        return self


@dataclass(frozen=True)
class HoverPayload:
    """Editor-facing markdown payload for a hover request."""

    title: str
    markdown: str
    related_sites: Tuple[str, ...] = ()


@dataclass(frozen=True)
class DefinitionTarget:
    """Resolved target for jump-to-definition style navigation."""

    uri: str
    line: int
    character: int
    end_line: Optional[int] = None
    end_character: Optional[int] = None


@dataclass(frozen=True)
class DocumentAnalysisState:
    """Cached analysis state for an open document."""

    uri: str
    path: Optional[str]
    version: Optional[int]
    source_text: str
    pipeline_result: Optional[PipelineResult]
    diagnostics: Tuple[Diagnostic, ...] = ()
    contracts: Tuple[ContractAnnotation, ...] = ()
    warnings: Tuple[str, ...] = ()
