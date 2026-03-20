"""Hover payload construction for DepPy analysis results."""

from __future__ import annotations

from typing import Optional

from deppy.pipeline.stages.render_stage import ContractAnnotation, Diagnostic

from deppy.lsp.compat import lsp_types
from deppy.lsp.models import DocumentAnalysisState, HoverPayload


def _same_line(path: Optional[str], candidate_path: Optional[str], line: int) -> bool:
    if candidate_path and path and candidate_path != path:
        return False
    return line >= 0


def _contract_matches(
    state: DocumentAnalysisState,
    contract: ContractAnnotation,
    line: int,
    character: int,
) -> bool:
    for site in contract.source_sites:
        location = site.source_location
        if location is None:
            continue
        file_path, site_line, site_col = location
        if not _same_line(state.path, file_path, line):
            continue
        if line != max(site_line - 1, 0):
            continue
        if character < max(site_col - 1, 0):
            continue
        return True
    return False


def _diagnostic_matches(
    state: DocumentAnalysisState,
    diagnostic: Diagnostic,
    line: int,
    character: int,
) -> bool:
    location = diagnostic.location
    if location is None:
        return False
    if not _same_line(state.path, location.file, line):
        return False
    if line != max(location.line - 1, 0):
        return False
    return character >= max(location.col - 1, 0)


def _contract_payload(
    state: DocumentAnalysisState,
    contract: ContractAnnotation,
) -> HoverPayload:
    trust_label = contract.trust.value.replace("_", " ")
    related_sites = tuple(str(site) for site in contract.source_sites)
    lines = [
        f"### {contract.kind.title()} contract for `{contract.scope_name}`",
        "",
        "```python",
        contract.to_decorator_string(),
        "```",
        "",
        f"- Trust: `{trust_label}`",
    ]

    if contract.trust.value == "proof_backed":
        lines.append("- Verification: proof-backed contract")

    if state.pipeline_result is not None:
        for site in contract.source_sites:
            section = state.pipeline_result.sections.get(site)
            if section is None:
                continue
            lines.extend(
                [
                    f"- Site `{site.name}` carrier: `{section.carrier_type}`",
                    f"- Site `{site.name}` refinements: `{section.refinements}`",
                ]
            )

    return HoverPayload(
        title=f"{contract.kind} contract",
        markdown="\n".join(lines),
        related_sites=related_sites,
    )


def _diagnostic_payload(diagnostic: Diagnostic) -> HoverPayload:
    lines = [
        "### Analysis diagnostic",
        "",
        diagnostic.message,
    ]
    if diagnostic.code:
        lines.append(f"\n- Code: `{diagnostic.code}`")
    lines.append(f"- Severity: `{diagnostic.severity.value}`")
    if diagnostic.suggestion:
        lines.append(f"- Suggestion: {diagnostic.suggestion}")
    return HoverPayload(
        title="analysis diagnostic",
        markdown="\n".join(lines),
        related_sites=(),
    )


def build_hover_payload(
    state: DocumentAnalysisState,
    line: int,
    character: int,
) -> Optional[HoverPayload]:
    """Build hover markdown from cached document analysis state."""

    for contract in state.contracts:
        if _contract_matches(state, contract, line, character):
            return _contract_payload(state, contract)

    for diagnostic in state.diagnostics:
        if _diagnostic_matches(state, diagnostic, line, character):
            return _diagnostic_payload(diagnostic)

    return None


def hover_to_lsp(payload: HoverPayload) -> object:
    """Convert a HoverPayload into an LSP Hover response."""

    return lsp_types.Hover(
        contents=lsp_types.MarkupContent(
            kind=lsp_types.MarkupKind.Markdown,
            value=payload.markdown,
        )
    )
