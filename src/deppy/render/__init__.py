"""deppy.render -- Rendering and display of analysis results.

Phase 10 (render) of the sheaf-descent semantic typing pipeline.  This
package provides:

- **ContractRenderer**: Render contracts as decorator/inline/docstring syntax.
- **DiagnosticRenderer**: Render error diagnostics with provenance chains.
- **SectionRenderer**: Render sections and covers for debugging.
- **SarifExporter**: Export diagnostics in SARIF 2.1.0 format for CI.
- **ResidualRenderer**: Render residual obstructions with explanations.

Typical usage::

    from deppy.render import (
        ContractRenderer,
        DiagnosticRenderer,
        SectionRenderer,
        SarifExporter,
        ResidualRenderer,
    )

    # Contract rendering
    renderer = ContractRenderer()
    text = renderer.render(contracts)

    # Diagnostic rendering
    diag_renderer = DiagnosticRenderer(use_color=True)
    print(diag_renderer.render(diagnostic))

    # Section debugging
    sec_renderer = SectionRenderer()
    print(sec_renderer.render_site_table(sections))

    # SARIF export
    exporter = SarifExporter()
    sarif = exporter.export(diagnostics)

    # Residual rendering
    res_renderer = ResidualRenderer()
    print(res_renderer.render(residuals))
"""

from deppy.render.contract_renderer import (
    ContractRenderer,
    RenderConfig,
)
from deppy.render.diagnostic_renderer import (
    Diagnostic,
    DiagnosticRenderer,
)
from deppy.render.section_renderer import SectionRenderer
from deppy.render.sarif_exporter import (
    DiagnosticInput,
    SarifExporter,
)
from deppy.render.residual_renderer import (
    ResidualDisplay,
    ResidualRenderer,
)
from deppy.render.report import (
    AnalysisReport,
    ErrorFinding,
    InferredPrecondition,
    analyze,
    format_report,
)

__all__ = [
    "ContractRenderer",
    "Diagnostic",
    "DiagnosticInput",
    "DiagnosticRenderer",
    "RenderConfig",
    "ResidualDisplay",
    "ResidualRenderer",
    "SarifExporter",
    "SectionRenderer",
    # report
    "AnalysisReport",
    "ErrorFinding",
    "InferredPrecondition",
    "analyze",
    "format_report",
]
