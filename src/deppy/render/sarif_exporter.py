"""SARIF 2.1.0 format export for CI integration.

SarifExporter converts diagnostics into the Static Analysis Results
Interchange Format (SARIF) 2.1.0, enabling integration with GitHub
Code Scanning, Azure DevOps, and other CI/CD platforms.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)


# ---------------------------------------------------------------------------
# SARIF constants
# ---------------------------------------------------------------------------

_SARIF_VERSION = "2.1.0"
_SARIF_SCHEMA = "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/main/sarif-2.1/schema/sarif-schema-2.1.0.json"
_TOOL_NAME = "deppy"
_TOOL_VERSION = "0.1.0"
_TOOL_INFO_URI = "https://github.com/deppy/deppy"


# ---------------------------------------------------------------------------
# Diagnostic protocol (duck-typed to avoid circular imports)
# ---------------------------------------------------------------------------

@dataclass
class DiagnosticInput:
    """Lightweight diagnostic input for SARIF export.

    This avoids importing from diagnostic_renderer to break cycles.
    """

    severity: str = "error"
    message: str = ""
    file: str = ""
    line: int = 0
    col: int = 0
    end_line: Optional[int] = None
    end_col: Optional[int] = None
    code: str = ""
    obstruction: Optional[ObstructionData] = None
    provenance: List[str] = field(default_factory=list)
    related: List[DiagnosticInput] = field(default_factory=list)
    category: str = ""


def _severity_to_sarif_level(severity: str) -> str:
    """Map diagnostic severity to SARIF level."""
    mapping = {
        "error": "error",
        "warning": "warning",
        "info": "note",
        "hint": "note",
    }
    return mapping.get(severity, "note")


def _compute_rule_id(diag: DiagnosticInput) -> str:
    """Compute a rule ID for a diagnostic."""
    if diag.code:
        return diag.code
    if diag.category:
        return f"deppy/{diag.category}"
    return "deppy/type-error"


def _compute_fingerprint(diag: DiagnosticInput) -> str:
    """Compute a stable fingerprint for deduplication."""
    data = f"{diag.file}:{diag.line}:{diag.col}:{diag.message}"
    return hashlib.sha256(data.encode()).hexdigest()[:16]


# ---------------------------------------------------------------------------
# SARIF builder helpers
# ---------------------------------------------------------------------------

def _create_physical_location(
    file: str,
    line: int,
    col: int,
    end_line: Optional[int] = None,
    end_col: Optional[int] = None,
) -> Dict[str, Any]:
    """Create a SARIF physicalLocation object."""
    region: Dict[str, Any] = {
        "startLine": max(line, 1),
        "startColumn": max(col, 1),
    }
    if end_line is not None:
        region["endLine"] = end_line
    if end_col is not None:
        region["endColumn"] = end_col

    return {
        "artifactLocation": {
            "uri": file,
            "uriBaseId": "%SRCROOT%",
        },
        "region": region,
    }


def _create_message(text: str) -> Dict[str, str]:
    """Create a SARIF message object."""
    return {"text": text}


def _create_location(
    file: str,
    line: int,
    col: int,
    end_line: Optional[int] = None,
    end_col: Optional[int] = None,
    message: str = "",
) -> Dict[str, Any]:
    """Create a SARIF location object."""
    loc: Dict[str, Any] = {
        "physicalLocation": _create_physical_location(
            file, line, col, end_line, end_col
        ),
    }
    if message:
        loc["message"] = _create_message(message)
    return loc


def _create_related_location(
    file: str,
    line: int,
    col: int,
    message: str,
    index: int,
) -> Dict[str, Any]:
    """Create a SARIF relatedLocation object."""
    return {
        "id": index,
        "physicalLocation": _create_physical_location(file, line, col),
        "message": _create_message(message),
    }


# ---------------------------------------------------------------------------
# SarifExporter
# ---------------------------------------------------------------------------

class SarifExporter:
    """Export diagnostics in SARIF 2.1.0 format.

    Produces a SARIF JSON object suitable for upload to GitHub Code Scanning,
    Azure DevOps, or other SARIF-compatible platforms.

    Usage::

        exporter = SarifExporter()
        sarif = exporter.export(diagnostics)
        with open("results.sarif", "w") as f:
            json.dump(sarif, f, indent=2)
    """

    def __init__(
        self,
        *,
        tool_name: str = _TOOL_NAME,
        tool_version: str = _TOOL_VERSION,
        include_provenance: bool = True,
        include_fingerprints: bool = True,
    ) -> None:
        self._tool_name = tool_name
        self._tool_version = tool_version
        self._include_provenance = include_provenance
        self._include_fingerprints = include_fingerprints

    def export(
        self,
        diagnostics: List[DiagnosticInput],
    ) -> Dict[str, Any]:
        """Export diagnostics to a complete SARIF 2.1.0 document."""
        run = self._create_run(diagnostics)

        return {
            "$schema": _SARIF_SCHEMA,
            "version": _SARIF_VERSION,
            "runs": [run],
        }

    def export_json(
        self,
        diagnostics: List[DiagnosticInput],
        indent: int = 2,
    ) -> str:
        """Export diagnostics to a SARIF JSON string."""
        sarif = self.export(diagnostics)
        return json.dumps(sarif, indent=indent)

    def _create_run(
        self,
        diagnostics: List[DiagnosticInput],
    ) -> Dict[str, Any]:
        """Create a SARIF run object containing all results."""
        rules: Dict[str, Dict[str, Any]] = {}
        results: List[Dict[str, Any]] = []

        for diag in diagnostics:
            result = self._create_result(diag)
            results.append(result)

            rule_id = _compute_rule_id(diag)
            if rule_id not in rules:
                rules[rule_id] = self._create_rule(rule_id, diag)

        tool: Dict[str, Any] = {
            "driver": {
                "name": self._tool_name,
                "version": self._tool_version,
                "informationUri": _TOOL_INFO_URI,
                "rules": list(rules.values()),
            }
        }

        artifacts = self._collect_artifacts(diagnostics)

        run: Dict[str, Any] = {
            "tool": tool,
            "results": results,
        }

        if artifacts:
            run["artifacts"] = artifacts

        invocation = self._create_invocation(diagnostics)
        run["invocations"] = [invocation]

        return run

    def _create_result(
        self,
        diag: DiagnosticInput,
    ) -> Dict[str, Any]:
        """Create a SARIF result object from a diagnostic."""
        rule_id = _compute_rule_id(diag)
        level = _severity_to_sarif_level(diag.severity)

        result: Dict[str, Any] = {
            "ruleId": rule_id,
            "level": level,
            "message": _create_message(diag.message),
        }

        if diag.file and diag.line > 0:
            location = _create_location(
                diag.file, diag.line, diag.col,
                diag.end_line, diag.end_col,
            )
            result["locations"] = [location]

        related_locs: List[Dict[str, Any]] = []
        for i, rel in enumerate(diag.related):
            if rel.file and rel.line > 0:
                related_locs.append(
                    _create_related_location(
                        rel.file, rel.line, rel.col,
                        rel.message, i + 1,
                    )
                )
        if related_locs:
            result["relatedLocations"] = related_locs

        if self._include_provenance and diag.provenance:
            code_flows = self._create_code_flows(diag)
            if code_flows:
                result["codeFlows"] = code_flows

        if self._include_fingerprints:
            result["partialFingerprints"] = {
                "primaryLocationLineHash": _compute_fingerprint(diag),
            }

        if diag.obstruction is not None:
            result["properties"] = self._create_result_properties(diag)

        return result

    def _create_rule(
        self,
        rule_id: str,
        diag: DiagnosticInput,
    ) -> Dict[str, Any]:
        """Create a SARIF rule (reportingDescriptor) object."""
        rule: Dict[str, Any] = {
            "id": rule_id,
            "name": rule_id.replace("/", "_").replace("-", "_"),
            "shortDescription": {
                "text": _infer_rule_description(rule_id),
            },
            "helpUri": f"{_TOOL_INFO_URI}/docs/rules/{rule_id}",
        }

        level = _severity_to_sarif_level(diag.severity)
        rule["defaultConfiguration"] = {
            "level": level,
        }

        return rule

    def _create_code_flows(
        self,
        diag: DiagnosticInput,
    ) -> List[Dict[str, Any]]:
        """Create SARIF codeFlows from provenance information."""
        if not diag.provenance:
            return []

        thread_flow_locs: List[Dict[str, Any]] = []
        for step in diag.provenance:
            parts = step.split(":")
            if len(parts) >= 3:
                file_part = parts[0]
                try:
                    line_part = int(parts[1])
                    col_part = int(parts[2])
                except ValueError:
                    continue
                loc = {
                    "location": _create_location(
                        file_part, line_part, col_part,
                        message=step,
                    ),
                }
                thread_flow_locs.append(loc)

        if not thread_flow_locs:
            return []

        return [{
            "threadFlows": [{
                "locations": thread_flow_locs,
            }],
        }]

    def _create_result_properties(
        self,
        diag: DiagnosticInput,
    ) -> Dict[str, Any]:
        """Create custom properties from obstruction data."""
        props: Dict[str, Any] = {}

        if diag.obstruction is not None:
            obs = diag.obstruction
            if obs.cohomology_class is not None:
                props["cohomologyDegree"] = obs.cohomology_class.degree
                props["isTrivial"] = obs.cohomology_class.is_trivial
            props["conflictCount"] = len(obs.conflicting_overlaps)

            conflicts: List[str] = []
            for a_id, b_id in obs.conflicting_overlaps:
                conflicts.append(f"{a_id} vs {b_id}")
            if conflicts:
                props["conflictingSites"] = conflicts

        if diag.category:
            props["category"] = diag.category

        return props

    def _collect_artifacts(
        self,
        diagnostics: List[DiagnosticInput],
    ) -> List[Dict[str, Any]]:
        """Collect unique artifact (file) references."""
        files: Set[str] = set()
        for diag in diagnostics:
            if diag.file:
                files.add(diag.file)
            for rel in diag.related:
                if rel.file:
                    files.add(rel.file)

        artifacts: List[Dict[str, Any]] = []
        for f in sorted(files):
            artifacts.append({
                "location": {
                    "uri": f,
                    "uriBaseId": "%SRCROOT%",
                },
            })

        return artifacts

    def _create_invocation(
        self,
        diagnostics: List[DiagnosticInput],
    ) -> Dict[str, Any]:
        """Create SARIF invocation metadata."""
        has_errors = any(d.severity == "error" for d in diagnostics)
        return {
            "executionSuccessful": not has_errors,
            "toolExecutionNotifications": [],
        }

    def from_obstructions(
        self,
        obstructions: List[ObstructionData],
    ) -> Dict[str, Any]:
        """Convenience: export ObstructionData directly to SARIF."""
        diagnostics: List[DiagnosticInput] = []

        for obs in obstructions:
            if obs.is_trivial:
                continue

            file = ""
            line = 0
            col = 0
            if obs.conflicting_overlaps:
                first_a = obs.conflicting_overlaps[0][0]
                if first_a.source_location is not None:
                    loc = first_a.source_location
                    file = loc[0]
                    line = loc[1]
                    col = loc[2]

            diag = DiagnosticInput(
                severity="error",
                message=obs.explanation or "Type conflict",
                file=file,
                line=line,
                col=col,
                obstruction=obs,
                category=_classify_obstruction(obs),
            )
            diagnostics.append(diag)

        return self.export(diagnostics)


def _infer_rule_description(rule_id: str) -> str:
    """Infer a rule description from the rule ID."""
    descriptions: Dict[str, str] = {
        "deppy/type-error": "Type mismatch detected in sheaf-descent analysis",
        "deppy/missing_guard": "Missing type guard for narrowing",
        "deppy/type_mismatch": "Incompatible types at overlap",
        "deppy/bounds_violation": "Value exceeds expected bounds",
        "deppy/none_safety": "Potential None dereference",
        "deppy/shape_mismatch": "Tensor shape mismatch",
        "deppy/protocol_violation": "Protocol not satisfied",
        "deppy/missing_annotation": "Missing type annotation",
    }
    return descriptions.get(rule_id, f"DepPy diagnostic: {rule_id}")


def _classify_obstruction(obs: ObstructionData) -> str:
    """Classify an obstruction for SARIF categorization."""
    explanation = obs.explanation.lower()
    if "guard" in explanation or "branch" in explanation:
        return "missing_guard"
    if "none" in explanation or "optional" in explanation:
        return "none_safety"
    if "bound" in explanation or "range" in explanation:
        return "bounds_violation"
    if "mismatch" in explanation or "incompatible" in explanation:
        return "type_mismatch"
    if "shape" in explanation:
        return "shape_mismatch"
    return "type-error"
