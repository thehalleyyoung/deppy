"""
Don't Say Cocycle — localization of H¹ generators to human-readable diagnostics.
=================================================================================

The mathematical engine of deppy expresses type-checking failures as generators
of H¹(U, HybridTy), i.e., Čech 1-cocycles that witness non-trivial obstructions
in the presheaf of types.  Users do *not* want to hear about cocycles.

This module implements the **localization functor**

    Loc : H¹(U, HybridTy)  →  Diagnostic

which translates each cohomological obstruction into a human-readable diagnostic:
severity, location, plain-English message, code fragment, and suggested fix.

The functor is *faithful* in the sense that distinct H¹ generators never collapse
to the same diagnostic (information is preserved, not created).

Usage
-----
>>> from deppy.hybrid.diagnostics.localization import (
...     LocalizationFunctor, DiagnosticFormatter, ExistingCodeChecker,
... )
>>> checker = ExistingCodeChecker()
>>> result = checker.check_file("mymodule.py")
>>> print(DiagnosticFormatter().format_terminal(result.diagnostics))
"""

from __future__ import annotations

import ast
import difflib
import enum
import json
import logging
import os
import re
import textwrap
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    Iterable,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.scan_scope import iter_default_python_files

try:
    import z3 as _z3

    _HAS_Z3 = True
except ImportError:
    _z3 = None  # type: ignore[assignment]
    _HAS_Z3 = False

if TYPE_CHECKING:
    from deppy.hybrid.core.trust import HybridTrustLevel


# --- Integration with existing deppy codebase ---
try:
    from deppy.render.diagnostic_renderer import Diagnostic as _CoreDiagnostic, DiagnosticSeverity as _CoreSeverity
    from deppy.cohomological_analysis import CohomologicalResult as _CoreCohomResult
    from deppy.core._protocols import ObstructionData
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

logger = logging.getLogger(__name__)

# ═══════════════════════════════════════════════════════════════════════════════
# Layer-pair identifiers — the six faces of the hybrid cover
# ═══════════════════════════════════════════════════════════════════════════════

LAYER_INTENT = "INTENT"
LAYER_STRUCTURAL = "STRUCTURAL"
LAYER_SEMANTIC = "SEMANTIC"
LAYER_CODE = "CODE"
LAYER_PROOF = "PROOF"

_LAYER_PAIR_CODES: Dict[Tuple[str, str], str] = {
    (LAYER_INTENT, LAYER_CODE): "IC",
    (LAYER_INTENT, LAYER_STRUCTURAL): "IS",
    (LAYER_STRUCTURAL, LAYER_CODE): "SC",
    (LAYER_SEMANTIC, LAYER_CODE): "EC",
    (LAYER_SEMANTIC, LAYER_PROOF): "EP",
    (LAYER_INTENT, LAYER_SEMANTIC): "IE",
    (LAYER_PROOF, LAYER_CODE): "PC",
}

# Diagnostic code counter per layer pair (global, reset per session)
_CODE_COUNTER: Dict[str, int] = {}


def _next_code(pair_code: str) -> str:
    """Generate the next diagnostic code for a layer pair, e.g. ``DEPPY-IC-003``."""
    count = _CODE_COUNTER.get(pair_code, 0) + 1
    _CODE_COUNTER[pair_code] = count
    return f"DEPPY-{pair_code}-{count:03d}"


def reset_code_counter() -> None:
    """Reset the global diagnostic code counter (useful between sessions)."""
    _CODE_COUNTER.clear()


# ═══════════════════════════════════════════════════════════════════════════════
# Severity
# ═══════════════════════════════════════════════════════════════════════════════


class DiagnosticSeverity(enum.Enum):
    """Severity of a diagnostic message.

    Ordered from most to least severe so that ``max()`` gives the worst.
    """

    ERROR = "error"
    WARNING = "warning"
    INFO = "info"
    HINT = "hint"

    # Allow comparison for sorting / filtering.
    _ORDERING: Dict[str, int] = {  # type: ignore[assignment]
        "error": 0,
        "warning": 1,
        "info": 2,
        "hint": 3,
    }

    def __lt__(self, other: DiagnosticSeverity) -> bool:  # type: ignore[override]
        if not isinstance(other, DiagnosticSeverity):
            return NotImplemented
        return self._ORDERING.value[self.value] < self._ORDERING.value[other.value]  # type: ignore[union-attr]

    def __le__(self, other: DiagnosticSeverity) -> bool:  # type: ignore[override]
        if not isinstance(other, DiagnosticSeverity):
            return NotImplemented
        return self._ORDERING.value[self.value] <= self._ORDERING.value[other.value]  # type: ignore[union-attr]

    @property
    def icon(self) -> str:
        """Terminal-friendly icon for the severity level."""
        return {
            "error": "✖",
            "warning": "⚠",
            "info": "ℹ",
            "hint": "💡",
        }.get(self.value, "?")

    @property
    def sarif_level(self) -> str:
        """Map to SARIF ``level`` vocabulary."""
        return {
            "error": "error",
            "warning": "warning",
            "info": "note",
            "hint": "note",
        }.get(self.value, "none")

    @property
    def github_level(self) -> str:
        """Map to GitHub Actions annotation level."""
        return {
            "error": "error",
            "warning": "warning",
            "info": "notice",
            "hint": "notice",
        }.get(self.value, "notice")


# ═══════════════════════════════════════════════════════════════════════════════
# Suggested Fix
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class SuggestedFix:
    """A machine-actionable fix attached to a :class:`Diagnostic`.

    Attributes
    ----------
    description:
        One-line human description ("Add return type annotation ``-> int``").
    diff:
        Unified diff snippet showing the proposed change.
    confidence:
        Probability that this fix is correct, in [0, 1].
    provenance:
        How the fix was produced.  One of:

        * ``Z3_PROVEN``   — fix derived from a Z3 model / counterexample
        * ``LLM_SUGGESTED`` — LLM oracle proposed the fix
        * ``HEURISTIC``   — rule-based rewrite
        * ``MANUAL``      — human-written template
    """

    description: str
    diff: str = ""
    confidence: float = 0.0
    provenance: str = "HEURISTIC"

    # -- Provenance constants --------------------------------------------------
    Z3_PROVEN: str = "Z3_PROVEN"
    LLM_SUGGESTED: str = "LLM_SUGGESTED"
    HEURISTIC: str = "HEURISTIC"
    MANUAL: str = "MANUAL"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "description": self.description,
            "diff": self.diff,
            "confidence": self.confidence,
            "provenance": self.provenance,
        }

    def __str__(self) -> str:
        prov = f" [{self.provenance}]" if self.provenance else ""
        conf = f" ({self.confidence:.0%})" if self.confidence else ""
        return f"{self.description}{prov}{conf}"


# ═══════════════════════════════════════════════════════════════════════════════
# Diagnostic
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class Diagnostic(_CoreDiagnostic if _HAS_DEPPY_CORE else object):
    """A single diagnostic message produced by the localization functor.

    Extends the core ``Diagnostic`` when available, adding cohomological
    provenance (h1_generator) and richer location metadata.

    Every ``Diagnostic`` is the image of an H¹ generator under *Loc*.  The
    :pyattr:`h1_generator` field stores the original mathematical name for
    expert-mode output; all other fields are in plain English.

    Attributes
    ----------
    file_path:
        Absolute or project-relative path to the file.
    line_start / line_end:
        1-based line range (inclusive).
    col_start / col_end:
        0-based column range.
    severity:
        One of ERROR, WARNING, INFO, HINT.
    code:
        Machine-readable identifier, e.g. ``"DEPPY-IC-001"``.
    message:
        One-line plain-English summary.
    detail:
        Multi-line explanation with context.
    intent_fragment:
        The piece of docstring / spec clause involved (if any).
    code_fragment:
        The piece of source code involved (if any).
    suggested_fix:
        Optional actionable fix.
    trust_level:
        How confident is this diagnosis.  One of:
        ``UNTRUSTED``, ``LLM_JUDGED``, ``PROPERTY_CHECKED``,
        ``Z3_PROVEN``, ``LEAN_VERIFIED``.
    h1_generator:
        The underlying mathematical obstruction name — for expert mode.
    related:
        Other diagnostics that are logically connected.
    timestamp:
        When this diagnostic was created (UTC).
    """

    file_path: str = ""
    line_start: int = 0
    line_end: int = 0
    col_start: int = 0
    col_end: int = 0
    severity: DiagnosticSeverity = DiagnosticSeverity.WARNING
    code: str = ""
    message: str = ""
    detail: str = ""
    intent_fragment: Optional[str] = None
    code_fragment: Optional[str] = None
    suggested_fix: Optional[SuggestedFix] = None
    trust_level: str = "UNTRUSTED"
    h1_generator: Optional[str] = None
    related: List[Diagnostic] = field(default_factory=list)
    timestamp: str = field(
        default_factory=lambda: datetime.now(timezone.utc).isoformat()
    )

    # -- Predicates -----------------------------------------------------------

    def is_error(self) -> bool:
        return self.severity is DiagnosticSeverity.ERROR

    def is_warning(self) -> bool:
        return self.severity is DiagnosticSeverity.WARNING

    @property
    def location_str(self) -> str:
        """``path:line:col`` for terminal output."""
        parts = [self.file_path or "<unknown>"]
        if self.line_start:
            parts.append(str(self.line_start))
            if self.col_start:
                parts.append(str(self.col_start))
        return ":".join(parts)

    # -- Serialisation --------------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {
            "file_path": self.file_path,
            "line_start": self.line_start,
            "line_end": self.line_end,
            "col_start": self.col_start,
            "col_end": self.col_end,
            "severity": self.severity.value,
            "code": self.code,
            "message": self.message,
            "detail": self.detail,
            "trust_level": self.trust_level,
            "timestamp": self.timestamp,
        }
        if self.intent_fragment is not None:
            d["intent_fragment"] = self.intent_fragment
        if self.code_fragment is not None:
            d["code_fragment"] = self.code_fragment
        if self.suggested_fix is not None:
            d["suggested_fix"] = self.suggested_fix.to_dict()
        if self.h1_generator is not None:
            d["h1_generator"] = self.h1_generator
        if self.related:
            d["related"] = [r.to_dict() for r in self.related]
        return d

    def __str__(self) -> str:
        icon = self.severity.icon
        return f"{icon} {self.location_str}: {self.message} [{self.code}]"


# ═══════════════════════════════════════════════════════════════════════════════
# CheckResult — lightweight result container
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class CheckResult:
    """Result container for :class:`ExistingCodeChecker`.

    Attributes
    ----------
    file_path:
        Which file was checked.
    diagnostics:
        List of localized diagnostics.
    h1_dimension:
        Dimension of the first cohomology group (number of independent
        obstructions found).
    trust_summary:
        Count of diagnostics per trust level.
    """

    file_path: str = ""
    diagnostics: List[Diagnostic] = field(default_factory=list)
    h1_dimension: int = 0
    trust_summary: Dict[str, int] = field(default_factory=dict)

    def summary(self) -> str:
        """One-line summary for terminal output."""
        n_err = sum(1 for d in self.diagnostics if d.is_error())
        n_warn = sum(1 for d in self.diagnostics if d.is_warning())
        n_info = sum(
            1
            for d in self.diagnostics
            if d.severity
            in (DiagnosticSeverity.INFO, DiagnosticSeverity.HINT)
        )
        parts: List[str] = []
        if n_err:
            parts.append(f"{n_err} error{'s' if n_err != 1 else ''}")
        if n_warn:
            parts.append(f"{n_warn} warning{'s' if n_warn != 1 else ''}")
        if n_info:
            parts.append(f"{n_info} info")
        if not parts:
            return f"{self.file_path}: ✔ no issues ({self.h1_dimension} issue groups)"
        return f"{self.file_path}: {', '.join(parts)} ({self.h1_dimension} issue groups)"

    def has_errors(self) -> bool:
        return any(d.is_error() for d in self.diagnostics)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "file_path": self.file_path,
            "h1_dimension": self.h1_dimension,
            "trust_summary": self.trust_summary,
            "diagnostics": [d.to_dict() for d in self.diagnostics],
            "summary": self.summary(),
        }


# ═══════════════════════════════════════════════════════════════════════════════
# LocalizationFunctor — THE CORE
# ═══════════════════════════════════════════════════════════════════════════════


# Severity lookup for layer pairs: how bad is this gap?
_DEFAULT_SEVERITY: Dict[Tuple[str, str], DiagnosticSeverity] = {
    (LAYER_INTENT, LAYER_CODE): DiagnosticSeverity.ERROR,
    (LAYER_STRUCTURAL, LAYER_CODE): DiagnosticSeverity.ERROR,
    (LAYER_PROOF, LAYER_CODE): DiagnosticSeverity.ERROR,
    (LAYER_SEMANTIC, LAYER_CODE): DiagnosticSeverity.WARNING,
    (LAYER_INTENT, LAYER_STRUCTURAL): DiagnosticSeverity.WARNING,
    (LAYER_SEMANTIC, LAYER_PROOF): DiagnosticSeverity.INFO,
    (LAYER_INTENT, LAYER_SEMANTIC): DiagnosticSeverity.INFO,
}

# Default trust for each layer pair
_DEFAULT_TRUST: Dict[Tuple[str, str], str] = {
    (LAYER_INTENT, LAYER_CODE): "LLM_JUDGED",
    (LAYER_INTENT, LAYER_STRUCTURAL): "LLM_JUDGED",
    (LAYER_STRUCTURAL, LAYER_CODE): "Z3_PROVEN" if _HAS_Z3 else "PROPERTY_CHECKED",
    (LAYER_SEMANTIC, LAYER_CODE): "LLM_JUDGED",
    (LAYER_SEMANTIC, LAYER_PROOF): "PROPERTY_CHECKED",
    (LAYER_INTENT, LAYER_SEMANTIC): "LLM_JUDGED",
    (LAYER_PROOF, LAYER_CODE): "Z3_PROVEN" if _HAS_Z3 else "PROPERTY_CHECKED",
}


class LocalizationFunctor:
    """Map H¹(U, HybridTy) generators to human-readable :class:`Diagnostic` objects.

    The functor ``Loc: H¹ → Diagnostic`` translates mathematical obstructions:

    ============== ============== ============================================
    Layer A        Layer B        Diagnostic pattern
    ============== ============== ============================================
    INTENT         CODE           "Intent says X, code does Y"
    INTENT         STRUCTURAL     "Docstring promises X, no type/assert enforces it"
    STRUCTURAL     CODE           "Type says A, but code can produce B"
    SEMANTIC       CODE           "Semantic property X not upheld by implementation"
    SEMANTIC       PROOF          "Claimed property has no proof or test"
    INTENT         SEMANTIC       "Intent claim not covered by any semantic check"
    PROOF          CODE           "Proof obligation not discharged"
    ============== ============== ============================================

    Parameters
    ----------
    severity_overrides:
        Override the default severity for specific layer pairs.
    trust_overrides:
        Override the default trust level for specific layer pairs.
    include_h1_names:
        If True, attach the raw cohomological generator name.
    suggest_fixes:
        If True, attempt to generate :class:`SuggestedFix` for each diagnostic.
    """

    def __init__(
        self,
        severity_overrides: Optional[Dict[Tuple[str, str], DiagnosticSeverity]] = None,
        trust_overrides: Optional[Dict[Tuple[str, str], str]] = None,
        include_h1_names: bool = False,
        suggest_fixes: bool = True,
    ) -> None:
        self._severity = dict(_DEFAULT_SEVERITY)
        if severity_overrides:
            self._severity.update(severity_overrides)

        self._trust = dict(_DEFAULT_TRUST)
        if trust_overrides:
            self._trust.update(trust_overrides)

        self._include_h1_names = include_h1_names
        self._suggest_fixes = suggest_fixes

        # Dispatch table: layer pair → localizer method
        self._dispatch: Dict[Tuple[str, str], Callable[..., Diagnostic]] = {
            (LAYER_INTENT, LAYER_CODE): self._intent_code_gap,
            (LAYER_INTENT, LAYER_STRUCTURAL): self._intent_structural_gap,
            (LAYER_STRUCTURAL, LAYER_CODE): self._structural_code_gap,
            (LAYER_SEMANTIC, LAYER_CODE): self._semantic_code_gap,
            (LAYER_SEMANTIC, LAYER_PROOF): self._semantic_proof_gap,
            (LAYER_INTENT, LAYER_SEMANTIC): self._intent_semantic_gap,
            (LAYER_PROOF, LAYER_CODE): self._proof_code_gap,
        }

    # ------------------------------------------------------------------
    # Public interface
    # ------------------------------------------------------------------

    def localize(self, obstruction: Dict[str, Any]) -> Diagnostic:
        """Localize a single H¹ obstruction to a :class:`Diagnostic`.

        Parameters
        ----------
        obstruction:
            Dictionary describing the obstruction.  Required keys:

            * ``layer_a``, ``layer_b`` — the two layers involved
            * ``file_path`` — source file
            * ``line_start``, ``line_end`` — location

            Optional keys (used to enrich the message):

            * ``intent_text`` — the docstring / spec clause
            * ``code_text`` — the code fragment
            * ``type_expected``, ``type_actual`` — type mismatch info
            * ``property_name`` — semantic property name
            * ``counterexample`` — Z3 counterexample string
            * ``proof_obligation`` — Lean obligation text
            * ``h1_name`` — raw generator name
        """
        layer_a = obstruction.get("layer_a", LAYER_INTENT)
        layer_b = obstruction.get("layer_b", LAYER_CODE)
        pair = (layer_a, layer_b)

        # Normalise pair order: we always want the canonical direction
        if pair not in self._dispatch:
            pair = (layer_b, layer_a)
        if pair not in self._dispatch:
            logger.warning("Unknown layer pair %s/%s — using generic diagnostic", layer_a, layer_b)
            return self._generic_gap(obstruction)

        handler = self._dispatch[pair]
        diag = handler(obstruction)

        if self._suggest_fixes:
            fix = self._suggest_fix(obstruction, diag)
            if fix is not None:
                diag.suggested_fix = fix

        if self._include_h1_names and "h1_name" in obstruction:
            diag.h1_generator = obstruction["h1_name"]

        return diag

    def localize_batch(
        self, obstructions: Iterable[Dict[str, Any]]
    ) -> List[Diagnostic]:
        """Localize a batch of obstructions, returning a sorted list."""
        diagnostics = [self.localize(obs) for obs in obstructions]
        diagnostics.sort(
            key=lambda d: (d.severity, d.file_path, d.line_start)
        )
        return diagnostics

    # ------------------------------------------------------------------
    # Layer-pair handlers
    # ------------------------------------------------------------------

    def _base_diagnostic(
        self,
        obs: Dict[str, Any],
        pair: Tuple[str, str],
        message: str,
        detail: str,
    ) -> Diagnostic:
        """Shared constructor for all layer-pair handlers."""
        pair_code = _LAYER_PAIR_CODES.get(pair, "XX")
        return Diagnostic(
            file_path=obs.get("file_path", ""),
            line_start=obs.get("line_start", 0),
            line_end=obs.get("line_end", 0),
            col_start=obs.get("col_start", 0),
            col_end=obs.get("col_end", 0),
            severity=self._severity.get(pair, DiagnosticSeverity.WARNING),
            code=_next_code(pair_code),
            message=message,
            detail=detail,
            intent_fragment=obs.get("intent_text"),
            code_fragment=obs.get("code_text"),
            trust_level=self._trust.get(pair, "UNTRUSTED"),
            h1_generator=obs.get("h1_name") if self._include_h1_names else None,
        )

    def _intent_code_gap(self, obs: Dict[str, Any]) -> Diagnostic:
        """Intent says X, code does Y."""
        intent = obs.get("intent_text", "<no intent>")
        code = obs.get("code_text", "<no code>")
        func_name = obs.get("function_name", "")
        prefix = f"In `{func_name}`: " if func_name else ""

        message = f"{prefix}Intent–code mismatch"
        detail_lines = [
            "The documented behavior says:",
            f"  {_quote(intent)}",
            "",
            f"But the code does:",
            f"  {_quote(code)}",
            "",
            "These disagree — the implementation may not match the documented behavior.",
        ]
        if obs.get("counterexample"):
            detail_lines.extend([
                "",
                f"Counterexample: {obs['counterexample']}",
            ])

        return self._base_diagnostic(
            obs,
            (LAYER_INTENT, LAYER_CODE),
            message,
            "\n".join(detail_lines),
        )

    def _intent_structural_gap(self, obs: Dict[str, Any]) -> Diagnostic:
        """Docstring promises X, no type/assert enforces it."""
        intent = obs.get("intent_text", "<no intent>")
        func_name = obs.get("function_name", "")
        property_name = obs.get("property_name", "the stated property")
        prefix = f"In `{func_name}`: " if func_name else ""

        message = f"{prefix}Unenforced intent"
        detail_lines = [
            "The documented behavior says:",
            f"  {_quote(intent)}",
            "",
            "But the checker did not find a type annotation, assertion, or clear",
            f"guard that enforces `{property_name}`.",
            "",
            "Add a clearer type annotation, assert, contract, or guard to make this behavior explicit.",
        ]

        return self._base_diagnostic(
            obs,
            (LAYER_INTENT, LAYER_STRUCTURAL),
            message,
            "\n".join(detail_lines),
        )

    def _structural_code_gap(self, obs: Dict[str, Any]) -> Diagnostic:
        """Type says A, but code can produce B."""
        expected = obs.get("type_expected", "<expected>")
        actual = obs.get("type_actual", "<actual>")
        func_name = obs.get("function_name", "")
        prefix = f"In `{func_name}`: " if func_name else ""

        message = f"{prefix}Type–code mismatch: expected `{expected}`, got `{actual}`"
        detail_lines = [
            f"The type annotation/contract says the value should be:",
            f"  {expected}",
            "",
            f"But the code can produce:",
            f"  {actual}",
        ]
        if obs.get("counterexample"):
            detail_lines.extend([
                "",
                f"Counterexample: {obs['counterexample']}",
            ])
        if _HAS_Z3 and obs.get("z3_model"):
            detail_lines.extend([
                "",
                f"Z3 model: {obs['z3_model']}",
            ])

        return self._base_diagnostic(
            obs,
            (LAYER_STRUCTURAL, LAYER_CODE),
            message,
            "\n".join(detail_lines),
        )

    def _semantic_code_gap(self, obs: Dict[str, Any]) -> Diagnostic:
        """Semantic property X not upheld by implementation."""
        prop = obs.get("property_name", "<property>")
        func_name = obs.get("function_name", "")
        prefix = f"In `{func_name}`: " if func_name else ""

        message = f"{prefix}Semantic property `{prop}` not upheld"
        detail_lines = [
            f"The behavior `{prop}` should hold,",
            "but the implementation does not clearly guarantee it.",
        ]
        if obs.get("violation_witness"):
            detail_lines.extend([
                "",
                f"Witness of violation:",
                f"  {obs['violation_witness']}",
            ])
        if obs.get("code_text"):
            detail_lines.extend([
                "",
                f"Relevant code:",
                f"  {obs['code_text']}",
            ])

        return self._base_diagnostic(
            obs,
            (LAYER_SEMANTIC, LAYER_CODE),
            message,
            "\n".join(detail_lines),
        )

    def _semantic_proof_gap(self, obs: Dict[str, Any]) -> Diagnostic:
        """Claimed property has no proof or test."""
        prop = obs.get("property_name", "<property>")
        func_name = obs.get("function_name", "")
        prefix = f"In `{func_name}`: " if func_name else ""

        message = f"{prefix}Property `{prop}` has no proof or test"
        detail_lines = [
            f"The behavior `{prop}` is claimed but not verified:",
            "  - No property-based test covers it",
            "  - No solver-backed proof covers it",
            "  - No formal proof covers it",
            "",
            "Write a property test or add a stronger automated check.",
        ]

        return self._base_diagnostic(
            obs,
            (LAYER_SEMANTIC, LAYER_PROOF),
            message,
            "\n".join(detail_lines),
        )

    def _intent_semantic_gap(self, obs: Dict[str, Any]) -> Diagnostic:
        """Intent claim not covered by any semantic check."""
        intent = obs.get("intent_text", "<no intent>")
        func_name = obs.get("function_name", "")
        prefix = f"In `{func_name}`: " if func_name else ""

        message = f"{prefix}Intent claim has no semantic check"
        detail_lines = [
            "The documented behavior says:",
            f"  {_quote(intent)}",
            "",
            "But no test or stronger automated check covers this claim.",
            "Right now it is only documentation.",
            "",
            "Add a property test or another executable check.",
        ]

        return self._base_diagnostic(
            obs,
            (LAYER_INTENT, LAYER_SEMANTIC),
            message,
            "\n".join(detail_lines),
        )

    def _proof_code_gap(self, obs: Dict[str, Any]) -> Diagnostic:
        """Proof obligation not discharged."""
        obligation = obs.get("proof_obligation", "<obligation>")
        func_name = obs.get("function_name", "")
        prefix = f"In `{func_name}`: " if func_name else ""

        message = f"{prefix}Proof obligation not discharged"
        detail_lines = [
            "The following required check is still open:",
            f"  {_quote(obligation)}",
            "",
            "But no proof or solver result closes it yet.",
        ]
        if obs.get("lean_theorem"):
            detail_lines.extend([
                "",
                f"Lean obligation: {obs['lean_theorem']}",
            ])

        return self._base_diagnostic(
            obs,
            (LAYER_PROOF, LAYER_CODE),
            message,
            "\n".join(detail_lines),
        )

    def _generic_gap(self, obs: Dict[str, Any]) -> Diagnostic:
        """Fallback for unknown layer pairs."""
        layer_a = obs.get("layer_a", "?")
        layer_b = obs.get("layer_b", "?")
        message = f"Layer mismatch between {layer_a} and {layer_b}"
        detail = (
            f"The checker found conflicting evidence between {layer_a} and {layer_b}, "
            "but does not yet have a more specific explanation for this case."
        )
        return Diagnostic(
            file_path=obs.get("file_path", ""),
            line_start=obs.get("line_start", 0),
            line_end=obs.get("line_end", 0),
            col_start=obs.get("col_start", 0),
            col_end=obs.get("col_end", 0),
            severity=DiagnosticSeverity.WARNING,
            code=_next_code("XX"),
            message=message,
            detail=detail,
            intent_fragment=obs.get("intent_text"),
            code_fragment=obs.get("code_text"),
            trust_level="UNTRUSTED",
        )

    # ------------------------------------------------------------------
    # Fix suggestion
    # ------------------------------------------------------------------

    def _suggest_fix(
        self, obs: Dict[str, Any], diag: Diagnostic
    ) -> Optional[SuggestedFix]:
        """Attempt to produce a :class:`SuggestedFix` for *diag*.

        Strategy priority:
        1. Z3-derived fix (if a counterexample provides a concrete correction)
        2. Heuristic fix (template-based rewrites for common patterns)
        3. No fix (return None)
        """
        pair = (obs.get("layer_a", ""), obs.get("layer_b", ""))

        # Attempt Z3-derived fix
        if _HAS_Z3 and obs.get("z3_fix_model"):
            return self._z3_derived_fix(obs)

        # Attempt heuristic fixes per pair type
        if pair == (LAYER_INTENT, LAYER_STRUCTURAL):
            return self._heuristic_add_annotation(obs)
        if pair == (LAYER_STRUCTURAL, LAYER_CODE):
            return self._heuristic_type_fix(obs)
        if pair == (LAYER_SEMANTIC, LAYER_PROOF):
            return self._heuristic_add_test(obs)
        if pair == (LAYER_INTENT, LAYER_SEMANTIC):
            return self._heuristic_add_property(obs)

        return None

    def _z3_derived_fix(self, obs: Dict[str, Any]) -> SuggestedFix:
        """Build a fix from a Z3 model that shows the correct value."""
        model_str = obs.get("z3_fix_model", "")
        return SuggestedFix(
            description=f"Apply Z3-derived correction: {model_str[:80]}",
            diff=obs.get("z3_fix_diff", ""),
            confidence=0.95,
            provenance=SuggestedFix.Z3_PROVEN,
        )

    def _heuristic_add_annotation(self, obs: Dict[str, Any]) -> Optional[SuggestedFix]:
        """Suggest adding a type annotation or assertion."""
        func_name = obs.get("function_name", "")
        prop = obs.get("property_name", "")
        if not func_name:
            return None

        desc = f"Add assertion for `{prop}` in `{func_name}`"
        diff = _make_diff_snippet(
            obs.get("file_path", ""),
            obs.get("line_start", 0),
            "",
            f"    assert {prop}, 'Expected: {prop}'  # deppy: enforce intent\n",
        )
        return SuggestedFix(
            description=desc,
            diff=diff,
            confidence=0.5,
            provenance=SuggestedFix.HEURISTIC,
        )

    def _heuristic_type_fix(self, obs: Dict[str, Any]) -> Optional[SuggestedFix]:
        """Suggest fixing a type annotation."""
        expected = obs.get("type_expected", "")
        actual = obs.get("type_actual", "")
        if not expected or not actual:
            return None
        return SuggestedFix(
            description=f"Change type from `{actual}` to `{expected}`",
            diff="",
            confidence=0.4,
            provenance=SuggestedFix.HEURISTIC,
        )

    def _heuristic_add_test(self, obs: Dict[str, Any]) -> Optional[SuggestedFix]:
        """Suggest adding a property test."""
        prop = obs.get("property_name", "")
        func_name = obs.get("function_name", "")
        if not prop:
            return None
        return SuggestedFix(
            description=f"Add a property test for `{prop}` in `{func_name}`",
            diff="",
            confidence=0.3,
            provenance=SuggestedFix.HEURISTIC,
        )

    def _heuristic_add_property(self, obs: Dict[str, Any]) -> Optional[SuggestedFix]:
        """Suggest adding a @deppy.property decorator."""
        intent = obs.get("intent_text", "")
        func_name = obs.get("function_name", "")
        if not func_name:
            return None
        return SuggestedFix(
            description=f"Add a dedicated property check for `{func_name}`",
            diff="",
            confidence=0.3,
            provenance=SuggestedFix.HEURISTIC,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# DiagnosticFormatter — multi-format rendering
# ═══════════════════════════════════════════════════════════════════════════════

# ANSI colour codes for terminal output
_RESET = "\033[0m"
_BOLD = "\033[1m"
_DIM = "\033[2m"
_RED = "\033[31m"
_YELLOW = "\033[33m"
_GREEN = "\033[32m"
_BLUE = "\033[34m"
_CYAN = "\033[36m"
_MAGENTA = "\033[35m"

_SEVERITY_COLOUR: Dict[DiagnosticSeverity, str] = {
    DiagnosticSeverity.ERROR: _RED,
    DiagnosticSeverity.WARNING: _YELLOW,
    DiagnosticSeverity.INFO: _BLUE,
    DiagnosticSeverity.HINT: _CYAN,
}

_TRUST_COLOUR: Dict[str, str] = {
    "UNTRUSTED": _RED,
    "LLM_JUDGED": _YELLOW,
    "RUNTIME_CHECKED": _YELLOW,
    "PROPERTY_CHECKED": _GREEN,
    "Z3_PROVEN": _BLUE,
    "LEAN_VERIFIED": _MAGENTA,
}


class DiagnosticFormatter:
    """Render :class:`Diagnostic` lists in multiple output formats.

    Supported formats:

    * **terminal** — coloured output with code context and fix suggestions
    * **sarif** — SARIF v2.1.0 for CI tools (CodeQL, GitHub Code Scanning)
    * **json** — flat JSON for programmatic consumption
    * **github_annotations** — GitHub Actions ``::error::`` / ``::warning::``
    * **markdown** — for pull-request review comments
    * **html** — for web dashboards
    """

    def __init__(
        self,
        show_detail: bool = True,
        show_fix: bool = True,
        show_trust: bool = True,
        colour: bool = True,
        max_code_lines: int = 5,
    ) -> None:
        self.show_detail = show_detail
        self.show_fix = show_fix
        self.show_trust = show_trust
        self.colour = colour
        self.max_code_lines = max_code_lines

    # ------------------------------------------------------------------
    # Terminal format
    # ------------------------------------------------------------------

    def format_terminal(self, diagnostics: Sequence[Diagnostic]) -> str:
        """Coloured terminal output with code context."""
        if not diagnostics:
            return f"{_GREEN}✔ No issues found.{_RESET}\n"

        lines: List[str] = []
        for diag in diagnostics:
            lines.append(self._terminal_one(diag))
        lines.append("")
        lines.append(self._terminal_summary(diagnostics))
        return "\n".join(lines)

    def _terminal_one(self, diag: Diagnostic) -> str:
        c = _SEVERITY_COLOUR.get(diag.severity, "") if self.colour else ""
        r = _RESET if self.colour else ""
        b = _BOLD if self.colour else ""
        d = _DIM if self.colour else ""

        parts: List[str] = []
        # Header line
        parts.append(
            f"{c}{b}{diag.severity.icon} {diag.severity.value.upper()}{r}"
            f" {b}{diag.location_str}{r}: {diag.message}"
            f" {d}[{diag.code}]{r}"
        )
        # Trust badge
        if self.show_trust:
            tc = _TRUST_COLOUR.get(diag.trust_level, "") if self.colour else ""
            parts.append(f"  {tc}trust: {diag.trust_level}{r}")

        # Code fragment
        if diag.code_fragment and self.max_code_lines > 0:
            snippet = _truncate_lines(diag.code_fragment, self.max_code_lines)
            parts.append(f"  {d}code:{r}")
            for ln in snippet.splitlines():
                parts.append(f"    {d}{ln}{r}")

        # Intent fragment
        if diag.intent_fragment:
            parts.append(f"  {d}intent: {_quote(diag.intent_fragment)}{r}")

        # Detail
        if self.show_detail and diag.detail:
            parts.append(f"  {d}---{r}")
            for ln in diag.detail.splitlines():
                parts.append(f"  {d}{ln}{r}")

        # Suggested fix
        if self.show_fix and diag.suggested_fix:
            fix = diag.suggested_fix
            fc = _GREEN if self.colour else ""
            parts.append(f"  {fc}💡 Fix: {fix.description}{r}")
            if fix.diff:
                for ln in fix.diff.splitlines()[:8]:
                    parts.append(f"    {fc}{ln}{r}")
            parts.append(
                f"    {d}confidence: {fix.confidence:.0%}"
                f" — provenance: {fix.provenance}{r}"
            )

        parts.append("")
        return "\n".join(parts)

    def _terminal_summary(self, diagnostics: Sequence[Diagnostic]) -> str:
        counts: Dict[str, int] = {}
        for d in diagnostics:
            key = d.severity.value
            counts[key] = counts.get(key, 0) + 1
        parts = [f"{v} {k}{'s' if v != 1 else ''}" for k, v in counts.items()]
        return f"Found {len(diagnostics)} issue{'s' if len(diagnostics) != 1 else ''}: {', '.join(parts)}"

    # ------------------------------------------------------------------
    # SARIF v2.1.0
    # ------------------------------------------------------------------

    def format_sarif(self, diagnostics: Sequence[Diagnostic]) -> Dict[str, Any]:
        """SARIF v2.1.0 output for CI tools."""
        results: List[Dict[str, Any]] = []
        rules: Dict[str, Dict[str, Any]] = {}

        for diag in diagnostics:
            rule_id = diag.code
            if rule_id not in rules:
                rules[rule_id] = {
                    "id": rule_id,
                    "shortDescription": {"text": diag.message},
                    "defaultConfiguration": {"level": diag.severity.sarif_level},
                    "properties": {"trust_level": diag.trust_level},
                }

            result: Dict[str, Any] = {
                "ruleId": rule_id,
                "level": diag.severity.sarif_level,
                "message": {
                    "text": diag.message,
                    "markdown": diag.detail or diag.message,
                },
                "locations": [
                    {
                        "physicalLocation": {
                            "artifactLocation": {"uri": diag.file_path},
                            "region": {
                                "startLine": diag.line_start,
                                "endLine": diag.line_end or diag.line_start,
                                "startColumn": diag.col_start,
                                "endColumn": diag.col_end,
                            },
                        }
                    }
                ],
                "properties": {
                    "trust_level": diag.trust_level,
                },
            }

            if diag.suggested_fix:
                result["fixes"] = [
                    {
                        "description": {
                            "text": diag.suggested_fix.description,
                        },
                        "artifactChanges": [],
                    }
                ]

            if diag.related:
                result["relatedLocations"] = [
                    {
                        "id": i,
                        "physicalLocation": {
                            "artifactLocation": {"uri": r.file_path},
                            "region": {
                                "startLine": r.line_start,
                                "endLine": r.line_end or r.line_start,
                            },
                        },
                        "message": {"text": r.message},
                    }
                    for i, r in enumerate(diag.related)
                ]

            results.append(result)

        return {
            "$schema": "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/main/sarif-2.1/schema/sarif-schema-2.1.0.json",
            "version": "2.1.0",
            "runs": [
                {
                    "tool": {
                        "driver": {
                            "name": "deppy",
                            "version": "0.1.0",
                            "informationUri": "https://github.com/mathdivergence/deppy",
                            "rules": list(rules.values()),
                        }
                    },
                    "results": results,
                }
            ],
        }

    # ------------------------------------------------------------------
    # JSON
    # ------------------------------------------------------------------

    def format_json(self, diagnostics: Sequence[Diagnostic]) -> str:
        """JSON output for programmatic consumption."""
        payload = {
            "version": "1.0",
            "tool": "deppy",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "count": len(diagnostics),
            "diagnostics": [d.to_dict() for d in diagnostics],
        }
        return json.dumps(payload, indent=2, ensure_ascii=False)

    # ------------------------------------------------------------------
    # GitHub Actions annotations
    # ------------------------------------------------------------------

    def format_github_annotations(
        self, diagnostics: Sequence[Diagnostic]
    ) -> List[Dict[str, Any]]:
        """GitHub Actions annotation objects.

        Each annotation is a dict with keys: ``level``, ``file``, ``line``,
        ``endLine``, ``col``, ``endColumn``, ``title``, ``message``.

        These can be printed as ``::warning file=...,line=...::message``.
        """
        annotations: List[Dict[str, Any]] = []
        for diag in diagnostics:
            ann: Dict[str, Any] = {
                "level": diag.severity.github_level,
                "file": diag.file_path,
                "line": diag.line_start,
                "endLine": diag.line_end or diag.line_start,
                "col": diag.col_start,
                "endColumn": diag.col_end,
                "title": f"[{diag.code}] {diag.message}",
                "message": diag.detail or diag.message,
                "trust_level": diag.trust_level,
            }
            annotations.append(ann)
        return annotations

    def format_github_commands(
        self, diagnostics: Sequence[Diagnostic]
    ) -> str:
        """GitHub Actions ``::warning::`` command strings."""
        lines: List[str] = []
        for diag in diagnostics:
            lvl = diag.severity.github_level
            params = (
                f"file={diag.file_path},"
                f"line={diag.line_start},"
                f"endLine={diag.line_end or diag.line_start},"
                f"col={diag.col_start},"
                f"endColumn={diag.col_end},"
                f"title=[{diag.code}] {diag.message}"
            )
            msg = (diag.detail or diag.message).replace("\n", "%0A")
            lines.append(f"::{lvl} {params}::{msg}")
        return "\n".join(lines)

    # ------------------------------------------------------------------
    # Markdown (for PR comments)
    # ------------------------------------------------------------------

    def format_markdown(self, diagnostics: Sequence[Diagnostic]) -> str:
        """Markdown output for pull-request review comments."""
        if not diagnostics:
            return "### ✅ deppy: No issues found\n"

        parts: List[str] = []
        n_err = sum(1 for d in diagnostics if d.is_error())
        n_warn = sum(1 for d in diagnostics if d.is_warning())
        parts.append(f"### deppy: {len(diagnostics)} issue{'s' if len(diagnostics) != 1 else ''}")
        parts.append("")
        parts.append(f"| Severity | Count |")
        parts.append(f"|----------|-------|")
        if n_err:
            parts.append(f"| ✖ Error | {n_err} |")
        if n_warn:
            parts.append(f"| ⚠ Warning | {n_warn} |")
        n_other = len(diagnostics) - n_err - n_warn
        if n_other:
            parts.append(f"| ℹ Info/Hint | {n_other} |")
        parts.append("")

        for diag in diagnostics:
            icon = diag.severity.icon
            parts.append(f"#### {icon} `{diag.code}` — {diag.message}")
            parts.append("")
            parts.append(f"**File:** `{diag.location_str}`  ")
            parts.append(f"**Trust:** `{diag.trust_level}`")
            parts.append("")
            if diag.detail:
                parts.append("<details>")
                parts.append(f"<summary>Details</summary>")
                parts.append("")
                parts.append("```")
                parts.append(diag.detail)
                parts.append("```")
                parts.append("</details>")
                parts.append("")
            if diag.code_fragment:
                parts.append("**Code:**")
                parts.append(f"```python")
                parts.append(_truncate_lines(diag.code_fragment, 10))
                parts.append("```")
                parts.append("")
            if diag.suggested_fix:
                fix = diag.suggested_fix
                parts.append(
                    f"💡 **Suggested fix** ({fix.confidence:.0%}, {fix.provenance}): "
                    f"{fix.description}"
                )
                if fix.diff:
                    parts.append("```diff")
                    parts.append(fix.diff)
                    parts.append("```")
                parts.append("")
            parts.append("---")
            parts.append("")

        return "\n".join(parts)

    # ------------------------------------------------------------------
    # HTML (for dashboards)
    # ------------------------------------------------------------------

    def format_html(self, diagnostics: Sequence[Diagnostic]) -> str:
        """HTML output for web dashboards."""
        sev_class = {
            DiagnosticSeverity.ERROR: "diag-error",
            DiagnosticSeverity.WARNING: "diag-warning",
            DiagnosticSeverity.INFO: "diag-info",
            DiagnosticSeverity.HINT: "diag-hint",
        }

        rows: List[str] = []
        for diag in diagnostics:
            cls = sev_class.get(diag.severity, "diag-info")
            fix_html = ""
            if diag.suggested_fix:
                fix = diag.suggested_fix
                fix_html = (
                    f'<div class="diag-fix">'
                    f"💡 {_html_escape(fix.description)} "
                    f"({fix.confidence:.0%}, {fix.provenance})"
                    f"</div>"
                )
            detail_html = ""
            if diag.detail:
                detail_html = (
                    f'<pre class="diag-detail">'
                    f"{_html_escape(diag.detail)}</pre>"
                )
            rows.append(
                f'<div class="diag-item {cls}">'
                f'  <span class="diag-severity">{diag.severity.icon}</span>'
                f'  <span class="diag-code">{_html_escape(diag.code)}</span>'
                f'  <span class="diag-location">{_html_escape(diag.location_str)}</span>'
                f'  <p class="diag-message">{_html_escape(diag.message)}</p>'
                f'  <span class="diag-trust trust-{diag.trust_level.lower()}">'
                f"    {diag.trust_level}"
                f"  </span>"
                f"  {detail_html}"
                f"  {fix_html}"
                f"</div>"
            )

        body = "\n".join(rows) if rows else '<p class="diag-ok">✅ No issues.</p>'

        return (
            "<!DOCTYPE html>\n"
            '<html lang="en">\n'
            "<head>\n"
            '  <meta charset="utf-8">\n'
            "  <title>deppy diagnostics</title>\n"
            "  <style>\n"
            "    body { font-family: monospace; margin: 2em; background: #1e1e1e; color: #d4d4d4; }\n"
            "    .diag-item { border-left: 4px solid; padding: 0.5em 1em; margin: 0.5em 0; }\n"
            "    .diag-error { border-color: #f44; background: #2a1515; }\n"
            "    .diag-warning { border-color: #fa0; background: #2a2515; }\n"
            "    .diag-info { border-color: #4af; background: #151a2a; }\n"
            "    .diag-hint { border-color: #4fa; background: #152a1a; }\n"
            "    .diag-code { color: #888; margin-left: 0.5em; }\n"
            "    .diag-location { color: #6af; margin-left: 0.5em; }\n"
            "    .diag-message { margin: 0.3em 0; }\n"
            "    .diag-detail { color: #999; font-size: 0.9em; white-space: pre-wrap; }\n"
            "    .diag-fix { color: #4f4; margin-top: 0.3em; }\n"
            "    .diag-trust { font-size: 0.8em; padding: 2px 6px; border-radius: 3px; }\n"
            "    .trust-untrusted { background: #533; color: #faa; }\n"
            "    .trust-llm_judged { background: #553; color: #ffa; }\n"
            "    .trust-property_checked { background: #353; color: #afa; }\n"
            "    .trust-z3_proven { background: #335; color: #aaf; }\n"
            "    .trust-lean_verified { background: #535; color: #faf; }\n"
            "    .diag-ok { color: #4f4; font-size: 1.5em; }\n"
            "  </style>\n"
            "</head>\n"
            "<body>\n"
            "  <h1>deppy diagnostics</h1>\n"
            f"  {body}\n"
            "</body>\n"
            "</html>\n"
        )


# ═══════════════════════════════════════════════════════════════════════════════
# ExistingCodeChecker — the zero-change entry point
# ═══════════════════════════════════════════════════════════════════════════════


class ExistingCodeChecker:
    """Check existing Python code for type/intent gaps — no annotations needed.

    This is the **zero-change entry point**: run ``deppy check myfile.py``
    and get diagnostics without modifying a single line.

    Pipeline:

    1. **Parse** the source (``ast.parse``).
    2. **Extract** an implicit presheaf (functions → intent + structural + code).
    3. **Compute** H¹ of the implicit cover (find obstructions).
    4. **Localize** H¹ generators to human-readable diagnostics.
    5. **Format** and return.

    Parameters
    ----------
    functor:
        Localization functor to use.  Defaults to a fresh
        :class:`LocalizationFunctor`.
    suggest_fixes:
        Whether to attempt fix suggestions.
    include_h1_names:
        Expose the raw cohomological generator names.
    """

    def __init__(
        self,
        functor: Optional[LocalizationFunctor] = None,
        suggest_fixes: bool = True,
        include_h1_names: bool = False,
    ) -> None:
        self._functor = functor or LocalizationFunctor(
            suggest_fixes=suggest_fixes,
            include_h1_names=include_h1_names,
        )

    def check_file(self, file_path: str) -> CheckResult:
        """Check a single Python file.

        Parameters
        ----------
        file_path:
            Path to a ``.py`` file.

        Returns
        -------
        CheckResult
            Diagnostics and summary.
        """
        path = Path(file_path)
        if not path.exists():
            return CheckResult(
                file_path=file_path,
                diagnostics=[
                    Diagnostic(
                        file_path=file_path,
                        severity=DiagnosticSeverity.ERROR,
                        code="DEPPY-SYS-001",
                        message=f"File not found: {file_path}",
                    )
                ],
            )
        try:
            source = path.read_text(encoding="utf-8")
        except OSError as exc:
            return CheckResult(
                file_path=file_path,
                diagnostics=[
                    Diagnostic(
                        file_path=file_path,
                        severity=DiagnosticSeverity.ERROR,
                        code="DEPPY-SYS-002",
                        message=f"Cannot read file: {exc}",
                    )
                ],
            )
        return self.check_source(source, file_path=file_path)

    def check_directory(
        self,
        dir_path: str,
        glob: str = "**/*.py",
    ) -> CheckResult:
        """Check all Python files in a directory tree.

        Parameters
        ----------
        dir_path:
            Root directory.
        glob:
            Glob pattern for file selection.

        Returns
        -------
        CheckResult
            Aggregated diagnostics across all files.
        """
        root = Path(dir_path)
        if not root.is_dir():
            return CheckResult(
                file_path=dir_path,
                diagnostics=[
                    Diagnostic(
                        file_path=dir_path,
                        severity=DiagnosticSeverity.ERROR,
                        code="DEPPY-SYS-003",
                        message=f"Not a directory: {dir_path}",
                    )
                ],
            )

        all_diags: List[Diagnostic] = []
        total_h1 = 0
        if glob == "**/*.py":
            py_files = iter_default_python_files(root)
        else:
            py_files = [path.resolve() for path in sorted(root.glob(glob)) if path.is_file()]
        for py_file in py_files:
            if py_file.is_file():
                result = self.check_file(str(py_file))
                all_diags.extend(result.diagnostics)
                total_h1 += result.h1_dimension

        return self._build_result(dir_path, all_diags, total_h1)

    def check_source(
        self,
        source: str,
        file_path: str = "<stdin>",
    ) -> CheckResult:
        """Check a source string directly.

        Parameters
        ----------
        source:
            Python source code.
        file_path:
            Virtual file path for diagnostic locations.

        Returns
        -------
        CheckResult
        """
        # Step 1: Parse
        try:
            tree = ast.parse(source, filename=file_path)
        except SyntaxError as exc:
            return CheckResult(
                file_path=file_path,
                diagnostics=[
                    Diagnostic(
                        file_path=file_path,
                        line_start=exc.lineno or 0,
                        col_start=exc.offset or 0,
                        severity=DiagnosticSeverity.ERROR,
                        code="DEPPY-SYS-004",
                        message=f"Syntax error: {exc.msg}",
                    )
                ],
            )

        # Step 2: Extract implicit presheaf (functions with their layers)
        obstructions = self._extract_obstructions(tree, source, file_path)

        # Step 3: Localize
        diagnostics = self._functor.localize_batch(obstructions)

        # Step 4: Build result
        return self._build_result(file_path, diagnostics, len(obstructions))

    # ------------------------------------------------------------------
    # Implicit presheaf extraction
    # ------------------------------------------------------------------

    def _extract_obstructions(
        self,
        tree: ast.Module,
        source: str,
        file_path: str,
    ) -> List[Dict[str, Any]]:
        """Walk the AST and find implicit layer mismatches.

        For each function/method:
        - INTENT layer: docstring
        - STRUCTURAL layer: type annotations, asserts
        - CODE layer: the body
        """
        obstructions: List[Dict[str, Any]] = []
        source_lines = source.splitlines()

        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                obs_list = self._check_function(node, source_lines, file_path)
                obstructions.extend(obs_list)

        return obstructions

    def _check_function(
        self,
        node: Union[ast.FunctionDef, ast.AsyncFunctionDef],
        source_lines: List[str],
        file_path: str,
    ) -> List[Dict[str, Any]]:
        """Check a single function for layer gaps."""
        obstructions: List[Dict[str, Any]] = []
        func_name = node.name
        docstring = ast.get_docstring(node)
        has_annotations = self._has_type_annotations(node)
        has_asserts = self._has_assertions(node)
        has_guards = self._has_guard_conditions(node)
        has_return_annotation = node.returns is not None

        line_start = node.lineno
        line_end = node.end_lineno or node.lineno
        code_text = "\n".join(source_lines[line_start - 1 : line_end])
        implementation_start = line_start
        if (
            node.body
            and isinstance(node.body[0], ast.Expr)
            and isinstance(getattr(node.body[0], "value", None), ast.Constant)
            and isinstance(node.body[0].value.value, str)
        ):
            if len(node.body) > 1:
                implementation_start = node.body[1].lineno
            else:
                implementation_start = line_end
        implementation_text = "\n".join(
            source_lines[implementation_start - 1 : line_end]
        )
        fragments = ()
        accepted_constraints = []

        if docstring:
            from deppy.nl_synthesis.docstring_parser import parse_docstring_fragments
            from deppy.nl_synthesis.verifier import verify_synthesized_constraints

            params = [
                arg.arg
                for arg in node.args.args
                if arg.arg not in {"self", "cls"}
            ]
            fragments = parse_docstring_fragments(docstring)
            constraints = verify_synthesized_constraints(
                fragments,
                params,
            )
            accepted_constraints = [
                constraint
                for constraint in constraints
                if constraint.verification_status == "accepted"
            ]
        has_explicit_ensures = any(fragment.kind == "ensures" for fragment in fragments)

        base = {
            "file_path": file_path,
            "line_start": line_start,
            "line_end": line_end,
            "col_start": node.col_offset,
            "col_end": node.end_col_offset or 0,
            "function_name": func_name,
            "code_text": code_text[:500],
        }

        contract_intent = _extract_contract_intent(docstring) if docstring else None

        # Intent–Structural gap: only explicit contract-like docstrings should
        # generate proof obligations. Summary prose is too noisy.
        if contract_intent and not has_annotations and not has_asserts and not has_guards:
            obstructions.append({
                **base,
                "layer_a": LAYER_INTENT,
                "layer_b": LAYER_STRUCTURAL,
                "intent_text": contract_intent,
                "property_name": "documented behavior",
                "h1_name": f"H1_IS_{func_name}",
            })

        # Intent–Code gap: only explicit return-contract sections/phrases
        # should trigger this fallback. Plain summary sentences like
        # "Return args as list." are too noisy to treat as mismatches.
        if docstring and not has_return_annotation and not has_explicit_ensures:
            returns_mention = _mentions_return(docstring)
            if returns_mention:
                obstructions.append({
                    **base,
                    "layer_a": LAYER_INTENT,
                    "layer_b": LAYER_CODE,
                    "intent_text": returns_mention,
                    "h1_name": f"H1_IC_{func_name}",
                })

        # Structural–Code gap: bare returns only matter when the declared
        # return type is not explicitly ``None``.
        if (
            has_return_annotation
            and not self._returns_none_annotation(node)
            and self._has_bare_return(node)
        ):
            ret_ann = ast.dump(node.returns) if node.returns else "?"
            obstructions.append({
                **base,
                "layer_a": LAYER_STRUCTURAL,
                "layer_b": LAYER_CODE,
                "type_expected": ret_ann,
                "type_actual": "None (bare return)",
                "h1_name": f"H1_SC_{func_name}",
            })

        if docstring:
            for index, constraint in enumerate(accepted_constraints, 1):
                predicate_text = constraint.predicate_text or constraint.description
                if (
                    constraint.target
                    and constraint.kind in {"requires", "invariant"}
                    and "result" in predicate_text
                    and constraint.target not in predicate_text
                ):
                    predicate_text = predicate_text.replace("result", constraint.target)
                if not self._constraint_has_support(implementation_text, predicate_text):
                    obstructions.append({
                        **base,
                        "layer_a": LAYER_INTENT,
                        "layer_b": LAYER_CODE,
                        "intent_text": constraint.description,
                        "property_name": predicate_text,
                        "h1_name": f"H1_IC_{func_name}_{index}",
                        "counterexample": (
                            "The docstring-induced local section does not glue to the code layer; "
                            "no supporting implementation evidence was found."
                        ),
                    })
                if (
                    constraint.kind in {"requires", "invariant"}
                    and not self._constraint_has_structure(
                        predicate_text,
                        has_annotations=has_annotations,
                        has_asserts=has_asserts,
                        has_guards=has_guards,
                    )
                ):
                    obstructions.append({
                        **base,
                        "layer_a": LAYER_INTENT,
                        "layer_b": LAYER_STRUCTURAL,
                        "intent_text": constraint.description,
                        "property_name": predicate_text,
                        "h1_name": f"H1_IS_{func_name}_{index}",
                    })

        return obstructions

    def _has_type_annotations(
        self, node: Union[ast.FunctionDef, ast.AsyncFunctionDef]
    ) -> bool:
        """Check if any parameter has a type annotation."""
        for arg in node.args.args:
            if arg.annotation is not None:
                return True
        return node.returns is not None

    def _has_assertions(
        self, node: Union[ast.FunctionDef, ast.AsyncFunctionDef]
    ) -> bool:
        """Check if the function body contains assert statements."""
        for child in ast.walk(node):
            if isinstance(child, ast.Assert):
                return True
        return False

    def _has_guard_conditions(
        self, node: Union[ast.FunctionDef, ast.AsyncFunctionDef]
    ) -> bool:
        """Check for parameter-dependent runtime guards in the current function body."""
        params = {
            arg.arg
            for arg in node.args.args
            if arg.arg not in {"self", "cls"}
        }
        if not params:
            return False

        class _GuardVisitor(ast.NodeVisitor):
            def __init__(self, parameter_names: Set[str]) -> None:
                self._parameter_names = parameter_names
                self.found = False

            def visit_If(self, child: ast.If) -> None:  # type: ignore[override]
                names = {
                    name.id
                    for name in ast.walk(child.test)
                    if isinstance(name, ast.Name)
                }
                if self._parameter_names & names:
                    self.found = True
                    return
                self.generic_visit(child)

            def visit_Assert(self, child: ast.Assert) -> None:  # type: ignore[override]
                names = {
                    name.id
                    for name in ast.walk(child.test)
                    if isinstance(name, ast.Name)
                }
                if self._parameter_names & names:
                    self.found = True

            def visit_FunctionDef(self, child: ast.FunctionDef) -> None:  # type: ignore[override]
                return

            def visit_AsyncFunctionDef(self, child: ast.AsyncFunctionDef) -> None:  # type: ignore[override]
                return

            def visit_Lambda(self, child: ast.Lambda) -> None:  # type: ignore[override]
                return

            def visit_ClassDef(self, child: ast.ClassDef) -> None:  # type: ignore[override]
                return

        visitor = _GuardVisitor(params)
        for statement in node.body:
            visitor.visit(statement)
            if visitor.found:
                return True
        return False

    def _has_bare_return(
        self, node: Union[ast.FunctionDef, ast.AsyncFunctionDef]
    ) -> bool:
        """Check if the function body has a ``return`` with no value."""

        class _BareReturnVisitor(ast.NodeVisitor):
            def __init__(self) -> None:
                self.found = False

            def visit_Return(self, child: ast.Return) -> None:  # type: ignore[override]
                if child.value is None:
                    self.found = True

            def visit_FunctionDef(self, child: ast.FunctionDef) -> None:  # type: ignore[override]
                return

            def visit_AsyncFunctionDef(self, child: ast.AsyncFunctionDef) -> None:  # type: ignore[override]
                return

            def visit_Lambda(self, child: ast.Lambda) -> None:  # type: ignore[override]
                return

            def visit_ClassDef(self, child: ast.ClassDef) -> None:  # type: ignore[override]
                return

        visitor = _BareReturnVisitor()
        for statement in node.body:
            visitor.visit(statement)
            if visitor.found:
                return True
        return False

    @staticmethod
    def _returns_none_annotation(
        node: Union[ast.FunctionDef, ast.AsyncFunctionDef]
    ) -> bool:
        """Return True when the declared return annotation is exactly ``None``."""
        annotation = node.returns
        return (
            isinstance(annotation, ast.Constant) and annotation.value is None
        ) or (
            isinstance(annotation, ast.Name) and annotation.id == "None"
        )

    @staticmethod
    def _constraint_has_structure(
        predicate_text: str,
        *,
        has_annotations: bool,
        has_asserts: bool,
        has_guards: bool,
    ) -> bool:
        lowered = predicate_text.lower()
        if any(token in lowered for token in ("len(", "> 0", ">= 0", "sorted", "unique", "non_empty")):
            return has_annotations or has_asserts or has_guards
        return True

    @staticmethod
    def _constraint_has_support(code_text: str, predicate_text: str) -> bool:
        lowered_code = code_text.lower()
        lowered_pred = predicate_text.lower()

        if "len(result)" in lowered_pred or "result is non-empty" in lowered_pred:
            return any(
                token in lowered_code
                for token in ("assert ", "raise valueerror", "raise indexerror", "raise runtimeerror")
            )
        if "len(" in lowered_pred or "non-empty" in lowered_pred or "non_empty" in lowered_pred:
            return any(
                token in lowered_code
                for token in ("len(", "if not ", "assert ", "raise valueerror")
            )

        evidence_groups = [
            ((">= 0", "> 0", "positive", "non-negative"), (">= 0", "> 0", "max(0", "abs(", "raise valueerror")),
            (("sorted",), ("sorted(", ".sort(")),
            (("unique",), ("set(", "dict.fromkeys", "unique")),
            (("none", "not none", "non_null"), ("is not none", "is none", "return none", "raise valueerror")),
        ]
        for markers, evidence in evidence_groups:
            if any(marker in lowered_pred for marker in markers):
                return any(token in lowered_code for token in evidence)

        if "return" in lowered_pred:
            return "return " in lowered_code
        return True

    # ------------------------------------------------------------------
    # Result builder
    # ------------------------------------------------------------------

    def _build_result(
        self,
        file_path: str,
        diagnostics: List[Diagnostic],
        h1_dim: int,
    ) -> CheckResult:
        trust_summary: Dict[str, int] = {}
        for d in diagnostics:
            trust_summary[d.trust_level] = trust_summary.get(d.trust_level, 0) + 1

        return CheckResult(
            file_path=file_path,
            diagnostics=diagnostics,
            h1_dimension=h1_dim,
            trust_summary=trust_summary,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════════════════════════


def _quote(text: str, max_len: int = 120) -> str:
    """Quote a text fragment, truncating if necessary."""
    text = text.strip().replace("\n", " ")
    if len(text) > max_len:
        return text[: max_len - 3] + "..."
    return text


def _truncate_lines(text: str, max_lines: int) -> str:
    """Truncate text to at most *max_lines* lines."""
    lines = text.splitlines()
    if len(lines) <= max_lines:
        return text
    return "\n".join(lines[:max_lines]) + f"\n... ({len(lines) - max_lines} more lines)"


def _html_escape(text: str) -> str:
    """Minimal HTML escaping."""
    return (
        text.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


def _make_diff_snippet(
    file_path: str, line: int, old: str, new: str
) -> str:
    """Create a minimal unified-diff snippet."""
    old_lines = old.splitlines(keepends=True) if old else []
    new_lines = new.splitlines(keepends=True)
    diff = difflib.unified_diff(
        old_lines,
        new_lines,
        fromfile=f"a/{file_path}",
        tofile=f"b/{file_path}",
        lineterm="",
    )
    return "\n".join(diff)


def _first_sentence(text: str) -> str:
    """Extract the first sentence from a docstring."""
    text = text.strip()
    for end in (".", "!", "?"):
        idx = text.find(end)
        if idx != -1:
            return text[: idx + 1]
    # No sentence-ending punctuation: take first line
    return text.split("\n")[0]


def _mentions_return(docstring: str) -> Optional[str]:
    """Check if a docstring mentions a return value and extract that clause."""
    for line in docstring.splitlines():
        stripped = line.strip()
        if re.match(r"^(returns?|yields?)\s*:", stripped, re.IGNORECASE):
            return _first_sentence(stripped) or stripped[:80]

    match = re.search(
        r"\b(return value|returned value|returns?:)\b",
        docstring,
        re.IGNORECASE,
    )
    if match:
        start = max(0, match.start() - 20)
        end = min(len(docstring), match.end() + 80)
        fragment = docstring[start:end].strip()
        return _first_sentence(fragment) or fragment[:80]
    return None


def _extract_contract_intent(docstring: str) -> Optional[str]:
    """Return a contract-like claim from a docstring, if one is explicit."""
    first = _first_sentence(docstring).strip()
    if not first:
        return None

    if re.match(
        r"^(args?|arguments?|parameters?|returns?|yields?|raises?|requires?|ensures?|preconditions?|postconditions?|invariants?)\s*:$",
        first,
        re.IGNORECASE,
    ):
        return None

    lowered = first.lower()
    if re.search(
        r"\b(requires?|ensures?|guarantees?|must|shall|only if|never|always|raises?)\b",
        lowered,
    ):
        return first

    for line in docstring.splitlines():
        stripped = line.strip()
        if re.match(
            r"^(args?|arguments?|parameters?|returns?|yields?|raises?|requires?|ensures?|preconditions?|postconditions?|invariants?)\s*:",
            stripped,
            re.IGNORECASE,
        ):
            return first

    return None


# ═══════════════════════════════════════════════════════════════════════════════
# Module-level convenience
# ═══════════════════════════════════════════════════════════════════════════════


def check_file(path: str, **kwargs: Any) -> CheckResult:
    """Convenience: check a file with default settings."""
    return ExistingCodeChecker(**kwargs).check_file(path)


def check_source(source: str, **kwargs: Any) -> CheckResult:
    """Convenience: check a source string with default settings."""
    return ExistingCodeChecker(**kwargs).check_source(source)
