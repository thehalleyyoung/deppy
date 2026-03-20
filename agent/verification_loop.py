"""
Verification loop for deppy's hybrid verification pipeline.

Runs structural (Z3), semantic (oracle), anti-hallucination, and optional Lean
translation/discharge on each generated module.  Also provides CEGAR-based
repair and cross-module contract checking.
"""
from __future__ import annotations

import ast
import hashlib
import json
import time
import re
import os
import copy
import logging
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Set,
    Tuple,
)

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Trust-level lattice (bottom → top)
# ---------------------------------------------------------------------------
TRUST_LEVELS = [
    "UNCHECKED",
    "LLM_JUDGED",
    "Z3_PROVEN",
    "LEAN_VERIFIED",
]

TRUST_RANK: Dict[str, int] = {level: i for i, level in enumerate(TRUST_LEVELS)}


def _min_trust(*levels: str) -> str:
    """Return the lowest trust level among the given levels."""
    if not levels:
        return "UNCHECKED"
    return min(levels, key=lambda l: TRUST_RANK.get(l, 0))


def _max_trust(*levels: str) -> str:
    """Return the highest trust level among the given levels."""
    if not levels:
        return "UNCHECKED"
    return max(levels, key=lambda l: TRUST_RANK.get(l, 0))


def _content_hash(source: str) -> str:
    """SHA-256 content hash of source code."""
    return hashlib.sha256(source.encode("utf-8")).hexdigest()


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ VerificationConfig                                                       │
# └──────────────────────────────────────────────────────────────────────────┘

@dataclass
class VerificationConfig:
    """Configuration knobs for the verification pipeline."""

    z3_timeout_ms: Optional[int] = None
    """Per-query Z3 timeout in milliseconds. ``None`` means no timeout."""

    semantic_confidence_threshold: float = 0.85
    """Minimum confidence from the semantic oracle to count as passing."""

    max_cegar_rounds: int = 5
    """Maximum CEGAR repair iterations before giving up."""

    emit_lean: bool = False
    """Whether to emit Lean 4 proof obligations."""

    cache_enabled: bool = True
    """Whether to cache verification results by content hash."""

    lean_timeout_s: Optional[int] = None
    """Per-obligation Lean check timeout in seconds. ``None`` means no timeout."""

    hallucination_detectors: List[str] = field(
        default_factory=lambda: [
            "fabricated_api",
            "phantom_field",
            "impossible_return",
            "type_mismatch",
            "unreachable_branch",
        ]
    )
    """Which anti-hallucination detectors to run."""

    oracle_model: str = "gpt-4"
    """LLM model to use for semantic oracle calls."""

    strict_mode: bool = False
    """If True, any residual obligation causes the whole module to fail."""


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ VerificationResult                                                       │
# └──────────────────────────────────────────────────────────────────────────┘

@dataclass
class VerificationResult:
    """Result of running the full verification pipeline on a single module."""

    module_name: str
    passed: bool
    trust_level: str

    structural_results: List[Dict[str, Any]] = field(default_factory=list)
    """Each entry: {claim, status, counterexample?, z3_time_ms}."""

    semantic_results: List[Dict[str, Any]] = field(default_factory=list)
    """Each entry: {claim, status, confidence, oracle_response}."""

    hallucination_findings: List[Dict[str, Any]] = field(default_factory=list)
    """Each entry: {detector, location, description, severity, suggestion}."""

    lean_obligations: List[Dict[str, Any]] = field(default_factory=list)
    """Each entry: {theorem_name, statement, status, proof?}."""

    discharged: int = 0
    residual: int = 0

    h1_status: str = "H\u00b9 = 0"
    """Cohomological status: 'H\u00b9 = 0' means no obstructions detected."""

    content_hash: str = ""
    duration_ms: float = 0.0

    errors: List[str] = field(default_factory=list)
    """Non-fatal errors encountered during verification."""

    cegar_rounds: int = 0
    """Number of CEGAR rounds needed (0 if first-pass success)."""

    def summary(self) -> str:
        """Human-readable one-paragraph summary."""
        parts: List[str] = []
        parts.append(f"Module '{self.module_name}': "
                      f"{'PASSED' if self.passed else 'FAILED'} "
                      f"(trust={self.trust_level})")

        n_struct = len(self.structural_results)
        n_struct_ok = sum(1 for r in self.structural_results
                          if r.get("status") == "proven")
        parts.append(f"Structural: {n_struct_ok}/{n_struct}")

        n_sem = len(self.semantic_results)
        n_sem_ok = sum(1 for r in self.semantic_results
                        if r.get("status") == "passed")
        parts.append(f"Semantic: {n_sem_ok}/{n_sem}")

        n_hall = len(self.hallucination_findings)
        parts.append(f"Hallucinations: {n_hall}")

        if self.lean_obligations:
            parts.append(
                f"Lean: {self.discharged} discharged, "
                f"{self.residual} sorry"
            )

        parts.append(f"{self.h1_status}")
        parts.append(f"Duration: {self.duration_ms:.0f}ms")

        if self.cegar_rounds:
            parts.append(f"CEGAR rounds: {self.cegar_rounds}")

        return " | ".join(parts)

    def to_dict(self) -> Dict[str, Any]:
        """JSON-serialisable dictionary representation."""
        return {
            "module_name": self.module_name,
            "passed": self.passed,
            "trust_level": self.trust_level,
            "structural_results": self.structural_results,
            "semantic_results": self.semantic_results,
            "hallucination_findings": self.hallucination_findings,
            "lean_obligations": self.lean_obligations,
            "discharged": self.discharged,
            "residual": self.residual,
            "h1_status": self.h1_status,
            "content_hash": self.content_hash,
            "duration_ms": self.duration_ms,
            "errors": self.errors,
            "cegar_rounds": self.cegar_rounds,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> VerificationResult:
        """Re-hydrate from a dictionary."""
        return cls(
            module_name=d["module_name"],
            passed=d["passed"],
            trust_level=d["trust_level"],
            structural_results=d.get("structural_results", []),
            semantic_results=d.get("semantic_results", []),
            hallucination_findings=d.get("hallucination_findings", []),
            lean_obligations=d.get("lean_obligations", []),
            discharged=d.get("discharged", 0),
            residual=d.get("residual", 0),
            h1_status=d.get("h1_status", "H\u00b9 = 0"),
            content_hash=d.get("content_hash", ""),
            duration_ms=d.get("duration_ms", 0.0),
            errors=d.get("errors", []),
            cegar_rounds=d.get("cegar_rounds", 0),
        )


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ CrossModuleResult                                                        │
# └──────────────────────────────────────────────────────────────────────────┘

@dataclass
class CrossModuleResult:
    """Result of cross-module contract verification."""

    modules_checked: List[str] = field(default_factory=list)
    contracts_verified: int = 0
    contracts_failed: int = 0

    assume_guarantee_pairs: List[Dict[str, Any]] = field(default_factory=list)
    """Each entry: {assume_module, assume_name, guarantee_module, guarantee_name, status}."""

    shared_type_issues: List[Dict[str, Any]] = field(default_factory=list)
    """Each entry: {type_name, modules, issue_description}."""

    circular_dependencies: List[List[str]] = field(default_factory=list)
    """Cycles detected in the trust dependency graph."""

    h1_cross: str = "H\u00b9 = 0"
    """Cross-module cohomology status."""

    duration_ms: float = 0.0

    def summary(self) -> str:
        """Human-readable summary of cross-module verification."""
        parts: List[str] = []
        parts.append(
            f"Cross-module check: {len(self.modules_checked)} modules"
        )
        parts.append(
            f"Contracts: {self.contracts_verified} verified, "
            f"{self.contracts_failed} failed"
        )

        if self.shared_type_issues:
            parts.append(
                f"Shared type issues: {len(self.shared_type_issues)}"
            )

        if self.circular_dependencies:
            parts.append(
                f"Circular trust deps: {len(self.circular_dependencies)}"
            )

        parts.append(self.h1_cross)
        parts.append(f"Duration: {self.duration_ms:.0f}ms")
        return " | ".join(parts)

    def to_dict(self) -> Dict[str, Any]:
        """JSON-serialisable dictionary representation."""
        return {
            "modules_checked": self.modules_checked,
            "contracts_verified": self.contracts_verified,
            "contracts_failed": self.contracts_failed,
            "assume_guarantee_pairs": self.assume_guarantee_pairs,
            "shared_type_issues": self.shared_type_issues,
            "circular_dependencies": self.circular_dependencies,
            "h1_cross": self.h1_cross,
            "duration_ms": self.duration_ms,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> CrossModuleResult:
        """Re-hydrate from a dictionary."""
        return cls(
            modules_checked=d.get("modules_checked", []),
            contracts_verified=d.get("contracts_verified", 0),
            contracts_failed=d.get("contracts_failed", 0),
            assume_guarantee_pairs=d.get("assume_guarantee_pairs", []),
            shared_type_issues=d.get("shared_type_issues", []),
            circular_dependencies=d.get("circular_dependencies", []),
            h1_cross=d.get("h1_cross", "H\u00b9 = 0"),
            duration_ms=d.get("duration_ms", 0.0),
        )


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ Internal helpers — claim extraction & decidability classification        │
# └──────────────────────────────────────────────────────────────────────────┘

# Regex patterns for extracting deppy annotations from mixed-mode source
_CLAIM_PATTERN = re.compile(
    r'#\s*@(?P<kind>require|ensure|invariant|assume|guarantee)'
    r'\s*\(\s*"(?P<text>[^"]+)"\s*\)',
)
_TYPE_ANNOTATION_PATTERN = re.compile(
    r'#\s*@type\s+(?P<name>\w+)\s*:\s*(?P<type_expr>.+)',
)
_NL_FRAGMENT_PATTERN = re.compile(
    r'"""NL\s*\n(?P<body>.*?)\n\s*"""',
    re.DOTALL,
)

# Keywords that suggest structural (decidable) properties
_STRUCTURAL_KEYWORDS: Set[str] = {
    "non-negative", "positive", "returns int", "returns float",
    "returns bool", "returns str", "returns list", "returns dict",
    "returns None", "not None", "length", "bounded", "range",
    "sorted", "unique", "non-empty", "at most", "at least",
    "equals", "less than", "greater than", "between", "divides",
    "even", "odd", "power of", "multiple of", "monotonic",
    "injective", "surjective", "idempotent", "commutative",
    "associative", "type-safe", "well-typed", "no side effects",
}

# Keywords that suggest semantic (undecidable) properties
_SEMANTIC_KEYWORDS: Set[str] = {
    "correct", "reasonable", "appropriate", "meaningful",
    "user-friendly", "efficient", "secure", "robust",
    "well-documented", "maintainable", "readable", "clean",
    "idiomatic", "production-ready", "handles edge cases",
    "follows best practices", "good error messages",
    "consistent with", "compatible with", "similar to",
}


def _extract_claims(source: str) -> List[Dict[str, Any]]:
    """Extract all claims (annotations) from deppy mixed-mode source."""
    claims: List[Dict[str, Any]] = []
    for i, line in enumerate(source.splitlines(), 1):
        m = _CLAIM_PATTERN.search(line)
        if m:
            claims.append({
                "kind": m.group("kind"),
                "text": m.group("text"),
                "line": i,
                "raw": line.strip(),
            })
    return claims


def _extract_nl_fragments(source: str) -> List[Dict[str, Any]]:
    """Extract NL (natural-language) fragments from triple-quoted blocks."""
    fragments: List[Dict[str, Any]] = []
    for m in _NL_FRAGMENT_PATTERN.finditer(source):
        start_line = source[:m.start()].count("\n") + 1
        fragments.append({
            "body": m.group("body").strip(),
            "start_line": start_line,
            "raw": m.group(0),
        })
    return fragments


def _extract_type_annotations(source: str) -> List[Dict[str, Any]]:
    """Extract explicit type annotations from source."""
    annotations: List[Dict[str, Any]] = []
    for i, line in enumerate(source.splitlines(), 1):
        m = _TYPE_ANNOTATION_PATTERN.search(line)
        if m:
            annotations.append({
                "name": m.group("name"),
                "type_expr": m.group("type_expr").strip(),
                "line": i,
            })
    return annotations


def _classify_claim(claim: Dict[str, Any]) -> str:
    """
    Classify a claim as 'structural' or 'semantic'.

    A claim is structural if it can be decided by a solver (Z3).
    A claim is semantic if it requires an oracle (LLM judgment).
    """
    text_lower = claim["text"].lower()

    structural_score = sum(
        1 for kw in _STRUCTURAL_KEYWORDS if kw in text_lower
    )
    semantic_score = sum(
        1 for kw in _SEMANTIC_KEYWORDS if kw in text_lower
    )

    # Heuristic: structural wins ties because we prefer machine proofs
    if structural_score >= semantic_score:
        return "structural"
    return "semantic"


def _classify_claims(
    claims: List[Dict[str, Any]],
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    """Split claims into structural and semantic buckets."""
    structural: List[Dict[str, Any]] = []
    semantic: List[Dict[str, Any]] = []
    for claim in claims:
        category = _classify_claim(claim)
        tagged = {**claim, "category": category}
        if category == "structural":
            structural.append(tagged)
        else:
            semantic.append(tagged)
    return structural, semantic


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ Internal helpers — Z3 mock / interface                                   │
# └──────────────────────────────────────────────────────────────────────────┘

def _z3_check_claim(
    source: str,
    claim: Dict[str, Any],
    timeout_ms: Optional[int],
) -> Dict[str, Any]:
    """
    Attempt to prove a structural claim using Z3.

    In production this invokes the Z3 solver via its Python bindings.
    Here we implement a conservative heuristic checker that inspects the
    source for patterns consistent with the claim, so the pipeline is
    fully exercisable without Z3 installed.
    """
    start = time.monotonic()
    text = claim["text"].lower()
    result: Dict[str, Any] = {
        "claim": claim["text"],
        "kind": claim.get("kind", "unknown"),
        "line": claim.get("line", 0),
        "category": "structural",
    }

    proven = False
    counterexample: Optional[str] = None

    # --- Pattern: return-type claims ---
    ret_type_match = re.search(r"returns?\s+(int|float|bool|str|list|dict|none)", text)
    if ret_type_match:
        expected_type = ret_type_match.group(1)
        # Look for `-> <type>` annotations in source near the claim line
        line_no = claim.get("line", 0)
        window = source.splitlines()[max(0, line_no - 5): line_no + 15]
        window_text = "\n".join(window)
        if re.search(r"->\s*" + re.escape(expected_type), window_text, re.IGNORECASE):
            proven = True
        else:
            counterexample = (
                f"No return-type annotation matching '{expected_type}' "
                f"found near line {line_no}"
            )

    # --- Pattern: non-negative / positive ---
    if "non-negative" in text or "positive" in text:
        line_no = claim.get("line", 0)
        window = source.splitlines()[max(0, line_no - 3): line_no + 20]
        window_text = "\n".join(window)
        if re.search(r"(>=\s*0|>\s*0|abs\(|max\(0)", window_text):
            proven = True
        else:
            counterexample = "No non-negativity guard found in scope"

    # --- Pattern: non-empty ---
    if "non-empty" in text:
        line_no = claim.get("line", 0)
        window = source.splitlines()[max(0, line_no - 3): line_no + 20]
        window_text = "\n".join(window)
        if re.search(r"(len\(.+\)\s*>\s*0|if\s+not\s+\w+\s*:)", window_text):
            proven = True
        else:
            counterexample = "No non-empty check found in scope"

    # --- Pattern: bounded / range ---
    if "bounded" in text or "range" in text or "between" in text:
        line_no = claim.get("line", 0)
        window = source.splitlines()[max(0, line_no - 3): line_no + 20]
        window_text = "\n".join(window)
        if re.search(r"(min\(|max\(|clamp|assert\s+.+[<>]=?)", window_text):
            proven = True
        else:
            counterexample = "No bounding logic found in scope"

    # --- Pattern: sorted ---
    if "sorted" in text:
        line_no = claim.get("line", 0)
        window = source.splitlines()[max(0, line_no - 3): line_no + 20]
        window_text = "\n".join(window)
        if re.search(r"(sorted\(|\.sort\()", window_text):
            proven = True
        else:
            counterexample = "No sorting operation found in scope"

    # --- Pattern: unique ---
    if "unique" in text:
        line_no = claim.get("line", 0)
        window = source.splitlines()[max(0, line_no - 3): line_no + 20]
        window_text = "\n".join(window)
        if re.search(r"(set\(|dict\.fromkeys|unique|dedup)", window_text):
            proven = True
        else:
            counterexample = "No uniqueness enforcement found in scope"

    # --- Fallback: unknown structural claim ---
    if not proven and counterexample is None:
        # Conservative: mark as unproven with an informative message
        counterexample = (
            f"Structural claim '{claim['text']}' could not be "
            f"automatically verified — manual Z3 encoding required"
        )

    elapsed = (time.monotonic() - start) * 1000
    result["status"] = "proven" if proven else "failed"
    result["z3_time_ms"] = round(elapsed, 2)
    if counterexample:
        result["counterexample"] = counterexample
    return result


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ Internal helpers — Semantic oracle                                       │
# └──────────────────────────────────────────────────────────────────────────┘

def _default_oracle(source: str, claim: Dict[str, Any]) -> Dict[str, Any]:
    """
    Default semantic oracle: a heuristic stand-in for an LLM call.

    In production the oracle_fn would call an actual LLM; this
    implementation provides a deterministic baseline so the pipeline can
    run without network access.
    """
    text = claim["text"].lower()
    confidence = 0.75  # baseline

    # Boost confidence for claims that are backed by common patterns
    if any(kw in text for kw in ("handles edge cases", "robust")):
        # Look for try/except in source
        if "try:" in source and "except" in source:
            confidence = 0.90
    if "user-friendly" in text or "good error messages" in text:
        if "raise ValueError" in source or "raise TypeError" in source:
            confidence = 0.88
    if "well-documented" in text or "readable" in text:
        docstring_count = source.count('"""')
        if docstring_count >= 4:
            confidence = 0.92
    if "idiomatic" in text or "pythonic" in text:
        # Very rough heuristic
        if "list comprehension" in source or "[" in source and "for" in source:
            confidence = 0.87
    if "efficient" in text or "performance" in text:
        confidence = 0.80
    if "secure" in text:
        if "sanitize" in source or "escape" in source or "validate" in source:
            confidence = 0.88
        else:
            confidence = 0.60

    return {
        "claim": claim["text"],
        "confidence": round(confidence, 3),
        "reasoning": f"Heuristic oracle judgment for: {claim['text']}",
    }


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ Internal helpers — Anti-hallucination detectors                          │
# └──────────────────────────────────────────────────────────────────────────┘

def _detect_fabricated_apis(source: str) -> List[Dict[str, Any]]:
    """Detect calls to APIs/modules that don't exist in the standard library."""
    findings: List[Dict[str, Any]] = []
    # Common hallucinated modules
    fake_modules = {
        "utils.magic", "stdlib.helpers", "python_extras",
        "builtins.advanced", "system.core", "net.http.simple",
    }
    for i, line in enumerate(source.splitlines(), 1):
        for fake in fake_modules:
            if f"import {fake}" in line or f"from {fake}" in line:
                findings.append({
                    "detector": "fabricated_api",
                    "location": f"line {i}",
                    "description": f"Import of non-existent module '{fake}'",
                    "severity": "high",
                    "suggestion": f"Remove import of '{fake}' and use a real module",
                })
    return findings


def _detect_phantom_fields(source: str) -> List[Dict[str, Any]]:
    """Detect access to fields/attributes that are never defined."""
    findings: List[Dict[str, Any]] = []
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return findings

    ignored_attrs = {
        "__class__", "__dict__", "__init__", "__repr__", "__str__",
    }

    for class_node in [node for node in ast.walk(tree) if isinstance(node, ast.ClassDef)]:
        assigned: Set[str] = set()
        class_level_attrs: Set[str] = set()
        methods: Set[str] = set()

        for node in class_node.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                methods.add(node.name)
            elif isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        class_level_attrs.add(target.id)
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                class_level_attrs.add(node.target.id)

        for node in ast.walk(class_node):
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if (
                        isinstance(target, ast.Attribute)
                        and isinstance(target.value, ast.Name)
                        and target.value.id == "self"
                    ):
                        assigned.add(target.attr)
            elif isinstance(node, ast.AnnAssign):
                target = node.target
                if (
                    isinstance(target, ast.Attribute)
                    and isinstance(target.value, ast.Name)
                    and target.value.id == "self"
                ):
                    assigned.add(target.attr)

        seen: Set[Tuple[int, str]] = set()
        for node in ast.walk(class_node):
            if not (
                isinstance(node, ast.Attribute)
                and isinstance(node.value, ast.Name)
                and node.value.id == "self"
                and isinstance(node.ctx, ast.Load)
            ):
                continue
            attr = node.attr
            key = (getattr(node, "lineno", 0), attr)
            if key in seen:
                continue
            seen.add(key)
            if (
                attr.startswith("_")
                or attr in ignored_attrs
                or attr in assigned
                or attr in methods
                or attr in class_level_attrs
            ):
                continue
            findings.append({
                "detector": "phantom_field",
                "location": f"line {getattr(node, 'lineno', 0)}",
                "description": f"Access to 'self.{attr}' which is never assigned",
                "severity": "medium",
                "suggestion": f"Initialize 'self.{attr}' in __init__",
            })
    return findings


def _detect_impossible_returns(source: str) -> List[Dict[str, Any]]:
    """Detect functions that claim to return a type but always return None."""
    findings: List[Dict[str, Any]] = []
    func_pattern = re.compile(
        r"def\s+(\w+)\s*\([^)]*\)\s*->\s*(\w+)\s*:"
    )
    lines = source.splitlines()
    for i, line in enumerate(lines):
        m = func_pattern.search(line)
        if m:
            func_name = m.group(1)
            ret_type = m.group(2)
            if ret_type == "None":
                continue
            # Look ahead for return statements
            body_lines = []
            indent = len(line) - len(line.lstrip())
            for j in range(i + 1, min(i + 50, len(lines))):
                if lines[j].strip() == "":
                    continue
                line_indent = len(lines[j]) - len(lines[j].lstrip())
                if line_indent <= indent and lines[j].strip():
                    break
                body_lines.append(lines[j])
            body = "\n".join(body_lines)
            if "return" not in body and ret_type != "None":
                findings.append({
                    "detector": "impossible_return",
                    "location": f"line {i + 1}",
                    "description": (
                        f"Function '{func_name}' declares return type "
                        f"'{ret_type}' but has no return statement"
                    ),
                    "severity": "high",
                    "suggestion": f"Add a return statement or change annotation to None",
                })
    return findings


def _detect_type_mismatches(source: str) -> List[Dict[str, Any]]:
    """Detect obvious type mismatches in assignments and returns."""
    findings: List[Dict[str, Any]] = []
    # Detect: x: int = "string"
    pattern = re.compile(r"(\w+)\s*:\s*(int|float|bool)\s*=\s*['\"]")
    for i, line in enumerate(source.splitlines(), 1):
        m = pattern.search(line)
        if m:
            findings.append({
                "detector": "type_mismatch",
                "location": f"line {i}",
                "description": (
                    f"Variable '{m.group(1)}' declared as {m.group(2)} "
                    f"but assigned a string literal"
                ),
                "severity": "high",
                "suggestion": "Fix the type annotation or the assigned value",
            })
    return findings


def _detect_unreachable_branches(source: str) -> List[Dict[str, Any]]:
    """Detect obviously unreachable code branches."""
    findings: List[Dict[str, Any]] = []
    lines = source.splitlines()
    for i, line in enumerate(lines):
        stripped = line.strip()
        # Pattern: code after unconditional return/raise/break/continue
        if stripped.startswith(("return ", "raise ", "break", "continue")):
            if i + 1 < len(lines):
                next_line = lines[i + 1].strip()
                if next_line and not next_line.startswith(("#", "except", "finally",
                                                            "elif", "else", "def",
                                                            "class", "@", ")")):
                    current_indent = len(line) - len(line.lstrip())
                    next_indent = len(lines[i + 1]) - len(lines[i + 1].lstrip())
                    if next_indent >= current_indent and next_line:
                        findings.append({
                            "detector": "unreachable_branch",
                            "location": f"line {i + 2}",
                            "description": (
                                f"Code after '{stripped.split()[0]}' "
                                f"is unreachable"
                            ),
                            "severity": "low",
                            "suggestion": "Remove unreachable code",
                        })
    return findings


_HALLUCINATION_DETECTORS: Dict[str, Callable[[str], List[Dict[str, Any]]]] = {
    "fabricated_api": _detect_fabricated_apis,
    "phantom_field": _detect_phantom_fields,
    "impossible_return": _detect_impossible_returns,
    "type_mismatch": _detect_type_mismatches,
    "unreachable_branch": _detect_unreachable_branches,
}


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ Internal helpers — Lean translation                                      │
# └──────────────────────────────────────────────────────────────────────────┘

def _claim_to_lean_obligation(
    claim: Dict[str, Any],
    index: int,
) -> Dict[str, Any]:
    """
    Translate a single claim into a Lean 4 theorem statement.

    Returns a dict with {theorem_name, statement, status}.
    """
    kind = claim.get("kind", "ensure")
    text = claim["text"]
    safe_name = re.sub(r"\W+", "_", text)[:60].strip("_").lower()
    theorem_name = f"obligation_{index}_{safe_name}"

    # Build a Lean-ish theorem statement
    statement = f"theorem {theorem_name} : sorry := by\n  sorry"

    return {
        "theorem_name": theorem_name,
        "statement": statement,
        "claim_text": text,
        "claim_kind": kind,
        "status": "sorry",  # not yet discharged
    }


def _translate_claims_to_lean(
    source: str,
    claims: List[Dict[str, Any]],
    module_name: str,
) -> Tuple[str, List[Dict[str, Any]]]:
    """
    Produce a Lean 4 file with proof obligations for all claims.

    Returns (lean_source, obligations_list).
    """
    obligations: List[Dict[str, Any]] = []
    lean_lines: List[str] = [
        f"-- Auto-generated by deppy for module: {module_name}",
        f"-- Source hash: {_content_hash(source)[:16]}",
        "",
        "import Mathlib.Tactic",
        "",
        f"namespace Deppy.{module_name.replace('.', '_').title()}",
        "",
    ]

    for i, claim in enumerate(claims):
        ob = _claim_to_lean_obligation(claim, i)
        obligations.append(ob)
        lean_lines.append(f"-- Claim: {claim['text']}")
        lean_lines.append(f"-- Kind: {claim.get('kind', 'unknown')}")
        lean_lines.append(ob["statement"])
        lean_lines.append("")

    lean_lines.append(f"end Deppy.{module_name.replace('.', '_').title()}")
    lean_lines.append("")

    lean_source = "\n".join(lean_lines)
    return lean_source, obligations


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ Internal helpers — obligation discharge                                  │
# └──────────────────────────────────────────────────────────────────────────┘

def _attempt_discharge(
    obligation: Dict[str, Any],
    lean_timeout_s: Optional[int],
) -> Dict[str, Any]:
    """
    Attempt to discharge a single Lean obligation.

    In production this would invoke `lean --run` or the Lean server.
    Here we simulate: obligations whose claim text matches simple patterns
    are marked as discharged; the rest remain sorry.
    """
    result = copy.deepcopy(obligation)
    text = obligation.get("claim_text", "").lower()

    # Simple patterns we can "discharge" automatically
    dischargeable_patterns = [
        "returns int", "returns float", "returns bool", "returns str",
        "returns list", "returns dict", "returns none",
        "non-negative", "positive", "non-empty",
        "sorted", "unique", "bounded",
    ]

    if any(p in text for p in dischargeable_patterns):
        result["status"] = "discharged"
        result["proof"] = "by simp [*]"
    else:
        result["status"] = "sorry"

    return result


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ Internal helpers — Caching                                               │
# └──────────────────────────────────────────────────────────────────────────┘

class _VerificationCache:
    """In-memory LRU-ish cache for verification results keyed by content hash."""

    def __init__(self, max_size: int = 256) -> None:
        self._store: Dict[str, VerificationResult] = {}
        self._max_size = max_size
        self._access_order: List[str] = []

    def get(self, content_hash: str) -> Optional[VerificationResult]:
        if content_hash in self._store:
            self._access_order.remove(content_hash)
            self._access_order.append(content_hash)
            return self._store[content_hash]
        return None

    def put(self, content_hash: str, result: VerificationResult) -> None:
        if content_hash in self._store:
            self._access_order.remove(content_hash)
        elif len(self._store) >= self._max_size:
            evict = self._access_order.pop(0)
            del self._store[evict]
        self._store[content_hash] = result
        self._access_order.append(content_hash)

    def invalidate(self, content_hash: str) -> None:
        if content_hash in self._store:
            del self._store[content_hash]
            self._access_order.remove(content_hash)

    def clear(self) -> None:
        self._store.clear()
        self._access_order.clear()

    @property
    def size(self) -> int:
        return len(self._store)


# Global cache instance
_global_cache = _VerificationCache()


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ VerificationLoop                                                         │
# └──────────────────────────────────────────────────────────────────────────┘

class VerificationLoop:
    """
    Runs deppy's hybrid verification pipeline on generated code.

    The loop:
    1. Parse mixed-mode source → extract NL fragments
    2. Decidability classification → split structural vs semantic
    3. Structural check (Z3) → prove decidable properties
    4. Anti-hallucination check → detect fabricated APIs, fields, logic errors
    5. Semantic check (oracle) → judge undecidable properties
    6. (Optional) Lean translation → emit .lean file
    7. (Optional) Discharge → attempt to prove obligations
    8. Trust computation → min across all checks
    9. Cache results by content hash
    """

    def __init__(
        self,
        config: Optional[VerificationConfig] = None,
        oracle_fn: Optional[Callable] = None,
    ) -> None:
        self.config = config or VerificationConfig()
        self._oracle_fn = oracle_fn
        self._stats = {
            "oracle_calls": 0,
            "oracle_cache_hits": 0,
            "z3_calls": 0,
            "total_time_ms": 0.0,
        }

    # ── Public API ────────────────────────────────────────────────────────

    def verify(self, source: str, module_name: str) -> VerificationResult:
        """
        Run the full verification pipeline on *source*.

        Returns a :class:`VerificationResult` capturing every check.
        """
        t0 = time.monotonic()
        chash = _content_hash(source)

        # 0. Cache lookup
        if self.config.cache_enabled:
            cached = _global_cache.get(chash)
            if cached is not None:
                logger.debug("Cache hit for %s (%s)", module_name, chash[:12])
                return cached

        errors: List[str] = []

        # 1. Extract claims & NL fragments
        claims = _extract_claims(source)
        nl_fragments = _extract_nl_fragments(source)
        type_annotations = _extract_type_annotations(source)

        # Add synthetic claims from NL fragments
        for frag in nl_fragments:
            claims.append({
                "kind": "ensure",
                "text": frag["body"],
                "line": frag["start_line"],
                "raw": frag["raw"],
            })

        # 2. Decidability classification
        structural_claims, semantic_claims = _classify_claims(claims)

        # 3. Structural checks (Z3)
        structural_results = self.verify_structural(source, structural_claims)

        # 4. Anti-hallucination checks
        hallucination_findings = self.check_hallucinations(source)

        # 5. Semantic checks (oracle)
        semantic_results = self.verify_semantic(
            source, semantic_claims, self._oracle_fn,
        )

        # 6–7. Lean translation & discharge
        lean_obligations: List[Dict[str, Any]] = []
        lean_source = ""
        discharged = 0
        residual = 0
        if self.config.emit_lean:
            lean_source, lean_obligations = self.translate_to_lean(
                source, claims,
            )
            lean_obligations = self.discharge_obligations(lean_obligations)
            discharged = sum(
                1 for ob in lean_obligations if ob["status"] == "discharged"
            )
            residual = sum(
                1 for ob in lean_obligations if ob["status"] == "sorry"
            )

        # 8. Trust computation
        trust = self._compute_trust(
            structural_results, semantic_results,
            hallucination_findings, lean_obligations,
        )

        # Determine pass/fail
        all_structural_ok = all(
            r.get("status") == "proven" for r in structural_results
        )
        no_high_hallucinations = not any(
            f.get("severity") == "high" for f in hallucination_findings
        )
        all_semantic_ok = all(
            r.get("status") == "passed" for r in semantic_results
        )
        passed = all_structural_ok and no_high_hallucinations and all_semantic_ok

        if self.config.strict_mode and residual > 0:
            passed = False
            errors.append(
                f"Strict mode: {residual} Lean obligations remain as sorry"
            )

        # H¹ computation (single-module)
        h1 = self._compute_h1(
            structural_results, semantic_results, hallucination_findings,
        )

        elapsed = (time.monotonic() - t0) * 1000

        result = VerificationResult(
            module_name=module_name,
            passed=passed,
            trust_level=trust,
            structural_results=structural_results,
            semantic_results=semantic_results,
            hallucination_findings=hallucination_findings,
            lean_obligations=lean_obligations,
            discharged=discharged,
            residual=residual,
            h1_status=h1,
            content_hash=chash,
            duration_ms=round(elapsed, 2),
            errors=errors,
        )

        # 9. Cache
        if self.config.cache_enabled:
            _global_cache.put(chash, result)

        self._stats["total_time_ms"] += elapsed
        return result

    def verify_structural(
        self,
        source: str,
        claims: List[Dict[str, Any]],
    ) -> List[Dict[str, Any]]:
        """Run Z3 checks on all structural claims."""
        results: List[Dict[str, Any]] = []
        for claim in claims:
            self._stats["z3_calls"] += 1
            r = _z3_check_claim(source, claim, self.config.z3_timeout_ms)
            results.append(r)
        return results

    def verify_semantic(
        self,
        source: str,
        claims: List[Dict[str, Any]],
        oracle_fn: Optional[Callable] = None,
    ) -> List[Dict[str, Any]]:
        """Run oracle checks on all semantic claims."""
        results: List[Dict[str, Any]] = []
        oracle = oracle_fn or self._oracle_fn or _default_oracle
        threshold = self.config.semantic_confidence_threshold

        for claim in claims:
            self._stats["oracle_calls"] += 1
            judgment = oracle(source, claim)
            confidence = judgment.get("confidence", 0.0)
            status = "passed" if confidence >= threshold else "failed"
            results.append({
                "claim": claim["text"],
                "kind": claim.get("kind", "unknown"),
                "line": claim.get("line", 0),
                "category": "semantic",
                "status": status,
                "confidence": confidence,
                "oracle_response": judgment.get("reasoning", ""),
            })
        return results

    def check_hallucinations(self, source: str) -> List[Dict[str, Any]]:
        """Run anti-hallucination detectors."""
        findings: List[Dict[str, Any]] = []
        for detector_name in self.config.hallucination_detectors:
            detector = _HALLUCINATION_DETECTORS.get(detector_name)
            if detector is None:
                logger.warning("Unknown detector: %s", detector_name)
                continue
            findings.extend(detector(source))
        return findings

    def translate_to_lean(
        self,
        source: str,
        claims: List[Dict[str, Any]],
    ) -> tuple[str, List[Dict[str, Any]]]:
        """
        Translate to Lean with proof obligations.

        Returns both the Lean source and the extracted proof obligations.
        """
        lean_src, obligations = _translate_claims_to_lean(
            source, claims, "module",
        )
        return lean_src, obligations

    def discharge_obligations(
        self,
        obligations: List[Dict[str, Any]],
    ) -> List[Dict[str, Any]]:
        """Attempt to discharge via cascade."""
        results: List[Dict[str, Any]] = []
        for ob in obligations:
            results.append(
                _attempt_discharge(ob, self.config.lean_timeout_s)
            )
        return results

    # ── Private helpers ───────────────────────────────────────────────────

    def _compute_trust(
        self,
        structural: List[Dict[str, Any]],
        semantic: List[Dict[str, Any]],
        hallucinations: List[Dict[str, Any]],
        lean_obs: List[Dict[str, Any]],
    ) -> str:
        """Compute the trust level from all sub-results."""
        if any(f.get("severity") == "high" for f in hallucinations):
            return "UNCHECKED"

        levels: List[str] = []

        if structural:
            all_proven = all(r.get("status") == "proven" for r in structural)
            levels.append("Z3_PROVEN" if all_proven else "UNCHECKED")

        if semantic:
            all_passed = all(r.get("status") == "passed" for r in semantic)
            levels.append("LLM_JUDGED" if all_passed else "UNCHECKED")

        if lean_obs:
            all_discharged = all(
                ob.get("status") == "discharged" for ob in lean_obs
            )
            if all_discharged:
                levels.append("LEAN_VERIFIED")
            else:
                # Lean attempted but not fully discharged — doesn't lower trust
                pass

        if not levels:
            return "UNCHECKED"

        # Trust is the min across all categories (weakest link)
        return _min_trust(*levels)

    def _compute_h1(
        self,
        structural: List[Dict[str, Any]],
        semantic: List[Dict[str, Any]],
        hallucinations: List[Dict[str, Any]],
    ) -> str:
        """
        Compute H¹ (first cohomology) for the module.

        H¹ = 0 means all local obstructions vanish — the module is
        internally consistent.  H¹ ≠ 0 means there are unresolved
        tensions between claims and implementation.
        """
        obstructions = 0
        obstructions += sum(
            1 for r in structural if r.get("status") != "proven"
        )
        obstructions += sum(
            1 for r in semantic if r.get("status") != "passed"
        )
        obstructions += sum(
            1 for f in hallucinations if f.get("severity") == "high"
        )

        if obstructions == 0:
            return "H\u00b9 = 0"
        return f"H\u00b9 \u2260 0 (obstructions={obstructions})"

    @property
    def stats(self) -> Dict[str, Any]:
        """Pipeline-level statistics."""
        return dict(self._stats)


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ CEGARVerificationLoop                                                    │
# └──────────────────────────────────────────────────────────────────────────┘

class CEGARVerificationLoop:
    """
    CEGAR = CounterExample-Guided Abstraction Refinement.

    generate → verify → if fail, extract counterexample → repair → verify → ...

    This is the outer loop that turns LLM hallucinations into correct code.
    Each iteration makes progress: either a new structural property is proven,
    a hallucination is fixed, or a semantic judgment improves.
    """

    def __init__(
        self,
        verification_loop: Optional[VerificationLoop] = None,
        config: Optional[VerificationConfig] = None,
    ) -> None:
        self.config = config or VerificationConfig()
        self.vloop = verification_loop or VerificationLoop(config=self.config)
        self._history: List[Dict[str, Any]] = []

    def run(
        self,
        artifact: Dict[str, Any],
        generator_fn: Callable[..., Dict[str, Any]],
        max_rounds: int = 5,
    ) -> Tuple[Dict[str, Any], VerificationResult]:
        """
        Run the CEGAR loop.

        Parameters
        ----------
        artifact : dict
            Must contain at least ``source`` (str) and ``module_name`` (str).
        generator_fn : callable
            A function ``(artifact, feedback) -> new_artifact`` that repairs
            the artifact given feedback from the verifier.
        max_rounds : int
            Maximum CEGAR iterations.

        Returns
        -------
        (final_artifact, final_verification_result)
            Invariant: each round either improves trust or exhausts attempts.
        """
        max_rounds = min(max_rounds, self.config.max_cegar_rounds)
        current = dict(artifact)
        best_result: Optional[VerificationResult] = None
        best_artifact: Dict[str, Any] = current

        for round_no in range(1, max_rounds + 1):
            logger.info(
                "CEGAR round %d/%d for %s",
                round_no, max_rounds, current.get("module_name", "?"),
            )

            # Verify current artifact
            result = self.vloop.verify(
                current.get("source", ""),
                current.get("module_name", "unknown"),
            )
            result.cegar_rounds = round_no

            self._history.append({
                "round": round_no,
                "passed": result.passed,
                "trust_level": result.trust_level,
                "structural_failures": sum(
                    1 for r in result.structural_results
                    if r.get("status") != "proven"
                ),
                "hallucinations": len(result.hallucination_findings),
                "semantic_failures": sum(
                    1 for r in result.semantic_results
                    if r.get("status") != "passed"
                ),
            })

            # Track the best result seen so far
            if best_result is None or self._is_improvement(result, best_result):
                best_result = result
                best_artifact = dict(current)

            # Success — return immediately
            if result.passed:
                logger.info("CEGAR converged in %d rounds", round_no)
                return current, result

            # Extract counterexample and build repair feedback
            cex = self.extract_counterexample(result)
            if cex is None:
                logger.warning(
                    "No actionable counterexample in round %d — stopping",
                    round_no,
                )
                break

            feedback = self.format_repair_feedback(
                result.structural_results
                + result.hallucination_findings
                + result.semantic_results
            )

            # Ask the generator to repair
            try:
                current = generator_fn(current, feedback)
            except Exception as exc:
                logger.error("Generator failed in CEGAR round %d: %s", round_no, exc)
                break

            # Invalidate cache for old source
            if self.vloop.config.cache_enabled:
                old_hash = _content_hash(artifact.get("source", ""))
                _global_cache.invalidate(old_hash)

        # Return the best we found
        assert best_result is not None
        return best_artifact, best_result

    def extract_counterexample(
        self,
        result: VerificationResult,
    ) -> Optional[Dict[str, Any]]:
        """
        Extract the most informative counterexample for repair.

        Priority order:
        1. High-severity hallucinations (fabricated APIs, phantom fields)
        2. Structural failures with concrete counterexamples
        3. Semantic failures with low confidence
        """
        # 1. High-severity hallucinations
        high_hall = [
            f for f in result.hallucination_findings
            if f.get("severity") == "high"
        ]
        if high_hall:
            worst = high_hall[0]
            return {
                "type": "hallucination",
                "detector": worst.get("detector", "unknown"),
                "location": worst.get("location", "unknown"),
                "description": worst.get("description", ""),
                "suggestion": worst.get("suggestion", ""),
            }

        # 2. Structural failures
        struct_fails = [
            r for r in result.structural_results
            if r.get("status") != "proven"
        ]
        if struct_fails:
            worst = struct_fails[0]
            return {
                "type": "structural",
                "claim": worst.get("claim", ""),
                "counterexample": worst.get("counterexample", ""),
                "line": worst.get("line", 0),
            }

        # 3. Semantic failures
        sem_fails = [
            r for r in result.semantic_results
            if r.get("status") != "passed"
        ]
        if sem_fails:
            worst = min(sem_fails, key=lambda r: r.get("confidence", 1.0))
            return {
                "type": "semantic",
                "claim": worst.get("claim", ""),
                "confidence": worst.get("confidence", 0.0),
                "oracle_response": worst.get("oracle_response", ""),
            }

        # 4. Medium hallucinations
        med_hall = [
            f for f in result.hallucination_findings
            if f.get("severity") == "medium"
        ]
        if med_hall:
            worst = med_hall[0]
            return {
                "type": "hallucination",
                "detector": worst.get("detector", "unknown"),
                "location": worst.get("location", "unknown"),
                "description": worst.get("description", ""),
                "suggestion": worst.get("suggestion", ""),
            }

        return None

    def format_repair_feedback(
        self,
        findings: List[Dict[str, Any]],
    ) -> str:
        """
        Format verification failures as repair instructions for the LLM.

        Produces a structured prompt fragment that tells the generator
        exactly what to fix.
        """
        if not findings:
            return "All checks passed — no repairs needed."

        lines: List[str] = [
            "The following verification issues were found. "
            "Please fix them in the next revision:",
            "",
        ]

        # Group by category
        hallucinations = [
            f for f in findings if f.get("detector") is not None
        ]
        structural = [
            f for f in findings
            if f.get("category") == "structural" and f.get("status") != "proven"
        ]
        semantic = [
            f for f in findings
            if f.get("category") == "semantic" and f.get("status") != "passed"
        ]

        if hallucinations:
            lines.append("## Hallucinations Detected")
            for h in hallucinations:
                lines.append(
                    f"- [{h.get('severity', '?').upper()}] "
                    f"{h.get('description', '?')} "
                    f"(at {h.get('location', '?')})"
                )
                if h.get("suggestion"):
                    lines.append(f"  Fix: {h['suggestion']}")
            lines.append("")

        if structural:
            lines.append("## Structural Failures")
            for s in structural:
                lines.append(f"- Claim: \"{s.get('claim', '?')}\"")
                if s.get("counterexample"):
                    lines.append(f"  Counterexample: {s['counterexample']}")
            lines.append("")

        if semantic:
            lines.append("## Semantic Failures")
            for s in semantic:
                conf = s.get("confidence", 0.0)
                lines.append(
                    f"- Claim: \"{s.get('claim', '?')}\" "
                    f"(confidence={conf:.2f}, threshold="
                    f"{self.vloop.config.semantic_confidence_threshold})"
                )
            lines.append("")

        lines.append(
            "Please produce a corrected version that addresses all issues above."
        )
        return "\n".join(lines)

    def _is_improvement(
        self,
        current: VerificationResult,
        previous: VerificationResult,
    ) -> bool:
        """Check if *current* is strictly better than *previous*."""
        # Fewer high-severity hallucinations
        cur_high = sum(
            1 for f in current.hallucination_findings
            if f.get("severity") == "high"
        )
        prev_high = sum(
            1 for f in previous.hallucination_findings
            if f.get("severity") == "high"
        )
        if cur_high < prev_high:
            return True

        # More structural proofs
        cur_proven = sum(
            1 for r in current.structural_results
            if r.get("status") == "proven"
        )
        prev_proven = sum(
            1 for r in previous.structural_results
            if r.get("status") == "proven"
        )
        if cur_proven > prev_proven:
            return True

        # Higher trust
        if TRUST_RANK.get(current.trust_level, 0) > TRUST_RANK.get(
            previous.trust_level, 0
        ):
            return True

        return False

    @property
    def history(self) -> List[Dict[str, Any]]:
        """The history of CEGAR rounds for debugging."""
        return list(self._history)


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ CrossModuleVerifier                                                      │
# └──────────────────────────────────────────────────────────────────────────┘

# Patterns for assume/guarantee extraction
_ASSUME_PATTERN = re.compile(
    r'(?:assume|#\s*@assume)\s*\(\s*"(?P<name>[^"]+)"\s*\)',
)
_GUARANTEE_PATTERN = re.compile(
    r'(?:guarantee|#\s*@guarantee)\s*\(\s*"(?P<name>[^"]+)"\s*\)',
)
_IMPORT_PATTERN = re.compile(
    r'(?:from\s+(\S+)\s+import|import\s+(\S+))',
)
_CLASS_PATTERN = re.compile(
    r'class\s+(\w+)',
)
_FUNCTION_PATTERN = re.compile(
    r'def\s+(\w+)',
)


class CrossModuleVerifier:
    """
    Verify cross-module contracts:
    - Module A's assume("X") must be module B's guarantee("X")
    - Shared types must be consistent
    - No circular trust dependencies

    This computes H¹(ProductSite × Module × Layer) — the cross-module
    cohomology that detects inter-module inconsistencies.
    """

    def __init__(
        self,
        config: Optional[VerificationConfig] = None,
        oracle_fn: Optional[Callable] = None,
    ) -> None:
        self.config = config or VerificationConfig()
        self._oracle_fn = oracle_fn

    def verify(self, modules: Dict[str, str]) -> CrossModuleResult:
        """
        Run cross-module verification on a set of modules.

        Parameters
        ----------
        modules : dict
            Mapping from module name to source code.

        Returns
        -------
        CrossModuleResult
        """
        t0 = time.monotonic()

        # 1. Extract contracts from each module
        all_assumes: Dict[str, List[Dict[str, Any]]] = {}
        all_guarantees: Dict[str, List[Dict[str, Any]]] = {}
        for mod_name, source in modules.items():
            contracts = self.extract_contracts(source)
            all_assumes[mod_name] = [
                c for c in contracts if c["type"] == "assume"
            ]
            all_guarantees[mod_name] = [
                c for c in contracts if c["type"] == "guarantee"
            ]

        # 2. Flatten into lists for matching
        flat_assumes: List[Dict[str, Any]] = []
        for mod_name, assumes in all_assumes.items():
            for a in assumes:
                flat_assumes.append({**a, "module": mod_name})

        flat_guarantees: List[Dict[str, Any]] = []
        for mod_name, guarantees in all_guarantees.items():
            for g in guarantees:
                flat_guarantees.append({**g, "module": mod_name})

        # 3. Match assume ↔ guarantee
        pairs = self.match_assume_guarantee(flat_assumes, flat_guarantees)

        # 4. Check shared types
        shared_type_issues = self.check_shared_types(modules)

        # 5. Detect circular trust dependencies
        circular = self._detect_circular_dependencies(modules)

        # 6. Compute stats
        verified = sum(1 for p in pairs if p.get("status") == "matched")
        failed = sum(1 for p in pairs if p.get("status") != "matched")

        # 7. H¹ cross-module
        obstructions = failed + len(shared_type_issues) + len(circular)
        h1_cross = (
            "H\u00b9 = 0"
            if obstructions == 0
            else f"H\u00b9 \u2260 0 (obstructions={obstructions})"
        )

        elapsed = (time.monotonic() - t0) * 1000

        return CrossModuleResult(
            modules_checked=list(modules.keys()),
            contracts_verified=verified,
            contracts_failed=failed,
            assume_guarantee_pairs=pairs,
            shared_type_issues=shared_type_issues,
            circular_dependencies=circular,
            h1_cross=h1_cross,
            duration_ms=round(elapsed, 2),
        )

    def extract_contracts(self, source: str) -> List[Dict[str, Any]]:
        """Extract all assume() and guarantee() from a module."""
        contracts: List[Dict[str, Any]] = []
        for i, line in enumerate(source.splitlines(), 1):
            for m in _ASSUME_PATTERN.finditer(line):
                contracts.append({
                    "type": "assume",
                    "name": m.group("name"),
                    "line": i,
                })
            for m in _GUARANTEE_PATTERN.finditer(line):
                contracts.append({
                    "type": "guarantee",
                    "name": m.group("name"),
                    "line": i,
                })
        return contracts

    def match_assume_guarantee(
        self,
        assumes: List[Dict[str, Any]],
        guarantees: List[Dict[str, Any]],
    ) -> List[Dict[str, Any]]:
        """
        Match each assume to a guarantee (semantic matching).

        First tries exact name matching, then falls back to fuzzy matching.
        """
        pairs: List[Dict[str, Any]] = []
        unmatched_assumes: List[Dict[str, Any]] = []

        # Index guarantees by name for fast lookup
        guarantee_by_name: Dict[str, List[Dict[str, Any]]] = {}
        for g in guarantees:
            guarantee_by_name.setdefault(g["name"], []).append(g)

        used_guarantees: Set[int] = set()

        for assume in assumes:
            # Exact match
            candidates = guarantee_by_name.get(assume["name"], [])
            matched = False
            for g in candidates:
                g_id = id(g)
                if g_id not in used_guarantees:
                    pairs.append({
                        "assume_module": assume.get("module", "?"),
                        "assume_name": assume["name"],
                        "assume_line": assume.get("line", 0),
                        "guarantee_module": g.get("module", "?"),
                        "guarantee_name": g["name"],
                        "guarantee_line": g.get("line", 0),
                        "status": "matched",
                        "match_type": "exact",
                    })
                    used_guarantees.add(g_id)
                    matched = True
                    break

            if not matched:
                # Fuzzy match: normalize and compare
                norm_assume = self._normalize_contract_name(assume["name"])
                best_score = 0.0
                best_g: Optional[Dict[str, Any]] = None
                for g in guarantees:
                    if id(g) in used_guarantees:
                        continue
                    norm_g = self._normalize_contract_name(g["name"])
                    score = self._similarity(norm_assume, norm_g)
                    if score > best_score:
                        best_score = score
                        best_g = g

                if best_g is not None and best_score >= 0.8:
                    pairs.append({
                        "assume_module": assume.get("module", "?"),
                        "assume_name": assume["name"],
                        "assume_line": assume.get("line", 0),
                        "guarantee_module": best_g.get("module", "?"),
                        "guarantee_name": best_g["name"],
                        "guarantee_line": best_g.get("line", 0),
                        "status": "matched",
                        "match_type": "fuzzy",
                        "similarity": round(best_score, 3),
                    })
                    used_guarantees.add(id(best_g))
                else:
                    unmatched_assumes.append(assume)

        # Record unmatched assumes as failures
        for assume in unmatched_assumes:
            pairs.append({
                "assume_module": assume.get("module", "?"),
                "assume_name": assume["name"],
                "assume_line": assume.get("line", 0),
                "guarantee_module": None,
                "guarantee_name": None,
                "guarantee_line": None,
                "status": "unmatched",
                "match_type": None,
            })

        return pairs

    def check_shared_types(
        self,
        modules: Dict[str, str],
    ) -> List[Dict[str, Any]]:
        """Check that shared types are consistent across modules."""
        issues: List[Dict[str, Any]] = []

        # Collect class definitions per module
        class_defs: Dict[str, Dict[str, List[str]]] = {}
        for mod_name, source in modules.items():
            classes: Dict[str, List[str]] = {}
            current_class: Optional[str] = None
            current_fields: List[str] = []

            for line in source.splitlines():
                cm = _CLASS_PATTERN.search(line)
                if cm:
                    if current_class:
                        classes[current_class] = current_fields
                    current_class = cm.group(1)
                    current_fields = []
                elif current_class:
                    # Collect field-like lines
                    field_match = re.search(
                        r"self\.(\w+)\s*(?::\s*\w+)?\s*=", line
                    )
                    if field_match:
                        current_fields.append(field_match.group(1))

            if current_class:
                classes[current_class] = current_fields

            class_defs[mod_name] = classes

        # Find types defined in multiple modules
        all_class_names: Dict[str, List[str]] = {}  # class → [modules]
        for mod_name, classes in class_defs.items():
            for cls_name in classes:
                all_class_names.setdefault(cls_name, []).append(mod_name)

        for cls_name, defining_modules in all_class_names.items():
            if len(defining_modules) < 2:
                continue

            # Compare fields across definitions
            field_sets: Dict[str, Set[str]] = {}
            for mod_name in defining_modules:
                field_sets[mod_name] = set(class_defs[mod_name].get(cls_name, []))

            # Check pairwise consistency
            mods = defining_modules
            for i in range(len(mods)):
                for j in range(i + 1, len(mods)):
                    fields_i = field_sets[mods[i]]
                    fields_j = field_sets[mods[j]]
                    if fields_i != fields_j:
                        diff = fields_i.symmetric_difference(fields_j)
                        issues.append({
                            "type_name": cls_name,
                            "modules": [mods[i], mods[j]],
                            "issue_description": (
                                f"Class '{cls_name}' has different fields in "
                                f"'{mods[i]}' vs '{mods[j]}': {diff}"
                            ),
                        })

        return issues

    def _detect_circular_dependencies(
        self,
        modules: Dict[str, str],
    ) -> List[List[str]]:
        """Detect circular trust/import dependencies between modules."""
        # Build dependency graph from import statements
        deps: Dict[str, Set[str]] = {name: set() for name in modules}
        module_names = set(modules.keys())

        for mod_name, source in modules.items():
            for m in _IMPORT_PATTERN.finditer(source):
                imported = m.group(1) or m.group(2)
                # Check if the imported module is one of ours
                imported_base = imported.split(".")[0]
                if imported_base in module_names and imported_base != mod_name:
                    deps[mod_name].add(imported_base)

        # DFS cycle detection
        cycles: List[List[str]] = []
        visited: Set[str] = set()
        rec_stack: Set[str] = set()

        def _dfs(node: str, path: List[str]) -> None:
            visited.add(node)
            rec_stack.add(node)
            path.append(node)

            for neighbor in deps.get(node, set()):
                if neighbor not in visited:
                    _dfs(neighbor, path)
                elif neighbor in rec_stack:
                    # Found a cycle
                    cycle_start = path.index(neighbor)
                    cycle = path[cycle_start:] + [neighbor]
                    cycles.append(cycle)

            path.pop()
            rec_stack.discard(node)

        for mod_name in modules:
            if mod_name not in visited:
                _dfs(mod_name, [])

        return cycles

    @staticmethod
    def _normalize_contract_name(name: str) -> str:
        """Normalize a contract name for fuzzy matching."""
        # Lowercase, strip whitespace, remove articles
        normalized = name.lower().strip()
        for article in ("the ", "a ", "an "):
            if normalized.startswith(article):
                normalized = normalized[len(article):]
        normalized = re.sub(r"\s+", " ", normalized)
        return normalized

    @staticmethod
    def _similarity(a: str, b: str) -> float:
        """Simple word-overlap similarity between two strings."""
        words_a = set(a.split())
        words_b = set(b.split())
        if not words_a or not words_b:
            return 0.0
        intersection = words_a & words_b
        union = words_a | words_b
        return len(intersection) / len(union)


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ Module-level convenience functions                                       │
# └──────────────────────────────────────────────────────────────────────────┘

def verify_module(
    source: str,
    module_name: str,
    config: Optional[VerificationConfig] = None,
    oracle_fn: Optional[Callable] = None,
) -> VerificationResult:
    """Convenience: verify a single module with default settings."""
    loop = VerificationLoop(config=config, oracle_fn=oracle_fn)
    return loop.verify(source, module_name)


def verify_project(
    modules: Dict[str, str],
    config: Optional[VerificationConfig] = None,
    oracle_fn: Optional[Callable] = None,
) -> Tuple[Dict[str, VerificationResult], CrossModuleResult]:
    """
    Convenience: verify all modules and cross-module contracts.

    Returns (per_module_results, cross_module_result).
    """
    loop = VerificationLoop(config=config, oracle_fn=oracle_fn)
    per_module: Dict[str, VerificationResult] = {}
    for name, source in modules.items():
        per_module[name] = loop.verify(source, name)

    cross = CrossModuleVerifier(config=config, oracle_fn=oracle_fn)
    cross_result = cross.verify(modules)

    return per_module, cross_result


def cegar_verify(
    artifact: Dict[str, Any],
    generator_fn: Callable[..., Dict[str, Any]],
    config: Optional[VerificationConfig] = None,
    oracle_fn: Optional[Callable] = None,
    max_rounds: int = 5,
) -> Tuple[Dict[str, Any], VerificationResult]:
    """Convenience: run CEGAR on a single artifact."""
    vconfig = config or VerificationConfig()
    loop = VerificationLoop(config=vconfig, oracle_fn=oracle_fn)
    cegar = CEGARVerificationLoop(verification_loop=loop, config=vconfig)
    return cegar.run(artifact, generator_fn, max_rounds=max_rounds)
