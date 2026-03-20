"""
Intent oracle for deppy's autonomous agent.

Parses natural-language prompts into structured intent specifications,
detects ambiguities, and refines specifications via CEGAR when the
generated code doesn't match the original intent.

Classes
-------
IntentOracle
    Main oracle: ``parse_intent(prompt) → IntentSpec``
IntentSpec
    Structured intent with requirements, constraints, priorities.
AmbiguityDetector
    Finds ambiguous or underspecified parts of the NL spec.
IntentRefiner
    CEGAR on intent: if code doesn't match, refine the spec.
"""
from __future__ import annotations

import copy
import hashlib
import json
import logging
import os
import re
import textwrap
import time
from collections import OrderedDict
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Set,
    Sequence,
    Tuple,
    Union,
)

logger = logging.getLogger(__name__)


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  Domain taxonomy                                                        ║
# ╚══════════════════════════════════════════════════════════════════════════╝

KNOWN_DOMAINS: Dict[str, List[str]] = {
    "web": [
        "http", "api", "rest", "graphql", "server", "endpoint",
        "route", "request", "response", "html", "css", "frontend",
        "backend", "middleware", "cors", "websocket", "url",
    ],
    "finance": [
        "trading", "stock", "portfolio", "price", "market", "order",
        "buy", "sell", "exchange", "ticker", "dividend", "risk",
        "hedge", "option", "bond", "interest", "bank", "payment",
    ],
    "data": [
        "database", "sql", "csv", "json", "parse", "etl", "pipeline",
        "transform", "schema", "query", "table", "record", "column",
        "index", "migrate", "orm", "nosql", "redis", "cache",
    ],
    "ml": [
        "model", "train", "predict", "neural", "classification",
        "regression", "feature", "dataset", "accuracy", "loss",
        "epoch", "batch", "tensor", "embedding", "transformer",
    ],
    "cli": [
        "command", "argument", "flag", "terminal", "shell", "script",
        "option", "subcommand", "prompt", "interactive",
    ],
    "game": [
        "game", "player", "score", "level", "sprite", "render",
        "collision", "physics", "input", "loop", "tick", "entity",
    ],
    "crypto": [
        "encrypt", "decrypt", "hash", "sign", "verify", "key",
        "certificate", "token", "auth", "password", "secret",
    ],
    "system": [
        "file", "process", "thread", "socket", "network", "os",
        "daemon", "service", "monitor", "log", "config", "deploy",
    ],
}

# Module archetypes discovered from common project patterns
MODULE_ARCHETYPES: Dict[str, Dict[str, Any]] = {
    "api_server": {
        "modules": ["models", "routes", "middleware", "config", "main"],
        "dependencies": {"routes": ["models", "middleware"], "main": ["routes", "config"]},
    },
    "data_pipeline": {
        "modules": ["source", "transform", "validate", "sink", "orchestrate"],
        "dependencies": {
            "transform": ["source"],
            "validate": ["transform"],
            "sink": ["validate"],
            "orchestrate": ["source", "transform", "validate", "sink"],
        },
    },
    "cli_tool": {
        "modules": ["cli", "core", "config", "output"],
        "dependencies": {"cli": ["core", "config", "output"]},
    },
    "trading_system": {
        "modules": ["market_data", "strategy", "execution", "risk", "portfolio", "main"],
        "dependencies": {
            "strategy": ["market_data"],
            "execution": ["strategy", "risk"],
            "portfolio": ["execution", "market_data"],
            "main": ["market_data", "strategy", "execution", "risk", "portfolio"],
        },
    },
    "ml_pipeline": {
        "modules": ["data_loader", "features", "model", "train", "evaluate", "serve"],
        "dependencies": {
            "features": ["data_loader"],
            "model": ["features"],
            "train": ["model", "data_loader"],
            "evaluate": ["model", "train"],
            "serve": ["model"],
        },
    },
}


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  Requirement / Constraint / Priority                                    ║
# ╚══════════════════════════════════════════════════════════════════════════╝

@dataclass
class Requirement:
    """A single functional or non-functional requirement."""

    id: str = ""
    text: str = ""
    kind: str = "functional"  # functional | non_functional | constraint
    priority: str = "medium"  # high | medium | low
    module_hint: str = ""
    verifiable: bool = True
    source: str = "parsed"  # parsed | inferred | refined

    def to_dict(self) -> Dict[str, Any]:
        return {
            "id": self.id,
            "text": self.text,
            "kind": self.kind,
            "priority": self.priority,
            "module_hint": self.module_hint,
            "verifiable": self.verifiable,
            "source": self.source,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "Requirement":
        return cls(**{k: v for k, v in d.items() if k in cls.__dataclass_fields__})


@dataclass
class Constraint:
    """A constraint on the generated project."""

    text: str = ""
    kind: str = "hard"  # hard | soft | preference
    scope: str = "project"  # project | module | function
    target: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {"text": self.text, "kind": self.kind, "scope": self.scope, "target": self.target}


@dataclass
class Priority:
    """An explicit priority from the user."""

    text: str = ""
    weight: float = 1.0

    def to_dict(self) -> Dict[str, Any]:
        return {"text": self.text, "weight": self.weight}


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  ModuleSpec                                                             ║
# ╚══════════════════════════════════════════════════════════════════════════╝

@dataclass
class ModuleSpec:
    """Specification for a single module within the project."""

    name: str = ""
    description: str = ""
    responsibilities: List[str] = field(default_factory=list)
    dependencies: List[str] = field(default_factory=list)
    public_api: List[Dict[str, Any]] = field(default_factory=list)
    constraints: List[str] = field(default_factory=list)
    patterns: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "description": self.description,
            "responsibilities": self.responsibilities,
            "dependencies": self.dependencies,
            "public_api": self.public_api,
            "constraints": self.constraints,
            "patterns": self.patterns,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "ModuleSpec":
        return cls(**{k: v for k, v in d.items() if k in cls.__dataclass_fields__})


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  IntentSpec — structured intent                                         ║
# ╚══════════════════════════════════════════════════════════════════════════╝

@dataclass
class IntentSpec:
    """
    Structured intent parsed from a natural-language prompt.

    This is the central data structure produced by the IntentOracle
    and consumed by the rest of the orchestrator pipeline.
    """

    project_name: str = ""
    domain: str = "general"
    description: str = ""
    modules: List[ModuleSpec] = field(default_factory=list)
    requirements: List[Requirement] = field(default_factory=list)
    constraints: List[Constraint] = field(default_factory=list)
    priorities: List[Priority] = field(default_factory=list)
    ambiguities: List[Dict[str, Any]] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)
    raw_prompt: str = ""
    confidence: float = 0.0
    revision: int = 0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "project_name": self.project_name,
            "domain": self.domain,
            "description": self.description,
            "modules": [m.to_dict() for m in self.modules],
            "requirements": [r.to_dict() for r in self.requirements],
            "constraints": [c.to_dict() for c in self.constraints],
            "priorities": [p.to_dict() for p in self.priorities],
            "ambiguities": self.ambiguities,
            "metadata": self.metadata,
            "confidence": self.confidence,
            "revision": self.revision,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "IntentSpec":
        spec = cls()
        spec.project_name = d.get("project_name", "")
        spec.domain = d.get("domain", "general")
        spec.description = d.get("description", "")
        spec.confidence = d.get("confidence", 0.0)
        spec.revision = d.get("revision", 0)
        spec.ambiguities = d.get("ambiguities", [])
        spec.metadata = d.get("metadata", {})

        for m in d.get("modules", []):
            if isinstance(m, dict):
                spec.modules.append(ModuleSpec.from_dict(m))
            elif isinstance(m, ModuleSpec):
                spec.modules.append(m)

        for r in d.get("requirements", []):
            if isinstance(r, dict):
                spec.requirements.append(Requirement.from_dict(r))
            elif isinstance(r, Requirement):
                spec.requirements.append(r)

        for c in d.get("constraints", []):
            if isinstance(c, dict):
                spec.constraints.append(Constraint(**{
                    k: v for k, v in c.items() if k in Constraint.__dataclass_fields__
                }))
            elif isinstance(c, Constraint):
                spec.constraints.append(c)

        for p in d.get("priorities", []):
            if isinstance(p, dict):
                spec.priorities.append(Priority(**{
                    k: v for k, v in p.items() if k in Priority.__dataclass_fields__
                }))
            elif isinstance(p, Priority):
                spec.priorities.append(p)

        return spec

    def module_names(self) -> List[str]:
        return [m.name for m in self.modules]

    def high_priority_requirements(self) -> List[Requirement]:
        return [r for r in self.requirements if r.priority == "high"]

    def hard_constraints(self) -> List[Constraint]:
        return [c for c in self.constraints if c.kind == "hard"]

    def has_ambiguities(self) -> bool:
        return len(self.ambiguities) > 0

    def merge(self, other: "IntentSpec") -> "IntentSpec":
        """Merge another spec into this one (for refinement)."""
        merged = copy.deepcopy(self)
        merged.revision += 1

        seen_mods = {m.name for m in merged.modules}
        for m in other.modules:
            if m.name not in seen_mods:
                merged.modules.append(copy.deepcopy(m))

        seen_reqs = {r.id for r in merged.requirements if r.id}
        for r in other.requirements:
            if r.id and r.id not in seen_reqs:
                merged.requirements.append(copy.deepcopy(r))
            elif not r.id:
                merged.requirements.append(copy.deepcopy(r))

        merged.constraints.extend(copy.deepcopy(other.constraints))
        merged.priorities.extend(copy.deepcopy(other.priorities))

        if other.ambiguities:
            merged.ambiguities = other.ambiguities

        merged.confidence = max(merged.confidence, other.confidence)
        return merged

    def summary(self) -> str:
        lines = [
            f"Project: {self.project_name} ({self.domain})",
            f"Description: {self.description[:120]}...",
            f"Modules: {', '.join(self.module_names())}",
            f"Requirements: {len(self.requirements)}",
            f"Constraints: {len(self.constraints)}",
            f"Confidence: {self.confidence:.2f}",
            f"Revision: {self.revision}",
        ]
        if self.ambiguities:
            lines.append(f"Ambiguities: {len(self.ambiguities)}")
        return "\n".join(lines)


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  Ambiguity                                                              ║
# ╚══════════════════════════════════════════════════════════════════════════╝

@dataclass
class Ambiguity:
    """An ambiguous or underspecified aspect of the intent."""

    text: str = ""
    kind: str = "vague"  # vague | missing | contradictory | multi_interpretation
    location: str = ""
    suggestions: List[str] = field(default_factory=list)
    severity: str = "medium"  # low | medium | high
    resolved: bool = False
    resolution: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "text": self.text,
            "kind": self.kind,
            "location": self.location,
            "suggestions": self.suggestions,
            "severity": self.severity,
            "resolved": self.resolved,
            "resolution": self.resolution,
        }


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  AmbiguityDetector                                                      ║
# ╚══════════════════════════════════════════════════════════════════════════╝

class AmbiguityDetector:
    """
    Detects ambiguous, vague, or underspecified parts of an NL prompt
    or IntentSpec.

    Detection strategies:
      - Vague language detection (hedging, generics)
      - Missing critical spec elements
      - Contradictory requirements
      - Multiple valid interpretations
    """

    # Words / phrases that signal vagueness
    VAGUE_MARKERS: List[str] = [
        "somehow", "maybe", "perhaps", "kind of", "sort of",
        "something like", "etc", "and so on", "various",
        "appropriate", "suitable", "proper", "good",
        "nice", "cool", "awesome", "interesting",
        "simple", "easy", "basic",
    ]

    # Critical elements that should be specified
    CRITICAL_ELEMENTS: List[str] = [
        "persistence",
        "authentication",
        "error_handling",
        "input_validation",
        "concurrency",
        "logging",
    ]

    def __init__(
        self,
        llm_fn: Optional[Callable[..., str]] = None,
        strict: bool = False,
    ) -> None:
        self._llm_fn = llm_fn
        self._strict = strict

    def detect(self, prompt: str, spec: Optional[IntentSpec] = None) -> List[Ambiguity]:
        """Detect ambiguities in the prompt and/or spec."""
        ambiguities: List[Ambiguity] = []

        ambiguities.extend(self._detect_vague_language(prompt))
        ambiguities.extend(self._detect_missing_elements(prompt, spec))
        if spec:
            ambiguities.extend(self._detect_contradictions(spec))
            ambiguities.extend(self._detect_multi_interpretations(prompt, spec))

        if self._llm_fn and self._strict:
            ambiguities.extend(self._detect_with_llm(prompt, spec))

        return ambiguities

    def _detect_vague_language(self, prompt: str) -> List[Ambiguity]:
        """Find vague language markers in the prompt."""
        results: List[Ambiguity] = []
        prompt_lower = prompt.lower()
        for marker in self.VAGUE_MARKERS:
            idx = prompt_lower.find(marker)
            if idx >= 0:
                context_start = max(0, idx - 30)
                context_end = min(len(prompt), idx + len(marker) + 30)
                context = prompt[context_start:context_end]
                results.append(Ambiguity(
                    text=f'Vague language: "{marker}"',
                    kind="vague",
                    location=f"char {idx}",
                    suggestions=[
                        f"Replace '{marker}' with a specific requirement",
                        "Provide concrete criteria or examples",
                    ],
                    severity="low" if marker in ("simple", "easy", "basic") else "medium",
                ))
        return results

    def _detect_missing_elements(
        self, prompt: str, spec: Optional[IntentSpec]
    ) -> List[Ambiguity]:
        """Check for critical missing spec elements."""
        results: List[Ambiguity] = []
        prompt_lower = prompt.lower()

        element_keywords: Dict[str, List[str]] = {
            "persistence": ["database", "storage", "save", "persist", "store", "file", "db"],
            "authentication": ["auth", "login", "user", "password", "session", "token", "jwt"],
            "error_handling": ["error", "exception", "fail", "catch", "handle", "retry"],
            "input_validation": ["validate", "check", "sanitize", "input", "form", "parse"],
            "concurrency": ["async", "thread", "parallel", "concurrent", "await", "lock"],
            "logging": ["log", "monitor", "trace", "debug", "audit"],
        }

        # Check which elements are implicitly relevant but not mentioned
        domain_implies: Dict[str, List[str]] = {
            "web": ["authentication", "error_handling", "input_validation", "logging"],
            "finance": ["persistence", "error_handling", "input_validation", "logging"],
            "data": ["persistence", "error_handling", "input_validation"],
            "system": ["error_handling", "logging", "concurrency"],
        }

        detected_domain = _detect_domain(prompt)
        implied = domain_implies.get(detected_domain, ["error_handling"])

        for element in implied:
            keywords = element_keywords.get(element, [])
            if not any(kw in prompt_lower for kw in keywords):
                results.append(Ambiguity(
                    text=f"Missing specification for: {element}",
                    kind="missing",
                    location="prompt",
                    suggestions=[
                        f"Specify {element} requirements explicitly",
                        f"Should {element} be included? If so, what approach?",
                    ],
                    severity="medium" if element in ("persistence", "authentication") else "low",
                ))

        return results

    def _detect_contradictions(self, spec: IntentSpec) -> List[Ambiguity]:
        """Check for contradictory requirements in the spec."""
        results: List[Ambiguity] = []
        reqs_text = [r.text.lower() for r in spec.requirements]

        contradiction_pairs = [
            ("real-time", "batch"),
            ("synchronous", "asynchronous"),
            ("simple", "comprehensive"),
            ("minimal", "full-featured"),
            ("lightweight", "enterprise"),
        ]

        for w1, w2 in contradiction_pairs:
            has_w1 = any(w1 in t for t in reqs_text)
            has_w2 = any(w2 in t for t in reqs_text)
            if has_w1 and has_w2:
                results.append(Ambiguity(
                    text=f"Potentially contradictory: '{w1}' vs '{w2}'",
                    kind="contradictory",
                    location="requirements",
                    suggestions=[
                        f"Clarify whether you need {w1} or {w2}, or both in different contexts",
                    ],
                    severity="high",
                ))

        return results

    def _detect_multi_interpretations(
        self, prompt: str, spec: IntentSpec
    ) -> List[Ambiguity]:
        """Detect parts of the prompt that have multiple valid readings."""
        results: List[Ambiguity] = []

        # "app" could mean web app, desktop app, mobile app, CLI app
        if re.search(r"\bapp\b", prompt, re.IGNORECASE):
            if not any(
                kw in prompt.lower()
                for kw in ["web", "desktop", "mobile", "cli", "terminal", "api", "server"]
            ):
                results.append(Ambiguity(
                    text="Ambiguous: 'app' — web, desktop, mobile, or CLI?",
                    kind="multi_interpretation",
                    location="prompt",
                    suggestions=["Specify: web app, CLI tool, desktop app, or API server"],
                    severity="medium",
                ))

        # "database" could mean SQL, NoSQL, in-memory, file-based
        if re.search(r"\bdatabase\b", prompt, re.IGNORECASE):
            if not any(
                kw in prompt.lower()
                for kw in ["sql", "postgres", "mysql", "sqlite", "mongo", "redis", "in-memory"]
            ):
                results.append(Ambiguity(
                    text="Ambiguous: 'database' — which type?",
                    kind="multi_interpretation",
                    location="prompt",
                    suggestions=["Specify: SQLite, PostgreSQL, MongoDB, or in-memory"],
                    severity="low",
                ))

        return results

    def _detect_with_llm(
        self, prompt: str, spec: Optional[IntentSpec]
    ) -> List[Ambiguity]:
        """Use LLM to detect subtle ambiguities."""
        if not self._llm_fn:
            return []

        system = (
            "You are a requirements analyst. Identify ambiguities, "
            "underspecifications, and potential misinterpretations in this "
            "software specification. Return a JSON array of objects with "
            "keys: text, kind (vague|missing|contradictory|multi_interpretation), "
            "severity (low|medium|high), suggestions (array of strings)."
        )
        spec_text = spec.summary() if spec else ""
        query = f"{system}\n\nPrompt: {prompt}\n\nParsed spec:\n{spec_text}"

        try:
            raw = self._llm_fn(query)
            parsed = _safe_json_parse(raw, fallback=[])
            if isinstance(parsed, list):
                results: List[Ambiguity] = []
                for item in parsed:
                    if isinstance(item, dict):
                        results.append(Ambiguity(
                            text=item.get("text", ""),
                            kind=item.get("kind", "vague"),
                            severity=item.get("severity", "medium"),
                            suggestions=item.get("suggestions", []),
                            location="llm_detected",
                        ))
                return results
        except Exception as exc:
            logger.debug("LLM ambiguity detection failed: %s", exc)

        return []


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  IntentRefiner — CEGAR on intent                                        ║
# ╚══════════════════════════════════════════════════════════════════════════╝

class IntentRefiner:
    """
    CEGAR loop on intent specifications.

    If the generated code doesn't match the original intent, the refiner
    extracts a counterexample (the mismatch) and refines the spec to be
    more precise, then re-generates.

    Cycle::

        spec → generate → verify_against_intent → mismatch? → refine → spec'
    """

    def __init__(
        self,
        llm_fn: Optional[Callable[..., str]] = None,
        max_refinements: int = 3,
    ) -> None:
        self._llm_fn = llm_fn
        self._max_refinements = max_refinements
        self._history: List[Dict[str, Any]] = []

    def refine(
        self,
        spec: IntentSpec,
        code_summary: str,
        mismatches: List[Dict[str, Any]],
    ) -> IntentSpec:
        """
        Refine the intent spec based on mismatches between code and intent.

        Parameters
        ----------
        spec : IntentSpec
            Current intent specification.
        code_summary : str
            Summary of the generated code.
        mismatches : list
            Detected mismatches between code and intent.

        Returns
        -------
        IntentSpec
            Refined specification with more precise requirements.
        """
        if not mismatches:
            return spec

        self._history.append({
            "revision": spec.revision,
            "mismatches": mismatches,
            "timestamp": time.time(),
        })

        refined = copy.deepcopy(spec)
        refined.revision += 1

        for mm in mismatches:
            kind = mm.get("kind", "missing")
            detail = mm.get("detail", "")
            suggestion = mm.get("suggestion", "")

            if kind == "missing_requirement":
                refined.requirements.append(Requirement(
                    id=f"refined_{refined.revision}_{len(refined.requirements)}",
                    text=detail or suggestion,
                    kind="functional",
                    priority="high",
                    source="refined",
                ))
            elif kind == "wrong_behavior":
                refined.constraints.append(Constraint(
                    text=f"Must NOT: {detail}. Instead: {suggestion}",
                    kind="hard",
                    scope="project",
                ))
            elif kind == "missing_module":
                mod_name = mm.get("module_name", f"module_{len(refined.modules)}")
                refined.modules.append(ModuleSpec(
                    name=mod_name,
                    description=detail,
                    responsibilities=[detail],
                ))
            elif kind == "wrong_type":
                refined.constraints.append(Constraint(
                    text=f"Type constraint: {detail}",
                    kind="hard",
                    scope="function",
                    target=mm.get("target", ""),
                ))

        # Use LLM for deeper refinement
        if self._llm_fn and len(mismatches) > 2:
            llm_refinements = self._refine_with_llm(spec, code_summary, mismatches)
            refined = refined.merge(llm_refinements)

        # Clear old ambiguities — the refinement may resolve them
        refined.ambiguities = [
            a for a in refined.ambiguities
            if not any(
                mm.get("resolves_ambiguity") == a.get("text")
                for mm in mismatches
            )
        ]

        refined.confidence = min(1.0, spec.confidence + 0.1 * len(mismatches))
        return refined

    def validate_against_code(
        self,
        spec: IntentSpec,
        code_summary: str,
    ) -> Tuple[bool, List[Dict[str, Any]]]:
        """
        Validate whether the code summary matches the intent spec.

        Returns (valid, mismatches).
        """
        mismatches: List[Dict[str, Any]] = []

        # Check each requirement against code summary
        code_lower = code_summary.lower()
        for req in spec.requirements:
            keywords = _extract_keywords(req.text)
            if keywords and not any(kw in code_lower for kw in keywords):
                mismatches.append({
                    "kind": "missing_requirement",
                    "detail": f"Requirement not reflected in code: {req.text}",
                    "requirement_id": req.id,
                })

        # Check each module exists
        for mod in spec.modules:
            if mod.name.lower() not in code_lower and mod.name.replace("_", " ") not in code_lower:
                mismatches.append({
                    "kind": "missing_module",
                    "module_name": mod.name,
                    "detail": f"Module '{mod.name}' not found in generated code",
                })

        # Check hard constraints
        for constraint in spec.hard_constraints():
            keywords = _extract_keywords(constraint.text)
            if keywords and not any(kw in code_lower for kw in keywords):
                mismatches.append({
                    "kind": "wrong_behavior",
                    "detail": f"Constraint not met: {constraint.text}",
                })

        # Use LLM for deeper validation
        if self._llm_fn and not mismatches:
            llm_mismatches = self._validate_with_llm(spec, code_summary)
            mismatches.extend(llm_mismatches)

        valid = len(mismatches) == 0
        return valid, mismatches

    def _refine_with_llm(
        self,
        spec: IntentSpec,
        code_summary: str,
        mismatches: List[Dict[str, Any]],
    ) -> IntentSpec:
        """Use LLM to suggest refinements."""
        if not self._llm_fn:
            return IntentSpec()

        system = (
            "You are a requirements analyst. Given an intent specification, "
            "generated code summary, and detected mismatches, produce a "
            "refined specification as JSON with keys: requirements (array), "
            "constraints (array), modules (array of {name, description})."
        )
        prompt = (
            f"{system}\n\n"
            f"Current spec:\n{spec.summary()}\n\n"
            f"Code summary:\n{code_summary}\n\n"
            f"Mismatches:\n{json.dumps(mismatches, indent=2)}"
        )

        try:
            raw = self._llm_fn(prompt)
            parsed = _safe_json_parse(raw, fallback={})
            return IntentSpec.from_dict(parsed)
        except Exception as exc:
            logger.debug("LLM refinement failed: %s", exc)
            return IntentSpec()

    def _validate_with_llm(
        self,
        spec: IntentSpec,
        code_summary: str,
    ) -> List[Dict[str, Any]]:
        """Use LLM to find mismatches between spec and code."""
        if not self._llm_fn:
            return []

        system = (
            "You are a code reviewer. Compare the intent specification "
            "with the generated code summary. Find mismatches. Return a "
            "JSON array of {kind, detail, suggestion}. "
            "kind is one of: missing_requirement, wrong_behavior, "
            "missing_module, wrong_type."
        )
        prompt = (
            f"{system}\n\n"
            f"Intent spec:\n{spec.summary()}\n\n"
            f"Code summary:\n{code_summary}"
        )

        try:
            raw = self._llm_fn(prompt)
            parsed = _safe_json_parse(raw, fallback=[])
            if isinstance(parsed, list):
                return [m for m in parsed if isinstance(m, dict)]
        except Exception as exc:
            logger.debug("LLM validation failed: %s", exc)

        return []

    @property
    def history(self) -> List[Dict[str, Any]]:
        return list(self._history)


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  IntentOracle — main class                                              ║
# ╚══════════════════════════════════════════════════════════════════════════╝

class IntentOracle:
    """
    Oracle interface for intent understanding.

    Parses natural-language prompts into structured :class:`IntentSpec`
    objects, detects ambiguities, and iteratively refines specifications.

    Usage::

        oracle = IntentOracle(llm_fn=my_llm)
        spec = oracle.parse_intent("write me a trading app")
        if spec.has_ambiguities():
            spec = oracle.clarify(spec, spec.ambiguities[0])
        valid = oracle.validate(spec, code_summary)
    """

    def __init__(
        self,
        llm_fn: Optional[Callable[..., str]] = None,
        strict: bool = False,
        max_refinements: int = 3,
    ) -> None:
        self._llm_fn = llm_fn
        self._strict = strict
        self._ambiguity_detector = AmbiguityDetector(llm_fn=llm_fn, strict=strict)
        self._refiner = IntentRefiner(llm_fn=llm_fn, max_refinements=max_refinements)
        self._parse_cache: Dict[str, IntentSpec] = {}

    # ------------------------------------------------------------------
    # Core API
    # ------------------------------------------------------------------

    def parse_intent(self, prompt: str) -> IntentSpec:
        """
        Parse a natural-language prompt into a structured IntentSpec.

        Performs:
          1. Domain detection
          2. Keyword extraction
          3. Module decomposition
          4. Requirement extraction
          5. Constraint extraction
          6. Ambiguity detection
        """
        cache_key = hashlib.sha256(prompt.encode()).hexdigest()[:16]
        if cache_key in self._parse_cache:
            return copy.deepcopy(self._parse_cache[cache_key])

        # Step 1: Domain detection
        domain = _detect_domain(prompt)

        # Step 2: Extract project name
        project_name = _extract_project_name(prompt)

        # Step 3: Extract modules (heuristic + archetype matching)
        modules = self._extract_modules(prompt, domain)

        # Step 4: Extract requirements
        requirements = self._extract_requirements(prompt, domain)

        # Step 5: Extract constraints
        constraints = self._extract_constraints(prompt)

        # Step 6: Extract priorities
        priorities = self._extract_priorities(prompt)

        # Step 7: Ambiguity detection
        spec = IntentSpec(
            project_name=project_name,
            domain=domain,
            description=prompt,
            modules=modules,
            requirements=requirements,
            constraints=constraints,
            priorities=priorities,
            raw_prompt=prompt,
            confidence=0.0,
            metadata={"parse_method": "heuristic", "domain_detected": domain},
        )

        ambiguities = self._ambiguity_detector.detect(prompt, spec)
        spec.ambiguities = [a.to_dict() for a in ambiguities]

        # Compute confidence
        spec.confidence = self._compute_confidence(spec)

        # Optionally refine with LLM
        if self._llm_fn and spec.confidence < 0.7:
            llm_spec = self._parse_with_llm(prompt)
            if llm_spec:
                spec = spec.merge(llm_spec)
                spec.metadata["parse_method"] = "heuristic+llm"

        self._parse_cache[cache_key] = spec
        return copy.deepcopy(spec)

    def clarify(
        self,
        spec: IntentSpec,
        ambiguity: Union[Dict[str, Any], Ambiguity],
    ) -> IntentSpec:
        """
        Resolve an ambiguity in the spec.

        In autonomous mode (no user interaction), picks the most
        reasonable default. In interactive mode, would prompt the user.
        """
        if isinstance(ambiguity, Ambiguity):
            amb_dict = ambiguity.to_dict()
        else:
            amb_dict = ambiguity

        kind = amb_dict.get("kind", "vague")
        suggestions = amb_dict.get("suggestions", [])

        refined = copy.deepcopy(spec)

        if kind == "missing" and suggestions:
            # Add the first suggestion as a requirement
            refined.requirements.append(Requirement(
                id=f"clarified_{refined.revision}_{len(refined.requirements)}",
                text=suggestions[0],
                kind="functional",
                priority="medium",
                source="clarified",
            ))

        elif kind == "multi_interpretation" and suggestions:
            # Add a constraint resolving the ambiguity
            refined.constraints.append(Constraint(
                text=suggestions[0],
                kind="soft",
                scope="project",
            ))

        elif kind == "vague":
            # Use LLM to interpret the vague language
            if self._llm_fn:
                interpretation = self._interpret_vague(
                    spec.raw_prompt or spec.description,
                    amb_dict.get("text", ""),
                )
                if interpretation:
                    refined.requirements.append(Requirement(
                        id=f"interpreted_{refined.revision}_{len(refined.requirements)}",
                        text=interpretation,
                        kind="functional",
                        priority="medium",
                        source="clarified",
                    ))

        # Mark ambiguity as resolved
        refined.ambiguities = [
            a for a in refined.ambiguities
            if a.get("text") != amb_dict.get("text")
        ]
        refined.revision += 1
        refined.confidence = min(1.0, refined.confidence + 0.05)

        return refined

    def validate(self, spec: IntentSpec, code_summary: str) -> bool:
        """
        Validate that the code matches the intent spec.

        Returns True if the code matches, False if there are mismatches.
        """
        valid, _ = self._refiner.validate_against_code(spec, code_summary)
        return valid

    def refine(
        self,
        spec: IntentSpec,
        code_summary: str,
    ) -> IntentSpec:
        """
        Refine spec by validating against code and fixing mismatches.

        This implements the CEGAR loop on intent.
        """
        valid, mismatches = self._refiner.validate_against_code(spec, code_summary)
        if valid:
            return spec
        return self._refiner.refine(spec, code_summary, mismatches)

    # ------------------------------------------------------------------
    # Module extraction
    # ------------------------------------------------------------------

    def _extract_modules(self, prompt: str, domain: str) -> List[ModuleSpec]:
        """Extract module specifications from the prompt."""
        modules: List[ModuleSpec] = []

        # Try to match an archetype
        archetype = self._match_archetype(prompt, domain)
        if archetype:
            arch_modules = archetype.get("modules", [])
            arch_deps = archetype.get("dependencies", {})
            for mod_name in arch_modules:
                modules.append(ModuleSpec(
                    name=mod_name,
                    description=f"{mod_name} module for {domain} project",
                    dependencies=arch_deps.get(mod_name, []),
                    patterns=[domain],
                ))
            return modules

        # Fall back to keyword-based extraction
        prompt_lower = prompt.lower()
        extracted: List[str] = []

        # Look for explicit module mentions
        for match in re.finditer(
            r"(?:module|component|service|layer)s?\s*(?:for|:)?\s*(\w+(?:\s*,\s*\w+)*)",
            prompt_lower,
        ):
            names = [n.strip() for n in match.group(1).split(",")]
            extracted.extend(names)

        # Look for functional nouns
        functional_nouns = [
            "parser", "validator", "generator", "processor", "handler",
            "manager", "controller", "service", "engine", "client",
            "server", "router", "store", "cache", "queue",
            "scheduler", "monitor", "reporter", "analyzer",
        ]
        for noun in functional_nouns:
            if noun in prompt_lower:
                extracted.append(noun)

        if extracted:
            seen: Set[str] = set()
            for name in extracted:
                name = name.strip().replace(" ", "_")
                if name and name not in seen:
                    seen.add(name)
                    modules.append(ModuleSpec(
                        name=name,
                        description=f"{name} component",
                    ))
        else:
            # Default: single 'main' module
            modules.append(ModuleSpec(
                name="main",
                description=prompt[:200],
            ))

        return modules

    def _match_archetype(
        self, prompt: str, domain: str
    ) -> Optional[Dict[str, Any]]:
        """Try to match the prompt against a known module archetype."""
        prompt_lower = prompt.lower()

        # Direct archetype keyword matching
        archetype_keywords: Dict[str, List[str]] = {
            "api_server": ["api", "server", "rest", "endpoint"],
            "data_pipeline": ["pipeline", "etl", "transform", "data processing"],
            "cli_tool": ["cli", "command line", "terminal tool"],
            "trading_system": ["trading", "stock", "portfolio", "market"],
            "ml_pipeline": ["machine learning", "ml", "train", "model", "predict"],
        }

        best_match = ""
        best_score = 0
        for arch_name, keywords in archetype_keywords.items():
            score = sum(1 for kw in keywords if kw in prompt_lower)
            if score > best_score:
                best_score = score
                best_match = arch_name

        if best_score >= 2 and best_match in MODULE_ARCHETYPES:
            return MODULE_ARCHETYPES[best_match]

        # Domain-based fallback
        domain_to_archetype = {
            "finance": "trading_system",
            "web": "api_server",
            "data": "data_pipeline",
            "cli": "cli_tool",
            "ml": "ml_pipeline",
        }
        arch = domain_to_archetype.get(domain, "")
        if arch and arch in MODULE_ARCHETYPES:
            return MODULE_ARCHETYPES[arch]

        return None

    # ------------------------------------------------------------------
    # Requirement / constraint / priority extraction
    # ------------------------------------------------------------------

    def _extract_requirements(
        self, prompt: str, domain: str
    ) -> List[Requirement]:
        """Extract requirements from the prompt."""
        reqs: List[Requirement] = []
        sentences = re.split(r"[.!?\n]", prompt)

        for i, sentence in enumerate(sentences):
            sentence = sentence.strip()
            if not sentence:
                continue

            # Detect requirement-like sentences
            low = sentence.lower()
            is_req = any(kw in low for kw in [
                "must", "should", "need", "require", "want",
                "support", "handle", "provide", "include",
                "allow", "enable", "accept", "reject",
            ])
            if is_req:
                priority = "high" if any(
                    w in low for w in ["must", "critical", "essential", "require"]
                ) else "medium"
                reqs.append(Requirement(
                    id=f"req_{i}",
                    text=sentence,
                    kind="functional",
                    priority=priority,
                    source="parsed",
                ))

        return reqs

    def _extract_constraints(self, prompt: str) -> List[Constraint]:
        """Extract constraints from the prompt."""
        constraints: List[Constraint] = []
        prompt_lower = prompt.lower()

        constraint_patterns = [
            (r"(?:must not|should not|cannot|don't|do not)\s+(.+?)(?:[.!?\n]|$)", "hard"),
            (r"(?:prefer|ideally|if possible)\s+(.+?)(?:[.!?\n]|$)", "soft"),
            (r"(?:no more than|at most|maximum|limit)\s+(.+?)(?:[.!?\n]|$)", "hard"),
            (r"(?:at least|minimum)\s+(.+?)(?:[.!?\n]|$)", "hard"),
        ]

        for pattern, kind in constraint_patterns:
            for m in re.finditer(pattern, prompt_lower):
                constraints.append(Constraint(
                    text=m.group(1).strip(),
                    kind=kind,
                    scope="project",
                ))

        return constraints

    def _extract_priorities(self, prompt: str) -> List[Priority]:
        """Extract priorities from the prompt."""
        priorities: List[Priority] = []
        prompt_lower = prompt.lower()

        priority_markers = [
            (r"(?:most importantly?|priority|first and foremost)\s*[,:]?\s*(.+?)(?:[.!?\n]|$)", 2.0),
            (r"(?:also|additionally|plus)\s*[,:]?\s*(.+?)(?:[.!?\n]|$)", 1.0),
            (r"(?:nice to have|optionally|bonus)\s*[,:]?\s*(.+?)(?:[.!?\n]|$)", 0.5),
        ]

        for pattern, weight in priority_markers:
            for m in re.finditer(pattern, prompt_lower):
                priorities.append(Priority(
                    text=m.group(1).strip(),
                    weight=weight,
                ))

        return priorities

    # ------------------------------------------------------------------
    # LLM-assisted parsing
    # ------------------------------------------------------------------

    def _parse_with_llm(self, prompt: str) -> Optional[IntentSpec]:
        """Use LLM for deeper intent parsing."""
        if not self._llm_fn:
            return None

        system = (
            "You are a software architect. Parse the user's request into a "
            "structured JSON with keys:\n"
            "- project_name: string\n"
            "- domain: string (web, finance, data, ml, cli, game, crypto, system, general)\n"
            "- description: string\n"
            "- modules: [{name, description, dependencies, responsibilities}]\n"
            "- requirements: [{text, kind (functional|non_functional), priority (high|medium|low)}]\n"
            "- constraints: [{text, kind (hard|soft)}]\n"
            "Return valid JSON only."
        )

        try:
            raw = self._llm_fn(f"{system}\n\nUser request: {prompt}")
            parsed = _safe_json_parse(raw, fallback=None)
            if parsed and isinstance(parsed, dict):
                spec = IntentSpec.from_dict(parsed)
                spec.metadata["parse_method"] = "llm"
                return spec
        except Exception as exc:
            logger.debug("LLM parsing failed: %s", exc)

        return None

    def _interpret_vague(self, prompt: str, vague_text: str) -> str:
        """Use LLM to interpret vague language in context."""
        if not self._llm_fn:
            return ""

        system = (
            "Given a software request and a vague phrase found in it, "
            "provide a specific, actionable interpretation. "
            "Reply with a single sentence."
        )
        query = f"{system}\n\nRequest: {prompt}\nVague phrase: {vague_text}"

        try:
            return self._llm_fn(query).strip()
        except Exception:
            return ""

    # ------------------------------------------------------------------
    # Confidence scoring
    # ------------------------------------------------------------------

    def _compute_confidence(self, spec: IntentSpec) -> float:
        """Compute a confidence score for the parsed spec."""
        score = 0.0

        # Has a meaningful project name
        if spec.project_name and spec.project_name != "project":
            score += 0.1

        # Has a detected domain (not "general")
        if spec.domain != "general":
            score += 0.15

        # Has modules
        if spec.modules:
            score += min(0.2, len(spec.modules) * 0.05)

        # Has requirements
        if spec.requirements:
            score += min(0.2, len(spec.requirements) * 0.05)

        # Has constraints
        if spec.constraints:
            score += min(0.1, len(spec.constraints) * 0.03)

        # Fewer ambiguities = more confidence
        if not spec.ambiguities:
            score += 0.15
        else:
            score += max(0.0, 0.15 - len(spec.ambiguities) * 0.03)

        # Reasonable description length
        desc_len = len(spec.description)
        if desc_len > 30:
            score += 0.1
        if desc_len > 100:
            score += 0.05

        return min(1.0, score)


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  Private helpers                                                        ║
# ╚══════════════════════════════════════════════════════════════════════════╝

def _detect_domain(prompt: str) -> str:
    """Detect the project domain from the prompt."""
    prompt_lower = prompt.lower()
    best_domain = "general"
    best_score = 0

    for domain, keywords in KNOWN_DOMAINS.items():
        score = sum(1 for kw in keywords if kw in prompt_lower)
        if score > best_score:
            best_score = score
            best_domain = domain

    return best_domain if best_score >= 2 else "general"


def _extract_project_name(prompt: str) -> str:
    """Extract a project name from the prompt."""
    # Look for explicit name mentions
    patterns = [
        r"(?:called|named)\s+['\"]?(\w[\w-]*)['\"]?",
        r"(?:build|create|write|make)\s+(?:me\s+)?(?:a\s+)?(\w[\w\s]{1,20}?)(?:\s+(?:app|tool|system|service|api|server))",
    ]
    for pat in patterns:
        m = re.search(pat, prompt, re.IGNORECASE)
        if m:
            name = m.group(1).strip().replace(" ", "_").lower()
            if len(name) <= 30:
                return name

    # Fall back to first meaningful noun phrase
    words = prompt.split()[:10]
    nouns = [w.lower().strip(".,!?") for w in words if len(w) > 3 and w.isalpha()]
    skip = {"write", "build", "create", "make", "want", "need", "please", "with", "that", "this"}
    meaningful = [n for n in nouns if n not in skip]
    if meaningful:
        return "_".join(meaningful[:3])

    return "project"


def _extract_keywords(text: str) -> List[str]:
    """Extract meaningful keywords from a text string."""
    stop_words = {
        "the", "a", "an", "is", "are", "was", "were", "be", "been",
        "being", "have", "has", "had", "do", "does", "did", "will",
        "would", "could", "should", "may", "might", "shall", "can",
        "to", "of", "in", "for", "on", "with", "at", "by", "from",
        "as", "into", "through", "during", "before", "after",
        "and", "but", "or", "nor", "not", "so", "yet", "both",
        "it", "its", "this", "that", "these", "those", "which",
    }
    words = re.findall(r"\b\w+\b", text.lower())
    return [w for w in words if w not in stop_words and len(w) > 2]


def _safe_json_parse(text: str, fallback: Any = None) -> Any:
    """Parse JSON, with markdown fence extraction."""
    text = text.strip()
    try:
        return json.loads(text)
    except (json.JSONDecodeError, ValueError):
        pass
    match = re.search(r"```(?:json)?\s*\n(.*?)```", text, re.DOTALL)
    if match:
        try:
            return json.loads(match.group(1))
        except (json.JSONDecodeError, ValueError):
            pass
    brace_start = text.find("{")
    brace_end = text.rfind("}")
    if brace_start >= 0 and brace_end > brace_start:
        try:
            return json.loads(text[brace_start : brace_end + 1])
        except (json.JSONDecodeError, ValueError):
            pass
    bracket_start = text.find("[")
    bracket_end = text.rfind("]")
    if bracket_start >= 0 and bracket_end > bracket_start:
        try:
            return json.loads(text[bracket_start : bracket_end + 1])
        except (json.JSONDecodeError, ValueError):
            pass
    return fallback
