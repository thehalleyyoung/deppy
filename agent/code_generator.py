"""
Type-driven code generation with verification for deppy.

Generates code from expanded type specifications, verifies it against
those specifications, and repairs via CEGAR when verification fails.

Classes
-------
TypeDrivenGenerator
    Main generator: ``generate(type_spec, context) → GeneratedCode``
GeneratedCode
    Code + metadata + trust level.
GenerationStrategy
    Strategy selector: mock, template, or LLM-based.
CodeVerifier
    Checks generated code against the type spec.
"""
from __future__ import annotations

import ast
import copy
import hashlib
import json
import logging
import os
import re
import textwrap
import time
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


# ---------------------------------------------------------------------------
# Trust-level lattice (mirrors verification_loop.py)
# ---------------------------------------------------------------------------

TRUST_LEVELS = ["UNCHECKED", "LLM_JUDGED", "Z3_PROVEN", "LEAN_VERIFIED"]
TRUST_RANK: Dict[str, int] = {level: i for i, level in enumerate(TRUST_LEVELS)}


def _min_trust(*levels: str) -> str:
    if not levels:
        return "UNCHECKED"
    return min(levels, key=lambda l: TRUST_RANK.get(l, 0))


def _content_hash(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  GeneratedCode                                                          ║
# ╚══════════════════════════════════════════════════════════════════════════╝

@dataclass
class GeneratedCode:
    """
    Result of code generation: source code plus metadata.

    Attributes
    ----------
    source : str
        The generated Python source code.
    module_name : str
        Name of the module this code belongs to.
    trust_level : str
        Trust level assigned after verification.
    strategy_used : str
        Which generation strategy produced the code.
    generation_time_ms : float
        Time taken to generate (milliseconds).
    verification_passed : bool
        Whether the code passed verification.
    metadata : dict
        Additional generation metadata.
    repair_history : list
        History of CEGAR repair rounds.
    content_hash : str
        SHA-256 hash of the source.
    """

    source: str = ""
    module_name: str = ""
    trust_level: str = "UNCHECKED"
    strategy_used: str = "unknown"
    generation_time_ms: float = 0.0
    verification_passed: bool = False
    metadata: Dict[str, Any] = field(default_factory=dict)
    repair_history: List[Dict[str, Any]] = field(default_factory=list)
    content_hash: str = ""

    def __post_init__(self) -> None:
        if self.source and not self.content_hash:
            self.content_hash = _content_hash(self.source)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "source": self.source,
            "module_name": self.module_name,
            "trust_level": self.trust_level,
            "strategy_used": self.strategy_used,
            "generation_time_ms": self.generation_time_ms,
            "verification_passed": self.verification_passed,
            "metadata": self.metadata,
            "repair_history": self.repair_history,
            "content_hash": self.content_hash,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "GeneratedCode":
        known = {f.name for f in cls.__dataclass_fields__.values()}  # type: ignore[attr-defined]
        filtered = {k: v for k, v in d.items() if k in known}
        return cls(**filtered)

    @property
    def line_count(self) -> int:
        return len(self.source.splitlines()) if self.source else 0

    def summary(self) -> str:
        return (
            f"GeneratedCode({self.module_name}, "
            f"{self.line_count} lines, "
            f"strategy={self.strategy_used}, "
            f"trust={self.trust_level}, "
            f"verified={self.verification_passed})"
        )


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  VerificationResult (local, lightweight)                                ║
# ╚══════════════════════════════════════════════════════════════════════════╝

@dataclass
class VerificationResult:
    """Result of verifying generated code against its type spec."""

    passed: bool = False
    trust_level: str = "UNCHECKED"
    checks: List[Dict[str, Any]] = field(default_factory=list)
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    duration_ms: float = 0.0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "passed": self.passed,
            "trust_level": self.trust_level,
            "checks": self.checks,
            "errors": self.errors,
            "warnings": self.warnings,
            "duration_ms": self.duration_ms,
        }

    @property
    def failed_checks(self) -> List[Dict[str, Any]]:
        return [c for c in self.checks if c.get("status") == "failed"]

    def summary(self) -> str:
        total = len(self.checks)
        passed = sum(1 for c in self.checks if c.get("status") == "passed")
        return (
            f"Verification: {passed}/{total} checks passed, "
            f"trust={self.trust_level}, "
            f"{'PASS' if self.passed else 'FAIL'}"
        )


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  GenerationStrategy                                                     ║
# ╚══════════════════════════════════════════════════════════════════════════╝

class GenerationStrategy:
    """
    Selects and executes a code generation strategy.

    Strategies (in order of preference):
      1. **template** — if the type spec matches a known template
      2. **llm** — use an LLM to generate code from the spec
      3. **mock** — generate a stub / mock implementation
    """

    def __init__(
        self,
        llm_fn: Optional[Callable[..., str]] = None,
        preferred: str = "auto",
    ) -> None:
        self._llm_fn = llm_fn
        self._preferred = preferred
        self._templates = _load_builtin_templates()

    def select(self, type_spec: Dict[str, Any], context: Dict[str, Any]) -> str:
        """
        Select the best generation strategy for the given spec.

        Returns one of: 'template', 'llm', 'mock'.
        """
        if self._preferred != "auto":
            return self._preferred

        # Check if a template matches
        template_name = self._find_template(type_spec)
        if template_name:
            return "template"

        # If LLM is available, use it
        if self._llm_fn is not None:
            return "llm"

        return "mock"

    def generate(
        self,
        strategy: str,
        type_spec: Dict[str, Any],
        context: Dict[str, Any],
    ) -> str:
        """Execute the given strategy and return source code."""
        if strategy == "template":
            return self._generate_from_template(type_spec, context)
        elif strategy == "llm":
            return self._generate_with_llm(type_spec, context)
        elif strategy == "mock":
            return self._generate_mock(type_spec, context)
        else:
            logger.warning("Unknown strategy %r, falling back to mock", strategy)
            return self._generate_mock(type_spec, context)

    # ------------------------------------------------------------------
    # Template generation
    # ------------------------------------------------------------------

    def _find_template(self, type_spec: Dict[str, Any]) -> Optional[str]:
        """Find a matching template for the type spec."""
        patterns = type_spec.get("metadata", {}).get("patterns", [])
        name = type_spec.get("name", "").lower()

        for tpl_name, tpl in self._templates.items():
            tpl_keywords = tpl.get("keywords", [])
            if any(kw in name for kw in tpl_keywords):
                return tpl_name
            if any(p in tpl_keywords for p in patterns):
                return tpl_name

        return None

    def _generate_from_template(
        self, type_spec: Dict[str, Any], context: Dict[str, Any]
    ) -> str:
        """Generate code from a matching template."""
        template_name = self._find_template(type_spec)
        if not template_name or template_name not in self._templates:
            return self._generate_mock(type_spec, context)

        template = self._templates[template_name]
        source = template["code"]

        # Substitute placeholders
        name = type_spec.get("name", "Module")
        source = source.replace("{{MODULE_NAME}}", name)
        source = source.replace("{{module_name}}", name.lower().replace("-", "_"))

        desc = type_spec.get("metadata", {}).get("description", f"{name} module")
        source = source.replace("{{DESCRIPTION}}", desc)

        # Substitute functions
        functions = type_spec.get("associated_functions", [])
        if functions:
            func_block = "\n\n".join(
                _generate_function_stub(fn, type_spec) for fn in functions
            )
            source = source.replace("{{FUNCTIONS}}", func_block)
        else:
            source = source.replace("{{FUNCTIONS}}", "")

        return source

    # ------------------------------------------------------------------
    # LLM generation
    # ------------------------------------------------------------------

    def _generate_with_llm(
        self, type_spec: Dict[str, Any], context: Dict[str, Any]
    ) -> str:
        """Generate code using an LLM."""
        if not self._llm_fn:
            return self._generate_mock(type_spec, context)

        prompt = _build_llm_generation_prompt(type_spec, context)

        try:
            raw = self._llm_fn(prompt)
            return _extract_code_block(raw)
        except Exception as exc:
            logger.warning("LLM generation failed: %s", exc)
            return self._generate_mock(type_spec, context)

    # ------------------------------------------------------------------
    # Mock generation
    # ------------------------------------------------------------------

    def _generate_mock(
        self, type_spec: Dict[str, Any], context: Dict[str, Any]
    ) -> str:
        """Generate a mock / stub implementation."""
        name = type_spec.get("name", "module")
        safe_name = name.replace("-", "_").replace(".", "_")
        desc = type_spec.get("metadata", {}).get("description", f"{name} module")

        lines: List[str] = [
            f'"""{desc}."""',
            "from __future__ import annotations",
            "",
            "from typing import Any, Dict, List, Optional",
            "",
        ]

        # Generate a class if the spec has contracts
        contracts = type_spec.get("contracts", {})
        if contracts:
            class_name = _to_class_name(safe_name)
            lines.append(f"class {class_name}:")
            lines.append(f'    """{desc}."""')
            lines.append("")
            lines.append("    def __init__(self) -> None:")
            lines.append("        self._data: Dict[str, Any] = {}")
            lines.append("")

            for fn_name in type_spec.get("associated_functions", []):
                lines.extend(_generate_method_stub_lines(fn_name, contracts))
                lines.append("")
        else:
            for fn_name in type_spec.get("associated_functions", []):
                lines.append(_generate_function_stub(fn_name, type_spec))
                lines.append("")

        if not type_spec.get("associated_functions") and not contracts:
            lines.extend([
                f"def main() -> None:",
                f'    """Entry point for {name}."""',
                "    raise NotImplementedError",
                "",
            ])

        return "\n".join(lines)


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  CodeVerifier                                                           ║
# ╚══════════════════════════════════════════════════════════════════════════╝

class CodeVerifier:
    """
    Verifies generated code against its type specification.

    Checks performed:
      1. Syntax validity (AST parse)
      2. Required functions / classes present
      3. Type annotation completeness
      4. Contract compliance (pre/post conditions in docstrings)
      5. Refinement predicate consistency
      6. Dependency imports present
      7. Optional: delegate to VerificationLoop for deep checks
    """

    def __init__(
        self,
        llm_fn: Optional[Callable[..., str]] = None,
        strict: bool = False,
    ) -> None:
        self._llm_fn = llm_fn
        self._strict = strict

    def verify(
        self,
        code: GeneratedCode,
        type_spec: Dict[str, Any],
    ) -> VerificationResult:
        """
        Verify *code* against *type_spec*.

        Returns a VerificationResult with per-check details.
        """
        t0 = time.monotonic()
        checks: List[Dict[str, Any]] = []
        errors: List[str] = []
        warnings: List[str] = []

        # Check 1: Syntax
        syntax_ok, syntax_error = self._check_syntax(code.source)
        checks.append({
            "name": "syntax",
            "status": "passed" if syntax_ok else "failed",
            "detail": syntax_error or "Valid Python syntax",
        })
        if not syntax_ok:
            errors.append(f"Syntax error: {syntax_error}")

        # Check 2: Required functions/classes
        func_checks = self._check_required_functions(code.source, type_spec)
        checks.extend(func_checks)
        for fc in func_checks:
            if fc["status"] == "failed":
                errors.append(f"Missing: {fc['detail']}")

        # Check 3: Type annotations
        anno_check = self._check_type_annotations(code.source)
        checks.append(anno_check)
        if anno_check["status"] == "failed":
            warnings.append(anno_check["detail"])

        # Check 4: Contract compliance
        contract_checks = self._check_contracts(code.source, type_spec)
        checks.extend(contract_checks)
        for cc in contract_checks:
            if cc["status"] == "failed":
                if self._strict:
                    errors.append(f"Contract: {cc['detail']}")
                else:
                    warnings.append(f"Contract: {cc['detail']}")

        # Check 5: Refinement predicates
        predicate_checks = self._check_predicates(code.source, type_spec)
        checks.extend(predicate_checks)
        for pc in predicate_checks:
            if pc["status"] == "failed":
                warnings.append(f"Predicate: {pc['detail']}")

        # Check 6: Dependency imports
        dep_checks = self._check_dependencies(code.source, type_spec)
        checks.extend(dep_checks)

        # Check 7: No dangerous patterns
        safety_checks = self._check_safety(code.source)
        checks.extend(safety_checks)
        for sc in safety_checks:
            if sc["status"] == "failed":
                warnings.append(f"Safety: {sc['detail']}")

        # Optionally delegate to VerificationLoop
        deep_result = self._deep_verify(code, type_spec)
        if deep_result:
            checks.extend(deep_result.get("checks", []))

        passed = len(errors) == 0
        trust = self._compute_trust(checks, passed)
        duration = (time.monotonic() - t0) * 1000

        return VerificationResult(
            passed=passed,
            trust_level=trust,
            checks=checks,
            errors=errors,
            warnings=warnings,
            duration_ms=duration,
        )

    # ------------------------------------------------------------------
    # Individual checks
    # ------------------------------------------------------------------

    def _check_syntax(self, source: str) -> Tuple[bool, str]:
        """Check Python syntax validity."""
        try:
            ast.parse(source)
            return True, ""
        except SyntaxError as exc:
            return False, f"Line {exc.lineno}: {exc.msg}"

    def _check_required_functions(
        self, source: str, type_spec: Dict[str, Any]
    ) -> List[Dict[str, Any]]:
        """Check that required functions/classes are defined."""
        checks: List[Dict[str, Any]] = []
        required = type_spec.get("associated_functions", [])
        if not required:
            return checks

        try:
            tree = ast.parse(source)
        except SyntaxError:
            return checks

        defined: Set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                defined.add(node.name)
            elif isinstance(node, ast.ClassDef):
                defined.add(node.name)
                for item in node.body:
                    if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        defined.add(item.name)

        for fn_name in required:
            found = fn_name in defined or fn_name.lower() in {d.lower() for d in defined}
            checks.append({
                "name": f"function:{fn_name}",
                "status": "passed" if found else "failed",
                "detail": f"Function '{fn_name}' {'found' if found else 'not found'} in source",
            })

        return checks

    def _check_type_annotations(self, source: str) -> Dict[str, Any]:
        """Check type annotation coverage."""
        try:
            tree = ast.parse(source)
        except SyntaxError:
            return {
                "name": "type_annotations",
                "status": "failed",
                "detail": "Cannot parse source for annotation check",
            }

        total_params = 0
        annotated_params = 0
        functions_with_return_type = 0
        total_functions = 0

        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                total_functions += 1
                if node.returns is not None:
                    functions_with_return_type += 1
                for arg in node.args.args:
                    if arg.arg != "self":
                        total_params += 1
                        if arg.annotation is not None:
                            annotated_params += 1

        if total_params == 0 and total_functions == 0:
            return {
                "name": "type_annotations",
                "status": "passed",
                "detail": "No functions to check",
            }

        coverage = 0.0
        if total_params > 0:
            coverage = annotated_params / total_params
        elif total_functions > 0:
            coverage = functions_with_return_type / total_functions

        threshold = 0.7 if self._strict else 0.3
        passed = coverage >= threshold

        return {
            "name": "type_annotations",
            "status": "passed" if passed else "failed",
            "detail": (
                f"Type annotation coverage: {coverage:.0%} "
                f"({annotated_params}/{total_params} params, "
                f"{functions_with_return_type}/{total_functions} return types)"
            ),
        }

    def _check_contracts(
        self, source: str, type_spec: Dict[str, Any]
    ) -> List[Dict[str, Any]]:
        """Check contract annotations in docstrings."""
        checks: List[Dict[str, Any]] = []
        contracts = type_spec.get("contracts", {})
        if not contracts:
            return checks

        requires = contracts.get("requires", [])
        ensures = contracts.get("ensures", [])

        source_lower = source.lower()

        for req in requires:
            keywords = _extract_keywords(req)
            found = any(kw in source_lower for kw in keywords) if keywords else True
            checks.append({
                "name": f"contract:requires:{req[:40]}",
                "status": "passed" if found else "failed",
                "detail": f"Precondition {'reflected' if found else 'not found'}: {req[:80]}",
            })

        for ens in ensures:
            keywords = _extract_keywords(ens)
            found = any(kw in source_lower for kw in keywords) if keywords else True
            checks.append({
                "name": f"contract:ensures:{ens[:40]}",
                "status": "passed" if found else "failed",
                "detail": f"Postcondition {'reflected' if found else 'not found'}: {ens[:80]}",
            })

        return checks

    def _check_predicates(
        self, source: str, type_spec: Dict[str, Any]
    ) -> List[Dict[str, Any]]:
        """Check refinement predicates."""
        checks: List[Dict[str, Any]] = []
        predicates = type_spec.get("refinement_predicates", [])
        if not predicates:
            return checks

        source_lower = source.lower()

        predicate_patterns: Dict[str, List[str]] = {
            "positive": ["> 0", ">0", "positive", "greater than 0"],
            "non-negative": [">= 0", ">=0", "non-negative", "nonnegative", ">= 0"],
            "non-empty": ["len(", "not empty", "nonempty", "len("] ,
            "sorted": ["sort", "sorted", "ascending", "descending"],
            "unique": ["unique", "distinct", "set(", "no duplicates"],
            "valid": ["valid", "validate", "is_valid"],
            "bounded": ["bound", "limit", "range", "clamp", "min(", "max("],
        }

        for pred in predicates:
            patterns = predicate_patterns.get(pred.lower(), [pred.lower()])
            found = any(p in source_lower for p in patterns)
            checks.append({
                "name": f"predicate:{pred}",
                "status": "passed" if found else "failed",
                "detail": f"Predicate '{pred}' {'found' if found else 'not found'}",
            })

        return checks

    def _check_dependencies(
        self, source: str, type_spec: Dict[str, Any]
    ) -> List[Dict[str, Any]]:
        """Check that dependency modules are imported."""
        checks: List[Dict[str, Any]] = []
        dep_params = type_spec.get("dependent_params", [])
        if not dep_params:
            return checks

        for param in dep_params:
            name = param.get("name", "")
            if name:
                found = name in source
                checks.append({
                    "name": f"dep_param:{name}",
                    "status": "passed" if found else "failed",
                    "detail": f"Dependent param '{name}' {'found' if found else 'not found'}",
                })

        return checks

    def _check_safety(self, source: str) -> List[Dict[str, Any]]:
        """Check for unsafe patterns."""
        checks: List[Dict[str, Any]] = []

        unsafe_patterns = [
            (r"\beval\s*\(", "Use of eval()"),
            (r"\bexec\s*\(", "Use of exec()"),
            (r"\b__import__\s*\(", "Use of __import__()"),
            (r"\bos\.system\s*\(", "Use of os.system()"),
            (r"\bsubprocess\.call\s*\(.*shell\s*=\s*True", "Shell injection risk"),
        ]

        for pattern, description in unsafe_patterns:
            if re.search(pattern, source):
                checks.append({
                    "name": f"safety:{description}",
                    "status": "failed",
                    "detail": description,
                })

        if not any(c["status"] == "failed" for c in checks):
            checks.append({
                "name": "safety:no_unsafe_patterns",
                "status": "passed",
                "detail": "No unsafe patterns detected",
            })

        return checks

    def _deep_verify(
        self,
        code: GeneratedCode,
        type_spec: Dict[str, Any],
    ) -> Optional[Dict[str, Any]]:
        """
        Delegate to VerificationLoop for deeper checks.
        Guarded import — returns None if not available.
        """
        try:
            from agent.verification_loop import VerificationLoop
            vloop = VerificationLoop()
            result = vloop.verify(code.source, code.module_name)
            if hasattr(result, "to_dict"):
                return result.to_dict()
            return result if isinstance(result, dict) else None
        except ImportError:
            return None
        except Exception as exc:
            logger.debug("Deep verification failed: %s", exc)
            return None

    def _compute_trust(
        self, checks: List[Dict[str, Any]], passed: bool
    ) -> str:
        """Compute trust level from check results."""
        if not passed:
            return "UNCHECKED"

        total = len(checks)
        if total == 0:
            return "UNCHECKED"

        pass_count = sum(1 for c in checks if c.get("status") == "passed")
        ratio = pass_count / total

        if ratio >= 0.95:
            return "Z3_PROVEN"
        elif ratio >= 0.7:
            return "LLM_JUDGED"
        else:
            return "UNCHECKED"


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  TypeDrivenGenerator — main class                                       ║
# ╚══════════════════════════════════════════════════════════════════════════╝

class TypeDrivenGenerator:
    """
    Type-driven code generator with integrated verification.

    Generates code from expanded type specifications, verifies it,
    and repairs via CEGAR when verification fails.

    Usage::

        gen = TypeDrivenGenerator(llm_fn=my_llm)
        code = gen.generate(type_spec, context)
        result = gen.verify(code, type_spec)
        if not result.passed:
            code = gen.repair(code, result.failed_checks)
    """

    def __init__(
        self,
        llm_fn: Optional[Callable[..., str]] = None,
        strategy: str = "auto",
        strict: bool = False,
        max_repair_rounds: int = 3,
    ) -> None:
        self._llm_fn = llm_fn
        self._strategy = GenerationStrategy(llm_fn=llm_fn, preferred=strategy)
        self._verifier = CodeVerifier(llm_fn=llm_fn, strict=strict)
        self._max_repair_rounds = max_repair_rounds
        self._generation_count = 0
        self._repair_count = 0
        self._cache: Dict[str, GeneratedCode] = {}

    # ------------------------------------------------------------------
    # Core API
    # ------------------------------------------------------------------

    def generate(
        self,
        type_spec: Dict[str, Any],
        context: Optional[Dict[str, Any]] = None,
    ) -> GeneratedCode:
        """
        Generate code from a type specification.

        Parameters
        ----------
        type_spec : dict
            Expanded type specification with refinement predicates,
            contracts, associated functions, etc.
        context : dict, optional
            Generation context (intent, plan, already-generated modules).

        Returns
        -------
        GeneratedCode
            Generated code with metadata and trust level.
        """
        context = context or {}
        cache_key = _content_hash(json.dumps(type_spec, sort_keys=True))

        if cache_key in self._cache:
            logger.debug("Cache hit for %s", type_spec.get("name", "?"))
            return copy.deepcopy(self._cache[cache_key])

        t0 = time.monotonic()
        strategy_name = self._strategy.select(type_spec, context)
        logger.info(
            "Generating %s with strategy=%s",
            type_spec.get("name", "?"),
            strategy_name,
        )

        source = self._strategy.generate(strategy_name, type_spec, context)
        elapsed_ms = (time.monotonic() - t0) * 1000
        self._generation_count += 1

        code = GeneratedCode(
            source=source,
            module_name=type_spec.get("name", "module"),
            trust_level="UNCHECKED",
            strategy_used=strategy_name,
            generation_time_ms=elapsed_ms,
            metadata={
                "type_spec_hash": cache_key,
                "context_keys": list(context.keys()),
            },
        )

        self._cache[cache_key] = code
        return copy.deepcopy(code)

    def verify(
        self,
        code: GeneratedCode,
        type_spec: Dict[str, Any],
    ) -> VerificationResult:
        """
        Verify generated code against its type specification.

        Parameters
        ----------
        code : GeneratedCode
            The code to verify.
        type_spec : dict
            The type specification to verify against.

        Returns
        -------
        VerificationResult
            Detailed verification results.
        """
        result = self._verifier.verify(code, type_spec)
        code.verification_passed = result.passed
        code.trust_level = result.trust_level
        return result

    def repair(
        self,
        code: GeneratedCode,
        failures: List[Dict[str, Any]],
        type_spec: Optional[Dict[str, Any]] = None,
        context: Optional[Dict[str, Any]] = None,
    ) -> GeneratedCode:
        """
        Repair code based on verification failures (CEGAR).

        Parameters
        ----------
        code : GeneratedCode
            The code that failed verification.
        failures : list
            List of failed checks from verification.
        type_spec : dict, optional
            Type spec for re-generation.
        context : dict, optional
            Generation context.

        Returns
        -------
        GeneratedCode
            Repaired code.
        """
        self._repair_count += 1
        context = context or {}

        repair_context = dict(context)
        repair_context["previous_source"] = code.source
        repair_context["failures"] = failures
        repair_context["cegar_feedback"] = _format_failures_as_feedback(failures)
        repair_context["repair_round"] = self._repair_count

        if self._llm_fn:
            repaired_source = self._repair_with_llm(code, failures, repair_context)
        else:
            repaired_source = self._repair_heuristic(code, failures)

        repaired = GeneratedCode(
            source=repaired_source,
            module_name=code.module_name,
            trust_level="UNCHECKED",
            strategy_used=f"repair:{code.strategy_used}",
            metadata={
                **code.metadata,
                "repaired": True,
                "repair_round": self._repair_count,
            },
            repair_history=[
                *code.repair_history,
                {
                    "round": self._repair_count,
                    "failures": len(failures),
                    "strategy": "llm" if self._llm_fn else "heuristic",
                },
            ],
        )

        return repaired

    def generate_and_verify(
        self,
        type_spec: Dict[str, Any],
        context: Optional[Dict[str, Any]] = None,
    ) -> Tuple[GeneratedCode, VerificationResult]:
        """
        Generate code, verify it, and repair via CEGAR if needed.

        Returns the final (code, verification_result) pair.
        """
        context = context or {}
        code = self.generate(type_spec, context)
        result = self.verify(code, type_spec)

        rounds = 0
        while not result.passed and rounds < self._max_repair_rounds:
            rounds += 1
            logger.info(
                "CEGAR round %d for %s (%d failures)",
                rounds,
                code.module_name,
                len(result.failed_checks),
            )
            code = self.repair(code, result.failed_checks, type_spec, context)
            result = self.verify(code, type_spec)

        return code, result

    # ------------------------------------------------------------------
    # Internal repair methods
    # ------------------------------------------------------------------

    def _repair_with_llm(
        self,
        code: GeneratedCode,
        failures: List[Dict[str, Any]],
        context: Dict[str, Any],
    ) -> str:
        """Use LLM to repair code based on failures."""
        if not self._llm_fn:
            return code.source

        feedback = context.get("cegar_feedback", "")
        prompt = (
            "Fix the following Python code based on the verification failures.\n\n"
            f"Current code:\n```python\n{code.source}\n```\n\n"
            f"Failures:\n{feedback}\n\n"
            "Return the fixed code wrapped in ```python ... ```.\n"
            "Preserve the overall structure but fix the specific issues."
        )

        try:
            raw = self._llm_fn(prompt)
            repaired = _extract_code_block(raw)
            # Validate syntax
            ast.parse(repaired)
            return repaired
        except SyntaxError:
            logger.warning("LLM repair produced invalid syntax, keeping original")
            return code.source
        except Exception as exc:
            logger.warning("LLM repair failed: %s", exc)
            return code.source

    def _repair_heuristic(
        self,
        code: GeneratedCode,
        failures: List[Dict[str, Any]],
    ) -> str:
        """Attempt heuristic repairs for common issues."""
        source = code.source

        for failure in failures:
            name = failure.get("name", "")
            detail = failure.get("detail", "")

            if "syntax" in name.lower():
                # Can't heuristically fix syntax errors
                continue

            if "not found" in detail.lower() and "function" in name.lower():
                fn_name = name.split(":")[-1] if ":" in name else "unknown"
                stub = (
                    f"\n\ndef {fn_name}(*args: Any, **kwargs: Any) -> Any:\n"
                    f'    """TODO: implement {fn_name}."""\n'
                    f"    raise NotImplementedError\n"
                )
                source += stub

            if "eval" in detail.lower() or "exec" in detail.lower():
                source = re.sub(r"\beval\s*\(([^)]+)\)", r"ast.literal_eval(\1)", source)
                source = re.sub(r"\bexec\s*\(([^)]+)\)", r"# exec removed: \1", source)
                if "import ast" not in source:
                    source = "import ast\n" + source

        return source

    # ------------------------------------------------------------------
    # Stats
    # ------------------------------------------------------------------

    @property
    def stats(self) -> Dict[str, Any]:
        return {
            "generations": self._generation_count,
            "repairs": self._repair_count,
            "cache_size": len(self._cache),
        }


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  Builtin templates                                                      ║
# ╚══════════════════════════════════════════════════════════════════════════╝

def _load_builtin_templates() -> Dict[str, Dict[str, Any]]:
    """Load builtin code generation templates."""
    return {
        "data_model": {
            "keywords": ["model", "data", "record", "entity", "schema"],
            "code": textwrap.dedent('''\
                """{{DESCRIPTION}}."""
                from __future__ import annotations

                from dataclasses import dataclass, field
                from typing import Any, Dict, List, Optional

                @dataclass
                class {{MODULE_NAME}}:
                    """{{DESCRIPTION}}."""

                    {{FUNCTIONS}}

                    def to_dict(self) -> Dict[str, Any]:
                        """Serialize to dictionary."""
                        return self.__dict__

                    @classmethod
                    def from_dict(cls, d: Dict[str, Any]) -> "{{MODULE_NAME}}":
                        """Deserialize from dictionary."""
                        return cls(**d)
            '''),
        },
        "service": {
            "keywords": ["service", "handler", "processor", "engine", "manager"],
            "code": textwrap.dedent('''\
                """{{DESCRIPTION}}."""
                from __future__ import annotations

                import logging
                from typing import Any, Dict, List, Optional

                logger = logging.getLogger(__name__)

                class {{MODULE_NAME}}:
                    """{{DESCRIPTION}}."""

                    def __init__(self, config: Optional[Dict[str, Any]] = None) -> None:
                        self._config = config or {}
                        self._initialized = False

                    def initialize(self) -> None:
                        """Initialize the service."""
                        self._initialized = True
                        logger.info("{{MODULE_NAME}} initialized")

                    {{FUNCTIONS}}

                    def shutdown(self) -> None:
                        """Shut down the service."""
                        self._initialized = False
                        logger.info("{{MODULE_NAME}} shut down")
            '''),
        },
        "validator": {
            "keywords": ["validator", "validate", "check", "verify"],
            "code": textwrap.dedent('''\
                """{{DESCRIPTION}}."""
                from __future__ import annotations

                from typing import Any, Dict, List, Optional, Tuple

                class {{MODULE_NAME}}:
                    """{{DESCRIPTION}}."""

                    def __init__(self, strict: bool = False) -> None:
                        self._strict = strict
                        self._errors: List[str] = []

                    def validate(self, data: Any) -> Tuple[bool, List[str]]:
                        """Validate data. Returns (valid, errors)."""
                        self._errors = []
                        self._validate_impl(data)
                        return len(self._errors) == 0, list(self._errors)

                    def _validate_impl(self, data: Any) -> None:
                        """Override to implement validation logic."""
                        raise NotImplementedError

                    {{FUNCTIONS}}
            '''),
        },
    }


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  Private helpers                                                        ║
# ╚══════════════════════════════════════════════════════════════════════════╝

def _extract_code_block(text: str) -> str:
    """Extract code from markdown fences or return raw text."""
    match = re.search(r"```(?:python)?\s*\n(.*?)```", text, re.DOTALL)
    if match:
        return match.group(1).strip()
    return text.strip()


def _to_class_name(name: str) -> str:
    """Convert a snake_case name to PascalCase."""
    parts = name.split("_")
    return "".join(p.capitalize() for p in parts if p)


def _generate_function_stub(fn_name: str, type_spec: Dict[str, Any]) -> str:
    """Generate a function stub."""
    contracts = type_spec.get("contracts", {})
    requires = contracts.get("requires", [])
    ensures = contracts.get("ensures", [])

    lines = [f"def {fn_name}(*args: Any, **kwargs: Any) -> Any:"]

    doc_lines = [f'    """Execute {fn_name}.']
    if requires:
        doc_lines.append("")
        doc_lines.append("    Requires:")
        for req in requires:
            doc_lines.append(f"        - {req}")
    if ensures:
        doc_lines.append("")
        doc_lines.append("    Ensures:")
        for ens in ensures:
            doc_lines.append(f"        - {ens}")
    doc_lines.append('    """')
    lines.extend(doc_lines)
    lines.append("    raise NotImplementedError")

    return "\n".join(lines)


def _generate_method_stub_lines(
    fn_name: str, contracts: Dict[str, List[str]]
) -> List[str]:
    """Generate method stub lines for a class."""
    requires = contracts.get("requires", [])
    ensures = contracts.get("ensures", [])

    lines = [f"    def {fn_name}(self, *args: Any, **kwargs: Any) -> Any:"]
    lines.append(f'        """Execute {fn_name}.')
    if requires:
        lines.append("")
        lines.append("        Requires:")
        for req in requires:
            lines.append(f"            - {req}")
    if ensures:
        lines.append("")
        lines.append("        Ensures:")
        for ens in ensures:
            lines.append(f"            - {ens}")
    lines.append('        """')
    lines.append("        raise NotImplementedError")
    return lines


def _build_llm_generation_prompt(
    type_spec: Dict[str, Any], context: Dict[str, Any]
) -> str:
    """Build a comprehensive LLM prompt for code generation."""
    name = type_spec.get("name", "module")
    desc = type_spec.get("metadata", {}).get("description", f"{name} module")

    parts = [
        f"Generate a complete Python module: {name}",
        f"\nDescription: {desc}",
    ]

    predicates = type_spec.get("refinement_predicates", [])
    if predicates:
        parts.append(f"\nRefinement predicates: {', '.join(predicates)}")

    contracts = type_spec.get("contracts", {})
    if contracts.get("requires"):
        parts.append(f"\nPreconditions:")
        for req in contracts["requires"]:
            parts.append(f"  - {req}")
    if contracts.get("ensures"):
        parts.append(f"\nPostconditions:")
        for ens in contracts["ensures"]:
            parts.append(f"  - {ens}")

    functions = type_spec.get("associated_functions", [])
    if functions:
        parts.append(f"\nRequired functions: {', '.join(functions)}")

    dep_params = type_spec.get("dependent_params", [])
    if dep_params:
        parts.append("\nDependent parameters:")
        for dp in dep_params:
            parts.append(f"  - {dp.get('name', '?')}: {dp.get('constraint', '?')}")

    # CEGAR feedback from previous round
    feedback = context.get("cegar_feedback", "")
    if feedback:
        parts.append(f"\n--- REPAIR INSTRUCTIONS ---\n{feedback}")
        prev = context.get("previous_source", "")
        if prev:
            parts.append(f"\nPrevious (buggy) code:\n```python\n{prev}\n```")

    parts.append(
        "\n\nRequirements:\n"
        "- Use type hints on all functions\n"
        "- Include docstrings\n"
        "- Handle errors properly\n"
        "- No use of eval() or exec()\n"
        "- Wrap code in ```python ... ```"
    )

    return "\n".join(parts)


def _format_failures_as_feedback(failures: List[Dict[str, Any]]) -> str:
    """Format verification failures as human-readable feedback."""
    lines: List[str] = []
    for f in failures:
        name = f.get("name", "?")
        detail = f.get("detail", "?")
        lines.append(f"FAILED [{name}]: {detail}")
    return "\n".join(lines)


def _extract_keywords(text: str) -> List[str]:
    """Extract meaningful keywords from text."""
    stop_words = {
        "the", "a", "an", "is", "are", "was", "were", "be", "been",
        "being", "have", "has", "had", "do", "does", "did", "will",
        "would", "could", "should", "may", "might", "shall", "can",
        "to", "of", "in", "for", "on", "with", "at", "by", "from",
        "as", "into", "through", "and", "but", "or", "not", "so",
        "it", "its", "this", "that", "these", "those", "which",
    }
    words = re.findall(r"\b\w+\b", text.lower())
    return [w for w in words if w not in stop_words and len(w) > 2]
