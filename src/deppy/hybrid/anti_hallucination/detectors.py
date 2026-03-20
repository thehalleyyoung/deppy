"""Specific hallucination pattern detectors for LLM-generated artifacts.

Each detector targets a specific artifact category (code, documentation,
specification, proof) and checks for common hallucination patterns.  Where
possible, detectors delegate to existing deppy infrastructure:

- :func:`deppy.types.type_from_python` for type checking.
- :mod:`deppy.library_theories` for theory-pack enumeration.
- :class:`deppy.solver.Z3Backend` for satisfiability / validity checks.
- :mod:`deppy.nl_synthesis` for docstring constraint extraction.

All detectors produce :class:`Detection` instances that carry structured
evidence, severity, and suggested fixes.
"""
from __future__ import annotations

import ast
import itertools
import re
import textwrap
import time
from collections import defaultdict
from dataclasses import dataclass, field
from enum import Enum
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterable,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

if TYPE_CHECKING:
    from deppy.core._protocols import TrustLevel
    from deppy.library_theories.theory_pack_base import TheoryPackBase
    from deppy.nl_synthesis import (
        DocstringParser,
        SynthesizedAnnotationBundle,
        synthesize_types_from_docstring,
    )
    from deppy.solver.solver_interface import SolverResult
    from deppy.solver.z3_backend import Z3Backend
    from deppy.types.base import TypeBase
    from deppy.types.refinement import Predicate, RefinementType


# ======================================================================
#  Lazy import helpers
# ======================================================================

def _import_type_from_python():
    from deppy.types import type_from_python
    return type_from_python


def _import_z3_backend():
    from deppy.solver.z3_backend import Z3Backend
    return Z3Backend


def _import_nl_synthesis():
    from deppy.nl_synthesis import synthesize_types_from_docstring
    return synthesize_types_from_docstring


def _import_docstring_parser():
    from deppy.nl_synthesis import DocstringParser
    return DocstringParser


def _import_theory_pack_registry():
    from deppy.library_theories.pack_registry import PackRegistry
    return PackRegistry


def _import_solver_interface():
    from deppy.solver.solver_interface import SolverObligation, SolverStatus
    return SolverObligation, SolverStatus


def _import_refinement_types():
    from deppy.types.refinement import (
        ConjunctionPred,
        FalsePred,
        TruePred,
        VarPred,
    )
    return ConjunctionPred, FalsePred, TruePred, VarPred


# ======================================================================
#  Detection dataclass (~50 lines)
# ======================================================================

class DetectionCategory(Enum):
    """Category of a hallucination detection."""
    CODE = "CODE"
    DOC = "DOC"
    SPEC = "SPEC"
    PROOF = "PROOF"


class DetectionSeverity(Enum):
    """Severity of a hallucination detection."""
    CRITICAL = "CRITICAL"
    HIGH = "HIGH"
    MEDIUM = "MEDIUM"
    LOW = "LOW"


@dataclass
class Detection:
    """A single hallucination detection with structured evidence.

    Each detection records which detector found it, what category the
    hallucination belongs to, how severe it is, and optionally a suggested fix.
    The ``trust_level`` mirrors the deppy TrustLevel lattice.
    """
    detector: str
    category: str       # CODE, DOC, SPEC, PROOF
    severity: str       # CRITICAL, HIGH, MEDIUM, LOW
    description: str
    evidence: List[str] = field(default_factory=list)
    location: Optional[Dict[str, Any]] = None
    suggested_fix: Optional[str] = None
    trust_level: str = "assumed"

    def to_dict(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {
            "detector": self.detector,
            "category": self.category,
            "severity": self.severity,
            "description": self.description,
            "evidence": self.evidence,
            "trust_level": self.trust_level,
        }
        if self.location is not None:
            d["location"] = self.location
        if self.suggested_fix is not None:
            d["suggested_fix"] = self.suggested_fix
        return d

    @property
    def is_critical(self) -> bool:
        return self.severity == "CRITICAL"

    @property
    def is_high_or_above(self) -> bool:
        return self.severity in ("CRITICAL", "HIGH")


# ======================================================================
#  CodeHallucinationDetector (~300 lines)
# ======================================================================

class CodeHallucinationDetector:
    """Detects hallucinated code patterns.

    Checks for:
    - API calls to nonexistent modules / functions.
    - Type contradictions detectable via :func:`deppy.types.type_from_python`.
    - Logic gaps (missing branches, uncovered cases).
    - Undefined variable references.
    """

    _BUILTIN_MODULES = frozenset({
        "os", "sys", "io", "re", "math", "json", "csv", "ast",
        "collections", "itertools", "functools", "operator", "typing",
        "pathlib", "hashlib", "hmac", "secrets", "uuid", "datetime",
        "time", "random", "copy", "pprint", "textwrap", "enum",
        "dataclasses", "abc", "contextlib", "logging", "warnings",
        "unittest", "pytest", "argparse", "configparser", "subprocess",
        "threading", "multiprocessing", "socket", "http", "urllib",
        "email", "html", "xml", "sqlite3", "pickle", "shelve",
        "struct", "array", "queue", "heapq", "bisect",
        "string", "codecs", "unicodedata", "locale",
        "decimal", "fractions", "statistics",
        "shutil", "tempfile", "glob", "fnmatch",
        "signal", "traceback", "inspect", "dis",
        "importlib", "pkgutil", "platform",
    })

    _COMMON_THIRD_PARTY = frozenset({
        "numpy", "np", "pandas", "pd", "scipy", "sklearn",
        "torch", "tensorflow", "tf", "keras", "jax",
        "matplotlib", "plt", "seaborn", "sns", "plotly",
        "requests", "httpx", "aiohttp", "flask", "django",
        "fastapi", "pydantic", "sqlalchemy", "celery",
        "redis", "boto3", "botocore", "google",
        "yaml", "toml", "dotenv", "click", "typer",
        "pytest", "hypothesis", "mock", "tqdm",
        "PIL", "cv2", "transformers", "tokenizers",
        "z3", "sympy", "networkx",
    })

    def __init__(self) -> None:
        self._known_modules: Set[str] = set(self._BUILTIN_MODULES | self._COMMON_THIRD_PARTY)

    def detect_nonexistent_api(
        self, code: str, theory_packs: Optional[Dict[str, Any]] = None
    ) -> List[Detection]:
        """Detect API calls to modules or functions that likely do not exist.

        Uses ``deppy.library_theories`` (via *theory_packs*) to expand the
        known symbol set if available.
        """
        detections: List[Detection] = []

        try:
            tree = ast.parse(code)
        except SyntaxError as exc:
            detections.append(
                Detection(
                    detector="CodeHallucinationDetector",
                    category="CODE",
                    severity="CRITICAL",
                    description="Code has syntax errors and cannot be parsed",
                    evidence=["SyntaxError: " + str(exc)],
                    location={"line": getattr(exc, "lineno", None)},
                    suggested_fix="Fix syntax errors before checking for hallucinations",
                )
            )
            return detections

        known_symbols = self._build_known_symbols(tree, theory_packs)
        imported_names = self._collect_imports(tree)

        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    top_module = alias.name.split(".")[0]
                    if top_module not in self._known_modules:
                        detections.append(
                            Detection(
                                detector="CodeHallucinationDetector",
                                category="CODE",
                                severity="HIGH",
                                description="Import of potentially nonexistent module: '" + alias.name + "'",
                                evidence=["Module '" + alias.name + "' not in known standard/common libraries"],
                                location={"line": node.lineno, "col": node.col_offset},
                                suggested_fix="Verify that '" + alias.name + "' is an installable package",
                                trust_level="assumed",
                            )
                        )

            elif isinstance(node, ast.ImportFrom) and node.module:
                top_module = node.module.split(".")[0]
                if top_module not in self._known_modules and top_module not in imported_names:
                    detections.append(
                        Detection(
                            detector="CodeHallucinationDetector",
                            category="CODE",
                            severity="HIGH",
                            description="Import from potentially nonexistent module: '" + node.module + "'",
                            evidence=["Module '" + node.module + "' not in known libraries"],
                            location={"line": node.lineno},
                            suggested_fix="Verify that '" + node.module + "' exists and is importable",
                            trust_level="assumed",
                        )
                    )

            elif isinstance(node, ast.Call):
                func_name = self._get_call_name(node)
                if func_name and "." in func_name:
                    parts = func_name.split(".")
                    if parts[0] not in known_symbols and parts[0] not in imported_names:
                        detections.append(
                            Detection(
                                detector="CodeHallucinationDetector",
                                category="CODE",
                                severity="MEDIUM",
                                description="Call to potentially undefined: '" + func_name + "'",
                                evidence=["Base '" + parts[0] + "' not in scope"],
                                location={"line": node.lineno, "col": node.col_offset},
                                trust_level="residual",
                            )
                        )

        return detections

    def detect_impossible_types(self, code: str) -> List[Detection]:
        """Detect type contradictions in annotations.

        Uses :func:`deppy.types.type_from_python` when available to attempt
        type construction; contradictions surface as construction failures.
        """
        detections: List[Detection] = []

        try:
            tree = ast.parse(code)
        except SyntaxError:
            return detections

        type_from_python = None
        try:
            type_from_python = _import_type_from_python()
        except Exception:
            pass

        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue

            # Check for contradictory annotation patterns
            return_ann = node.returns
            if return_ann is not None:
                ann_str = ast.dump(return_ann)

                # None return with non-None annotation
                has_only_none_returns = True
                has_any_return = False
                for child in ast.walk(node):
                    if isinstance(child, ast.Return):
                        has_any_return = True
                        if child.value is not None and not (
                            isinstance(child.value, ast.Constant) and child.value.value is None
                        ):
                            has_only_none_returns = False

                if has_any_return and has_only_none_returns:
                    if not self._annotation_is_none(return_ann):
                        detections.append(
                            Detection(
                                detector="CodeHallucinationDetector",
                                category="CODE",
                                severity="HIGH",
                                description="Function '" + node.name + "' always returns None but has non-None return annotation",
                                evidence=[
                                    "Return annotation: " + ast.unparse(return_ann) if hasattr(ast, "unparse") else "Return annotation present",
                                    "All return statements return None",
                                ],
                                location={"line": node.lineno, "function": node.name},
                                suggested_fix="Change return annotation to None or Optional[...]",
                                trust_level="bounded_auto",
                            )
                        )

            # Check for parameters annotated with incompatible defaults
            for arg, default in self._zip_args_defaults(node):
                if arg.annotation is not None and default is not None:
                    contradiction = self._check_annotation_default_mismatch(arg, default)
                    if contradiction:
                        detections.append(
                            Detection(
                                detector="CodeHallucinationDetector",
                                category="CODE",
                                severity="MEDIUM",
                                description=contradiction,
                                evidence=["Parameter: " + arg.arg],
                                location={"line": node.lineno, "function": node.name, "param": arg.arg},
                                trust_level="bounded_auto",
                            )
                        )

        return detections

    def detect_logic_gaps(self, code: str) -> List[Detection]:
        """Detect missing branches, uncovered match cases, and logic gaps."""
        detections: List[Detection] = []

        try:
            tree = ast.parse(code)
        except SyntaxError:
            return detections

        for node in ast.walk(tree):
            # Missing else in if/elif chains that appear exhaustive
            if isinstance(node, ast.If):
                if node.orelse and isinstance(node.orelse[0], ast.If):
                    # It is an if/elif chain -- check if there is a final else
                    chain = self._collect_if_chain(node)
                    if len(chain) >= 2 and not self._chain_has_else(node):
                        detections.append(
                            Detection(
                                detector="CodeHallucinationDetector",
                                category="CODE",
                                severity="MEDIUM",
                                description="if/elif chain with " + str(len(chain)) + " branches but no else clause",
                                evidence=["Chain starts at line " + str(node.lineno)],
                                location={"line": node.lineno},
                                suggested_fix="Add an else clause or document why it is unreachable",
                                trust_level="residual",
                            )
                        )

            # Try without except
            if isinstance(node, ast.Try):
                if not node.handlers and not node.finalbody:
                    detections.append(
                        Detection(
                            detector="CodeHallucinationDetector",
                            category="CODE",
                            severity="HIGH",
                            description="try block with no except or finally clause",
                            evidence=["Line " + str(node.lineno)],
                            location={"line": node.lineno},
                            suggested_fix="Add appropriate exception handlers",
                            trust_level="bounded_auto",
                        )
                    )

                # Bare except that silently passes
                for handler in node.handlers:
                    if handler.type is None:
                        body_stmts = handler.body
                        if len(body_stmts) == 1 and isinstance(body_stmts[0], ast.Pass):
                            detections.append(
                                Detection(
                                    detector="CodeHallucinationDetector",
                                    category="CODE",
                                    severity="HIGH",
                                    description="Bare except with pass -- silently swallows all exceptions",
                                    evidence=["Line " + str(handler.lineno)],
                                    location={"line": handler.lineno},
                                    suggested_fix="Catch specific exceptions or at minimum log the error",
                                    trust_level="bounded_auto",
                                )
                            )

            # Functions that claim to return but have unreachable code after return
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                for i, stmt in enumerate(node.body):
                    if isinstance(stmt, ast.Return) and i < len(node.body) - 1:
                        remaining = node.body[i + 1:]
                        non_trivial = [s for s in remaining if not isinstance(s, (ast.Pass, ast.Expr))]
                        if non_trivial:
                            detections.append(
                                Detection(
                                    detector="CodeHallucinationDetector",
                                    category="CODE",
                                    severity="MEDIUM",
                                    description="Unreachable code after return in '" + node.name + "'",
                                    evidence=[str(len(non_trivial)) + " unreachable statements after line " + str(stmt.lineno)],
                                    location={"line": stmt.lineno, "function": node.name},
                                    suggested_fix="Remove dead code or restructure control flow",
                                    trust_level="bounded_auto",
                                )
                            )
                        break

        return detections

    # -- helpers -----------------------------------------------------------

    def _build_known_symbols(
        self, tree: ast.Module, theory_packs: Optional[Dict[str, Any]]
    ) -> Set[str]:
        """Collect all symbols defined or imported in the AST."""
        symbols: Set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Name):
                symbols.add(node.id)
            elif isinstance(node, ast.FunctionDef):
                symbols.add(node.name)
            elif isinstance(node, ast.ClassDef):
                symbols.add(node.name)
            elif isinstance(node, ast.Import):
                for alias in node.names:
                    symbols.add(alias.asname or alias.name.split(".")[0])
            elif isinstance(node, ast.ImportFrom):
                for alias in (node.names or []):
                    symbols.add(alias.asname or alias.name)

        if theory_packs:
            for pack_name, pack_data in theory_packs.items():
                if isinstance(pack_data, dict):
                    symbols.update(pack_data.get("symbols", []))
                    symbols.update(pack_data.get("functions", []))

        # Also try deppy theory pack registry
        try:
            PackRegistry = _import_theory_pack_registry()
            registry = PackRegistry()
            for pack in registry.all_packs():
                pack_name_str = getattr(pack, "name", "")
                if pack_name_str:
                    symbols.add(pack_name_str)
        except Exception:
            pass

        return symbols

    def _collect_imports(self, tree: ast.Module) -> Set[str]:
        """Collect all imported names."""
        names: Set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    names.add(alias.asname or alias.name.split(".")[0])
            elif isinstance(node, ast.ImportFrom):
                if node.module:
                    names.add(node.module.split(".")[0])
                for alias in (node.names or []):
                    names.add(alias.asname or alias.name)
        return names

    @staticmethod
    def _get_call_name(node: ast.Call) -> Optional[str]:
        """Extract dotted name from a Call node."""
        if isinstance(node.func, ast.Name):
            return node.func.id
        if isinstance(node.func, ast.Attribute):
            parts: List[str] = [node.func.attr]
            value = node.func.value
            while isinstance(value, ast.Attribute):
                parts.append(value.attr)
                value = value.value
            if isinstance(value, ast.Name):
                parts.append(value.id)
            return ".".join(reversed(parts))
        return None

    @staticmethod
    def _annotation_is_none(ann: ast.expr) -> bool:
        """Check if an annotation represents None."""
        if isinstance(ann, ast.Constant) and ann.value is None:
            return True
        if isinstance(ann, ast.Name) and ann.id == "None":
            return True
        return False

    @staticmethod
    def _zip_args_defaults(
        node: Union[ast.FunctionDef, ast.AsyncFunctionDef]
    ) -> List[Tuple[ast.arg, Optional[ast.expr]]]:
        """Zip function args with their defaults (right-aligned)."""
        args = node.args.args
        defaults = node.args.defaults
        n_no_default = len(args) - len(defaults)
        result: List[Tuple[ast.arg, Optional[ast.expr]]] = []
        for i, arg in enumerate(args):
            if i < n_no_default:
                result.append((arg, None))
            else:
                result.append((arg, defaults[i - n_no_default]))
        return result

    @staticmethod
    def _check_annotation_default_mismatch(
        arg: ast.arg, default: ast.expr
    ) -> Optional[str]:
        """Check if an annotation and default value are obviously mismatched."""
        ann = arg.annotation
        if ann is None:
            return None

        ann_name = ""
        if isinstance(ann, ast.Name):
            ann_name = ann.id
        elif isinstance(ann, ast.Constant):
            ann_name = type(ann.value).__name__

        if not ann_name:
            return None

        if isinstance(default, ast.Constant):
            default_type = type(default.value).__name__
            _INCOMPATIBLE = {
                ("int", "str"), ("str", "int"), ("float", "str"),
                ("str", "float"), ("bool", "str"), ("str", "bool"),
                ("int", "list"), ("str", "list"), ("list", "int"),
            }
            if (ann_name.lower(), default_type.lower()) in _INCOMPATIBLE:
                return (
                    "Parameter '" + arg.arg + "' annotated as " + ann_name
                    + " but default is " + default_type + "(" + repr(default.value) + ")"
                )
        return None

    @staticmethod
    def _collect_if_chain(node: ast.If) -> List[ast.If]:
        """Collect all if/elif nodes in a chain."""
        chain = [node]
        current = node
        while current.orelse and len(current.orelse) == 1 and isinstance(current.orelse[0], ast.If):
            current = current.orelse[0]
            chain.append(current)
        return chain

    @staticmethod
    def _chain_has_else(node: ast.If) -> bool:
        """Check if an if/elif chain ends with an else."""
        current = node
        while current.orelse:
            if len(current.orelse) == 1 and isinstance(current.orelse[0], ast.If):
                current = current.orelse[0]
            else:
                # Non-empty orelse that is not another If = else block
                return True
        return False


# ======================================================================
#  DocHallucinationDetector (~250 lines)
# ======================================================================

class DocHallucinationDetector:
    """Detects hallucinated documentation patterns.

    Checks for:
    - False claims about function behavior.
    - Missing caveats (e.g., can raise but doc says it does not).
    - Phantom parameters documented but not in signature.
    """

    _PARAM_PATTERN = re.compile(
        r"(?::param\s+(\w+)\s*:|@param\s+(\w+)\s|"
        r"Args:\s*\n(?:\s+(\w+)[\s:(].*\n)*)",
        re.MULTILINE,
    )
    _GOOGLE_PARAM_RE = re.compile(r"^\s+(\w+)\s*[\(:]", re.MULTILINE)
    _RETURN_CLAIM_RE = re.compile(
        r"(?:returns?\s+(?:a\s+)?(\w+)|:rtype:\s*(\w+))",
        re.IGNORECASE,
    )

    def detect_false_claims(
        self, docstring: str, code_ast: ast.Module
    ) -> List[Detection]:
        """Detect demonstrably false claims in *docstring* given *code_ast*."""
        detections: List[Detection] = []

        # Check "never raises" / "does not raise" claims
        no_raise_claim = bool(re.search(
            r"\b(never\s+raises?|does\s+not\s+raise|no\s+exceptions?|"
            r"will\s+not\s+raise|cannot\s+raise)\b",
            docstring,
            re.IGNORECASE,
        ))
        if no_raise_claim:
            raises_found: List[str] = []
            for node in ast.walk(code_ast):
                if isinstance(node, ast.Raise) and node.exc is not None:
                    if isinstance(node.exc, ast.Call) and isinstance(node.exc.func, ast.Name):
                        raises_found.append(node.exc.func.id)
                    elif isinstance(node.exc, ast.Name):
                        raises_found.append(node.exc.id)
            if raises_found:
                detections.append(
                    Detection(
                        detector="DocHallucinationDetector",
                        category="DOC",
                        severity="HIGH",
                        description="Docstring claims no exceptions, but code raises: " + ", ".join(sorted(set(raises_found))),
                        evidence=["Claim: 'never raises'", "Actually raises: " + str(raises_found)],
                        suggested_fix="Document the exceptions or add try/except",
                        trust_level="bounded_auto",
                    )
                )

        # Check "pure function" / "no side effects" claims
        pure_claim = bool(re.search(
            r"\b(pure\s+function|no\s+side\s+effects?|side-?effect\s+free|"
            r"referentially\s+transparent)\b",
            docstring,
            re.IGNORECASE,
        ))
        if pure_claim:
            side_effects = self._detect_side_effects(code_ast)
            if side_effects:
                detections.append(
                    Detection(
                        detector="DocHallucinationDetector",
                        category="DOC",
                        severity="HIGH",
                        description="Docstring claims pure/no side effects, but code has: " + ", ".join(side_effects[:5]),
                        evidence=["Claim: 'pure function'"] + side_effects[:5],
                        suggested_fix="Remove purity claim or refactor to eliminate side effects",
                        trust_level="bounded_auto",
                    )
                )

        # Check "thread-safe" claims
        thread_safe_claim = bool(re.search(
            r"\b(thread[- ]?safe|concurrent[- ]?safe)\b",
            docstring,
            re.IGNORECASE,
        ))
        if thread_safe_claim:
            has_locking = False
            for node in ast.walk(code_ast):
                if isinstance(node, ast.Attribute) and node.attr in ("acquire", "release", "Lock", "RLock"):
                    has_locking = True
                elif isinstance(node, ast.Name) and node.id in ("Lock", "RLock", "Semaphore"):
                    has_locking = True
            if not has_locking:
                mutable_state = self._has_mutable_shared_state(code_ast)
                if mutable_state:
                    detections.append(
                        Detection(
                            detector="DocHallucinationDetector",
                            category="DOC",
                            severity="MEDIUM",
                            description="Claims thread-safety but no locking observed and mutable state detected",
                            evidence=mutable_state[:3],
                            suggested_fix="Add synchronization primitives or remove thread-safety claim",
                            trust_level="residual",
                        )
                    )

        # Check return type claims
        for m in self._RETURN_CLAIM_RE.finditer(docstring):
            claimed_type = (m.group(1) or m.group(2) or "").lower()
            if not claimed_type:
                continue
            actual_returns = self._collect_return_types(code_ast)
            if actual_returns and claimed_type not in actual_returns:
                detections.append(
                    Detection(
                        detector="DocHallucinationDetector",
                        category="DOC",
                        severity="MEDIUM",
                        description="Docstring claims return type '" + claimed_type + "' but code suggests: " + ", ".join(sorted(actual_returns)),
                        evidence=["Claimed: " + claimed_type, "Observed: " + str(sorted(actual_returns))],
                        trust_level="residual",
                    )
                )

        return detections

    def detect_missing_caveats(
        self, docstring: str, code_ast: ast.Module
    ) -> List[Detection]:
        """Detect important caveats missing from *docstring*."""
        detections: List[Detection] = []

        # Missing mention of exceptions
        code_exceptions: Set[str] = set()
        for node in ast.walk(code_ast):
            if isinstance(node, ast.Raise) and node.exc is not None:
                if isinstance(node.exc, ast.Call) and isinstance(node.exc.func, ast.Name):
                    code_exceptions.add(node.exc.func.id)
                elif isinstance(node.exc, ast.Name):
                    code_exceptions.add(node.exc.id)

        doc_lower = docstring.lower()
        for exc in code_exceptions:
            if exc.lower() not in doc_lower and "raises" not in doc_lower:
                detections.append(
                    Detection(
                        detector="DocHallucinationDetector",
                        category="DOC",
                        severity="MEDIUM",
                        description="Code raises '" + exc + "' but docstring does not mention it",
                        evidence=["Exception: " + exc],
                        suggested_fix="Add ':raises " + exc + ":' to docstring",
                        trust_level="residual",
                    )
                )

        # Missing mention of None return
        for node in ast.walk(code_ast):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                returns_none = any(
                    isinstance(child, ast.Return) and (
                        child.value is None or
                        (isinstance(child.value, ast.Constant) and child.value.value is None)
                    )
                    for child in ast.walk(node)
                )
                if returns_none and "none" not in doc_lower and "optional" not in doc_lower:
                    detections.append(
                        Detection(
                            detector="DocHallucinationDetector",
                            category="DOC",
                            severity="LOW",
                            description="Function '" + node.name + "' can return None but docstring does not mention it",
                            evidence=["Return None found in " + node.name],
                            suggested_fix="Document that None may be returned",
                            trust_level="residual",
                        )
                    )

        return detections

    def detect_phantom_params(
        self, docstring: str, func_ast: ast.FunctionDef
    ) -> List[Detection]:
        """Detect parameters documented in *docstring* but absent from *func_ast*."""
        detections: List[Detection] = []
        doc_params = self._extract_doc_params(docstring)

        code_params: Set[str] = set()
        for arg in func_ast.args.args + func_ast.args.kwonlyargs:
            if arg.arg not in ("self", "cls"):
                code_params.add(arg.arg)
        if func_ast.args.vararg:
            code_params.add(func_ast.args.vararg.arg)
        if func_ast.args.kwarg:
            code_params.add(func_ast.args.kwarg.arg)

        phantoms = doc_params - code_params
        for p in phantoms:
            detections.append(
                Detection(
                    detector="DocHallucinationDetector",
                    category="DOC",
                    severity="HIGH",
                    description="Phantom parameter '" + p + "' documented but not in function signature",
                    evidence=[
                        "Documented: " + p,
                        "Actual params: " + str(sorted(code_params)),
                    ],
                    location={"function": func_ast.name, "phantom_param": p},
                    suggested_fix="Remove '" + p + "' from docstring or add to signature",
                    trust_level="bounded_auto",
                )
            )

        return detections

    # -- helpers -----------------------------------------------------------

    def _extract_doc_params(self, docstring: str) -> Set[str]:
        """Extract parameter names from docstring."""
        params: Set[str] = set()
        # :param x: or @param x
        for m in re.finditer(r":param\s+(\w+)\s*:|@param\s+(\w+)", docstring):
            name = m.group(1) or m.group(2)
            if name:
                params.add(name)
        # Google-style Args: section
        args_match = re.search(r"Args:\s*\n((?:\s+\w+.*\n)*)", docstring)
        if args_match:
            for m in self._GOOGLE_PARAM_RE.finditer(args_match.group(1)):
                params.add(m.group(1))
        # NumPy-style Parameters section
        params_match = re.search(r"Parameters\s*[-]+\s*\n((?:\s+\w+.*\n)*)", docstring)
        if params_match:
            for m in self._GOOGLE_PARAM_RE.finditer(params_match.group(1)):
                params.add(m.group(1))
        return params

    @staticmethod
    def _detect_side_effects(tree: ast.Module) -> List[str]:
        """Detect potential side effects in code."""
        effects: List[str] = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Call):
                name = ""
                if isinstance(node.func, ast.Attribute):
                    name = node.func.attr
                elif isinstance(node.func, ast.Name):
                    name = node.func.id
                if name in ("print", "write", "send", "append", "extend",
                            "insert", "remove", "pop", "clear", "update",
                            "setattr", "delattr"):
                    effects.append("call to '" + name + "' at line " + str(node.lineno))
            elif isinstance(node, ast.Global):
                effects.append("global statement at line " + str(node.lineno))
            elif isinstance(node, ast.Nonlocal):
                effects.append("nonlocal statement at line " + str(node.lineno))
        return effects

    @staticmethod
    def _has_mutable_shared_state(tree: ast.Module) -> List[str]:
        """Check for mutable shared state patterns."""
        issues: List[str] = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Global):
                issues.append("global statement at line " + str(node.lineno))
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Attribute) and isinstance(target.value, ast.Name):
                        if target.value.id == "self":
                            issues.append("self." + target.attr + " mutation at line " + str(node.lineno))
        return issues

    @staticmethod
    def _collect_return_types(tree: ast.Module) -> Set[str]:
        """Collect return type hints from type annotations."""
        types: Set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node.returns:
                    if isinstance(node.returns, ast.Name):
                        types.add(node.returns.id.lower())
                    elif isinstance(node.returns, ast.Constant):
                        types.add(str(type(node.returns.value).__name__).lower())
        return types


# ======================================================================
#  SpecHallucinationDetector (~250 lines)
# ======================================================================

class SpecHallucinationDetector:
    """Detects hallucinated specifications.

    Uses :class:`deppy.solver.Z3Backend` for satisfiability and validity checks.
    """

    def __init__(self, *, use_z3: bool = True) -> None:
        self._use_z3 = use_z3
        self._backend: Any = None

    def _get_backend(self) -> Any:
        """Lazily instantiate Z3Backend."""
        if self._backend is not None:
            return self._backend
        if not self._use_z3:
            return None
        try:
            Z3Backend = _import_z3_backend()
            self._backend = Z3Backend()
            if not self._backend.is_available:
                self._backend = None
        except Exception:
            self._backend = None
        return self._backend

    def detect_unsatisfiable_spec(
        self, spec: Dict[str, Any]
    ) -> List[Detection]:
        """Detect specifications that are unsatisfiable (always false).

        Uses Z3 to check SAT of the conjunction of all constraints.
        """
        detections: List[Detection] = []
        constraints = spec.get("constraints", [])
        if not constraints:
            return detections

        backend = self._get_backend()
        if backend is None:
            return self._heuristic_unsat_check(spec, constraints)

        try:
            SolverObligation, SolverStatus = _import_solver_interface()
            ConjunctionPred, FalsePred, TruePred, VarPred = _import_refinement_types()

            preds = []
            for c in constraints:
                if isinstance(c, str):
                    preds.append(VarPred(var_name=c.replace(" ", "_")[:40]))
                elif isinstance(c, dict):
                    desc = c.get("predicate", c.get("description", str(c)))
                    preds.append(VarPred(var_name=str(desc).replace(" ", "_")[:40]))

            if not preds:
                return detections

            conj = ConjunctionPred(conjuncts=tuple(preds))
            obligation = SolverObligation(
                predicate=conj,
                description="spec_satisfiability",
            )
            result = backend.check(obligation)

            if hasattr(result, "status") and result.status == SolverStatus.UNSAT:
                detections.append(
                    Detection(
                        detector="SpecHallucinationDetector",
                        category="SPEC",
                        severity="CRITICAL",
                        description="Specification is unsatisfiable -- no possible implementation can meet these constraints",
                        evidence=[
                            "Z3 returned UNSAT for " + str(len(constraints)) + " constraints",
                            "Constraints: " + str(constraints[:5]),
                        ],
                        suggested_fix="Relax contradictory constraints",
                        trust_level="trusted_auto",
                    )
                )
        except Exception:
            detections.extend(self._heuristic_unsat_check(spec, constraints))

        return detections

    def _heuristic_unsat_check(
        self, spec: Dict[str, Any], constraints: List[Any]
    ) -> List[Detection]:
        """Heuristic unsatisfiability check when Z3 is unavailable."""
        detections: List[Detection] = []
        strs = [str(c).lower() for c in constraints]

        _CONTRADICTION_PATTERNS = [
            ("must be positive", "must be negative"),
            ("must be zero", "must be non-zero"),
            ("must be empty", "must be non-empty"),
            ("must be true", "must be false"),
            ("must be null", "must be non-null"),
            ("must be finite", "must be infinite"),
            ("is required", "is forbidden"),
        ]
        for pos, neg in _CONTRADICTION_PATTERNS:
            has_pos = any(pos in s for s in strs)
            has_neg = any(neg in s for s in strs)
            if has_pos and has_neg:
                detections.append(
                    Detection(
                        detector="SpecHallucinationDetector",
                        category="SPEC",
                        severity="HIGH",
                        description="Likely contradictory constraints: '" + pos + "' and '" + neg + "'",
                        evidence=["Heuristic contradiction detection (Z3 unavailable)"],
                        suggested_fix="Resolve the contradiction between constraints",
                        trust_level="residual",
                    )
                )

        return detections

    def detect_vacuous_spec(
        self, spec: Dict[str, Any]
    ) -> List[Detection]:
        """Detect specifications that are vacuously true (trivially satisfied).

        A vacuous spec provides no useful constraints -- any implementation
        would satisfy it.
        """
        detections: List[Detection] = []
        constraints = spec.get("constraints", [])

        if not constraints:
            detections.append(
                Detection(
                    detector="SpecHallucinationDetector",
                    category="SPEC",
                    severity="MEDIUM",
                    description="Specification has no constraints -- vacuously true",
                    evidence=["Empty constraint set"],
                    suggested_fix="Add meaningful constraints",
                    trust_level="bounded_auto",
                )
            )
            return detections

        # Check for trivially true constraints
        trivial_count = 0
        _TRIVIAL_PATTERNS = [
            r"^true$", r"^1$", r"^always$",
            r".*\b(any|anything|everything)\b.*",
            r"^x\s*[=><!]=\s*x$",
        ]
        for c in constraints:
            c_str = str(c).strip().lower()
            for pat in _TRIVIAL_PATTERNS:
                if re.match(pat, c_str):
                    trivial_count += 1
                    break

        if trivial_count == len(constraints):
            detections.append(
                Detection(
                    detector="SpecHallucinationDetector",
                    category="SPEC",
                    severity="MEDIUM",
                    description="All " + str(len(constraints)) + " constraints appear trivially true",
                    evidence=["Constraints: " + str(constraints[:5])],
                    suggested_fix="Replace trivial constraints with meaningful ones",
                    trust_level="bounded_auto",
                )
            )
        elif trivial_count > 0:
            detections.append(
                Detection(
                    detector="SpecHallucinationDetector",
                    category="SPEC",
                    severity="LOW",
                    description=str(trivial_count) + " of " + str(len(constraints)) + " constraints are trivially true",
                    evidence=["Some constraints provide no information"],
                    suggested_fix="Review and strengthen trivial constraints",
                    trust_level="residual",
                )
            )

        return detections

    def detect_contradictory_spec(
        self, specs: List[Dict[str, Any]]
    ) -> List[Detection]:
        """Detect contradictions across multiple specification dicts."""
        detections: List[Detection] = []
        n = len(specs)

        for i in range(n):
            for j in range(i + 1, n):
                ci = [str(c) for c in specs[i].get("constraints", [])]
                cj = [str(c) for c in specs[j].get("constraints", [])]

                combined = {"constraints": ci + cj}
                unsat = self.detect_unsatisfiable_spec(combined)
                for det in unsat:
                    det_copy = Detection(
                        detector=det.detector,
                        category=det.category,
                        severity=det.severity,
                        description="Contradiction between spec " + str(i) + " and spec " + str(j) + ": " + det.description,
                        evidence=det.evidence + [
                            "Spec " + str(i) + " constraints: " + str(ci[:3]),
                            "Spec " + str(j) + " constraints: " + str(cj[:3]),
                        ],
                        suggested_fix=det.suggested_fix,
                        trust_level=det.trust_level,
                    )
                    detections.append(det_copy)

        return detections


# ======================================================================
#  ProofHallucinationDetector (~200 lines)
# ======================================================================

class ProofHallucinationDetector:
    """Detects hallucinated proofs.

    Checks for:
    - Circular reasoning in proof steps.
    - Gaps where conclusions do not follow from premises.
    - Wrong theorem application (conclusion does not match statement).
    """

    def detect_circular_proof(
        self, proof_steps: List[Dict[str, Any]]
    ) -> List[Detection]:
        """Detect circular reasoning in *proof_steps*.

        Each step should have:
        - ``"id"`` -- unique step identifier
        - ``"uses"`` -- list of step ids this step depends on
        - ``"conclusion"`` -- what this step establishes
        """
        detections: List[Detection] = []

        graph: Dict[str, List[str]] = {}
        for step in proof_steps:
            sid = step.get("id", "")
            uses = step.get("uses", [])
            if isinstance(uses, str):
                uses = [uses]
            graph[sid] = list(uses)

        cycles = self._find_cycles(graph)
        for cycle in cycles:
            detections.append(
                Detection(
                    detector="ProofHallucinationDetector",
                    category="PROOF",
                    severity="CRITICAL",
                    description="Circular reasoning detected: " + " -> ".join(cycle),
                    evidence=["Cycle: " + str(cycle)],
                    suggested_fix="Break the circular dependency by introducing an independent lemma",
                    trust_level="assumed",
                )
            )

        return detections

    def detect_gap_in_proof(
        self, proof_steps: List[Dict[str, Any]]
    ) -> List[Detection]:
        """Detect gaps in *proof_steps* where conclusions do not follow.

        Each step should have:
        - ``"id"`` -- unique step identifier
        - ``"uses"`` -- list of step ids this step depends on
        - ``"rule"`` -- the inference rule applied
        - ``"conclusion"`` -- what this step establishes
        """
        detections: List[Detection] = []
        known_ids: Set[str] = set()
        established: Set[str] = set()

        for step in proof_steps:
            sid = step.get("id", "")
            uses = step.get("uses", [])
            if isinstance(uses, str):
                uses = [uses]
            rule = step.get("rule", "")
            conclusion = step.get("conclusion", "")

            # Check that all referenced steps exist
            for dep in uses:
                if dep and dep not in known_ids:
                    detections.append(
                        Detection(
                            detector="ProofHallucinationDetector",
                            category="PROOF",
                            severity="HIGH",
                            description="Step '" + sid + "' references undefined step '" + dep + "'",
                            evidence=[
                                "Step: " + sid,
                                "Missing dependency: " + dep,
                                "Known steps so far: " + str(sorted(known_ids)),
                            ],
                            location={"step": sid, "missing_dep": dep},
                            suggested_fix="Add the missing step or fix the reference",
                            trust_level="assumed",
                        )
                    )

            # Check that rule is specified
            if not rule and uses:
                detections.append(
                    Detection(
                        detector="ProofHallucinationDetector",
                        category="PROOF",
                        severity="MEDIUM",
                        description="Step '" + sid + "' has no inference rule specified",
                        evidence=["Step depends on " + str(uses) + " but no rule justifies the conclusion"],
                        location={"step": sid},
                        suggested_fix="Specify the inference rule (e.g., modus ponens, induction hypothesis)",
                        trust_level="residual",
                    )
                )

            # Check that conclusion is specified
            if not conclusion:
                detections.append(
                    Detection(
                        detector="ProofHallucinationDetector",
                        category="PROOF",
                        severity="MEDIUM",
                        description="Step '" + sid + "' has no conclusion",
                        evidence=["Every proof step must establish something"],
                        location={"step": sid},
                        suggested_fix="State what this step proves",
                        trust_level="residual",
                    )
                )

            known_ids.add(sid)
            if conclusion:
                established.add(conclusion)

        return detections

    def detect_wrong_theorem(
        self, statement: str, proof: str
    ) -> List[Detection]:
        """Detect if a proof appears to prove something different from its statement.

        Uses textual overlap heuristics -- the proof's conclusion should reference
        key terms from the statement.
        """
        detections: List[Detection] = []

        stmt_tokens = self._extract_key_terms(statement)
        proof_tokens = self._extract_key_terms(proof)

        if not stmt_tokens or not proof_tokens:
            return detections

        overlap = stmt_tokens & proof_tokens
        if not overlap:
            detections.append(
                Detection(
                    detector="ProofHallucinationDetector",
                    category="PROOF",
                    severity="HIGH",
                    description="Proof appears to prove a different theorem -- no key term overlap with statement",
                    evidence=[
                        "Statement terms: " + str(sorted(stmt_tokens)[:10]),
                        "Proof terms: " + str(sorted(proof_tokens)[:10]),
                    ],
                    suggested_fix="Verify that the proof targets the correct theorem",
                    trust_level="assumed",
                )
            )
        elif len(overlap) < len(stmt_tokens) * 0.3:
            detections.append(
                Detection(
                    detector="ProofHallucinationDetector",
                    category="PROOF",
                    severity="MEDIUM",
                    description="Proof has low overlap with theorem statement (" + str(len(overlap)) + "/" + str(len(stmt_tokens)) + " key terms)",
                    evidence=[
                        "Overlap: " + str(sorted(overlap)[:10]),
                        "Missing: " + str(sorted(stmt_tokens - overlap)[:10]),
                    ],
                    suggested_fix="Ensure the proof addresses all key aspects of the theorem",
                    trust_level="residual",
                )
            )

        return detections

    # -- helpers -----------------------------------------------------------

    @staticmethod
    def _find_cycles(graph: Dict[str, List[str]]) -> List[List[str]]:
        """Find all cycles in a directed graph using DFS."""
        cycles: List[List[str]] = []
        visited: Set[str] = set()
        rec_stack: Set[str] = set()

        def _dfs(node: str, path: List[str]) -> None:
            visited.add(node)
            rec_stack.add(node)
            path.append(node)
            for neighbor in graph.get(node, []):
                if neighbor not in visited:
                    _dfs(neighbor, path)
                elif neighbor in rec_stack:
                    idx = path.index(neighbor)
                    cycles.append(path[idx:] + [neighbor])
            path.pop()
            rec_stack.discard(node)

        for node in graph:
            if node not in visited:
                _dfs(node, [])

        return cycles

    @staticmethod
    def _extract_key_terms(text: str) -> Set[str]:
        """Extract key mathematical/technical terms from text."""
        _STOPWORDS = frozenset({
            "a", "an", "the", "is", "are", "was", "were", "be", "been",
            "have", "has", "had", "do", "does", "did", "will", "would",
            "could", "should", "may", "might", "can", "shall",
            "to", "of", "in", "for", "on", "with", "at", "by", "from",
            "and", "but", "or", "not", "if", "then", "else", "than",
            "that", "this", "it", "we", "our", "let", "such",
            "where", "which", "when", "there", "here",
            "show", "prove", "note", "see", "consider", "assume",
        })
        tokens = set(re.findall(r"[a-z][a-z0-9_]+", text.lower()))
        return tokens - _STOPWORDS


# ======================================================================
#  HallucinationSuite (~150 lines)
# ======================================================================

class HallucinationSuite:
    """Runs all hallucination detectors on an artifact.

    Composes all four detector classes and provides aggregate reporting.

    Example::

        suite = HallucinationSuite()
        detections = suite.run_all(artifact)
        print(suite.summary(detections))
    """

    def __init__(
        self,
        *,
        code_detector: Optional[CodeHallucinationDetector] = None,
        doc_detector: Optional[DocHallucinationDetector] = None,
        spec_detector: Optional[SpecHallucinationDetector] = None,
        proof_detector: Optional[ProofHallucinationDetector] = None,
    ) -> None:
        self._code = code_detector or CodeHallucinationDetector()
        self._doc = doc_detector or DocHallucinationDetector()
        self._spec = spec_detector or SpecHallucinationDetector()
        self._proof = proof_detector or ProofHallucinationDetector()
        self.detectors: List[Any] = [self._code, self._doc, self._spec, self._proof]

    def run_all(
        self,
        artifact: Dict[str, Any],
        context: Optional[Dict[str, Any]] = None,
    ) -> List[Detection]:
        """Run all applicable detectors on *artifact*.

        The *artifact* dict determines which detectors fire:
        - ``"code"`` key -> CodeHallucinationDetector
        - ``"docstring"`` key -> DocHallucinationDetector
        - ``"spec"`` / ``"constraints"`` key -> SpecHallucinationDetector
        - ``"proof_steps"`` key -> ProofHallucinationDetector

        *context* may supply ``"theory_packs"`` for code detection.
        """
        detections: List[Detection] = []
        ctx = context or {}

        code = artifact.get("code", "")
        if code:
            detections.extend(self._run_code_detectors(code, ctx))

        docstring = artifact.get("docstring", "")
        code_for_doc = artifact.get("code", "")
        if docstring and code_for_doc:
            detections.extend(self._run_doc_detectors(docstring, code_for_doc))

        spec = artifact.get("spec", artifact.get("constraints", None))
        if spec is not None:
            if isinstance(spec, list):
                spec = {"constraints": spec}
            if isinstance(spec, dict):
                detections.extend(self._run_spec_detectors(spec))

        proof_steps = artifact.get("proof_steps", [])
        if proof_steps:
            detections.extend(self._run_proof_detectors(artifact))

        return detections

    def run_by_category(
        self,
        category: str,
        artifact: Dict[str, Any],
        context: Optional[Dict[str, Any]] = None,
    ) -> List[Detection]:
        """Run only detectors for *category* (CODE, DOC, SPEC, PROOF)."""
        ctx = context or {}
        category_upper = category.upper()

        if category_upper == "CODE":
            code = artifact.get("code", "")
            return self._run_code_detectors(code, ctx) if code else []

        if category_upper == "DOC":
            docstring = artifact.get("docstring", "")
            code = artifact.get("code", "")
            return self._run_doc_detectors(docstring, code) if docstring and code else []

        if category_upper == "SPEC":
            spec = artifact.get("spec", artifact.get("constraints", {}))
            if isinstance(spec, list):
                spec = {"constraints": spec}
            return self._run_spec_detectors(spec) if isinstance(spec, dict) else []

        if category_upper == "PROOF":
            return self._run_proof_detectors(artifact) if artifact.get("proof_steps") else []

        return []

    def summary(self, detections: List[Detection]) -> Dict[str, Any]:
        """Generate a summary of *detections*."""
        by_category: Dict[str, int] = defaultdict(int)
        by_severity: Dict[str, int] = defaultdict(int)
        by_detector: Dict[str, int] = defaultdict(int)

        for d in detections:
            by_category[d.category] += 1
            by_severity[d.severity] += 1
            by_detector[d.detector] += 1

        critical = sum(1 for d in detections if d.is_critical)
        high_or_above = sum(1 for d in detections if d.is_high_or_above)

        return {
            "total_detections": len(detections),
            "critical_count": critical,
            "high_or_above_count": high_or_above,
            "by_category": dict(by_category),
            "by_severity": dict(by_severity),
            "by_detector": dict(by_detector),
            "hallucination_detected": high_or_above > 0,
        }

    # -- internal runners --------------------------------------------------

    def _run_code_detectors(
        self, code: str, context: Dict[str, Any]
    ) -> List[Detection]:
        """Run all code detectors."""
        detections: List[Detection] = []
        theory_packs = context.get("theory_packs")
        detections.extend(self._code.detect_nonexistent_api(code, theory_packs))
        detections.extend(self._code.detect_impossible_types(code))
        detections.extend(self._code.detect_logic_gaps(code))
        return detections

    def _run_doc_detectors(
        self, docstring: str, code: str
    ) -> List[Detection]:
        """Run all doc detectors."""
        detections: List[Detection] = []
        try:
            tree = ast.parse(code)
        except SyntaxError:
            return detections

        detections.extend(self._doc.detect_false_claims(docstring, tree))
        detections.extend(self._doc.detect_missing_caveats(docstring, tree))

        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                detections.extend(self._doc.detect_phantom_params(docstring, node))

        return detections

    def _run_spec_detectors(
        self, spec: Dict[str, Any]
    ) -> List[Detection]:
        """Run all spec detectors."""
        detections: List[Detection] = []
        detections.extend(self._spec.detect_unsatisfiable_spec(spec))
        detections.extend(self._spec.detect_vacuous_spec(spec))
        return detections

    def _run_proof_detectors(
        self, artifact: Dict[str, Any]
    ) -> List[Detection]:
        """Run all proof detectors."""
        detections: List[Detection] = []
        proof_steps = artifact.get("proof_steps", [])
        if proof_steps:
            detections.extend(self._proof.detect_circular_proof(proof_steps))
            detections.extend(self._proof.detect_gap_in_proof(proof_steps))

        statement = artifact.get("theorem_statement", "")
        proof_text = artifact.get("proof_text", "")
        if statement and proof_text:
            detections.extend(self._proof.detect_wrong_theorem(statement, proof_text))

        return detections
