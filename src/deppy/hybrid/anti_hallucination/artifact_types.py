"""Hybrid artifact types for the anti-hallucination type checker (Pillar 4).

This module defines the type system for LLM-generated artifacts in DepPy's
anti-hallucination framework.  Every artifact produced by an LLM — code,
text, data, proofs, configuration — carries a *type* that prescribes a
battery of **structural** and **semantic** checks.  When all checks pass,
the artifact may be promoted through the trust lattice; when any fail, the
framework pinpoints the *kind* of hallucination and suggests remediation.

Mathematical foundations
~~~~~~~~~~~~~~~~~~~~~~~~
The artifact type system forms a fibred category over the trust lattice:

    π : ArtifactType  →  TrustLattice

For each trust level *t*, the fibre π⁻¹(t) contains exactly those artifacts
whose combined check results justify trust ≥ t.  Structural checks are
decidable predicates (Σ-types over the artifact grammar), while semantic
checks are oracle-dependent propositions whose truth is approximated by
LLM judges — modelled as partial elements in a Heyting algebra:

    Structural:  artifact ⊢ P          (decidable, ⊤ or ⊥)
    Semantic:    artifact ⊢ᵒ Q(oracle)  (confidence ∈ [0,1])

The join of all check results determines the artifact's final trust level.
A single FABRICATION failure collapses the trust to ⊥ (CONTRADICTED); less
severe failures (DRIFT, INCONSISTENCY) lower it proportionally.

Lean encoding
~~~~~~~~~~~~~
Each structural check carries a ``lean_prop`` field: a string that encodes
the check as a Lean 4 proposition.  When the hybrid pipeline asks for
formal verification, these propositions are assembled into a single
``theorem artifact_well_formed : P₁ ∧ P₂ ∧ … ∧ Pₙ`` and discharged to
the Lean kernel.  Semantic checks contribute ``axiom``-level declarations
that are trusted only to the degree the oracle warrants.

Usage
~~~~~
::

    code_type = CodeArtifactType()
    results   = code_type.check_structural(some_code_string)
    sem       = code_type.check_semantic(some_code_string, oracle_fn=my_llm)

    if all(r.passed for r in results):
        print("Artifact passes structural checks")
"""
from __future__ import annotations

import ast
import hashlib
import json
import re
import sys
import textwrap
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

if TYPE_CHECKING:
    from deppy.hybrid.core.trust import HybridTrustLevel

# Optional Z3 support — not required for core functionality.
try:
    import z3 as _z3

    _HAS_Z3 = True
except ImportError:
    _z3 = None  # type: ignore[assignment]
    _HAS_Z3 = False


# ═══════════════════════════════════════════════════════════════════
#  §1  Enumerations — artifact and hallucination taxonomies
# ═══════════════════════════════════════════════════════════════════



# --- Integration with existing deppy codebase ---
try:
    from deppy.types.base import TypeBase
    from deppy.types.refinement import RefinementType as _CoreRefinementType
    from deppy.kernel.trust_classifier import TrustClassifier as _CoreTrustClassifier
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

class ArtifactKind(Enum):
    """Classification of LLM-generated artifacts.

    Every artifact entering the anti-hallucination pipeline is tagged with
    exactly one ``ArtifactKind`` so that the correct battery of checks is
    selected.
    """

    CODE = auto()
    TEXT = auto()
    DATA = auto()
    PROOF = auto()
    CONFIG = auto()
    API_CALL = auto()
    DOCUMENTATION = auto()


class HallucinationKind(Enum):
    """Taxonomy of hallucination failure modes.

    The categories form a partial order by severity:

        DRIFT < INCONSISTENCY < STRUCTURAL < SEMANTIC < FABRICATION

    FABRICATION is the most severe — the artifact invents entities that
    have no basis in reality (e.g., a non-existent API).  DRIFT is the
    mildest — the artifact gradually deviates from the specification
    without an identifiable single point of failure.
    """

    STRUCTURAL = auto()
    SEMANTIC = auto()
    FABRICATION = auto()
    INCONSISTENCY = auto()
    DRIFT = auto()

    # -- severity helpers -----------------------------------------------

    @property
    def severity(self) -> int:
        """Return an integer severity score (higher ↔ worse)."""
        return _HALLUCINATION_SEVERITY[self]

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, HallucinationKind):
            return NotImplemented
        return self.severity < other.severity

    def __le__(self, other: object) -> bool:
        if not isinstance(other, HallucinationKind):
            return NotImplemented
        return self.severity <= other.severity


_HALLUCINATION_SEVERITY: Dict[HallucinationKind, int] = {
    HallucinationKind.DRIFT: 1,
    HallucinationKind.INCONSISTENCY: 2,
    HallucinationKind.STRUCTURAL: 3,
    HallucinationKind.SEMANTIC: 4,
    HallucinationKind.FABRICATION: 5,
}


# ═══════════════════════════════════════════════════════════════════
#  §2  Check result — the output of every structural / semantic check
# ═══════════════════════════════════════════════════════════════════


@dataclass
class CheckResult:
    """Result of a single structural or semantic check.

    Attributes
    ----------
    check_name:
        Human-readable identifier matching the originating check.
    passed:
        ``True`` iff the artifact satisfied this check.  For semantic
        checks, this is derived from ``confidence >= threshold``.
    hallucination_kind:
        ``None`` when the check passed; otherwise the category of
        hallucination detected.
    evidence:
        Free-form string describing *why* the check passed or failed.
        Should be concrete enough for a developer to act on.
    confidence:
        ∈ [0, 1].  For structural (decidable) checks this is always
        1.0 (pass) or 0.0 (fail).  Semantic checks report the oracle's
        estimated probability that the property holds.
    trust_level:
        String key into the trust lattice (e.g. ``"LEAN_VERIFIED"``).
        Set by the pipeline after aggregating all results.
    remediation:
        Optional suggestion for fixing the detected hallucination.
    """

    check_name: str
    passed: bool
    hallucination_kind: Optional[HallucinationKind] = None
    evidence: str = ""
    confidence: float = 1.0
    trust_level: str = "UNTRUSTED"
    remediation: Optional[str] = None

    # -- helpers --------------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        """Serialise to a plain dictionary for JSON / logging."""
        return {
            "check_name": self.check_name,
            "passed": self.passed,
            "hallucination_kind": (
                self.hallucination_kind.name if self.hallucination_kind else None
            ),
            "evidence": self.evidence,
            "confidence": self.confidence,
            "trust_level": self.trust_level,
            "remediation": self.remediation,
        }

    def is_error(self) -> bool:
        """Return ``True`` when this result represents a hard failure.

        A hard failure is one whose hallucination kind has severity ≥ 3
        (STRUCTURAL, SEMANTIC, or FABRICATION).
        """
        if self.passed:
            return False
        if self.hallucination_kind is None:
            return True  # unknown failure ⇒ treat as error
        return self.hallucination_kind.severity >= 3

    def __str__(self) -> str:
        mark = "✓" if self.passed else "✗"
        return f"[{mark}] {self.check_name} (confidence={self.confidence:.2f})"


# ═══════════════════════════════════════════════════════════════════
#  §3  StructuralCheck — decidable, purely syntactic / static checks
# ═══════════════════════════════════════════════════════════════════


@dataclass
class StructuralCheck:
    """A decidable property of an artifact, verified without an oracle.

    Structural checks correspond to Σ-types (decidable propositions)
    in the artifact type.  Each check carries:

    * A callable ``check_fn`` that returns ``True`` on success.
    * A ``lean_prop`` string encoding the same property as a Lean 4
      proposition — used when the pipeline escalates to formal verification.
    """

    name: str
    check_fn: Callable[..., Any]
    lean_prop: str = ""
    description: str = ""

    def run(self, artifact: Any) -> CheckResult:
        """Execute the check against *artifact*.

        Returns a :class:`CheckResult` with ``passed=True`` when
        ``check_fn(artifact)`` returns a truthy, non-list value, or an
        empty list.  A non-empty list is interpreted as a list of
        violations and the check fails.
        """
        try:
            result = self.check_fn(artifact)
        except Exception as exc:  # noqa: BLE001
            return CheckResult(
                check_name=self.name,
                passed=False,
                hallucination_kind=HallucinationKind.STRUCTURAL,
                evidence=f"Check raised {type(exc).__name__}: {exc}",
                confidence=0.0,
                trust_level="UNTRUSTED",
                remediation=f"Fix the artifact so that '{self.name}' does not raise.",
            )

        # A list result is interpreted as a list of violations.
        if isinstance(result, list):
            if len(result) == 0:
                return CheckResult(
                    check_name=self.name,
                    passed=True,
                    evidence="No violations found.",
                    confidence=1.0,
                    trust_level="RUNTIME_CHECKED",
                )
            return CheckResult(
                check_name=self.name,
                passed=False,
                hallucination_kind=HallucinationKind.STRUCTURAL,
                evidence=f"Violations: {result}",
                confidence=0.0,
                trust_level="UNTRUSTED",
                remediation=f"Address the following violations: {result}",
            )

        # Boolean / truthy result.
        passed = bool(result)
        return CheckResult(
            check_name=self.name,
            passed=passed,
            hallucination_kind=None if passed else HallucinationKind.STRUCTURAL,
            evidence="Check passed." if passed else "Check failed.",
            confidence=1.0 if passed else 0.0,
            trust_level="RUNTIME_CHECKED" if passed else "UNTRUSTED",
            remediation=None if passed else f"Ensure '{self.name}' is satisfied.",
        )


# ═══════════════════════════════════════════════════════════════════
#  §4  SemanticCheck — oracle-dependent, confidence-scored checks
# ═══════════════════════════════════════════════════════════════════


@dataclass
class SemanticCheck:
    """An oracle-dependent property whose truth is estimated with a
    confidence score.

    Semantic checks model propositions in the Heyting algebra of
    partial truth-values.  The ``prompt_template`` is formatted with
    the artifact and passed to an oracle function (typically an LLM
    judge) which returns a float ∈ [0, 1].

    The ``rubric`` dict provides grading criteria: keys are rubric
    categories (e.g. ``"correctness"``, ``"completeness"``), values
    are short descriptions the oracle should evaluate against.
    """

    name: str
    prompt_template: str = ""
    rubric: Dict[str, str] = field(default_factory=dict)
    confidence_threshold: float = 0.7
    lean_axiom: str = ""

    def build_prompt(self, artifact: Any) -> str:
        """Construct the oracle prompt by inserting the artifact.

        The template may contain ``{artifact}`` and ``{rubric}``
        placeholders.
        """
        rubric_text = "\n".join(
            f"- {key}: {value}" for key, value in self.rubric.items()
        )
        try:
            return self.prompt_template.format(
                artifact=artifact,
                rubric=rubric_text,
            )
        except (KeyError, IndexError):
            # Graceful fallback — include the artifact verbatim.
            return f"{self.prompt_template}\n\nArtifact:\n{artifact}"


# ═══════════════════════════════════════════════════════════════════
#  §5  ArtifactType — base class for all artifact types
# ═══════════════════════════════════════════════════════════════════


@dataclass
class ArtifactType:
    """Base artifact type prescribing structural and semantic checks.

    Subclasses populate ``structural_checks`` and ``semantic_checks``
    in their ``__init__`` or ``__post_init__`` with domain-specific
    predicates.  The base class provides the uniform execution methods
    ``check_structural`` and ``check_semantic``.
    """

    kind: ArtifactKind = ArtifactKind.CODE
    structural_checks: List[StructuralCheck] = field(default_factory=list)
    semantic_checks: List[SemanticCheck] = field(default_factory=list)

    # -- structural execution -------------------------------------------

    def check_structural(self, artifact: Any) -> List[CheckResult]:
        """Run every structural check against *artifact*.

        Returns a list of :class:`CheckResult` objects, one per check,
        in the same order as ``self.structural_checks``.
        """
        results: List[CheckResult] = []
        for check in self.structural_checks:
            results.append(check.run(artifact))
        return results

    # -- semantic execution ---------------------------------------------

    def check_semantic(
        self,
        artifact: Any,
        oracle_fn: Optional[Callable[..., float]] = None,
    ) -> List[CheckResult]:
        """Run every semantic check against *artifact*.

        If *oracle_fn* is ``None``, semantic checks are skipped and
        the returned results all have ``confidence=0.0`` with trust
        level ``"UNTRUSTED"``.

        The *oracle_fn* signature must be::

            oracle_fn(prompt: str) -> float   # confidence ∈ [0, 1]

        Parameters
        ----------
        artifact:
            The artifact to evaluate.
        oracle_fn:
            Callable that accepts a prompt string and returns a
            confidence score in [0, 1].
        """
        results: List[CheckResult] = []
        for sem_check in self.semantic_checks:
            prompt = sem_check.build_prompt(artifact)
            if oracle_fn is None:
                results.append(
                    CheckResult(
                        check_name=sem_check.name,
                        passed=False,
                        hallucination_kind=None,
                        evidence="No oracle provided; semantic check skipped.",
                        confidence=0.0,
                        trust_level="UNTRUSTED",
                    )
                )
                continue

            try:
                confidence = float(oracle_fn(prompt))
            except Exception as exc:  # noqa: BLE001
                results.append(
                    CheckResult(
                        check_name=sem_check.name,
                        passed=False,
                        hallucination_kind=HallucinationKind.SEMANTIC,
                        evidence=f"Oracle raised {type(exc).__name__}: {exc}",
                        confidence=0.0,
                        trust_level="UNTRUSTED",
                    )
                )
                continue

            confidence = max(0.0, min(1.0, confidence))
            passed = confidence >= sem_check.confidence_threshold
            results.append(
                CheckResult(
                    check_name=sem_check.name,
                    passed=passed,
                    hallucination_kind=(
                        None if passed else HallucinationKind.SEMANTIC
                    ),
                    evidence=(
                        f"Oracle confidence {confidence:.3f} "
                        f"(threshold {sem_check.confidence_threshold:.2f})"
                    ),
                    confidence=confidence,
                    trust_level="LLM_JUDGED" if passed else "UNTRUSTED",
                )
            )
        return results

    # -- Lean encoding --------------------------------------------------

    def to_lean_prop(self) -> str:
        """Generate a Lean 4 proposition encoding the structural checks.

        The result is a conjunction of all structural-check propositions::

            P₁ ∧ P₂ ∧ … ∧ Pₙ

        Semantic checks are emitted as ``axiom`` declarations (trusted
        to the oracle's confidence level).
        """
        struct_props = [
            sc.lean_prop for sc in self.structural_checks if sc.lean_prop
        ]
        sem_axioms = [
            sc.lean_axiom for sc in self.semantic_checks if sc.lean_axiom
        ]

        lines: List[str] = []
        lines.append("-- Auto-generated by deppy anti-hallucination pipeline")
        lines.append(f"-- Artifact kind: {self.kind.name}")
        lines.append("")

        if struct_props:
            conj = " ∧ ".join(f"({p})" for p in struct_props)
            lines.append(f"theorem artifact_well_formed : {conj} := by")
            lines.append("  sorry  -- to be discharged by Lean kernel")
        else:
            lines.append("-- No structural propositions to verify.")

        if sem_axioms:
            lines.append("")
            lines.append("-- Semantic axioms (oracle-trusted):")
            for ax in sem_axioms:
                lines.append(f"axiom {ax}")

        return "\n".join(lines)

    # -- content hashing ------------------------------------------------

    @staticmethod
    def content_hash(artifact: Any) -> str:
        """Return a SHA-256 hex digest of *artifact* for oracle caching.

        The artifact is first normalised to a canonical string form:
        * ``str`` / ``bytes`` are used directly.
        * Other types are serialised via ``json.dumps`` with sorted keys,
          falling back to ``repr()`` if JSON serialisation fails.
        """
        if isinstance(artifact, bytes):
            data = artifact
        elif isinstance(artifact, str):
            data = artifact.encode("utf-8")
        else:
            try:
                data = json.dumps(artifact, sort_keys=True).encode("utf-8")
            except (TypeError, ValueError):
                data = repr(artifact).encode("utf-8")
        return hashlib.sha256(data).hexdigest()


# ═══════════════════════════════════════════════════════════════════
#  §6  Code-analysis helpers — standalone functions used by checks
# ═══════════════════════════════════════════════════════════════════


def _safe_parse(code: str) -> Optional[ast.Module]:
    """Attempt to parse *code* as a Python module, returning ``None``
    on failure."""
    try:
        return ast.parse(code)
    except SyntaxError:
        return None


def parses_as_valid_python(code: str) -> bool:
    """Return ``True`` iff *code* is syntactically valid Python.

    Uses :func:`ast.parse` internally; any ``SyntaxError`` is caught
    and treated as a failure.
    """
    return _safe_parse(code) is not None


def all_imports_exist(code: str, known_modules: Optional[Set[str]] = None) -> List[str]:
    """Walk the AST for ``import`` / ``from … import`` statements and
    return a list of module names that are *not* in *known_modules*.

    When *known_modules* is ``None``, the function falls back to
    :data:`sys.stdlib_module_names` (Python 3.10+) plus a hard-coded
    set of common third-party packages.

    Parameters
    ----------
    code:
        Python source code to analyse.
    known_modules:
        Set of module names considered "real".  Top-level names only
        (e.g. ``{"os", "numpy"}``).

    Returns
    -------
    List of module names found in the code that are *not* in *known_modules*.
    An empty list means every import is accounted for.
    """
    if known_modules is None:
        known_modules = _default_known_modules()

    tree = _safe_parse(code)
    if tree is None:
        return ["<entire source failed to parse>"]

    missing: List[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                top = alias.name.split(".")[0]
                if top not in known_modules:
                    missing.append(alias.name)
        elif isinstance(node, ast.ImportFrom):
            if node.module is not None:
                top = node.module.split(".")[0]
                if top not in known_modules:
                    missing.append(node.module)
    return missing


def _default_known_modules() -> Set[str]:
    """Build a reasonable default set of known top-level module names."""
    base: Set[str] = set()
    # Python 3.10+ exposes stdlib_module_names.
    if hasattr(sys, "stdlib_module_names"):
        base |= sys.stdlib_module_names  # type: ignore[attr-defined]
    else:
        # Fallback for 3.9 and earlier — a representative subset.
        base |= {
            "abc", "ast", "asyncio", "base64", "bisect", "builtins",
            "calendar", "cmath", "codecs", "collections", "colorsys",
            "concurrent", "configparser", "contextlib", "copy", "csv",
            "ctypes", "dataclasses", "datetime", "decimal", "difflib",
            "dis", "email", "enum", "errno", "faulthandler", "fileinput",
            "fnmatch", "fractions", "ftplib", "functools", "gc", "getpass",
            "gettext", "glob", "gzip", "hashlib", "heapq", "hmac", "html",
            "http", "imaplib", "importlib", "inspect", "io", "itertools",
            "json", "keyword", "linecache", "locale", "logging", "lzma",
            "math", "mimetypes", "multiprocessing", "numbers", "operator",
            "os", "pathlib", "pickle", "pkgutil", "platform", "pprint",
            "profile", "pstats", "queue", "random", "re", "readline",
            "reprlib", "resource", "secrets", "select", "shelve", "shlex",
            "shutil", "signal", "site", "smtplib", "socket", "sqlite3",
            "ssl", "stat", "statistics", "string", "struct", "subprocess",
            "sys", "syslog", "tempfile", "test", "textwrap", "threading",
            "time", "timeit", "token", "tokenize", "tomllib", "trace",
            "traceback", "tracemalloc", "turtle", "types", "typing",
            "unicodedata", "unittest", "urllib", "uuid", "venv", "warnings",
            "wave", "weakref", "webbrowser", "xml", "xmlrpc", "zipfile",
            "zipimport", "zlib",
        }
    # Common third-party packages.
    base |= {
        "numpy", "np", "pandas", "pd", "scipy", "matplotlib", "plt",
        "sklearn", "torch", "tensorflow", "tf", "requests", "flask",
        "django", "fastapi", "pydantic", "pytest", "setuptools", "pip",
        "click", "typer", "rich", "tqdm", "PIL", "cv2", "yaml", "toml",
        "attrs", "httpx", "aiohttp", "celery", "redis", "sqlalchemy",
        "boto3", "docker", "paramiko", "cryptography", "jwt", "dotenv",
    }
    return base


def all_apis_exist(
    code: str,
    api_registry: Optional[Dict[str, Set[str]]] = None,
) -> List[str]:
    """Walk the AST for attribute access on known modules and return
    a list of hallucinated (non-existent) API calls.

    Parameters
    ----------
    code:
        Python source code.
    api_registry:
        Mapping from module name to its set of known public names.
        E.g. ``{"os": {"path", "getcwd", "listdir"}, ...}``.
        If ``None``, the check is skipped and an empty list is returned
        (since we cannot know what APIs exist without a registry).

    Returns
    -------
    List of ``"module.attr"`` strings that appear in the code but are
    not present in the registry.
    """
    if api_registry is None:
        return []

    tree = _safe_parse(code)
    if tree is None:
        return ["<entire source failed to parse>"]

    # Build alias → module mapping from import statements.
    alias_map: Dict[str, str] = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                key = alias.asname if alias.asname else alias.name
                alias_map[key] = alias.name
        elif isinstance(node, ast.ImportFrom):
            if node.module is not None:
                for alias in node.names:
                    key = alias.asname if alias.asname else alias.name
                    alias_map[key] = f"{node.module}.{alias.name}"

    hallucinated: List[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
            obj_name = node.value.id
            attr_name = node.attr
            module = alias_map.get(obj_name, obj_name)
            top_module = module.split(".")[0]
            if top_module in api_registry:
                known_attrs = api_registry[top_module]
                if attr_name not in known_attrs:
                    hallucinated.append(f"{obj_name}.{attr_name}")
    return hallucinated


def type_annotations_consistent(code: str) -> List[str]:
    """Check that type annotations in *code* parse and reference names
    that are defined or imported within the same source.

    This is a *best-effort* lint, not a full type-checker.  It catches
    common hallucinations such as referencing ``DataFrame`` without
    importing it, or using ``Optoinal`` (typo) as an annotation.

    Returns
    -------
    List of annotation strings that could not be resolved.  An empty
    list means no issues were found.
    """
    tree = _safe_parse(code)
    if tree is None:
        return ["<entire source failed to parse>"]

    # Collect every name defined or imported at module scope.
    defined_names: Set[str] = set()
    # Builtins are always available.
    defined_names |= {
        "int", "float", "str", "bool", "bytes", "list", "dict", "set",
        "tuple", "type", "None", "object", "complex", "frozenset",
        "bytearray", "memoryview", "range", "slice", "property",
        "classmethod", "staticmethod", "super", "Ellipsis",
    }
    # typing generics.
    defined_names |= {
        "Any", "Union", "Optional", "List", "Dict", "Set", "Tuple",
        "FrozenSet", "Sequence", "Mapping", "Iterable", "Iterator",
        "Callable", "Type", "ClassVar", "Final", "Literal",
        "TypeVar", "Generic", "Protocol",
    }

    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                defined_names.add(alias.asname or alias.name.split(".")[0])
        elif isinstance(node, ast.ImportFrom):
            for alias in node.names:
                defined_names.add(alias.asname or alias.name)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            defined_names.add(node.name)
        elif isinstance(node, ast.ClassDef):
            defined_names.add(node.name)
        elif isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    defined_names.add(target.id)
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            defined_names.add(node.target.id)

    # Collect annotation nodes.
    issues: List[str] = []
    annotation_nodes: List[ast.expr] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.returns is not None:
                annotation_nodes.append(node.returns)
            for arg in node.args.args + node.args.posonlyargs + node.args.kwonlyargs:
                if arg.annotation is not None:
                    annotation_nodes.append(arg.annotation)
        elif isinstance(node, ast.AnnAssign) and node.annotation is not None:
            annotation_nodes.append(node.annotation)

    for ann in annotation_nodes:
        _check_annotation_names(ann, defined_names, issues)

    return issues


def _check_annotation_names(
    node: ast.expr,
    defined: Set[str],
    issues: List[str],
) -> None:
    """Recursively check that every :class:`ast.Name` inside an
    annotation node references a name in *defined*."""
    if isinstance(node, ast.Name):
        if node.id not in defined:
            issues.append(node.id)
    elif isinstance(node, ast.Subscript):
        _check_annotation_names(node.value, defined, issues)
        _check_annotation_names(node.slice, defined, issues)
    elif isinstance(node, ast.Attribute):
        pass  # e.g. typing.Optional — we don't resolve dotted names
    elif isinstance(node, ast.Tuple):
        for elt in node.elts:
            _check_annotation_names(elt, defined, issues)
    elif isinstance(node, ast.Constant):
        # String annotations — try to parse and recurse.
        if isinstance(node.value, str):
            try:
                inner = ast.parse(node.value, mode="eval").body
                _check_annotation_names(inner, defined, issues)
            except SyntaxError:
                issues.append(f"unparseable string annotation: {node.value!r}")
    elif isinstance(node, ast.BinOp):
        # Python 3.10+ union syntax: X | Y
        _check_annotation_names(node.left, defined, issues)
        _check_annotation_names(node.right, defined, issues)


def no_undefined_variables(code: str) -> List[str]:
    """Perform a basic scope analysis and return names used before
    definition.

    This is intentionally conservative — it only analyses module-level
    and function-level scopes and will *not* detect all cases that a
    full type checker would.  The goal is to catch obvious LLM
    hallucinations such as referencing a variable that was never
    assigned.

    Returns
    -------
    List of variable names that appear to be used before definition.
    """
    tree = _safe_parse(code)
    if tree is None:
        return ["<entire source failed to parse>"]

    # Collect module-level definitions.
    module_defs: Set[str] = _builtin_names()
    for node in ast.iter_child_nodes(tree):
        _collect_defs(node, module_defs)

    # Now walk function bodies.
    undefined: List[str] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            _check_function_scope(node, module_defs, undefined)

    return undefined


def _builtin_names() -> Set[str]:
    """Return a set of Python built-in names."""
    import builtins
    return set(dir(builtins))


def _collect_defs(node: ast.AST, defs: Set[str]) -> None:
    """Collect names defined by *node* (non-recursive)."""
    if isinstance(node, ast.Import):
        for alias in node.names:
            defs.add(alias.asname or alias.name.split(".")[0])
    elif isinstance(node, ast.ImportFrom):
        for alias in node.names:
            defs.add(alias.asname or alias.name)
    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        defs.add(node.name)
    elif isinstance(node, ast.ClassDef):
        defs.add(node.name)
    elif isinstance(node, ast.Assign):
        for target in node.targets:
            if isinstance(target, ast.Name):
                defs.add(target.id)
    elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
        defs.add(node.target.id)
    elif isinstance(node, ast.For) and isinstance(node.target, ast.Name):
        defs.add(node.target.id)
    elif isinstance(node, ast.With):
        for item in node.items:
            if item.optional_vars and isinstance(item.optional_vars, ast.Name):
                defs.add(item.optional_vars.id)


def _check_function_scope(
    func_node: Union[ast.FunctionDef, ast.AsyncFunctionDef],
    enclosing: Set[str],
    undefined: List[str],
) -> None:
    """Check for undefined variables inside a single function."""
    local_defs: Set[str] = set(enclosing)

    # Function arguments are defined.
    for arg in func_node.args.args:
        local_defs.add(arg.arg)
    for arg in func_node.args.posonlyargs:
        local_defs.add(arg.arg)
    for arg in func_node.args.kwonlyargs:
        local_defs.add(arg.arg)
    if func_node.args.vararg:
        local_defs.add(func_node.args.vararg.arg)
    if func_node.args.kwarg:
        local_defs.add(func_node.args.kwarg.arg)

    # First pass: collect all local definitions.
    for child in ast.walk(func_node):
        _collect_defs(child, local_defs)

    # Second pass: find Name nodes in Load context.
    for child in ast.walk(func_node):
        if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Load):
            if child.id not in local_defs:
                if child.id not in undefined:
                    undefined.append(child.id)


def return_type_matches(code: str, expected: str) -> bool:
    """Check that the *first* function definition in *code* has a
    return annotation matching *expected*.

    Comparison is purely syntactic: the annotation source text
    (unparsed) is compared to *expected* after stripping whitespace.

    Returns ``True`` if the annotation matches, ``False`` otherwise
    (including when no function or no return annotation exists).
    """
    tree = _safe_parse(code)
    if tree is None:
        return False

    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.returns is None:
                return False
            try:
                ann_src = ast.unparse(node.returns)
            except AttributeError:
                # ast.unparse unavailable before Python 3.9
                return False
            return ann_src.strip() == expected.strip()

    return False  # No function found.


# ═══════════════════════════════════════════════════════════════════
#  §7  CodeArtifactType — checks for LLM-generated Python code
# ═══════════════════════════════════════════════════════════════════


class CodeArtifactType(ArtifactType):
    """Artifact type for LLM-generated Python code.

    Structural checks (decidable, ⊤ or ⊥):
    * ``parses_as_valid_python`` — AST-parseable?
    * ``all_imports_exist`` — every import references a real module?
    * ``all_apis_exist`` — every attribute access on a known module is
      a real API entry?
    * ``type_annotations_consistent`` — annotations reference defined names?
    * ``no_undefined_variables`` — no use-before-def in obvious cases?
    * ``return_type_matches`` — first function's return annotation matches?

    Semantic checks (oracle-dependent, confidence ∈ [0, 1]):
    * ``implements_spec`` — does the code implement the given spec?
    * ``no_obvious_bugs`` — is the code free of obvious logical errors?
    * ``complexity_matches`` — is the algorithmic complexity as claimed?

    Lean encoding
    ~~~~~~~~~~~~~
    Each structural check maps to a Lean 4 proposition.  The conjunction
    of all propositions is emitted as a ``theorem`` to be discharged by
    the Lean kernel.  Semantic checks are emitted as ``axiom``
    declarations whose trust level matches the oracle's confidence.
    """

    def __init__(
        self,
        *,
        known_modules: Optional[Set[str]] = None,
        api_registry: Optional[Dict[str, Set[str]]] = None,
        expected_return_type: Optional[str] = None,
        spec: Optional[str] = None,
        claimed_complexity: Optional[str] = None,
    ) -> None:
        self.known_modules = known_modules
        self.api_registry = api_registry
        self.expected_return_type = expected_return_type
        self.spec = spec
        self.claimed_complexity = claimed_complexity

        structural: List[StructuralCheck] = self._build_structural_checks()
        semantic: List[SemanticCheck] = self._build_semantic_checks()

        super().__init__(
            kind=ArtifactKind.CODE,
            structural_checks=structural,
            semantic_checks=semantic,
        )

    # -- structural check builders --------------------------------------

    def _build_structural_checks(self) -> List[StructuralCheck]:
        """Construct the list of structural checks for code artifacts."""
        checks: List[StructuralCheck] = []

        checks.append(StructuralCheck(
            name="parses_as_valid_python",
            check_fn=parses_as_valid_python,
            lean_prop="code_parses_as_valid_python code",
            description="Verify that the generated code is syntactically valid Python.",
        ))

        km = self.known_modules
        checks.append(StructuralCheck(
            name="all_imports_exist",
            check_fn=lambda code: all_imports_exist(code, km),
            lean_prop="∀ m ∈ imports(code), m ∈ known_modules",
            description=(
                "Verify that every import statement references a module "
                "known to exist (stdlib or registered third-party)."
            ),
        ))

        ar = self.api_registry
        checks.append(StructuralCheck(
            name="all_apis_exist",
            check_fn=lambda code: all_apis_exist(code, ar),
            lean_prop="∀ (m, a) ∈ api_calls(code), a ∈ registry(m)",
            description=(
                "Verify that every attribute access on a known module "
                "corresponds to an actually-existing API."
            ),
        ))

        checks.append(StructuralCheck(
            name="type_annotations_consistent",
            check_fn=type_annotations_consistent,
            lean_prop="∀ ann ∈ annotations(code), resolves(ann, scope(code))",
            description=(
                "Verify that type annotations reference names that are "
                "defined or imported in the same source."
            ),
        ))

        checks.append(StructuralCheck(
            name="no_undefined_variables",
            check_fn=no_undefined_variables,
            lean_prop="∀ v ∈ used_vars(code), v ∈ defined_vars(code)",
            description=(
                "Basic scope analysis to detect variables used before "
                "they are defined."
            ),
        ))

        if self.expected_return_type is not None:
            ert = self.expected_return_type
            checks.append(StructuralCheck(
                name="return_type_matches",
                check_fn=lambda code: return_type_matches(code, ert),
                lean_prop=f"return_annotation(code) = \"{ert}\"",
                description=(
                    f"Verify that the first function's return type "
                    f"annotation matches '{ert}'."
                ),
            ))

        return checks

    # -- semantic check builders ----------------------------------------

    def _build_semantic_checks(self) -> List[SemanticCheck]:
        """Construct the list of semantic checks for code artifacts."""
        checks: List[SemanticCheck] = []

        checks.append(self._implements_spec_check())
        checks.append(self._no_obvious_bugs_check())

        if self.claimed_complexity is not None:
            checks.append(self._complexity_matches_check())

        return checks

    @staticmethod
    def _implements_spec_check() -> SemanticCheck:
        """Semantic check: does the code implement its specification?"""
        return SemanticCheck(
            name="implements_spec",
            prompt_template=textwrap.dedent("""\
                You are a code reviewer.  Evaluate whether the following
                code correctly implements the specification described below.

                Code:
                ```python
                {artifact}
                ```

                Rubric:
                {rubric}

                Return a confidence score between 0.0 (clearly wrong) and
                1.0 (clearly correct).
            """),
            rubric={
                "completeness": "Does the code handle all cases in the spec?",
                "correctness": "Are the logic and control flow correct?",
                "edge_cases": "Are boundary conditions handled properly?",
            },
            confidence_threshold=0.7,
            lean_axiom="sem_implements_spec : code_satisfies_spec code spec",
        )

    @staticmethod
    def _no_obvious_bugs_check() -> SemanticCheck:
        """Semantic check: is the code free of obvious bugs?"""
        return SemanticCheck(
            name="no_obvious_bugs",
            prompt_template=textwrap.dedent("""\
                You are a bug-detection expert.  Analyse the following code
                for obvious logical errors, off-by-one mistakes, null/None
                dereferences, or incorrect API usage.

                Code:
                ```python
                {artifact}
                ```

                Rubric:
                {rubric}

                Return a confidence score between 0.0 (definitely has bugs)
                and 1.0 (no bugs found).
            """),
            rubric={
                "logic_errors": "Are there any flawed conditionals or loops?",
                "null_safety": "Could None propagate unexpectedly?",
                "api_misuse": "Are library APIs called with correct arguments?",
                "resource_leaks": "Are files/connections properly closed?",
            },
            confidence_threshold=0.75,
            lean_axiom="sem_no_obvious_bugs : ¬ has_obvious_bugs code",
        )

    def _complexity_matches_check(self) -> SemanticCheck:
        """Semantic check: does the code's complexity match the claim?"""
        cc = self.claimed_complexity or "unknown"
        return SemanticCheck(
            name="complexity_matches",
            prompt_template=textwrap.dedent(f"""\
                You are an algorithm analyst.  Determine whether the
                following code has time complexity {cc}.

                Code:
                ```python
                {{artifact}}
                ```

                Rubric:
                {{rubric}}

                Return a confidence score between 0.0 (clearly not {cc})
                and 1.0 (clearly {cc}).
            """),
            rubric={
                "time_complexity": f"Is the dominant term {cc}?",
                "hidden_costs": "Are there hidden quadratic or worse loops?",
                "data_structure_costs": "Do data structures introduce overhead?",
            },
            confidence_threshold=0.7,
            lean_axiom=f"sem_complexity_matches : complexity code = {cc}",
        )

    # -- convenience wrappers -------------------------------------------

    def check_all(
        self,
        code: str,
        oracle_fn: Optional[Callable[..., float]] = None,
    ) -> List[CheckResult]:
        """Run both structural and semantic checks and return the
        combined results list."""
        return self.check_structural(code) + self.check_semantic(code, oracle_fn)


# ═══════════════════════════════════════════════════════════════════
#  §8  TextArtifactType — checks for LLM-generated prose / text
# ═══════════════════════════════════════════════════════════════════


_CITATION_PATTERN = re.compile(
    r"\[(\d+)\]"           # bracketed number  [1]
    r"|"
    r"\(([A-Z][a-z]+(?:\s+(?:et\s+al\.?|&\s+[A-Z][a-z]+))?,?\s*\d{4})\)"  # (Author, 2023)
)

_JSON_LIKE = re.compile(r"^\s*[\[{]")


def _references_exist(text: str) -> List[str]:
    """Check that inline citations in *text* refer to entries listed in
    a references section (heuristic).

    Looks for ``[N]`` or ``(Author, Year)`` patterns and verifies
    that each number / author appears later in a section whose heading
    contains "reference" or "bibliography" (case-insensitive).

    Returns a list of unresolved citations.
    """
    citations = _CITATION_PATTERN.findall(text)
    if not citations:
        return []

    # Try to find a references block.
    lower = text.lower()
    ref_start = -1
    for marker in ("references", "bibliography", "works cited"):
        idx = lower.rfind(marker)
        if idx != -1:
            ref_start = idx
            break

    if ref_start == -1:
        # No references section — every citation is unresolved.
        unique: List[str] = []
        for groups in citations:
            cite = groups[0] or groups[1]
            if cite and cite not in unique:
                unique.append(cite)
        return unique

    ref_block = text[ref_start:]
    unresolved: List[str] = []
    for groups in citations:
        cite = groups[0] or groups[1]
        if not cite:
            continue
        if cite not in ref_block and cite not in unresolved:
            unresolved.append(cite)
    return unresolved


def _no_self_contradiction(text: str) -> List[str]:
    """Heuristic check for self-contradictions in *text*.

    Looks for explicit negation patterns near repeated claims.
    This is extremely rudimentary — production systems should use an
    NLI model or oracle.  We keep it as a cheap structural pre-filter.

    Returns a list of suspicious sentence pairs.
    """
    sentences = re.split(r"[.!?]+", text)
    sentences = [s.strip() for s in sentences if len(s.strip()) > 10]

    contradictions: List[str] = []
    negation_words = {"not", "never", "no", "neither", "nor", "cannot", "don't",
                      "doesn't", "didn't", "won't", "wouldn't", "shouldn't",
                      "isn't", "aren't", "wasn't", "weren't", "hasn't", "haven't"}

    for i, s1 in enumerate(sentences):
        words1 = set(s1.lower().split())
        for s2 in sentences[i + 1:]:
            words2 = set(s2.lower().split())
            overlap = words1 & words2 - negation_words
            # If two sentences share many words but one has a negation
            # the other lacks, flag it.
            if len(overlap) >= 4:
                neg1 = words1 & negation_words
                neg2 = words2 & negation_words
                if neg1 != neg2 and (neg1 or neg2):
                    contradictions.append(f"'{s1[:60]}…' vs '{s2[:60]}…'")
                    if len(contradictions) >= 5:
                        return contradictions
    return contradictions


def _text_schema_valid(text: str) -> bool:
    """If *text* looks like JSON, verify that it parses.  Otherwise
    return ``True`` (plain text is always schema-valid)."""
    if _JSON_LIKE.match(text):
        try:
            json.loads(text)
        except json.JSONDecodeError:
            return False
    return True


class TextArtifactType(ArtifactType):
    """Artifact type for LLM-generated prose, documentation, or mixed text.

    Structural checks:
    * ``references_exist`` — inline citations have matching references
    * ``no_self_contradiction`` — heuristic self-contradiction detector
    * ``schema_valid`` — if the text looks like JSON, it must parse

    Semantic checks:
    * ``grounded_in_sources`` — claims are supported by cited sources
    * ``accurate_claims`` — factual statements are correct
    * ``no_fabricated_citations`` — cited works actually exist
    """

    def __init__(self) -> None:
        structural = [
            StructuralCheck(
                name="references_exist",
                check_fn=_references_exist,
                lean_prop="∀ c ∈ citations(text), c ∈ references(text)",
                description="Inline citations resolve to a references section.",
            ),
            StructuralCheck(
                name="no_self_contradiction",
                check_fn=_no_self_contradiction,
                lean_prop="¬ ∃ (s₁ s₂ ∈ sentences(text)), contradicts(s₁, s₂)",
                description="No pair of sentences obviously contradicts each other.",
            ),
            StructuralCheck(
                name="schema_valid",
                check_fn=_text_schema_valid,
                lean_prop="is_json(text) → json_parses(text)",
                description="If the text looks like JSON, it must parse.",
            ),
        ]

        semantic = [
            SemanticCheck(
                name="grounded_in_sources",
                prompt_template=textwrap.dedent("""\
                    You are a fact-checker.  Determine whether the claims
                    in the following text are supported by the cited sources.

                    Text:
                    {artifact}

                    Rubric:
                    {rubric}

                    Return a confidence score between 0.0 and 1.0.
                """),
                rubric={
                    "source_support": "Is each claim backed by a citation?",
                    "faithfulness": "Do citations accurately represent their sources?",
                },
                confidence_threshold=0.7,
                lean_axiom="sem_grounded : grounded_in_sources text sources",
            ),
            SemanticCheck(
                name="accurate_claims",
                prompt_template=textwrap.dedent("""\
                    You are a domain expert.  Evaluate the factual accuracy
                    of the following text.

                    Text:
                    {artifact}

                    Rubric:
                    {rubric}

                    Return a confidence score between 0.0 and 1.0.
                """),
                rubric={
                    "factual_correctness": "Are stated facts verifiable and correct?",
                    "numeric_accuracy": "Are numbers, dates, and quantities accurate?",
                    "attribution": "Are ideas attributed to the right people/works?",
                },
                confidence_threshold=0.75,
                lean_axiom="sem_accurate_claims : accurate text",
            ),
            SemanticCheck(
                name="no_fabricated_citations",
                prompt_template=textwrap.dedent("""\
                    You are a citation verifier.  Check whether the
                    following citations refer to real, published works.

                    Text:
                    {artifact}

                    Rubric:
                    {rubric}

                    Return a confidence score between 0.0 and 1.0.
                """),
                rubric={
                    "existence": "Does each cited work actually exist?",
                    "author_match": "Do the authors listed match the real work?",
                    "year_match": "Is the publication year correct?",
                },
                confidence_threshold=0.8,
                lean_axiom="sem_no_fabricated_citations : ∀ c ∈ citations(text), real(c)",
            ),
        ]

        super().__init__(
            kind=ArtifactKind.TEXT,
            structural_checks=structural,
            semantic_checks=semantic,
        )


# ═══════════════════════════════════════════════════════════════════
#  §9  DataArtifactType — checks for LLM-generated data / datasets
# ═══════════════════════════════════════════════════════════════════


def _schema_valid(data: Any, schema: Optional[Dict[str, Any]] = None) -> bool:
    """Validate *data* against a simple dict-based schema.

    Schema format (intentionally minimal — no jsonschema dependency)::

        {
            "type": "dict",          # or "list", "str", "int", "float", "bool"
            "keys": {                # required when type == "dict"
                "name": {"type": "str"},
                "age":  {"type": "int"},
            },
            "items": {"type": "int"},  # required when type == "list"
        }

    Returns ``True`` when the data conforms to the schema.
    """
    if schema is None:
        return True  # No schema ⇒ vacuously valid.

    expected_type = schema.get("type")
    type_map: Dict[str, type] = {
        "dict": dict,
        "list": list,
        "str": str,
        "int": int,
        "float": (int, float),  # type: ignore[dict-item]
        "bool": bool,
    }

    if expected_type and expected_type in type_map:
        if not isinstance(data, type_map[expected_type]):
            return False

    if expected_type == "dict" and isinstance(data, dict):
        key_schemas = schema.get("keys", {})
        for key, sub_schema in key_schemas.items():
            if key not in data:
                return False
            if not _schema_valid(data[key], sub_schema):
                return False

    if expected_type == "list" and isinstance(data, list):
        item_schema = schema.get("items")
        if item_schema:
            for item in data:
                if not _schema_valid(item, item_schema):
                    return False

    return True


def _types_correct(data: Any) -> List[str]:
    """Check that all values in a dict/list structure have consistent
    types across rows (for tabular-like data).

    If *data* is a list of dicts, verify that each key has consistent
    types across all rows.

    Returns a list of type-mismatch descriptions.
    """
    if not isinstance(data, list) or not data:
        return []

    if not all(isinstance(row, dict) for row in data):
        return []

    # data is List[Dict] — check column types.
    column_types: Dict[str, Set[str]] = {}
    for row in data:
        for key, value in row.items():
            col_types = column_types.setdefault(key, set())
            col_types.add(type(value).__name__)

    issues: List[str] = []
    for col, types in column_types.items():
        # Allow int/float coexistence as numeric.
        normalised = types - {"int", "float"} | (
            {"numeric"} if types & {"int", "float"} else set()
        )
        if len(normalised) > 1:
            issues.append(
                f"Column '{col}' has mixed types: {sorted(types)}"
            )
    return issues


def _ranges_plausible(
    data: Any,
    ranges: Optional[Dict[str, Tuple[float, float]]] = None,
) -> List[str]:
    """Check that numeric values in *data* fall within plausible ranges.

    Parameters
    ----------
    data:
        A dict or list of dicts.
    ranges:
        Mapping from key name to ``(min, max)`` tuple.  If ``None``,
        only checks for common implausible values (NaN, Inf).

    Returns
    -------
    List of range-violation descriptions.
    """
    issues: List[str] = []

    rows: List[Dict[str, Any]]
    if isinstance(data, dict):
        rows = [data]
    elif isinstance(data, list):
        rows = [r for r in data if isinstance(r, dict)]
    else:
        return []

    for idx, row in enumerate(rows):
        for key, value in row.items():
            if not isinstance(value, (int, float)):
                continue
            # Check for NaN / Inf.
            if isinstance(value, float) and (
                value != value or value == float("inf") or value == float("-inf")
            ):
                issues.append(f"Row {idx}, key '{key}': value is NaN or Inf")
                continue
            # Check against explicit ranges.
            if ranges and key in ranges:
                lo, hi = ranges[key]
                if value < lo or value > hi:
                    issues.append(
                        f"Row {idx}, key '{key}': {value} outside [{lo}, {hi}]"
                    )

    return issues


class DataArtifactType(ArtifactType):
    """Artifact type for LLM-generated structured data.

    Structural checks:
    * ``schema_valid`` — data conforms to the declared schema
    * ``types_correct`` — column types are consistent across rows
    * ``ranges_plausible`` — numeric values within declared / sane ranges

    Semantic checks:
    * ``values_realistic`` — data values are plausible in context
    * ``no_fabricated_entries`` — entries correspond to real entities
    """

    def __init__(
        self,
        *,
        schema: Optional[Dict[str, Any]] = None,
        ranges: Optional[Dict[str, Tuple[float, float]]] = None,
    ) -> None:
        self._schema = schema
        self._ranges = ranges

        s = self._schema
        r = self._ranges

        structural = [
            StructuralCheck(
                name="schema_valid",
                check_fn=lambda data: _schema_valid(data, s),
                lean_prop="schema_valid data schema",
                description="Data conforms to the declared schema.",
            ),
            StructuralCheck(
                name="types_correct",
                check_fn=_types_correct,
                lean_prop="∀ col ∈ columns(data), consistent_type(col)",
                description="Column types are consistent across rows.",
            ),
            StructuralCheck(
                name="ranges_plausible",
                check_fn=lambda data: _ranges_plausible(data, r),
                lean_prop="∀ (col, v) ∈ numeric_cells(data), lo(col) ≤ v ≤ hi(col)",
                description="Numeric values within declared or sane ranges.",
            ),
        ]

        semantic = [
            SemanticCheck(
                name="values_realistic",
                prompt_template=textwrap.dedent("""\
                    You are a data quality analyst.  Evaluate whether the
                    values in the following dataset are realistic and
                    internally consistent.

                    Data:
                    {artifact}

                    Rubric:
                    {rubric}

                    Return a confidence score between 0.0 and 1.0.
                """),
                rubric={
                    "plausibility": "Are values within realistic ranges?",
                    "internal_consistency": "Are related fields consistent?",
                    "distribution": "Does the data show plausible variance?",
                },
                confidence_threshold=0.7,
                lean_axiom="sem_values_realistic : realistic data",
            ),
            SemanticCheck(
                name="no_fabricated_entries",
                prompt_template=textwrap.dedent("""\
                    You are a data integrity checker.  Determine whether
                    the entries in the following dataset correspond to real
                    entities (people, places, products, etc.) rather than
                    fabricated ones.

                    Data:
                    {artifact}

                    Rubric:
                    {rubric}

                    Return a confidence score between 0.0 and 1.0.
                """),
                rubric={
                    "entity_existence": "Do named entities actually exist?",
                    "relationship_validity": "Are stated relationships real?",
                },
                confidence_threshold=0.8,
                lean_axiom="sem_no_fabricated_entries : ∀ e ∈ entries(data), real(e)",
            ),
        ]

        super().__init__(
            kind=ArtifactKind.DATA,
            structural_checks=structural,
            semantic_checks=semantic,
        )


# ═══════════════════════════════════════════════════════════════════
#  §10 ConfigArtifactType — checks for LLM-generated configuration
# ═══════════════════════════════════════════════════════════════════


def _config_syntax_valid(text: str) -> bool:
    """Try to parse *text* as JSON, then YAML, then TOML.

    Returns ``True`` if at least one parser succeeds.  YAML and TOML
    imports are attempted lazily so the module works without them.
    """
    # JSON
    try:
        json.loads(text)
        return True
    except (json.JSONDecodeError, ValueError):
        pass

    # YAML (optional)
    try:
        import yaml  # type: ignore[import-untyped]
        yaml.safe_load(text)
        return True
    except ImportError:
        pass
    except Exception:  # noqa: BLE001
        pass

    # TOML — Python 3.11+ has tomllib.
    try:
        import tomllib  # type: ignore[import-not-found]
        tomllib.loads(text)
        return True
    except ImportError:
        try:
            import tomli  # type: ignore[import-untyped,import-not-found]
            tomli.loads(text)
            return True
        except ImportError:
            pass
        except Exception:  # noqa: BLE001
            pass
    except Exception:  # noqa: BLE001
        pass

    return False


def _config_parse(text: str) -> Optional[Dict[str, Any]]:
    """Parse *text* into a dict (trying JSON → YAML → TOML).

    Returns ``None`` if no parser succeeds.
    """
    try:
        result = json.loads(text)
        if isinstance(result, dict):
            return result
    except (json.JSONDecodeError, ValueError):
        pass

    try:
        import yaml  # type: ignore[import-untyped]
        result = yaml.safe_load(text)
        if isinstance(result, dict):
            return result
    except ImportError:
        pass
    except Exception:  # noqa: BLE001
        pass

    try:
        import tomllib  # type: ignore[import-not-found]
        result = tomllib.loads(text)
        if isinstance(result, dict):
            return result
    except ImportError:
        try:
            import tomli  # type: ignore[import-untyped,import-not-found]
            result = tomli.loads(text)
            if isinstance(result, dict):
                return result
        except ImportError:
            pass
        except Exception:  # noqa: BLE001
            pass
    except Exception:  # noqa: BLE001
        pass

    return None


def _all_keys_recognised(
    text: str,
    valid_keys: Optional[Set[str]] = None,
) -> List[str]:
    """Parse *text* and return top-level keys that are not in
    *valid_keys*.

    Returns an empty list when *valid_keys* is ``None`` (no schema to
    validate against) or when all keys are recognised.
    """
    if valid_keys is None:
        return []

    parsed = _config_parse(text)
    if parsed is None:
        return ["<config failed to parse>"]

    unknown = [k for k in parsed if k not in valid_keys]
    return unknown


def _values_in_valid_ranges(
    text: str,
    value_ranges: Optional[Dict[str, Tuple[Any, Any]]] = None,
) -> List[str]:
    """Parse *text* and check that values are within declared ranges.

    *value_ranges* maps key names to ``(min, max)`` tuples for numeric
    values.  Non-numeric values are ignored.

    Returns a list of violations.
    """
    if value_ranges is None:
        return []

    parsed = _config_parse(text)
    if parsed is None:
        return ["<config failed to parse>"]

    issues: List[str] = []
    for key, (lo, hi) in value_ranges.items():
        if key in parsed:
            val = parsed[key]
            if isinstance(val, (int, float)):
                if val < lo or val > hi:
                    issues.append(f"Key '{key}': {val} outside [{lo}, {hi}]")
    return issues


class ConfigArtifactType(ArtifactType):
    """Artifact type for LLM-generated configuration files.

    Structural checks:
    * ``valid_syntax`` — parseable as JSON, YAML, or TOML
    * ``all_keys_recognised`` — no unknown top-level keys
    * ``values_in_valid_ranges`` — numeric values within declared ranges

    Semantic checks:
    * ``configuration_sensible`` — settings make sense together
    * ``no_conflicting_settings`` — no mutually exclusive options set
    """

    def __init__(
        self,
        *,
        valid_keys: Optional[Set[str]] = None,
        value_ranges: Optional[Dict[str, Tuple[Any, Any]]] = None,
    ) -> None:
        self._valid_keys = valid_keys
        self._value_ranges = value_ranges

        vk = self._valid_keys
        vr = self._value_ranges

        structural = [
            StructuralCheck(
                name="valid_syntax",
                check_fn=_config_syntax_valid,
                lean_prop="config_parses text",
                description="Configuration text parses as JSON, YAML, or TOML.",
            ),
            StructuralCheck(
                name="all_keys_recognised",
                check_fn=lambda text: _all_keys_recognised(text, vk),
                lean_prop="∀ k ∈ keys(config), k ∈ valid_keys",
                description="All top-level keys are in the recognised set.",
            ),
            StructuralCheck(
                name="values_in_valid_ranges",
                check_fn=lambda text: _values_in_valid_ranges(text, vr),
                lean_prop="∀ (k, v) ∈ config, in_range(k, v)",
                description="Numeric values fall within declared valid ranges.",
            ),
        ]

        semantic = [
            SemanticCheck(
                name="configuration_sensible",
                prompt_template=textwrap.dedent("""\
                    You are a DevOps expert.  Evaluate whether the following
                    configuration is sensible and internally consistent.

                    Configuration:
                    {artifact}

                    Rubric:
                    {rubric}

                    Return a confidence score between 0.0 and 1.0.
                """),
                rubric={
                    "coherence": "Do the settings work well together?",
                    "defaults": "Are non-default values justified?",
                    "security": "Are there insecure settings?",
                },
                confidence_threshold=0.7,
                lean_axiom="sem_config_sensible : sensible config",
            ),
            SemanticCheck(
                name="no_conflicting_settings",
                prompt_template=textwrap.dedent("""\
                    You are a configuration validator.  Check whether any
                    settings in the following configuration are mutually
                    exclusive or contradictory.

                    Configuration:
                    {artifact}

                    Rubric:
                    {rubric}

                    Return a confidence score between 0.0 and 1.0.
                """),
                rubric={
                    "mutual_exclusion": "Are any mutually exclusive options both enabled?",
                    "dependency_satisfaction": "Are required dependencies between options met?",
                },
                confidence_threshold=0.75,
                lean_axiom="sem_no_conflicts : ¬ has_conflicts config",
            ),
        ]

        super().__init__(
            kind=ArtifactKind.CONFIG,
            structural_checks=structural,
            semantic_checks=semantic,
        )


# ═══════════════════════════════════════════════════════════════════
#  §11 ProofArtifactType — checks for LLM-generated formal proofs
# ═══════════════════════════════════════════════════════════════════


_LEAN_KEYWORD_RE = re.compile(
    r"\b(theorem|lemma|def|example|instance|structure|inductive"
    r"|class|namespace|section|variable|axiom|noncomputable"
    r"|open|import|set_option|#check|#eval|sorry|by|where"
    r"|match|fun|let|have|show|suffices|calc|intro|apply"
    r"|exact|rw|simp|ring|omega|linarith|norm_num|decide"
    r"|constructor|cases|induction|rcases|obtain|use"
    r"|contradiction|exfalso|trivial|rfl|congr|ext|funext)\b"
)

_LEAN_TACTIC_BLOCK_RE = re.compile(r"\bby\b")

_LEAN_BRACKET_PAIRS: Dict[str, str] = {
    "(": ")",
    "{": "}",
    "[": "]",
    "⟨": "⟩",
}


def _well_formed_lean_syntax(proof: str) -> bool:
    """Heuristic check for well-formed Lean 4 syntax.

    This is *not* a real Lean parser — it checks:
    1. The text contains at least one Lean keyword.
    2. Brackets are balanced.

    Returns ``True`` when the proof passes these heuristics.
    """
    # Must contain at least one Lean keyword.
    if not _LEAN_KEYWORD_RE.search(proof):
        return False

    # Bracket balance.
    stack: List[str] = []
    for ch in proof:
        if ch in _LEAN_BRACKET_PAIRS:
            stack.append(_LEAN_BRACKET_PAIRS[ch])
        elif ch in _LEAN_BRACKET_PAIRS.values():
            if not stack or stack[-1] != ch:
                return False
            stack.pop()
    return len(stack) == 0


def _all_referenced_lemmas_exist(
    proof: str,
    known_lemmas: Optional[Set[str]] = None,
) -> List[str]:
    """Extract lemma/theorem names referenced in *proof* and return
    those not in *known_lemmas*.

    Heuristic: looks for identifiers following ``apply``, ``exact``,
    ``rw [...,`` etc.  This is a rough approximation — a real
    implementation would use the Lean server.

    Returns a list of unresolved lemma names.
    """
    if known_lemmas is None:
        return []  # No registry ⇒ cannot check.

    # Extract identifiers following tactic keywords.
    ref_pattern = re.compile(
        r"\b(?:apply|exact|rw\s*\[?|simp\s*\[?|have\s+\w+\s*:=\s*)"
        r"\s*([A-Za-z_][A-Za-z0-9_'.]*)"
    )
    referenced = set(ref_pattern.findall(proof))

    # Filter out Lean builtins / tactics.
    lean_builtins = {
        "rfl", "trivial", "sorry", "True", "False", "And", "Or",
        "Not", "Iff", "Eq", "Nat", "Int", "List", "Option", "Prod",
        "Sum", "Fin", "id", "fun", "let", "have", "show",
    }
    referenced -= lean_builtins

    missing = [name for name in sorted(referenced) if name not in known_lemmas]
    return missing


class ProofArtifactType(ArtifactType):
    """Artifact type for LLM-generated formal proofs (Lean 4).

    Structural checks:
    * ``well_formed_lean_syntax`` — basic syntactic well-formedness
    * ``all_referenced_lemmas_exist`` — referenced lemmas are in the library

    Semantic checks:
    * ``proof_strategy_sound`` — oracle judges the overall strategy
    * ``steps_follow_logically`` — each step follows from the previous
    """

    def __init__(
        self,
        *,
        known_lemmas: Optional[Set[str]] = None,
    ) -> None:
        self._known_lemmas = known_lemmas

        kl = self._known_lemmas

        structural = [
            StructuralCheck(
                name="well_formed_lean_syntax",
                check_fn=_well_formed_lean_syntax,
                lean_prop="well_formed_lean proof",
                description=(
                    "Heuristic check that the proof contains Lean keywords "
                    "and has balanced brackets."
                ),
            ),
            StructuralCheck(
                name="all_referenced_lemmas_exist",
                check_fn=lambda proof: _all_referenced_lemmas_exist(proof, kl),
                lean_prop="∀ lem ∈ refs(proof), lem ∈ library",
                description=(
                    "Every lemma/theorem name referenced by tactics "
                    "exists in the known lemma set."
                ),
            ),
        ]

        semantic = [
            SemanticCheck(
                name="proof_strategy_sound",
                prompt_template=textwrap.dedent("""\
                    You are a formal verification expert.  Evaluate whether
                    the following Lean 4 proof uses a sound overall strategy.

                    Proof:
                    {artifact}

                    Rubric:
                    {rubric}

                    Return a confidence score between 0.0 and 1.0.
                """),
                rubric={
                    "strategy": "Is the high-level approach correct?",
                    "completeness": "Does it address all proof obligations?",
                    "sorry_usage": "Are there unjustified 'sorry' uses?",
                },
                confidence_threshold=0.7,
                lean_axiom="sem_strategy_sound : sound_strategy proof",
            ),
            SemanticCheck(
                name="steps_follow_logically",
                prompt_template=textwrap.dedent("""\
                    You are a proof assistant.  Check whether each step
                    in the following Lean 4 proof follows logically from
                    the preceding context.

                    Proof:
                    {artifact}

                    Rubric:
                    {rubric}

                    Return a confidence score between 0.0 and 1.0.
                """),
                rubric={
                    "logical_flow": "Does each tactic step follow from the goal?",
                    "type_correctness": "Are intermediate types correct?",
                    "termination": "Does the proof actually close all goals?",
                },
                confidence_threshold=0.75,
                lean_axiom="sem_steps_logical : ∀ s ∈ steps(proof), logically_follows(s)",
            ),
        ]

        super().__init__(
            kind=ArtifactKind.PROOF,
            structural_checks=structural,
            semantic_checks=semantic,
        )


# ═══════════════════════════════════════════════════════════════════
#  §12 Registry — map ArtifactKind to default ArtifactType instances
# ═══════════════════════════════════════════════════════════════════


_DEFAULT_TYPE_FACTORIES: Dict[ArtifactKind, Callable[..., ArtifactType]] = {
    ArtifactKind.CODE: CodeArtifactType,
    ArtifactKind.TEXT: TextArtifactType,
    ArtifactKind.DATA: DataArtifactType,
    ArtifactKind.CONFIG: ConfigArtifactType,
    ArtifactKind.PROOF: ProofArtifactType,
}


def default_artifact_type(kind: ArtifactKind, **kwargs: Any) -> ArtifactType:
    """Create a default :class:`ArtifactType` for the given *kind*.

    Additional keyword arguments are forwarded to the constructor of
    the concrete artifact-type class.

    Raises :class:`ValueError` for artifact kinds that do not yet have
    a dedicated type (``API_CALL``, ``DOCUMENTATION``).
    """
    factory = _DEFAULT_TYPE_FACTORIES.get(kind)
    if factory is None:
        raise ValueError(
            f"No default artifact type for {kind.name}.  "
            f"Supported kinds: {sorted(k.name for k in _DEFAULT_TYPE_FACTORIES)}"
        )
    return factory(**kwargs)


def run_all_checks(
    artifact: Any,
    kind: ArtifactKind,
    oracle_fn: Optional[Callable[..., float]] = None,
    **kwargs: Any,
) -> List[CheckResult]:
    """Convenience: create the default type for *kind*, run all checks.

    Parameters
    ----------
    artifact:
        The artifact to check.
    kind:
        The artifact kind (determines which checks to run).
    oracle_fn:
        Optional oracle for semantic checks.
    **kwargs:
        Forwarded to :func:`default_artifact_type`.

    Returns
    -------
    Combined list of structural and semantic check results.
    """
    art_type = default_artifact_type(kind, **kwargs)
    structural = art_type.check_structural(artifact)
    semantic = art_type.check_semantic(artifact, oracle_fn)
    return structural + semantic


def summarise_results(results: List[CheckResult]) -> Dict[str, Any]:
    """Produce a summary dict from a list of check results.

    Keys:
    * ``total``: number of checks run
    * ``passed``: number that passed
    * ``failed``: number that failed
    * ``errors``: number of hard errors (severity ≥ 3)
    * ``worst_hallucination``: the highest-severity hallucination kind,
      or ``None`` if all passed
    * ``min_confidence``: the lowest confidence across all results
    * ``results``: list of individual result dicts
    """
    passed = sum(1 for r in results if r.passed)
    failed = len(results) - passed
    errors = sum(1 for r in results if r.is_error())
    confidences = [r.confidence for r in results] if results else [0.0]

    worst: Optional[HallucinationKind] = None
    for r in results:
        if r.hallucination_kind is not None:
            if worst is None or r.hallucination_kind.severity > worst.severity:
                worst = r.hallucination_kind

    return {
        "total": len(results),
        "passed": passed,
        "failed": failed,
        "errors": errors,
        "worst_hallucination": worst.name if worst else None,
        "min_confidence": min(confidences),
        "results": [r.to_dict() for r in results],
    }
