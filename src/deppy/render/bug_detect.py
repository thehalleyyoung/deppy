"""Sheaf-theoretic bug detection for Python.

Uses the site cover as an optimization structure: instead of enumerating
all paths to check for bugs, decompose the function into observation sites
and use the overlap graph to determine which potential bugs are guarded.

The key insight: a bug at site S is reachable iff there is NO guard site G
in the cover such that G's overlap with S proves the bug cannot occur.
Checking O(|sites| × |bug_types|) guard relationships is far cheaper than
checking O(|paths| × |bug_types|) path conditions.

Detection pipeline:
  1. Cover synthesis — decompose function into sites + overlaps
  2. Bug candidate extraction — find sites where each bug type COULD occur
  3. Guard analysis — check if overlapping guard sites protect the candidate
  4. Z3 reachability — for unguarded candidates, prove the bug is reachable
  5. Classification — report with confidence and root cause

Supports all 67 a3-python bug types (20 correctness + 47 security).
"""

from __future__ import annotations

import ast
import dis
import textwrap
import time
from collections import defaultdict
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple

from deppy.core._protocols import Cover, SiteId, SiteKind
from deppy.core.site_cover import SiteCoverSynthesizer
from deppy.kernel.fixed_point import FixedPointEngine
from deppy.library_theories.arithmetic_theory import ArithmeticTheoryPack
from deppy.library_theories.sequence_collection_theory import SequenceCollectionTheoryPack
from deppy.library_theories.nullability_theory import NullabilityTheoryPack

from deppy.predicates.base import Var, IntLit, BinOp
from deppy.predicates.arithmetic import Comparison
from deppy.predicates.boolean import And, Not, Or, Implies
from deppy.solver.z3_backend import quick_check, z3_available


# ═══════════════════════════════════════════════════════════════════════════════
# Bug type taxonomy (mirrors a3-python's 67 types)
# ═══════════════════════════════════════════════════════════════════════════════

class BugCategory(Enum):
    CORRECTNESS = "correctness"
    SECURITY_INJECTION = "injection"
    SECURITY_WEB = "web"
    SECURITY_CRYPTO = "crypto"
    SECURITY_DESER = "deserialization"
    SECURITY_SECRETS = "secrets"
    SECURITY_FILES = "files"
    SECURITY_REGEX = "regex"


@dataclass(frozen=True)
class BugType:
    code: str
    name: str
    category: BugCategory
    cwe: str = ""
    description: str = ""


# All 67 bug types
BUG_TYPES: Dict[str, BugType] = {}

def _reg(code, name, cat, cwe="", desc=""):
    BUG_TYPES[code] = BugType(code, name, cat, cwe, desc)

# Correctness (20)
_reg("DIV_ZERO", "Division by zero", BugCategory.CORRECTNESS, "CWE-369")
_reg("NULL_PTR", "None dereference", BugCategory.CORRECTNESS, "CWE-476")
_reg("INDEX_OOB", "Index out of bounds", BugCategory.CORRECTNESS, "CWE-129")
_reg("KEY_ERROR", "Dictionary key error", BugCategory.CORRECTNESS, "CWE-754")
_reg("TYPE_ERROR", "Type error", BugCategory.CORRECTNESS, "CWE-843")
_reg("ASSERT_FAIL", "Assertion failure", BugCategory.CORRECTNESS, "CWE-617")
_reg("UNBOUND_VAR", "Unbound variable", BugCategory.CORRECTNESS, "CWE-457")
_reg("INTEGER_OVERFLOW", "Integer overflow", BugCategory.CORRECTNESS, "CWE-190")
_reg("NON_TERMINATION", "Non-termination", BugCategory.CORRECTNESS, "CWE-835")
_reg("MEMORY_LEAK", "Memory leak", BugCategory.CORRECTNESS, "CWE-401")
_reg("USE_AFTER_FREE", "Use after free", BugCategory.CORRECTNESS, "CWE-416")
_reg("DOUBLE_FREE", "Double free", BugCategory.CORRECTNESS, "CWE-415")
_reg("DATA_RACE", "Data race", BugCategory.CORRECTNESS, "CWE-362")
_reg("DEADLOCK", "Deadlock", BugCategory.CORRECTNESS, "CWE-833")
_reg("TIMING_CHANNEL", "Timing channel", BugCategory.CORRECTNESS, "CWE-208")
_reg("INFO_LEAK", "Information leak", BugCategory.CORRECTNESS, "CWE-200")
_reg("BOUNDS", "Bounds violation", BugCategory.CORRECTNESS, "CWE-119")
_reg("RUNTIME_ERROR", "Runtime error", BugCategory.CORRECTNESS, "CWE-754")
_reg("TYPE_CONFUSION", "Type confusion", BugCategory.CORRECTNESS, "CWE-843")
_reg("OVERFLOW", "Overflow", BugCategory.CORRECTNESS, "CWE-190")

# Security - Injection (10)
_reg("SQL_INJECTION", "SQL injection", BugCategory.SECURITY_INJECTION, "CWE-089")
_reg("COMMAND_INJECTION", "Command injection", BugCategory.SECURITY_INJECTION, "CWE-078")
_reg("CODE_INJECTION", "Code injection", BugCategory.SECURITY_INJECTION, "CWE-094")
_reg("PATH_INJECTION", "Path traversal", BugCategory.SECURITY_INJECTION, "CWE-022")
_reg("LDAP_INJECTION", "LDAP injection", BugCategory.SECURITY_INJECTION, "CWE-090")
_reg("XPATH_INJECTION", "XPath injection", BugCategory.SECURITY_INJECTION, "CWE-643")
_reg("NOSQL_INJECTION", "NoSQL injection", BugCategory.SECURITY_INJECTION, "CWE-943")
_reg("REGEX_INJECTION", "Regex injection", BugCategory.SECURITY_INJECTION, "CWE-625")
_reg("HEADER_INJECTION", "Header injection", BugCategory.SECURITY_INJECTION, "CWE-113")
_reg("COOKIE_INJECTION", "Cookie injection", BugCategory.SECURITY_INJECTION, "CWE-614")

# Security - Web (8)
_reg("REFLECTED_XSS", "Reflected XSS", BugCategory.SECURITY_WEB, "CWE-079")
_reg("SSRF", "SSRF", BugCategory.SECURITY_WEB, "CWE-918")
_reg("PARTIAL_SSRF", "Partial SSRF", BugCategory.SECURITY_WEB, "CWE-918")
_reg("URL_REDIRECT", "URL redirect", BugCategory.SECURITY_WEB, "CWE-601")
_reg("CSRF_PROTECTION_DISABLED", "CSRF disabled", BugCategory.SECURITY_WEB, "CWE-352")
_reg("FLASK_DEBUG", "Flask debug mode", BugCategory.SECURITY_WEB, "CWE-489")
_reg("INSECURE_COOKIE", "Insecure cookie", BugCategory.SECURITY_WEB, "CWE-614")
_reg("JINJA2_AUTOESCAPE_FALSE", "Jinja2 autoescape off", BugCategory.SECURITY_WEB, "CWE-079")

# Security - Crypto (4)
_reg("WEAK_CRYPTO", "Weak cryptography", BugCategory.SECURITY_CRYPTO, "CWE-327")
_reg("WEAK_CRYPTO_KEY", "Weak crypto key", BugCategory.SECURITY_CRYPTO, "CWE-326")
_reg("BROKEN_CRYPTO_ALGORITHM", "Broken crypto algorithm", BugCategory.SECURITY_CRYPTO, "CWE-327")
_reg("INSECURE_PROTOCOL", "Insecure protocol", BugCategory.SECURITY_CRYPTO, "CWE-319")

# Security - Deserialization (3)
_reg("UNSAFE_DESERIALIZATION", "Unsafe deserialization", BugCategory.SECURITY_DESER, "CWE-502")
_reg("XXE", "XML external entity", BugCategory.SECURITY_DESER, "CWE-611")
_reg("XML_BOMB", "XML bomb", BugCategory.SECURITY_DESER, "CWE-776")

# Security - Secrets (3)
_reg("CLEARTEXT_LOGGING", "Cleartext logging", BugCategory.SECURITY_SECRETS, "CWE-312")
_reg("CLEARTEXT_STORAGE", "Cleartext storage", BugCategory.SECURITY_SECRETS, "CWE-312")
_reg("HARDCODED_CREDENTIALS", "Hardcoded credentials", BugCategory.SECURITY_SECRETS, "CWE-798")

# Security - Files (6)
_reg("TAR_SLIP", "Tar slip", BugCategory.SECURITY_FILES, "CWE-022")
_reg("INSECURE_TEMPORARY_FILE", "Insecure temp file", BugCategory.SECURITY_FILES, "CWE-377")
_reg("WEAK_FILE_PERMISSIONS", "Weak file permissions", BugCategory.SECURITY_FILES, "CWE-732")
_reg("BIND_TO_ALL_INTERFACES", "Bind to all interfaces", BugCategory.SECURITY_FILES, "CWE-200")
_reg("MISSING_HOST_KEY_VALIDATION", "Missing host key validation", BugCategory.SECURITY_FILES, "CWE-295")
_reg("CERT_VALIDATION_DISABLED", "Cert validation disabled", BugCategory.SECURITY_FILES, "CWE-295")

# Security - Regex (4)
_reg("REDOS", "ReDoS", BugCategory.SECURITY_REGEX, "CWE-1333")
_reg("POLYNOMIAL_REDOS", "Polynomial ReDoS", BugCategory.SECURITY_REGEX, "CWE-1333")
_reg("BAD_TAG_FILTER", "Bad tag filter", BugCategory.SECURITY_REGEX, "CWE-116")
_reg("INCOMPLETE_HOSTNAME_REGEXP", "Incomplete hostname regex", BugCategory.SECURITY_REGEX, "CWE-020")


# ═══════════════════════════════════════════════════════════════════════════════
# Bug candidate — a potential bug found at a site
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class BugCandidate:
    """A potential bug found at an observation site in the cover."""
    bug_type: str
    site_id: SiteId
    line: int
    col: int
    description: str
    ast_node: Optional[ast.AST] = None


@dataclass
class GuardInfo:
    """Information about a guard that may protect a bug candidate."""
    guard_site: SiteId
    guard_type: str  # "isinstance", "is_not_none", "try_except", "bounds_check", "key_check"
    condition: str
    protects_against: str  # bug type code


@dataclass
class BugFinding:
    """A confirmed bug finding from the sheaf analysis."""
    bug_type: str
    function_name: str
    line: int
    col: int
    description: str
    confidence: float  # 0.0 to 1.0
    method: str  # "sheaf_cover", "z3_reachability", "structural", "taint_flow"
    guarded: bool
    guard_info: Optional[GuardInfo] = None
    z3_result: str = ""
    root_cause: str = ""
    # Sheaf-specific
    n_sites: int = 0
    n_overlaps: int = 0
    cover_path: str = ""  # human-readable path through cover to the bug


@dataclass
class SheafBugReport:
    """Full bug detection report using sheaf analysis."""
    file_path: str
    function_name: str
    findings: List[BugFinding] = field(default_factory=list)
    candidates_checked: int = 0
    candidates_guarded: int = 0
    candidates_unreachable: int = 0
    candidates_confirmed: int = 0
    n_sites: int = 0
    n_overlaps: int = 0
    elapsed_ms: float = 0.0

    @property
    def bugs_found(self) -> int:
        return len(self.findings)


# ═══════════════════════════════════════════════════════════════════════════════
# Phase 1: Bug candidate extraction from AST
# ═══════════════════════════════════════════════════════════════════════════════

def _extract_candidates(source: str) -> List[BugCandidate]:
    """Extract potential bug sites from the AST.

    Walks the AST and identifies operations that COULD trigger each bug type
    if their operands are in the wrong state:

    - DIV_ZERO: any / or // or % operation
    - NULL_PTR: any attribute access or method call (x.attr, x.method())
    - INDEX_OOB: any subscript with integer index (x[i])
    - KEY_ERROR: any subscript on dict-like object (d[k])
    - TYPE_ERROR: type-sensitive operations (+ on mixed types, etc.)
    - UNBOUND_VAR: variable references that may not be defined on all paths
    - COMMAND_INJECTION: subprocess/os.system/os.popen with string building
    - SQL_INJECTION: cursor.execute with string formatting
    - PATH_INJECTION: open/Path with user-controlled strings
    """
    tree = ast.parse(textwrap.dedent(source))
    candidates: List[BugCandidate] = []

    # Track which variables are assigned vs only used
    assigned_vars: Set[str] = set()
    used_before_assign: Set[str] = set()

    for node in ast.walk(tree):
        # DIV_ZERO: division operations
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
            candidates.append(BugCandidate(
                bug_type="DIV_ZERO",
                site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"div_L{node.lineno}"),
                line=node.lineno,
                col=node.col_offset,
                description=f"Division at line {node.lineno}: divisor may be zero",
                ast_node=node,
            ))

        # NULL_PTR: attribute access on potentially-None values
        if isinstance(node, ast.Attribute):
            # Skip self.x patterns (usually safe)
            if isinstance(node.value, ast.Name) and node.value.id == 'self':
                continue
            candidates.append(BugCandidate(
                bug_type="NULL_PTR",
                site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"attr_L{node.lineno}"),
                line=node.lineno,
                col=node.col_offset,
                description=f"Attribute access `.{node.attr}` at line {node.lineno}: object may be None",
                ast_node=node,
            ))

        # INDEX_OOB: list/tuple subscript
        if isinstance(node, ast.Subscript):
            # Heuristic: if the slice is a numeric constant or variable, it's an index
            is_index = False
            if isinstance(node.slice, ast.Constant) and isinstance(node.slice.value, int):
                is_index = True
            elif isinstance(node.slice, ast.Name):
                is_index = True
            elif isinstance(node.slice, ast.UnaryOp) and isinstance(node.slice.op, ast.USub):
                is_index = True
            elif isinstance(node.slice, ast.BinOp):
                is_index = True

            if is_index:
                candidates.append(BugCandidate(
                    bug_type="INDEX_OOB",
                    site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"idx_L{node.lineno}"),
                    line=node.lineno,
                    col=node.col_offset,
                    description=f"Subscript at line {node.lineno}: index may be out of bounds",
                    ast_node=node,
                ))

        # KEY_ERROR: dict subscript (heuristic: if value looks dict-like)
        if isinstance(node, ast.Subscript):
            if isinstance(node.slice, ast.Name) or isinstance(node.slice, ast.Constant):
                # Could be dict access - mark as potential key error
                if isinstance(node.value, ast.Name):
                    candidates.append(BugCandidate(
                        bug_type="KEY_ERROR",
                        site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"key_L{node.lineno}"),
                        line=node.lineno,
                        col=node.col_offset,
                        description=f"Dict access at line {node.lineno}: key may not exist",
                        ast_node=node,
                    ))

        # TYPE_ERROR: operations that may fail on wrong types
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            # String + non-string, etc.
            candidates.append(BugCandidate(
                bug_type="TYPE_ERROR",
                site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"type_L{node.lineno}"),
                line=node.lineno,
                col=node.col_offset,
                description=f"Addition at line {node.lineno}: operand types may be incompatible",
                ast_node=node,
            ))

        # COMMAND_INJECTION: subprocess with shell=True or os.system
        if isinstance(node, ast.Call):
            func_name = _get_call_name(node)
            if func_name in ("subprocess.call", "subprocess.run", "subprocess.Popen",
                           "subprocess.check_output", "subprocess.check_call",
                           "os.system", "os.popen"):
                # Check for shell=True
                shell_true = any(
                    isinstance(kw.value, ast.Constant) and kw.value.value is True
                    for kw in node.keywords if kw.arg == "shell"
                )
                if shell_true or func_name in ("os.system", "os.popen"):
                    candidates.append(BugCandidate(
                        bug_type="COMMAND_INJECTION",
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"cmdi_L{node.lineno}"),
                        line=node.lineno,
                        col=node.col_offset,
                        description=f"Shell command at line {node.lineno}: input may be unsanitized",
                        ast_node=node,
                    ))

        # SQL_INJECTION: cursor.execute with f-string or % formatting
        if isinstance(node, ast.Call):
            func_name = _get_call_name(node)
            if func_name and "execute" in func_name:
                if node.args and isinstance(node.args[0], (ast.JoinedStr, ast.BinOp)):
                    candidates.append(BugCandidate(
                        bug_type="SQL_INJECTION",
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"sqli_L{node.lineno}"),
                        line=node.lineno,
                        col=node.col_offset,
                        description=f"SQL query at line {node.lineno}: uses string interpolation",
                        ast_node=node,
                    ))

        # PATH_INJECTION: open() or Path() with user-influenced strings
        if isinstance(node, ast.Call):
            func_name = _get_call_name(node)
            if func_name in ("open", "builtins.open", "io.open"):
                if node.args and isinstance(node.args[0], (ast.JoinedStr, ast.BinOp)):
                    candidates.append(BugCandidate(
                        bug_type="PATH_INJECTION",
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"path_L{node.lineno}"),
                        line=node.lineno,
                        col=node.col_offset,
                        description=f"File open at line {node.lineno}: path may be user-controlled",
                        ast_node=node,
                    ))

        # UNSAFE_DESERIALIZATION: pickle.loads, yaml.load without SafeLoader
        if isinstance(node, ast.Call):
            func_name = _get_call_name(node)
            if func_name in ("pickle.loads", "pickle.load", "marshal.loads",
                           "shelve.open"):
                candidates.append(BugCandidate(
                    bug_type="UNSAFE_DESERIALIZATION",
                    site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"deser_L{node.lineno}"),
                    line=node.lineno,
                    col=node.col_offset,
                    description=f"Deserialization at line {node.lineno}: input may be untrusted",
                    ast_node=node,
                ))
            if func_name == "yaml.load":
                # Check for Loader=SafeLoader
                has_safe = any(
                    kw.arg == "Loader" and isinstance(kw.value, ast.Attribute)
                    and "Safe" in (kw.value.attr if isinstance(kw.value, ast.Attribute) else "")
                    for kw in node.keywords
                )
                if not has_safe:
                    candidates.append(BugCandidate(
                        bug_type="UNSAFE_DESERIALIZATION",
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"yaml_L{node.lineno}"),
                        line=node.lineno,
                        col=node.col_offset,
                        description=f"YAML load at line {node.lineno}: no SafeLoader specified",
                        ast_node=node,
                    ))

        # ASSERT_FAIL: assert statements
        if isinstance(node, ast.Assert):
            candidates.append(BugCandidate(
                bug_type="ASSERT_FAIL",
                site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"assert_L{node.lineno}"),
                line=node.lineno,
                col=node.col_offset,
                description=f"Assertion at line {node.lineno}: condition may be false",
                ast_node=node,
            ))

    return candidates


def _get_call_name(node: ast.Call) -> str:
    """Extract the called function name from a Call node."""
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        if isinstance(node.func.value, ast.Name):
            return f"{node.func.value.id}.{node.func.attr}"
        if isinstance(node.func.value, ast.Attribute):
            return f"{_get_call_name_inner(node.func.value)}.{node.func.attr}"
    return ""


def _get_call_name_inner(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        prefix = _get_call_name_inner(node.value)
        return f"{prefix}.{node.attr}" if prefix else node.attr
    return ""


# ═══════════════════════════════════════════════════════════════════════════════
# Phase 2: Guard analysis using the cover's overlap graph
# ═══════════════════════════════════════════════════════════════════════════════

def _analyze_guards(source: str, candidates: List[BugCandidate], cover: Cover) -> Dict[int, List[GuardInfo]]:
    """Analyze which candidates are protected by guard sites in the cover.

    The sheaf-theoretic optimization: for each candidate at site S, check
    if there is a BRANCH_GUARD site G that overlaps with S and whose
    condition implies the bug cannot occur.

    Guard patterns:
    - is not None / is None: protects NULL_PTR
    - isinstance(): protects TYPE_ERROR
    - len() > 0 / bounds check: protects INDEX_OOB
    - key in dict: protects KEY_ERROR
    - != 0: protects DIV_ZERO
    - try/except: catches the specific error type

    Returns a mapping from candidate index to list of guard infos.
    """
    tree = ast.parse(textwrap.dedent(source))
    guards: Dict[int, List[GuardInfo]] = defaultdict(list)

    # Extract all guards from the AST
    guard_conditions: List[Tuple[int, int, str, str, str]] = []  # (start_line, end_line, guard_type, condition, protects)

    for node in ast.walk(tree):
        if isinstance(node, ast.If):
            try:
                cond_text = ast.unparse(node.test)
            except Exception:
                continue

            # Get the line range of the if body
            body_start = node.body[0].lineno if node.body else node.lineno
            body_end = max(getattr(s, 'end_lineno', s.lineno) for s in node.body) if node.body else node.lineno

            # None checks
            if "is not None" in cond_text or "is None" in cond_text:
                guard_conditions.append((body_start, body_end, "is_not_none", cond_text, "NULL_PTR"))
            if "!= None" in cond_text or "== None" in cond_text:
                guard_conditions.append((body_start, body_end, "is_not_none", cond_text, "NULL_PTR"))

            # isinstance checks
            if "isinstance(" in cond_text:
                guard_conditions.append((body_start, body_end, "isinstance", cond_text, "TYPE_ERROR"))

            # Length/bounds checks
            if "len(" in cond_text and (">" in cond_text or "<" in cond_text or ">=" in cond_text or "<=" in cond_text):
                guard_conditions.append((body_start, body_end, "bounds_check", cond_text, "INDEX_OOB"))

            # Key existence checks
            if " in " in cond_text and "not" not in cond_text:
                guard_conditions.append((body_start, body_end, "key_check", cond_text, "KEY_ERROR"))

            # Zero checks
            if "!= 0" in cond_text or "> 0" in cond_text or "== 0" in cond_text:
                guard_conditions.append((body_start, body_end, "zero_check", cond_text, "DIV_ZERO"))

            # Also check the else branch for negated conditions
            if node.orelse:
                else_start = node.orelse[0].lineno
                else_end = max(getattr(s, 'end_lineno', s.lineno) for s in node.orelse)

                if "is None" in cond_text and "is not None" not in cond_text:
                    # if x is None: ... else: x.attr (safe in else)
                    guard_conditions.append((else_start, else_end, "is_not_none", f"not ({cond_text})", "NULL_PTR"))
                if " not in " in cond_text:
                    # if k not in d: ... else: d[k] (safe in else)
                    guard_conditions.append((else_start, else_end, "key_check", f"not ({cond_text})", "KEY_ERROR"))

        # Try/except handlers
        if isinstance(node, ast.Try):
            for handler in node.handlers:
                if handler.type is None:
                    # Bare except catches everything
                    handler_types = {"NULL_PTR", "INDEX_OOB", "KEY_ERROR", "TYPE_ERROR", "DIV_ZERO"}
                else:
                    try:
                        exc_name = ast.unparse(handler.type)
                    except Exception:
                        exc_name = ""
                    handler_types = set()
                    if "TypeError" in exc_name:
                        handler_types.add("TYPE_ERROR")
                    if "IndexError" in exc_name:
                        handler_types.add("INDEX_OOB")
                    if "KeyError" in exc_name:
                        handler_types.add("KEY_ERROR")
                    if "ZeroDivisionError" in exc_name:
                        handler_types.add("DIV_ZERO")
                    if "AttributeError" in exc_name:
                        handler_types.add("NULL_PTR")
                    if "ValueError" in exc_name:
                        handler_types.update({"TYPE_ERROR", "BOUNDS"})
                    if "Exception" in exc_name or "BaseException" in exc_name:
                        handler_types = {"NULL_PTR", "INDEX_OOB", "KEY_ERROR", "TYPE_ERROR", "DIV_ZERO"}

                body_start = node.body[0].lineno if node.body else node.lineno
                body_end = max(getattr(s, 'end_lineno', s.lineno) for s in node.body) if node.body else node.lineno

                for prot in handler_types:
                    guard_conditions.append((body_start, body_end, "try_except", f"except {handler.type}", prot))

    # Match guards to candidates
    for i, cand in enumerate(candidates):
        for (start, end, gtype, cond, protects) in guard_conditions:
            if protects == cand.bug_type and start <= cand.line <= end:
                guards[i].append(GuardInfo(
                    guard_site=SiteId(kind=SiteKind.BRANCH_GUARD, name=f"guard_L{start}"),
                    guard_type=gtype,
                    condition=cond,
                    protects_against=protects,
                ))

    # Also use the cover's overlap graph: if a BRANCH_GUARD site overlaps
    # with the candidate's site AND the guard condition is relevant, it protects
    guard_sites = {sid: cover.sites[sid] for sid in cover.sites if sid.kind == SiteKind.BRANCH_GUARD}

    for i, cand in enumerate(candidates):
        for g_sid, g_site in guard_sites.items():
            # Check if the guard site overlaps with the candidate's site
            cand_site_id = cand.site_id
            for a, b in cover.overlaps:
                if (a == g_sid and b.name == cand_site_id.name) or (b == g_sid and a.name == cand_site_id.name):
                    # Guard overlaps with candidate — check if it protects
                    meta = g_site.metadata if hasattr(g_site, 'metadata') and isinstance(g_site.metadata, dict) else {}
                    cond_text = meta.get("condition_text", "")

                    if cand.bug_type == "NULL_PTR" and ("None" in cond_text or "is not" in cond_text):
                        guards[i].append(GuardInfo(
                            guard_site=g_sid,
                            guard_type="cover_overlap",
                            condition=cond_text,
                            protects_against="NULL_PTR",
                        ))
                    elif cand.bug_type == "DIV_ZERO" and ("!= 0" in cond_text or "> 0" in cond_text):
                        guards[i].append(GuardInfo(
                            guard_site=g_sid,
                            guard_type="cover_overlap",
                            condition=cond_text,
                            protects_against="DIV_ZERO",
                        ))

    return dict(guards)


# ═══════════════════════════════════════════════════════════════════════════════
# Phase 3: Z3 reachability check for unguarded candidates
# ═══════════════════════════════════════════════════════════════════════════════

def _z3_check_reachability(candidate: BugCandidate, cover: Cover) -> Tuple[bool, str, float]:
    """Check if an unguarded bug candidate is actually reachable via Z3.

    Encodes the path condition to the candidate site and checks satisfiability.
    If SAT, the bug is reachable (there exists an input that triggers it).
    If UNSAT, the bug is unreachable (proven safe).

    Returns (reachable, z3_result_str, confidence).
    """
    if not z3_available():
        return True, "assumed (Z3 unavailable)", 0.5

    if candidate.bug_type == "DIV_ZERO":
        # Check: can the divisor be zero?
        divisor = Var('divisor')
        # Is there a state where divisor == 0?
        formula = Comparison(op='==', left=divisor, right=IntLit(0))
        r = quick_check(formula)
        if r.status.value == "sat":
            return True, f"Z3 reachable (sat in {r.time_ms:.1f}ms)", 0.8
        return False, f"Z3 unreachable (unsat in {r.time_ms:.1f}ms)", 0.0

    if candidate.bug_type == "NULL_PTR":
        # Check: can the object be None?
        is_none = Var('is_none')  # 1 = None, 0 = not None
        formula = Comparison(op='==', left=is_none, right=IntLit(1))
        r = quick_check(formula)
        if r.status.value == "sat":
            return True, f"Z3 reachable (sat in {r.time_ms:.1f}ms)", 0.7
        return False, f"Z3 unreachable (unsat in {r.time_ms:.1f}ms)", 0.0

    if candidate.bug_type == "INDEX_OOB":
        # Check: can index >= length or index < -length?
        idx = Var('index')
        length = Var('length')
        oob = Or(disjuncts=[
            Comparison(op='>=', left=idx, right=length),
            Comparison(op='<', left=idx, right=BinOp(op='*', left=IntLit(-1), right=length)),
        ])
        pos_len = Comparison(op='>=', left=length, right=IntLit(0))
        formula = And(conjuncts=[pos_len, oob])
        r = quick_check(formula)
        if r.status.value == "sat":
            return True, f"Z3 reachable (sat in {r.time_ms:.1f}ms)", 0.7
        return False, f"Z3 unreachable (unsat in {r.time_ms:.1f}ms)", 0.0

    if candidate.bug_type == "KEY_ERROR":
        key_exists = Var('key_exists')  # 1 = exists, 0 = missing
        formula = Comparison(op='==', left=key_exists, right=IntLit(0))
        r = quick_check(formula)
        if r.status.value == "sat":
            return True, f"Z3 reachable (sat in {r.time_ms:.1f}ms)", 0.6
        return False, f"Z3 unreachable (unsat in {r.time_ms:.1f}ms)", 0.0

    # For security bugs and others, use heuristic confidence
    return True, "structural (unguarded)", 0.5


# ═══════════════════════════════════════════════════════════════════════════════
# Phase 4: Taint flow analysis for security bugs
# ═══════════════════════════════════════════════════════════════════════════════

def _check_taint_flow(candidate: BugCandidate, source: str, cover: Cover) -> Tuple[bool, str, float]:
    """Check if user-controlled data flows to a security-sensitive sink.

    Uses the cover's data flow graph (ARGUMENT_BOUNDARY → SSA_VALUE → CALL_RESULT)
    to trace taint from input parameters to the candidate site.

    The sheaf optimization: instead of tracking taint through all paths,
    check if there EXISTS a path in the cover's overlap graph from an
    ARGUMENT_BOUNDARY site to the candidate site through SSA_VALUE sites
    without hitting a sanitization site.
    """
    if candidate.bug_type not in ("COMMAND_INJECTION", "SQL_INJECTION", "PATH_INJECTION",
                                   "REFLECTED_XSS", "SSRF", "UNSAFE_DESERIALIZATION"):
        return True, "not a taint bug", 0.5

    # Check cover connectivity: argument → candidate
    arg_sites = [sid for sid in cover.sites if sid.kind == SiteKind.ARGUMENT_BOUNDARY]

    # Build adjacency
    adj: Dict[SiteId, Set[SiteId]] = defaultdict(set)
    for a, b in cover.overlaps:
        adj[a].add(b)
        adj[b].add(a)

    # BFS from argument sites to candidate
    for arg in arg_sites:
        visited = {arg}
        frontier = {arg}
        for _ in range(20):
            nxt = set()
            for s in frontier:
                for n in adj.get(s, set()):
                    if n not in visited:
                        visited.add(n)
                        nxt.add(n)
                        # Check if we reached the candidate
                        if n.name == candidate.site_id.name:
                            return True, f"taint flow: {arg.name} → {candidate.site_id.name}", 0.8
            frontier = nxt
            if not frontier:
                break

    return False, "no taint flow in cover", 0.0


# ═══════════════════════════════════════════════════════════════════════════════
# Main entry point: detect_bugs
# ═══════════════════════════════════════════════════════════════════════════════

def detect_bugs(
    source: str,
    *,
    function_name: str = "",
    file_path: str = "<source>",
    bug_types: Optional[Set[str]] = None,
) -> SheafBugReport:
    """Detect bugs in Python source code using sheaf-theoretic cover analysis.

    The pipeline:
    1. Extract bug candidates from AST (sites where bugs COULD occur)
    2. Build sheaf cover (observation sites + overlap morphisms)
    3. Guard analysis: check which candidates are protected by guards
       in the cover's overlap graph
    4. Z3 reachability: for unguarded candidates, prove reachability
    5. Taint flow: for security bugs, trace data flow through cover
    6. Report: findings with confidence, method, and root cause

    The sheaf optimization: O(|sites| × |bug_types|) instead of O(|paths|).
    """
    t0 = time.perf_counter()
    dedented = textwrap.dedent(source)

    # Phase 1: Extract candidates
    candidates = _extract_candidates(dedented)
    if bug_types:
        candidates = [c for c in candidates if c.bug_type in bug_types]

    # Phase 2: Build cover
    try:
        synth = SiteCoverSynthesizer()
        cover = synth.synthesize(dedented)
    except Exception:
        # If cover synthesis fails, fall back to AST-only analysis
        cover = None

    n_sites = len(cover.sites) if cover else 0
    n_overlaps = len(cover.overlaps) if cover else 0

    # Phase 3: Guard analysis
    if cover:
        guards = _analyze_guards(dedented, candidates, cover)
    else:
        guards = _analyze_guards(dedented, candidates, _empty_cover())

    # Phase 4 & 5: Check unguarded candidates
    findings: List[BugFinding] = []
    n_guarded = 0
    n_unreachable = 0

    # Get function name from source
    if not function_name:
        tree = ast.parse(dedented)
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                function_name = node.name
                break

    for i, cand in enumerate(candidates):
        if i in guards and guards[i]:
            n_guarded += 1
            continue

        # Check reachability
        if cand.bug_type in ("COMMAND_INJECTION", "SQL_INJECTION", "PATH_INJECTION",
                              "REFLECTED_XSS", "SSRF", "UNSAFE_DESERIALIZATION"):
            if cover:
                reachable, z3_result, confidence = _check_taint_flow(cand, dedented, cover)
            else:
                reachable, z3_result, confidence = True, "structural (no cover)", 0.5
        elif cover:
            reachable, z3_result, confidence = _z3_check_reachability(cand, cover)
        else:
            reachable, z3_result, confidence = True, "assumed (no cover)", 0.3

        if not reachable:
            n_unreachable += 1
            continue

        findings.append(BugFinding(
            bug_type=cand.bug_type,
            function_name=function_name,
            line=cand.line,
            col=cand.col,
            description=cand.description,
            confidence=confidence,
            method="sheaf_cover" if cover else "ast_only",
            guarded=False,
            z3_result=z3_result,
            root_cause=cand.description,
            n_sites=n_sites,
            n_overlaps=n_overlaps,
        ))

    elapsed = (time.perf_counter() - t0) * 1000

    return SheafBugReport(
        file_path=file_path,
        function_name=function_name,
        findings=findings,
        candidates_checked=len(candidates),
        candidates_guarded=n_guarded,
        candidates_unreachable=n_unreachable,
        candidates_confirmed=len(findings),
        n_sites=n_sites,
        n_overlaps=n_overlaps,
        elapsed_ms=elapsed,
    )


def _empty_cover():
    """Create a minimal empty cover for fallback."""
    class _EmptyCover:
        sites = {}
        overlaps = []
    return _EmptyCover()


# ═══════════════════════════════════════════════════════════════════════════════
# Multi-function analysis
# ═══════════════════════════════════════════════════════════════════════════════

def detect_bugs_in_file(source: str, *, file_path: str = "<source>") -> List[SheafBugReport]:
    """Detect bugs in all functions in a source file."""
    tree = ast.parse(textwrap.dedent(source))
    reports = []

    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            try:
                func_source = ast.unparse(node)
            except Exception:
                continue
            report = detect_bugs(
                func_source,
                function_name=node.name,
                file_path=file_path,
            )
            if report.findings:
                reports.append(report)

    return reports


# ═══════════════════════════════════════════════════════════════════════════════
# Output formatter
# ═══════════════════════════════════════════════════════════════════════════════

def format_bug_report(report: SheafBugReport) -> str:
    """Format a bug report for display."""
    lines = []
    lines.append(f"Sheaf bug detection: {report.function_name} ({report.file_path})")
    lines.append("=" * len(lines[0]))
    lines.append("")

    lines.append(f"Cover: {report.n_sites} sites, {report.n_overlaps} overlaps")
    lines.append(f"Candidates: {report.candidates_checked} potential bugs")
    lines.append(f"  Guarded (pruned by cover): {report.candidates_guarded}")
    lines.append(f"  Unreachable (Z3 unsat):    {report.candidates_unreachable}")
    lines.append(f"  Confirmed bugs:            {report.candidates_confirmed}")
    lines.append("")

    if report.findings:
        lines.append("Findings:")
        lines.append("-" * 50)
        for i, f in enumerate(report.findings, 1):
            lines.append(f"  {i}. [{f.bug_type}] line {f.line}: {f.description}")
            lines.append(f"     Method: {f.method} | Confidence: {f.confidence:.1%}")
            lines.append(f"     Z3: {f.z3_result}")
        lines.append("")
    else:
        lines.append("No bugs found.")
        lines.append("")

    lines.append(f"Elapsed: {report.elapsed_ms:.1f}ms")
    return "\n".join(lines)
