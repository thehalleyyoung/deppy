"""Sheaf-theoretic bug detection: types as sheaf objects, bugs as gluing obstructions.

The fundamental idea: a Python function defines a presheaf of types over its
observation site cover.  Each site carries a LOCAL TYPE SECTION — a refinement
type describing what values must satisfy at that program point.  A bug exists
precisely when local sections at overlapping sites FAIL TO GLUE into a
consistent global section.

Concretely:
  - At a division site ``a / b``, the divisor site carries the REQUIRED section
    ``{x : int | x ≠ 0}``.  The upstream SSA site carrying ``b`` provides an
    AVAILABLE section (e.g., plain ``int``).  If the restriction map from the
    available section to the required section is not provably total, that
    overlap is a GLUING OBSTRUCTION — a potential division-by-zero bug.

  - A guard ``if b != 0:`` introduces a BRANCH_GUARD site whose section refines
    the available type to ``{x : int | x ≠ 0}``.  This makes the restriction
    map total, resolving the obstruction.

Detection pipeline:
  1. Cover synthesis — build the Grothendieck cover (sites + overlaps)
  2. Section assignment — assign required/available type sections at each site
  3. Gluing audit — for each overlap, check section compatibility
  4. Obstruction extraction — incompatible overlaps are candidate bugs
  5. Z3 discharge — prove obstructions genuine (SAT) or spurious (UNSAT)

Supports all 88 a3-python bug types via type section requirements.
"""

from __future__ import annotations

import ast
import textwrap
import time
from collections import defaultdict
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from deppy.core._protocols import Cover, SiteId, SiteKind, LocalSection, TrustLevel
from deppy.core.site_cover import SiteCoverSynthesizer
from deppy.core.section import SectionFactory, SectionMerger, GlobalSectionBuilder

from deppy.predicates.base import Predicate, Var, IntLit, BinOp, NoneLit, BoolLit, StrLit, Term
from deppy.predicates.arithmetic import Comparison
from deppy.predicates.boolean import And, Not, Or, Implies
from deppy.solver.z3_backend import quick_check, z3_available
from deppy.types.base import (
    TypeBase, PrimitiveType, PrimitiveKind, OptionalType, ListType,
    DictType, INT_TYPE, FLOAT_TYPE, STR_TYPE, BOOL_TYPE, NONE_TYPE, ANY_TYPE,
)
from deppy.types.refinement import RefinementType, refine, NonNull, Positive


# ═══════════════════════════════════════════════════════════════════════════════
# Bug taxonomy — all 88 a3-python types, organized by which sheaf-theoretic
# obstruction pattern they correspond to
# ═══════════════════════════════════════════════════════════════════════════════

class ObstructionFamily(Enum):
    """How the bug manifests as a sheaf gluing failure."""
    REFINEMENT_GAP = "refinement_gap"
    # Available section's refinement does not imply required section's refinement.
    # Examples: DIV_ZERO (need ≠0), INDEX_OOB (need 0≤i<len), NULL_PTR (need ≠None)

    CARRIER_MISMATCH = "carrier_mismatch"
    # Available section's carrier type is incompatible with required carrier.
    # Examples: TYPE_ERROR (str + int), TYPE_CONFUSION

    TAINT_LEAKAGE = "taint_leakage"
    # A tainted (user-controlled) section reaches a sensitive sink without
    # passing through a sanitization site.  The "type" is {x : str | sanitized(x)},
    # and the available section is {x : str | tainted(x)}.
    # Examples: SQL_INJECTION, COMMAND_INJECTION, XSS, SSRF

    PROTOCOL_VIOLATION = "protocol_violation"
    # A section claims a value satisfies a protocol, but the actual implementation
    # is missing required methods.
    # Examples: ITERATOR_PROTOCOL, CONTEXT_MANAGER_PROTOCOL

    RESOURCE_LIFETIME = "resource_lifetime"
    # A section's lifetime (open/closed, allocated/freed) is inconsistent across
    # overlapping sites.
    # Examples: USE_AFTER_FREE, DOUBLE_FREE, MEMORY_LEAK, USE_AFTER_CLOSE

    CONFIGURATION_WEAKNESS = "configuration_weakness"
    # A section at a configuration site carries a value that fails a security
    # policy refinement.
    # Examples: FLASK_DEBUG, WEAK_CRYPTO, INSECURE_COOKIE, CERT_VALIDATION_DISABLED

    EXCEPTION_ESCAPEMENT = "exception_escapement"
    # An error site's viability predicate is not satisfied — the section at the
    # error site says the exception CAN be raised, but no handler site's section
    # covers it.
    # Examples: VALUE_ERROR, RUNTIME_ERROR, FILE_NOT_FOUND


@dataclass(frozen=True)
class BugTypeSpec:
    """Specification of a bug type in sheaf-theoretic terms."""
    code: str
    name: str
    family: ObstructionFamily
    cwe: str = ""
    # The predicate template: given variable names from the AST, produce the
    # REQUIRED refinement predicate that must hold for safety
    required_predicate_desc: str = ""
    # What AST patterns trigger this bug type's section requirement
    ast_triggers: Tuple[str, ...] = ()


# Registry
BUG_SPECS: Dict[str, BugTypeSpec] = {}

def _s(code, name, family, cwe="", pred="", triggers=()):
    BUG_SPECS[code] = BugTypeSpec(code, name, family, cwe, pred, triggers)

# ── Refinement gap bugs (the most common: available type ⊄ required type) ────

_s("DIV_ZERO", "Division by zero", ObstructionFamily.REFINEMENT_GAP,
   "CWE-369", "{divisor : int | divisor ≠ 0}", ("Div", "FloorDiv", "Mod"))
_s("NULL_PTR", "None dereference", ObstructionFamily.REFINEMENT_GAP,
   "CWE-476", "{obj : T | obj is not None}", ("Attribute", "Call"))
_s("INDEX_OOB", "Index out of bounds", ObstructionFamily.REFINEMENT_GAP,
   "CWE-129", "{i : int | 0 ≤ i < len(seq)}", ("Subscript",))
_s("KEY_ERROR", "Dictionary key error", ObstructionFamily.REFINEMENT_GAP,
   "CWE-754", "{k : K | k ∈ keys(d)}", ("Subscript",))
_s("ASSERT_FAIL", "Assertion failure", ObstructionFamily.REFINEMENT_GAP,
   "CWE-617", "{cond : bool | cond is True}", ("Assert",))
_s("BOUNDS", "Bounds violation", ObstructionFamily.REFINEMENT_GAP,
   "CWE-119", "{i : int | lo ≤ i < hi}", ("Subscript",))
_s("INTEGER_OVERFLOW", "Integer overflow", ObstructionFamily.REFINEMENT_GAP,
   "CWE-190", "{x : int | MIN ≤ x ≤ MAX}", ("BinOp",))
_s("FP_DOMAIN", "FP domain error", ObstructionFamily.REFINEMENT_GAP,
   "CWE-369", "{x : float | x ∈ domain(f)}", ("Call",))

# ── Carrier mismatch bugs ────────────────────────────────────────────────────

_s("TYPE_ERROR", "Type error", ObstructionFamily.CARRIER_MISMATCH,
   "CWE-843", "carrier(left) ⊕-compatible carrier(right)", ("BinOp", "Call"))
_s("TYPE_CONFUSION", "Type confusion", ObstructionFamily.CARRIER_MISMATCH,
   "CWE-843", "carrier(actual) <: carrier(expected)", ("Call", "Return"))
_s("UNBOUND_VAR", "Unbound variable", ObstructionFamily.CARRIER_MISMATCH,
   "CWE-457", "carrier(x) ≠ ⊥ (bottom)", ("Name",))

# ── Taint leakage bugs (injection family) ────────────────────────────────────

_s("SQL_INJECTION", "SQL injection", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-089", "{q : str | ¬tainted(q) ∨ parameterized(q)}", ("Call",))
_s("COMMAND_INJECTION", "Command injection", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-078", "{cmd : str | ¬tainted(cmd)}", ("Call",))
_s("CODE_INJECTION", "Code injection", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-094", "{code : str | ¬tainted(code)}", ("Call",))
_s("PATH_INJECTION", "Path traversal", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-022", "{path : str | ¬tainted(path) ∨ sanitized(path)}", ("Call",))
_s("LDAP_INJECTION", "LDAP injection", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-090", "{q : str | ¬tainted(q)}", ("Call",))
_s("XPATH_INJECTION", "XPath injection", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-643", "{q : str | ¬tainted(q)}", ("Call",))
_s("NOSQL_INJECTION", "NoSQL injection", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-943", "{q : Any | ¬tainted(q)}", ("Call",))
_s("REGEX_INJECTION", "Regex injection", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-625", "{pat : str | ¬tainted(pat)}", ("Call",))
_s("HEADER_INJECTION", "Header injection", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-113", "{hdr : str | ¬tainted(hdr)}", ("Call",))
_s("COOKIE_INJECTION", "Cookie injection", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-614", "{val : str | ¬tainted(val)}", ("Call",))
_s("REFLECTED_XSS", "Reflected XSS", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-079", "{html : str | escaped(html)}", ("Call",))
_s("SSRF", "SSRF", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-918", "{url : str | ¬tainted(url) ∨ allowlisted(url)}", ("Call",))
_s("PARTIAL_SSRF", "Partial SSRF", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-918", "{url : str | ¬tainted(url)}", ("Call",))
_s("URL_REDIRECT", "URL redirect", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-601", "{url : str | ¬tainted(url) ∨ allowlisted(url)}", ("Call",))
_s("LOG_INJECTION", "Log injection", ObstructionFamily.TAINT_LEAKAGE,
   "CWE-117", "{msg : str | ¬tainted(msg)}", ("Call",))
_s("UNSAFE_SHELL_COMMAND_CONSTRUCTION", "Unsafe shell command",
   ObstructionFamily.TAINT_LEAKAGE, "CWE-078",
   "{cmd : str | ¬tainted(cmd)}", ("Call",))
_s("UNTRUSTED_DATA_TO_EXTERNAL_API", "Untrusted data to API",
   ObstructionFamily.TAINT_LEAKAGE, "CWE-020",
   "{data : Any | validated(data)}", ("Call",))

# ── Configuration weakness bugs ──────────────────────────────────────────────

_s("WEAK_CRYPTO", "Weak cryptography", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-327", "{algo : str | algo ∈ approved_set}", ("Call",))
_s("WEAK_CRYPTO_KEY", "Weak crypto key", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-326", "{key_size : int | key_size ≥ min_size}", ("Call",))
_s("BROKEN_CRYPTO_ALGORITHM", "Broken crypto", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-327", "{algo : str | algo ∉ broken_set}", ("Call",))
_s("INSECURE_PROTOCOL", "Insecure protocol", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-319", "{proto : str | proto ∈ {https, tls}}", ("Call",))
_s("UNSAFE_DESERIALIZATION", "Unsafe deser", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-502", "{loader : type | loader ∈ safe_loaders}", ("Call",))
_s("XXE", "XML external entity", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-611", "{parser : XMLParser | external_entities_disabled}", ("Call",))
_s("XML_BOMB", "XML bomb", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-776", "{parser : XMLParser | expansion_limit_set}", ("Call",))
_s("FLASK_DEBUG", "Flask debug mode", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-489", "{debug : bool | debug is False (in prod)}", ("Call",))
_s("INSECURE_COOKIE", "Insecure cookie", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-614", "{secure : bool | secure is True}", ("Call",))
_s("JINJA2_AUTOESCAPE_FALSE", "Jinja2 autoescape off",
   ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-079", "{autoescape : bool | autoescape is True}", ("Call",))
_s("CSRF_PROTECTION_DISABLED", "CSRF disabled",
   ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-352", "{csrf : bool | csrf_enabled}", ("Call",))
_s("CLEARTEXT_LOGGING", "Cleartext logging", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-312", "{data : str | ¬sensitive(data)}", ("Call",))
_s("CLEARTEXT_STORAGE", "Cleartext storage", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-312", "{data : str | encrypted(data)}", ("Call",))
_s("HARDCODED_CREDENTIALS", "Hardcoded creds", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-798", "{cred : str | ¬literal(cred)}", ("Assign",))
_s("TAR_SLIP", "Tar slip", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-022", "{member : str | ¬traverses_parent(member)}", ("Call",))
_s("INSECURE_TEMPORARY_FILE", "Insecure temp file",
   ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-377", "{tmpfile : File | created_securely}", ("Call",))
_s("WEAK_FILE_PERMISSIONS", "Weak perms", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-732", "{mode : int | mode & 0o077 == 0}", ("Call",))
_s("BIND_TO_ALL_INTERFACES", "Bind 0.0.0.0", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-200", "{host : str | host ≠ '0.0.0.0'}", ("Call",))
_s("MISSING_HOST_KEY_VALIDATION", "No host key check",
   ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-295", "{policy : HostKeyPolicy | policy ≠ AutoAddPolicy}", ("Call",))
_s("CERT_VALIDATION_DISABLED", "Cert validation off",
   ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-295", "{verify : bool | verify is True}", ("Call",))
_s("REDOS", "ReDoS", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-1333", "{pat : str | ¬super_linear(pat)}", ("Call",))
_s("POLYNOMIAL_REDOS", "Polynomial ReDoS", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-1333", "{pat : str | ¬polynomial_blowup(pat)}", ("Call",))
_s("BAD_TAG_FILTER", "Bad tag filter", ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-116", "{pat : str | complete_tag_match(pat)}", ("Call",))
_s("INCOMPLETE_HOSTNAME_REGEXP", "Incomplete hostname regex",
   ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-020", "{pat : str | anchored(pat)}", ("Call",))
_s("STACK_TRACE_EXPOSURE", "Stack trace exposure",
   ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-209", "{resp : Response | ¬contains_stacktrace(resp)}", ("Call",))
_s("INSECURE_DEFAULT_PROTOCOL", "Insecure default",
   ObstructionFamily.CONFIGURATION_WEAKNESS,
   "CWE-319", "{proto : str | proto ∈ secure_set}", ("Call",))

# ── Resource lifetime bugs ───────────────────────────────────────────────────

_s("USE_AFTER_FREE", "Use after free", ObstructionFamily.RESOURCE_LIFETIME,
   "CWE-416", "lifetime(obj) = ALIVE at use site")
_s("DOUBLE_FREE", "Double free", ObstructionFamily.RESOURCE_LIFETIME,
   "CWE-415", "lifetime(obj) = ALIVE at second free")
_s("MEMORY_LEAK", "Memory leak", ObstructionFamily.RESOURCE_LIFETIME,
   "CWE-401", "∀ alloc sites: ∃ matching free on all paths")
_s("USE_AFTER_CLOSE", "Use after close", ObstructionFamily.RESOURCE_LIFETIME,
   "CWE-416", "state(resource) = OPEN at use site")
_s("DOUBLE_CLOSE", "Double close", ObstructionFamily.RESOURCE_LIFETIME,
   "CWE-415", "state(resource) = OPEN at second close")
_s("MISSING_CLEANUP", "Missing cleanup", ObstructionFamily.RESOURCE_LIFETIME,
   "CWE-404", "∀ open sites: ∃ matching close on all paths")
_s("DATA_RACE", "Data race", ObstructionFamily.RESOURCE_LIFETIME,
   "CWE-362", "lock(obj) held at concurrent access")
_s("DEADLOCK", "Deadlock", ObstructionFamily.RESOURCE_LIFETIME,
   "CWE-833", "¬cyclic(lock_order)")
_s("NON_TERMINATION", "Non-termination", ObstructionFamily.RESOURCE_LIFETIME,
   "CWE-835", "∃ ranking function r : State → ℕ, r decreases each iteration")
_s("STACK_OVERFLOW", "Stack overflow", ObstructionFamily.RESOURCE_LIFETIME,
   "CWE-674", "recursion_depth bounded")
_s("TIMING_CHANNEL", "Timing channel", ObstructionFamily.RESOURCE_LIFETIME,
   "CWE-208", "execution_time independent of secret")
_s("INFO_LEAK", "Information leak", ObstructionFamily.RESOURCE_LIFETIME,
   "CWE-200", "output independent of secret input")

# ── Protocol violation bugs ──────────────────────────────────────────────────

_s("ITERATOR_PROTOCOL", "Iterator protocol", ObstructionFamily.PROTOCOL_VIOLATION,
   pred="has __iter__ and __next__")
_s("CONTEXT_MANAGER_PROTOCOL", "Context manager protocol",
   ObstructionFamily.PROTOCOL_VIOLATION, pred="has __enter__ and __exit__")
_s("DESCRIPTOR_PROTOCOL", "Descriptor protocol", ObstructionFamily.PROTOCOL_VIOLATION,
   pred="has __get__ or __set__")
_s("CALLABLE_PROTOCOL", "Callable protocol", ObstructionFamily.PROTOCOL_VIOLATION,
   pred="has __call__")
_s("ITERATOR_INVALID", "Invalid iterator", ObstructionFamily.PROTOCOL_VIOLATION,
   "CWE-664", "iterator state valid")
_s("SEND_SYNC", "Send/Sync violation", ObstructionFamily.PROTOCOL_VIOLATION,
   pred="thread-safe protocol")
_s("LISKOV_VIOLATION", "Liskov violation", ObstructionFamily.PROTOCOL_VIOLATION,
   pred="subtype preserves parent contract")

# ── Exception escapement bugs ────────────────────────────────────────────────

for _exc, _cwe in [
    ("VALUE_ERROR", ""), ("RUNTIME_ERROR", ""), ("NOT_IMPLEMENTED", ""),
    ("FILE_NOT_FOUND", ""), ("PERMISSION_ERROR", ""), ("OS_ERROR", ""),
    ("IO_ERROR", ""), ("IMPORT_ERROR", ""), ("MODULE_NOT_FOUND", ""),
    ("NAME_ERROR", ""), ("UNBOUND_LOCAL", ""), ("TIMEOUT_ERROR", ""),
    ("CONNECTION_ERROR", ""), ("UNICODE_ERROR", ""), ("LOOKUP_ERROR", ""),
    ("SYSTEM_ERROR", ""), ("ENVIRONMENT_ERROR", ""),
]:
    _s(_exc, f"{_exc} exception", ObstructionFamily.EXCEPTION_ESCAPEMENT,
       _cwe, f"{{op : T | ¬raises({_exc})}}")

# ── Contract bugs (semantic) ─────────────────────────────────────────────────

_s("PRECONDITION_VIOLATION", "Precondition violation",
   ObstructionFamily.REFINEMENT_GAP, pred="caller section ⊆ callee requires")
_s("POSTCONDITION_VIOLATION", "Postcondition violation",
   ObstructionFamily.REFINEMENT_GAP, pred="return section ⊆ ensures")
_s("INVARIANT_VIOLATION", "Invariant violation",
   ObstructionFamily.REFINEMENT_GAP, pred="section satisfies class invariant")
_s("REPRESENTATION_INVARIANT", "Rep invariant violation",
   ObstructionFamily.REFINEMENT_GAP, pred="internal state satisfies rep invariant")

# ── Data flow bugs ───────────────────────────────────────────────────────────

_s("UNVALIDATED_INPUT", "Unvalidated input", ObstructionFamily.TAINT_LEAKAGE,
   pred="{x : T | validated(x)}")
_s("UNCHECKED_RETURN", "Unchecked return", ObstructionFamily.REFINEMENT_GAP,
   pred="{ret : T | ret checked before use}")
_s("IGNORED_EXCEPTION", "Ignored exception", ObstructionFamily.EXCEPTION_ESCAPEMENT,
   pred="exception handled or propagated")
_s("PARTIAL_INIT", "Partial init", ObstructionFamily.REFINEMENT_GAP,
   pred="all fields initialized")
_s("STALE_VALUE", "Stale value", ObstructionFamily.RESOURCE_LIFETIME,
   pred="value is current (not stale)")

# ── Resource exhaustion ──────────────────────────────────────────────────────

_s("MEMORY_EXHAUSTION", "Memory exhaustion", ObstructionFamily.RESOURCE_LIFETIME,
   pred="allocation bounded")
_s("CPU_EXHAUSTION", "CPU exhaustion", ObstructionFamily.RESOURCE_LIFETIME,
   pred="computation bounded")
_s("DISK_EXHAUSTION", "Disk exhaustion", ObstructionFamily.RESOURCE_LIFETIME,
   pred="writes bounded")
_s("HANDLE_EXHAUSTION", "Handle exhaustion", ObstructionFamily.RESOURCE_LIFETIME,
   pred="open handles bounded")

# Also keep some extra mappings
_s("UNINIT_MEMORY", "Uninitialized memory", ObstructionFamily.REFINEMENT_GAP,
   "CWE-457", "{x : T | initialized(x)}")
_s("OVERFLOW", "Overflow", ObstructionFamily.REFINEMENT_GAP,
   "CWE-190", "{x : int | MIN ≤ x ≤ MAX}")
_s("RUNTIME_ERROR_GENERIC", "Runtime error", ObstructionFamily.EXCEPTION_ESCAPEMENT,
   "CWE-754", "{op : T | ¬raises(RuntimeError)}")
_s("CONCURRENT_MODIFICATION", "Concurrent modification",
   ObstructionFamily.RESOURCE_LIFETIME, pred="no concurrent mutation")
_s("ORDER_VIOLATION", "Order violation", ObstructionFamily.RESOURCE_LIFETIME,
   pred="operations in required order")
_s("PAM_AUTHORIZATION_BYPASS", "PAM bypass",
   ObstructionFamily.CONFIGURATION_WEAKNESS, pred="auth check present")
_s("WEAK_SENSITIVE_DATA_HASHING", "Weak hashing",
   ObstructionFamily.CONFIGURATION_WEAKNESS, "CWE-328",
   "{algo : str | algo ∈ strong_hashes}")
_s("OVERLY_LARGE_RANGE", "Overly large range",
   ObstructionFamily.CONFIGURATION_WEAKNESS, pred="range bounded")
_s("INCOMPLETE_URL_SUBSTRING_SANITIZATION", "Incomplete URL sanitization",
   ObstructionFamily.TAINT_LEAKAGE, "CWE-020",
   "{url : str | fully_sanitized(url)}")


# ═══════════════════════════════════════════════════════════════════════════════
# Type section: the sheaf-theoretic core
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class TypeSection:
    """A local type section at an observation site.

    In the presheaf of types F over the site cover, F(U) at site U is a
    refinement type {v : τ | φ(v)}.  The carrier τ is the base Python type;
    the predicate φ captures the refinement constraint.

    A bug at an overlap (U, V) is a failure of the cocycle condition:
    the restriction ρ_{UV} : F(U) → F(V) is not defined because the
    available section at U does not refine to what V requires.
    """
    site_id: SiteId
    carrier: TypeBase          # Base type (int, str, Optional[T], ...)
    predicate: Predicate       # Refinement predicate (the "section coordinate")
    trust: TrustLevel = TrustLevel.RESIDUAL
    provenance: str = ""       # How this section was derived


@dataclass(frozen=True)
class SectionRequirement:
    """What a site REQUIRES from values flowing into it.

    This is the "target" of the restriction map.  If the available section
    at the upstream site cannot be restricted to meet this requirement,
    that's a gluing obstruction (= potential bug).
    """
    site_id: SiteId
    bug_type: str              # Which bug type this requirement guards against
    required_predicate: Predicate  # Must hold for safety
    description: str = ""
    line: int = 0
    col: int = 0
    ast_node: Optional[ast.AST] = None


@dataclass
class GluingObstruction:
    """A failure of the cocycle condition at an overlap.

    When the available section at the upstream site cannot be restricted to
    satisfy the requirement at the downstream site, we have an obstruction.
    This IS the bug, expressed in sheaf-theoretic terms.
    """
    bug_type: str
    requirement: SectionRequirement
    available_section: Optional[TypeSection]
    # The "gap predicate": what's missing for the gluing to work
    # gap = ¬(available_predicate → required_predicate)
    # If gap is SAT, there exists an input triggering the bug
    gap_predicate: Predicate
    # Resolution info
    resolved_by_guard: bool = False
    guard_site: Optional[SiteId] = None
    guard_predicate: Optional[Predicate] = None
    # Z3 result
    z3_status: str = ""
    z3_time_ms: float = 0.0
    confidence: float = 0.0
    line: int = 0
    col: int = 0
    description: str = ""


@dataclass
class SheafBugReport:
    """Full bug detection report using sheaf-theoretic type section analysis."""
    file_path: str
    function_name: str
    # Sheaf structure
    n_sites: int = 0
    n_overlaps: int = 0
    n_requirements: int = 0  # Total section requirements extracted
    n_sections_assigned: int = 0
    # Gluing audit results
    obstructions: List[GluingObstruction] = field(default_factory=list)
    resolved_obstructions: int = 0  # Resolved by guards
    spurious_obstructions: int = 0  # Proved unreachable by Z3
    genuine_obstructions: int = 0   # Confirmed bugs
    elapsed_ms: float = 0.0

    @property
    def bugs_found(self) -> int:
        return self.genuine_obstructions

    @property
    def findings(self) -> List[GluingObstruction]:
        """Genuine (unresolved, reachable) obstructions = confirmed bugs."""
        return [o for o in self.obstructions
                if not o.resolved_by_guard and o.confidence > 0]


# ═══════════════════════════════════════════════════════════════════════════════
# Phase 1: Extract section requirements from AST
#
# Walk the AST and, at each operation that could fail, emit a
# SectionRequirement: the refinement type that the operand must have.
# ═══════════════════════════════════════════════════════════════════════════════

# ═══════════════════════════════════════════════════════════════════════════════
# AST helper predicates — used by requirement extraction
#
# These model fine-grained Python operational semantics as type-theoretic
# constructs: binding presheaves, lifecycle presheaves, ranking functions,
# lock ordering presheaves, and thread-target scoping.
# ═══════════════════════════════════════════════════════════════════════════════


def _is_inside_with(node: ast.AST, tree: ast.AST) -> bool:
    """Check if ``node`` is inside a ``with`` statement body.

    Models the resource lifecycle presheaf: a ``with`` block guarantees that
    the lifecycle section transitions OPEN → CLOSED on all paths (including
    exception paths), so the CLOSE obligation is automatically discharged.
    In sheaf terms, the with-block provides a *global section* of the lifecycle
    presheaf, making any OPEN→CLOSE gluing obstruction trivially resolvable.
    """
    # Build a child→parent map for the AST
    for parent in ast.walk(tree):
        for child in ast.iter_child_nodes(parent):
            if child is node:
                if isinstance(parent, ast.With) or isinstance(parent, ast.AsyncWith):
                    return True
            # Also check grandparents: the node might be nested deeper
            if isinstance(parent, (ast.With, ast.AsyncWith)):
                for desc in ast.walk(parent):
                    if desc is node:
                        return True
    return False


def _extract_loop_var(node: ast.While) -> Optional[str]:
    """Extract the variable being tested in a while-loop's condition.

    Models the ranking presheaf r : State → ℕ. The while-condition defines
    which state variable must decrease.  If the condition is ``n > 0``, the
    ranking function candidate is ``n`` itself.  If the condition is ``True``
    or a complex expression, we return None (no obvious ranking function
    candidate, so the requirement is unconditional).

    In dependent type terms: the loop's well-foundedness is a section of the
    ordinal-valued presheaf over the loop-header site.  If no ranking function
    section can be assigned, the loop's termination is unprovable → obstruction.
    """
    test = node.test
    # while x > 0, while x != 0, while x >= 1, while x
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        if isinstance(test.left, ast.Name):
            return test.left.id
        # while len(lst) > 0
        if isinstance(test.left, ast.Call) and isinstance(test.left.func, ast.Name):
            if test.left.func.id == 'len' and test.left.args:
                return _expr_to_var_name(test.left.args[0], None)
    if isinstance(test, ast.Name):
        return test.id
    # while not done → ranking variable is 'done'
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        if isinstance(test.operand, ast.Name):
            return test.operand.id
    # while True → no ranking variable
    if isinstance(test, ast.Constant) and test.value is True:
        return None
    return None


def _body_modifies_var(body: List[ast.stmt], var: str) -> bool:
    """Check if a loop body modifies the named variable.

    In the ranking presheaf framework, the ranking function r must STRICTLY
    DECREASE at each iteration.  If the body never assigns to the ranking
    variable, r is constant → no well-founded descent → non-termination
    obstruction.

    We check for:
    - Direct assignment: ``var = ...``
    - Augmented assignment: ``var += ...``, ``var -= ...``
    - Function calls that might modify via aliasing (conservative: any call
      with var as argument)
    """
    for stmt in body:
        for node in ast.walk(stmt):
            # Direct assignment
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name) and target.id == var:
                        return True
            # Augmented assignment (+=, -=, etc.)
            if isinstance(node, ast.AugAssign):
                if isinstance(node.target, ast.Name) and node.target.id == var:
                    return True
            # del var
            if isinstance(node, ast.Delete):
                for target in node.targets:
                    if isinstance(target, ast.Name) and target.id == var:
                        return True
            # Method calls that mutate: var.pop(), var.remove(), var.append() etc.
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                obj = node.func.value
                if isinstance(obj, ast.Name) and obj.id == var:
                    if node.func.attr in ('pop', 'remove', 'clear', 'append',
                                           'extend', 'insert', 'discard'):
                        return True
    return False


def _body_modifies_var_correctly(body: List[ast.stmt], var: str,
                                  loop_test: ast.AST) -> bool:
    """Check whether the loop body modifies ``var`` in the correct direction.

    In sheaf-theoretic terms, a ranking presheaf section must STRICTLY decrease
    along the site refinement order.  If ``while n > 0: n += 1``, the body
    modifies ``n`` but INCREASES it — the ranking function does not descend,
    so termination remains unprovable → obstruction.

    Returns True only if the modification direction is consistent with the
    loop condition (e.g. ``-=`` when condition is ``> 0``).
    """
    # Determine expected direction from loop condition
    expects_decrease = False
    expects_increase = False
    if isinstance(loop_test, ast.Compare) and len(loop_test.ops) == 1:
        op = loop_test.ops[0]
        if isinstance(op, (ast.Gt, ast.GtE)):
            expects_decrease = True  # while n > 0 → need n to decrease
        elif isinstance(op, (ast.Lt, ast.LtE)):
            expects_increase = True  # while n < limit → need n to increase

    if not expects_decrease and not expects_increase:
        return True  # can't determine direction → assume OK

    for stmt in body:
        for node in ast.walk(stmt):
            if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
                if node.target.id == var:
                    if isinstance(node.op, ast.Sub) and expects_decrease:
                        return True
                    if isinstance(node.op, ast.Add) and expects_increase:
                        return True
                    if isinstance(node.op, ast.Add) and expects_decrease:
                        return False  # wrong direction
                    if isinstance(node.op, ast.Sub) and expects_increase:
                        return False
    return True  # no AugAssign → can't tell, assume correct


def _is_inside_thread_target(node: ast.AST, tree: ast.AST) -> bool:
    """Check if ``node`` is inside a function passed as a threading.Thread target.

    Models the synchronization presheaf L : Sites → P(Locks).  Code inside
    a thread target executes concurrently with the spawner, so shared-object
    mutations without lock acquisition create a gluing obstruction: the
    synchronization section at the mutation site requires lock_held = True,
    but no lock-acquisition site provides that section.

    Detection: look for functions defined in the module that are referenced
    as ``target=func_name`` in a ``threading.Thread(...)`` call. Then check
    if ``node`` is inside such a function.
    """
    # Step 1: find all functions used as thread targets
    thread_target_names: Set[str] = set()
    for n in ast.walk(tree):
        if isinstance(n, ast.Call):
            func_name = _get_call_name(n)
            if 'Thread' in func_name:
                for kw in n.keywords:
                    if kw.arg == 'target' and isinstance(kw.value, ast.Name):
                        thread_target_names.add(kw.value.id)

    if not thread_target_names:
        return False

    # Step 2: check if node is inside one of those functions
    for func_def in ast.walk(tree):
        if isinstance(func_def, ast.FunctionDef) and func_def.name in thread_target_names:
            for desc in ast.walk(func_def):
                if desc is node:
                    return True

    return False


def _binding_analysis(tree: ast.AST) -> List[SectionRequirement]:
    """Analyze Python's LEGB scoping as a binding presheaf Γ : Sites → Env.

    The binding presheaf assigns to each site U the set of variables that are
    DEFINITELY bound at that point.  Formally:

        Γ(U) = {x ∈ Var | all control-flow paths to U include an assignment to x}

    A Name reference ``x`` at site U requires x ∈ dom(Γ(U)).  If x is only
    conditionally bound (assigned in one branch but not another), then the
    restriction map from the branch-site to the use-site is PARTIAL — the
    section doesn't glue, producing a BINDING_GAP obstruction.

    This models Python's operational semantics precisely: UnboundLocalError
    occurs at runtime when a name lookup finds no binding in the local scope.

    Algorithm:
    1. Collect all assignment targets (unconditional and conditional).
    2. For each Name reference, check if all paths to it include a binding.
    3. Conditional bindings (inside if/elif/else/try) are partial sections;
       they only cover part of the site cover.
    """
    reqs: List[SectionRequirement] = []

    for func_node in ast.walk(tree):
        if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue

        # Parameter names are unconditionally bound at function entry
        unconditional: Set[str] = set()
        for arg in func_node.args.args:
            unconditional.add(arg.arg)
        for arg in func_node.args.posonlyargs:
            unconditional.add(arg.arg)
        for arg in func_node.args.kwonlyargs:
            unconditional.add(arg.arg)
        if func_node.args.vararg:
            unconditional.add(func_node.args.vararg.arg)
        if func_node.args.kwarg:
            unconditional.add(func_node.args.kwarg.arg)

        # Walk the body to find all assignments
        # Track which are UNCONDITIONAL (in the main body) vs CONDITIONAL (in branches)
        conditional: Set[str] = set()
        all_used: List[Tuple[str, int, int, ast.AST]] = []  # (name, line, col, node)

        def _scan_body(stmts: List[ast.stmt], in_branch: bool = False) -> None:
            for stmt in stmts:
                # Assignment
                if isinstance(stmt, ast.Assign):
                    for target in stmt.targets:
                        if isinstance(target, ast.Name):
                            if in_branch:
                                conditional.add(target.id)
                            else:
                                unconditional.add(target.id)
                if isinstance(stmt, ast.AugAssign):
                    if isinstance(stmt.target, ast.Name):
                        if in_branch:
                            conditional.add(stmt.target.id)
                        else:
                            unconditional.add(stmt.target.id)
                # For loop variable
                if isinstance(stmt, ast.For):
                    target = stmt.target
                    if isinstance(target, ast.Name):
                        # For loop binding is conditional (loop might not execute)
                        conditional.add(target.id)
                    _scan_body(stmt.body, in_branch=True)
                    _scan_body(stmt.orelse, in_branch=True)
                # If branches: all bindings inside are conditional
                if isinstance(stmt, ast.If):
                    _scan_body(stmt.body, in_branch=True)
                    _scan_body(stmt.orelse, in_branch=True)
                # With statement
                if isinstance(stmt, (ast.With, ast.AsyncWith)):
                    for item in stmt.items:
                        if item.optional_vars and isinstance(item.optional_vars, ast.Name):
                            unconditional.add(item.optional_vars.id)
                    _scan_body(stmt.body, in_branch=in_branch)
                # Try
                if isinstance(stmt, ast.Try):
                    _scan_body(stmt.body, in_branch=True)
                    for handler in stmt.handlers:
                        if handler.name:
                            conditional.add(handler.name)
                        _scan_body(handler.body, in_branch=True)
                    _scan_body(stmt.orelse, in_branch=True)
                    _scan_body(stmt.finalbody, in_branch=True)
                # While
                if isinstance(stmt, ast.While):
                    _scan_body(stmt.body, in_branch=True)

        _scan_body(func_node.body, in_branch=False)

        # Collect all Name references (loads)
        for node in ast.walk(func_node):
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
                # Ignore builtins and common globals
                if node.id in ('print', 'len', 'range', 'int', 'str', 'float', 'bool',
                               'list', 'dict', 'set', 'tuple', 'type', 'isinstance',
                               'issubclass', 'hasattr', 'getattr', 'setattr', 'super',
                               'open', 'None', 'True', 'False', 'Exception', 'ValueError',
                               'TypeError', 'RuntimeError', 'KeyError', 'IndexError',
                               'AttributeError', 'StopIteration', 'NotImplementedError',
                               'OSError', 'IOError', 'FileNotFoundError', 'PermissionError',
                               'ZeroDivisionError', 'OverflowError', 'AssertionError',
                               'NameError', 'UnboundLocalError', 'ImportError',
                               'enumerate', 'zip', 'map', 'filter', 'sorted', 'reversed',
                               'min', 'max', 'sum', 'abs', 'any', 'all', 'id', 'repr',
                               'hash', 'hex', 'oct', 'bin', 'chr', 'ord', 'format',
                               'input', 'iter', 'next', 'object', 'property', 'staticmethod',
                               'classmethod', 'bytes', 'bytearray', 'memoryview',
                               'frozenset', 'complex', 'divmod', 'pow', 'round',
                               'self', 'cls', '__name__', '__file__', '__class__',
                               'threading', 'struct', 'hmac', 'secrets', 'os', 'sys',
                               'io', 'json', 'math', 'time', 'datetime', 'collections',
                               'functools', 'itertools', 'operator', 'copy', 'subprocess',
                               'pathlib', 'logging', 'warnings', 're', 'hashlib',
                               'random', 'socket', 'signal', 'contextlib', 'abc',
                               'dataclasses', 'typing', 'enum', 'textwrap',
                               ):
                    continue
                all_used.append((node.id, node.lineno, node.col_offset, node))

        # For each used variable: if it's ONLY conditionally bound (not in unconditional),
        # it's a binding presheaf gap — the section at the use site requires the variable
        # to be in dom(Γ), but the available section only covers the branch.
        for name, line, col, node in all_used:
            if name not in unconditional and name in conditional:
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.SSA_VALUE,
                                   name=f"bind_{name}_L{line}"),
                    bug_type="UNBOUND_VAR",
                    required_predicate=Comparison(
                        op='==', left=Var(f"bound_{name}"), right=IntLit(1)
                    ),
                    description=(
                        f"variable `{name}` only conditionally bound — "
                        f"binding presheaf Γ({name}) has partial section"
                    ),
                    line=line, col=col, ast_node=node,
                ))

    return reqs


def _recursion_analysis(tree: ast.AST) -> List[SectionRequirement]:
    """Detect unbounded recursion as a stack-depth presheaf obstruction.

    The call-stack defines a *stack-depth presheaf*

        D : Sitesᵒᵖ → ℤ₋₀  (non-negative integers)

    where D(site) is the remaining stack frames at that observation site.
    A recursive call at site U requires a *section*

        σ ∈ Γ(U, D)   such that   ρ_{U,U′}(σ) > 0

    i.e. the restriction map to the callee site U′ must carry a
    strictly-positive depth budget.  If no *explicit depth-limit mechanism*
    provides such a section, the presheaf has no global section bounded
    by sys.getrecursionlimit() → obstruction = potential STACK_OVERFLOW.

    Key insight: a *logical* base case (e.g. `if n <= 0: return 0`) proves
    *termination* but NOT stack-boundedness.  For STACK_OVERFLOW we require
    an **explicit depth budget**: an optional parameter with a default that
    is decremented and guarded, or a sys.getrecursionlimit() sentinel.
    """
    reqs: List[SectionRequirement] = []

    for func_node in ast.walk(tree):
        if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue

        func_name = func_node.name

        # Phase 1: collect self-calls (direct recursion sites)
        self_calls: List[ast.Call] = []
        for node in ast.walk(func_node):
            if isinstance(node, ast.Call):
                name = _get_call_name(node)
                if name == func_name:
                    self_calls.append(node)

        if not self_calls:
            continue

        self_call_line = self_calls[0].lineno

        # Phase 2: check for sys.getrecursionlimit() sentinel in the
        # function body — this provides an explicit ceiling section.
        func_source = ""
        try:
            func_source = ast.unparse(func_node)
        except Exception:
            pass
        if "getrecursionlimit" in func_source or "setrecursionlimit" in func_source:
            continue

        # Phase 3: identify depth-budget parameters.
        # A depth-budget parameter is one with a DEFAULT VALUE that is
        # modified (decremented / incremented) in recursive calls and
        # checked in a condition.  Required params like `n` in fibonacci
        # prove termination but not stack-boundedness, so they are NOT
        # treated as depth budgets.
        params_with_defaults: Set[str] = set()
        defaults = func_node.args.defaults
        args = func_node.args.args
        if defaults:
            offset = len(args) - len(defaults)
            for i, _d in enumerate(defaults):
                if offset + i < len(args):
                    params_with_defaults.add(args[offset + i].arg)
        for kw, dflt in zip(func_node.args.kwonlyargs, func_node.args.kw_defaults):
            if dflt is not None:
                params_with_defaults.add(kw.arg)

        has_depth_limit = False
        for call in self_calls:
            # Check positional args for decrement/increment pattern
            for arg in call.args:
                if isinstance(arg, ast.BinOp) and isinstance(arg.op, (ast.Sub, ast.Add)):
                    left_name = _expr_to_var_name(arg.left, "")
                    if left_name in params_with_defaults:
                        # Found budget ± N pattern; verify a condition guard exists
                        for s in ast.walk(func_node):
                            if isinstance(s, ast.If):
                                try:
                                    cond = ast.unparse(s.test)
                                except Exception:
                                    cond = ""
                                if left_name in cond:
                                    has_depth_limit = True
                                    break
                        if has_depth_limit:
                            break
            # Check keyword args (e.g. traverse(child, depth=depth+1))
            if not has_depth_limit:
                for kw in call.keywords:
                    if kw.arg in params_with_defaults:
                        has_depth_limit = True
                        break
            if has_depth_limit:
                break

        if has_depth_limit:
            continue

        # Phase 4: emit obstruction — the stack-depth presheaf has no
        # bounded global section at the recursive call site.
        reqs.append(SectionRequirement(
            site_id=SiteId(kind=SiteKind.CALL_RESULT,
                           name=f"recurse_{func_name}_L{self_call_line}"),
            bug_type="STACK_OVERFLOW",
            required_predicate=Comparison(
                op='>', left=Var(f"ranking_{func_name}"), right=IntLit(0)
            ),
            description=(
                f"recursive call `{func_name}()` has no explicit depth budget — "
                f"stack-depth presheaf D : Sitesᵒᵖ → ℤ has no bounded section"
            ),
            line=self_call_line, col=0, ast_node=func_node,
        ))

    return reqs



def _double_close_analysis(tree: ast.AST) -> List[SectionRequirement]:
    """Detect double-close as a lifecycle presheaf inconsistency.

    The lifecycle presheaf S : Sites → {OPEN, CLOSED} assigns a state to
    each resource at each site.  A .close() call transitions S(site) from
    OPEN → CLOSED.  A SECOND .close() on the same object requires
    S(site) = OPEN, but the available section says S(site) = CLOSED
    (from the first close) → the restriction map is undefined → obstruction.

    Algorithm: track sequences of .close() calls on the same object variable
    at the function level.  If the same variable has two .close() calls with
    no intervening reassignment, that's a double-close.
    """
    reqs: List[SectionRequirement] = []

    for func_node in ast.walk(tree):
        if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue

        # Collect all .close() calls and assignments in order
        close_calls: Dict[str, List[int]] = defaultdict(list)  # var → [line, ...]
        reassignments: Dict[str, List[int]] = defaultdict(list)  # var → [line, ...]

        for node in ast.walk(func_node):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                if node.func.attr == 'close':
                    var = _expr_to_var_name(node.func.value, "")
                    if var:
                        close_calls[var].append(node.lineno)
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        reassignments[target.id].append(node.lineno)

        # Check for double close: two close calls with no reassignment in between
        for var, lines in close_calls.items():
            if len(lines) < 2:
                continue
            lines.sort()
            for i in range(len(lines) - 1):
                first_close = lines[i]
                second_close = lines[i + 1]
                # Check if var is reassigned between the two closes
                reassigned_between = any(
                    first_close < rline < second_close
                    for rline in reassignments.get(var, [])
                )
                if not reassigned_between:
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.CALL_RESULT,
                                       name=f"dblclose_{var}_L{second_close}"),
                        bug_type="DOUBLE_CLOSE",
                        required_predicate=Comparison(
                            op='==', left=Var(f"lifecycle_{var}"),
                            right=IntLit(1)  # requires OPEN
                        ),
                        description=(
                            f"`{var}.close()` at line {second_close} — "
                            f"lifecycle presheaf says S({var}) = CLOSED after line {first_close}"
                        ),
                        line=second_close, col=0,
                    ))

    return reqs


def _deadlock_analysis(tree: ast.AST) -> List[SectionRequirement]:
    """Detect deadlock as a cyclic lock-ordering presheaf failure.

    The lock ordering presheaf O : Sites → ℕ assigns a total order to lock
    acquisition sites.  If thread T1 acquires lock A then lock B, and thread
    T2 acquires lock B then lock A, the ordering presheaf has NO consistent
    global section — the cocycle condition O(A) < O(B) and O(B) < O(A) is
    contradictory → obstruction.

    Formally: let G = (Locks, <) be the lock acquisition order graph.
    Each thread's lock sequence defines directed edges.  A CYCLE in G means
    the ordering presheaf has no section → deadlock obstruction.

    Algorithm:
    1. Find all functions (potential thread targets).
    2. Extract lock acquisition sequences (with-lock or acquire/release).
    3. Build the acquisition order graph.
    4. Detect cycles → emit requirements.
    """
    reqs: List[SectionRequirement] = []

    # Collect lock acquisition sequences per function (including nested functions)
    lock_sequences: Dict[str, List[str]] = {}  # func_name → [lock_var, ...]

    def _extract_lock_sequence(func_node: ast.AST) -> List[str]:
        """Extract ordered lock acquisitions from a function, handling nesting.

        For nested with-statements like:
            with a:
                with b:  → sequence is [a, b]

        This correctly models the lock ordering presheaf: the ORDER of
        acquisition defines directed edges in the ordering graph.
        """
        locks: List[str] = []

        def _walk_stmts(stmts: List[ast.stmt]) -> None:
            for stmt in stmts:
                if isinstance(stmt, (ast.With, ast.AsyncWith)):
                    for item in stmt.items:
                        ctx = item.context_expr
                        var = _expr_to_var_name(ctx, "")
                        if var:
                            locks.append(var)
                    _walk_stmts(stmt.body)
                elif isinstance(stmt, ast.If):
                    _walk_stmts(stmt.body)
                    _walk_stmts(stmt.orelse)
                elif isinstance(stmt, (ast.For, ast.While)):
                    _walk_stmts(stmt.body)
                elif isinstance(stmt, ast.Try):
                    _walk_stmts(stmt.body)
                    for handler in stmt.handlers:
                        _walk_stmts(handler.body)
                # Explicit acquire
                elif isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                    if isinstance(stmt.value.func, ast.Attribute):
                        if stmt.value.func.attr == 'acquire':
                            var = _expr_to_var_name(stmt.value.func.value, "")
                            if var:
                                locks.append(var)

        if isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            _walk_stmts(func_node.body)
        return locks

    for func_node in ast.walk(tree):
        if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue

        locks = _extract_lock_sequence(func_node)
        if locks:
            lock_sequences[func_node.name] = locks

    # Build lock order graph: for each function's lock sequence [A, B, C],
    # add edges A→B, B→C (A must be acquired before B).
    edges: Set[Tuple[str, str]] = set()
    for func_name, locks in lock_sequences.items():
        for i in range(len(locks) - 1):
            edges.add((locks[i], locks[i + 1]))

    # Detect cycles in the lock order graph
    # A cycle means ∃ locks L1, L2 such that L1 → ... → L2 AND L2 → ... → L1
    adj: Dict[str, Set[str]] = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)

    def _has_path(src: str, dst: str, visited: Set[str]) -> bool:
        if src == dst:
            return True
        visited.add(src)
        for nxt in adj.get(src, set()):
            if nxt not in visited and _has_path(nxt, dst, visited):
                return True
        return False

    # Check each edge for back-edges (cycles)
    reported: Set[FrozenSet[str]] = set()
    for a, b in edges:
        if _has_path(b, a, set()):
            pair = frozenset({a, b})
            if pair not in reported:
                reported.add(pair)
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.HEAP_PROTOCOL,
                                   name=f"deadlock_{a}_{b}"),
                    bug_type="DEADLOCK",
                    required_predicate=Comparison(
                        op='<', left=Var(f"lock_order_{a}"),
                        right=Var(f"lock_order_{b}")
                    ),
                    description=(
                        f"cyclic lock ordering: {a} ↔ {b} — "
                        f"lock ordering presheaf O has no consistent section"
                    ),
                    line=0, col=0,
                ))

    return reqs


def _extract_requirements(source: str) -> List[SectionRequirement]:
    """Extract type section requirements from the AST.

    Each requirement says: "at this site, the value must satisfy this
    refinement predicate, or bug X can occur."
    """
    tree = ast.parse(textwrap.dedent(source))
    reqs: List[SectionRequirement] = []

    # Collect parameter names — parameters are assumed not-None at the
    # function boundary (they get the strongest possible section).
    _param_names: Set[str] = set()
    for fnode in ast.walk(tree):
        if isinstance(fnode, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for arg in fnode.args.args:
                _param_names.add(arg.arg)
            for arg in fnode.args.posonlyargs:
                _param_names.add(arg.arg)
            for arg in fnode.args.kwonlyargs:
                _param_names.add(arg.arg)
            if fnode.args.vararg:
                _param_names.add(fnode.args.vararg.arg)
            if fnode.args.kwarg:
                _param_names.add(fnode.args.kwarg.arg)

    # Collect imported module names — module objects are always bound and
    # never None, so attribute access on them (mod.func) is safe.
    # This provides resilience for unknown/third-party modules: even if we
    # don't know what acme_lib.transform() returns, we know acme_lib itself
    # is not None (the import guarantees it).
    _imported_modules: Set[str] = set()
    for fnode in ast.walk(tree):
        if isinstance(fnode, ast.Import):
            for alias in fnode.names:
                _imported_modules.add(alias.asname or alias.name.split('.')[0])
        elif isinstance(fnode, ast.ImportFrom):
            if fnode.module:
                _imported_modules.add(fnode.module.split('.')[0])
            for alias in fnode.names:
                _imported_modules.add(alias.asname or alias.name)

    # Collect variables assigned to open() — for lifecycle tracking
    _open_vars: Set[str] = set()
    _close_lines: Dict[str, List[int]] = defaultdict(list)
    for fnode in ast.walk(tree):
        if isinstance(fnode, ast.Assign) and isinstance(fnode.value, ast.Call):
            fn = _get_call_name(fnode.value)
            if fn in ("open", "builtins.open", "io.open"):
                for t in fnode.targets:
                    if isinstance(t, ast.Name):
                        _open_vars.add(t.id)
        if isinstance(fnode, ast.Call) and isinstance(fnode.func, ast.Attribute):
            if fnode.func.attr == 'close':
                var = _expr_to_var_name(fnode.func.value, "")
                if var:
                    _close_lines[var].append(fnode.lineno)

    for node in ast.walk(tree):
        # ── REFINEMENT_GAP: Division by zero ──
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
            divisor_var = _expr_to_var_name(node.right, f"div_rhs_L{node.lineno}")
            reqs.append(SectionRequirement(
                site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"div_L{node.lineno}"),
                bug_type="DIV_ZERO",
                required_predicate=Comparison(op='!=', left=Var(divisor_var), right=IntLit(0)),
                description=f"divisor `{_expr_repr(node.right)}` must be ≠ 0",
                line=node.lineno, col=node.col_offset, ast_node=node,
            ))

        # ── REFINEMENT_GAP: None dereference ──
        # The presheaf F at an attribute-access site requires F(U) = {obj : T | obj ≠ None}.
        # We skip known-not-None cases:
        #   - self: always bound to the instance
        #   - function parameters: assumed not-None at boundary (no Optional annotation)
        #   - module-level names: imports are always bound
        #   - direct call results: open(), len(), etc. never return None implicitly
        if isinstance(node, ast.Attribute):
            if isinstance(node.value, ast.Name):
                skip_names = {'self', 'cls', 'threading', 'struct', 'hmac', 'secrets',
                              'os', 'sys', 'io', 'json', 'math', 'time', 'datetime',
                              'collections', 'functools', 'itertools', 'operator',
                              'copy', 'subprocess', 'pathlib', 'logging', 're',
                              'hashlib', 'random', 'socket', 'signal'} | _imported_modules
                if node.value.id in skip_names:
                    pass  # Skip: known not-None
                elif node.value.id in _param_names:
                    pass  # Skip: function parameter (assumed not-None)
                else:
                    obj_var = _expr_to_var_name(node.value, f"obj_L{node.lineno}")
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"attr_L{node.lineno}"),
                        bug_type="NULL_PTR",
                        required_predicate=Comparison(op='!=', left=Var(f"{obj_var}_is_none"), right=IntLit(1)),
                        description=f"`{_expr_repr(node.value)}.{node.attr}` — object must not be None",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))
            elif not isinstance(node.value, ast.Call):
                # Non-Name, non-Call attribute access: could be None
                obj_var = _expr_to_var_name(node.value, f"obj_L{node.lineno}")
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"attr_L{node.lineno}"),
                    bug_type="NULL_PTR",
                    required_predicate=Comparison(op='!=', left=Var(f"{obj_var}_is_none"), right=IntLit(1)),
                    description=f"`{_expr_repr(node.value)}.{node.attr}` — object must not be None",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # ── REFINEMENT_GAP: Index out of bounds ──
        # Skip direct-parameter indices: if the index is a plain Name that
        # matches a function parameter, it's a precondition of the caller →
        # not an obstruction in THIS function's presheaf.
        if isinstance(node, ast.Subscript):
            if _is_index_access(node):
                # Check if index is a direct function parameter (precondition)
                is_param_idx = False
                if isinstance(node.slice, ast.Name):
                    for parent_fn in ast.walk(tree):
                        if isinstance(parent_fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            fn_params = {a.arg for a in parent_fn.args.args}
                            if node.slice.id in fn_params:
                                # Verify node is inside this function
                                for desc in ast.walk(parent_fn):
                                    if desc is node:
                                        is_param_idx = True
                                        break
                            if is_param_idx:
                                break

                if not is_param_idx:
                    idx_var = _expr_to_var_name(node.slice, f"idx_L{node.lineno}")
                    seq_var = _expr_to_var_name(node.value, f"seq_L{node.lineno}")
                    len_var = f"len_{seq_var}"
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"idx_L{node.lineno}"),
                        bug_type="INDEX_OOB",
                        required_predicate=And(conjuncts=[
                            Comparison(op='>=', left=Var(idx_var), right=IntLit(0)),
                            Comparison(op='<', left=Var(idx_var), right=Var(len_var)),
                        ]),
                        description=f"index `{_expr_repr(node.slice)}` must be in [0, len({_expr_repr(node.value)}))",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

        # ── REFINEMENT_GAP: Key error ──
        # Pure Store context (d[k] = v) never raises KeyError.
        # But AugAssign (d[k] += v) reads first → CAN raise.
        if isinstance(node, ast.Subscript) and _is_dict_access(node):
            ctx = getattr(node, 'ctx', None)
            is_pure_store = isinstance(ctx, ast.Store)
            # AugAssign target has Store ctx but reads first → treat as Load
            is_aug_assign_target = False
            if is_pure_store:
                for parent_node in ast.walk(tree):
                    if isinstance(parent_node, ast.AugAssign) and parent_node.target is node:
                        is_aug_assign_target = True
                        break
            if isinstance(ctx, ast.Load) or is_aug_assign_target:
                key_var = _expr_to_var_name(node.slice, f"key_L{node.lineno}")
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"key_L{node.lineno}"),
                    bug_type="KEY_ERROR",
                    required_predicate=Comparison(op='==', left=Var(f"{key_var}_exists"), right=IntLit(1)),
                    description=f"key `{_expr_repr(node.slice)}` must exist in dict",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # ── REFINEMENT_GAP: Assertion ──
        if isinstance(node, ast.Assert):
            reqs.append(SectionRequirement(
                site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"assert_L{node.lineno}"),
                bug_type="ASSERT_FAIL",
                required_predicate=Comparison(op='==', left=Var(f"assert_cond_L{node.lineno}"), right=IntLit(1)),
                description=f"assertion condition must be true",
                line=node.lineno, col=node.col_offset, ast_node=node,
            ))

        # ── CARRIER_MISMATCH: Type error on binary ops ──
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult)):
            left_var = _expr_to_var_name(node.left, f"binop_l_L{node.lineno}")
            right_var = _expr_to_var_name(node.right, f"binop_r_L{node.lineno}")
            op_sym = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*'}.get(type(node.op), '+')
            reqs.append(SectionRequirement(
                site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"binop_L{node.lineno}"),
                bug_type="TYPE_ERROR",
                required_predicate=Comparison(
                    op='==',
                    left=Var(f"type_{left_var}"),
                    right=Var(f"type_{right_var}"),
                ),
                description=f"operand types must be ⊕-compatible for `{op_sym}`",
                line=node.lineno, col=node.col_offset, ast_node=node,
            ))

        # ── CARRIER_MISMATCH: Type confusion on method call ──
        #    obj.method() requires carrier(obj) to have `method`.
        #    This is a deeper check than NULL_PTR — it's about the carrier
        #    supporting the protocol, not just being non-None.
        #    Skip when the object is a known type constructor call:
        #    str(x).upper() → carrier is provably str (constructor return type).
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            method = node.func.attr
            obj_expr = node.func.value
            obj_var = _expr_to_var_name(obj_expr, f"obj_L{node.lineno}")

            # Skip TYPE_CONFUSION when object is a known-type constructor call.
            # In sheaf terms: the call-result site has a PROVABLE carrier section.
            _is_known_constructor = (
                isinstance(obj_expr, ast.Call) and isinstance(obj_expr.func, ast.Name)
                and obj_expr.func.id in ('str', 'int', 'float', 'bool', 'list', 'dict',
                                          'set', 'tuple', 'bytes', 'bytearray')
            )

            if not _is_known_constructor:
                if method in ('upper', 'lower', 'strip', 'split', 'replace', 'encode',
                              'decode', 'startswith', 'endswith', 'format', 'join'):
                    # str-specific methods: carrier must be str
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"typeconf_L{node.lineno}"),
                        bug_type="TYPE_CONFUSION",
                        required_predicate=Comparison(
                            op='==', left=Var(f"carrier_{obj_var}"), right=IntLit(1)  # 1 = str
                        ),
                        description=f"`.{method}()` requires carrier(obj) = str",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))
                elif method in ('append', 'extend', 'pop', 'insert', 'remove', 'sort', 'reverse'):
                    # list-specific methods: carrier must be list
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"typeconf_L{node.lineno}"),
                        bug_type="TYPE_CONFUSION",
                        required_predicate=Comparison(
                            op='==', left=Var(f"carrier_{obj_var}"), right=IntLit(2)  # 2 = list
                        ),
                        description=f"`.{method}()` requires carrier(obj) = list",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

        # ── BINDING_GAP: Unbound variable ──
        #    Python's LEGB scoping defines a presheaf Γ : Sites → Env.
        #    A Name reference requires x ∈ dom(Γ(U)).
        #    We detect variables used before unconditional assignment.
        #    (Tracked via _binding_analysis below, injected after the walk.)

        # ── REFINEMENT_GAP: Integer overflow on struct.pack / ctypes ──
        if isinstance(node, ast.Call):
            func_name = _get_call_name(node)
            if func_name in ("struct.pack",) and len(node.args) >= 2:
                fmt_arg = node.args[0]
                if isinstance(fmt_arg, ast.Constant) and isinstance(fmt_arg.value, str):
                    fmt = fmt_arg.value
                    if 'i' in fmt or 'h' in fmt or 'b' in fmt or 'l' in fmt:
                        val_var = _expr_to_var_name(node.args[1], f"pack_val_L{node.lineno}")
                        bits = {'b': 8, 'h': 16, 'i': 32, 'l': 32, 'q': 64}.get(
                            next((c for c in fmt if c in 'bhilq'), 'i'), 32)
                        lo = -(2 ** (bits - 1))
                        hi = 2 ** (bits - 1) - 1
                        reqs.append(SectionRequirement(
                            site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"pack_L{node.lineno}"),
                            bug_type="INTEGER_OVERFLOW",
                            required_predicate=And(conjuncts=[
                                Comparison(op='>=', left=Var(val_var), right=IntLit(lo)),
                                Comparison(op='<=', left=Var(val_var), right=IntLit(hi)),
                            ]),
                            description=f"struct.pack('{fmt}'): value must be in [{lo}, {hi}]",
                            line=node.lineno, col=node.col_offset, ast_node=node,
                        ))
                    if 'q' in fmt:
                        val_var = _expr_to_var_name(node.args[1], f"pack_val_L{node.lineno}")
                        lo = -(2**63)
                        hi = 2**63 - 1
                        reqs.append(SectionRequirement(
                            site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"pack_L{node.lineno}"),
                            bug_type="OVERFLOW",
                            required_predicate=And(conjuncts=[
                                Comparison(op='>=', left=Var(val_var), right=IntLit(lo)),
                                Comparison(op='<=', left=Var(val_var), right=IntLit(hi)),
                            ]),
                            description=f"struct.pack('{fmt}'): value must be in [{lo}, {hi}]",
                            line=node.lineno, col=node.col_offset, ast_node=node,
                        ))

        # ── LIFECYCLE_GAP: Resource leak (open without with) ──
        #    Resource lifecycle presheaf: OPEN site must have CLOSE on all paths.
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.Call):
            func_name = _get_call_name(node.value)
            if func_name in ("open", "builtins.open", "io.open"):
                # Check: is this inside a with-statement?
                if not _is_inside_with(node, tree):
                    var_name = _expr_to_var_name(node.targets[0], f"res_L{node.lineno}")
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"resleak_L{node.lineno}"),
                        bug_type="MEMORY_LEAK",
                        required_predicate=Comparison(
                            op='==', left=Var(f"closed_{var_name}"), right=IntLit(1)
                        ),
                        description=f"`{_expr_repr(node.targets[0])}` = open(...) without context manager — resource may leak",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

        # ── LIFECYCLE_GAP: Use after close ──
        #    Calling .read()/.write() on a closed file.
        #    Only flag if the use happens AFTER a .close() call on the same var.
        #    In sheaf terms: the lifecycle presheaf S transitions from OPEN→CLOSED
        #    at the close site.  A use site AFTER the close site has S = CLOSED,
        #    and the use requires S = OPEN → obstruction.
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            method = node.func.attr
            if method in ('read', 'write', 'readline', 'readlines', 'seek', 'tell'):
                obj_var = _expr_to_var_name(node.func.value, f"fobj_L{node.lineno}")
                # Only flag if there's a .close() on this var BEFORE this line
                close_lines_for_var = _close_lines.get(obj_var, [])
                has_prior_close = any(cl < node.lineno for cl in close_lines_for_var)
                if has_prior_close:
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"useclose_L{node.lineno}"),
                        bug_type="USE_AFTER_FREE",
                        required_predicate=Comparison(
                            op='==', left=Var(f"lifecycle_{obj_var}"), right=IntLit(1)  # 1=OPEN
                        ),
                        description=f"`.{method}()` requires lifecycle({_expr_repr(node.func.value)}) = OPEN",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

        # ── LIFECYCLE_GAP: Double close ──
        # NOTE: Individual .close() calls are NOT flagged here — the
        # _double_close_analysis() post-walk handler detects PAIRS of close
        # calls on the same variable with no intervening reassignment.
        # This avoids FPs on single close calls guarded by boolean flags.

        # ── RANKING_GAP: Non-termination (while loops) ──
        if isinstance(node, ast.While):
            loop_var = _extract_loop_var(node)
            if loop_var:
                # Check if the loop body modifies the loop variable
                body_modifies = _body_modifies_var(node.body, loop_var)
                # Also check that modification is in the correct direction
                correct_dir = _body_modifies_var_correctly(
                    node.body, loop_var, node.test)
                if not body_modifies or not correct_dir:
                    reason = (
                        f"`{loop_var}` not modified in body"
                        if not body_modifies
                        else f"`{loop_var}` modified in wrong direction"
                    )
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.LOOP_HEADER_INVARIANT,
                                       name=f"loop_L{node.lineno}"),
                        bug_type="NON_TERMINATION",
                        required_predicate=Comparison(
                            op='>', left=Var(f"ranking_{loop_var}"), right=IntLit(0)
                        ),
                        description=f"while loop: no ranking function — {reason}",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

        # ── RANKING_GAP: Unbounded recursion ──
        #    A function that calls itself without a base case.

        # ── SYNCHRONIZATION_GAP: Data race ──
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            method = node.func.attr
            if method in ('append', 'extend', 'pop', 'insert', 'remove',
                          '__setitem__', '__delitem__'):
                obj_var = _expr_to_var_name(node.func.value, f"shared_L{node.lineno}")
                # Only flag if inside a thread-spawned function
                if _is_inside_thread_target(node, tree):
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.HEAP_PROTOCOL,
                                       name=f"race_L{node.lineno}"),
                        bug_type="DATA_RACE",
                        required_predicate=Comparison(
                            op='==', left=Var(f"lock_held_{obj_var}"), right=IntLit(1)
                        ),
                        description=f"`.{method}()` on shared object requires lock held",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

        # Data race via subscript assignment: d[k] = v inside thread target
        if isinstance(node, ast.Assign):
            for tgt in node.targets:
                if isinstance(tgt, ast.Subscript) and isinstance(tgt.value, ast.Name):
                    if _is_inside_thread_target(node, tree):
                        obj_var = tgt.value.id
                        reqs.append(SectionRequirement(
                            site_id=SiteId(kind=SiteKind.HEAP_PROTOCOL,
                                           name=f"race_L{node.lineno}"),
                            bug_type="DATA_RACE",
                            required_predicate=Comparison(
                                op='==', left=Var(f"lock_held_{obj_var}"), right=IntLit(1)
                            ),
                            description=f"subscript assignment on shared `{obj_var}` requires lock held",
                            line=node.lineno, col=node.col_offset, ast_node=node,
                        ))

        # ── SECRECY_GAP: Information leak ──
        if isinstance(node, ast.Raise) and node.exc is not None:
            try:
                exc_text = ast.unparse(node.exc)
            except Exception:
                exc_text = ""
            # Only flag interpolation that includes variable data (not just
            # type(e).__name__ or static strings)
            has_interpolation = ('{' in exc_text or 'f"' in exc_text or "f'" in exc_text or '%' in exc_text)
            # Heuristic: safe patterns that don't leak secrets
            safe_interp = all(
                seg.strip().rstrip('}').strip() in ('', 'type(e).__name__', 'e.__class__.__name__')
                for seg in exc_text.split('{')[1:]
                if '}' in seg
            ) if has_interpolation and '{' in exc_text else False
            if has_interpolation and not safe_interp:
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.ERROR, name=f"infoleak_L{node.lineno}"),
                    bug_type="INFO_LEAK",
                    required_predicate=Comparison(
                        op='==', left=Var(f"secret_in_msg_L{node.lineno}"), right=IntLit(0)
                    ),
                    description=f"raise with interpolated data may leak sensitive information",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # Info leak via traceback exposure in return values or dict literals
        # Only flag traceback.format_exc() when its result appears in a return,
        # not when it's merely passed to a logging function.
        if isinstance(node, ast.Call):
            try:
                call_text = ast.unparse(node)
            except Exception:
                call_text = ""
            if 'traceback.format_exc' in call_text or 'traceback.format_exception' in call_text:
                # Walk up to see if this call is inside a return/dict/yield
                _is_returned = False
                for parent_node in ast.walk(tree):
                    if isinstance(parent_node, ast.Return) and parent_node.value is not None:
                        try:
                            ret_text = ast.unparse(parent_node.value)
                        except Exception:
                            ret_text = ""
                        if 'traceback.format_exc' in ret_text or 'traceback.format_exception' in ret_text:
                            _is_returned = True
                            break
                    # Also flag if assigned then returned or embedded in dict
                    if isinstance(parent_node, ast.Assign) and len(parent_node.targets) == 1:
                        if isinstance(parent_node.targets[0], ast.Name):
                            _tb_var = parent_node.targets[0].id
                            try:
                                rhs_text = ast.unparse(parent_node.value)
                            except Exception:
                                rhs_text = ""
                            if 'traceback.format_exc' in rhs_text or 'traceback.format_exception' in rhs_text:
                                # Check if this var appears in any return statement
                                for ret_node in ast.walk(tree):
                                    if isinstance(ret_node, ast.Return) and ret_node.value is not None:
                                        try:
                                            rv = ast.unparse(ret_node.value)
                                        except Exception:
                                            rv = ""
                                        if _tb_var in rv:
                                            _is_returned = True
                                            break
                if _is_returned:
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.ERROR, name=f"infoleak_L{node.lineno}"),
                        bug_type="INFO_LEAK",
                        required_predicate=Comparison(
                            op='==', left=Var(f"tb_exposed_L{node.lineno}"), right=IntLit(0)
                        ),
                        description="traceback exposure leaks internal stack information",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

        # Info leak via str(e) / repr(e) in return values inside except blocks
        if isinstance(node, ast.Return) and node.value is not None:
            try:
                ret_text = ast.unparse(node.value)
            except Exception:
                ret_text = ""
            # Check if str(e) or repr(e) appears where e is an exception variable
            # We detect exception variable names from enclosing except handlers
            _exc_vars: Set[str] = set()
            for eh in ast.walk(tree):
                if isinstance(eh, ast.ExceptHandler) and eh.name:
                    _exc_vars.add(eh.name)
            for ev in _exc_vars:
                if f"str({ev})" in ret_text or f"repr({ev})" in ret_text:
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.ERROR, name=f"infoleak_L{node.lineno}"),
                        bug_type="INFO_LEAK",
                        required_predicate=Comparison(
                            op='==', left=Var(f"secret_in_msg_L{node.lineno}"), right=IntLit(0)
                        ),
                        description="returning str(exception) may leak sensitive information",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))
                    break

        # ── SECRECY_GAP: Timing channel ──
        #    Detected by: for-loop comparing secret data with early exit.
        if isinstance(node, ast.For):
            # Check if body contains an early return/break inside a comparison
            # Detect both subscript indexing (a[i] != b[i]) and zip iteration
            # (for x, y in zip(a, b): if x != y)
            try:
                iter_text = ast.unparse(node.iter)
            except Exception:
                iter_text = ""
            is_zip_loop = "zip(" in iter_text
            for child in ast.walk(node):
                if isinstance(child, ast.If):
                    try:
                        cond_text = ast.unparse(child.test)
                    except Exception:
                        continue
                    has_subscript_cmp = ('[' in cond_text and ('!=' in cond_text or '==' in cond_text))
                    has_name_cmp = (is_zip_loop and ('!=' in cond_text or '==' in cond_text))
                    body_returns = any(isinstance(s, (ast.Return, ast.Break)) for s in child.body)
                    if (has_subscript_cmp or has_name_cmp) and body_returns:
                        reqs.append(SectionRequirement(
                            site_id=SiteId(kind=SiteKind.BRANCH_GUARD,
                                           name=f"timing_L{child.lineno}"),
                            bug_type="TIMING_CHANNEL",
                            required_predicate=Comparison(
                                op='==', left=Var(f"timing_indep_L{child.lineno}"), right=IntLit(1)
                            ),
                            description=f"early exit in element-wise comparison leaks timing information",
                            line=child.lineno, col=child.col_offset, ast_node=child,
                        ))

        # Timing channel via == comparison of hash/digest results
        # Collect variables assigned from .hexdigest()/.digest()/hashlib.* calls
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            if isinstance(node.ops[0], (ast.Eq, ast.NotEq)):
                try:
                    left_text = ast.unparse(node.left)
                    right_text = ast.unparse(node.comparators[0])
                except Exception:
                    left_text = right_text = ""
                # Direct call in comparison
                has_hash = any(
                    kw in left_text or kw in right_text
                    for kw in ('.hexdigest()', '.digest()', 'hashlib.')
                )
                # Indirect: check if compared variables were assigned from hash calls
                if not has_hash:
                    hash_vars: Set[str] = set()
                    for sib in ast.walk(tree):
                        if isinstance(sib, ast.Assign) and len(sib.targets) == 1:
                            if isinstance(sib.targets[0], ast.Name):
                                try:
                                    rhs_text = ast.unparse(sib.value)
                                except Exception:
                                    rhs_text = ""
                                if any(kw in rhs_text for kw in (
                                    '.hexdigest()', '.digest()', 'hashlib.',
                                    'sha256(', 'sha1(', 'sha512(', 'md5(')):
                                    hash_vars.add(sib.targets[0].id)
                    if hash_vars & {left_text.strip(), right_text.strip()}:
                        has_hash = True
                # Also detect == on secret/key/token/password parameters
                if not has_hash:
                    _secret_kws = ('key', 'secret', 'token', 'password',
                                   'credential', 'api_key', 'auth_token',
                                   'passw', 'passwd')
                    combined = (left_text + ' ' + right_text).lower()
                    if any(kw in combined for kw in _secret_kws):
                        has_hash = True
                if has_hash:
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.BRANCH_GUARD,
                                       name=f"timing_L{node.lineno}"),
                        bug_type="TIMING_CHANNEL",
                        required_predicate=Comparison(
                            op='==', left=Var(f"timing_indep_L{node.lineno}"), right=IntLit(1)
                        ),
                        description="== comparison of secret/key/hash leaks timing information; use hmac.compare_digest",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

        # ── REFINEMENT_GAP: Bounds (slice access) ──
        if isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Slice):
            seq_var = _expr_to_var_name(node.value, f"buf_L{node.lineno}")
            if node.slice.upper is not None:
                upper_var = _expr_to_var_name(node.slice.upper, f"upper_L{node.lineno}")
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"bounds_L{node.lineno}"),
                    bug_type="BOUNDS",
                    required_predicate=Comparison(
                        op='<=', left=Var(upper_var), right=Var(f"len_{seq_var}")
                    ),
                    description=f"slice upper bound must be ≤ len({_expr_repr(node.value)})",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # ── REFINEMENT_GAP: FP domain error ──
        #    Math functions with restricted domains define presheaves over
        #    the real line.  The function site requires a section satisfying
        #    the domain predicate; if no such section is available, the
        #    restriction map is undefined → obstruction.
        if isinstance(node, ast.Call):
            func_name = _get_call_name(node)
            _fp_domain_specs: Dict[str, Tuple[str, str]] = {
                "math.log": ("positive", "math.log(x) requires x > 0"),
                "math.log2": ("positive", "math.log2(x) requires x > 0"),
                "math.log10": ("positive", "math.log10(x) requires x > 0"),
                "math.log1p": ("gt_neg1", "math.log1p(x) requires x > -1"),
                "math.sqrt": ("non_negative", "math.sqrt(x) requires x ≥ 0"),
                "math.asin": ("unit_interval", "math.asin(x) requires -1 ≤ x ≤ 1"),
                "math.acos": ("unit_interval", "math.acos(x) requires -1 ≤ x ≤ 1"),
                "math.acosh": ("ge_one", "math.acosh(x) requires x ≥ 1"),
                "math.atanh": ("open_unit", "math.atanh(x) requires -1 < x < 1"),
            }
            if func_name in _fp_domain_specs and node.args:
                domain_kind, desc = _fp_domain_specs[func_name]
                # abs() wrapping guarantees non-negative → skip for sqrt etc.
                arg0 = node.args[0]
                if domain_kind == "non_negative" and isinstance(arg0, ast.Call):
                    abs_name = _get_call_name(arg0)
                    if abs_name in ("abs", "builtins.abs", "math.fabs"):
                        continue
                arg_var = _expr_to_var_name(node.args[0], f"fp_arg_L{node.lineno}")
                if domain_kind == "positive":
                    pred: Predicate = Comparison(op='>', left=Var(arg_var), right=IntLit(0))
                elif domain_kind == "non_negative":
                    pred = Comparison(op='>=', left=Var(arg_var), right=IntLit(0))
                elif domain_kind == "unit_interval":
                    pred = And(conjuncts=[
                        Comparison(op='>=', left=Var(arg_var), right=IntLit(-1)),
                        Comparison(op='<=', left=Var(arg_var), right=IntLit(1)),
                    ])
                elif domain_kind == "gt_neg1":
                    pred = Comparison(op='>', left=Var(arg_var), right=IntLit(-1))
                elif domain_kind == "ge_one":
                    pred = Comparison(op='>=', left=Var(arg_var), right=IntLit(1))
                elif domain_kind == "open_unit":
                    pred = And(conjuncts=[
                        Comparison(op='>', left=Var(arg_var), right=IntLit(-1)),
                        Comparison(op='<', left=Var(arg_var), right=IntLit(1)),
                    ])
                else:
                    pred = Comparison(op='>', left=Var(arg_var), right=IntLit(0))
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.CALL_RESULT,
                                   name=f"fpdomain_L{node.lineno}"),
                    bug_type="FP_DOMAIN",
                    required_predicate=pred,
                    description=desc,
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # ── EXCEPTION_ESCAPEMENT: ValueError ──
        #    Operations that raise ValueError when given invalid input.
        #    In sheaf terms: the call site requires a section in the
        #    "parseable" or "present-in-collection" sub-presheaf, but the
        #    available section is the full carrier → restriction undefined.
        if isinstance(node, ast.Call):
            func_name = _get_call_name(node)
            # int(), float() on string arguments — may raise ValueError
            if func_name in ('int', 'float') and node.args:
                arg_var = _expr_to_var_name(node.args[0], f"parse_arg_L{node.lineno}")
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.CALL_RESULT,
                                   name=f"valerr_L{node.lineno}"),
                    bug_type="VALUE_ERROR",
                    required_predicate=Comparison(
                        op='==', left=Var(f"parseable_{arg_var}"), right=IntLit(1)
                    ),
                    description=f"`{func_name}({_expr_repr(node.args[0])})` may raise ValueError on non-numeric input",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))
            # list.remove() — raises ValueError if item not in list
            if isinstance(node.func, ast.Attribute) and node.func.attr == 'remove':
                if node.args:
                    item_var = _expr_to_var_name(node.args[0], f"item_L{node.lineno}")
                    obj_var = _expr_to_var_name(node.func.value, f"list_L{node.lineno}")
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.CALL_RESULT,
                                       name=f"valerr_L{node.lineno}"),
                        bug_type="VALUE_ERROR",
                        required_predicate=Comparison(
                            op='==', left=Var(f"{item_var}_in_{obj_var}"), right=IntLit(1)
                        ),
                        description=f"`.remove({_expr_repr(node.args[0])})` raises ValueError if item not in list",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

        # ── EXCEPTION_ESCAPEMENT: ValueError on tuple unpacking ──
        if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Tuple):
            n_targets = len(node.targets[0].elts)
            val_var = _expr_to_var_name(node.value, f"unpack_L{node.lineno}")
            reqs.append(SectionRequirement(
                site_id=SiteId(kind=SiteKind.CALL_RESULT,
                               name=f"unpack_L{node.lineno}"),
                bug_type="VALUE_ERROR",
                required_predicate=Comparison(
                    op='==', left=Var(f"len_{val_var}"), right=IntLit(n_targets)
                ),
                description=f"unpacking into {n_targets} variables requires exactly {n_targets} elements",
                line=node.lineno, col=node.col_offset, ast_node=node,
            ))

        # ── TAINT_LEAKAGE: Injection sinks ──
        if isinstance(node, ast.Call):
            func_name = _get_call_name(node)
            taint_spec = _get_taint_sink_spec(func_name, node)
            if taint_spec:
                bug_code, desc, arg_idx = taint_spec
                arg_var = f"arg{arg_idx}_L{node.lineno}"
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"sink_L{node.lineno}"),
                    bug_type=bug_code,
                    required_predicate=Comparison(
                        op='==', left=Var(f"tainted_{arg_var}"), right=IntLit(0)
                    ),
                    description=desc,
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # ── CONFIGURATION_WEAKNESS: Unsafe API usage ──
        if isinstance(node, ast.Call):
            func_name = _get_call_name(node)
            config_spec = _get_config_weakness_spec(func_name, node)
            if config_spec:
                bug_code, desc, pred = config_spec
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"config_L{node.lineno}"),
                    bug_type=bug_code,
                    required_predicate=pred,
                    description=desc,
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

    # ── Post-walk analyses (require whole-function view) ──
    reqs.extend(_binding_analysis(tree))
    reqs.extend(_recursion_analysis(tree))
    reqs.extend(_double_close_analysis(tree))
    reqs.extend(_deadlock_analysis(tree))

    return reqs


# ═══════════════════════════════════════════════════════════════════════════════
# Phase 2: Presheaf section computation via forward abstract interpretation
#
# The key sheaf-theoretic insight: abstract interpretation IS the computation
# of a global section of the refinement presheaf over the site cover.
#
#   F : Sites^op → RefinementCtx
#
# where F(U) = {Γ : Var → {v : τ | φ(v)}} is a dependent context assigning
# each variable a refinement type at site U.  The forward analysis computes
# stalks of this presheaf by:
#
#   - Transfer functions   = restriction maps ρ_{UV} : F(U) → F(V)
#   - Branch conditions    = pullbacks along condition morphisms
#   - Join points          = section merging via cocycle condition (meet in type lattice)
#   - Widening             = truncation to a coarser stalk (loses precision, gains termination)
#   - The fixpoint          = the global section
#
# This is genuinely sheaf-theoretic because the abstract domain forms a category
# of refinement types with subtyping as morphisms, and the analysis respects
# restriction (monotone transfer) and gluing (join = cocycle).
# ═══════════════════════════════════════════════════════════════════════════════


class _AbstractVal(Enum):
    """Three-valued abstract boolean: the stalk of the truth-value presheaf.

    In the presheaf of truth values B : Sites^op → {⊤, ⊥, ?}, each site
    carries a definite (⊤/⊥) or unknown (?) truth value for each tracked
    proposition.  The restriction map ρ_{UV} preserves definite values and
    maps unknown to unknown — monotone in the information ordering ? ⊑ ⊤, ? ⊑ ⊥.

    The cocycle condition at join points:
      ⊤ ⊔ ⊤ = ⊤,  ⊥ ⊔ ⊥ = ⊥,  otherwise ? (sections disagree → no gluing)

    This IS the sheaf condition: two local sections glue iff they agree on overlaps.
    """
    TRUE = "true"
    FALSE = "false"
    UNKNOWN = "unknown"

    def negate(self) -> '_AbstractVal':
        """Contravariant morphism in the truth-value presheaf."""
        if self is _AbstractVal.TRUE:
            return _AbstractVal.FALSE
        if self is _AbstractVal.FALSE:
            return _AbstractVal.TRUE
        return _AbstractVal.UNKNOWN

    def join(self, other: '_AbstractVal') -> '_AbstractVal':
        """Cocycle condition: sections glue iff they agree; otherwise ?."""
        if self is other:
            return self
        return _AbstractVal.UNKNOWN

    def meet(self, other: '_AbstractVal') -> '_AbstractVal':
        """Pullback: intersection of two sections (most informative agreement)."""
        if self is _AbstractVal.UNKNOWN:
            return other
        if other is _AbstractVal.UNKNOWN:
            return self
        if self is other:
            return self
        return _AbstractVal.UNKNOWN  # contradictory stalks

    @property
    def is_definitely_true(self) -> bool:
        return self is _AbstractVal.TRUE

    @property
    def is_definitely_false(self) -> bool:
        return self is _AbstractVal.FALSE


@dataclass
class _Stalk:
    """A stalk of the refinement presheaf at a single site.

    F(U) = Γ_U : Var → RefinementType, where each variable maps to a
    three-valued abstract refinement.  The stalk tracks:

    - is_none[v]      : whether v is definitely None/not-None/unknown
    - is_zero[v]      : whether v is definitely zero/nonzero/unknown
    - is_negative[v]  : whether v is definitely negative/non-negative/unknown
    - is_bound[v]     : whether v is definitely bound/unbound/unknown
    - is_open[v]      : whether resource v is open/closed/unknown
    - has_key[v]      : whether dict key v is known to exist/not-exist/unknown
    - is_in_domain[v] : whether v is in a valid math domain (positive, in range)
    - carrier[v]      : the base type of v (if known)

    These form heterogeneous fiber coordinates — each site can track
    different propositions depending on which operations occur there.
    The restriction map projects out irrelevant coordinates.
    """
    is_none: Dict[str, _AbstractVal] = field(default_factory=dict)
    is_zero: Dict[str, _AbstractVal] = field(default_factory=dict)
    is_negative: Dict[str, _AbstractVal] = field(default_factory=dict)
    is_bound: Dict[str, _AbstractVal] = field(default_factory=dict)
    is_open: Dict[str, _AbstractVal] = field(default_factory=dict)
    has_key: Dict[str, _AbstractVal] = field(default_factory=dict)
    is_in_domain: Dict[str, _AbstractVal] = field(default_factory=dict)
    carrier: Dict[str, TypeBase] = field(default_factory=dict)

    def copy(self) -> '_Stalk':
        """Restriction to an identical sub-site (identity morphism)."""
        return _Stalk(
            is_none=dict(self.is_none),
            is_zero=dict(self.is_zero),
            is_negative=dict(self.is_negative),
            is_bound=dict(self.is_bound),
            is_open=dict(self.is_open),
            has_key=dict(self.has_key),
            is_in_domain=dict(self.is_in_domain),
            carrier=dict(self.carrier),
        )

    def join(self, other: '_Stalk') -> '_Stalk':
        """Cocycle condition at a join point: merge two local sections.

        At a control-flow join (e.g., after if/else), two branches provide
        local sections that must be glued.  The cocycle condition says:
        the glued section agrees with both branches on their overlap.
        If the branches disagree on a proposition, the glued section is ?.

        This is the categorical coproduct in the information ordering.
        """
        result = _Stalk()
        all_vars = set(self.is_none) | set(other.is_none)
        for v in all_vars:
            result.is_none[v] = self.is_none.get(v, _AbstractVal.UNKNOWN).join(
                other.is_none.get(v, _AbstractVal.UNKNOWN))
        all_vars = set(self.is_zero) | set(other.is_zero)
        for v in all_vars:
            result.is_zero[v] = self.is_zero.get(v, _AbstractVal.UNKNOWN).join(
                other.is_zero.get(v, _AbstractVal.UNKNOWN))
        all_vars = set(self.is_negative) | set(other.is_negative)
        for v in all_vars:
            result.is_negative[v] = self.is_negative.get(v, _AbstractVal.UNKNOWN).join(
                other.is_negative.get(v, _AbstractVal.UNKNOWN))
        all_vars = set(self.is_bound) | set(other.is_bound)
        for v in all_vars:
            result.is_bound[v] = self.is_bound.get(v, _AbstractVal.UNKNOWN).join(
                other.is_bound.get(v, _AbstractVal.UNKNOWN))
        all_vars = set(self.is_open) | set(other.is_open)
        for v in all_vars:
            result.is_open[v] = self.is_open.get(v, _AbstractVal.UNKNOWN).join(
                other.is_open.get(v, _AbstractVal.UNKNOWN))
        all_vars = set(self.has_key) | set(other.has_key)
        for v in all_vars:
            result.has_key[v] = self.has_key.get(v, _AbstractVal.UNKNOWN).join(
                other.has_key.get(v, _AbstractVal.UNKNOWN))
        all_vars = set(self.is_in_domain) | set(other.is_in_domain)
        for v in all_vars:
            result.is_in_domain[v] = self.is_in_domain.get(v, _AbstractVal.UNKNOWN).join(
                other.is_in_domain.get(v, _AbstractVal.UNKNOWN))
        # Carriers: keep only where both agree
        for v in set(self.carrier) & set(other.carrier):
            if self.carrier[v] is other.carrier[v]:
                result.carrier[v] = self.carrier[v]
        return result

    def refine_by_condition(self, test: ast.expr, positive: bool = True) -> '_Stalk':
        """Pullback along a condition morphism: restrict the stalk to the
        sub-site where the condition holds (or doesn't, if positive=False).

        In sheaf terms, a branch condition c defines a sub-site U_c ⊆ U.
        The pullback c*F(U) refines the stalk to carry additional information
        that c provides.  This is a genuine categorical pullback: we're
        computing F(U_c) = F(U) ×_{B} {⊤} along the condition map c : U → B.
        """
        refined = self.copy()

        # ── None checks: is/is not None ──
        if isinstance(test, ast.Compare) and len(test.ops) == 1:
            left = test.left
            cmp_op = test.ops[0]
            right = test.comparators[0]
            var_name = None
            is_none_cmp = False

            if isinstance(right, ast.Constant) and right.value is None:
                if isinstance(left, ast.Name):
                    var_name = left.id
                    is_none_cmp = True
            elif isinstance(left, ast.Constant) and left.value is None:
                if isinstance(right, ast.Name):
                    var_name = right.id
                    is_none_cmp = True

            if var_name and is_none_cmp:
                if isinstance(cmp_op, ast.Is):
                    val = _AbstractVal.TRUE if positive else _AbstractVal.FALSE
                    refined.is_none[var_name] = val
                elif isinstance(cmp_op, ast.IsNot):
                    val = _AbstractVal.FALSE if positive else _AbstractVal.TRUE
                    refined.is_none[var_name] = val
                elif isinstance(cmp_op, ast.Eq):
                    val = _AbstractVal.TRUE if positive else _AbstractVal.FALSE
                    refined.is_none[var_name] = val
                elif isinstance(cmp_op, ast.NotEq):
                    val = _AbstractVal.FALSE if positive else _AbstractVal.TRUE
                    refined.is_none[var_name] = val

            # ── Zero checks: == 0, != 0, > 0, < 0 ──
            if isinstance(left, ast.Name) and isinstance(right, ast.Constant):
                if isinstance(right.value, (int, float)):
                    if right.value == 0:
                        if isinstance(cmp_op, ast.Eq):
                            refined.is_zero[left.id] = (
                                _AbstractVal.TRUE if positive else _AbstractVal.FALSE)
                        elif isinstance(cmp_op, ast.NotEq):
                            refined.is_zero[left.id] = (
                                _AbstractVal.FALSE if positive else _AbstractVal.TRUE)
                        elif isinstance(cmp_op, (ast.Gt, ast.Lt)):
                            # x > 0 or x < 0 → definitely nonzero
                            if positive:
                                refined.is_zero[left.id] = _AbstractVal.FALSE
                            # ¬(x > 0) doesn't tell us x == 0
                        elif isinstance(cmp_op, ast.GtE):
                            if positive:
                                refined.is_negative[left.id] = _AbstractVal.FALSE

        # ── isinstance → carrier refinement ──
        if isinstance(test, ast.Call) and isinstance(test.func, ast.Name):
            if test.func.id == 'isinstance' and len(test.args) >= 2:
                if isinstance(test.args[0], ast.Name):
                    var_name = test.args[0].id
                    if positive:
                        # We know the carrier type narrows
                        refined.is_none[var_name] = _AbstractVal.FALSE
                        type_arg = test.args[1]
                        if isinstance(type_arg, ast.Name):
                            _CARRIER_MAP = {
                                'int': INT_TYPE, 'float': FLOAT_TYPE,
                                'str': STR_TYPE, 'bool': BOOL_TYPE,
                            }
                            if type_arg.id in _CARRIER_MAP:
                                refined.carrier[var_name] = _CARRIER_MAP[type_arg.id]

        # ── Membership test: `x in d` / `x not in d` → has_key refinement ──
        if isinstance(test, ast.Compare) and len(test.ops) == 1:
            cmp_op = test.ops[0]
            if isinstance(cmp_op, ast.In) and isinstance(test.left, ast.Name):
                key_var = test.left.id
                refined.has_key[key_var] = _AbstractVal.TRUE if positive else _AbstractVal.FALSE
            elif isinstance(cmp_op, ast.NotIn) and isinstance(test.left, ast.Name):
                key_var = test.left.id
                refined.has_key[key_var] = _AbstractVal.FALSE if positive else _AbstractVal.TRUE

        # ── Truthiness test: `if x:` → x is not None and not zero ──
        if isinstance(test, ast.Name):
            if positive:
                refined.is_none[test.id] = _AbstractVal.FALSE
                refined.is_zero[test.id] = _AbstractVal.FALSE
            # ¬(if x:) means x is falsy but could be None, 0, "", etc.

        # ── `not` operator: contravariantly flip ──
        if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
            return self.refine_by_condition(test.operand, positive=not positive)

        # ── `and` / `or` — pullback along conjunction/disjunction ──
        if isinstance(test, ast.BoolOp):
            if isinstance(test.op, ast.And):
                if positive:
                    # All conjuncts hold: iterated pullback
                    result = refined
                    for value in test.values:
                        result = result.refine_by_condition(value, positive=True)
                    return result
                # ¬(a ∧ b) = ¬a ∨ ¬b — can't refine (cocycle disagrees)
            elif isinstance(test.op, ast.Or):
                if not positive:
                    # ¬(a ∨ b) = ¬a ∧ ¬b: iterated pullback
                    result = refined
                    for value in test.values:
                        result = result.refine_by_condition(value, positive=False)
                    return result
                # a ∨ b in positive: can't refine (disjunction = union of sub-sites)

        return refined

    def to_predicate(self, var_name: str) -> Predicate:
        """Concretize the stalk into a deppy Predicate via the Galois connection.

        The Galois connection α : Concrete ⇄ Abstract : γ maps:
          - α(concrete set) → abstract stalk (abstraction)
          - γ(abstract stalk) → concrete predicate (concretization)

        This function computes γ: we read definite facts from the stalk
        coordinates and conjoin them into a concrete refinement predicate.
        """
        conjuncts: List[Predicate] = []

        nv = self.is_none.get(var_name, _AbstractVal.UNKNOWN)
        if nv is _AbstractVal.FALSE:
            conjuncts.append(Comparison(op='!=', left=Var(f"{var_name}_is_none"), right=IntLit(1)))
        elif nv is _AbstractVal.TRUE:
            conjuncts.append(Comparison(op='==', left=Var(f"{var_name}_is_none"), right=IntLit(1)))

        zv = self.is_zero.get(var_name, _AbstractVal.UNKNOWN)
        if zv is _AbstractVal.FALSE:
            conjuncts.append(Comparison(op='!=', left=Var(var_name), right=IntLit(0)))
        elif zv is _AbstractVal.TRUE:
            conjuncts.append(Comparison(op='==', left=Var(var_name), right=IntLit(0)))

        bv = self.is_bound.get(var_name, _AbstractVal.UNKNOWN)
        if bv is _AbstractVal.TRUE:
            conjuncts.append(Comparison(op='==', left=Var(f"bound_{var_name}"), right=IntLit(1)))

        ov = self.is_open.get(var_name, _AbstractVal.UNKNOWN)
        if ov is _AbstractVal.TRUE:
            conjuncts.append(Comparison(op='==', left=Var(f"open_{var_name}"), right=IntLit(1)))
        elif ov is _AbstractVal.FALSE:
            conjuncts.append(Comparison(op='==', left=Var(f"open_{var_name}"), right=IntLit(0)))

        kv = self.has_key.get(var_name, _AbstractVal.UNKNOWN)
        if kv is _AbstractVal.TRUE:
            conjuncts.append(Comparison(op='==', left=Var(f"{var_name}_exists"), right=IntLit(1)))

        dv = self.is_in_domain.get(var_name, _AbstractVal.UNKNOWN)
        if dv is _AbstractVal.TRUE:
            conjuncts.append(Comparison(op='==', left=Var(f"{var_name}_in_domain"), right=IntLit(1)))

        if not conjuncts:
            return And(conjuncts=[])  # True (no information)
        if len(conjuncts) == 1:
            return conjuncts[0]
        return And(conjuncts=conjuncts)

    def subsumes_requirement(self, req: 'SectionRequirement') -> bool:
        """Check if this stalk's section already implies the requirement.

        This is the sheaf-theoretic totality check: does the restriction map
        ρ : F(avail) → F(req) exist?  If the stalk already carries the
        information that the requirement demands, the map is total and
        there's no gluing obstruction.

        This lets the abstract interpretation resolve obstructions directly,
        without needing Z3 — the presheaf section computation alone proves
        that the local sections glue.
        """
        bug = req.bug_type
        var = _extract_var_from_site(req)
        if not var:
            return False

        # NULL_PTR: requires is_none = FALSE
        if bug == "NULL_PTR":
            return self.is_none.get(var, _AbstractVal.UNKNOWN).is_definitely_false

        # DIV_ZERO: requires is_zero = FALSE
        if bug == "DIV_ZERO":
            return self.is_zero.get(var, _AbstractVal.UNKNOWN).is_definitely_false

        # UNBOUND_VAR: requires is_bound = TRUE
        if bug == "UNBOUND_VAR":
            return self.is_bound.get(var, _AbstractVal.UNKNOWN).is_definitely_true

        # USE_AFTER_FREE / USE_AFTER_CLOSE: requires is_open = TRUE
        if bug in ("USE_AFTER_FREE", "USE_AFTER_CLOSE"):
            return self.is_open.get(var, _AbstractVal.UNKNOWN).is_definitely_true

        # DOUBLE_FREE / DOUBLE_CLOSE: requires is_open = TRUE (before second close)
        if bug in ("DOUBLE_FREE", "DOUBLE_CLOSE"):
            return self.is_open.get(var, _AbstractVal.UNKNOWN).is_definitely_true

        # KEY_ERROR: requires has_key = TRUE
        if bug == "KEY_ERROR":
            return self.has_key.get(var, _AbstractVal.UNKNOWN).is_definitely_true

        # FP_DOMAIN: requires is_in_domain = TRUE
        if bug == "FP_DOMAIN":
            return self.is_in_domain.get(var, _AbstractVal.UNKNOWN).is_definitely_true

        return False


class _PresheafAnalyzer:
    """Forward abstract interpreter as presheaf section computation.

    Computes the global section of the refinement presheaf

        F : Sites^op → DepCtx

    by forward dataflow analysis.  Each basic block / statement is a site,
    and the transfer function for statement s at site U is the restriction map

        ρ_{U,U'} : F(U) → F(U')

    where U' is the successor site.  The restriction map is monotone in the
    information ordering (we only ADD refinement, never forget — unless at
    join points where the cocycle condition forces us to lose information).

    The fixpoint of the analysis IS the global section: a consistent
    assignment of refinement stalks to all sites.
    """

    def __init__(self, tree: ast.AST) -> None:
        self._tree = tree
        self._stalks: Dict[int, _Stalk] = {}  # line → stalk at that site

    def analyze(self) -> Dict[int, _Stalk]:
        """Compute the global section by forward analysis.

        Returns: mapping from line number to the presheaf stalk at that site.
        """
        for func_node in ast.walk(self._tree):
            if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue

            # Initialize the entry stalk: parameters are bound, not-none is unknown
            entry = _Stalk()
            for arg in func_node.args.args:
                entry.is_bound[arg.arg] = _AbstractVal.TRUE
                # Parameters are unknown in all other dimensions
            for arg in func_node.args.posonlyargs:
                entry.is_bound[arg.arg] = _AbstractVal.TRUE
            for arg in func_node.args.kwonlyargs:
                entry.is_bound[arg.arg] = _AbstractVal.TRUE
            if func_node.args.vararg:
                entry.is_bound[func_node.args.vararg.arg] = _AbstractVal.TRUE
            if func_node.args.kwarg:
                entry.is_bound[func_node.args.kwarg.arg] = _AbstractVal.TRUE

            # Forward-propagate through the body
            self._analyze_body(func_node.body, entry)

        return self._stalks

    def _analyze_body(self, stmts: List[ast.stmt], stalk: _Stalk) -> _Stalk:
        """Propagate the stalk through a sequence of statements.

        Each statement s_i defines a site U_i.  The transfer function for s_i
        is the restriction map ρ_{U_i, U_{i+1}} that transforms the stalk.
        """
        current = stalk
        for stmt in stmts:
            current = self._transfer(stmt, current)
        return current

    def _transfer(self, stmt: ast.stmt, stalk: _Stalk) -> _Stalk:
        """Transfer function = restriction map for a single statement.

        Computes ρ_{U,U'} : F(U) → F(U'), where U is the site before
        the statement and U' is the site after.
        """
        # Record the stalk at this line
        self._stalks[getattr(stmt, 'lineno', 0)] = stalk

        # ── Assignment: update the stalk with new bindings ──
        if isinstance(stmt, ast.Assign):
            result = stalk.copy()
            for target in stmt.targets:
                if isinstance(target, ast.Name):
                    var = target.id
                    result.is_bound[var] = _AbstractVal.TRUE
                    # Infer value properties from the RHS
                    self._transfer_assign_rhs(result, var, stmt.value)
            return result

        if isinstance(stmt, ast.AugAssign):
            result = stalk.copy()
            if isinstance(stmt.target, ast.Name):
                result.is_bound[stmt.target.id] = _AbstractVal.TRUE
                # Augmented assignment: result properties depend on op
                # e.g., x += 1 where x was zero → x is nonzero
                result.is_zero[stmt.target.id] = _AbstractVal.UNKNOWN
                result.is_none[stmt.target.id] = _AbstractVal.FALSE  # arithmetic result is never None
            return result

        # ── If/else: pullback + join (the core sheaf operation) ──
        if isinstance(stmt, ast.If):
            # Pullback along condition: compute stalk in true/false sub-sites
            true_entry = stalk.refine_by_condition(stmt.test, positive=True)
            false_entry = stalk.refine_by_condition(stmt.test, positive=False)

            # Propagate through both branches
            true_exit = self._analyze_body(stmt.body, true_entry)
            false_exit = (self._analyze_body(stmt.orelse, false_entry)
                         if stmt.orelse else false_entry)

            # Check if either branch terminates (return/raise/break)
            true_terminates = _body_terminates(stmt.body)
            false_terminates = _body_terminates(stmt.orelse) if stmt.orelse else False

            if true_terminates and false_terminates:
                # Both branches exit: stalk is dead (⊥), but we return the join
                # as a conservative approximation
                return true_exit.join(false_exit)
            if true_terminates:
                # Only the false branch continues: no join needed
                return false_exit
            if false_terminates:
                # Only the true branch continues
                return true_exit

            # Cocycle condition: both branches continue, must glue stalks
            return true_exit.join(false_exit)

        # ── For loop: join entry with back-edge (widening after 1 iteration) ──
        if isinstance(stmt, ast.For):
            result = stalk.copy()
            if isinstance(stmt.target, ast.Name):
                result.is_bound[stmt.target.id] = _AbstractVal.TRUE
                result.is_none[stmt.target.id] = _AbstractVal.UNKNOWN
            body_exit = self._analyze_body(stmt.body, result)
            # Widen: join entry and body exit (lose precision from loop)
            return result.join(body_exit)

        # ── While loop: similar, with condition refinement ──
        if isinstance(stmt, ast.While):
            loop_entry = stalk.refine_by_condition(stmt.test, positive=True)
            body_exit = self._analyze_body(stmt.body, loop_entry)
            # Widen: fixpoint approximation via single join
            widened = stalk.join(body_exit)
            # After loop: condition is false
            return widened.refine_by_condition(stmt.test, positive=False)

        # ── With statement: resource is open inside, closed after ──
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            result = stalk.copy()
            for item in stmt.items:
                if item.optional_vars and isinstance(item.optional_vars, ast.Name):
                    var = item.optional_vars.id
                    result.is_bound[var] = _AbstractVal.TRUE
                    result.is_none[var] = _AbstractVal.FALSE
                    result.is_open[var] = _AbstractVal.TRUE
            body_exit = self._analyze_body(stmt.body, result)
            # After with: resource is closed
            after = body_exit.copy()
            for item in stmt.items:
                if item.optional_vars and isinstance(item.optional_vars, ast.Name):
                    after.is_open[item.optional_vars.id] = _AbstractVal.FALSE
            return after

        # ── Try/except: join of normal and exception paths ──
        if isinstance(stmt, ast.Try):
            normal_exit = self._analyze_body(stmt.body, stalk)
            handler_exits = []
            for handler in stmt.handlers:
                h_stalk = stalk.copy()
                if handler.name:
                    h_stalk.is_bound[handler.name] = _AbstractVal.TRUE
                    h_stalk.is_none[handler.name] = _AbstractVal.FALSE
                h_exit = self._analyze_body(handler.body, h_stalk)
                handler_exits.append(h_exit)
            # Join normal and all handler exits
            result = normal_exit
            for h_exit in handler_exits:
                result = result.join(h_exit)
            if stmt.orelse:
                result = self._analyze_body(stmt.orelse, result)
            if stmt.finalbody:
                result = self._analyze_body(stmt.finalbody, result)
            return result

        # ── Expression statement (e.g., function call) ──
        if isinstance(stmt, ast.Expr):
            result = stalk.copy()
            # .close() call → resource transitions to CLOSED
            if isinstance(stmt.value, ast.Call) and isinstance(stmt.value.func, ast.Attribute):
                if stmt.value.func.attr == 'close':
                    obj = stmt.value.func.value
                    if isinstance(obj, ast.Name):
                        result.is_open[obj.id] = _AbstractVal.FALSE
            return result

        # ── Return: record stalk but don't propagate ──
        if isinstance(stmt, ast.Return):
            return stalk

        # ── Delete: unbind ──
        if isinstance(stmt, ast.Delete):
            result = stalk.copy()
            for target in stmt.targets:
                if isinstance(target, ast.Name):
                    result.is_bound[target.id] = _AbstractVal.FALSE
            return result

        # Default: identity restriction map (no information change)
        return stalk

    def _transfer_assign_rhs(self, stalk: _Stalk, var: str, value: ast.expr) -> None:
        """Compute stalk refinements from an assignment RHS.

        This is the restriction map component that flows type information
        from the RHS expression into the variable's stalk coordinates.
        """
        # Reset to unknown first (assignment overwrites)
        stalk.is_none[var] = _AbstractVal.UNKNOWN
        stalk.is_zero[var] = _AbstractVal.UNKNOWN
        stalk.is_negative[var] = _AbstractVal.UNKNOWN

        # None literal → definitely None
        if isinstance(value, ast.Constant):
            if value.value is None:
                stalk.is_none[var] = _AbstractVal.TRUE
                return
            stalk.is_none[var] = _AbstractVal.FALSE
            if isinstance(value.value, (int, float)):
                stalk.is_zero[var] = (
                    _AbstractVal.TRUE if value.value == 0 else _AbstractVal.FALSE)
                stalk.is_negative[var] = (
                    _AbstractVal.TRUE if value.value < 0 else _AbstractVal.FALSE)
            if isinstance(value.value, int):
                stalk.carrier[var] = INT_TYPE
            elif isinstance(value.value, float):
                stalk.carrier[var] = FLOAT_TYPE
            elif isinstance(value.value, str):
                stalk.carrier[var] = STR_TYPE
            elif isinstance(value.value, bool):
                stalk.carrier[var] = BOOL_TYPE
            return

        # Constructor calls: int(), str(), float(), list(), dict(), etc.
        if isinstance(value, ast.Call) and isinstance(value.func, ast.Name):
            constructor_map = {
                'int': (INT_TYPE, _AbstractVal.FALSE),
                'float': (FLOAT_TYPE, _AbstractVal.FALSE),
                'str': (STR_TYPE, _AbstractVal.FALSE),
                'bool': (BOOL_TYPE, _AbstractVal.FALSE),
                'list': (ListType(element=ANY_TYPE), _AbstractVal.FALSE),
                'dict': (DictType(key=ANY_TYPE, value=ANY_TYPE), _AbstractVal.FALSE),
            }
            if value.func.id in constructor_map:
                carrier, is_none = constructor_map[value.func.id]
                stalk.carrier[var] = carrier
                stalk.is_none[var] = is_none
                return

        # open() → resource is open
        if isinstance(value, ast.Call) and isinstance(value.func, ast.Name):
            if value.func.id == 'open':
                stalk.is_open[var] = _AbstractVal.TRUE
                stalk.is_none[var] = _AbstractVal.FALSE

        # List/Dict/Set/Tuple literal → not None
        if isinstance(value, (ast.List, ast.Dict, ast.Set, ast.Tuple)):
            stalk.is_none[var] = _AbstractVal.FALSE

        # BinOp result → not None (arithmetic/string ops produce values)
        if isinstance(value, ast.BinOp):
            stalk.is_none[var] = _AbstractVal.FALSE

        # Name copy: propagate stalk from the source variable
        if isinstance(value, ast.Name):
            src = value.id
            for dim in ('is_none', 'is_zero', 'is_negative', 'is_bound', 'is_open',
                       'has_key', 'is_in_domain'):
                src_map = getattr(stalk, dim)
                if src in src_map:
                    src_map[var] = src_map[src]
            if src in stalk.carrier:
                stalk.carrier[var] = stalk.carrier[src]

    def stalk_at(self, line: int) -> _Stalk:
        """Get the presheaf stalk at a given line (site).

        If the exact line isn't recorded, returns the closest preceding stalk
        (restriction to a sub-site inherits the parent stalk).
        """
        if line in self._stalks:
            return self._stalks[line]
        # Find the closest preceding line
        candidates = [l for l in self._stalks if l <= line]
        if candidates:
            return self._stalks[max(candidates)]
        return _Stalk()  # Terminal object: no information


def _body_terminates(stmts: List[ast.stmt]) -> bool:
    """Check if a statement list always terminates (return/raise/break)."""
    if not stmts:
        return False
    last = stmts[-1]
    if isinstance(last, (ast.Return, ast.Raise, ast.Break)):
        return True
    if isinstance(last, ast.If):
        return (_body_terminates(last.body) and
                _body_terminates(last.orelse) if last.orelse else False)
    return False


def _assign_available_sections(
    source: str,
    requirements: List[SectionRequirement],
    cover: Optional[Cover],
) -> Tuple[Dict[int, TypeSection], _PresheafAnalyzer]:
    """Assign available type sections via presheaf forward analysis.

    Runs the forward abstract interpreter to compute the global section of
    the refinement presheaf, then reads off the stalk at each requirement
    site to produce a concrete available section.

    The available section at requirement site R is:

        F(R) = γ(stalk_R)   (concretization via Galois connection)

    where stalk_R is the presheaf stalk at R's line, and γ maps the abstract
    stalk coordinates to a concrete deppy Predicate.  This predicate then
    flows into the gluing gap computation:

        gap = F(R)_available ∧ ¬F(R)_required

    A strengthened available section (from the abstract interpretation)
    narrows the gap, potentially making it UNSAT → spurious obstruction.

    Returns both the section mapping and the analyzer, so that downstream
    phases can query stalks directly (e.g., for subsumption checks that
    resolve obstructions without Z3).
    """
    tree = ast.parse(textwrap.dedent(source))
    sections: Dict[int, TypeSection] = {}

    # Run the presheaf analyzer: compute global section
    analyzer = _PresheafAnalyzer(tree)
    analyzer.analyze()

    for i, req in enumerate(requirements):
        # Read the stalk at this requirement's site
        stalk = analyzer.stalk_at(req.line)

        # Extract the relevant variable name from the requirement's site_id
        # Site names follow patterns like "div_L10", "attr_x_L5", "bind_x_L3"
        var_name = _extract_var_from_site(req)

        # Concretize: γ(stalk) → Predicate
        if var_name:
            pred = stalk.to_predicate(var_name)
            carrier = stalk.carrier.get(var_name, ANY_TYPE)
            trust = TrustLevel.TRUSTED_AUTO
        else:
            pred = And(conjuncts=[])  # True
            carrier = ANY_TYPE
            trust = TrustLevel.RESIDUAL

        sections[i] = TypeSection(
            site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"avail_{req.site_id.name}"),
            carrier=carrier,
            predicate=pred,
            trust=trust,
            provenance=f"presheaf stalk at L{req.line}" if var_name else "default: unconstrained",
        )

    return sections, analyzer


def _extract_var_from_site(req: SectionRequirement) -> Optional[str]:
    """Extract the variable name relevant to a section requirement.

    Inspects the requirement's AST node and site_id to determine which
    variable's stalk coordinates are relevant for the available section.
    """
    node = req.ast_node

    # Division: the divisor variable
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
        if isinstance(node.right, ast.Name):
            return node.right.id

    # Attribute access: the object being accessed
    if isinstance(node, ast.Attribute):
        if isinstance(node.value, ast.Name):
            return node.value.id

    # Subscript: index or object
    if isinstance(node, ast.Subscript):
        if isinstance(node.value, ast.Name):
            return node.value.id

    # Name reference (for UNBOUND_VAR)
    if isinstance(node, ast.Name):
        return node.id

    # Call: the function or first argument
    if isinstance(node, ast.Call):
        if isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name):
            return node.func.value.id

    # From site_id name: extract variable after last underscore
    name = req.site_id.name
    # Patterns: bind_x_L3, attr_x_L5, div_L10
    parts = name.split('_')
    if len(parts) >= 3 and parts[-1].startswith('L'):
        return '_'.join(parts[1:-1])

    return None


# ═══════════════════════════════════════════════════════════════════════════════
# Phase 3: Guard resolution — find guard sites whose sections resolve obstructions
#
# A BRANCH_GUARD site G that overlaps with requirement site R provides a
# restriction map: if G's predicate implies R's required predicate, the
# obstruction is resolved.
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class _GuardSite:
    """A guard extracted from the AST with its line range and predicate."""
    guard_type: str
    predicate: Predicate
    protects_against: Set[str]  # bug type codes
    start_line: int
    end_line: int
    condition_text: str
    protected_key: str = ""  # for key_exists guards: the specific key tested


def _extract_guard_sites(source: str) -> List[_GuardSite]:
    """Extract guard sites and the type refinements they provide.

    Each guard narrows the available type section within its scope,
    potentially making the restriction map to the requirement site total.
    """
    tree = ast.parse(textwrap.dedent(source))
    guards: List[_GuardSite] = []

    for node in ast.walk(tree):
        if isinstance(node, ast.If):
            try:
                cond_text = ast.unparse(node.test)
            except Exception:
                continue

            body_start = node.body[0].lineno if node.body else node.lineno
            body_end = max(
                (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                default=node.lineno,
            )

            # None checks → refines Optional[T] to T
            if "is not None" in cond_text or ("!= None" in cond_text):
                var = _extract_guarded_var(node.test, "not_none")
                guards.append(_GuardSite(
                    guard_type="not_none",
                    predicate=Comparison(op='!=', left=Var(f"{var}_is_none"), right=IntLit(1)),
                    protects_against={"NULL_PTR"},
                    start_line=body_start, end_line=body_end,
                    condition_text=cond_text,
                ))

            # Negated none checks → in the else branch
            if ("is None" in cond_text and "is not None" not in cond_text) or "== None" in cond_text:
                if node.orelse:
                    else_start = node.orelse[0].lineno
                    else_end = max(
                        (getattr(s, 'end_lineno', s.lineno) for s in node.orelse),
                        default=else_start,
                    )
                    var = _extract_guarded_var(node.test, "not_none")
                    guards.append(_GuardSite(
                        guard_type="not_none",
                        predicate=Comparison(op='!=', left=Var(f"{var}_is_none"), right=IntLit(1)),
                        protects_against={"NULL_PTR"},
                        start_line=else_start, end_line=else_end,
                        condition_text=f"else of: {cond_text}",
                    ))

            # Zero checks → refines int to {x | x ≠ 0}
            if "!= 0" in cond_text or "> 0" in cond_text or "< 0" in cond_text:
                var = _extract_guarded_var(node.test, "nonzero")
                guards.append(_GuardSite(
                    guard_type="nonzero",
                    predicate=Comparison(op='!=', left=Var(var), right=IntLit(0)),
                    protects_against={"DIV_ZERO"},
                    start_line=body_start, end_line=body_end,
                    condition_text=cond_text,
                ))

            # isinstance checks → refines Union to specific type
            if "isinstance(" in cond_text:
                guards.append(_GuardSite(
                    guard_type="isinstance",
                    predicate=BoolLit(True),  # Abstract: we just know the carrier narrows
                    protects_against={"TYPE_ERROR", "TYPE_CONFUSION"},
                    start_line=body_start, end_line=body_end,
                    condition_text=cond_text,
                ))

            # Positive/non-negative checks → refines FP domain
            if "> 0" in cond_text or ">= 0" in cond_text:
                guards.append(_GuardSite(
                    guard_type="positive",
                    predicate=BoolLit(True),
                    protects_against={"FP_DOMAIN"},
                    start_line=body_start, end_line=body_end,
                    condition_text=cond_text,
                ))

            # Length/bounds checks → refines index to {i | 0 ≤ i < len}
            if "len(" in cond_text and any(op in cond_text for op in (">", "<", ">=", "<=", "==")):
                guards.append(_GuardSite(
                    guard_type="bounds",
                    predicate=BoolLit(True),  # Abstract bound check
                    protects_against={"INDEX_OOB", "BOUNDS"},
                    start_line=body_start, end_line=body_end,
                    condition_text=cond_text,
                ))

            # Key existence / item-in-collection → refines to {k | k ∈ keys(d)}
            # Also protects VALUE_ERROR for `.remove()` calls
            if " in " in cond_text and "not" not in cond_text.split(" in ")[0].split()[-1:]:
                # Handle compound conditions: "k1 in d and k2 in d and ..."
                # Extract ALL tested keys, emit one guard per key
                import re as _re
                key_parts = _re.findall(r'(["\']?\w+["\']?)\s+in\s+', cond_text)
                if key_parts:
                    for tested_key in key_parts:
                        guards.append(_GuardSite(
                            guard_type="key_exists",
                            predicate=BoolLit(True),
                            protects_against={"KEY_ERROR", "VALUE_ERROR"},
                            start_line=body_start, end_line=body_end,
                            condition_text=cond_text,
                            protected_key=tested_key,
                        ))
                else:
                    tested_key = cond_text.split(" in ")[0].strip()
                    guards.append(_GuardSite(
                        guard_type="key_exists",
                        predicate=BoolLit(True),
                        protects_against={"KEY_ERROR", "VALUE_ERROR"},
                        start_line=body_start, end_line=body_end,
                        condition_text=cond_text,
                        protected_key=tested_key,
                    ))
            # "not in" → else branch has the key
            if " not in " in cond_text and node.orelse:
                else_start = node.orelse[0].lineno
                else_end = max(
                    (getattr(s, 'end_lineno', s.lineno) for s in node.orelse),
                    default=else_start,
                )
                tested_key_ni = cond_text.split(" not in ")[0].strip()
                guards.append(_GuardSite(
                    guard_type="key_exists",
                    predicate=BoolLit(True),
                    protects_against={"KEY_ERROR", "VALUE_ERROR"},
                    start_line=else_start, end_line=else_end,
                    condition_text=f"else of: {cond_text}",
                    protected_key=tested_key_ni,
                ))

        # try/except → exception handler sites catch specific bug types
        if isinstance(node, ast.Try):
            body_start = node.body[0].lineno if node.body else node.lineno
            body_end = max(
                (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                default=node.lineno,
            )
            for handler in node.handlers:
                exc_types = _handler_protects(handler)
                if exc_types:
                    guards.append(_GuardSite(
                        guard_type="try_except",
                        predicate=BoolLit(True),
                        protects_against=exc_types,
                        start_line=body_start, end_line=body_end,
                        condition_text=f"try/except {_handler_name(handler)}",
                    ))

    # ── with-statement guards: resolve MEMORY_LEAK, USE_AFTER_FREE, DOUBLE_FREE ──
    # A with-statement provides a GLOBAL SECTION of the lifecycle presheaf:
    # the resource is guaranteed OPEN inside the block and CLOSED after,
    # on ALL paths including exception paths.
    for node in ast.walk(tree):
        if isinstance(node, (ast.With, ast.AsyncWith)):
            body_start = node.body[0].lineno if node.body else node.lineno
            body_end = max(
                (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                default=node.lineno,
            )
            # Inside the with block, the resource is OPEN → resolves USE_AFTER_FREE
            # The with block itself → resolves MEMORY_LEAK (cleanup guaranteed)
            guards.append(_GuardSite(
                guard_type="with_block",
                predicate=BoolLit(True),
                protects_against={"MEMORY_LEAK", "USE_AFTER_FREE", "DOUBLE_FREE",
                                  "USE_AFTER_CLOSE", "DOUBLE_CLOSE", "MISSING_CLEANUP"},
                start_line=body_start, end_line=body_end,
                condition_text=f"with-statement (lifecycle presheaf global section)",
            ))

        # ── Lock acquisition guards: resolve DATA_RACE ──
        # A with-lock block provides a section of the synchronization presheaf:
        # lock_held = True inside the block.
        if isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                ctx_text = ""
                try:
                    ctx_text = ast.unparse(item.context_expr)
                except Exception:
                    pass
                if 'lock' in ctx_text.lower() or 'Lock' in ctx_text or 'mutex' in ctx_text.lower():
                    body_start = node.body[0].lineno if node.body else node.lineno
                    body_end = max(
                        (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                        default=node.lineno,
                    )
                    guards.append(_GuardSite(
                        guard_type="lock_held",
                        predicate=BoolLit(True),
                        protects_against={"DATA_RACE", "CONCURRENT_MODIFICATION"},
                        start_line=body_start, end_line=body_end,
                        condition_text=f"with {ctx_text} (synchronization presheaf section)",
                    ))

        # ── hmac.compare_digest guard: resolve TIMING_CHANNEL ──
        if isinstance(node, ast.Call):
            try:
                call_text = ast.unparse(node)
            except Exception:
                call_text = ""
            if 'compare_digest' in call_text or 'secrets.compare_digest' in call_text:
                # The entire function containing this call is protected
                for parent in ast.walk(tree):
                    if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        for desc in ast.walk(parent):
                            if desc is node:
                                func_start = parent.body[0].lineno if parent.body else parent.lineno
                                func_end = max(
                                    (getattr(s, 'end_lineno', s.lineno) for s in parent.body),
                                    default=func_start + 100,
                                )
                                guards.append(_GuardSite(
                                    guard_type="constant_time_compare",
                                    predicate=BoolLit(True),
                                    protects_against={"TIMING_CHANNEL"},
                                    start_line=func_start, end_line=func_end,
                                    condition_text="hmac.compare_digest (constant-time comparison)",
                                ))

    # ── isinstance-then-convert guards: resolve TYPE_ERROR ──
    # Pattern: if not isinstance(x, T): x = T(x)
    # After this, x is guaranteed to be of type T.  This is an assertion-style
    # guard that provides a TYPE section for the rest of the function.
    for node in ast.walk(tree):
        if isinstance(node, ast.If):
            try:
                cond_text = ast.unparse(node.test)
            except Exception:
                continue
            # Check for: if not isinstance(x, T): x = T(x)
            if "not isinstance(" in cond_text and node.body:
                # Everything AFTER this if-block is guarded: x has type T
                if_end = max(
                    (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                    default=node.lineno,
                )
                # Find the enclosing function to get end line
                for parent in ast.walk(tree):
                    if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        for desc in ast.walk(parent):
                            if desc is node:
                                func_end = max(
                                    (getattr(s, 'end_lineno', s.lineno) for s in parent.body),
                                    default=if_end + 100,
                                )
                                guards.append(_GuardSite(
                                    guard_type="isinstance_convert",
                                    predicate=BoolLit(True),
                                    protects_against={"TYPE_ERROR", "TYPE_CONFUSION"},
                                    start_line=if_end + 1, end_line=func_end,
                                    condition_text=f"isinstance-then-convert: {cond_text}",
                                ))
                                break

    # ── max/min clamping guards: resolve INTEGER_OVERFLOW, OVERFLOW, BOUNDS ──
    # Pattern: x = max(lo, min(x, hi)) or x = min(hi, max(x, lo))
    # Also: x = min(x, len(buf)) — clamps slice upper to buffer length.
    # The clamped value is guaranteed in [lo, hi] → overflow resolved.
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            try:
                val_text = ast.unparse(node.value)
            except Exception:
                continue
            is_clamp = (('max(' in val_text and 'min(' in val_text) or
                        ('clamp' in val_text.lower()) or
                        ('min(' in val_text and 'len(' in val_text) or
                        ('max(' in val_text and (', 0)' in val_text or ', 0,' in val_text)))
            if is_clamp:
                assign_line = node.lineno
                assign_end = getattr(node, 'end_lineno', assign_line) or assign_line
                # Find enclosing function end
                for parent in ast.walk(tree):
                    if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        for desc in ast.walk(parent):
                            if desc is node:
                                func_end = max(
                                    (getattr(s, 'end_lineno', s.lineno) for s in parent.body),
                                    default=assign_end + 100,
                                )
                                guards.append(_GuardSite(
                                    guard_type="clamping",
                                    predicate=BoolLit(True),
                                    protects_against={"INTEGER_OVERFLOW", "OVERFLOW", "BOUNDS", "FP_DOMAIN"},
                                    start_line=assign_end, end_line=func_end,
                                    condition_text=f"clamping: {val_text[:60]}",
                                ))
                                break

    # ── Unconditional binding guards: resolve UNBOUND_VAR ──
    # If a variable is assigned UNCONDITIONALLY before use, the binding
    # presheaf section is total at the use site.
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            # Track unconditional assignments in the body
            for i, stmt in enumerate(node.body):
                if isinstance(stmt, ast.Assign):
                    for target in stmt.targets:
                        if isinstance(target, ast.Name):
                            var = target.id
                            # Everything after this assignment has the var bound
                            assign_end = getattr(stmt, 'end_lineno', stmt.lineno) or stmt.lineno
                            func_end = max(
                                (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                                default=assign_end + 100,
                            )
                            guards.append(_GuardSite(
                                guard_type="unconditional_binding",
                                predicate=BoolLit(True),
                                protects_against={"UNBOUND_VAR"},
                                start_line=assign_end + 1, end_line=func_end,
                                condition_text=f"unconditional assignment to `{var}` (binding presheaf section)",
                            ))

    # ── Early-return guards ──
    # Pattern: if cond: return/raise → everything AFTER the if is guarded by ¬cond
    # This is the most common guard pattern in Python
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for i, stmt in enumerate(node.body):
            if not isinstance(stmt, ast.If):
                continue
            # Check if the if-body ends with return or raise
            body_terminates = (
                stmt.body and
                isinstance(stmt.body[-1], (ast.Return, ast.Raise))
            )
            if not body_terminates:
                continue

            try:
                cond_text = ast.unparse(stmt.test)
            except Exception:
                continue

            # Everything after this if is guarded by ¬cond
            after_start = stmt.end_lineno + 1 if hasattr(stmt, 'end_lineno') and stmt.end_lineno else stmt.lineno + 1
            # End at the function end
            func_end = max(
                (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                default=after_start + 100,
            )

            # Determine what the negated condition protects.
            # The early-return pattern is Python's most common guard idiom:
            #   if bad_condition: return/raise
            #   # everything here is guarded by ¬bad_condition
            protects: Set[str] = set()

            if "== 0" in cond_text or "!= 0" in cond_text:
                protects.add("DIV_ZERO")
            if "is None" in cond_text or "== None" in cond_text:
                protects.add("NULL_PTR")
            if "not " in cond_text and " in " in cond_text:
                protects.add("KEY_ERROR")
            if "len(" in cond_text and ("== 0" in cond_text or "< " in cond_text or "<= 0" in cond_text):
                protects.update({"INDEX_OOB", "DIV_ZERO"})
            # `> len(` or `>= len(` → bounds check protects INDEX_OOB
            if "len(" in cond_text and ("> len(" in cond_text or ">= len(" in cond_text or
                                         "> len(" in cond_text.replace(" ", "")):
                protects.update({"INDEX_OOB", "BOUNDS"})
            # `if not items:` / `if not x:` → protects against empty-collection bugs
            if cond_text.startswith("not ") and " " not in cond_text[4:]:
                protects.update({"INDEX_OOB", "ASSERT_FAIL", "BOUNDS", "DIV_ZERO"})
            # isinstance checks → type guards
            if "isinstance(" in cond_text:
                protects.update({"TYPE_ERROR", "TYPE_CONFUSION"})
            # Range/value checks → overflow protection and FP domain
            if any(op in cond_text for op in ("> ", "< ", ">= ", "<= ")):
                protects.update({"INTEGER_OVERFLOW", "OVERFLOW", "BOUNDS", "FP_DOMAIN"})
            # `<= 0` or `< 0` guard before math.log/sqrt → FP domain
            if "<= 0" in cond_text or "< 0" in cond_text or "> 1" in cond_text or "< -1" in cond_text:
                protects.add("FP_DOMAIN")
            # `len(data) != N` → protects unpacking ValueError
            if "len(" in cond_text and ("!=" in cond_text or "==" in cond_text):
                protects.add("VALUE_ERROR")

            if protects:
                guards.append(_GuardSite(
                    guard_type="early_return",
                    predicate=BoolLit(True),
                    protects_against=protects,
                    start_line=after_start, end_line=func_end,
                    condition_text=f"after early return: if {cond_text}: return/raise",
                ))

    return guards


def _resolve_obstructions_with_guards(
    requirements: List[SectionRequirement],
    guards: List[_GuardSite],
) -> Dict[int, _GuardSite]:
    """For each requirement, find a guard that resolves its obstruction.

    A guard resolves requirement i if:
    1. The guard's line range covers the requirement's line
    2. The guard protects against the requirement's bug type
    3. For key_exists guards, the tested key must match the requirement key
    """
    resolutions: Dict[int, _GuardSite] = {}
    for i, req in enumerate(requirements):
        for g in guards:
            if req.bug_type in g.protects_against and g.start_line <= req.line <= g.end_line:
                # For key_exists guards, verify the specific key matches
                if g.guard_type == "key_exists" and g.protected_key and req.bug_type == "KEY_ERROR":
                    # Normalize key: strip quotes for comparison
                    guard_key = g.protected_key.strip("'\"")
                    # Try extracting actual key from requirement's ast_node
                    key_match = False
                    if hasattr(req, 'ast_node') and req.ast_node is not None:
                        if isinstance(req.ast_node, ast.Subscript):
                            try:
                                key_text = ast.unparse(req.ast_node.slice).strip("'\"")
                                if key_text == guard_key:
                                    key_match = True
                            except Exception:
                                pass
                    # Also check description for key name
                    if not key_match and guard_key in req.description:
                        key_match = True
                    if not key_match:
                        continue  # different key — don't resolve
                resolutions[i] = g
                break
    return resolutions


# ═══════════════════════════════════════════════════════════════════════════════
# Phase 4: Z3 discharge — check if unresolved obstructions are genuine
#
# For each unresolved obstruction, the "gap predicate" is:
#   ¬(available_predicate → required_predicate)
# which simplifies to:
#   available_predicate ∧ ¬required_predicate
#
# If this is SAT, there exists an input that triggers the bug.
# If UNSAT, the obstruction is spurious (the types are actually compatible).
# ═══════════════════════════════════════════════════════════════════════════════

def _discharge_obstruction(
    req: SectionRequirement,
    available: TypeSection,
) -> Tuple[str, float, float]:
    """Check if the gluing gap is genuine via Z3.

    Returns (z3_status, confidence, time_ms).
    """
    if not z3_available():
        return "assumed (Z3 unavailable)", 0.5, 0.0

    # The gap: available ∧ ¬required
    # Since available is often True (unconstrained), this reduces to
    # checking if ¬required is SAT (i.e., is there a value violating the requirement?)
    gap = And(conjuncts=[available.predicate, Not(req.required_predicate)])
    r = quick_check(gap)

    if r.status.value == "sat":
        return f"SAT (gap exists, {r.time_ms:.1f}ms)", 0.8, r.time_ms
    elif r.status.value == "unsat":
        return f"UNSAT (no gap, {r.time_ms:.1f}ms)", 0.0, r.time_ms
    else:
        return f"{r.status.value} ({r.time_ms:.1f}ms)", 0.4, r.time_ms


def _discharge_taint_obstruction(
    req: SectionRequirement,
    source_code: str,
    cover: Optional[Cover],
) -> Tuple[str, float, float]:
    """Check if a taint-flow obstruction is genuine.

    For taint bugs, the question is: does user-controlled data reach the
    sink site without passing through a sanitization site?

    In sheaf terms: is there a path in the cover's overlap graph from an
    ARGUMENT_BOUNDARY site to the sink site where no intermediate site's
    section carries the {sanitized} refinement?
    """
    if cover is None:
        return "structural (no cover)", 0.5, 0.0

    arg_sites = [sid for sid in cover.sites if sid.kind == SiteKind.ARGUMENT_BOUNDARY]
    if not arg_sites:
        return "no input boundary", 0.2, 0.0

    # Build adjacency from overlaps
    adj: Dict[SiteId, Set[SiteId]] = defaultdict(set)
    for a, b in cover.overlaps:
        adj[a].add(b)
        adj[b].add(a)

    # BFS: argument → sink
    for arg in arg_sites:
        visited = {arg}
        frontier = {arg}
        for _ in range(30):
            nxt = set()
            for s in frontier:
                for n in adj.get(s, set()):
                    if n not in visited:
                        visited.add(n)
                        nxt.add(n)
                        if n.name == req.site_id.name:
                            return (
                                f"taint path: {arg.name} →...→ {req.site_id.name}",
                                0.75, 0.0,
                            )
            frontier = nxt
            if not frontier:
                break

    return "no taint path in cover", 0.0, 0.0


# ═══════════════════════════════════════════════════════════════════════════════
# Main entry point
# ═══════════════════════════════════════════════════════════════════════════════

def detect_bugs(
    source: str,
    *,
    function_name: str = "",
    file_path: str = "<source>",
    bug_types: Optional[Set[str]] = None,
) -> SheafBugReport:
    """Detect bugs by checking type section gluing across the site cover.

    Pipeline:
      1. Synthesize site cover (Grothendieck topology on the function)
      2. Extract section requirements (what each site needs)
      3. Assign available sections (what flows in from upstream)
      4. Extract guard sites (refinement providers)
      5. Check gluing: for each requirement, does the available section
         restrict to satisfy it?  If not → obstruction (= candidate bug)
      6. Resolve obstructions with guards
      7. Discharge remaining obstructions with Z3
    """
    t0 = time.perf_counter()
    dedented = textwrap.dedent(source)

    # Infer function name
    if not function_name:
        tree = ast.parse(dedented)
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                function_name = node.name
                break

    # Phase 1: Build cover
    try:
        synth = SiteCoverSynthesizer()
        cover = synth.synthesize(dedented)
    except Exception:
        cover = None
    n_sites = len(cover.sites) if cover else 0
    n_overlaps = len(cover.overlaps) if cover else 0

    # Phase 2: Extract section requirements
    requirements = _extract_requirements(dedented)
    if bug_types:
        requirements = [r for r in requirements if r.bug_type in bug_types]

    # Phase 3: Assign available sections (presheaf forward analysis)
    available, presheaf = _assign_available_sections(dedented, requirements, cover)

    # Phase 4: Extract guard sites
    guards = _extract_guard_sites(dedented)

    # Phase 5: Resolve obstructions with guards
    resolutions = _resolve_obstructions_with_guards(requirements, guards)

    # Phase 5b: Presheaf stalk subsumption — resolve obstructions directly
    # from the global section without needing guard sites or Z3.
    # This is the most elegant resolution: the presheaf section at the
    # requirement site already implies the requirement, so the restriction
    # map ρ is provably total from the abstract interpretation alone.
    stalk_resolutions: Set[int] = set()
    for i, req in enumerate(requirements):
        if i not in resolutions:
            stalk = presheaf.stalk_at(req.line)
            if stalk.subsumes_requirement(req):
                stalk_resolutions.add(i)

    # Phase 6: Build obstructions and discharge
    obstructions: List[GluingObstruction] = []
    n_resolved = 0
    n_spurious = 0
    n_genuine = 0

    for i, req in enumerate(requirements):
        avail = available.get(i)

        # Stalk subsumption: presheaf section proves the map is total
        if i in stalk_resolutions:
            n_resolved += 1
            obstructions.append(GluingObstruction(
                bug_type=req.bug_type,
                requirement=req,
                available_section=avail,
                gap_predicate=And(conjuncts=[]),  # Resolved
                resolved_by_guard=True,
                guard_site=SiteId(kind=SiteKind.SSA_VALUE, name=f"stalk_L{req.line}"),
                guard_predicate=avail.predicate if avail else None,
                z3_status="resolved by presheaf stalk (ρ is total)",
                confidence=0.0,
                line=req.line, col=req.col,
                description=(
                    f"[SAFE] {req.description} — presheaf stalk subsumes requirement "
                    f"(restriction map total from abstract interpretation)"
                ),
            ))
            continue

        if i in resolutions:
            # Guard resolves this obstruction
            g = resolutions[i]
            obstructions.append(GluingObstruction(
                bug_type=req.bug_type,
                requirement=req,
                available_section=avail,
                gap_predicate=And(conjuncts=[]),  # Resolved
                resolved_by_guard=True,
                guard_site=SiteId(kind=SiteKind.BRANCH_GUARD, name=f"guard_L{g.start_line}"),
                guard_predicate=g.predicate,
                z3_status="resolved by guard",
                confidence=0.0,
                line=req.line, col=req.col,
                description=f"[SAFE] {req.description} — guarded by `{g.condition_text}`",
            ))
            n_resolved += 1
            continue

        # Unresolved: check if the gap is genuine
        spec = BUG_SPECS.get(req.bug_type)
        family = spec.family if spec else ObstructionFamily.REFINEMENT_GAP

        if family == ObstructionFamily.TAINT_LEAKAGE:
            z3_status, confidence, z3_ms = _discharge_taint_obstruction(req, dedented, cover)
        elif family == ObstructionFamily.CONFIGURATION_WEAKNESS:
            # Config weaknesses are structural — if the pattern matches, it's a finding
            z3_status, confidence, z3_ms = "structural match", 0.7, 0.0
        else:
            z3_status, confidence, z3_ms = _discharge_obstruction(req, avail)

        gap = And(conjuncts=[avail.predicate, Not(req.required_predicate)]) if avail else Not(req.required_predicate)

        if confidence <= 0:
            n_spurious += 1
        else:
            n_genuine += 1

        obstructions.append(GluingObstruction(
            bug_type=req.bug_type,
            requirement=req,
            available_section=avail,
            gap_predicate=gap,
            resolved_by_guard=False,
            z3_status=z3_status,
            z3_time_ms=z3_ms,
            confidence=confidence,
            line=req.line, col=req.col,
            description=f"{'[BUG]' if confidence > 0 else '[SAFE]'} {req.description} — {z3_status}",
        ))

    elapsed = (time.perf_counter() - t0) * 1000

    return SheafBugReport(
        file_path=file_path,
        function_name=function_name,
        n_sites=n_sites,
        n_overlaps=n_overlaps,
        n_requirements=len(requirements),
        n_sections_assigned=len(available),
        obstructions=obstructions,
        resolved_obstructions=n_resolved,
        spurious_obstructions=n_spurious,
        genuine_obstructions=n_genuine,
        elapsed_ms=elapsed,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Multi-function analysis
# ═══════════════════════════════════════════════════════════════════════════════

def detect_bugs_in_file(source: str, *, file_path: str = "<source>") -> List[SheafBugReport]:
    """Detect bugs in all functions in a source file."""
    tree = ast.parse(textwrap.dedent(source))
    reports = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            try:
                func_source = ast.unparse(node)
            except Exception:
                continue
            report = detect_bugs(func_source, function_name=node.name, file_path=file_path)
            reports.append(report)
    return reports


# ═══════════════════════════════════════════════════════════════════════════════
# Output formatter
# ═══════════════════════════════════════════════════════════════════════════════

def format_bug_report(report: SheafBugReport) -> str:
    """Format a bug report showing the sheaf-theoretic analysis."""
    lines = []
    hdr = f"Sheaf type-section analysis: {report.function_name} ({report.file_path})"
    lines.append(hdr)
    lines.append("═" * len(hdr))
    lines.append("")

    lines.append(f"Cover topology: {report.n_sites} sites, {report.n_overlaps} overlaps")
    lines.append(f"Section requirements extracted: {report.n_requirements}")
    lines.append("")
    lines.append("Gluing audit:")
    lines.append(f"  Resolved by guards (restriction maps exist):  {report.resolved_obstructions}")
    lines.append(f"  Spurious (Z3 UNSAT — sections actually glue): {report.spurious_obstructions}")
    lines.append(f"  Genuine obstructions (confirmed bugs):        {report.genuine_obstructions}")
    lines.append("")

    findings = report.findings
    if findings:
        lines.append("Obstructions (bugs as gluing failures):")
        lines.append("─" * 60)
        for i, ob in enumerate(findings, 1):
            spec = BUG_SPECS.get(ob.bug_type)
            family = spec.family.value if spec else "unknown"
            lines.append(f"  {i}. [{ob.bug_type}] line {ob.line} ({family})")
            lines.append(f"     {ob.requirement.description}")
            if spec:
                lines.append(f"     Required section: {spec.required_predicate_desc}")
            lines.append(f"     Available section: unconstrained (no upstream refinement)")
            lines.append(f"     Gap: {ob.z3_status} | confidence: {ob.confidence:.0%}")
        lines.append("")
    else:
        lines.append("No gluing obstructions — all local type sections are compatible.")
        lines.append("")

    # Show resolved obstructions for completeness
    resolved = [o for o in report.obstructions if o.resolved_by_guard]
    if resolved:
        lines.append("Resolved obstructions (guards provide restriction maps):")
        lines.append("─" * 60)
        for ob in resolved:
            lines.append(f"  ✓ [{ob.bug_type}] line {ob.line}: {ob.requirement.description}")
            lines.append(f"    Guard: {ob.guard_site.name if ob.guard_site else '?'}")
        lines.append("")

    lines.append(f"Elapsed: {report.elapsed_ms:.1f}ms")
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# AST helpers
# ═══════════════════════════════════════════════════════════════════════════════

def _expr_to_var_name(node: ast.AST, fallback: str) -> str:
    """Extract a variable name from an AST expression."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        prefix = _expr_to_var_name(node.value, "")
        return f"{prefix}_{node.attr}" if prefix else node.attr
    return fallback


def _expr_repr(node: ast.AST) -> str:
    """Get a short string representation of an AST expression."""
    try:
        return ast.unparse(node)
    except Exception:
        return "?"


def _is_index_access(node: ast.Subscript) -> bool:
    """Heuristic: is this subscript an integer index access?"""
    s = node.slice
    if isinstance(s, ast.Constant) and isinstance(s.value, int):
        return True
    if isinstance(s, ast.Name):
        return True
    if isinstance(s, ast.UnaryOp) and isinstance(s.op, ast.USub):
        return True
    if isinstance(s, ast.BinOp):
        return True
    # len(x) as index → always one-past-end (always OOB)
    if isinstance(s, ast.Call) and isinstance(s.func, ast.Name) and s.func.id == 'len':
        return True
    return False


def _is_dict_access(node: ast.Subscript) -> bool:
    """Heuristic: could this be a dictionary access?"""
    s = node.slice
    return isinstance(s, (ast.Name, ast.Constant))


def _get_call_name(node: ast.Call) -> str:
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        if isinstance(node.func.value, ast.Name):
            return f"{node.func.value.id}.{node.func.attr}"
        if isinstance(node.func.value, ast.Attribute):
            prefix = _get_call_name_inner(node.func.value)
            return f"{prefix}.{node.func.attr}"
    return ""


def _get_call_name_inner(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        prefix = _get_call_name_inner(node.value)
        return f"{prefix}.{node.attr}" if prefix else node.attr
    return ""


def _extract_guarded_var(test: ast.AST, context: str) -> str:
    """Extract the variable name being guarded in a condition."""
    if isinstance(test, ast.Compare):
        return _expr_to_var_name(test.left, f"guarded_{context}")
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _extract_guarded_var(test.operand, context)
    if isinstance(test, ast.Call):
        if test.args:
            return _expr_to_var_name(test.args[0], f"guarded_{context}")
    return f"guarded_{context}"


def _handler_protects(handler: ast.ExceptHandler) -> Set[str]:
    """Determine which bug types a try/except handler protects against."""
    if handler.type is None:
        return {"NULL_PTR", "INDEX_OOB", "KEY_ERROR", "TYPE_ERROR",
                "DIV_ZERO", "ASSERT_FAIL", "VALUE_ERROR", "RUNTIME_ERROR",
                "FP_DOMAIN", "STACK_OVERFLOW"}
    try:
        exc_name = ast.unparse(handler.type)
    except Exception:
        return set()
    mapping = {
        "ZeroDivisionError": {"DIV_ZERO"},
        "TypeError": {"TYPE_ERROR", "TYPE_CONFUSION"},
        "IndexError": {"INDEX_OOB", "BOUNDS"},
        "KeyError": {"KEY_ERROR"},
        "AttributeError": {"NULL_PTR"},
        "AssertionError": {"ASSERT_FAIL"},
        "ValueError": {"VALUE_ERROR", "TYPE_ERROR", "BOUNDS", "FP_DOMAIN"},
        "OverflowError": {"INTEGER_OVERFLOW", "OVERFLOW"},
        "RecursionError": {"STACK_OVERFLOW", "NON_TERMINATION"},
        "FileNotFoundError": {"FILE_NOT_FOUND"},
        "PermissionError": {"PERMISSION_ERROR"},
        "OSError": {"OS_ERROR", "IO_ERROR"},
        "IOError": {"IO_ERROR"},
        "ImportError": {"IMPORT_ERROR"},
        "ModuleNotFoundError": {"MODULE_NOT_FOUND"},
        "NameError": {"NAME_ERROR", "UNBOUND_VAR"},
        "UnboundLocalError": {"UNBOUND_LOCAL", "UNBOUND_VAR"},
        "RuntimeError": {"RUNTIME_ERROR", "STACK_OVERFLOW"},
        "TimeoutError": {"TIMEOUT_ERROR"},
        "ConnectionError": {"CONNECTION_ERROR"},
        "UnicodeError": {"UNICODE_ERROR"},
        "LookupError": {"LOOKUP_ERROR", "INDEX_OOB", "KEY_ERROR"},
        "StopIteration": {"ITERATOR_INVALID"},
        "Exception": {"NULL_PTR", "INDEX_OOB", "KEY_ERROR", "TYPE_ERROR",
                       "DIV_ZERO", "ASSERT_FAIL", "VALUE_ERROR", "RUNTIME_ERROR",
                       "FP_DOMAIN", "STACK_OVERFLOW"},
        "BaseException": {"NULL_PTR", "INDEX_OOB", "KEY_ERROR", "TYPE_ERROR",
                          "DIV_ZERO", "ASSERT_FAIL", "VALUE_ERROR", "RUNTIME_ERROR",
                          "FP_DOMAIN", "STACK_OVERFLOW"},
    }
    result: Set[str] = set()
    for key, codes in mapping.items():
        if key in exc_name:
            result.update(codes)
    return result


def _handler_name(handler: ast.ExceptHandler) -> str:
    if handler.type is None:
        return "bare except"
    try:
        return ast.unparse(handler.type)
    except Exception:
        return "?"


# ═══════════════════════════════════════════════════════════════════════════════
# Taint sink and configuration weakness detection tables
# ═══════════════════════════════════════════════════════════════════════════════

def _get_taint_sink_spec(
    func_name: str, node: ast.Call
) -> Optional[Tuple[str, str, int]]:
    """If func_name is a known injection sink, return (bug_code, desc, arg_index)."""
    sinks = {
        # Command injection
        "os.system": ("COMMAND_INJECTION", "os.system with potentially tainted command", 0),
        "os.popen": ("COMMAND_INJECTION", "os.popen with potentially tainted command", 0),
        "subprocess.call": ("COMMAND_INJECTION", "subprocess with potentially tainted command", 0),
        "subprocess.run": ("COMMAND_INJECTION", "subprocess with potentially tainted command", 0),
        "subprocess.Popen": ("COMMAND_INJECTION", "subprocess with potentially tainted command", 0),
        "subprocess.check_output": ("COMMAND_INJECTION", "subprocess with potentially tainted command", 0),
        "subprocess.check_call": ("COMMAND_INJECTION", "subprocess with potentially tainted command", 0),
        # Code injection
        "eval": ("CODE_INJECTION", "eval with potentially tainted code", 0),
        "exec": ("CODE_INJECTION", "exec with potentially tainted code", 0),
        "compile": ("CODE_INJECTION", "compile with potentially tainted code", 0),
    }
    if func_name in sinks:
        # For subprocess, check shell=True
        if func_name.startswith("subprocess."):
            shell_true = any(
                isinstance(kw.value, ast.Constant) and kw.value.value is True
                for kw in node.keywords if kw.arg == "shell"
            )
            if not shell_true:
                return None
        return sinks[func_name]

    # SQL injection: *.execute with string interpolation
    if func_name and "execute" in func_name:
        if node.args and isinstance(node.args[0], (ast.JoinedStr, ast.BinOp)):
            return ("SQL_INJECTION", f"{func_name} with string-interpolated query", 0)

    # Path injection: open() with dynamic path
    if func_name in ("open", "builtins.open", "io.open"):
        if node.args and isinstance(node.args[0], (ast.JoinedStr, ast.BinOp)):
            return ("PATH_INJECTION", f"open() with dynamically constructed path", 0)

    return None


def _get_config_weakness_spec(
    func_name: str, node: ast.Call
) -> Optional[Tuple[str, str, Any]]:
    """If func_name is a known configuration-sensitive API, return (bug_code, desc, predicate)."""

    # Unsafe deserialization
    if func_name in ("pickle.loads", "pickle.load", "marshal.loads", "shelve.open"):
        return ("UNSAFE_DESERIALIZATION",
                f"{func_name}: deserializing untrusted data",
                Comparison(op='==', left=Var("safe_loader"), right=IntLit(0)))

    if func_name == "yaml.load":
        has_safe = any(
            kw.arg == "Loader" and isinstance(kw.value, ast.Attribute)
            and "Safe" in getattr(kw.value, 'attr', '')
            for kw in node.keywords
        )
        if not has_safe:
            return ("UNSAFE_DESERIALIZATION",
                    "yaml.load without SafeLoader",
                    Comparison(op='==', left=Var("safe_loader"), right=IntLit(0)))

    # Flask debug
    if func_name in ("app.run", "Flask.run"):
        debug_true = any(
            kw.arg == "debug" and isinstance(kw.value, ast.Constant) and kw.value.value is True
            for kw in node.keywords
        )
        if debug_true:
            return ("FLASK_DEBUG",
                    "Flask app running in debug mode",
                    Comparison(op='==', left=Var("debug"), right=IntLit(1)))

    # Weak crypto
    if func_name in ("hashlib.md5", "hashlib.sha1"):
        return ("WEAK_CRYPTO",
                f"{func_name}: weak hash algorithm",
                Comparison(op='==', left=Var("strong_hash"), right=IntLit(0)))

    # Insecure requests
    if func_name in ("requests.get", "requests.post", "requests.put", "requests.delete"):
        verify_false = any(
            kw.arg == "verify" and isinstance(kw.value, ast.Constant) and kw.value.value is False
            for kw in node.keywords
        )
        if verify_false:
            return ("CERT_VALIDATION_DISABLED",
                    f"{func_name} with verify=False",
                    Comparison(op='==', left=Var("cert_verify"), right=IntLit(0)))

    # Bind to all interfaces
    if func_name in ("socket.bind", "server.bind"):
        if node.args:
            try:
                arg_text = ast.unparse(node.args[0])
            except Exception:
                arg_text = ""
            if "0.0.0.0" in arg_text:
                return ("BIND_TO_ALL_INTERFACES",
                        "binding to 0.0.0.0 (all interfaces)",
                        Comparison(op='==', left=Var("bind_all"), right=IntLit(1)))

    return None
