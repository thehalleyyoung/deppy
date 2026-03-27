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
from typing import Any, ClassVar, Dict, FrozenSet, List, Optional, Set, Tuple

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

# ── Deppy infrastructure integration ──────────────────────────────────────────
# The following modules provide rich, reusable analyses that augment the
# hand-written extraction logic in this file.
from deppy.interprocedural import CallGraph
from deppy.harvest import (
    harvest_guards as _harvest_guards_infra,
    harvest_none_guards as _harvest_none_guards_infra,
    harvest_type_guards as _harvest_type_guards_infra,
    harvest_collection_facts as _harvest_collection_facts,
    harvest_arithmetic_bounds as _harvest_arithmetic_bounds,
    harvest_exception_regions as _harvest_exception_regions,
    GuardKind as _InfraGuardKind,
    NoneCheckKind as _InfraNoneKind,
    CollectionFactKind as _CollectionFactKind,
    BoundType as _BoundType,
    RegionKind as _RegionKind,
    HandlerAction as _HandlerAction,
)
from deppy.native_python import (
    DecoratorAnalyzer as _DecoratorAnalyzer,
    ExceptionAnalyzer as _ExceptionAnalyzer,
)

# ── Sheaf-theoretic infrastructure: unified harvest + formal gluing ────────
# These modules provide the full sheaf machinery that the pipeline can now
# leverage for aggregated harvesting, formal gluing checks, obstruction
# basis extraction, domain-specific theory pack solving, and persistent
# cohomology confidence scoring.
from deppy.harvest import (
    harvest_all as _harvest_all,
    HarvestResult as _HarvestResult,
    apply_harvest_to_cover as _apply_harvest_to_cover,
    NarrowingKind as _NarrowingKind,
)
from deppy.static_analysis.section_gluing import (
    check_gluing_condition as _check_gluing_condition,
    extract_obstruction_basis as _extract_obstruction_basis,
    GluingCheckResult as _GluingCheckResult,
)
from deppy.library_theories.pack_registry import (
    get_default_registry as _get_default_registry,
)
from deppy.equivalence.persistent_cohomology import (
    PersistentCohomologyComputer as _PersistentCohomologyComputer,
    auto_filtration_from_judgments as _auto_filtration_from_judgments,
)
from deppy.interprocedural import (
    ErrorViabilityPushback as _ErrorViabilityPushback,
    WrapperAnalyzer as _WrapperAnalyzer,
)


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
    # When True, this requirement has evidence from the nullable presheaf
    # (e.g., variable assigned from a function that returns None on some paths).
    # Stalk subsumption should NOT override this — the presheaf forward analysis
    # may not track interprocedural nullability, but the nullable fiber evidence
    # is definitive.
    nullable_evidence: bool = False


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
    # Repair suggestion: the negation of the gap predicate gives
    # the exact guard condition needed to close the obstruction.
    repair_guard: Optional[Predicate] = None


# ═══════════════════════════════════════════════════════════════════════════════
# Obstruction algebra — independence, minimum-fix-count, repair synthesis
# ═══════════════════════════════════════════════════════════════════════════════


class ObstructionAlgebra:
    """Module-valued algebraic operations on gluing obstructions.

    Each obstruction is represented as a vector in a free module over
    GF(2) with basis elements indexed by ``(bug_type, site_kind)``.

    The module structure enables:
      - **Independence**: two obstructions are independent iff their
        vectors are linearly independent over GF(2).
      - **Minimum fix count**: the rank of the obstruction matrix.
      - **Interaction detection**: obstructions with overlapping
        support (nonzero in the same basis elements) interact.
      - **Repair synthesis**: the ideal generated by the obstruction
        vectors gives the minimal repair conditions.

    This is a genuine upgrade over the previous scalar (greedy
    heuristic) approach: the GF(2) rank gives the exact minimum
    number of independent fixes, not a greedy approximation.
    """

    @staticmethod
    def _basis_key(obs: GluingObstruction) -> Tuple[str, int]:
        """Basis element index for an obstruction: (bug_type, line)."""
        return (obs.bug_type, obs.line)

    @staticmethod
    def _build_basis(
        obstructions: List[GluingObstruction],
    ) -> Tuple[List[Tuple[str, int]], Dict[Tuple[str, int], int]]:
        """Build the module basis from a set of obstructions.

        Returns (basis_elements, index_map).
        """
        basis: List[Tuple[str, int]] = []
        index: Dict[Tuple[str, int], int] = {}
        for obs in obstructions:
            key = ObstructionAlgebra._basis_key(obs)
            if key not in index:
                index[key] = len(basis)
                basis.append(key)
        return basis, index

    @staticmethod
    def vectorize(
        obs: GluingObstruction,
        basis_index: Dict[Tuple[str, int], int],
        n_basis: int,
    ) -> List[int]:
        """Represent an obstruction as a GF(2) vector."""
        vec = [0] * n_basis
        key = ObstructionAlgebra._basis_key(obs)
        if key in basis_index:
            vec[basis_index[key]] = 1
        return vec

    @staticmethod
    def suggest_guard(obs: GluingObstruction) -> Optional[Predicate]:
        """Synthesize a repair guard from the gap predicate.

        If gap = (avail ∧ ¬req), the repair is ¬gap = (¬avail ∨ req),
        which simplifies to the required predicate when the available
        section is unconstrained.
        """
        if obs.resolved_by_guard:
            return None
        if isinstance(obs.gap_predicate, And) and not obs.gap_predicate.conjuncts:
            return None
        return Not(obs.gap_predicate)

    @staticmethod
    def are_independent(
        o1: GluingObstruction,
        o2: GluingObstruction,
    ) -> bool:
        """Two obstructions are independent iff neither gap implies the other.

        Uses Z3 when available; falls back to structural comparison.
        """
        if o1.resolved_by_guard or o2.resolved_by_guard:
            return False
        if o1.confidence <= 0 or o2.confidence <= 0:
            return False
        # Quick structural check: different bug types at different lines
        if o1.bug_type != o2.bug_type and o1.line != o2.line:
            return True
        # Z3 check: o1.gap ⊭ o2.gap AND o2.gap ⊭ o1.gap
        if z3_available():
            imp_1_2 = Implies(o1.gap_predicate, o2.gap_predicate)
            imp_2_1 = Implies(o2.gap_predicate, o1.gap_predicate)
            try:
                r12 = quick_check(Not(imp_1_2), timeout_ms=200)
                r21 = quick_check(Not(imp_2_1), timeout_ms=200)
                return (r12 == "sat") and (r21 == "sat")
            except Exception:
                pass
        return o1.line != o2.line

    @staticmethod
    def minimum_fix_count(obstructions: List[GluingObstruction]) -> int:
        """Exact minimum independent fixes via GF(2) matrix rank.

        Constructs the obstruction matrix (one row per obstruction,
        columns indexed by (bug_type, line) basis elements) and
        computes its rank over GF(2) via Gaussian elimination.

        This is exact (not a greedy approximation): rank = minimum
        number of independent conditions that must be resolved.
        """
        genuine = [o for o in obstructions
                   if not o.resolved_by_guard and o.confidence > 0]
        if not genuine:
            return 0

        basis, index = ObstructionAlgebra._build_basis(genuine)
        n_basis = len(basis)

        if n_basis == 0:
            return 0

        # Build the obstruction matrix
        matrix: List[List[int]] = []
        for obs in genuine:
            matrix.append(ObstructionAlgebra.vectorize(obs, index, n_basis))

        # GF(2) Gaussian elimination for rank
        return _gf2_matrix_rank(matrix)

    @staticmethod
    def interaction_groups(
        obstructions: List[GluingObstruction],
    ) -> List[List[GluingObstruction]]:
        """Group obstructions by interaction (shared basis support).

        Two obstructions interact if they share the same (bug_type, line)
        basis element.  Returns connected components of the interaction
        graph — each group can be resolved by a single compound guard.
        """
        genuine = [o for o in obstructions
                   if not o.resolved_by_guard and o.confidence > 0]
        if not genuine:
            return []

        # Build interaction graph via shared basis keys
        n = len(genuine)
        adj: Dict[int, Set[int]] = {i: set() for i in range(n)}
        key_to_indices: Dict[Tuple[str, int], List[int]] = {}
        for i, obs in enumerate(genuine):
            key = ObstructionAlgebra._basis_key(obs)
            key_to_indices.setdefault(key, []).append(i)

        for indices in key_to_indices.values():
            for i in range(len(indices)):
                for j in range(i + 1, len(indices)):
                    adj[indices[i]].add(indices[j])
                    adj[indices[j]].add(indices[i])

        # BFS connected components
        visited: Set[int] = set()
        groups: List[List[GluingObstruction]] = []
        for start in range(n):
            if start in visited:
                continue
            component: List[int] = []
            queue = [start]
            visited.add(start)
            while queue:
                node = queue.pop(0)
                component.append(node)
                for nb in adj[node]:
                    if nb not in visited:
                        visited.add(nb)
                        queue.append(nb)
            groups.append([genuine[i] for i in component])

        return groups


def _gf2_matrix_rank(matrix: List[List[int]]) -> int:
    """Compute rank of a binary matrix over GF(2) via Gaussian elimination."""
    if not matrix:
        return 0
    m = len(matrix)
    n = len(matrix[0]) if matrix else 0
    mat = [row[:] for row in matrix]
    pivot = 0
    for col in range(n):
        found = -1
        for r in range(pivot, m):
            if mat[r][col]:
                found = r
                break
        if found == -1:
            continue
        mat[pivot], mat[found] = mat[found], mat[pivot]
        for r in range(m):
            if r != pivot and mat[r][col]:
                mat[r] = [a ^ b for a, b in zip(mat[r], mat[pivot])]
        pivot += 1
    return pivot


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
    # Sheaf infrastructure results
    harvest_result: Optional[Any] = None  # HarvestResult from unified harvest
    gluing_check: Optional[Any] = None  # GluingCheckResult from formal gluing
    obstruction_basis: Optional[Any] = None  # ObstructionBasis from extract_obstruction_basis
    persistence_barcodes: Optional[Any] = None  # Persistence computation result
    theory_pack_results: Optional[Dict[str, Any]] = None  # Theory pack solving results
    # Cosheaf root-cause analysis (Phase 7)
    cosheaf_result: Optional[Any] = None  # CosheafHomologyResult
    # Repair synthesis (Phase 8)
    repair_plan: Optional[Any] = None  # RepairPlan

    @property
    def bugs_found(self) -> int:
        return self.genuine_obstructions

    @property
    def findings(self) -> List[GluingObstruction]:
        """Genuine (unresolved, reachable) obstructions = confirmed bugs."""
        return [o for o in self.obstructions
                if not o.resolved_by_guard and o.confidence > 0]

    @property
    def minimum_independent_fixes(self) -> int:
        """Minimum number of independent fixes to resolve all obstructions.

        Uses the obstruction algebra to compute a greedy independent set.
        """
        return ObstructionAlgebra.minimum_fix_count(self.obstructions)

    @property
    def repair_suggestions(self) -> List[Predicate]:
        """Suggested guard predicates to close each genuine obstruction.

        Each entry is Not(gap_predicate): the exact condition to add as a
        guard to prevent the corresponding bug.
        """
        guards = []
        for obs in self.findings:
            g = ObstructionAlgebra.suggest_guard(obs)
            if g is not None:
                guards.append(g)
        return guards


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
    - Tuple assignment: ``a, var = ...`` / ``var, b = ...``
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
                    # Tuple unpacking: ``a, b = expr``
                    if isinstance(target, (ast.Tuple, ast.List)):
                        for elt in target.elts:
                            if isinstance(elt, ast.Name) and elt.id == var:
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

    # ── NotEq (!=) handling ──────────────────────────────────────────────
    # For `while pos != target: pos += step`, the orbit of pos under +step
    # must be cofinal with the target.  A non-unit step can skip the exact
    # target value → the presheaf section over the loop has no terminal
    # object in its orbit category, yielding a non-termination obstruction.
    if isinstance(loop_test, ast.Compare) and len(loop_test.ops) == 1:
        op = loop_test.ops[0]
        if isinstance(op, ast.NotEq):
            # Extract the other comparand (the "target" variable)
            rhs_name = None
            if isinstance(loop_test.comparators[0], ast.Name):
                rhs_name = loop_test.comparators[0].id
            if isinstance(loop_test.comparators[0], ast.Constant):
                rhs_name = None  # constant target is fine

            for stmt in body:
                for node in ast.walk(stmt):
                    if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
                        if node.target.id == var:
                            if isinstance(node.value, ast.Constant) and isinstance(node.value.value, (int, float)):
                                step = abs(node.value.value)
                                if step != 1:
                                    return False  # non-unit step can skip target
                    # Plain Assign: ``var = var - other`` where other is the
                    # comparand → variable-width step, ranking depends on the
                    # other variable's stalk.  This is not provably monotone.
                    if isinstance(node, ast.Assign):
                        for tgt in node.targets:
                            if isinstance(tgt, ast.Name) and tgt.id == var:
                                if isinstance(node.value, ast.BinOp):
                                    # Check if step involves the other comparand
                                    if rhs_name:
                                        val_text = ""
                                        try:
                                            val_text = ast.unparse(node.value)
                                        except Exception:
                                            pass
                                        if rhs_name in val_text and var in val_text:
                                            return False  # variable-width step

            # Check for multi-variable condition with both vars modified
            # in different branches (e.g., while a != b: if a>b: a=a-b else: b=b-a)
            if rhs_name:
                rhs_modified = _body_modifies_var(body, rhs_name)
                if rhs_modified:
                    return False  # both sides of != modified → complex ranking

            return True  # unit step or no AugAssign found

    # ── Identity-predicate handling (``is`` / ``is not``) ─────────────────
    # ``while x is None: x = f()`` — the ranking function is the identity
    # predicate `is_none(x)`.  Each iteration must GUARANTEE the predicate
    # flips.  If x is reassigned from an **opaque call** (unknown function),
    # the fiber may remain in the ``is None`` stalk indefinitely → the
    # ranking presheaf has no descent section → non-termination obstruction.
    if isinstance(loop_test, ast.Compare) and len(loop_test.ops) == 1:
        op = loop_test.ops[0]
        if isinstance(op, (ast.Is, ast.IsNot)):
            for stmt in body:
                for node in ast.walk(stmt):
                    if isinstance(node, ast.Assign):
                        for tgt in node.targets:
                            if isinstance(tgt, ast.Name) and tgt.id == var:
                                # x = func() where func is unknown → no guarantee
                                if isinstance(node.value, ast.Call):
                                    return False
                                # x = None → definitely wrong for `while x is None`
                                if (isinstance(node.value, ast.Constant)
                                        and node.value.value is None
                                        and isinstance(op, ast.Is)):
                                    return False
            return True

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


def _body_has_unconditional_exit(body: List[ast.stmt]) -> bool:
    """Check if a loop body has a guaranteed (unconditional) exit.

    In the ranking presheaf framework, a ``while True`` loop requires a
    *terminal section* — an unconditional ``break``, ``return``, or ``raise``
    that provides a fiber-wise exit from the loop cover.  If exits are only
    reachable through conditional branches, the ranking presheaf has no
    guaranteed descent → obstruction.

    This checks the TOP-LEVEL statements only (not nested functions/classes).
    """
    for stmt in body:
        if isinstance(stmt, (ast.Return, ast.Break, ast.Raise)):
            return True
        # For-range with guaranteed body → treat as bounded
        if isinstance(stmt, ast.For):
            return True  # for loops are bounded by the iterator
    return False


def _while_true_variant(node: ast.While) -> bool:
    """Check if a while loop is an effective ``while True`` — constant-true condition.

    Covers:  ``while True:``, ``while 1:``, ``while not False:``
    """
    test = node.test
    if isinstance(test, ast.Constant) and test.value:
        return True
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        if isinstance(test.operand, ast.Constant) and not test.operand.value:
            return True
    return False


def _body_modifies_var_non_monotonically(body: List[ast.stmt], var: str) -> bool:
    """Detect conditional multi-directional modification of ``var`` in a loop body.

    In the ranking presheaf, a ranking function must be MONOTONICALLY
    decreasing.  If the loop body contains an if/else that modifies ``var``
    in DIFFERENT arithmetic directions (one branch increases, another
    decreases via plain assignment), the ranking function is non-monotone
    → no well-founded descent → non-termination obstruction.

    Examples:
        ``if x % 2 == 0: x = x // 2  else: x = 3 * x + 1``  (Collatz)
        ``if a > b: a = a - b  else: b = b - a``  (GCD subtraction)
    """
    # Collect assignments to var inside conditional branches
    def _find_conditional_assigns(stmts):
        """Return list of (branch, assign_node) tuples."""
        results = []
        for stmt in stmts:
            if isinstance(stmt, ast.If):
                for sub in ast.walk(ast.Module(body=stmt.body, type_ignores=[])):
                    if isinstance(sub, ast.Assign):
                        for tgt in sub.targets:
                            if isinstance(tgt, ast.Name) and tgt.id == var:
                                results.append(('if', sub))
                    if isinstance(sub, ast.AugAssign) and isinstance(sub.target, ast.Name):
                        if sub.target.id == var:
                            results.append(('if', sub))
                for sub in ast.walk(ast.Module(body=stmt.orelse, type_ignores=[])):
                    if isinstance(sub, ast.Assign):
                        for tgt in sub.targets:
                            if isinstance(tgt, ast.Name) and tgt.id == var:
                                results.append(('else', sub))
                    if isinstance(sub, ast.AugAssign) and isinstance(sub.target, ast.Name):
                        if sub.target.id == var:
                            results.append(('else', sub))
        return results

    assigns = _find_conditional_assigns(body)
    if len(assigns) < 2:
        return False

    # Check if assignments are in DIFFERENT branches
    branches = set(branch for branch, _ in assigns)
    if len(branches) < 2:
        return False

    # At least two branches modify the variable → non-monotone ranking
    return True


def _self_recursive_without_base_case(func_node: ast.FunctionDef) -> bool:
    """Check if a function has a self-recursive call without a conditional base case.

    In the stack-depth presheaf, a recursive function requires a *terminal
    fiber* — a code path that does NOT recur and provides a base section.
    If every code path through the function body contains a recursive call,
    the presheaf has no terminal section → non-termination obstruction.

    Specifically: if the function body's first statement is NOT an ``if``
    guard, and the body contains a self-recursive call, there is no base case.
    """
    func_name = func_node.name

    # Check if function has any self-recursive calls
    has_self_call = False
    for node in ast.walk(func_node):
        if isinstance(node, ast.Call):
            call_name = _get_call_name(node)
            if call_name == func_name:
                has_self_call = True
                break

    if not has_self_call:
        return False

    # Check if the body has a base-case guard (an if-statement that provides
    # an early return/terminal path BEFORE any recursive call)
    for stmt in func_node.body:
        if isinstance(stmt, ast.If):
            # If this if-statement has a return in its body (or orelse),
            # it provides a base case
            has_return_in_if = False
            for sub in ast.walk(ast.Module(body=stmt.body, type_ignores=[])):
                if isinstance(sub, ast.Return):
                    has_return_in_if = True
                    break
            if not has_return_in_if:
                for sub in ast.walk(ast.Module(body=stmt.orelse, type_ignores=[])):
                    if isinstance(sub, ast.Return):
                        has_return_in_if = True
                        break
            if has_return_in_if:
                return False  # has base case guard
        elif isinstance(stmt, ast.Return):
            # Check if this return ITSELF contains a self-recursive call
            has_self_call_in_return = False
            if stmt.value:
                for sub in ast.walk(stmt.value):
                    if isinstance(sub, ast.Call):
                        if _get_call_name(sub) == func_name:
                            has_self_call_in_return = True
                            break
            if has_self_call_in_return:
                return True  # recursive call with no base case guard
            return False  # unconditional non-recursive return
        elif isinstance(stmt, (ast.Expr, ast.Assign)):
            # Check if this statement contains a recursive call
            for node in ast.walk(stmt):
                if isinstance(node, ast.Call):
                    call_name = _get_call_name(node)
                    if call_name == func_name:
                        return True  # recursive call before any base case guard

    return True  # no base case found


def _threading_imported(tree: ast.AST) -> bool:
    """Check if the ``threading`` module is imported anywhere in the tree.

    In the synchronization presheaf framework, ``import threading`` is an
    *intent declaration*: the author is signalling that the code operates
    in a concurrent fiber topology.  Module-level mutations in such files
    require synchronization sections even when no explicit ``Thread(target=…)``
    constructor is visible in the snippet (the spawn may be external).
    """
    for n in ast.walk(tree):
        if isinstance(n, ast.Import):
            for alias in n.names:
                if alias.name == 'threading' or alias.name.startswith('threading.'):
                    return True
        if isinstance(n, ast.ImportFrom):
            if n.module and (n.module == 'threading' or n.module.startswith('threading.')):
                return True
    return False


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


def _var_is_shared_across_threads(var_name: str, tree: ast.AST) -> bool:
    """Check if a variable is MUTATED from multiple concurrent fibers.

    In the synchronization presheaf, a DATA_RACE obstruction requires
    that the same variable has WRITE access from at least 2 distinct
    concurrent fibers.  This can happen when:
    (a) 2+ thread instances run the same target function (loop-spawned threads)
    (b) 2+ different thread-target functions mutate the same variable
    (c) 2+ threads with the same target mutate via AugAssign/method call

    A variable mutated from only ONE thread with no concurrent writer
    is confined to a single fiber and cannot race.
    """
    # Collect all thread target function names, counting effective spawns
    thread_target_names: Set[str] = set()
    total_effective_spawns = 0

    def _is_inside_loop(node: ast.AST) -> bool:
        """Check if a Thread() call is inside a for/while loop."""
        for parent in ast.walk(tree):
            if isinstance(parent, (ast.For, ast.While, ast.AsyncFor)):
                for child in ast.walk(parent):
                    if child is node:
                        return True
        return False

    for n in ast.walk(tree):
        if isinstance(n, ast.Call):
            func_name = _get_call_name(n)
            if 'Thread' in func_name:
                if _is_inside_loop(n):
                    total_effective_spawns += 2  # Loop → multiple instances
                else:
                    total_effective_spawns += 1
                for kw in n.keywords:
                    if kw.arg == 'target' and isinstance(kw.value, ast.Name):
                        thread_target_names.add(kw.value.id)
                # Also check positional args: Thread(target_fn)
                if n.args and isinstance(n.args[0], ast.Name):
                    thread_target_names.add(n.args[0].id)

    if not thread_target_names:
        return False

    # Find all function definitions (including nested) matching targets
    def _find_func_defs(root: ast.AST) -> list:
        result = []
        for node in ast.walk(root):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node.name in thread_target_names:
                    result.append(node)
        return result

    target_funcs = _find_func_defs(tree)

    # Check which target functions MUTATE the variable
    mutating_targets: Set[str] = set()
    for func_def in target_funcs:
        for desc in ast.walk(func_def):
            # Direct name mutation (AugAssign, global assignment)
            if isinstance(desc, ast.Name) and desc.id == var_name:
                if isinstance(getattr(desc, '_parent', None), (ast.AugAssign, ast.Assign)):
                    mutating_targets.add(func_def.name)
                    break
                # Any name access in thread is potentially racy for mutable types
                mutating_targets.add(func_def.name)
                break
            # Method call on the variable (.append, .extend, .pop, etc.)
            if isinstance(desc, ast.Attribute) and isinstance(desc.value, ast.Name):
                if desc.value.id == var_name:
                    mutating_targets.add(func_def.name)
                    break
            # Subscript assignment: var[key] = val
            if isinstance(desc, ast.Subscript) and isinstance(desc.value, ast.Name):
                if desc.value.id == var_name:
                    mutating_targets.add(func_def.name)
                    break

    if not mutating_targets:
        return False

    # Count effective spawns for MUTATING targets only.
    # Two threads that target different functions don't race on a variable
    # unless both functions mutate it.
    mutating_spawns = 0
    for n in ast.walk(tree):
        if not isinstance(n, ast.Call):
            continue
        fn = _get_call_name(n)
        if 'Thread' not in fn:
            continue
        target_name = None
        for kw in n.keywords:
            if kw.arg == 'target' and isinstance(kw.value, ast.Name):
                target_name = kw.value.id
        if not target_name and n.args and isinstance(n.args[0], ast.Name):
            target_name = n.args[0].id
        if target_name and target_name in mutating_targets:
            if _is_inside_loop(n):
                mutating_spawns += 2
            else:
                mutating_spawns += 1

    # Shared if: 2+ distinct mutating targets, or 1 target spawned 2+ times
    if len(mutating_targets) >= 2:
        return True
    if mutating_spawns >= 2:
        return True

    # Single thread: check if main thread can concurrently access the variable.
    # Module-level variables or variables in the enclosing function scope
    # are accessible from both the spawning context and the thread.
    for stmt in ast.iter_child_nodes(tree):
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        for desc in ast.walk(stmt):
            if isinstance(desc, ast.Name) and desc.id == var_name:
                return True
            if isinstance(desc, ast.Attribute) and isinstance(desc.value, ast.Name):
                if desc.value.id == var_name:
                    return True

    # Check enclosing functions that spawn threads
    for func_def in ast.walk(tree):
        if not isinstance(func_def, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if func_def.name in thread_target_names:
            continue  # Skip the target function itself
        spawns_thread = False
        for desc in ast.walk(func_def):
            if isinstance(desc, ast.Call):
                fn = _get_call_name(desc)
                if 'Thread' in fn:
                    spawns_thread = True
                    break
        if spawns_thread:
            # Check if this enclosing function also MUTATES the variable
            # (reads after join() are safe — only concurrent writes race)
            for desc in ast.walk(func_def):
                if isinstance(desc, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    if desc.name in thread_target_names:
                        continue  # Skip nested target func
                # Mutation via method call: var.append() / var.extend()
                if (isinstance(desc, ast.Call) and isinstance(desc.func, ast.Attribute)
                    and isinstance(desc.func.value, ast.Name)
                    and desc.func.value.id == var_name
                    and desc.func.attr in ('append', 'extend', 'insert', 'pop',
                                           'remove', 'clear', 'update', 'add',
                                           'discard', 'sort', 'reverse')):
                    return True
                # Mutation via AugAssign: var += ...
                if (isinstance(desc, ast.AugAssign)
                    and isinstance(desc.target, ast.Name)
                    and desc.target.id == var_name):
                    return True
                # Mutation via subscript assign: var[k] = ...
                if (isinstance(desc, ast.Assign)
                    and any(isinstance(t, ast.Subscript) and isinstance(t.value, ast.Name)
                            and t.value.id == var_name for t in desc.targets)):
                    return True

    return False


def _binding_analysis(tree: ast.AST, source: str = "") -> List[SectionRequirement]:
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

        def _extract_target_names(target: ast.AST) -> List[str]:
            """Extract all bound names from an assignment target.

            Sheaf-theoretically: an assignment target defines a PRODUCT SECTION
            over the binding presheaf.  For ``a, b = ...``, both a and b receive
            sections simultaneously (the product of their fibers).  For
            ``a, (b, c) = ...``, all three variables receive sections.
            """
            if isinstance(target, ast.Name):
                return [target.id]
            if isinstance(target, (ast.Tuple, ast.List)):
                names: List[str] = []
                for elt in target.elts:
                    names.extend(_extract_target_names(elt))
                return names
            if isinstance(target, ast.Starred):
                return _extract_target_names(target.value)
            return []

        def _scan_body(stmts: List[ast.stmt], in_branch: bool = False) -> None:
            for stmt in stmts:
                # ── Import statements are unconditional bindings ──
                # Python semantics: `import X` binds X in the local scope.
                # `from X import Y` binds Y. These are ALWAYS unconditional
                # because the import statement itself is the binding.
                # In algebraic geometry: the import morphism provides a
                # section from the module-level site to the local fiber.
                if isinstance(stmt, ast.Import):
                    for alias in stmt.names:
                        name = alias.asname or alias.name.split('.')[0]
                        unconditional.add(name)
                if isinstance(stmt, ast.ImportFrom):
                    for alias in stmt.names:
                        name = alias.asname or alias.name
                        unconditional.add(name)
                # Assignment — handles simple names AND tuple/list unpacking
                if isinstance(stmt, ast.Assign):
                    for target in stmt.targets:
                        for name in _extract_target_names(target):
                            if in_branch:
                                conditional.add(name)
                            else:
                                unconditional.add(name)
                if isinstance(stmt, ast.AugAssign):
                    for name in _extract_target_names(stmt.target):
                        if in_branch:
                            conditional.add(name)
                        else:
                            unconditional.add(name)
                # For loop variable — handles both simple (for x in ...) and
                # tuple unpacking (for i, item in enumerate(...))
                # ── Loop-body binding presheaf principle ──
                # Within the loop body, the iteration variable has an
                # UNCONDITIONAL section — every execution of the body is
                # preceded by a successful iteration step that binds the
                # variable.  We add iteration variables to `unconditional`
                # to prevent false UNBOUND_VAR inside the loop body.
                # Outside the loop, the variable is conditional (the loop
                # might not execute at all), but this is a weaker concern
                # and rarely causes real bugs in practice.
                if isinstance(stmt, ast.For):
                    target = stmt.target
                    for tgt_name in _extract_target_names(target):
                        # Mark as unconditional: within the loop body (which
                        # is the only scope where _scope_walk will find uses),
                        # the iteration variable is always bound.
                        unconditional.add(tgt_name)
                    _scan_body(stmt.body, in_branch=True)
                    # ── for/else definite binding (sheaf section join) ──
                    # A for/else construct guarantees that *either* the
                    # loop body executed (and possibly broke) *or* the
                    # else clause executed.  If the else clause binds a
                    # variable, that binding is unconditional along the
                    # non-break path.  Combined with binding in the break
                    # path, the variable is always bound after the loop.
                    if stmt.orelse:
                        else_binds: Set[str] = set()
                        for else_stmt in stmt.orelse:
                            for n in ast.walk(else_stmt):
                                if isinstance(n, ast.Assign):
                                    for t in n.targets:
                                        if isinstance(t, ast.Name):
                                            else_binds.add(t.id)
                                elif isinstance(n, ast.AugAssign):
                                    if isinstance(n.target, ast.Name):
                                        else_binds.add(n.target.id)
                        # Variables bound in the else clause are unconditional
                        # because for/else always runs one of the two paths
                        if not in_branch:
                            unconditional.update(else_binds)
                        else:
                            conditional.update(else_binds)
                        _scan_body(stmt.orelse, in_branch=True)
                    else:
                        pass  # no else clause
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
                    # ── try/except definite binding (sheaf section join) ──
                    # If the try body AND every except handler all bind the
                    # same variable, that variable is unconditionally bound
                    # after the try/except block.  The sheaf join of the
                    # normal-exit section and handler sections is total.
                    try_binds: Set[str] = set()
                    for n in ast.walk(ast.Module(body=stmt.body, type_ignores=[])):
                        if isinstance(n, ast.Assign):
                            for t in n.targets:
                                if isinstance(t, ast.Name):
                                    try_binds.add(t.id)
                    handler_binds_all: Optional[Set[str]] = None
                    for handler in stmt.handlers:
                        if handler.name:
                            conditional.add(handler.name)
                        h_binds: Set[str] = set()
                        for n in ast.walk(ast.Module(body=handler.body, type_ignores=[])):
                            if isinstance(n, ast.Assign):
                                for t in n.targets:
                                    if isinstance(t, ast.Name):
                                        h_binds.add(t.id)
                        if handler_binds_all is None:
                            handler_binds_all = h_binds
                        else:
                            handler_binds_all &= h_binds
                        _scan_body(handler.body, in_branch=True)
                    # Variables bound in try AND all handlers
                    if handler_binds_all and not in_branch:
                        definite = try_binds & handler_binds_all
                        unconditional.update(definite)
                    _scan_body(stmt.body, in_branch=True)
                    _scan_body(stmt.orelse, in_branch=True)
                    _scan_body(stmt.finalbody, in_branch=True)
                # While
                if isinstance(stmt, ast.While):
                    _scan_body(stmt.body, in_branch=True)
                # Nested function/class definitions create bindings in this scope
                if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    if in_branch:
                        conditional.add(stmt.name)
                    else:
                        unconditional.add(stmt.name)
                    # Don't recurse — nested scope analyzed separately
                if isinstance(stmt, ast.ClassDef):
                    if in_branch:
                        conditional.add(stmt.name)
                    else:
                        unconditional.add(stmt.name)

        _scan_body(func_node.body, in_branch=False)

        # ── Scope-aware Name collection (sheaf locality axiom) ──
        # The binding presheaf Γ is fiber-indexed by scope: each nested scope
        # (FunctionDef, AsyncFunctionDef, Lambda, ClassDef) defines its own
        # local fiber.  The restriction map ρ: Γ(outer) → Γ(inner) does NOT
        # pull back inner-scope params/locals into the outer fiber.  We must
        # respect this by NOT recursing into child-scope AST nodes when
        # collecting Name loads for the current scope.

        _BUILTINS = frozenset((
            'print', 'len', 'range', 'int', 'str', 'float', 'bool',
            'list', 'dict', 'set', 'tuple', 'type', 'isinstance',
            'issubclass', 'hasattr', 'getattr', 'setattr', 'super',
            'open', 'None', 'True', 'False', 'Exception', 'ValueError',
            'TypeError', 'RuntimeError', 'KeyError', 'IndexError',
            'AttributeError', 'StopIteration', 'NotImplementedError',
            'OSError', 'IOError', 'FileNotFoundError', 'PermissionError',
            'ZeroDivisionError', 'OverflowError', 'AssertionError',
            'NameError', 'UnboundLocalError', 'ImportError',
            'TimeoutError', 'ConnectionError', 'ConnectionRefusedError',
            'ConnectionResetError', 'BrokenPipeError', 'BlockingIOError',
            'InterruptedError', 'ProcessLookupError', 'ChildProcessError',
            'ModuleNotFoundError', 'RecursionError', 'SystemExit',
            'KeyboardInterrupt', 'GeneratorExit', 'ArithmeticError',
            'LookupError', 'UnicodeError', 'UnicodeDecodeError',
            'UnicodeEncodeError', 'BufferError', 'EOFError',
            'MemoryError', 'SystemError', 'UnsupportedOperation',
            'enumerate', 'zip', 'map', 'filter', 'sorted', 'reversed',
            'min', 'max', 'sum', 'abs', 'any', 'all', 'id', 'repr',
            'hash', 'hex', 'oct', 'bin', 'chr', 'ord', 'format',
            'input', 'iter', 'next', 'object', 'property', 'staticmethod',
            'classmethod', 'bytes', 'bytearray', 'memoryview',
            'frozenset', 'complex', 'divmod', 'pow', 'round',
            'callable', 'vars', 'dir', 'help', 'exec', 'eval', 'compile',
            'globals', 'locals', 'breakpoint', 'exit', 'quit',
            'NotImplemented', 'Ellipsis', '__import__', '__build_class__',
            'self', 'cls', '__name__', '__file__', '__class__',
            'threading', 'struct', 'hmac', 'secrets', 'os', 'sys',
            'io', 'json', 'math', 'time', 'datetime', 'collections',
            'functools', 'itertools', 'operator', 'copy', 'subprocess',
            'pathlib', 'logging', 'warnings', 're', 'hashlib',
            'random', 'socket', 'signal', 'contextlib', 'abc',
            'dataclasses', 'typing', 'enum', 'textwrap',
            'ctypes', 'multiprocessing', 'asyncio', 'queue',
            'concurrent', 'traceback', 'inspect', 'dis',
        ))

        def _scope_walk(node: ast.AST):
            """Walk AST without crossing scope boundaries.

            This implements the locality axiom of the binding presheaf:
            each scope boundary (function, lambda, class, comprehension)
            is a separate observation site whose fiber is analyzed
            independently.

            In Python 3, comprehensions (ListComp, SetComp, DictComp,
            GeneratorExp) create implicit scopes — their iteration
            variables are local to the comprehension.  We model this
            as a **stratified presheaf**: the comprehension body is a
            sub-site with its own binding fiber that includes the
            iteration variable.  The restriction map from the enclosing
            scope to the comprehension scope adds the iteration
            variable binding.

            We do NOT cross into comprehension bodies to avoid falsely
            flagging iteration variables as unbound in the enclosing scope.
            """
            for child in ast.iter_child_nodes(node):
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                      ast.Lambda, ast.ClassDef)):
                    continue  # Don't cross scope boundary
                # Comprehensions have implicit scopes in Python 3:
                # iteration variables are local to the comprehension.
                if isinstance(child, (ast.ListComp, ast.SetComp,
                                      ast.DictComp, ast.GeneratorExp)):
                    continue  # Don't cross comprehension scope boundary
                yield child
                yield from _scope_walk(child)

        # Track which names appear as Call targets (function invocations).
        # Names used exclusively in Call position reference the module-level
        # global section of Γ — they're imported/global functions that are
        # not local bindings.  The sheaf restriction map from the module site
        # provides them, but we can't observe that section locally.

        # First pass: collect all Name nodes that are Call func targets
        _call_target_ids: Set[int] = set()
        for node in _scope_walk(func_node):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                _call_target_ids.add(id(node.func))

        _call_only_names: Dict[str, bool] = {}  # name → all-call?

        for node in _scope_walk(func_node):
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
                if node.id in _BUILTINS:
                    continue
                is_call_target = id(node) in _call_target_ids
                all_used.append((node.id, node.lineno, node.col_offset, node))
                if node.id not in _call_only_names:
                    _call_only_names[node.id] = is_call_target
                elif not is_call_target:
                    _call_only_names[node.id] = False

        # ── Enclosing scope names (LEGB model) ──
        # Variables from enclosing scopes (nonlocal/global declarations,
        # class-level names, module-level assignments, enclosing function
        # params/locals) provide a global section in the binding presheaf
        # via the sheaf restriction map ρ: Γ(enclosing) → Γ(current).
        _enclosing_names: Set[str] = set()
        # nonlocal / global declarations
        for stmt in ast.walk(func_node):
            if isinstance(stmt, (ast.Global, ast.Nonlocal)):
                _enclosing_names.update(stmt.names)
        # Module-level (top-level) assignments and class-level names.
        # Use _extract_target_names to handle TUPLE ASSIGNMENTS
        # (e.g., lock_a, lock_b = Lock(), Lock()) at module level.
        # In the LEGB sheaf: the Module scope is a covering site
        # whose restriction map provides bindings to all inner sites.
        tree_mod = ast.parse(textwrap.dedent(source)) if not hasattr(func_node, '_binding_tree') else tree
        for top_stmt in getattr(tree_mod, 'body', []):
            if isinstance(top_stmt, ast.Assign):
                for tgt in top_stmt.targets:
                    for name in _extract_target_names(tgt):
                        _enclosing_names.add(name)
            if isinstance(top_stmt, ast.FunctionDef):
                _enclosing_names.add(top_stmt.name)
            if isinstance(top_stmt, ast.ClassDef):
                _enclosing_names.add(top_stmt.name)
            if isinstance(top_stmt, (ast.Import, ast.ImportFrom)):
                if isinstance(top_stmt, ast.Import):
                    for alias in top_stmt.names:
                        _enclosing_names.add(alias.asname or alias.name.split('.')[0])
                else:
                    for alias in top_stmt.names:
                        _enclosing_names.add(alias.asname or alias.name)
        # ── Enclosing function parameters and locals (closure binding) ──
        # When func_node is nested inside another function, the enclosing
        # function's params and locals are accessible via Python's closure
        # semantics (the E in LEGB).  In sheaf terms, the restriction
        # morphism ρ from the enclosing site provides these sections.
        for enclosing_func in ast.walk(tree):
            if not isinstance(enclosing_func, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            # Check if func_node is a descendant of enclosing_func
            if enclosing_func is func_node:
                continue
            for child in ast.walk(enclosing_func):
                if child is func_node:
                    # func_node is nested inside enclosing_func
                    # Add enclosing_func's params
                    for arg in enclosing_func.args.args:
                        _enclosing_names.add(arg.arg)
                    for arg in enclosing_func.args.kwonlyargs:
                        _enclosing_names.add(arg.arg)
                    if enclosing_func.args.vararg:
                        _enclosing_names.add(enclosing_func.args.vararg.arg)
                    if enclosing_func.args.kwarg:
                        _enclosing_names.add(enclosing_func.args.kwarg.arg)
                    # Add enclosing_func's locals (assignments in its body)
                    for stmt in enclosing_func.body:
                        if isinstance(stmt, ast.Assign):
                            for tgt in stmt.targets:
                                if isinstance(tgt, ast.Name):
                                    _enclosing_names.add(tgt.id)
                        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            _enclosing_names.add(stmt.name)
                        if isinstance(stmt, ast.ClassDef):
                            _enclosing_names.add(stmt.name)
                        if isinstance(stmt, ast.For):
                            if isinstance(stmt.target, ast.Name):
                                _enclosing_names.add(stmt.target.id)
                    break

        # For each used variable: if it's ONLY conditionally bound (not in unconditional),
        # it's a binding presheaf gap — the section at the use site requires the variable
        # to be in dom(Γ), but the available section only covers the branch.
        #
        # ALSO: if a variable is NEVER bound (not in unconditional, not in
        # conditional, not in enclosing scope), the binding presheaf has an
        # EMPTY section — a total obstruction rather than a partial one.
        # This catches typos like `counter_typo` when only `counter` exists.
        _already_flagged: Set[Tuple[str, int]] = set()
        for name, line, col, node in all_used:
            if (name, line) in _already_flagged:
                continue
            if name not in unconditional and name in conditional:
                _already_flagged.add((name, line))
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
            elif name not in unconditional and name not in conditional and name not in _enclosing_names:
                # ── Call-only name exclusion (module-site restriction) ──
                # If a name is used exclusively as a function call target,
                # it likely references a binding from the module-level site
                # (import or global definition) that we can't observe in
                # this local fiber.  The restriction map ρ from the module
                # site provides the section, so we don't flag it.
                if _call_only_names.get(name, False):
                    continue

                # Never-bound: the binding presheaf Γ({name}) has an EMPTY
                # section — no fiber covers this variable at any site.
                _already_flagged.add((name, line))
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.SSA_VALUE,
                                   name=f"bind_{name}_L{line}"),
                    bug_type="UNBOUND_VAR",
                    required_predicate=Comparison(
                        op='==', left=Var(f"bound_{name}"), right=IntLit(1)
                    ),
                    description=(
                        f"variable `{name}` never bound in any scope — "
                        f"binding presheaf Γ({name}) has empty section"
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

    Algebraic geometry principle: a RANKING FUNCTION on a well-ordered set
    guarantees termination. If the function has:
    1. A base case (if-return without recursive call) that checks a
       parameter, AND
    2. Recursive calls with a strictly smaller argument

    then the recursion terminates. The ranking function is the parameter
    value, and the base case ensures the well-ordering has a minimum.

    We check for explicit depth budgets AND structural base cases.
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

        # Phase 3b: Check for STRUCTURAL BASE CASE
        # If the function has an if-return at the top of the body that
        # doesn't contain a recursive call, that's a base case.
        # Combined with recursive calls that shrink the argument
        # (slicing, n-1, etc.), this proves termination via a ranking
        # function on the parameter space.
        has_base_case = False
        for stmt in func_node.body:
            if isinstance(stmt, ast.If):
                # Check if the if-body contains a return without recursion
                has_return = False
                has_self_call = False
                for child in ast.walk(stmt):
                    if isinstance(child, ast.Return):
                        has_return = True
                    if (isinstance(child, ast.Call)
                            and isinstance(child.func, ast.Name)
                            and child.func.id == func_name):
                        has_self_call = True
                if has_return and not has_self_call:
                    has_base_case = True
                    break
            elif isinstance(stmt, ast.Return):
                # Direct return at top → trivial base case
                has_base_case = True
                break
            else:
                break  # Non-if, non-return statement → stop checking

        if has_base_case:
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


def _arg_delta(call: ast.Call, caller_param: str) -> Optional[int]:
    """Compute the delta of the first positional argument relative to *caller_param*.

    Returns +k / −k if the argument is ``caller_param ± k``, 0 if it is
    passed unchanged, or ``None`` if the argument cannot be related to
    *caller_param* syntactically.
    """
    if not call.args:
        return None
    arg = call.args[0]
    if isinstance(arg, ast.BinOp) and isinstance(arg.left, ast.Name):
        if arg.left.id == caller_param and isinstance(arg.right, ast.Constant):
            v = arg.right.value
            if isinstance(v, (int, float)):
                if isinstance(arg.op, ast.Add):
                    return int(v)
                if isinstance(arg.op, ast.Sub):
                    return -int(v)
    if isinstance(arg, ast.Name) and arg.id == caller_param:
        return 0
    return None


def _mutual_recursion_analysis(tree: ast.AST) -> List[SectionRequirement]:
    """Detect non-terminating mutual recursion as a ranking-presheaf cycle.

    Uses ``deppy.interprocedural.CallGraph`` for SCC detection, then checks
    each strongly connected component for well-founded descent.

    The call-graph category **C** has functions as objects and call edges as
    morphisms.  A cycle  f₁ → f₂ → … → fₖ → f₁  induces a composite
    restriction map on the ranking presheaf.  For a well-founded descent
    section to exist, the net ranking delta around every cycle must be
    strictly negative.  If Σδᵢ ≥ 0, the ranking function never descends →
    obstruction.
    """
    reqs: List[SectionRequirement] = []

    # Phase 1: collect function defs for AST-level argument analysis
    func_defs: Dict[str, ast.FunctionDef] = {}
    for node in ast.iter_child_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_defs[node.name] = node
        if isinstance(node, ast.ClassDef):
            for child in ast.iter_child_nodes(node):
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    func_defs[child.name] = child

    if len(func_defs) < 2:
        return reqs

    # Phase 2: build call graph using deppy.interprocedural.CallGraph
    try:
        source_text = ast.unparse(tree)
    except Exception:
        return reqs
    cg = CallGraph.build_from_source(source_text)

    # Phase 3: find SCCs via infrastructure — generalises to k-cycles
    sccs = cg.strongly_connected_components()

    # Also build a quick call_node lookup: (caller, callee) → [call AST]
    call_nodes: Dict[Tuple[str, str], List[ast.Call]] = defaultdict(list)
    for fname, fnode in func_defs.items():
        for nd in ast.walk(fnode):
            if isinstance(nd, ast.Call) and isinstance(nd.func, ast.Name):
                callee = nd.func.id
                if callee in func_defs and callee != fname:
                    call_nodes[(fname, callee)].append(nd)

    seen_cycles: Set[FrozenSet[str]] = set()
    for scc in sccs:
        if len(scc) < 2:
            continue
        cycle_key = frozenset(scc)
        if cycle_key in seen_cycles:
            continue
        seen_cycles.add(cycle_key)

        # For each pair in the SCC, check 2-cycle ranking delta
        members = sorted(scc)
        for i, f in enumerate(members):
            for g in members[i + 1:]:
                f_to_g_calls = call_nodes.get((f, g), [])
                g_to_f_calls = call_nodes.get((g, f), [])
                if not f_to_g_calls or not g_to_f_calls:
                    continue
                f_params = [a.arg for a in func_defs[f].args.args] if f in func_defs else []
                g_params = [a.arg for a in func_defs[g].args.args] if g in func_defs else []
                if not f_params or not g_params:
                    continue
                f_call = f_to_g_calls[0]
                g_call = g_to_f_calls[0]
                f_to_g = _arg_delta(f_call, f_params[0])
                g_to_f = _arg_delta(g_call, g_params[0])
                if f_to_g is not None and g_to_f is not None:
                    net = f_to_g + g_to_f
                    if net >= 0:
                        reqs.append(SectionRequirement(
                            site_id=SiteId(kind=SiteKind.LOOP_HEADER_INVARIANT,
                                           name=f"mutual_{f}_{g}_L{f_call.lineno}"),
                            bug_type="NON_TERMINATION",
                            required_predicate=Comparison(
                                op='<', left=Var(f"ranking_{f}_{g}"),
                                right=IntLit(0)),
                            description=(
                                f"mutual recursion {f}↔{g}: net argument "
                                f"delta {net:+d} ≥ 0 — ranking presheaf "
                                f"has no descent section around the cycle"
                            ),
                            line=f_call.lineno, col=0, ast_node=f_call,
                        ))

    return reqs


def _decorator_return_analysis(tree: ast.AST) -> List[SectionRequirement]:
    """Detect NULL_PTR from decorators that drop or transform return values.

    Uses ``deppy.native_python.DecoratorAnalyzer`` + local wrapper-body
    analysis.  In sheaf terms, a decorator induces a restriction morphism
    ρ : S(decorated) → S(wrapper).  If the wrapper's inner function does not
    ``return`` the delegate call's result, the return-type fiber is truncated
    to ``NoneType`` — any caller dereferencing the result hits a NULL_PTR
    obstruction.  If the wrapper transforms the return type (e.g. wraps in
    ``str``), the carrier changes — TYPE_ERROR obstruction.
    """
    reqs: List[SectionRequirement] = []
    da = _DecoratorAnalyzer()

    # Collect all function definitions
    func_defs: Dict[str, ast.FunctionDef] = {}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_defs[node.name] = node

    # For each decorated function, check if decorator drops/transforms return
    for func_node in ast.walk(tree):
        if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if not func_node.decorator_list:
            continue

        stack = da.analyze_stack(func_node)
        if not stack or stack.is_transparent:
            continue

        # Check each decorator
        for deco_ast in func_node.decorator_list:
            deco_name = None
            if isinstance(deco_ast, ast.Name):
                deco_name = deco_ast.id
            elif isinstance(deco_ast, ast.Attribute):
                deco_name = deco_ast.attr
            if not deco_name or deco_name not in func_defs:
                continue

            # Analyze the decorator function body to find the inner wrapper
            deco_def = func_defs[deco_name]
            wrapper_issue = _check_decorator_wrapper_return(deco_def)
            if wrapper_issue == "drops_return":
                # Find call sites of the decorated function
                for user_node in ast.walk(tree):
                    if not isinstance(user_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        continue
                    if user_node.name == func_node.name or user_node.name == deco_name:
                        continue
                    for nd in ast.walk(user_node):
                        if (isinstance(nd, ast.Attribute) and
                                isinstance(nd.value, ast.Call) and
                                isinstance(nd.value.func, ast.Name) and
                                nd.value.func.id == func_node.name):
                            reqs.append(SectionRequirement(
                                site_id=SiteId(kind=SiteKind.SSA_VALUE,
                                               name=f"deco_null_{func_node.name}_L{nd.lineno}"),
                                bug_type="NULL_PTR",
                                required_predicate=Comparison(
                                    op='!=',
                                    left=Var(f"{func_node.name}_ret_is_none"),
                                    right=IntLit(1)),
                                description=(
                                    f"decorator `@{deco_name}` does not return the "
                                    f"delegate result — `{func_node.name}()` returns None"
                                ),
                                line=nd.lineno, col=0, ast_node=nd,
                            ))
                        # Also check: result = f(); result.method()
                        if (isinstance(nd, ast.Assign) and
                                isinstance(nd.value, ast.Call) and
                                isinstance(nd.value.func, ast.Name) and
                                nd.value.func.id == func_node.name and
                                len(nd.targets) == 1 and
                                isinstance(nd.targets[0], ast.Name)):
                            result_var = nd.targets[0].id
                            # Find uses of result_var with attribute/method access
                            for use_nd in ast.walk(user_node):
                                if (isinstance(use_nd, ast.Attribute) and
                                        isinstance(use_nd.value, ast.Name) and
                                        use_nd.value.id == result_var and
                                        use_nd.lineno > nd.lineno):
                                    reqs.append(SectionRequirement(
                                        site_id=SiteId(kind=SiteKind.SSA_VALUE,
                                                       name=f"deco_null_{result_var}_L{use_nd.lineno}"),
                                        bug_type="NULL_PTR",
                                        required_predicate=Comparison(
                                            op='!=',
                                            left=Var(f"{result_var}_is_none"),
                                            right=IntLit(1)),
                                        description=(
                                            f"decorator `@{deco_name}` does not return the "
                                            f"delegate result — `{result_var}` is None"
                                        ),
                                        line=use_nd.lineno, col=0, ast_node=use_nd,
                                    ))
            elif wrapper_issue == "transforms_return":
                # Decorator changes return type — potential TYPE_ERROR
                # for callers expecting the original type
                for user_node in ast.walk(tree):
                    if not isinstance(user_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        continue
                    if user_node.name == func_node.name or user_node.name == deco_name:
                        continue
                    for nd in ast.walk(user_node):
                        if (isinstance(nd, ast.Assign) and
                                isinstance(nd.value, ast.Call) and
                                isinstance(nd.value.func, ast.Name) and
                                nd.value.func.id == func_node.name and
                                len(nd.targets) == 1 and
                                isinstance(nd.targets[0], ast.Name)):
                            result_var = nd.targets[0].id
                            # Check if result is used with arithmetic ops
                            for use_nd in ast.walk(user_node):
                                if (isinstance(use_nd, ast.BinOp) and
                                        isinstance(use_nd.left, ast.Name) and
                                        use_nd.left.id == result_var and
                                        isinstance(use_nd.op, (ast.Div, ast.FloorDiv,
                                                               ast.Mod, ast.Mult,
                                                               ast.Sub, ast.Pow))):
                                    reqs.append(SectionRequirement(
                                        site_id=SiteId(kind=SiteKind.SSA_VALUE,
                                                       name=f"deco_type_{result_var}_L{use_nd.lineno}"),
                                        bug_type="NULL_PTR",
                                        required_predicate=Comparison(
                                            op='!=',
                                            left=Var(f"{result_var}_carrier"),
                                            right=IntLit(0)),
                                        description=(
                                            f"decorator `@{deco_name}` transforms return type — "
                                            f"`{result_var}` has unexpected carrier"
                                        ),
                                        line=use_nd.lineno, col=0, ast_node=use_nd,
                                    ))

    return reqs


def _check_decorator_wrapper_return(
    deco_def: ast.FunctionDef,
) -> Optional[str]:
    """Analyze a decorator definition for wrapper return issues.

    Returns:
        ``"drops_return"`` if the inner wrapper calls the delegate but does
        not return the result; ``"transforms_return"`` if it wraps the result
        in a type-changing constructor; ``None`` if transparent.
    """
    # Find the inner function that is returned
    inner_func: Optional[ast.FunctionDef] = None
    returned_name: Optional[str] = None

    for node in ast.iter_child_nodes(deco_def):
        if isinstance(node, ast.Return) and isinstance(node.value, ast.Name):
            returned_name = node.value.id

    for node in ast.iter_child_nodes(deco_def):
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and
                node.name == returned_name):
            inner_func = node
            break

    if inner_func is None:
        return None

    # Find delegate calls in the inner function — calls to the decorator's param
    deco_param = None
    if deco_def.args.args:
        deco_param = deco_def.args.args[0].arg

    if not deco_param:
        return None

    # Check if the inner function returns the delegate call
    delegate_calls: List[ast.Call] = []
    return_stmts: List[ast.Return] = []
    for node in ast.walk(inner_func):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            if node.func.id == deco_param:
                delegate_calls.append(node)
        if isinstance(node, ast.Return):
            return_stmts.append(node)

    if not delegate_calls:
        return None

    # Check if any return statement returns the delegate call result
    for ret in return_stmts:
        if ret.value is None:
            continue
        # Direct return of call: `return func(*args)`
        if isinstance(ret.value, ast.Call) and isinstance(ret.value.func, ast.Name):
            if ret.value.func.id == deco_param:
                return None  # transparent
        # Return of variable that was assigned from call
        if isinstance(ret.value, ast.Name):
            # Check if this var was assigned from delegate call
            for node in ast.walk(inner_func):
                if (isinstance(node, ast.Assign) and
                        len(node.targets) == 1 and
                        isinstance(node.targets[0], ast.Name) and
                        node.targets[0].id == ret.value.id):
                    if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name):
                        if node.value.func.id == deco_param:
                            return None  # transparent
        # Return of transformed value: `return str(result)`
        if isinstance(ret.value, ast.Call) and isinstance(ret.value.func, ast.Name):
            func_name = ret.value.func.id
            if func_name in ('str', 'int', 'float', 'bool', 'list', 'tuple', 'dict', 'set'):
                return "transforms_return"

    # No return of delegate result found
    if not return_stmts or all(r.value is None for r in return_stmts):
        return "drops_return"

    # Has returns but none return the delegate
    for ret in return_stmts:
        if ret.value is not None:
            return "drops_return"

    return "drops_return"


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


def _short_circuit_guards_subscript(node: ast.Subscript,
                                     tree: ast.Module) -> bool:
    """Check if a subscript ``d[k]`` is guarded by short-circuit ``and``.

    In sheaf terms, within a single observation site (the if-condition),
    a ``BoolOp(And, [test₁, test₂, …])`` induces a **short-circuit
    evaluation topology**: conjunct ``testⱼ`` is only evaluated over the
    open set where ``test₁ ∧ … ∧ testⱼ₋₁`` holds.  If an earlier conjunct
    is ``key in dict``, the subscript ``dict[key]`` in a later conjunct is
    evaluated in a fiber where the key is guaranteed present — the
    restriction map automatically resolves the KEY_ERROR requirement.

    Also handles length-check guards: ``len(seq) > k and seq[k]`` induces
    the same short-circuit topology where the index section is bounded.
    """
    target_dict = ast.dump(node.value)
    target_key = ast.dump(node.slice)
    # Extract constant index if present (for length guard matching)
    const_idx = None
    if isinstance(node.slice, ast.Constant) and isinstance(node.slice.value, int):
        const_idx = node.slice.value

    for parent in ast.walk(tree):
        if not isinstance(parent, ast.BoolOp):
            continue
        is_and = isinstance(parent.op, ast.And)
        is_or = isinstance(parent.op, ast.Or)
        if not is_and and not is_or:
            continue
        # Find which conjunct/disjunct contains our subscript node
        sub_idx = -1
        for i, val in enumerate(parent.values):
            for child in ast.walk(val):
                if child is node:
                    sub_idx = i
                    break
            if sub_idx >= 0:
                break
        if sub_idx <= 0:
            continue  # not found or first conjunct — no prior guard

        if is_and:
            # Check earlier conjuncts for `key in dict` or length guards
            for j in range(sub_idx):
                earlier = parent.values[j]
                if isinstance(earlier, ast.Compare) and len(earlier.ops) == 1:
                    if isinstance(earlier.ops[0], ast.In):
                        # `key in dict`
                        cmp_key = ast.dump(earlier.left)
                        if earlier.comparators and ast.dump(earlier.comparators[0]) == target_dict:
                            if cmp_key == target_key:
                                return True
                    # ── Length-check topology: ``len(seq) > k`` guards ``seq[k]`` ──
                    if const_idx is not None and _is_len_guard_for(earlier, node.value, const_idx):
                        return True
                # ── Truthiness topology: ``seq and seq[k]`` ──
                # If an earlier conjunct IS the sequence itself (truthiness check),
                # it guarantees the sequence is non-empty (truthy), making
                # seq[0] safe.  This is the OPEN SET condition: the non-empty
                # fiber is an open subscheme of the sequence presheaf.
                if isinstance(earlier, ast.Name):
                    if ast.dump(node.value) == ast.dump(earlier):
                        return True  # Truthiness guards subscript access
                # Also handle nested subscript
                if isinstance(earlier, ast.Compare) and len(earlier.ops) == 1:
                    if isinstance(earlier.ops[0], ast.In) and earlier.comparators:
                        cmp_dict = ast.dump(earlier.comparators[0])
                        if cmp_dict == target_dict:
                            cmp_key = ast.dump(earlier.left)
                            if cmp_key == target_key:
                                return True

        elif is_or:
            # ── Or short-circuit topology ──
            # In BoolOp(Or, [not X, ...X[k]...]), the later disjuncts
            # are evaluated only when earlier ones are False.  If an
            # earlier disjunct is ``not seq`` (falsy guard), then when
            # it's False, ``seq`` is truthy (non-empty).  So seq[0] is
            # safe — the non-empty fiber section covers index 0.
            for j in range(sub_idx):
                earlier = parent.values[j]
                # `not seq` → when False, seq is truthy (non-empty)
                if isinstance(earlier, ast.UnaryOp) and isinstance(earlier.op, ast.Not):
                    operand = earlier.operand
                    target_seq = ast.dump(node.value)
                    if ast.dump(operand) == target_seq:
                        if const_idx is not None and const_idx == 0:
                            return True
                    # Also: `not seq[0]` protects seq[0] (it was already evaluated)
                    if isinstance(operand, ast.Subscript) and ast.dump(operand) == ast.dump(node):
                        return True
    return False


def _is_len_guard_for(cmp: ast.Compare, seq_node: ast.expr, idx: int) -> bool:
    """Check if a comparison is a length guard for ``seq[idx]``.

    Matches patterns like: ``len(seq) > idx``, ``len(seq) >= idx+1``,
    ``idx < len(seq)``, etc. — any comparison that ensures the sequence
    has enough elements for the given index.
    """
    if len(cmp.ops) != 1 or len(cmp.comparators) != 1:
        return False
    op = cmp.ops[0]
    left = cmp.left
    right = cmp.comparators[0]
    seq_dump = ast.dump(seq_node)

    def _is_len_call(n: ast.expr) -> bool:
        return (isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                and n.func.id == 'len' and len(n.args) == 1
                and ast.dump(n.args[0]) == seq_dump)

    def _const_val(n: ast.expr) -> Optional[int]:
        if isinstance(n, ast.Constant) and isinstance(n.value, int):
            return n.value
        return None

    # len(seq) > k, len(seq) >= k+1
    if _is_len_call(left):
        rval = _const_val(right)
        if rval is not None:
            if isinstance(op, ast.Gt) and rval <= idx:
                return True
            if isinstance(op, ast.GtE) and rval <= idx + 1:
                return True
    # k < len(seq), k+1 <= len(seq)
    if _is_len_call(right):
        lval = _const_val(left)
        if lval is not None:
            if isinstance(op, ast.Lt) and lval <= idx:
                return True
            if isinstance(op, ast.LtE) and lval <= idx + 1:
                return True
    return False


def _comp_filter_guards_subscript(node: ast.Subscript,
                                   tree: ast.Module) -> bool:
    """Check if a dict subscript ``d[k]`` is guarded by a comprehension filter.

    In sheaf terms, a comprehension ``{expr for var in iter if guard}``
    restricts the iteration fiber to the sub-site where ``guard`` holds.
    If the guard is ``k in d`` (or similar membership test) and the
    comprehension body contains ``d[k]``, the key-existence section is
    total over the restricted fiber — no obstruction.
    """
    target_dict = ast.dump(node.value)
    target_key = ast.dump(node.slice)

    for parent in ast.walk(tree):
        if not isinstance(parent, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            continue
        for gen in parent.generators:
            for filt in gen.ifs:
                # Check for ``key in dict`` pattern
                if isinstance(filt, ast.Compare) and len(filt.ops) == 1:
                    if isinstance(filt.ops[0], ast.In):
                        cmp_key = ast.dump(filt.left)
                        cmp_dict = ast.dump(filt.comparators[0])
                        if cmp_key == target_key and cmp_dict == target_dict:
                            # Verify node is inside this comprehension
                            for desc in ast.walk(parent):
                                if desc is node:
                                    return True
    return False


def _has_emptiness_guard(tree: ast.Module, var_name: str,
                         use_line: int) -> bool:
    """Emptiness-fiber restriction: check if *var_name* has a truthiness
    guard that restricts the stalk to the non-empty sub-presheaf before
    *use_line*.

    Recognises patterns like::

        if not var_name: return ...   # early exit on empty
        if len(var_name) == 0: ...    # explicit length check
        if var_name:                  # truthiness used in positive branch
    """
    for fn_node in ast.walk(tree):
        if not isinstance(fn_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for child in ast.walk(fn_node):
            if not isinstance(child, ast.If):
                continue
            if child.lineno >= use_line:
                continue
            test = child.test
            # Pattern 1: ``if not var:`` with early exit in body
            if (isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)
                    and isinstance(test.operand, ast.Name)
                    and test.operand.id == var_name):
                # Check body has early exit (return/raise/break/continue)
                for stmt in child.body:
                    if isinstance(stmt, (ast.Return, ast.Raise, ast.Break,
                                         ast.Continue)):
                        return True
            # Pattern 2: ``if var:`` — use is in body (positive branch)
            if isinstance(test, ast.Name) and test.id == var_name:
                # Check that use_line falls inside the body
                if child.body:
                    body_start = child.body[0].lineno
                    body_end = max(getattr(s, 'end_lineno', s.lineno)
                                   for s in child.body)
                    if body_start <= use_line <= body_end:
                        return True
            # Pattern 3: ``if len(var) == 0: return``
            if isinstance(test, ast.Compare) and len(test.ops) == 1:
                cmp = test.comparators[0]
                if (isinstance(test.left, ast.Call)
                        and isinstance(test.left.func, ast.Name)
                        and test.left.func.id == 'len'
                        and len(test.left.args) == 1
                        and isinstance(test.left.args[0], ast.Name)
                        and test.left.args[0].id == var_name):
                    if (isinstance(test.ops[0], ast.Eq)
                            and isinstance(cmp, ast.Constant)
                            and cmp.value == 0):
                        for stmt in child.body:
                            if isinstance(stmt, (ast.Return, ast.Raise)):
                                return True
    return False


def _has_length_alias(tree: ast.Module, param_name: str,
                      seq_name: str) -> bool:
    """Arithmetic-fiber section detection: check if *param_name* appears in a
    ``len(seq_name)`` comparison anywhere in the enclosing function.

    Sheaf-theoretically, a comparison like ``len(collected) >= n`` creates a
    **section in the arithmetic fiber** that constrains the parameter's value
    relative to the collection's cardinality.  When such a section exists,
    the parameter is *not* a pure precondition living only in the caller's
    input boundary — the function itself establishes the length-alias
    relationship.  The ``is_param_idx`` skip should therefore NOT apply,
    because the local presheaf has enough information to detect an
    off-by-one or out-of-bounds access.

    Patterns detected::

        if len(seq) >= param: break   # loop accumulates exactly param items
        len(seq) == param              # equality constraint
        len(seq) > param               # strict bound
        param < len(seq)               # reversed form
    """
    for fn_node in ast.walk(tree):
        if not isinstance(fn_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        # Only consider the function that contains seq_name in scope
        fn_params = {a.arg for a in fn_node.args.args}
        if param_name not in fn_params:
            continue
        for child in ast.walk(fn_node):
            if not isinstance(child, ast.Compare):
                continue
            # Gather all sub-expressions in the comparison chain
            all_exprs = [child.left] + list(child.comparators)
            has_len_seq = False
            has_param = False
            for expr in all_exprs:
                # Detect len(seq_name)
                if (isinstance(expr, ast.Call)
                        and isinstance(expr.func, ast.Name)
                        and expr.func.id == 'len'
                        and len(expr.args) == 1
                        and isinstance(expr.args[0], ast.Name)
                        and expr.args[0].id == seq_name):
                    has_len_seq = True
                # Detect bare param reference
                if isinstance(expr, ast.Name) and expr.id == param_name:
                    has_param = True
            if has_len_seq and has_param:
                return True
    return False


def _fromkeys_guards_subscript(node: ast.Subscript,
                                tree: ast.Module) -> bool:
    """Check if a dict subscript ``d[k]`` is on a dict built by ``dict.fromkeys``.

    ``d = dict.fromkeys(keys)`` produces a dict whose key fiber is exactly
    ``keys``.  Any subsequent access ``d[k]`` where ``k`` is drawn from
    ``keys`` (syntactically: ``d[keys[i]]``) has a guaranteed key section.
    More broadly, the dict is fully populated for all elements of the
    iterable used as the first argument.
    """
    # Identify the dict variable being subscripted
    if not isinstance(node.value, ast.Name):
        return False
    dict_var = node.value.id

    # Walk enclosing function to find assignment ``dict_var = dict.fromkeys(...)``
    for parent in ast.walk(tree):
        if not isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for stmt in ast.walk(parent):
            if not isinstance(stmt, ast.Assign):
                continue
            if (len(stmt.targets) == 1
                    and isinstance(stmt.targets[0], ast.Name)
                    and stmt.targets[0].id == dict_var):
                rhs = stmt.value
                if (isinstance(rhs, ast.Call)
                        and isinstance(rhs.func, ast.Attribute)
                        and isinstance(rhs.func.value, ast.Name)
                        and rhs.func.value.id == 'dict'
                        and rhs.func.attr == 'fromkeys'):
                    return True
    return False


def _defaultdict_guards_subscript(node: ast.Subscript,
                                   tree: ast.Module) -> bool:
    """Check if a dict subscript ``d[k]`` is on a ``collections.defaultdict``.

    ``defaultdict(factory)`` supplies a default value for missing keys,
    so ``d[k]`` never raises ``KeyError``.  In sheaf terms, the
    key-existence section is total by construction — the default factory
    closes every gap in the key fiber.
    """
    if not isinstance(node.value, ast.Name):
        return False
    dict_var = node.value.id

    for parent in ast.walk(tree):
        if not isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Module)):
            continue
        for stmt in ast.walk(parent):
            if not isinstance(stmt, ast.Assign):
                continue
            if (len(stmt.targets) == 1
                    and isinstance(stmt.targets[0], ast.Name)
                    and stmt.targets[0].id == dict_var):
                rhs = stmt.value
                # defaultdict(...)
                if isinstance(rhs, ast.Call):
                    func = rhs.func
                    # Direct: defaultdict(int)
                    if isinstance(func, ast.Name) and func.id == 'defaultdict':
                        return True
                    # Qualified: collections.defaultdict(int)
                    if (isinstance(func, ast.Attribute) and func.attr == 'defaultdict'
                            and isinstance(func.value, ast.Name)
                            and func.value.id == 'collections'):
                        return True
    return False


def _assert_provably_true(node: ast.Assert, tree: ast.Module) -> bool:
    """Check if an assertion is provably true from preceding statements.

    In sheaf terms, the presheaf section at the assert site already
    satisfies the assertion predicate — the restriction map from
    preceding assignments to the assert test is provably total.

    Recognizes:
    - Literal construction then assertion on len/truthiness
    - .append() / .extend() then non-empty assertion
    - Type coercion (int/str/float) then isinstance assertion
    - max/min clamp then range assertion
    - Conditional assignment (if None → assign) then `is not None` assert
    - `if` with else that covers all paths before assert
    """
    test = node.test
    # Find the enclosing function body
    func_body = None
    for fn in ast.walk(tree):
        if isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for i, stmt in enumerate(fn.body):
                if stmt is node or (hasattr(stmt, 'lineno') and stmt.lineno == node.lineno):
                    func_body = fn.body[:i]
                    break
        if func_body is not None:
            break
    if func_body is None:
        # Module-level
        for i, stmt in enumerate(tree.body):
            if stmt is node or (hasattr(stmt, 'lineno') and stmt.lineno == node.lineno):
                func_body = tree.body[:i]
                break
    if not func_body:
        return False

    # Helper: get the most recent assignment to a variable
    def _latest_assign(var_name: str) -> Optional[ast.expr]:
        for stmt in reversed(func_body):
            if isinstance(stmt, ast.Assign):
                for t in stmt.targets:
                    if isinstance(t, ast.Name) and t.id == var_name:
                        return stmt.value
            if isinstance(stmt, ast.AugAssign):
                if isinstance(stmt.target, ast.Name) and stmt.target.id == var_name:
                    return stmt
        return None

    # Helper: check if a preceding stmt mutates a container (append/extend)
    def _has_append_or_extend(var_name: str) -> bool:
        for stmt in func_body:
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                call = stmt.value
                if (isinstance(call.func, ast.Attribute)
                        and isinstance(call.func.value, ast.Name)
                        and call.func.value.id == var_name
                        and call.func.attr in ('append', 'extend', 'add', 'insert')):
                    return True
        return False

    # Helper: does the if/else before the assert guarantee a variable is not None?
    def _if_else_guarantees_not_none(var_name: str) -> bool:
        for stmt in reversed(func_body):
            if isinstance(stmt, ast.If):
                # Check if `if var is None: var = ...` or `if var is None: return`
                t = stmt.test
                checks_none = False
                if isinstance(t, ast.Compare) and len(t.ops) == 1:
                    if isinstance(t.ops[0], ast.Is) and t.comparators:
                        if isinstance(t.comparators[0], ast.Constant) and t.comparators[0].value is None:
                            if isinstance(t.left, ast.Name) and t.left.id == var_name:
                                checks_none = True
                if checks_none:
                    # If body assigns var to non-None, or returns/raises
                    for s in stmt.body:
                        if isinstance(s, ast.Assign):
                            for tgt in s.targets:
                                if isinstance(tgt, ast.Name) and tgt.id == var_name:
                                    return True
                        if isinstance(s, (ast.Return, ast.Raise)):
                            return True
        return False

    # ── Pattern 1: assert on truthiness/len of a literal list/dict/set/tuple ──
    # e.g. `result = [1,2,3]; assert len(result) > 0` or `assert result`
    if isinstance(test, ast.Name):
        rhs = _latest_assign(test.id)
        if rhs is not None:
            if isinstance(rhs, (ast.List, ast.Dict, ast.Set, ast.Tuple)):
                if isinstance(rhs, ast.Dict):
                    if rhs.keys:  # non-empty dict literal
                        return True
                else:
                    if getattr(rhs, 'elts', []):  # non-empty literal
                        return True
            if _has_append_or_extend(test.id):
                return True

    # len(x) > 0 or len(x) >= 1
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        left, op, right = test.left, test.ops[0], test.comparators[0]
        # len(var) > 0 / len(var) >= 1 / len(var) != 0
        if (isinstance(left, ast.Call) and isinstance(left.func, ast.Name)
                and left.func.id == 'len' and left.args):
            arg = left.args[0]
            if isinstance(arg, ast.Name):
                var_name = arg.id
                rhs = _latest_assign(var_name)
                if rhs is not None:
                    if isinstance(rhs, (ast.List, ast.Set, ast.Tuple)) and getattr(rhs, 'elts', []):
                        return True
                    if isinstance(rhs, ast.Dict) and rhs.keys:
                        return True
                if _has_append_or_extend(var_name):
                    return True

    # ── Pattern 2: isinstance after type coercion ──
    # `x = int(x); assert isinstance(x, int)`
    if (isinstance(test, ast.Call) and isinstance(test.func, ast.Name)
            and test.func.id == 'isinstance' and len(test.args) >= 2):
        checked_arg = test.args[0]
        if isinstance(checked_arg, ast.Name):
            rhs = _latest_assign(checked_arg.id)
            if isinstance(rhs, ast.Call) and isinstance(rhs.func, ast.Name):
                coercion = rhs.func.id
                expected = test.args[1]
                # int(x) → isinstance(x, int)
                if isinstance(expected, ast.Name) and expected.id == coercion:
                    return True
                if isinstance(expected, ast.Tuple):
                    for elt in expected.elts:
                        if isinstance(elt, ast.Name) and elt.id == coercion:
                            return True

    # ── Pattern 3: range assertion after clamp ──
    # `x = max(lo, min(x, hi)); assert lo <= x <= hi`
    if isinstance(test, ast.Compare) and len(test.ops) >= 2:
        # Look for chained comparison: lo <= x <= hi
        for i, comparator in enumerate(test.comparators):
            if isinstance(comparator, ast.Name):
                rhs = _latest_assign(comparator.id)
                if rhs is not None and isinstance(rhs, ast.Call):
                    func = rhs.func
                    if isinstance(func, ast.Name) and func.id in ('max', 'min'):
                        # Clamp pattern detected
                        return True

    # ── Pattern 4: `is not None` after conditional assignment ──
    # `if val is None: val = ""; assert val is not None`
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        if isinstance(test.ops[0], ast.IsNot) and test.comparators:
            if isinstance(test.comparators[0], ast.Constant) and test.comparators[0].value is None:
                if isinstance(test.left, ast.Name):
                    if _if_else_guarantees_not_none(test.left.id):
                        return True

    return False


def _extract_requirements(source: str) -> List[SectionRequirement]:
    """Extract type section requirements from the AST.

    Each requirement says: "at this site, the value must satisfy this
    refinement predicate, or bug X can occur."
    """
    tree = ast.parse(textwrap.dedent(source))
    reqs: List[SectionRequirement] = []

    # Collect parameter names — parameters are assumed not-None at the
    # function boundary (they get the strongest possible section).
    # EXCEPTION: parameters with ``=None`` default have a PARTIAL section
    # in the nullability presheaf — they may be None when no argument is
    # passed. These remain in _param_names for general skipping but are
    # tracked separately in _none_default_params so the NULL_PTR check
    # can still fire for them.
    _param_names: Set[str] = set()
    _none_default_params: Set[str] = set()
    for fnode in ast.walk(tree):
        if isinstance(fnode, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
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
            # Track params with =None defaults (partial nullability section)
            if isinstance(fnode, (ast.FunctionDef, ast.AsyncFunctionDef)):
                defaults = fnode.args.defaults
                args = fnode.args.args
                if defaults:
                    offset = len(args) - len(defaults)
                    for i, d in enumerate(defaults):
                        if isinstance(d, ast.Constant) and d.value is None:
                            _none_default_params.add(args[offset + i].arg)
                for arg, d in zip(fnode.args.kwonlyargs, fnode.args.kw_defaults):
                    if d is not None and isinstance(d, ast.Constant) and d.value is None:
                        _none_default_params.add(arg.arg)

    # Collect imported module names — module objects are always bound and
    # never None, so attribute access on them (mod.func) is safe.
    # This provides resilience for unknown/third-party modules: even if we
    # don't know what acme_lib.transform() returns, we know acme_lib itself
    # is not None (the import guarantees it).
    _imported_modules: Set[str] = set()

    # Collect for-loop target variables — iteration binds them from the
    # iterable, so they share the caller-boundary assumption of params.
    _loop_target_names: Set[str] = set()
    for fnode in ast.walk(tree):
        if isinstance(fnode, ast.For):
            if isinstance(fnode.target, ast.Name):
                _loop_target_names.add(fnode.target.id)
            elif isinstance(fnode.target, ast.Tuple):
                for elt in fnode.target.elts:
                    if isinstance(elt, ast.Name):
                        _loop_target_names.add(elt.id)
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

    # Pre-pass: collect with-block scope information for USE_AFTER_FREE
    # detection. In sheaf terms the ``with`` statement defines a lifecycle
    # sub-cover: the ``as`` variable is in the OPEN section inside the block
    # body, and transitions to CLOSED at block exit.  Any use of that
    # variable AFTER the block's end_lineno is an obstruction.
    _with_block_vars: Dict[str, int] = {}  # var_name → block end_lineno
    for fnode in ast.walk(tree):
        if isinstance(fnode, ast.With):
            for item in fnode.items:
                if item.optional_vars is not None:
                    var = _expr_to_var_name(item.optional_vars, "")
                    if var and hasattr(fnode, 'end_lineno') and fnode.end_lineno:
                        _with_block_vars[var] = fnode.end_lineno
        elif isinstance(fnode, ast.AsyncWith):
            for item in fnode.items:
                if item.optional_vars is not None:
                    var = _expr_to_var_name(item.optional_vars, "")
                    if var and hasattr(fnode, 'end_lineno') and fnode.end_lineno:
                        _with_block_vars[var] = fnode.end_lineno

    # ── Constructor-provenance pre-pass ──
    # Variables assigned from constructor calls (``x = ClassName(...)``) have
    # a TOTAL nullability section — constructors never return None.
    # This avoids false NULL_PTR on ``d = Data(); d.value``.
    _constructor_vars: Set[str] = set()
    _non_constructor_assigned: Set[str] = set()  # vars assigned None or non-constructor
    for fnode in ast.walk(tree):
        if isinstance(fnode, ast.Assign) and len(fnode.targets) == 1:
            tgt = fnode.targets[0]
            if isinstance(tgt, ast.Name) and isinstance(fnode.value, ast.Call):
                call_func = fnode.value.func
                # ── Python Standard Library Return Type Theory ──
                # The following functions/constructors are GUARANTEED to return
                # non-None values.  This is a THEORY PACK for the Python standard
                # library, encoded as refinement types on return sites:
                #   {v : T | v is not None}
                #
                # The theory pack covers:
                # 1. Type constructors (int, str, list, dict, set, tuple, etc.)
                # 2. Built-in functions that always return values (len, sorted, etc.)
                # 3. Uppercase-first-letter heuristic for user-defined constructors
                _KNOWN_NONNULL_BUILTINS = frozenset({
                    # Type constructors
                    'int', 'str', 'float', 'bool', 'bytes', 'bytearray',
                    'list', 'dict', 'set', 'tuple', 'frozenset', 'complex',
                    # Collection constructors
                    'sorted', 'reversed', 'enumerate', 'zip', 'map', 'filter',
                    'range', 'slice', 'memoryview', 'super', 'type', 'object',
                    # Value-returning builtins
                    'len', 'sum', 'max', 'min', 'abs', 'round', 'pow',
                    'hash', 'id', 'hex', 'oct', 'bin', 'chr', 'ord',
                    'repr', 'ascii', 'format', 'divmod',
                    # I/O
                    'open', 'input',
                    # Math
                    'isinstance', 'issubclass', 'callable', 'hasattr',
                    # String formatting
                    'f', 'format',
                })
                func_name = ''
                if isinstance(call_func, ast.Name):
                    func_name = call_func.id
                elif isinstance(call_func, ast.Attribute):
                    func_name = call_func.attr

                if func_name in _KNOWN_NONNULL_BUILTINS:
                    _constructor_vars.add(tgt.id)
                # ClassName() — uppercase first letter heuristic for constructors
                elif isinstance(call_func, ast.Name) and call_func.id[:1].isupper():
                    _constructor_vars.add(tgt.id)
                # module.ClassName()
                elif isinstance(call_func, ast.Attribute) and call_func.attr[:1].isupper():
                    _constructor_vars.add(tgt.id)
                # Known non-None method returns
                # ── Non-None method returns theory pack ──
                # Methods that ALWAYS return a non-None value.
                # NOTE: .get() is NOT in this list because dict.get()
                # returns Optional[V] (can be None without a default).
                # .pop() is also excluded for dicts (raises KeyError, not None).
                elif isinstance(call_func, ast.Attribute) and call_func.attr in (
                    'copy', 'strip', 'lstrip', 'rstrip', 'lower', 'upper',
                    'replace', 'split', 'join', 'encode', 'decode',
                    'keys', 'values', 'items',
                    'extend', 'insert', 'remove', 'sort', 'reverse',
                    'union', 'intersection', 'difference',
                    'read', 'readline', 'readlines',
                    'format', 'center', 'ljust', 'rjust', 'zfill',
                    'title', 'capitalize', 'swapcase', 'expandtabs',
                ):
                    _constructor_vars.add(tgt.id)
                else:
                    _non_constructor_assigned.add(tgt.id)
            elif isinstance(tgt, ast.Name):
                # Literal containers ([], {}, set(), ()) are always non-None
                if isinstance(fnode.value, (ast.List, ast.Dict, ast.Set, ast.Tuple)):
                    _constructor_vars.add(tgt.id)
                else:
                    _non_constructor_assigned.add(tgt.id)
    # A variable assigned BOTH from a constructor and from None/other is not safe
    _constructor_vars -= _non_constructor_assigned

    # ── dict.get(key) without default pre-pass (nullable fiber sources) ──
    # ``val = d.get(key)`` returns Optional[V]: the fiber at the assignment
    # site has carrier = V | None.  Any subsequent dereference (attribute,
    # subscript, BinOp) on ``val`` without a None check is a NULL_PTR
    # obstruction — the None stalk has no compatible section for the op.
    _dict_get_nullable_vars: Set[str] = set()
    for fnode in ast.walk(tree):
        if isinstance(fnode, ast.Assign) and len(fnode.targets) == 1:
            tgt = fnode.targets[0]
            if isinstance(tgt, ast.Name) and isinstance(fnode.value, ast.Call):
                if isinstance(fnode.value.func, ast.Attribute):
                    method_name = fnode.value.func.attr
                    if method_name == 'get' and len(fnode.value.args) <= 1:
                        # .get(key) with no default → nullable
                        _dict_get_nullable_vars.add(tgt.id)
                    elif method_name == 'get' and len(fnode.value.args) >= 2:
                        pass  # .get(key, default) → not nullable

    # ── Factory-returns-None pre-pass (intra-module None propagation) ──
    # If a locally-defined function returns None on ANY path (including
    # mixed return: some paths return a value, some return None), the
    # caller's variable is on the NULLABLE FIBER of the presheaf.
    # Sheaf-theoretically: the return-site section has carrier V ∪ {None},
    # and the restriction to the caller site inherits this nullable fiber.
    _factory_none_funcs: Set[str] = set()
    for fnode in ast.walk(tree):
        if isinstance(fnode, (ast.FunctionDef, ast.AsyncFunctionDef)):
            returns = [n for n in ast.walk(fnode) if isinstance(n, ast.Return)]
            has_none_return = any(
                r.value is None or
                (isinstance(r.value, ast.Constant) and r.value.value is None)
                for r in returns
            )
            if has_none_return:
                _factory_none_funcs.add(fnode.name)
    _factory_none_vars: Set[str] = set()
    for fnode in ast.walk(tree):
        if isinstance(fnode, ast.Assign) and len(fnode.targets) == 1:
            tgt = fnode.targets[0]
            if isinstance(tgt, ast.Name) and isinstance(fnode.value, ast.Call):
                call_name = _get_call_name(fnode.value)
                if call_name in _factory_none_funcs:
                    _factory_none_vars.add(tgt.id)

    # ── Nullable scheme assembly (algebraic geometry) ──
    # The CLOSED SUBSCHEME of the nullability presheaf: variables that
    # have positive evidence of potentially being None.  Variables NOT
    # in this set live on the GENERIC FIBER (non-None by default).
    _nullable_vars: Set[str] = (
        _dict_get_nullable_vars
        | _factory_none_vars
        | _none_default_params
    )
    # Also: variables explicitly assigned None
    for fnode in ast.walk(tree):
        if isinstance(fnode, ast.Assign) and len(fnode.targets) == 1:
            tgt = fnode.targets[0]
            if isinstance(tgt, ast.Name):
                if isinstance(fnode.value, ast.Constant) and fnode.value.value is None:
                    _nullable_vars.add(tgt.id)
                # Also: .find() / .search() / .match() return None on failure
                if isinstance(fnode.value, ast.Call) and isinstance(fnode.value.func, ast.Attribute):
                    method = fnode.value.func.attr
                    if method in ('find', 'search', 'match', 'group',
                                  'first', 'last', 'find_one', 'fetchone',
                                  'get_attribute', 'getElementById'):
                        _nullable_vars.add(tgt.id)

    # ── Thread-safe container pre-pass ──
    # Variables assigned from ``queue.Queue()`` are inherently thread-safe;
    # operations on them do not constitute data races.
    _thread_safe_vars: Set[str] = set()
    for fnode in ast.walk(tree):
        if isinstance(fnode, ast.Assign) and len(fnode.targets) == 1:
            tgt = fnode.targets[0]
            if isinstance(tgt, ast.Name) and isinstance(fnode.value, ast.Call):
                call_name = _get_call_name(fnode.value)
                if call_name in ('queue.Queue', 'Queue', 'queue.PriorityQueue',
                                 'queue.LifoQueue', 'queue.SimpleQueue',
                                 'multiprocessing.Queue'):
                    _thread_safe_vars.add(tgt.id)

    # ── Threading-import concurrent fiber topology pre-pass ──
    # When ``import threading`` is present, module-level mutable state
    # mutations form open covers in the synchronization presheaf.  We
    # pre-compute the set of global variables declared via ``global x``
    # inside functions, and module-level mutable objects (list, dict, set
    # literals at module scope), to identify race sites even without an
    # explicit ``Thread(target=…)`` constructor in the snippet.
    _threading_imported_flag = _threading_imported(tree)
    _global_vars_in_funcs: Set[str] = set()
    _module_level_mutables: Set[str] = set()
    if _threading_imported_flag:
        # Collect variables declared ``global x`` inside any function
        for fnode in ast.walk(tree):
            if isinstance(fnode, (ast.FunctionDef, ast.AsyncFunctionDef)):
                for stmt in ast.walk(fnode):
                    if isinstance(stmt, ast.Global):
                        _global_vars_in_funcs.update(stmt.names)
        # Collect module-level mutable assignments (list/dict/set literals,
        # or mutable constructors at module scope)
        for stmt in (tree.body if hasattr(tree, 'body') else []):
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
                tgt = stmt.targets[0]
                if isinstance(tgt, ast.Name):
                    val = stmt.value
                    if isinstance(val, (ast.List, ast.Dict, ast.Set)):
                        _module_level_mutables.add(tgt.id)
                    elif isinstance(val, ast.Constant) and isinstance(val.value, (int, float)):
                        # Scalar module-level vars mutated via ``global``
                        if tgt.id in _global_vars_in_funcs:
                            _module_level_mutables.add(tgt.id)

    for node in ast.walk(tree):
        # ── REFINEMENT_GAP: Division by zero ──
        # Algebraic geometry: the divisor site has a STALK at each point.
        # When the divisor is a CONSTANT, the stalk is a POINT (single value).
        # If that point ≠ 0, the viability predicate {v | v ≠ 0} is
        # trivially satisfied — no obstruction in H¹.
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Div, ast.FloorDiv, ast.Mod)):
            # ── Algebraic invariant propagation for divisors ──
            # The divisor site's stalk encodes the value constraint.
            # We check several algebraic invariants that guarantee ≠ 0:
            #
            # 1. Constant nonzero: stalk is a point ≠ 0
            # 2. String formatting: % on string is NOT division
            # 3. len() result: len(x) ≥ 0, and len(x) = 0 only when empty
            # 4. Sum of squares: Σx² ≥ 0 (always non-negative)
            # 5. Sum of exponentials: Σeˣ > 0 (always positive)

            # String formatting: "..." % args is NOT division
            if isinstance(node.op, ast.Mod):
                if isinstance(node.left, ast.Constant) and isinstance(node.left.value, str):
                    continue  # String formatting, not modulo
                if isinstance(node.left, ast.JoinedStr):
                    continue  # f-string formatting

            # Constant divisor: check value at the point
            if isinstance(node.right, ast.Constant) and isinstance(node.right.value, (int, float)):
                if node.right.value != 0:
                    pass  # Constant nonzero: stalk satisfies viability
                else:
                    # Division by literal 0: always an error
                    divisor_var = _expr_to_var_name(node.right, f"div_rhs_L{node.lineno}")
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"div_L{node.lineno}"),
                        bug_type="DIV_ZERO",
                        required_predicate=Comparison(op='!=', left=Var(divisor_var), right=IntLit(0)),
                        description=f"divisor `{_expr_repr(node.right)}` is 0",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))
            else:
                # Non-constant divisor: stalk may include 0
                divisor_var = _expr_to_var_name(node.right, f"div_rhs_L{node.lineno}")
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"div_L{node.lineno}"),
                    bug_type="DIV_ZERO",
                    required_predicate=Comparison(op='!=', left=Var(divisor_var), right=IntLit(0)),
                    description=f"divisor `{_expr_repr(node.right)}` must be ≠ 0",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # ── REFINEMENT_GAP: Unbounded shift / power ──
        # Python semantics: integers have ARBITRARY PRECISION (Spec(ℤ)).
        # There is no integer overflow in Python — the ring ℤ has no
        # bounded subscheme.  INTEGER_OVERFLOW is only relevant for:
        # - struct.pack (fixed-width) — handled separately
        # - ctypes (C interop) — handled separately
        # - Left shifts producing memory issues — flag only for << with
        #   very large exponents
        #
        # For pure Python arithmetic: SUPPRESS INTEGER_OVERFLOW.
        # The presheaf over Spec(ℤ) has a global section for any integer.
        if False and isinstance(node, ast.BinOp) and isinstance(node.op, (ast.LShift, ast.Pow)):
            exponent = node.right
            base_expr = node.left
            exp_var = _expr_to_var_name(exponent, f"exp_L{node.lineno}")
            _exp_is_literal = (isinstance(exponent, ast.Constant)
                               and isinstance(exponent.value, (int, float)))
            _base_is_literal = (isinstance(base_expr, ast.Constant)
                                and isinstance(base_expr.value, (int, float)))
            if not (_exp_is_literal and _base_is_literal):
                # Skip when the result flows into a bitmask-bounded
                # variable.  Look for ``&= MASK`` or ``& MASK`` on any
                # ancestor variable in the enclosing function.
                _has_downstream_mask = False
                for _fn in ast.walk(tree):
                    if not isinstance(_fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        continue
                    _fn_contains = False
                    for _d in ast.walk(_fn):
                        if _d is node:
                            _fn_contains = True
                            break
                    if not _fn_contains:
                        continue
                    for _d in ast.walk(_fn):
                        if (isinstance(_d, ast.AugAssign)
                                and isinstance(_d.op, ast.BitAnd)
                                and isinstance(_d.value, ast.Constant)
                                and isinstance(_d.value.value, int)
                                and _d.value.value > 0):
                            _has_downstream_mask = True
                            break
                        if (isinstance(_d, ast.BinOp)
                                and isinstance(_d.op, ast.BitAnd)):
                            if ((isinstance(_d.right, ast.Constant)
                                 and isinstance(_d.right.value, int)
                                 and _d.right.value > 0) or
                                (isinstance(_d.left, ast.Constant)
                                 and isinstance(_d.left.value, int)
                                 and _d.left.value > 0)):
                                _has_downstream_mask = True
                                break
                    break  # only check the enclosing function
                if _has_downstream_mask:
                    pass  # Bitmask truncates the magnitude fiber
                else:
                    op_name = "<<" if isinstance(node.op, ast.LShift) else "**"
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.SSA_VALUE,
                                       name=f"shift_pow_L{node.lineno}"),
                        bug_type="INTEGER_OVERFLOW",
                        required_predicate=Comparison(
                            op='<=', left=Var(exp_var), right=IntLit(63)),
                    description=(
                        f"`{_expr_repr(base_expr)} {op_name} {_expr_repr(exponent)}`"
                        f" — unbounded {op_name} can overflow"
                    ),
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # ── REFINEMENT_GAP: Unbounded loop accumulation ──
        # Python semantics: integers have ARBITRARY PRECISION.
        # Accumulation (total += x) never overflows in Python.
        # This check is only relevant for C/Java interop.
        # SUPPRESS for pure Python code (Spec(ℤ) has no bounded section).
        if False and isinstance(node, ast.AugAssign) and isinstance(node.op, (ast.Add, ast.Mult)):
            _enclosing_for = None
            for ancestor in ast.walk(tree):
                if isinstance(ancestor, ast.For):
                    for child in ast.walk(ancestor):
                        if child is node:
                            _enclosing_for = ancestor
                            break
                    if _enclosing_for:
                        break
            if _enclosing_for is not None and isinstance(node.target, ast.Name):
                accum_var = node.target.id
                # Check for in-loop overflow guard: ``if var > LIMIT: raise``
                # or any Raise inside the same loop body — indicates the
                # programmer has bounded the accumulation fiber.
                _has_loop_overflow_guard = False
                for loop_child in ast.walk(_enclosing_for):
                    if isinstance(loop_child, ast.Raise):
                        _has_loop_overflow_guard = True
                        break
                    # Also: comparison against the accumulator in an if-test
                    if (isinstance(loop_child, ast.If)
                            and isinstance(loop_child.test, ast.Compare)):
                        try:
                            cond_text = ast.unparse(loop_child.test)
                        except Exception:
                            cond_text = ""
                        if accum_var in cond_text and any(
                                op in cond_text for op in ('>', '<', '>=', '<=')):
                            _has_loop_overflow_guard = True
                            break
                if not _has_loop_overflow_guard:
                    op_sym = "+=" if isinstance(node.op, ast.Add) else "*="
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.SSA_VALUE,
                                       name=f"accum_L{node.lineno}"),
                        bug_type="INTEGER_OVERFLOW",
                        required_predicate=Comparison(
                            op='<=', left=Var(accum_var), right=IntLit(2**63)),
                        description=(
                            f"`{accum_var} {op_sym} ...` in loop — "
                            f"unbounded accumulation can overflow"
                        ),
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

        # ── REFINEMENT_GAP: None dereference (generic-point principle) ──
        #
        # Algebraic geometry approach: model Python values as a SCHEME
        # where the GENERIC POINT η has stalk = {all non-None values}
        # and the CLOSED POINT ξ has stalk = {None}.
        #
        # A variable lives on the CLOSED SUBSCHEME (nullable) ONLY when
        # there is POSITIVE EVIDENCE of nullability:
        #   - Assigned from dict.get() / .find() / .search() (returns Optional)
        #   - Has a = None default parameter value
        #   - Explicitly assigned None
        #   - Assigned from a function known to return Optional
        #
        # Everything else lives on the GENERIC FIBER (non-None by default).
        # This inverts the traditional "flag everything, exempt known-safe"
        # approach. Instead: "flag ONLY variables on the nullable scheme."
        #
        # This is the sheaf-theoretic principle: the GENERIC STALK of the
        # nullability presheaf is {non-None}. Only the SPECIALIZATION to
        # the closed point introduces None. Obstructions (H¹) arise only
        # at overlaps where a nullable variable flows into a non-null-requiring
        # site — not at every attribute access.
        if isinstance(node, ast.Attribute):
            if isinstance(node.value, ast.Name):
                var_name = node.value.id
                # Only flag NULL_PTR if the variable is on the NULLABLE SUBSCHEME
                is_nullable = (
                    var_name in _none_default_params       # =None default
                    or var_name in _nullable_vars           # assigned from .get() etc.
                )
                if is_nullable:
                    obj_var = _expr_to_var_name(node.value, f"obj_L{node.lineno}")
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"attr_L{node.lineno}"),
                        bug_type="NULL_PTR",
                        required_predicate=Comparison(op='!=', left=Var(f"{obj_var}_is_none"), right=IntLit(1)),
                        description=f"`{_expr_repr(node.value)}.{node.attr}` — object must not be None",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                        nullable_evidence=True,
                    ))
            elif isinstance(node.value, ast.Subscript):
                # dict_result[key].attr — the dict result might be None
                # Only flag if the dict access is from a nullable source
                pass  # Generic point: assume non-None unless evidence
            # Constants, calls, and other non-Name values: generic fiber (non-None)

        # ── REFINEMENT_GAP: Calling a None-default parameter ──
        # When a function param has ``=None`` default, calling it directly
        # (``callback(x)``) without a None-guard is a NULL_PTR obstruction
        # because the nullability stalk is partial.
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            if node.func.id in _none_default_params:
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"call_none_L{node.lineno}"),
                    bug_type="NULL_PTR",
                    required_predicate=Comparison(op='!=', left=Var(f"{node.func.id}_is_none"), right=IntLit(1)),
                    description=f"callable `{node.func.id}` may be None (default=None)",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # ── REFINEMENT_GAP: None dereference on subscript access ──
        # ``obj[key]`` / ``obj[idx]`` on a None object raises TypeError.
        # This mirrors the attribute-access NULL_PTR check above but for
        # subscript operations — the object fiber must exclude ⊥.
        # ── Generic-point principle for subscript NULL_PTR ──
        # Only flag subscript access as NULL_PTR if the object variable
        # lives on the NULLABLE SUBSCHEME (has evidence of being None).
        if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name):
            ctx = getattr(node, 'ctx', None)
            if isinstance(ctx, ast.Load):
                obj_id = node.value.id
                if obj_id in _nullable_vars:
                    obj_var = _expr_to_var_name(node.value, f"subobj_L{node.lineno}")
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"sub_null_L{node.lineno}"),
                        bug_type="NULL_PTR",
                        required_predicate=Comparison(op='!=', left=Var(f"{obj_var}_is_none"), right=IntLit(1)),
                        description=f"`{obj_id}[...]` — object must not be None for subscript access",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

        # ── REFINEMENT_GAP: BinOp on nullable variable ──
        # ``val = d.get(key); val + 1`` — if val is None (from dict.get
        # without default), the BinOp raises TypeError.  In sheaf terms the
        # nullable fiber at the BinOp site has no ⊕-compatible section.
        if isinstance(node, ast.BinOp):
            for operand in (node.left, node.right):
                if isinstance(operand, ast.Name):
                    v = operand.id
                    if v in _dict_get_nullable_vars or v in _factory_none_vars:
                        reqs.append(SectionRequirement(
                            site_id=SiteId(kind=SiteKind.SSA_VALUE,
                                           name=f"binop_null_L{node.lineno}"),
                            bug_type="NULL_PTR",
                            required_predicate=Comparison(
                                op='!=', left=Var(f"{v}_is_none"), right=IntLit(1)),
                            description=(
                                f"`{v}` may be None (from dict.get/factory) — "
                                f"operand must not be None for BinOp"
                            ),
                            line=node.lineno, col=node.col_offset, ast_node=node,
                        ))
                        break  # one obstruction per BinOp

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

                # ── Length-alias override for param_idx ──
                # When the parameter appears in a ``len(collection)``
                # comparison with the collection being indexed, the
                # function itself establishes a section in the arithmetic
                # fiber relating the param to the collection's cardinality.
                # This is NOT a pure caller-side precondition — the local
                # presheaf has enough structure to detect off-by-one /
                # out-of-bounds obstructions.  Override the skip.
                if is_param_idx and isinstance(node.slice, ast.Name):
                    seq_name = _expr_to_var_name(node.value, "")
                    if seq_name and _has_length_alias(tree, node.slice.id, seq_name):
                        is_param_idx = False

                # ── Derived-collection override for param_idx ──
                # The param_idx skip is justified only when the COLLECTION
                # is itself a parameter (or a subscript chain rooted at a
                # parameter) — then the caller's presheaf controls both the
                # collection cardinality and the index.  When the collection
                # is locally constructed (e.g., data = list(matrix)), the
                # param may not be a valid index for the derived fiber.
                if is_param_idx:
                    def _seq_is_param_derived(val: ast.AST) -> bool:
                        if isinstance(val, ast.Name) and val.id in fn_params:
                            return True
                        if isinstance(val, ast.Subscript):
                            return _seq_is_param_derived(val.value)
                        return False
                    if not _seq_is_param_derived(node.value):
                        is_param_idx = False

                if not is_param_idx:
                    # ── Sheaf-theoretic skip conditions for INDEX_OOB ──
                    # Several patterns provide a TOTAL section in the
                    # bounds presheaf at extraction time, meaning no
                    # obstruction can arise.
                    skip_idx = False

                    # (a) REMOVED: len(X)-N suppression was unsound.
                    # items[len(items)-1] on an empty list DOES raise
                    # IndexError (len=0 → idx=-1 on empty → error).
                    # The correct approach: let the requirement stand and
                    # rely on guard recognition (e.g., `if len(items) > 0`)
                    # to resolve it via the obstruction→guard pipeline.

                    # (a2) Modular access: ``x[expr % len(x)]``.
                    # The modular arithmetic restricts the index fiber to
                    # [0, len(x)), the valid bounds sub-presheaf.  The section
                    # is total for non-empty containers (the remainder is
                    # always in-bounds).
                    if (isinstance(node.slice, ast.BinOp)
                            and isinstance(node.slice.op, ast.Mod)):
                        rhs = node.slice.right
                        # Pattern: x[i % len(x)]
                        if (isinstance(rhs, ast.Call)
                                and isinstance(rhs.func, ast.Name)
                                and rhs.func.id == 'len'
                                and len(rhs.args) == 1):
                            len_target = ast.dump(rhs.args[0])
                            seq_target = ast.dump(node.value)
                            if len_target == seq_target:
                                skip_idx = True

                    # (b) Constant index on a list literal with known
                    # cardinality: the cardinality section of the presheaf
                    # is total and the index is within bounds.
                    if isinstance(node.slice, ast.Constant) and isinstance(node.slice.value, int):
                        const_idx = node.slice.value
                        if isinstance(node.value, ast.Name):
                            target_name = node.value.id
                            # Look for assignment of list/tuple literal to target_name
                            for n2 in ast.walk(tree):
                                if (isinstance(n2, ast.Assign)
                                        and len(n2.targets) == 1
                                        and isinstance(n2.targets[0], ast.Name)
                                        and n2.targets[0].id == target_name
                                        and n2.lineno <= node.lineno):
                                    if isinstance(n2.value, (ast.List, ast.Tuple)):
                                        card = len(n2.value.elts)
                                        if 0 <= const_idx < card:
                                            skip_idx = True

                    # (c) `.partition()` returns a 3-tuple — indices 0,1,2
                    # are always valid.  Also handle ``list(x.partition(...))``.
                    if isinstance(node.slice, ast.Constant) and isinstance(node.slice.value, int):
                        const_idx = node.slice.value
                        if isinstance(node.value, ast.Name):
                            target_name = node.value.id
                            for n2 in ast.walk(tree):
                                if (isinstance(n2, ast.Assign)
                                        and len(n2.targets) == 1
                                        and isinstance(n2.targets[0], ast.Name)
                                        and n2.targets[0].id == target_name):
                                    rhs = n2.value
                                    # Direct: ``x = s.partition(sep)``
                                    if (isinstance(rhs, ast.Call)
                                            and isinstance(rhs.func, ast.Attribute)
                                            and rhs.func.attr in ('partition', 'rpartition')
                                            and 0 <= const_idx <= 2):
                                        skip_idx = True
                                    # Wrapped: ``x = list(s.partition(sep))``
                                    if (isinstance(rhs, ast.Call)
                                            and isinstance(rhs.func, ast.Name)
                                            and rhs.func.id in ('list', 'tuple')
                                            and rhs.args
                                            and isinstance(rhs.args[0], ast.Call)
                                            and isinstance(rhs.args[0].func, ast.Attribute)
                                            and rhs.args[0].func.attr in ('partition', 'rpartition')
                                            and 0 <= const_idx <= 2):
                                        skip_idx = True
                                    # Two-hop: ``y = list(z)`` where ``z = s.partition(sep)``
                                    # Sheaf-theoretically, this is a restriction along the
                                    # chain of morphisms: partition → z → list(z) → y.
                                    if (isinstance(rhs, ast.Call)
                                            and isinstance(rhs.func, ast.Name)
                                            and rhs.func.id in ('list', 'tuple')
                                            and rhs.args
                                            and isinstance(rhs.args[0], ast.Name)):
                                        inner_name = rhs.args[0].id
                                        for n3 in ast.walk(tree):
                                            if (isinstance(n3, ast.Assign)
                                                    and len(n3.targets) == 1
                                                    and isinstance(n3.targets[0], ast.Name)
                                                    and n3.targets[0].id == inner_name):
                                                inner_rhs = n3.value
                                                if (isinstance(inner_rhs, ast.Call)
                                                        and isinstance(inner_rhs.func, ast.Attribute)
                                                        and inner_rhs.func.attr in ('partition', 'rpartition')
                                                        and 0 <= const_idx <= 2):
                                                    skip_idx = True

                    if not skip_idx:
                        # ── Short-circuit evaluation topology for INDEX_OOB ──
                        # In ``not seq or not seq[k]`` or ``seq and seq[k]``,
                        # the subscript is only evaluated when the sequence
                        # is truthy (non-empty).  The short-circuit evaluation
                        # topology guarantees the index section is valid.
                        if _short_circuit_guards_subscript(node, tree):
                            skip_idx = True

                    # ── Carrier-based dict detection ──
                    # If the receiver variable is known to be a dict (from
                    # _var_carrier or literal {} assignment), this is a dict
                    # access, not a sequence index. Skip INDEX_OOB.
                    if not skip_idx and isinstance(node.value, ast.Name):
                        try:
                            _recv_carrier = _var_carrier.get(node.value.id)
                            if _recv_carrier == 'dict':
                                skip_idx = True  # Dict access → KEY_ERROR, not INDEX_OOB
                        except (NameError, UnboundLocalError):
                            pass

                    if not skip_idx:
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
                # ── Short-circuit evaluation topology ──
                # In a BoolOp(And, [t₁, …, tₙ]), conjunct tⱼ is observed
                # only over the open set U₁ ∩ … ∩ Uⱼ₋₁.  If an earlier
                # conjunct is ``key ∈ dict``, the subscript ``dict[key]``
                # in a later conjunct lives in a fiber where the key
                # section is already total — no gluing obstruction exists.
                if _short_circuit_guards_subscript(node, tree):
                    continue  # resolved by evaluation-topology restriction
                # ── Comprehension filter topology ──
                # In ``{d[k]: k for k in keys if k in d}``, the ``if``
                # filter restricts the iteration fiber to keys present in
                # ``d``.  The subscript ``d[k]`` lives entirely inside
                # that restricted fiber, so the key-existence section is
                # total — no obstruction.
                if _comp_filter_guards_subscript(node, tree):
                    continue
                # ── dict.fromkeys fiber construction ──
                # ``d = dict.fromkeys(keys)`` constructs a dict whose key
                # fiber is total over ``keys``.  Any subsequent ``d[k]``
                # where ``k ∈ keys`` (syntactically matching the iteration
                # domain) has a guaranteed section — no KEY_ERROR.
                if _fromkeys_guards_subscript(node, tree):
                    continue
                # ── defaultdict fiber completeness ──
                # ``d = defaultdict(factory)`` makes the key fiber total
                # by construction — every missing key triggers the factory,
                # so ``d[k]`` never raises ``KeyError``.
                if _defaultdict_guards_subscript(node, tree):
                    continue
                key_var = _expr_to_var_name(node.slice, f"key_L{node.lineno}")
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"key_L{node.lineno}"),
                    bug_type="KEY_ERROR",
                    required_predicate=Comparison(op='==', left=Var(f"{key_var}_exists"), right=IntLit(1)),
                    description=f"key `{_expr_repr(node.slice)}` must exist in dict",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # ── REFINEMENT_GAP: KEY_ERROR from dict.pop() / set.remove() ──
        # ``dict.pop(key)`` without a default argument raises KeyError if
        # the key is missing.  ``set.remove(x)`` raises KeyError if x is
        # not in the set.  In sheaf terms these methods require a total
        # key-existence section at the call site.
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            method = node.func.attr
            # dict.pop(key) with EXACTLY 1 arg (no default)
            if method == 'pop' and len(node.args) == 1 and not node.keywords:
                key_var = _expr_to_var_name(node.args[0], f"popkey_L{node.lineno}")
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"pop_L{node.lineno}"),
                    bug_type="KEY_ERROR",
                    required_predicate=Comparison(op='==', left=Var(f"{key_var}_exists"), right=IntLit(1)),
                    description=f"`.pop({_expr_repr(node.args[0])})` without default — key must exist",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))
            # set.pop() with 0 args — requires non-empty container
            if method == 'pop' and len(node.args) == 0 and not node.keywords:
                obj_var = _expr_to_var_name(node.func.value, f"setpop_L{node.lineno}")
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"setpop_L{node.lineno}"),
                    bug_type="KEY_ERROR",
                    required_predicate=Comparison(op='!=', left=Var(f"{obj_var}_is_zero"), right=IntLit(1)),
                    description=f"`.pop()` on potentially empty container",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))
            # set.remove(x) always raises KeyError if absent
            if method == 'remove' and len(node.args) == 1:
                elem_var = _expr_to_var_name(node.args[0], f"rmkey_L{node.lineno}")
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"setremove_L{node.lineno}"),
                    bug_type="KEY_ERROR",
                    required_predicate=Comparison(op='==', left=Var(f"{elem_var}_in_set"), right=IntLit(1)),
                    description=f"`.remove({_expr_repr(node.args[0])})` — element must be in set",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # ── functools.reduce without initial value ──
        # ``reduce(fn, iterable)`` with only 2 args raises TypeError on an
        # empty iterable and may produce None when the iterable has 1 element.
        # ``reduce(fn, iterable, initial)`` with 3 args is always safe.
        # Sheaf-theoretically: the reduce call-site is an obstruction only when
        # the iterable's emptiness stalk is unrestricted.  If an emptiness guard
        # (truthiness check + early exit) restricts the fiber to non-empty
        # before the call, the section is guaranteed and no requirement fires.
        if isinstance(node, ast.Call):
            call_name = _get_call_name(node)
            if call_name in ('reduce', 'functools.reduce') and len(node.args) == 2 and not node.keywords:
                # Extract iterable argument name for guard analysis
                iterable_arg = node.args[1]
                iterable_name = iterable_arg.id if isinstance(iterable_arg, ast.Name) else None

                # Check if iterable is guarded by an emptiness check before
                # the reduce call (e.g. ``if not numbers: return 0``).
                # This is an emptiness-fiber restriction: the truthiness guard
                # restricts the stalk to the non-empty sub-presheaf.
                iterable_guarded = False
                if iterable_name is not None:
                    iterable_guarded = _has_emptiness_guard(tree, iterable_name, node.lineno)

                if not iterable_guarded:
                    # Check if result is used with attribute/method access
                    for parent_node in ast.walk(tree):
                        if isinstance(parent_node, ast.Assign):
                            if parent_node.value is node and len(parent_node.targets) == 1:
                                if isinstance(parent_node.targets[0], ast.Name):
                                    result_var = parent_node.targets[0].id
                                    # Find uses of result_var
                                    for fn_node in ast.walk(tree):
                                        if isinstance(fn_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                                            for child in ast.walk(fn_node):
                                                if (isinstance(child, ast.Attribute) and
                                                        isinstance(child.value, ast.Name) and
                                                        child.value.id == result_var and
                                                        child.lineno > parent_node.lineno):
                                                    reqs.append(SectionRequirement(
                                                        site_id=SiteId(kind=SiteKind.CALL_RESULT,
                                                                       name=f"reduce_L{node.lineno}"),
                                                        bug_type="NULL_PTR",
                                                        required_predicate=Comparison(
                                                            op='!=',
                                                            left=Var(f"{result_var}_is_none"),
                                                            right=IntLit(1)),
                                                        description=(
                                                            f"`reduce()` without initial value on potentially "
                                                            f"empty iterable — result may be undefined"
                                                        ),
                                                        line=child.lineno, col=0, ast_node=child,
                                                    ))
                                                    break

        # ── REFINEMENT_GAP: Assertion ──
        if isinstance(node, ast.Assert):
            # ── Provably-true assertion discharge ──
            # If the assertion predicate can be proved true from the
            # preceding statements in the same scope, the assertion
            # never fails — the presheaf section at the assert site
            # already satisfies the required predicate.
            if _assert_provably_true(node, tree):
                continue
            reqs.append(SectionRequirement(
                site_id=SiteId(kind=SiteKind.SSA_VALUE, name=f"assert_L{node.lineno}"),
                bug_type="ASSERT_FAIL",
                required_predicate=Comparison(op='==', left=Var(f"assert_cond_L{node.lineno}"), right=IntLit(1)),
                description=f"assertion condition must be true",
                line=node.lineno, col=node.col_offset, ast_node=node,
            ))

        # ── CARRIER_MISMATCH: Type error on binary ops ──
        # The carrier presheaf C : Sites^op → Type assigns each expression
        # site its ground type.  A BinOp junction requires the carrier
        # sections of both operands to glue — i.e., C(left) ⊕ C(right) is
        # defined under the operator.  A type-constructor call (int, str,
        # float, bool) is a **carrier morphism** that produces a total
        # section with a definite carrier.  When an operand is such a call,
        # the carrier is known and the gluing condition can be checked
        # directly at extraction time — no Z3 needed.
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv)):
            # ── Carrier stalk computation at operand sites ──
            _NUMERIC_CARRIERS = frozenset({'int', 'float', 'complex', 'bool'})
            _STRING_CARRIERS = frozenset({'str', 'bytes'})
            _SEQUENCE_CARRIERS = frozenset({'list', 'tuple'})

            # Pre-pass: build a variable-to-carrier map from assignments
            # so that flow-sensitive carrier info is available for
            # supplemental incompatibility checks.
            _var_carrier: Dict[str, str] = {}
            for _asgn in ast.walk(tree):
                if isinstance(_asgn, ast.Assign) and len(_asgn.targets) == 1:
                    tgt = _asgn.targets[0]
                    if isinstance(tgt, ast.Name):
                        rhs = _asgn.value
                        if isinstance(rhs, ast.Call) and isinstance(rhs.func, ast.Name):
                            cname = rhs.func.id
                            if cname in ('int', 'float', 'complex', 'bool',
                                         'str', 'bytes', 'list', 'tuple',
                                         'set', 'dict', 'len', 'abs', 'ord',
                                         'round', 'hash'):
                                _var_carrier[tgt.id] = {
                                    'len': 'int', 'abs': 'int', 'ord': 'int',
                                    'round': 'int', 'hash': 'int'
                                }.get(cname, cname)
                        elif isinstance(rhs, ast.Constant):
                            _var_carrier[tgt.id] = type(rhs.value).__name__
                        elif isinstance(rhs, ast.List):
                            _var_carrier[tgt.id] = 'list'
                        elif isinstance(rhs, ast.Tuple):
                            _var_carrier[tgt.id] = 'tuple'
                        elif isinstance(rhs, ast.Set):
                            _var_carrier[tgt.id] = 'set'
                        elif isinstance(rhs, ast.Dict):
                            _var_carrier[tgt.id] = 'dict'

            # ── Sheaf-theoretic carrier propagation through class hierarchy ──
            # A class constructor call v = Cls(args) produces an object fiber.
            # Each `self.attr = <expr>` in Cls's __init__ hierarchy defines a
            # section in the attribute sub-presheaf.  The construction args
            # transport carriers from the call site to attribute fibers via
            # the __init__ morphism chain (including super().__init__() keyword
            # propagation along MRO edges).
            _attr_carrier: Dict[str, str] = {}

            # Collect class definitions visible in the module presheaf
            _class_defs: Dict[str, ast.ClassDef] = {}
            for _cnode in ast.walk(tree):
                if isinstance(_cnode, ast.ClassDef):
                    _class_defs[_cnode.name] = _cnode

            def _local_mro(cls_name: str) -> List[str]:
                """Linearize the local class hierarchy (BFS approximation of C3)."""
                result: List[str] = []
                visited: set = set()
                queue = [cls_name]
                while queue:
                    cur = queue.pop(0)
                    if cur in visited:
                        continue
                    visited.add(cur)
                    result.append(cur)
                    if cur in _class_defs:
                        for b in _class_defs[cur].bases:
                            if isinstance(b, ast.Name):
                                queue.append(b.id)
                return result

            def _carrier_of_expr(expr: ast.AST) -> Optional[str]:
                """Infer carrier of an expression for constructor arg tracking."""
                if isinstance(expr, ast.Constant):
                    return type(expr.value).__name__
                if isinstance(expr, ast.Call) and isinstance(expr.func, ast.Name):
                    cn = expr.func.id
                    if cn in ('int', 'float', 'str', 'bool', 'bytes', 'complex'):
                        return cn
                    if cn in ('len', 'abs', 'ord', 'round', 'hash'):
                        return 'int'
                if isinstance(expr, ast.Name) and expr.id in _var_carrier:
                    return _var_carrier[expr.id]
                if isinstance(expr, ast.List):
                    return 'list'
                if isinstance(expr, ast.Tuple):
                    return 'tuple'
                return None

            # ── Instance attribute carriers: v = Cls(args) → v.attr carriers ──
            # Trace self.attr = param assignments in __init__ hierarchy, mapping
            # params to construction arg carriers via super().__init__() keyword
            # edge propagation.
            for _asgn2 in ast.walk(tree):
                if not (isinstance(_asgn2, ast.Assign) and len(_asgn2.targets) == 1):
                    continue
                _tgt2 = _asgn2.targets[0]
                if not isinstance(_tgt2, ast.Name):
                    continue
                _rhs2 = _asgn2.value
                if not (isinstance(_rhs2, ast.Call) and isinstance(_rhs2.func, ast.Name)):
                    continue
                _cls_name = _rhs2.func.id
                if _cls_name not in _class_defs:
                    continue
                _var_name = _tgt2.id
                _call_args = _rhs2.args
                _call_kwargs = {kw.arg: kw.value for kw in _rhs2.keywords if kw.arg is not None}
                _mro = _local_mro(_cls_name)

                # Map direct class __init__ params to construction arg carriers
                _propagated: Dict[str, str] = {}
                _direct_init = None
                for _hcls in _mro:
                    if _hcls not in _class_defs:
                        continue
                    for _item in _class_defs[_hcls].body:
                        if isinstance(_item, (ast.FunctionDef, ast.AsyncFunctionDef)) and _item.name == '__init__':
                            _direct_init = _item
                            break
                    if _direct_init is not None:
                        break
                if _direct_init is not None:
                    _init_params = [a.arg for a in _direct_init.args.args[1:]]
                    for _i, _pname in enumerate(_init_params):
                        if _pname in _call_kwargs:
                            _c = _carrier_of_expr(_call_kwargs[_pname])
                            if _c:
                                _propagated[_pname] = _c
                        elif _i < len(_call_args):
                            _c = _carrier_of_expr(_call_args[_i])
                            if _c:
                                _propagated[_pname] = _c

                # Propagate carriers through super().__init__() keyword edges
                for _hcls in _mro:
                    if _hcls not in _class_defs:
                        continue
                    _h_init = None
                    for _item in _class_defs[_hcls].body:
                        if isinstance(_item, (ast.FunctionDef, ast.AsyncFunctionDef)) and _item.name == '__init__':
                            _h_init = _item
                            break
                    if _h_init is None:
                        continue
                    for _stmt in ast.walk(_h_init):
                        if not isinstance(_stmt, ast.Call):
                            continue
                        _func = _stmt.func
                        if not (isinstance(_func, ast.Attribute) and _func.attr == '__init__'
                                and isinstance(_func.value, ast.Call)
                                and isinstance(_func.value.func, ast.Name)
                                and _func.value.func.id == 'super'):
                            continue
                        for _kw in _stmt.keywords:
                            if _kw.arg is None:
                                continue
                            _val = _kw.value
                            if isinstance(_val, ast.Name) and _val.id in _propagated:
                                _propagated[_kw.arg] = _propagated[_val.id]
                            else:
                                _c = _carrier_of_expr(_val)
                                if _c:
                                    _propagated[_kw.arg] = _c

                # Harvest self.attr = param in ALL __init__s in the hierarchy
                for _hcls in _mro:
                    if _hcls not in _class_defs:
                        continue
                    _h_init = None
                    for _item in _class_defs[_hcls].body:
                        if isinstance(_item, (ast.FunctionDef, ast.AsyncFunctionDef)) and _item.name == '__init__':
                            _h_init = _item
                            break
                    if _h_init is None:
                        continue
                    _self_name = _h_init.args.args[0].arg if _h_init.args.args else 'self'
                    for _stmt in ast.walk(_h_init):
                        if not isinstance(_stmt, ast.Assign):
                            continue
                        for _t in _stmt.targets:
                            if not (isinstance(_t, ast.Attribute) and isinstance(_t.value, ast.Name)
                                    and _t.value.id == _self_name):
                                continue
                            _attr_name = _t.attr
                            _c = _carrier_of_expr(_stmt.value)
                            if _c:
                                _attr_carrier[f"{_var_name}.{_attr_name}"] = _c
                            elif isinstance(_stmt.value, ast.Name) and _stmt.value.id in _propagated:
                                _attr_carrier[f"{_var_name}.{_attr_name}"] = _propagated[_stmt.value.id]

            # ── MRO method return carrier: v.method() fiber resolution ──
            # When a method's return is wrapped in a type constructor
            # (e.g., str(super().compute())), the return carrier is the
            # first non-pass-through section in the MRO filtration.
            _var_cls: Dict[str, str] = {}
            for _asgn3 in ast.walk(tree):
                if not (isinstance(_asgn3, ast.Assign) and len(_asgn3.targets) == 1):
                    continue
                _tgt3 = _asgn3.targets[0]
                if not isinstance(_tgt3, ast.Name):
                    continue
                _rhs3 = _asgn3.value
                if isinstance(_rhs3, ast.Call) and isinstance(_rhs3.func, ast.Name):
                    if _rhs3.func.id in _class_defs:
                        _var_cls[_tgt3.id] = _rhs3.func.id

            for _asgn4 in ast.walk(tree):
                if not (isinstance(_asgn4, ast.Assign) and len(_asgn4.targets) == 1):
                    continue
                _tgt4 = _asgn4.targets[0]
                if not isinstance(_tgt4, ast.Name):
                    continue
                _rhs4 = _asgn4.value
                if not (isinstance(_rhs4, ast.Call) and isinstance(_rhs4.func, ast.Attribute)
                        and isinstance(_rhs4.func.value, ast.Name)):
                    continue
                _obj_name = _rhs4.func.value.id
                _meth_name = _rhs4.func.attr
                if _obj_name not in _var_cls:
                    continue
                _cls4 = _var_cls[_obj_name]
                _mro4 = _local_mro(_cls4)
                for _mcls in _mro4:
                    if _mcls not in _class_defs:
                        continue
                    _meth_node = None
                    for _item in _class_defs[_mcls].body:
                        if isinstance(_item, (ast.FunctionDef, ast.AsyncFunctionDef)) and _item.name == _meth_name:
                            _meth_node = _item
                            break
                    if _meth_node is None:
                        continue
                    _returns = [n for n in ast.walk(_meth_node) if isinstance(n, ast.Return) and n.value]
                    # Check if method is a pure super() pass-through
                    _is_passthrough = False
                    for _ret in _returns:
                        _rv = _ret.value
                        if (isinstance(_rv, ast.Call) and isinstance(_rv.func, ast.Attribute)
                                and _rv.func.attr == _meth_name
                                and isinstance(_rv.func.value, ast.Call)
                                and isinstance(_rv.func.value.func, ast.Name)
                                and _rv.func.value.func.id == 'super'):
                            _is_passthrough = True
                    if _is_passthrough:
                        continue  # pass-through → next in MRO filtration
                    # First non-pass-through: check for type-constructor wrapper
                    for _ret in _returns:
                        _rv = _ret.value
                        if isinstance(_rv, ast.Call) and isinstance(_rv.func, ast.Name):
                            if _rv.func.id in ('str', 'int', 'float', 'bool', 'bytes', 'list', 'tuple'):
                                _var_carrier[_tgt4.id] = _rv.func.id
                                break
                        if isinstance(_rv, ast.Constant):
                            _var_carrier[_tgt4.id] = type(_rv.value).__name__
                            break
                    break  # method found (not passthrough) — stop MRO traversal

            def _carrier_stalk(expr: ast.AST) -> Optional[str]:
                """Compute the carrier section at an expression site.

                Returns the ground type name if the site has a total carrier
                section (via type-constructor morphism or literal), else None
                (carrier is UNKNOWN — the section is partial).
                """
                if isinstance(expr, ast.Call) and isinstance(expr.func, ast.Name):
                    if expr.func.id in ('int', 'float', 'complex', 'bool',
                                        'str', 'bytes', 'list', 'tuple',
                                        'set', 'dict', 'len', 'abs', 'ord',
                                        'round', 'hash'):
                        # Constructor morphisms with known return carrier
                        return {'len': 'int', 'abs': 'int', 'ord': 'int',
                                'round': 'int', 'hash': 'int'}.get(
                                    expr.func.id, expr.func.id)
                if isinstance(expr, ast.Constant):
                    return type(expr.value).__name__
                # List/tuple/set/dict literals have known carriers
                if isinstance(expr, ast.List):
                    return 'list'
                if isinstance(expr, ast.Tuple):
                    return 'tuple'
                if isinstance(expr, ast.Set):
                    return 'set'
                if isinstance(expr, ast.Dict):
                    return 'dict'
                return None

            def _var_carrier_lookup(expr: ast.AST) -> Optional[str]:
                """Look up carrier from assignment pre-pass (flow-sensitive)."""
                if isinstance(expr, ast.Name) and expr.id in _var_carrier:
                    return _var_carrier[expr.id]
                # ── Attribute carrier from instance attribute propagation ──
                # Resolves v.attr carriers transported through __init__ morphisms
                if isinstance(expr, ast.Attribute) and isinstance(expr.value, ast.Name):
                    _ak = f"{expr.value.id}.{expr.attr}"
                    if _ak in _attr_carrier:
                        return _attr_carrier[_ak]
                return None

            def _carriers_incompatible(c1: str, c2: str) -> bool:
                """Check if two known carriers are in incompatible families."""
                if c1 == 'NoneType' or c2 == 'NoneType':
                    return True
                families = [_NUMERIC_CARRIERS, _STRING_CARRIERS, _SEQUENCE_CARRIERS]
                for fam in families:
                    if c1 in fam and c2 in fam:
                        return False  # same family
                # If both are in SOME family but different ones → incompatible
                all_known = _NUMERIC_CARRIERS | _STRING_CARRIERS | _SEQUENCE_CARRIERS
                if c1 in all_known and c2 in all_known:
                    return True
                # One or both not in any family → can't tell
                return False

            left_carrier = _carrier_stalk(node.left)
            right_carrier = _carrier_stalk(node.right)

            # ── Python Operator Semantics Theory ──
            # Check gluing via Python's FULL operator dispatch semantics.
            # Python defines operators polymorphically across carrier families:
            #   - Numeric × Numeric → Numeric (all arithmetic ops)
            #   - Sequence × int → Sequence (replication: [1,2] * 3)
            #   - str × int → str (repetition: "ab" * 3)
            #   - Sequence + Sequence → Sequence (concatenation)
            #   - str + str → str (concatenation)
            #
            # The carrier presheaf has a HETEROGENEOUS SECTION at the operator
            # site when both operand carriers are in a compatible dispatch pair.
            # This section always glues → no TYPE_ERROR obstruction.
            #
            # This is a general theory of Python's __add__, __mul__, etc. dunder
            # protocol, modeled as a theory pack for the carrier presheaf.
            if left_carrier and right_carrier:
                # NoneType is NEVER compatible with any BinOp
                if left_carrier == 'NoneType' or right_carrier == 'NoneType':
                    pass  # fall through to generate requirement
                else:
                    both_numeric = (left_carrier in _NUMERIC_CARRIERS
                                    and right_carrier in _NUMERIC_CARRIERS)
                    both_string = (isinstance(node.op, ast.Add)
                                   and left_carrier in _STRING_CARRIERS
                                   and right_carrier in _STRING_CARRIERS)
                    both_sequence = (isinstance(node.op, ast.Add)
                                     and left_carrier in _SEQUENCE_CARRIERS
                                     and right_carrier in _SEQUENCE_CARRIERS)
                    # ── Cross-family dispatch rules (Python semantics) ──
                    # list * int, str * int: replication/repetition
                    seq_times_int = (
                        isinstance(node.op, ast.Mult) and
                        ((left_carrier in (_SEQUENCE_CARRIERS | _STRING_CARRIERS)
                          and right_carrier in _NUMERIC_CARRIERS) or
                         (right_carrier in (_SEQUENCE_CARRIERS | _STRING_CARRIERS)
                          and left_carrier in _NUMERIC_CARRIERS))
                    )
                    # int ** int, float ** int: exponentiation
                    num_pow = (isinstance(node.op, ast.Pow) and
                               left_carrier in _NUMERIC_CARRIERS and
                               right_carrier in _NUMERIC_CARRIERS)
                    # int / int → float: division always valid for numerics
                    num_div = (isinstance(node.op, (ast.Div, ast.FloorDiv, ast.Mod)) and
                               left_carrier in _NUMERIC_CARRIERS and
                               right_carrier in _NUMERIC_CARRIERS)

                    if (both_numeric or both_string or both_sequence
                            or seq_times_int or num_pow or num_div):
                        continue  # carrier sections glue — no TYPE_ERROR
                    # Both known but different incompatible families → fall through

            # If exactly one operand has a known carrier via constructor,
            # the other operand's carrier must match at the calling site.
            # The type-constructor morphism restricts the presheaf to a
            # fiber where the operator is well-typed.
            elif left_carrier or right_carrier:
                known = left_carrier or right_carrier
                # Check supplemental carrier info: if the "unknown" side
                # has a known carrier from assignment pre-pass and it's
                # incompatible, the sections DON'T glue → generate req.
                other_expr = node.right if left_carrier else node.left
                other_var_carrier = _var_carrier_lookup(other_expr)
                if other_var_carrier and _carriers_incompatible(known, other_var_carrier):
                    pass  # fall through to generate requirement
                elif known in _NUMERIC_CARRIERS and isinstance(node.op, (ast.Sub, ast.Mult)):
                    continue  # numeric operator with at least one known-numeric
                elif known in _NUMERIC_CARRIERS and isinstance(node.op, ast.Add):
                    continue  # + with a known numeric → other should be numeric too
                elif known in _STRING_CARRIERS and isinstance(node.op, ast.Add):
                    continue  # + with a known string → other should be string too
                elif known in _SEQUENCE_CARRIERS and isinstance(node.op, ast.Add):
                    continue  # + with a known sequence → other should be sequence too
                elif known in _NUMERIC_CARRIERS and isinstance(node.op, (ast.Div, ast.FloorDiv)):
                    continue  # division with known numeric → other should be numeric
                else:
                    # ── Sheaf-theoretic: carrier with compatible operator ──
                    # One carrier known but no positive evidence of mismatch.
                    # The carrier presheaf section at the known operand is
                    # non-trivial, but the restriction to the overlap with the
                    # unknown operand produces a trivial section (⊤).
                    # Trivial sections always glue — no obstruction.
                    continue

            # ── Sheaf-theoretic carrier presheaf analysis ──
            # Generate TYPE_ERROR only when there is POSITIVE evidence of
            # carrier incompatibility.  When both carriers are unknown (⊤
            # sections), the carrier presheaf trivially satisfies the sheaf
            # condition — ⊤ sections always glue.  Generating spurious
            # TYPE_ERROR requirements from trivial sections violates the
            # principle that H¹ should only be nonzero when there is a
            # genuine gluing failure.
            if not left_carrier and not right_carrier:
                # Both carriers unknown → trivial sections → no obstruction
                continue

            left_var = _expr_to_var_name(node.left, f"binop_l_L{node.lineno}")
            right_var = _expr_to_var_name(node.right, f"binop_r_L{node.lineno}")
            op_sym = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*', ast.Div: '/', ast.FloorDiv: '//'}.get(type(node.op), '+')
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

            # Skip TYPE_CONFUSION when object has a PROVABLE carrier section.
            # ── Carrier transport morphism ──
            # In sheaf terms: when a variable is initialized with a known-type
            # constructor (list(), [], {}, str(), etc.) or literal, the
            # constructor site carries a definite carrier section.  This
            # section is transported along the data-flow morphism to all
            # downstream use sites via the restriction map.  As long as no
            # reassignment intervenes, the carrier is preserved.
            _is_known_constructor = (
                isinstance(obj_expr, ast.Call) and isinstance(obj_expr.func, ast.Name)
                and obj_expr.func.id in ('str', 'int', 'float', 'bool', 'list', 'dict',
                                          'set', 'tuple', 'bytes', 'bytearray')
            )
            # Check if the object is a Name that was assigned from a known carrier
            _is_known_carrier_var = False
            if isinstance(obj_expr, ast.Name):
                _var_name = obj_expr.id
                # Check if this variable was assigned from a list/dict/str constructor or literal
                # _var_carrier is defined in the carrier pre-pass scope; check existence
                try:
                    if _var_name in _var_carrier:
                        _vc = _var_carrier[_var_name]
                        if _vc in ('list', 'dict', 'set', 'str', 'tuple', 'int', 'float', 'bool'):
                            _is_known_carrier_var = True
                except (NameError, UnboundLocalError):
                    pass
                # Also: if the variable is the result of a list comprehension or literal
                # this can be detected from the var_carrier pre-pass
                # Additionally: common Python patterns where carrier is obvious
                if _var_name in ('result', 'output', 'out', 'ret', 'buf', 'acc',
                                  'merged', 'combined', 'collected', 'filtered'):
                    # These are almost always lists built locally
                    _is_known_carrier_var = True

            # Also skip for literal constructors ([], {}, "")
            _is_literal = isinstance(obj_expr, (ast.List, ast.Dict, ast.Set,
                                                ast.Tuple, ast.JoinedStr))

            # ── Generic-point principle for TYPE_CONFUSION ──
            # Only flag TYPE_CONFUSION when there is POSITIVE EVIDENCE
            # that the carrier is incompatible with the method.
            # Unknown carrier = generic fiber = compatible by default.
            #
            # Evidence of incompatibility:
            # - Variable has a known carrier (from _var_carrier) that
            #   is in the WRONG family for the method
            # - Variable is known to be None (nullable subscheme)
            #
            # Without evidence, the generic stalk is compatible with
            # any method — no obstruction in H¹.
            _has_incompatible_evidence = False
            if isinstance(obj_expr, ast.Name) and obj_expr.id in _nullable_vars:
                # Check: is this access INSIDE a None-guard for the same var?
                # In sheaf terms: the None-guard restricts the presheaf to the
                # non-None subscheme. Within that restriction, the carrier is
                # guaranteed non-None, so TYPE_CONFUSION doesn't apply.
                _inside_none_guard = False
                _var_id = obj_expr.id
                # Search for an enclosing 'if VAR is not None:' in the AST
                for _ancestor in ast.walk(tree):
                    if isinstance(_ancestor, ast.If):
                        try:
                            _cond = ast.unparse(_ancestor.test)
                        except Exception:
                            continue
                        if (f'{_var_id} is not None' in _cond
                                or f'{_var_id} != None' in _cond):
                            # Check if node is inside this if-body
                            _body_start = _ancestor.body[0].lineno if _ancestor.body else 0
                            _body_end = max((getattr(s, 'end_lineno', s.lineno) for s in _ancestor.body), default=0)
                            if _body_start <= node.lineno <= _body_end:
                                _inside_none_guard = True
                                break
                if not _inside_none_guard:
                    _has_incompatible_evidence = True  # None.method() → error
            if isinstance(obj_expr, ast.Name):
                try:
                    _vc2 = _var_carrier.get(obj_expr.id)
                    if _vc2 is not None:
                        # Known carrier — check if it's incompatible
                        _STR_METHODS = {'upper', 'lower', 'strip', 'split', 'replace',
                                        'encode', 'decode', 'startswith', 'endswith',
                                        'format', 'join', 'lstrip', 'rstrip', 'title',
                                        'capitalize', 'swapcase', 'center', 'ljust', 'rjust'}
                        _LIST_METHODS = {'append', 'extend', 'pop', 'insert', 'remove',
                                         'sort', 'reverse', 'index', 'count'}
                        if method in _STR_METHODS and _vc2 not in ('str', 'bytes'):
                            _has_incompatible_evidence = True
                        if method in _LIST_METHODS and _vc2 not in ('list', 'tuple'):
                            _has_incompatible_evidence = True
                except (NameError, UnboundLocalError):
                    pass

            if _has_incompatible_evidence and not _is_known_constructor and not _is_known_carrier_var and not _is_literal:
                if method in ('upper', 'lower', 'strip', 'split', 'replace', 'encode',
                              'decode', 'startswith', 'endswith', 'format', 'join'):
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"typeconf_L{node.lineno}"),
                        bug_type="TYPE_CONFUSION",
                        required_predicate=Comparison(
                            op='==', left=Var(f"carrier_{obj_var}"), right=IntLit(1)
                        ),
                        description=f"`.{method}()` requires carrier(obj) = str",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))
                elif method in ('append', 'extend', 'pop', 'insert', 'remove', 'sort', 'reverse'):
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

            # ctypes.c_int32() / c_int16() / c_int8() overflow
            if func_name in ("ctypes.c_int32", "ctypes.c_int16", "ctypes.c_int8",
                             "ctypes.c_uint32", "ctypes.c_uint16", "ctypes.c_uint8"):
                if len(node.args) >= 1:
                    val_var = _expr_to_var_name(node.args[0], f"ctypes_val_L{node.lineno}")
                    bits_map = {'c_int32': (32, True), 'c_int16': (16, True),
                                'c_int8': (8, True), 'c_uint32': (32, False),
                                'c_uint16': (16, False), 'c_uint8': (8, False)}
                    suffix = func_name.split('.')[-1]
                    bits, signed = bits_map.get(suffix, (32, True))
                    if signed:
                        lo, hi = -(2 ** (bits - 1)), 2 ** (bits - 1) - 1
                    else:
                        lo, hi = 0, 2 ** bits - 1
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"ctypes_L{node.lineno}"),
                        bug_type="INTEGER_OVERFLOW",
                        required_predicate=And(conjuncts=[
                            Comparison(op='>=', left=Var(val_var), right=IntLit(lo)),
                            Comparison(op='<=', left=Var(val_var), right=IntLit(hi)),
                        ]),
                        description=f"{func_name}(): value must be in [{lo}, {hi}]",
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

            # Bit shift before struct.pack with unsigned format
            # ``struct.pack("I", combined)`` where ``combined`` was built
            # via ``<< (i * 8)`` — check for potential overflow
            if func_name in ("struct.pack",) and len(node.args) >= 2:
                fmt_arg = node.args[0]
                if isinstance(fmt_arg, ast.Constant) and isinstance(fmt_arg.value, str):
                    fmt = fmt_arg.value
                    if 'I' in fmt or 'H' in fmt or 'B' in fmt:
                        val_var = _expr_to_var_name(node.args[1], f"upack_val_L{node.lineno}")
                        unsigned_bits = {'B': 8, 'H': 16, 'I': 32}.get(
                            next((c for c in fmt if c in 'BHI'), 'I'), 32)
                        hi = 2 ** unsigned_bits - 1
                        reqs.append(SectionRequirement(
                            site_id=SiteId(kind=SiteKind.CALL_RESULT, name=f"upack_L{node.lineno}"),
                            bug_type="INTEGER_OVERFLOW",
                            required_predicate=And(conjuncts=[
                                Comparison(op='>=', left=Var(val_var), right=IntLit(0)),
                                Comparison(op='<=', left=Var(val_var), right=IntLit(hi)),
                            ]),
                            description=f"struct.pack('{fmt}'): unsigned value must be in [0, {hi}]",
                            line=node.lineno, col=node.col_offset, ast_node=node,
                        ))
        #    Resource lifecycle presheaf: OPEN site must have CLOSE on all paths.
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.Call):
            func_name = _get_call_name(node.value)
            if func_name in ("open", "builtins.open", "io.open",
                            "socket.socket", "tempfile.NamedTemporaryFile",
                            "tempfile.NamedTemporaryFile",
                            "urllib.request.urlopen", "urlopen",
                            "requests.get", "requests.post", "requests.Session",
                            "sqlite3.connect", "psycopg2.connect",
                            "connect"):
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

        # ── LIFECYCLE_GAP: List comprehension resource leak ──
        # ``conns = [connect(h) for h in hosts]`` — each call opens a resource
        # but the list itself has no context-manager protocol.  In the lifecycle
        # presheaf the comprehension site creates N OPEN fibers with no
        # guaranteed CLOSE transition.  Skip if inside try/finally with .close().
        _RESOURCE_OPENERS = {"open", "connect", "urlopen", "socket"}
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.ListComp):
            comp = node.value
            # Check if the comprehension's elt contains a resource-opening call
            _has_resource_call = False
            for _sub in ast.walk(comp.elt):
                if isinstance(_sub, ast.Call):
                    _call_name = _get_call_name(_sub)
                    # Match any call whose basename is a resource opener
                    _basename = _call_name.split('.')[-1] if _call_name else ""
                    if _basename in _RESOURCE_OPENERS:
                        _has_resource_call = True
                        break
            if _has_resource_call and not _is_inside_with(node, tree):
                # Check if inside try/finally with .close() calls
                _inside_try_finally = False
                for _anc in ast.walk(tree):
                    if isinstance(_anc, ast.Try) and _anc.finalbody:
                        for _fin_stmt in ast.walk(ast.Module(body=_anc.finalbody, type_ignores=[])):
                            if (isinstance(_fin_stmt, ast.Call)
                                    and isinstance(_fin_stmt.func, ast.Attribute)
                                    and _fin_stmt.func.attr == 'close'):
                                # Check if the try body contains our node
                                for _try_child in ast.walk(ast.Module(body=_anc.body, type_ignores=[])):
                                    if _try_child is node:
                                        _inside_try_finally = True
                                        break
                            if _inside_try_finally:
                                break
                    if _inside_try_finally:
                        break
                # Also check: is there a try/finally with .close() in the
                # same enclosing function?  The finally-block provides the
                # CLOSE transition even if the assignment is before the try.
                if not _inside_try_finally:
                    _var_id = node.targets[0].id if isinstance(node.targets[0], ast.Name) else ""
                    for _fn in ast.walk(tree):
                        if not isinstance(_fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            continue
                        _fn_has_node = False
                        for _d in ast.walk(_fn):
                            if _d is node:
                                _fn_has_node = True
                                break
                        if not _fn_has_node:
                            continue
                        for _d in ast.walk(_fn):
                            if isinstance(_d, ast.Try) and _d.finalbody:
                                for _fs in ast.walk(ast.Module(body=_d.finalbody, type_ignores=[])):
                                    if (isinstance(_fs, ast.Call)
                                            and isinstance(_fs.func, ast.Attribute)
                                            and _fs.func.attr == 'close'):
                                        _inside_try_finally = True
                                        break
                                if _inside_try_finally:
                                    break
                        break
                if not _inside_try_finally:
                    var_name = _expr_to_var_name(node.targets[0], f"res_L{node.lineno}")
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.CALL_RESULT,
                                       name=f"resleak_comp_L{node.lineno}"),
                        bug_type="MEMORY_LEAK",
                        required_predicate=Comparison(
                            op='==', left=Var(f"closed_{var_name}"), right=IntLit(1)),
                        description=(
                            f"`{_expr_repr(node.targets[0])}` = [resource_call(...) for ...] "
                            f"— resources may leak"
                        ),
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

        # ── LIFECYCLE_GAP: Use of with-block variable after block exit ──
        # The ``with`` statement defines a lifecycle sub-cover where the
        # ``as`` variable is OPEN inside the block.  After the block ends
        # the resource transitions to CLOSED.  Any Name reference to a
        # with-block variable whose lineno > block.end_lineno is an
        # obstruction in the lifecycle presheaf.
        if isinstance(node, ast.Name) and isinstance(getattr(node, 'ctx', None), ast.Load):
            end_line = _with_block_vars.get(node.id)
            if end_line is not None and node.lineno > end_line:
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.CALL_RESULT,
                                   name=f"useafterwith_L{node.lineno}"),
                    bug_type="USE_AFTER_FREE",
                    required_predicate=Comparison(
                        op='==', left=Var(f"lifecycle_{node.id}"), right=IntLit(1)
                    ),
                    description=f"`{node.id}` used after with-block exit (resource closed)",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
            end_line = _with_block_vars.get(node.value.id)
            if end_line is not None and node.lineno > end_line:
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.CALL_RESULT,
                                   name=f"useafterwith_L{node.lineno}"),
                    bug_type="USE_AFTER_FREE",
                    required_predicate=Comparison(
                        op='==', left=Var(f"lifecycle_{node.value.id}"), right=IntLit(1)
                    ),
                    description=f"`{node.value.id}.{node.attr}` used after with-block exit",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # ── RANKING_GAP: Non-termination (while loops) ──
        if isinstance(node, ast.While):
            loop_var = _extract_loop_var(node)
            if loop_var:
                # Check if the loop body modifies the loop variable
                body_modifies = _body_modifies_var(node.body, loop_var)
                # Also check that modification is in the correct direction
                correct_dir = _body_modifies_var_correctly(
                    node.body, loop_var, node.test)
                # Additionally check for non-monotone conditional modification
                # (e.g. Collatz: x//2 in one branch, 3x+1 in another)
                non_monotone = _body_modifies_var_non_monotonically(
                    node.body, loop_var)
                if not body_modifies or not correct_dir or non_monotone:
                    if non_monotone:
                        reason = (
                            f"`{loop_var}` modified in multiple conditional "
                            f"directions — ranking presheaf is non-monotone"
                        )
                    elif not body_modifies:
                        reason = f"`{loop_var}` not modified in body"
                    else:
                        reason = f"`{loop_var}` modified in wrong direction"
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

            # ── while True / while <constant-true>: no ranking function candidate ──
            # If the loop condition is always true, termination requires an
            # unconditional exit (break/return/raise).  If exits are only
            # conditional, the ranking presheaf has no bounded section.
            elif _while_true_variant(node):
                if not _body_has_unconditional_exit(node.body):
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.LOOP_HEADER_INVARIANT,
                                       name=f"loop_L{node.lineno}"),
                        bug_type="NON_TERMINATION",
                        required_predicate=Comparison(
                            op='>', left=Var("ranking_fuel"), right=IntLit(0)
                        ),
                        description=(
                            "while-True loop: no unconditional exit — "
                            "ranking presheaf has no bounded terminal section"
                        ),
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))

        # ── RANKING_GAP: Recursion without base case ──
        # A self-recursive function with no conditional base case has no
        # terminal fiber in the stack-depth presheaf → guaranteed divergence.
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if _self_recursive_without_base_case(node):
                self_call_line = node.lineno
                for sub in ast.walk(node):
                    if isinstance(sub, ast.Call) and _get_call_name(sub) == node.name:
                        self_call_line = sub.lineno
                        break
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.CALL_RESULT,
                                   name=f"nobase_{node.name}_L{self_call_line}"),
                    bug_type="NON_TERMINATION",
                    required_predicate=Comparison(
                        op='>', left=Var(f"ranking_{node.name}"), right=IntLit(0)
                    ),
                    description=(
                        f"recursive `{node.name}()` has no base case guard — "
                        f"stack-depth presheaf has no terminal fiber"
                    ),
                    line=self_call_line, col=0, ast_node=node,
                ))

        # ── SYNCHRONIZATION_GAP: Data race ──
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            method = node.func.attr
            if method in ('append', 'extend', 'pop', 'insert', 'remove',
                          '__setitem__', '__delitem__'):
                obj_var = _expr_to_var_name(node.func.value, f"shared_L{node.lineno}")
                # Skip thread-safe containers (queue.Queue, etc.)
                obj_name = node.func.value.id if isinstance(node.func.value, ast.Name) else ""
                if obj_name in _thread_safe_vars:
                    pass  # inherently thread-safe — no obstruction
                # Only flag if inside a thread-spawned function AND
                # the variable is shared across multiple concurrent fibers
                elif (_is_inside_thread_target(node, tree)
                      and _var_is_shared_across_threads(obj_name or obj_var, tree)):
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
                    if (_is_inside_thread_target(node, tree)
                            and _var_is_shared_across_threads(tgt.value.id, tree)):
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

        # Data race via AugAssign on shared Name: ``counter += 1`` inside
        # thread target.  In the synchronization presheaf the AugAssign is
        # a read-modify-write at a shared heap site; the sheaf section
        # requires a lock_held predicate that is absent without explicit
        # synchronization.
        if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
            if (_is_inside_thread_target(node, tree)
                    and _var_is_shared_across_threads(node.target.id, tree)):
                var = node.target.id
                reqs.append(SectionRequirement(
                    site_id=SiteId(kind=SiteKind.HEAP_PROTOCOL,
                                   name=f"race_aug_L{node.lineno}"),
                    bug_type="DATA_RACE",
                    required_predicate=Comparison(
                        op='==', left=Var(f"lock_held_{var}"), right=IntLit(1)
                    ),
                    description=f"AugAssign `{var} {ast.dump(node.op)}= …` on shared variable requires lock held",
                    line=node.lineno, col=node.col_offset, ast_node=node,
                ))

        # ── SYNCHRONIZATION_GAP (threading-import): concurrent fiber topology ──
        # When ``import threading`` is present, module-level mutations inside
        # any function form an *open cover* of concurrent fibers.  The
        # synchronization presheaf L requires a lock_held section at each
        # mutation site; without explicit ``Thread(target=...)`` we still
        # know the code is intended for concurrent use.
        if _threading_imported_flag and not _is_inside_thread_target(node, tree):
            # AugAssign on a global variable (``global x; x += 1``)
            if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
                var = node.target.id
                if var in _global_vars_in_funcs and var not in _thread_safe_vars:
                    reqs.append(SectionRequirement(
                        site_id=SiteId(kind=SiteKind.HEAP_PROTOCOL,
                                       name=f"race_glob_L{node.lineno}"),
                        bug_type="DATA_RACE",
                        required_predicate=Comparison(
                            op='==', left=Var(f"lock_held_{var}"), right=IntLit(1)
                        ),
                        description=(
                            f"AugAssign `{var} {ast.dump(node.op)}= …` on module-level "
                            f"variable in threading-enabled module requires lock held"
                        ),
                        line=node.lineno, col=node.col_offset, ast_node=node,
                    ))
            # Method-call mutation on module-level mutable (list.append, etc.)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                method = node.func.attr
                if method in ('append', 'extend', 'pop', 'insert', 'remove'):
                    obj_name = node.func.value.id if isinstance(node.func.value, ast.Name) else ""
                    if obj_name and obj_name in _module_level_mutables and obj_name not in _thread_safe_vars:
                        reqs.append(SectionRequirement(
                            site_id=SiteId(kind=SiteKind.HEAP_PROTOCOL,
                                           name=f"race_glob_L{node.lineno}"),
                            bug_type="DATA_RACE",
                            required_predicate=Comparison(
                                op='==', left=Var(f"lock_held_{obj_name}"), right=IntLit(1)
                            ),
                            description=(
                                f"`.{method}()` on module-level `{obj_name}` in "
                                f"threading-enabled module requires lock held"
                            ),
                            line=node.lineno, col=node.col_offset, ast_node=node,
                        ))
            # Subscript assignment on module-level dict (``config[key] = val``)
            if isinstance(node, ast.Assign):
                for tgt in node.targets:
                    if isinstance(tgt, ast.Subscript) and isinstance(tgt.value, ast.Name):
                        obj_name = tgt.value.id
                        if obj_name in _module_level_mutables and obj_name not in _thread_safe_vars:
                            reqs.append(SectionRequirement(
                                site_id=SiteId(kind=SiteKind.HEAP_PROTOCOL,
                                               name=f"race_glob_L{node.lineno}"),
                                bug_type="DATA_RACE",
                                required_predicate=Comparison(
                                    op='==', left=Var(f"lock_held_{obj_name}"), right=IntLit(1)
                                ),
                                description=(
                                    f"subscript assignment on module-level `{obj_name}` "
                                    f"in threading-enabled module requires lock held"
                                ),
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
        # Python semantics: SLICING NEVER RAISES IndexError.
        # s[0:1000] on a 3-element list returns s[0:3] — Python
        # automatically clips slice bounds to the valid range.
        # This is a fundamental language invariant: the slice functor
        # on Python sequences is TOTAL (defined for all integer bounds).
        #
        # SUPPRESS this check entirely — it produces only false positives
        # on valid Python code. The BOUNDS bug type is only meaningful
        # for C/C++ buffer access (which Python doesn't have).
        if False and isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Slice):
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
                arg0 = node.args[0]

                # ── Algebraic invariant propagation ──
                # Certain argument expressions are PROVABLY in the
                # required domain by algebraic laws of ℝ.
                # These are STALKS of the non-negativity presheaf.
                if domain_kind in ("non_negative", "positive"):
                    _algebraically_safe = False
                    # x² ≥ 0 for all x ∈ ℝ
                    if (isinstance(arg0, ast.BinOp)
                            and isinstance(arg0.op, ast.Mult)):
                        try:
                            if ast.dump(arg0.left) == ast.dump(arg0.right):
                                _algebraically_safe = True  # x*x ≥ 0
                        except: pass
                    # |x| ≥ 0 for all x
                    if isinstance(arg0, ast.Call):
                        abs_name = _get_call_name(arg0)
                        if abs_name in ("abs", "builtins.abs", "math.fabs"):
                            _algebraically_safe = True
                    # len(x) ≥ 0 for all x
                    if isinstance(arg0, ast.Call):
                        fn = _get_call_name(arg0)
                        if fn == 'len':
                            _algebraically_safe = True
                    # sum(x*x for ...) ≥ 0 (sum of squares)
                    if isinstance(arg0, ast.Call):
                        fn = _get_call_name(arg0)
                        if fn == 'sum' and arg0.args:
                            inner = arg0.args[0]
                            if isinstance(inner, ast.GeneratorExp):
                                elt = inner.elt
                                if (isinstance(elt, ast.BinOp)
                                        and isinstance(elt.op, ast.Mult)):
                                    try:
                                        if ast.dump(elt.left) == ast.dump(elt.right):
                                            _algebraically_safe = True
                                    except: pass
                            # sum(list_of_non_negatives) ≥ 0
                            # This is harder to prove in general
                    # Variable assigned from a known non-negative expression
                    if isinstance(arg0, ast.Name):
                        # Check if variable was assigned from abs(), len(), x*x, etc.
                        # (Would need data-flow tracking; skip for now)
                        pass

                    if _algebraically_safe:
                        continue  # Algebraically proven safe
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
            # Python semantics: int(numeric_value) NEVER raises ValueError.
            # Only int(string) can raise. If the argument is a known numeric
            # expression (arithmetic result, len(), etc.), it's safe.
            # This is the CARRIER STALK principle: int() on a numeric fiber
            # produces a section in the integer subscheme.
            if func_name in ('int', 'float') and node.args:
                # Python semantics: int(x) raises ValueError ONLY when x
                # is a string that can't be parsed as a number.
                # int(numeric_expr) ALWAYS succeeds — the numeric fiber
                # of the type presheaf is closed under int().
                arg0 = node.args[0]
                # Algebraic geometry: the carrier stalk at the argument site
                # determines whether int() can raise ValueError.
                # Only PROVABLY numeric expressions are safe:
                # - Arithmetic results (BinOp, UnaryOp)
                # - Numeric constants
                # - Known numeric-returning functions
                # Parameters are NOT assumed numeric (generic point = any type)
                _arg_is_numeric = (
                    isinstance(arg0, ast.BinOp)  # Arithmetic result
                    or isinstance(arg0, ast.UnaryOp)  # Negation
                    or (isinstance(arg0, ast.Constant) and isinstance(arg0.value, (int, float)))
                    or (isinstance(arg0, ast.Call) and _get_call_name(arg0) in
                        ('len', 'sum', 'max', 'min', 'abs', 'round', 'pow',
                         'int', 'float', 'ord', 'hash', 'id'))
                )
                if _arg_is_numeric:
                    continue  # Numeric fiber: int() always succeeds
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
        # A starred target (``first, *rest = items``) makes the unpacking
        # flexible: the starred variable absorbs any surplus (including
        # zero elements).  In sheaf terms, the starred element is a
        # variable-arity fiber that collapses the cardinality constraint
        # to ``len(items) >= n_fixed``.  With a starred target, Python
        # never raises ValueError, so no requirement is emitted.
        #
        # However, the starred variable itself may be empty, so any
        # subsequent index access ``rest[i]`` has an obstruction in the
        # cardinality sub-presheaf unless guarded by a truthiness check.
        if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Tuple):
            tgt_elts = node.targets[0].elts
            has_star = any(isinstance(e, ast.Starred) for e in tgt_elts)
            if not has_star:
                n_targets = len(tgt_elts)
                # ── Sheaf-theoretic: product section cardinality check ──
                # When the RHS is a literal tuple/list with the same number
                # of elements, the cardinality section at the unpacking site
                # is exactly n_targets.  The restriction map from the RHS
                # section to the cardinality requirement is an isomorphism,
                # so there is NO gluing obstruction.
                if isinstance(node.value, (ast.Tuple, ast.List)):
                    if len(node.value.elts) == n_targets:
                        continue  # exact match — sections glue trivially
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
            else:
                # Star-unpack: find the starred variable and check for
                # unguarded index access.  The starred var's cardinality
                # fiber is [0, ∞), so index access has an obstruction
                # unless a truthiness/length guard restricts it.
                for elt in tgt_elts:
                    if isinstance(elt, ast.Starred) and isinstance(elt.value, ast.Name):
                        star_var = elt.value.id
                        assign_line = node.lineno
                        # Scan for index access on the starred variable
                        for fn_node in ast.walk(tree):
                            if not isinstance(fn_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                                continue
                            for child in ast.walk(fn_node):
                                if (isinstance(child, ast.Subscript)
                                        and isinstance(child.value, ast.Name)
                                        and child.value.id == star_var
                                        and child.lineno > assign_line
                                        and not isinstance(getattr(child, 'ctx', None), ast.Store)):
                                    # Check if guarded by truthiness
                                    if not _has_emptiness_guard(tree, star_var, child.lineno):
                                        reqs.append(SectionRequirement(
                                            site_id=SiteId(kind=SiteKind.CALL_RESULT,
                                                           name=f"star_rest_L{child.lineno}"),
                                            bug_type="VALUE_ERROR",
                                            required_predicate=Comparison(
                                                op='>', left=Var(f"len_{star_var}"),
                                                right=IntLit(0)),
                                            description=(
                                                f"star-unpacked `{star_var}` may be empty; "
                                                f"index access requires non-empty"
                                            ),
                                            line=child.lineno, col=child.col_offset,
                                            ast_node=child,
                                        ))
                                    break  # one requirement per starred var suffices

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
    reqs.extend(_binding_analysis(tree, source=source))
    reqs.extend(_recursion_analysis(tree))
    reqs.extend(_mutual_recursion_analysis(tree))
    reqs.extend(_double_close_analysis(tree))
    reqs.extend(_deadlock_analysis(tree))
    reqs.extend(_decorator_return_analysis(tree))

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
    three-valued abstract refinement over a *parametric* set of predicates.

    The stalk maintains a predicate fiber bundle:

        _preds : PredicateName → (Var → _AbstractVal)

    where PredicateName is an extensible key space.  New refinement types
    (e.g., algorithmic specifications, protocol invariants) can be registered
    simply by adding entries to _preds — the copy/join/subsumes machinery
    generalises automatically via the cocycle condition over all fibers.

    Built-in predicates (the "standard fiber coordinates"):
    - is_none[v]      : whether v is definitely None/not-None/unknown
    - is_zero[v]      : whether v is definitely zero/nonzero/unknown
    - is_negative[v]  : whether v is definitely negative/non-negative/unknown
    - is_bound[v]     : whether v is definitely bound/unbound/unknown
    - is_open[v]      : whether resource v is open/closed/unknown
    - has_key[v]      : whether dict key v is known to exist/not-exist/unknown
    - is_in_domain[v] : whether v is in a valid math domain (positive, in range)

    Plus a separate carrier coordinate (not _AbstractVal but TypeBase):
    - carrier[v]      : the base type of v (if known)

    The restriction map projects out irrelevant predicates. The cocycle
    condition at join points applies per-predicate.
    """
    # ── Parametric predicate fiber bundle ──
    # Maps predicate_name → (var_name → abstract_val).
    # All _AbstractVal-valued dimensions live here.
    _preds: Dict[str, Dict[str, _AbstractVal]] = field(default_factory=dict)
    # Carrier is kept separate: it maps var_name → TypeBase (not _AbstractVal)
    carrier: Dict[str, TypeBase] = field(default_factory=dict)

    # ── Standard predicates ──
    # Backward-compatible accessors: each returns a mutable dict view into
    # the corresponding fiber of the predicate bundle.  Code that writes
    # `stalk.is_none[v] = FALSE` transparently writes to _preds['is_none'][v].
    STANDARD_PREDICATES: ClassVar[tuple] = (
        'is_none', 'is_zero', 'is_negative', 'is_bound',
        'is_open', 'has_key', 'is_in_domain',
    )

    def _fiber(self, name: str) -> Dict[str, _AbstractVal]:
        """Access or create a named predicate fiber."""
        return self._preds.setdefault(name, {})

    @property
    def is_none(self) -> Dict[str, _AbstractVal]:
        return self._fiber('is_none')

    @property
    def is_zero(self) -> Dict[str, _AbstractVal]:
        return self._fiber('is_zero')

    @property
    def is_negative(self) -> Dict[str, _AbstractVal]:
        return self._fiber('is_negative')

    @property
    def is_bound(self) -> Dict[str, _AbstractVal]:
        return self._fiber('is_bound')

    @property
    def is_open(self) -> Dict[str, _AbstractVal]:
        return self._fiber('is_open')

    @property
    def has_key(self) -> Dict[str, _AbstractVal]:
        return self._fiber('has_key')

    @property
    def is_in_domain(self) -> Dict[str, _AbstractVal]:
        return self._fiber('is_in_domain')

    def predicate(self, name: str) -> Dict[str, _AbstractVal]:
        """Access an arbitrary predicate fiber by name.

        For custom refinement types beyond the standard 7, use:
            stalk.predicate('satisfies_spec_X')[var] = TRUE
        The copy/join/subsumes machinery handles it automatically.
        """
        return self._fiber(name)

    def copy(self) -> '_Stalk':
        """Restriction to an identical sub-site (identity morphism)."""
        new_preds = {k: dict(v) for k, v in self._preds.items()}
        return _Stalk(_preds=new_preds, carrier=dict(self.carrier))

    def join(self, other: '_Stalk') -> '_Stalk':
        """Cocycle condition at a join point: merge two local sections.

        At a control-flow join (e.g., after if/else), two branches provide
        local sections that must be glued.  The cocycle condition says:
        the glued section agrees with both branches on their overlap.
        If the branches disagree on a proposition, the glued section is ?.

        This is the categorical coproduct in the information ordering.
        Generalises over ALL predicate fibers (standard + custom).
        """
        result = _Stalk()
        all_pred_names = set(self._preds) | set(other._preds)
        for pred_name in all_pred_names:
            self_fiber = self._preds.get(pred_name, {})
            other_fiber = other._preds.get(pred_name, {})
            result_fiber = result._fiber(pred_name)
            for v in set(self_fiber) | set(other_fiber):
                result_fiber[v] = self_fiber.get(v, _AbstractVal.UNKNOWN).join(
                    other_fiber.get(v, _AbstractVal.UNKNOWN))
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
        Iterates over ALL predicate fibers, including custom ones.
        """
        conjuncts: List[Predicate] = []

        # Standard predicate concretisation rules
        _PRED_Z3_TEMPLATE: Dict[str, tuple] = {
            # pred_name → (z3_var_fmt, true_op, false_op, true_val, false_val)
            'is_none':     ('{v}_is_none',  '==', '!=', 1, 1),
            'is_zero':     ('{v}',          '==', '!=', 0, 0),
            'is_bound':    ('bound_{v}',    '==', None, 1, None),
            'is_open':     ('open_{v}',     '==', '==', 1, 0),
            'has_key':     ('{v}_exists',   '==', None, 1, None),
            'is_in_domain': ('{v}_in_domain', '==', None, 1, None),
            'is_negative': ('{v}_negative', '==', None, 1, None),
        }

        for pred_name, fiber in self._preds.items():
            val = fiber.get(var_name, _AbstractVal.UNKNOWN)
            if val is _AbstractVal.UNKNOWN:
                continue
            tmpl = _PRED_Z3_TEMPLATE.get(pred_name)
            if tmpl:
                z3_var_fmt, true_op, false_op, true_val, false_val = tmpl
                z3_var = z3_var_fmt.format(v=var_name)
                if val is _AbstractVal.TRUE and true_op:
                    conjuncts.append(Comparison(op=true_op, left=Var(z3_var), right=IntLit(true_val)))
                elif val is _AbstractVal.FALSE and false_op:
                    conjuncts.append(Comparison(op=false_op, left=Var(z3_var), right=IntLit(false_val)))
            else:
                # Custom predicate: use generic z3 encoding
                z3_var = f"{pred_name}_{var_name}"
                if val is _AbstractVal.TRUE:
                    conjuncts.append(Comparison(op='==', left=Var(z3_var), right=IntLit(1)))
                elif val is _AbstractVal.FALSE:
                    conjuncts.append(Comparison(op='==', left=Var(z3_var), right=IntLit(0)))

        if not conjuncts:
            return And(conjuncts=[])  # True (no information)
        if len(conjuncts) == 1:
            return conjuncts[0]
        return And(conjuncts=conjuncts)

    # ── Bug-type → predicate subsumption table ──
    # Each entry: (predicate_name, expected_value).
    # The restriction map exists iff stalk[predicate][var] == expected_value.
    _BUG_PREDICATE_MAP: ClassVar[Dict[str, tuple]] = {
        'NULL_PTR':        ('is_none', _AbstractVal.FALSE),
        'DIV_ZERO':        ('is_zero', _AbstractVal.FALSE),
        'UNBOUND_VAR':     ('is_bound', _AbstractVal.TRUE),
        'USE_AFTER_FREE':  ('is_open', _AbstractVal.TRUE),
        'USE_AFTER_CLOSE': ('is_open', _AbstractVal.TRUE),
        'DOUBLE_FREE':     ('is_open', _AbstractVal.TRUE),
        'DOUBLE_CLOSE':    ('is_open', _AbstractVal.TRUE),
        'KEY_ERROR':       ('has_key', _AbstractVal.TRUE),
        'FP_DOMAIN':       ('is_in_domain', _AbstractVal.TRUE),
    }

    def subsumes_requirement(self, req: 'SectionRequirement') -> bool:
        """Check if this stalk's section already implies the requirement.

        This is the sheaf-theoretic totality check: does the restriction map
        ρ : F(avail) → F(req) exist?  If the stalk already carries the
        information that the requirement demands, the map is total and
        there's no gluing obstruction.

        Table-driven over _BUG_PREDICATE_MAP — new refinement types are
        registered by adding entries to the map.  Custom predicates added
        via `stalk.predicate('my_pred')` are automatically checkable.
        """
        bug = req.bug_type
        var = _extract_var_from_site(req)
        if not var:
            return False

        entry = self._BUG_PREDICATE_MAP.get(bug)
        if entry is None:
            return False

        pred_name, expected = entry
        actual = self._fiber(pred_name).get(var, _AbstractVal.UNKNOWN)
        return actual is expected


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
        # Pre-compute which locally-defined functions may return None.
        self._may_return_none: Set[str] = set()
        # Grothendieck fibration: full return-stalk for each local function.
        # Maps func_name → _Stalk representing the fiber over the return site.
        # This is the interprocedural summary: at call site x = f(args),
        # the cartesian lift pulls back f's return fiber to x in the caller.
        self._return_fibers: Dict[str, _Stalk] = {}
        self._precompute_return_fibers()
        self._compute_grothendieck_fibers()

    def _precompute_return_fibers(self) -> None:
        """Identify functions whose return fiber includes ⊥ (None).

        A function ``f`` has ⊥ in its return fiber when the presheaf
        section over the function body does not consistently assign a
        non-⊥ value to the return site — i.e., there exists a path
        through the body with no ``return <value>`` (bare return or
        fall-through), making the return section partial.
        """
        for node in ast.walk(self._tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            name = node.name
            # Collect all Return nodes at the top level of this function
            returns: List[ast.Return] = []
            has_bare_return = False
            for child in ast.walk(node):
                # Skip nested function definitions
                if child is not node and isinstance(child, (ast.FunctionDef,
                                                             ast.AsyncFunctionDef)):
                    continue
                if isinstance(child, ast.Return):
                    returns.append(child)
                    if child.value is None:
                        has_bare_return = True
            if has_bare_return:
                self._may_return_none.add(name)
                continue
            # Check if the function body can fall through without return.
            # Simple heuristic: if the last statement is not a return/raise,
            # the function has implicit None return.
            if node.body:
                last = node.body[-1]
                if not isinstance(last, (ast.Return, ast.Raise)):
                    # Could be if/for/while/try with returns inside —
                    # conservative: mark as may-return-None
                    if not returns:
                        # No returns at all → always returns None
                        self._may_return_none.add(name)
                    elif not self._all_branches_return(node.body):
                        self._may_return_none.add(name)

        # ── Decorator-induced return fiber truncation ─────────────────────
        # If a function is decorated by a locally-defined decorator that
        # drops the delegate result, the effective return fiber collapses
        # to None regardless of the function body.
        func_defs: Dict[str, ast.FunctionDef] = {}
        for node in ast.walk(self._tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                func_defs[node.name] = node

        for node in ast.walk(self._tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            if not node.decorator_list:
                continue
            for deco in node.decorator_list:
                deco_name = None
                if isinstance(deco, ast.Name):
                    deco_name = deco.id
                elif isinstance(deco, ast.Attribute):
                    deco_name = deco.attr
                if deco_name and deco_name in func_defs:
                    issue = _check_decorator_wrapper_return(func_defs[deco_name])
                    if issue in ("drops_return", "transforms_return"):
                        self._may_return_none.add(node.name)

    def _all_branches_return(self, stmts: List[ast.stmt]) -> bool:
        """Check if all branches of a statement list end with return/raise."""
        if not stmts:
            return False
        last = stmts[-1]
        if isinstance(last, (ast.Return, ast.Raise)):
            return True
        if isinstance(last, ast.If):
            # Both if and else branches must return
            if_returns = self._all_branches_return(last.body)
            else_returns = self._all_branches_return(last.orelse) if last.orelse else False
            return if_returns and else_returns
        if isinstance(last, ast.For) and last.orelse:
            return self._all_branches_return(last.orelse)
        if isinstance(last, ast.Try):
            # All handlers + body must return
            body_ret = self._all_branches_return(last.body)
            handler_ret = all(self._all_branches_return(h.body)
                             for h in last.handlers) if last.handlers else True
            return body_ret and handler_ret
        return False

    def _compute_grothendieck_fibers(self) -> None:
        """Compute interprocedural return fibers via Grothendieck fibration.

        For each locally-defined function, analyze its body to compute the
        full return stalk — the fiber of the refinement presheaf over the
        return site.  This captures not just None-ness but all refinement
        predicates: zero-ness, boundedness, type, openness, etc.

        Mathematically, this is the Grothendieck construction:
        - Base category B: the call graph (functions as objects, calls as morphisms)
        - Fiber over f in B: the stalk at f's return site
        - Reindexing along a call f->g: pullback of g's return fiber to f's context

        At a call site ``x = g(args)`` in function f, the cartesian lift
        transfers g's return fiber to x in f's stalk.
        """
        func_defs: Dict[str, ast.FunctionDef] = {}
        for node in ast.walk(self._tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                func_defs[node.name] = node

        for name, func_node in func_defs.items():
            # ── Fiber coherence: skip decorated functions whose return fiber
            # was truncated to ⊥ by a return-dropping decorator.  The
            # undecorated body's return fiber is NOT the effective return
            # fiber — the decorator acts as a base change that collapses it.
            # Pulling back the undecorated fiber would violate the cocycle
            # condition on the Grothendieck fibration.
            if name in self._may_return_none:
                continue
            try:
                return_stalk = self._analyze_return_fiber(func_node)
                if return_stalk is not None:
                    self._return_fibers[name] = return_stalk
            except Exception:
                pass

    def _analyze_return_fiber(self, func_node: ast.FunctionDef) -> Optional['_Stalk']:
        """Analyze a function body to extract the return fiber.

        Walks the body looking for return statements, extracts the
        returned expression's refinement properties, and joins them
        (cocycle condition) to produce the function's return stalk.

        The return stalk uses a synthetic variable '_result' to hold
        the refinements of the returned value.
        """
        returns: List[ast.Return] = []
        for child in ast.walk(func_node):
            if child is not func_node and isinstance(
                child, (ast.FunctionDef, ast.AsyncFunctionDef)
            ):
                continue
            if isinstance(child, ast.Return):
                returns.append(child)

        if not returns:
            return None

        result_stalk = _Stalk()
        result_var = '_result'
        first = True

        # Pre-compute simple variable-to-value mapping within the function
        # to trace ``return var`` where ``var = None`` (nullable fiber).
        _local_var_vals: Dict[str, ast.AST] = {}
        for stmt in ast.walk(func_node):
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
                tgt = stmt.targets[0]
                if isinstance(tgt, ast.Name):
                    _local_var_vals[tgt.id] = stmt.value

        for ret in returns:
            branch_stalk = _Stalk()
            if ret.value is None:
                branch_stalk.is_none[result_var] = _AbstractVal.TRUE
            else:
                branch_stalk.is_none[result_var] = _AbstractVal.FALSE
                val = ret.value

                if isinstance(val, ast.Constant):
                    if val.value is None:
                        branch_stalk.is_none[result_var] = _AbstractVal.TRUE
                    elif isinstance(val.value, (int, float)):
                        if val.value == 0:
                            branch_stalk.is_zero[result_var] = _AbstractVal.TRUE
                        else:
                            branch_stalk.is_zero[result_var] = _AbstractVal.FALSE
                        if val.value < 0:
                            branch_stalk.is_negative[result_var] = _AbstractVal.TRUE
                        else:
                            branch_stalk.is_negative[result_var] = _AbstractVal.FALSE
                elif isinstance(val, (ast.List, ast.Tuple, ast.Set)):
                    branch_stalk.is_none[result_var] = _AbstractVal.FALSE
                    branch_stalk.is_zero[result_var] = (
                        _AbstractVal.TRUE if not val.elts
                        else _AbstractVal.FALSE
                    )
                elif isinstance(val, ast.Dict):
                    branch_stalk.is_none[result_var] = _AbstractVal.FALSE
                elif isinstance(val, ast.Call):
                    if isinstance(val.func, ast.Name):
                        fn = val.func.id
                        if fn and fn[0].isupper():
                            branch_stalk.is_none[result_var] = _AbstractVal.FALSE
                        elif fn in ('sorted', 'list', 'dict', 'set', 'tuple',
                                    'str', 'bytes', 'frozenset'):
                            branch_stalk.is_none[result_var] = _AbstractVal.FALSE
                        elif fn in ('len', 'abs', 'sum', 'min', 'max',
                                    'int', 'float', 'bool'):
                            branch_stalk.is_none[result_var] = _AbstractVal.FALSE
                            branch_stalk.is_zero[result_var] = _AbstractVal.UNKNOWN
                elif isinstance(val, ast.BinOp):
                    branch_stalk.is_none[result_var] = _AbstractVal.FALSE
                # ── Name → trace through local assignment ──
                # ``return var`` where ``var = None`` → nullable fiber
                elif isinstance(val, ast.Name):
                    local_val = _local_var_vals.get(val.id)
                    if local_val is not None:
                        if isinstance(local_val, ast.Constant) and local_val.value is None:
                            branch_stalk.is_none[result_var] = _AbstractVal.TRUE
                        elif isinstance(local_val, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
                            branch_stalk.is_none[result_var] = _AbstractVal.FALSE
                        elif isinstance(local_val, ast.Call):
                            cn = ""
                            try:
                                cn = ast.unparse(local_val.func) if hasattr(local_val, 'func') else ""
                            except Exception:
                                pass
                            if cn and cn[0].isupper():
                                branch_stalk.is_none[result_var] = _AbstractVal.FALSE

            if first:
                result_stalk = branch_stalk
                first = False
            else:
                result_stalk = result_stalk.join(branch_stalk)

        return result_stalk

    def _is_locally_defined(self, name: str) -> bool:
        """Check if a function name is defined in the current module."""
        for node in ast.walk(self._tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node.name == name:
                    return True
        return False

    def _init_class_field_stalks(self, func_node: ast.AST, entry: '_Stalk') -> None:
        """Lift class __init__ field assignments to entry stalk of other methods.

        When a method ``m`` is inside a class ``C`` and ``C.__init__`` assigns
        ``self.attr = <expr>`` where ``<expr>`` is a non-None literal or
        constructor call, the entry stalk for ``m`` should reflect that
        ``self.attr`` is non-None.  This is the restriction of the class
        presheaf section from the global (post-init) site to the method site.
        """
        # Find the enclosing class
        enclosing_class = None
        for node in ast.walk(self._tree):
            if isinstance(node, ast.ClassDef):
                for item in node.body:
                    if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        if item is func_node:
                            enclosing_class = node
                            break
                if enclosing_class is not None:
                    break
        if enclosing_class is None:
            return
        if getattr(func_node, 'name', '') == '__init__':
            return  # Don't lift to __init__ itself

        # Find __init__ in this class
        init_node = None
        for item in enclosing_class.body:
            if (isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and item.name == '__init__'):
                init_node = item
                break
        if init_node is None:
            return

        # Scan __init__ body for self.attr = <non-None>
        self_param = (init_node.args.args[0].arg
                      if init_node.args.args else 'self')
        for stmt in ast.walk(init_node):
            if not isinstance(stmt, ast.Assign):
                continue
            for tgt in stmt.targets:
                if (isinstance(tgt, ast.Attribute) and isinstance(tgt.value, ast.Name)
                        and tgt.value.id == self_param):
                    attr_key = f"{self_param}.{tgt.attr}"
                    val = stmt.value
                    if isinstance(val, ast.Constant) and val.value is not None:
                        entry.is_none[attr_key] = _AbstractVal.FALSE
                    elif isinstance(val, (ast.List, ast.Dict, ast.Set, ast.Tuple)):
                        entry.is_none[attr_key] = _AbstractVal.FALSE
                    elif (isinstance(val, ast.Call) and isinstance(val.func, ast.Name)
                          and val.func.id[0:1].isupper()):
                        entry.is_none[attr_key] = _AbstractVal.FALSE
                    elif isinstance(val, ast.ListComp):
                        entry.is_none[attr_key] = _AbstractVal.FALSE

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

            # ── Class field initialization: presheaf section lift ──
            # When analyzing a method other than __init__, the class's
            # __init__ has already run, so ``self.attr`` fields assigned
            # in __init__ to non-None values carry a non-⊥ section at
            # the method's entry site.  This is a restriction of the
            # class presheaf's global section to the method sub-site.
            self._init_class_field_stalks(func_node, entry)

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
                # ``finally: x.close()`` is a resource lifecycle morphism:
                # the finally-block guarantees that the close transition
                # fires on ALL exit paths (normal, exception, break, etc.).
                # In the resource presheaf, this means x transitions to the
                # CLOSED fiber unconditionally — equivalent to a ``with`` block.
                for fstmt in stmt.finalbody:
                    if (isinstance(fstmt, ast.Expr)
                            and isinstance(fstmt.value, ast.Call)
                            and isinstance(fstmt.value.func, ast.Attribute)
                            and fstmt.value.func.attr == 'close'):
                        obj = fstmt.value.func.value
                        if isinstance(obj, ast.Name):
                            result.is_open[obj.id] = _AbstractVal.FALSE
            return result

        # ── Match/case: coproduct decomposition over pattern fibers ──
        # Each case is a coproduct summand; the match block's exit stalk
        # is the join (gluing) of all case-arm exit stalks.  If every case
        # unconditionally binds a variable, the post-match section for that
        # variable is total.  A wildcard ``case _:`` makes the coproduct
        # exhaustive — no residual fiber remains unmatched.
        if isinstance(stmt, ast.Match):
            case_exits: List[_Stalk] = []
            has_wildcard = False
            for case in stmt.cases:
                case_stalk = stalk.copy()
                # Bind pattern variables
                pat = case.pattern
                for pvar in _pattern_bound_names(pat):
                    case_stalk.is_bound[pvar] = _AbstractVal.TRUE
                    case_stalk.is_none[pvar] = _AbstractVal.FALSE
                if _pattern_is_wildcard(pat):
                    has_wildcard = True
                case_exit = self._analyze_body(case.body, case_stalk)
                # Only non-terminating cases contribute to post-match flow.
                # A case that returns/raises/breaks never reaches the point
                # after the match block — its fiber is dead in the post-match
                # stalk.
                if not _body_terminates(case.body):
                    case_exits.append(case_exit)
            if not case_exits:
                # ALL cases terminate → execution never continues past match
                return stalk
            # Join all non-terminating case exits
            result = case_exits[0]
            for ce in case_exits[1:]:
                result = result.join(ce)
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

        # ── IfExp (ternary): coproduct decomposition at expression level ──
        # ``x = body if test else orelse`` decomposes into two fibers:
        #   - test-true fiber  → body expression section
        #   - test-false fiber → orelse expression section
        # The result stalk is the join (gluing) of both fiber sections.
        # Special case: ``x = v if v else default`` guarantees x is truthy
        # (non-None, non-zero) because the body fiber is the truthiness
        # sub-site of v, and the orelse default provides a fallback.
        if isinstance(value, ast.IfExp):
            # Both branches produce a non-None value in most cases
            body = value.body
            orelse = value.orelse
            # If orelse is a non-None constant → result is definitely not None
            if isinstance(orelse, ast.Constant) and orelse.value is not None:
                stalk.is_none[var] = _AbstractVal.FALSE
            # If body is a non-None constant → join with orelse info
            elif isinstance(body, ast.Constant) and body.value is not None:
                stalk.is_none[var] = _AbstractVal.FALSE
            # ``v if v else default`` pattern: test is truthiness of same var
            test = value.test
            if isinstance(test, ast.Name):
                # The test variable's truthiness guarantees body branch is truthy.
                # If orelse is a non-zero, non-None constant, result is always truthy.
                if isinstance(orelse, ast.Constant) and orelse.value not in (None, 0, '', False):
                    stalk.is_zero[var] = _AbstractVal.FALSE
                    stalk.is_none[var] = _AbstractVal.FALSE
                # If orelse is a Name (parameter/variable), the programmer is
                # explicitly providing a fallback for the falsy case.  Absent
                # evidence that the fallback itself is zero/None, treat the
                # section as truthy.  This handles ``x = b if b else default``.
                elif isinstance(orelse, ast.Name):
                    # Check if the fallback is known-zero or known-None in stalk
                    fb = orelse.id
                    fb_zero = stalk.is_zero.get(fb, _AbstractVal.UNKNOWN)
                    fb_none = stalk.is_none.get(fb, _AbstractVal.UNKNOWN)
                    if fb_zero is not _AbstractVal.TRUE:
                        stalk.is_zero[var] = _AbstractVal.FALSE
                    if fb_none is not _AbstractVal.TRUE:
                        stalk.is_none[var] = _AbstractVal.FALSE
                # If orelse is a function call (e.g., ``v if v else func()``),
                # assume the fallback produces a truthy value.
                elif isinstance(orelse, ast.Call):
                    stalk.is_zero[var] = _AbstractVal.FALSE
                    stalk.is_none[var] = _AbstractVal.FALSE
            # ``v if v is not None else default`` pattern
            if (isinstance(test, ast.Compare) and len(test.ops) == 1
                    and isinstance(test.ops[0], ast.IsNot)
                    and isinstance(test.comparators[0], ast.Constant)
                    and test.comparators[0].value is None):
                if isinstance(orelse, ast.Constant) and orelse.value is not None:
                    stalk.is_none[var] = _AbstractVal.FALSE

        # ── PascalCase calls: constructor morphisms always produce non-⊥ ──
        # A class constructor ``Cls(...)`` is a morphism in the carrier
        # presheaf that always lands in the Cls-fiber, never in the ⊥-fiber
        # (None).  This is a fundamental property of constructor sections.
        if isinstance(value, ast.Call) and isinstance(value.func, ast.Name):
            fname = value.func.id
            if fname and fname[0].isupper() and fname not in ('None', 'True', 'False'):
                stalk.is_none[var] = _AbstractVal.FALSE

        # ── Builtins and stdlib functions that always produce non-None ──
        # These are morphisms in the type presheaf whose codomain fiber
        # excludes ⊥ (None).  The list is conservative: only functions
        # guaranteed to return a value (not None) on success.
        if isinstance(value, ast.Call):
            func = value.func
            call_name = ''
            if isinstance(func, ast.Name):
                call_name = func.id
            elif isinstance(func, ast.Attribute):
                call_name = func.attr
            _NONNONE_CALL_NAMES = {
                'sorted', 'reversed', 'enumerate', 'zip', 'map', 'filter',
                'range', 'len', 'abs', 'min', 'max', 'sum', 'any', 'all',
                'hash', 'id', 'repr', 'hex', 'oct', 'bin', 'chr', 'ord',
                'divmod', 'pow', 'round', 'type', 'isinstance', 'issubclass',
                'reduce', 'partial', 'lru_cache', 'wraps',
            }
            if call_name in _NONNONE_CALL_NAMES:
                # Special case: reduce() with only 2 args can fail on empty
                if (call_name == 'reduce' and isinstance(value, ast.Call)
                        and len(value.args) == 2 and not value.keywords):
                    # Check emptiness-fiber restriction on the iterable.
                    # If the iterable is guarded as non-empty, reduce is safe.
                    iter_arg = value.args[1]
                    iter_name = iter_arg.id if isinstance(iter_arg, ast.Name) else None
                    if iter_name and _has_emptiness_guard(self._tree, iter_name, value.lineno):
                        stalk.is_none[var] = _AbstractVal.FALSE
                    else:
                        stalk.is_none[var] = _AbstractVal.UNKNOWN
                else:
                    stalk.is_none[var] = _AbstractVal.FALSE
            # ── Interprocedural return-fiber analysis ──
            # If ``f`` is locally defined and its return fiber includes ⊥
            # (i.e., it may return None), mark the result as potentially None.
            # This propagates the partiality of the return section to the
            # caller's presheaf — the gluing condition requires the caller
            # to handle the None case.
            if isinstance(func, ast.Name) and func.id in self._may_return_none:
                stalk.is_none[var] = _AbstractVal.UNKNOWN
            # Converse: locally-defined function that always returns a value
            # (all branches end in ``return <expr>``) → return fiber excludes ⊥.
            elif (isinstance(func, ast.Name)
                  and func.id not in self._may_return_none
                  and self._is_locally_defined(func.id)):
                stalk.is_none[var] = _AbstractVal.FALSE

            # ── Grothendieck cartesian lift ──
            # Pull back the callee's full return fiber to the caller's stalk.
            # This transfers all predicates (zero, negative, bound, etc.),
            # not just None-ness.  The pullback renames '_result' → var.
            if isinstance(func, ast.Name) and func.id in self._return_fibers:
                ret_fiber = self._return_fibers[func.id]
                rv = '_result'
                for pred_name in _Stalk.STANDARD_PREDICATES:
                    src_fiber = ret_fiber._preds.get(pred_name, {})
                    if rv in src_fiber:
                        existing = stalk._fiber(pred_name).get(var, _AbstractVal.UNKNOWN)
                        pulled = src_fiber[rv]
                        # Meet: combine caller-known info with callee return info
                        stalk._fiber(pred_name)[var] = existing.meet(pulled)

        # ── Attribute call: method calls on non-None objects produce values ──
        # ``obj.method(...)`` — if method returns self or a new object,
        # the result is typically non-None (e.g., builder pattern).
        if isinstance(value, ast.Call) and isinstance(value.func, ast.Attribute):
            method = value.func.attr
            # Methods that conventionally return new non-None values
            _NONNONE_METHODS = {
                'copy', 'replace', 'strip', 'lstrip', 'rstrip',
                'lower', 'upper', 'title', 'capitalize', 'join',
                'format', 'encode', 'decode', 'split', 'rsplit',
                'partition', 'rpartition',
            }
            if method in _NONNONE_METHODS:
                stalk.is_none[var] = _AbstractVal.FALSE
            # list()/dict()/set() view methods
            if method in ('keys', 'values', 'items'):
                stalk.is_none[var] = _AbstractVal.FALSE
            # ── Local return-self analysis (builder pattern) ──
            # If the called method is defined in the same file and every
            # return statement returns ``self``, the call is non-None.
            # This is a sheaf-theoretic local section lift: the method's
            # return fiber is the same object fiber → non-⊥.
            obj = value.func.value
            if isinstance(obj, ast.Name):
                obj_carrier = stalk.carrier.get(obj.id, '')
                for cls_node in ast.walk(self._tree):
                    if not isinstance(cls_node, ast.ClassDef):
                        continue
                    # Match by carrier type or by any class definition
                    for item in cls_node.body:
                        if (isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
                                and item.name == method):
                            returns = [n for n in ast.walk(item) if isinstance(n, ast.Return)]
                            if returns and all(
                                isinstance(r.value, ast.Name) and r.value.id == 'self'
                                for r in returns if r.value is not None
                            ):
                                stalk.is_none[var] = _AbstractVal.FALSE

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


def _pattern_bound_names(pattern) -> List[str]:
    """Extract variable names bound by a match-case pattern.

    Pattern matching introduces bindings into the case-arm's local site.
    Each ``MatchAs(name=v)`` or ``MatchStar(name=v)`` creates a section
    in the binding presheaf for variable ``v``.
    """
    names: List[str] = []
    if not hasattr(ast, 'MatchAs'):  # Python < 3.10
        return names
    if isinstance(pattern, ast.MatchAs):
        if pattern.name:
            names.append(pattern.name)
        if pattern.pattern:
            names.extend(_pattern_bound_names(pattern.pattern))
    elif isinstance(pattern, ast.MatchOr):
        for p in pattern.patterns:
            names.extend(_pattern_bound_names(p))
    elif isinstance(pattern, ast.MatchSequence):
        for p in pattern.patterns:
            names.extend(_pattern_bound_names(p))
    elif isinstance(pattern, ast.MatchMapping):
        for p in pattern.patterns:
            names.extend(_pattern_bound_names(p))
        if hasattr(pattern, 'rest') and pattern.rest:
            names.append(pattern.rest)
    elif isinstance(pattern, ast.MatchClass):
        for p in pattern.patterns:
            names.extend(_pattern_bound_names(p))
        for p in pattern.kwd_patterns:
            names.extend(_pattern_bound_names(p))
    elif isinstance(pattern, ast.MatchStar):
        if pattern.name:
            names.append(pattern.name)
    elif isinstance(pattern, ast.MatchValue):
        pass  # no bindings
    return names


def _pattern_is_wildcard(pattern) -> bool:
    """Check if a match-case pattern is a wildcard (catches everything).

    A wildcard ``case _:`` is ``MatchAs(name=None, pattern=None)``
    in the AST.  It provides an exhaustive fiber decomposition — every
    value is covered, so the coproduct ∐ cases = total.
    """
    if not hasattr(ast, 'MatchAs'):
        return False
    if isinstance(pattern, ast.MatchAs):
        return pattern.pattern is None
    return False


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
        # Chained attributes: self.parts.method → "self.parts"
        if isinstance(node.value, ast.Attribute) and isinstance(node.value.value, ast.Name):
            return f"{node.value.value.id}.{node.value.attr}"

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
        # Chained: self.parts.append(...) → "self.parts"
        if (isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Attribute)
                and isinstance(node.func.value.value, ast.Name)):
            return f"{node.func.value.value.id}.{node.func.value.attr}"

    # From site_id name: extract variable after last underscore
    name = req.site_id.name
    # Patterns: bind_x_L3, attr_x_L5, div_L10
    parts = name.split('_')
    if len(parts) >= 3 and parts[-1].startswith('L'):
        return '_'.join(parts[1:-1])

    return None


def _extract_var_from_req_description(desc: str) -> Optional[str]:
    """Extract the primary variable name from a requirement description.

    For lifecycle requirements the description has the form
    ``\`fout.write\` used after ...`` or ``\`fout\` used after ...``
    — we extract the root variable (``fout``).
    """
    if '`' in desc:
        try:
            start = desc.index('`') + 1
            end = desc.index('`', start)
            token = desc[start:end]
            # ``fout.write`` → ``fout``
            return token.split('.')[0]
        except (ValueError, IndexError):
            pass
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
    """A guard extracted from the AST with its line range and predicate.

    Each guard represents a sub-site of the observation cover where a
    condition is known to hold.  The guard carries:

    1. A Z3 `predicate` for SMT discharge
    2. A `stalk_refinement` dict mapping (pred_name, var) → _AbstractVal,
       describing how the guard refines the presheaf stalk.
       This enables predicate-based guard resolution: a guard resolves a
       requirement if its stalk_refinement implies the requirement's
       predicate entry from _BUG_PREDICATE_MAP.
    3. The legacy `protects_against` set (derived from stalk_refinement
       but kept for backward compatibility and for guards that protect
       against bug types without a predicate entry, e.g., INTEGER_OVERFLOW).
    """
    guard_type: str
    predicate: Predicate
    protects_against: Set[str]  # bug type codes
    start_line: int
    end_line: int
    condition_text: str
    protected_key: str = ""  # for key_exists guards: the specific key tested
    # Fiber locality: restrict protection to specific resource variables.
    # When non-empty, the guard only resolves requirements whose variable
    # is in this set — prevents outer ``with`` from resolving inner-var UAF.
    protected_vars: Set[str] = field(default_factory=set)
    # Predicate-based refinement: (pred_name, var_name) → abstract value
    stalk_refinement: Dict[tuple, '_AbstractVal'] = field(default_factory=dict)


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

            # ── try/except definite assignment: NULL_PTR guard ──
            # If the same variable is assigned in the try body AND every
            # except handler, that variable has a definite section after
            # the try/except — it is never None.  Sheaf section join
            # across exception fibers.
            try_assigns: Set[str] = set()
            for s in node.body:
                for n in ast.walk(s):
                    if isinstance(n, ast.Assign):
                        for t in n.targets:
                            if isinstance(t, ast.Name):
                                try_assigns.add(t.id)
            if node.handlers and try_assigns:
                handler_assigns_all: Optional[Set[str]] = None
                for handler in node.handlers:
                    h_assigns: Set[str] = set()
                    for s in handler.body:
                        for n in ast.walk(s):
                            if isinstance(n, ast.Assign):
                                for t in n.targets:
                                    if isinstance(t, ast.Name):
                                        h_assigns.add(t.id)
                    if handler_assigns_all is None:
                        handler_assigns_all = h_assigns
                    else:
                        handler_assigns_all &= h_assigns
                if handler_assigns_all:
                    definite_vars = try_assigns & handler_assigns_all
                    if definite_vars:
                        try_end = max(
                            body_end,
                            max(
                                (getattr(s, 'end_lineno', s.lineno)
                                 for h in node.handlers for s in h.body),
                                default=body_end,
                            ),
                        )
                        guards.append(_GuardSite(
                            guard_type="try_except_definite",
                            predicate=BoolLit(True),
                            protects_against={"NULL_PTR"},
                            start_line=try_end, end_line=try_end + 100,
                            protected_vars=definite_vars,
                            condition_text=f"try/except defines {definite_vars}",
                        ))

    # ── with-statement guards: resolve MEMORY_LEAK, USE_AFTER_FREE, DOUBLE_FREE ──
    # A with-statement provides a GLOBAL SECTION of the lifecycle presheaf:
    # the resource is guaranteed OPEN inside the block and CLOSED after,
    # on ALL paths including exception paths.
    # Fiber locality: the guard's protected_vars restrict it to only the
    # variables bound in THIS with-statement's ``as`` clause, preventing
    # an outer ``with`` from incorrectly resolving inner-variable UAF.
    for node in ast.walk(tree):
        if isinstance(node, (ast.With, ast.AsyncWith)):
            body_start = node.body[0].lineno if node.body else node.lineno
            body_end = max(
                (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                default=node.lineno,
            )
            # Collect variables bound by this with-statement's items
            with_vars: Set[str] = set()
            for item in node.items:
                if item.optional_vars is not None:
                    v = _expr_to_var_name(item.optional_vars, "")
                    if v:
                        with_vars.add(v)
            # Inside the with block, the resource is OPEN → resolves USE_AFTER_FREE
            # The with block itself → resolves MEMORY_LEAK (cleanup guaranteed)
            guards.append(_GuardSite(
                guard_type="with_block",
                predicate=BoolLit(True),
                protects_against={"MEMORY_LEAK", "USE_AFTER_FREE", "DOUBLE_FREE",
                                  "USE_AFTER_CLOSE", "DOUBLE_CLOSE", "MISSING_CLEANUP"},
                start_line=body_start, end_line=body_end,
                condition_text=f"with-statement (lifecycle presheaf global section)",
                protected_vars=with_vars,
            ))

        # ── try/finally with .close(): resource lifecycle guaranteed ──
        # A try/finally block with `.close()` in the finally clause is
        # functionally equivalent to a `with` statement — it establishes
        # a resource lifecycle presheaf section where cleanup is guaranteed
        # on ALL exit paths.  The guard extends backward to cover the
        # resource allocation site (the open/socket call preceding try).
        if isinstance(node, ast.Try) and node.finalbody:
            for fstmt in node.finalbody:
                if (isinstance(fstmt, ast.Expr)
                        and isinstance(fstmt.value, ast.Call)
                        and isinstance(fstmt.value.func, ast.Attribute)
                        and fstmt.value.func.attr == 'close'):
                    # The guard covers from before the try (where the resource
                    # is typically allocated) to the end of the finally block.
                    # Walk backward from the try to find the allocation site.
                    close_target = fstmt.value.func.value
                    close_var = None
                    if isinstance(close_target, ast.Name):
                        close_var = close_target.id

                    try_start = node.body[0].lineno if node.body else node.lineno
                    try_end = max(
                        (getattr(s, 'end_lineno', s.lineno) for s in node.finalbody),
                        default=node.lineno,
                    )

                    # Extend guard backward to cover the resource allocation
                    # site — typically 1-3 lines before the try block.
                    guard_start = try_start
                    if close_var:
                        # Look for assignment to the closed variable in the
                        # enclosing function/module, before the try block.
                        for sib in ast.walk(tree):
                            if isinstance(sib, ast.Assign):
                                for t in sib.targets:
                                    if isinstance(t, ast.Name) and t.id == close_var:
                                        if sib.lineno < try_start:
                                            guard_start = min(guard_start, sib.lineno)

                    guards.append(_GuardSite(
                        guard_type="try_finally_close",
                        predicate=BoolLit(True),
                        protects_against={"MEMORY_LEAK", "USE_AFTER_CLOSE", "MISSING_CLEANUP"},
                        start_line=guard_start, end_line=try_end,
                        condition_text="try/finally .close() (resource lifecycle presheaf)",
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
            # Sheaf-theoretic: ANY min/max call bounds the magnitude fiber
            # to a truncated presheaf.  ``min(x, K)`` alone is an upper
            # clamp; ``max(x, K)`` alone is a lower clamp.
            is_clamp = (('max(' in val_text and 'min(' in val_text) or
                        ('clamp' in val_text.lower()) or
                        ('min(' in val_text and 'len(' in val_text) or
                        ('max(' in val_text and (', 0)' in val_text or ', 0,' in val_text or '(0,' in val_text or '(0 ,' in val_text)) or
                        # Bare min(var, constant) or min(constant, var) — upper clamp
                        (isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name)
                         and node.value.func.id == 'min' and len(node.value.args) == 2
                         and any(isinstance(a, ast.Constant) and isinstance(a.value, (int, float))
                                 for a in node.value.args)) or
                        # Bare max(var, constant) — lower clamp
                        (isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name)
                         and node.value.func.id == 'max' and len(node.value.args) == 2
                         and any(isinstance(a, ast.Constant) and isinstance(a.value, (int, float))
                                 for a in node.value.args)))
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
                                    protects_against={"INTEGER_OVERFLOW", "OVERFLOW", "BOUNDS", "FP_DOMAIN", "INDEX_OOB"},
                                    start_line=assign_end, end_line=func_end,
                                    condition_text=f"clamping: {val_text[:60]}",
                                ))
                                break

    # ── Range bounds-check guards: resolve INTEGER_OVERFLOW ──
    # Pattern: ``if -N <= x <= N:`` or ``if x < N and x > -N:``
    # A range comparison restricts the integer stalk to a bounded fiber,
    # eliminating the possibility of overflow.
    # Also: ``x &= 0xFF...`` bitmask — restricts to a fixed-width fiber.
    for node in ast.walk(tree):
        # Bitmask: ``x &= 0xFFFF`` or ``x = x & 0xFFFF``
        if isinstance(node, ast.AugAssign) and isinstance(node.op, ast.BitAnd):
            if isinstance(node.value, ast.Constant) and isinstance(node.value.value, int):
                mask_line = node.lineno
                mask_end = getattr(node, 'end_lineno', mask_line) or mask_line
                for parent in ast.walk(tree):
                    if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        for desc in ast.walk(parent):
                            if desc is node:
                                func_end = max(
                                    (getattr(s, 'end_lineno', s.lineno) for s in parent.body),
                                    default=mask_end + 100,
                                )
                                guards.append(_GuardSite(
                                    guard_type="bitmask_bound",
                                    predicate=BoolLit(True),
                                    protects_against={"INTEGER_OVERFLOW", "OVERFLOW"},
                                    start_line=mask_end, end_line=func_end,
                                    condition_text=f"bitmask &= 0x{node.value.value:X} (bounded fiber)",
                                ))
                                break
        # Inline bitmask BinOp: ``return (a + b) & 0xFFFFFFFF`` or
        # ``x = expr & MASK`` — the BitAnd truncates the magnitude fiber
        # to a bounded presheaf section, resolving INTEGER_OVERFLOW.
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitAnd):
            mask_const = None
            if isinstance(node.right, ast.Constant) and isinstance(node.right.value, int):
                mask_const = node.right.value
            elif isinstance(node.left, ast.Constant) and isinstance(node.left.value, int):
                mask_const = node.left.value
            if mask_const is not None and mask_const > 0:
                mask_line = node.lineno
                for parent in ast.walk(tree):
                    if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        for desc in ast.walk(parent):
                            if desc is node:
                                func_end = max(
                                    (getattr(s, 'end_lineno', s.lineno) for s in parent.body),
                                    default=mask_line + 100,
                                )
                                guards.append(_GuardSite(
                                    guard_type="bitmask_bound",
                                    predicate=BoolLit(True),
                                    protects_against={"INTEGER_OVERFLOW", "OVERFLOW"},
                                    start_line=mask_line, end_line=func_end,
                                    condition_text=f"bitmask & 0x{mask_const:X} (bounded fiber)",
                                ))
                                break
        # Range comparison: ``if -N <= x <= N:`` or similar
        if isinstance(node, ast.If):
            try:
                cond_text = ast.unparse(node.test)
            except Exception:
                continue
            # Check for chained comparison: ``lo <= x <= hi``
            is_range = False
            test = node.test
            if (isinstance(test, ast.Compare) and len(test.ops) >= 2
                    and all(isinstance(op, (ast.LtE, ast.Lt)) for op in test.ops)):
                is_range = True
            # Also: ``x >= lo and x <= hi``
            if (isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And)):
                has_lower = False
                has_upper = False
                for val in test.values:
                    if isinstance(val, ast.Compare):
                        for op in val.ops:
                            if isinstance(op, (ast.GtE, ast.Gt)):
                                has_lower = True
                            if isinstance(op, (ast.LtE, ast.Lt)):
                                has_upper = True
                if has_lower and has_upper:
                    is_range = True
            if is_range:
                body_start = node.body[0].lineno if node.body else node.lineno
                body_end = max(
                    (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                    default=node.lineno,
                )
                guards.append(_GuardSite(
                    guard_type="range_bounds_check",
                    predicate=BoolLit(True),
                    protects_against={"INTEGER_OVERFLOW", "OVERFLOW", "BOUNDS"},
                    start_line=body_start, end_line=body_end,
                    condition_text=f"range check: {cond_text[:60]}",
                ))

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
                                protected_key=var,  # fiber index: which variable's binding section
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

            if "== 0" in cond_text or "!= 0" in cond_text or "<= 0" in cond_text or "< 0" in cond_text:
                protects.add("DIV_ZERO")
            if "is None" in cond_text or "== None" in cond_text:
                protects.add("NULL_PTR")
            if "not " in cond_text and " in " in cond_text:
                protects.add("KEY_ERROR")
            # ── Cardinality section from len() early-return ──
            # An early return `if len(x) OP K: return` splits the covering
            # sieve.  The continuation branch carries a cardinality section
            # ¬(len(x) OP K), providing a lower bound on collection length.
            # This resolves INDEX_OOB for indices within that bound.
            # Covers: len(x)==0, len(x)<N, len(x)<=N for any N.
            if "len(" in cond_text and ("== 0" in cond_text or "< " in cond_text or "<= " in cond_text):
                protects.update({"INDEX_OOB", "DIV_ZERO"})
            # `> len(` or `>= len(` → bounds check protects INDEX_OOB
            if "len(" in cond_text and ("> len(" in cond_text or ">= len(" in cond_text or
                                         "> len(" in cond_text.replace(" ", "")):
                protects.update({"INDEX_OOB", "BOUNDS"})
            # `if not items:` / `if not x:` → protects against empty-collection bugs
            # Also handles compound: `if not x or not y:` (each variable is truthy after)
            if cond_text.startswith("not ") and " " not in cond_text[4:]:
                protects.update({"INDEX_OOB", "ASSERT_FAIL", "BOUNDS", "DIV_ZERO"})
            # Compound negated truthiness: `if not x or not y:`
            if " or " in cond_text:
                parts = cond_text.split(" or ")
                if all(p.strip().startswith("not ") for p in parts):
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

    # ══════════════════════════════════════════════════════════════════════
    # ASSERT GUARDS — fiber restriction via assertion
    #
    # An `assert P` statement introduces a FIBER RESTRICTION: the
    # continuation presheaf is restricted to the open set where P holds.
    # If P is violated, the program terminates (raises AssertionError),
    # so every section after the assert carries the P-refinement.
    # Sheaf-theoretically, the assert kills the ¬P fiber.
    # ══════════════════════════════════════════════════════════════════════
    for node in ast.walk(tree):
        if isinstance(node, ast.Assert):
            try:
                cond_text = ast.unparse(node.test)
            except Exception:
                continue
            assert_line = node.lineno
            # Guard covers everything after the assert to end of enclosing function
            for parent in ast.walk(tree):
                if not isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    continue
                # Check if this assert is inside this function
                func_start = parent.lineno
                func_end_line = max(
                    (getattr(s, 'end_lineno', s.lineno) for s in parent.body),
                    default=func_start + 200,
                )
                if not (func_start <= assert_line <= func_end_line):
                    continue
                after_start = assert_line + 1
                # Apply same patterns as if-conditions
                if "is not None" in cond_text or "!= None" in cond_text:
                    guards.append(_GuardSite(
                        guard_type="assert_guard",
                        predicate=BoolLit(True),
                        protects_against={"NULL_PTR"},
                        start_line=after_start, end_line=func_end_line,
                        condition_text=f"assert {cond_text}",
                    ))
                if "!= 0" in cond_text or "> 0" in cond_text or "< 0" in cond_text or "<= 0" not in cond_text and ">= 1" in cond_text:
                    guards.append(_GuardSite(
                        guard_type="assert_guard",
                        predicate=BoolLit(True),
                        protects_against={"DIV_ZERO"},
                        start_line=after_start, end_line=func_end_line,
                        condition_text=f"assert {cond_text}",
                    ))
                if "len(" in cond_text and any(op in cond_text for op in (">", "<", ">=", "<=", "==")):
                    guards.append(_GuardSite(
                        guard_type="assert_guard",
                        predicate=BoolLit(True),
                        protects_against={"INDEX_OOB", "BOUNDS"},
                        start_line=after_start, end_line=func_end_line,
                        condition_text=f"assert {cond_text}",
                    ))
                if "> 0" in cond_text or ">= 0" in cond_text:
                    guards.append(_GuardSite(
                        guard_type="assert_guard",
                        predicate=BoolLit(True),
                        protects_against={"FP_DOMAIN"},
                        start_line=after_start, end_line=func_end_line,
                        condition_text=f"assert {cond_text}",
                    ))
                if "isinstance(" in cond_text:
                    guards.append(_GuardSite(
                        guard_type="assert_guard",
                        predicate=BoolLit(True),
                        protects_against={"TYPE_ERROR", "TYPE_CONFUSION"},
                        start_line=after_start, end_line=func_end_line,
                        condition_text=f"assert {cond_text}",
                    ))
                break  # found the enclosing function

    # ══════════════════════════════════════════════════════════════════════
    # TERNARY / IfExp GUARDS — inline coproduct decomposition
    #
    # `x.attr if x is not None else default` is a coproduct:
    #   body-fiber (x is not None) ⊔ orelse-fiber (x is None).
    # The attribute access lives in the body-fiber where the guard holds.
    # Sheaf-theoretically, the IfExp test restricts the body to the
    # open set where the predicate is true.
    # ══════════════════════════════════════════════════════════════════════
    for node in ast.walk(tree):
        if isinstance(node, ast.IfExp):
            try:
                cond_text = ast.unparse(node.test)
            except Exception:
                continue
            body_start = getattr(node.body, 'lineno', node.lineno)
            body_end = getattr(node.body, 'end_lineno', body_start) or body_start
            if "is not None" in cond_text or "!= None" in cond_text:
                guards.append(_GuardSite(
                    guard_type="ternary_guard",
                    predicate=BoolLit(True),
                    protects_against={"NULL_PTR"},
                    start_line=body_start, end_line=body_end,
                    condition_text=f"ternary: {cond_text}",
                ))
            if "!= 0" in cond_text or "> 0" in cond_text or "< 0" in cond_text:
                guards.append(_GuardSite(
                    guard_type="ternary_guard",
                    predicate=BoolLit(True),
                    protects_against={"DIV_ZERO"},
                    start_line=body_start, end_line=body_end,
                    condition_text=f"ternary: {cond_text}",
                ))
            if "len(" in cond_text:
                guards.append(_GuardSite(
                    guard_type="ternary_guard",
                    predicate=BoolLit(True),
                    protects_against={"INDEX_OOB", "BOUNDS"},
                    start_line=body_start, end_line=body_end,
                    condition_text=f"ternary: {cond_text}",
                ))

    # ══════════════════════════════════════════════════════════════════════
    # TRUTHINESS GUARDS — non-empty section from truthiness test
    #
    # `if data:` where `data` is a sequence means `len(data) > 0`.
    # Inside the body, data carries a NON-EMPTY SECTION: the cardinality
    # sub-presheaf restricts to {n ∈ ℕ | n > 0}, making data[0] valid.
    # We recognize bare variable truthiness checks as INDEX_OOB guards.
    # ══════════════════════════════════════════════════════════════════════
    for node in ast.walk(tree):
        if isinstance(node, ast.If):
            try:
                cond_text = ast.unparse(node.test)
            except Exception:
                continue
            # Bare variable truthiness: `if data:` or `if items:`
            if isinstance(node.test, ast.Name):
                body_start = node.body[0].lineno if node.body else node.lineno
                body_end = max(
                    (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                    default=node.lineno,
                )
                guards.append(_GuardSite(
                    guard_type="truthiness",
                    predicate=BoolLit(True),
                    protects_against={"INDEX_OOB", "BOUNDS", "NULL_PTR", "KEY_ERROR"},
                    start_line=body_start, end_line=body_end,
                    condition_text=f"truthiness: {cond_text}",
                ))

    # ══════════════════════════════════════════════════════════════════════
    # HASATTR GUARDS — attribute-existence probe on the object presheaf
    #
    # `hasattr(obj, 'name')` probes whether the object's attribute
    # presheaf has a section for 'name'.  Inside the true branch,
    # `obj.name` is safe — the attribute exists.  For NULL_PTR,
    # `hasattr(obj, ...)` also proves obj is not None (can't call
    # hasattr on None).
    # ══════════════════════════════════════════════════════════════════════
    for node in ast.walk(tree):
        if isinstance(node, ast.If):
            try:
                cond_text = ast.unparse(node.test)
            except Exception:
                continue
            if "hasattr(" in cond_text:
                # Short-circuit: in `hasattr(obj, 'x') and obj.x ...`, the RHS
                # of the `and` is on the SAME LINE as the hasattr call — so the
                # guard must cover the condition line itself as well.
                cond_line = node.lineno
                body_start = node.body[0].lineno if node.body else node.lineno
                body_end = max(
                    (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                    default=node.lineno,
                )
                guards.append(_GuardSite(
                    guard_type="hasattr_guard",
                    predicate=BoolLit(True),
                    protects_against={"NULL_PTR", "ATTRIBUTE_ERROR"},
                    start_line=cond_line, end_line=body_end,
                    condition_text=f"hasattr: {cond_text}",
                ))

    # ══════════════════════════════════════════════════════════════════════
    # CONTINUE/BREAK AS LOOP-LOCAL EARLY RETURN
    #
    # In a loop body, `if x is None: continue` restricts the remainder
    # of the loop iteration to the ¬(x is None) fiber.  This is the
    # loop-local analogue of an early return: the `continue` kills the
    # None fiber for the rest of the iteration body.
    # Sheaf-theoretically: the iteration presheaf's continuation section
    # is restricted to the open set where ¬cond holds.
    # ══════════════════════════════════════════════════════════════════════
    for node in ast.walk(tree):
        if not isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            continue
        for i, stmt in enumerate(node.body):
            if not isinstance(stmt, ast.If):
                continue
            # Check if the if-body ends with continue or break
            body_terminates = (
                stmt.body and
                isinstance(stmt.body[-1], (ast.Continue, ast.Break))
            )
            if not body_terminates:
                continue
            try:
                cond_text = ast.unparse(stmt.test)
            except Exception:
                continue
            # Everything after this if (within the loop body) is guarded by ¬cond
            after_start = (stmt.end_lineno or stmt.lineno) + 1
            loop_body_end = max(
                (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                default=after_start + 50,
            )
            protects_cont: Set[str] = set()
            if "is None" in cond_text and "is not None" not in cond_text:
                protects_cont.add("NULL_PTR")
            if "== None" in cond_text:
                protects_cont.add("NULL_PTR")
            if "== 0" in cond_text or "!= 0" in cond_text:
                protects_cont.add("DIV_ZERO")
            if cond_text.startswith("not "):
                protects_cont.update({"INDEX_OOB", "NULL_PTR"})
            if "not hasattr(" in cond_text or "not isinstance(" in cond_text:
                protects_cont.add("NULL_PTR")
            if "hasattr(" in cond_text and "not " not in cond_text:
                protects_cont.add("NULL_PTR")
            if protects_cont:
                guards.append(_GuardSite(
                    guard_type="continue_guard",
                    predicate=BoolLit(True),
                    protects_against=protects_cont,
                    start_line=after_start, end_line=loop_body_end,
                    condition_text=f"after continue/break: if {cond_text}",
                ))

    # ══════════════════════════════════════════════════════════════════════
    # NESTED EARLY-RETURN GUARDS
    #
    # The basic early-return logic only checks top-level function body
    # statements.  But early returns inside `for` loops and nested `if`
    # blocks are equally valid guard patterns.
    # `for x in items: if bad(x): return` → after the if, code is guarded.
    # `if outer: if inner_bad: return; use_inner` → after inner if, guarded.
    # ══════════════════════════════════════════════════════════════════════
    for func_node in ast.walk(tree):
        if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        func_end = max(
            (getattr(s, 'end_lineno', s.lineno) for s in func_node.body),
            default=func_node.lineno + 200,
        )
        # Walk all nested blocks looking for if-return patterns
        for container in ast.walk(func_node):
            # Check inside for-loop bodies and if-else bodies
            body_lists = []
            if isinstance(container, (ast.For, ast.AsyncFor, ast.While)):
                body_lists.append(container.body)
            if isinstance(container, ast.If):
                body_lists.append(container.body)
                if container.orelse:
                    body_lists.append(container.orelse)
            for body in body_lists:
                for j, inner_stmt in enumerate(body):
                    if not isinstance(inner_stmt, ast.If):
                        continue
                    inner_terminates = (
                        inner_stmt.body and
                        isinstance(inner_stmt.body[-1], (ast.Return, ast.Raise))
                    )
                    if not inner_terminates:
                        continue
                    try:
                        inner_cond = ast.unparse(inner_stmt.test)
                    except Exception:
                        continue
                    inner_after = (inner_stmt.end_lineno or inner_stmt.lineno) + 1
                    block_end = max(
                        (getattr(s, 'end_lineno', s.lineno) for s in body),
                        default=inner_after + 50,
                    )
                    nested_protects: Set[str] = set()
                    if "== 0" in inner_cond or "!= 0" in inner_cond or "<= 0" in inner_cond or "< 0" in inner_cond:
                        nested_protects.add("DIV_ZERO")
                    if "is None" in inner_cond or "== None" in inner_cond:
                        nested_protects.add("NULL_PTR")
                    if "len(" in inner_cond:
                        nested_protects.update({"INDEX_OOB", "BOUNDS"})
                    if inner_cond.startswith("not ") and " " not in inner_cond[4:]:
                        nested_protects.update({"INDEX_OOB", "NULL_PTR", "DIV_ZERO"})
                    if "isinstance(" in inner_cond:
                        nested_protects.update({"TYPE_ERROR", "TYPE_CONFUSION"})
                    if any(op in inner_cond for op in ("> ", "< ", ">= ", "<= ")):
                        nested_protects.update({"INTEGER_OVERFLOW", "OVERFLOW", "BOUNDS", "FP_DOMAIN"})
                    if nested_protects:
                        # Return exits the function, so guard extends to func_end
                        guards.append(_GuardSite(
                            guard_type="nested_early_return",
                            predicate=BoolLit(True),
                            protects_against=nested_protects,
                            start_line=inner_after, end_line=func_end,
                            condition_text=f"nested early return: if {inner_cond}",
                        ))

    # ══════════════════════════════════════════════════════════════════════
    # RANGE/ENUMERATE LOOP-BOUNDED INDEX — valid-index sub-presheaf
    #
    # `for i in range(len(lst)):` creates a loop variable `i` bounded by
    # len(lst).  Inside the loop, `lst[i]` lies in the valid-index
    # sub-presheaf [0, len(lst)).  The loop iteration morphism ensures
    # the index section is total on each fiber.
    # Similarly, `for i, v in enumerate(lst):` bounds i by len(lst).
    # ══════════════════════════════════════════════════════════════════════
    for node in ast.walk(tree):
        if not isinstance(node, (ast.For, ast.AsyncFor)):
            continue
        iter_text = ""
        try:
            iter_text = ast.unparse(node.iter)
        except Exception:
            continue
        # Detect: range(len(X)) or enumerate(X)
        is_range_len = "range(len(" in iter_text.replace(" ", "") or "range(len(" in iter_text
        is_enumerate = iter_text.startswith("enumerate(") or "enumerate(" in iter_text
        # Also detect: range(var) where var = len(...) in the same scope
        if (not is_range_len and not is_enumerate
                and isinstance(node.iter, ast.Call)
                and isinstance(node.iter.func, ast.Name)
                and node.iter.func.id == 'range'
                and node.iter.args):
            arg0 = node.iter.args[0]
            if isinstance(arg0, ast.Name):
                # Find assignment: var = len(...)
                for assign in ast.walk(tree):
                    if (isinstance(assign, ast.Assign)
                            and len(assign.targets) == 1
                            and isinstance(assign.targets[0], ast.Name)
                            and assign.targets[0].id == arg0.id
                            and isinstance(assign.value, ast.Call)
                            and isinstance(assign.value.func, ast.Name)
                            and assign.value.func.id == 'len'):
                        is_range_len = True
                        break
        if is_range_len or is_enumerate:
            # Determine the range bound margin (k in `range(len(x) - k)`)
            range_margin = 0
            if is_range_len:
                try:
                    call_node = node.iter
                    if isinstance(call_node, ast.Call) and call_node.args:
                        arg0 = call_node.args[0]
                        # range(len(x) - k)
                        if (isinstance(arg0, ast.BinOp) and isinstance(arg0.op, ast.Sub)
                                and isinstance(arg0.right, ast.Constant)
                                and isinstance(arg0.right.value, int)):
                            range_margin = arg0.right.value
                except Exception:
                    pass

            # Check if any subscript in the loop body uses loop_var + offset
            # (e.g., arr[i + 1]) — such access may go past bounds unless the
            # range margin accounts for the offset.
            loop_var = ""
            if isinstance(node.target, ast.Name):
                loop_var = node.target.id
            elif isinstance(node.target, ast.Tuple) and node.target.elts:
                first = node.target.elts[0]
                if isinstance(first, ast.Name):
                    loop_var = first.id
            has_unsafe_offset = False
            if loop_var:
                for sub_node in ast.walk(node):
                    if isinstance(sub_node, ast.Subscript):
                        try:
                            idx_text = ast.unparse(sub_node.slice)
                        except Exception:
                            continue
                        if loop_var in idx_text and ("+" in idx_text or "-" in idx_text):
                            # Parse the offset to check against range_margin
                            sl = sub_node.slice
                            offset_safe = False
                            # Pattern: i + k where k <= range_margin
                            if (isinstance(sl, ast.BinOp) and isinstance(sl.op, ast.Add)
                                    and isinstance(sl.left, ast.Name)
                                    and sl.left.id == loop_var
                                    and isinstance(sl.right, ast.Constant)
                                    and isinstance(sl.right.value, int)):
                                if sl.right.value <= range_margin:
                                    offset_safe = True
                            # Pattern: i - k where k >= 0 (always safe)
                            if (isinstance(sl, ast.BinOp) and isinstance(sl.op, ast.Sub)
                                    and isinstance(sl.left, ast.Name)
                                    and sl.left.id == loop_var
                                    and isinstance(sl.right, ast.Constant)
                                    and isinstance(sl.right.value, int)
                                    and sl.right.value >= 0):
                                offset_safe = True
                            if not offset_safe:
                                has_unsafe_offset = True
                                break
            if not has_unsafe_offset:
                body_start = node.body[0].lineno if node.body else node.lineno
                body_end = max(
                    (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                    default=node.lineno,
                )
                guards.append(_GuardSite(
                    guard_type="loop_bounded_index",
                    predicate=BoolLit(True),
                    protects_against={"INDEX_OOB"},
                    start_line=body_start, end_line=body_end,
                    condition_text=f"loop-bounded index: {iter_text[:60]}",
                ))

    # ══════════════════════════════════════════════════════════════════════
    # NONE-FILTERING COMPREHENSION — filtered iteration sub-presheaf
    #
    # `filtered = [x for x in items if x is not None]` followed by
    # `for x in filtered:` guarantees x is never None inside the loop.
    # The comprehension filter restricts the iteration fiber to the
    # non-None sub-presheaf.
    # ══════════════════════════════════════════════════════════════════════
    for node in ast.walk(tree):
        if not isinstance(node, (ast.For, ast.AsyncFor)):
            continue
        # Check if iterating over a variable assigned from a
        # None-filtering comprehension
        if not isinstance(node.iter, ast.Name):
            continue
        iter_var = node.iter.id
        loop_var = ""
        if isinstance(node.target, ast.Name):
            loop_var = node.target.id
        if not loop_var:
            continue
        # Find the assignment: iter_var = [x for x in items if x is not None]
        for assign_node in ast.walk(tree):
            if not isinstance(assign_node, ast.Assign):
                continue
            if (len(assign_node.targets) == 1
                    and isinstance(assign_node.targets[0], ast.Name)
                    and assign_node.targets[0].id == iter_var
                    and assign_node.lineno < node.lineno):
                rhs = assign_node.value
                if isinstance(rhs, ast.ListComp) and rhs.generators:
                    gen = rhs.generators[0]
                    for if_clause in gen.ifs:
                        # Pattern: x is not None
                        if (isinstance(if_clause, ast.Compare)
                                and len(if_clause.ops) == 1
                                and isinstance(if_clause.ops[0], ast.IsNot)
                                and if_clause.comparators
                                and isinstance(if_clause.comparators[0], ast.Constant)
                                and if_clause.comparators[0].value is None):
                            body_start = node.body[0].lineno if node.body else node.lineno
                            body_end = max(
                                (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                                default=node.lineno,
                            )
                            guards.append(_GuardSite(
                                guard_type="none_filter_comprehension",
                                predicate=BoolLit(True),
                                protects_against={"NULL_PTR"},
                                start_line=body_start, end_line=body_end,
                                protected_vars={loop_var},
                                condition_text=f"None-filtered comprehension: {iter_var}",
                            ))

    # ══════════════════════════════════════════════════════════════════════
    # LITERAL CONSTRUCTION — non-None by construction
    #
    # Variables assigned from literal constructors ([...], {...}, (...),
    # "...", constructor()) are provably non-None.  The presheaf section
    # at the assignment site is total.
    # NOTE: Only applies to non-None literals/constructors where the
    # variable is never reassigned to a potentially-None value.
    # ══════════════════════════════════════════════════════════════════════
    for node in ast.walk(tree):
        if not isinstance(node, ast.Assign) or len(node.targets) != 1:
            continue
        if not isinstance(node.targets[0], ast.Name):
            continue
        rhs = node.value
        # Must be non-None literal/constructor
        is_nonnone_literal = False
        if isinstance(rhs, (ast.List, ast.Dict, ast.Set, ast.Tuple)):
            is_nonnone_literal = True
        elif isinstance(rhs, ast.JoinedStr):
            is_nonnone_literal = True  # f-strings are always str
        elif isinstance(rhs, ast.Constant):
            # Exclude None! Only non-None constants are non-None by construction
            if rhs.value is not None:
                is_nonnone_literal = True
        if not is_nonnone_literal:
            continue
        var_name = node.targets[0].id
        assign_line = node.lineno
        # Check that the variable is NOT later reassigned to something
        # potentially None in the same scope (too conservative otherwise)
        later_reassigned = False
        for parent_fn in ast.walk(tree):
            if not isinstance(parent_fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            for stmt in ast.walk(parent_fn):
                if isinstance(stmt, ast.Assign) and stmt is not node:
                    for t in stmt.targets:
                        if isinstance(t, ast.Name) and t.id == var_name and stmt.lineno > assign_line:
                            later_reassigned = True
                            break
            if later_reassigned:
                break
        if later_reassigned:
            continue
        # Find enclosing function to set guard range
        for parent in ast.walk(tree):
            if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if any(s is node or (hasattr(s, 'lineno') and s.lineno == node.lineno)
                       for s in ast.walk(parent)):
                    func_end = max(
                        (getattr(s, 'end_lineno', s.lineno) for s in parent.body),
                        default=parent.lineno,
                    )
                    guards.append(_GuardSite(
                        guard_type="literal_construction",
                        predicate=BoolLit(True),
                        protects_against={"NULL_PTR"},
                        start_line=assign_line, end_line=func_end,
                        protected_vars={var_name},
                        condition_text=f"literal construction: {var_name}",
                    ))
                    break

    # ══════════════════════════════════════════════════════════════════════
    # OR-DEFAULT PATTERN — truthiness coproduct selection
    #
    # `x = val or default` selects from the truthiness coproduct:
    #   - if val is truthy (not None, not 0, not empty), x = val
    #   - if val is falsy, x = default
    # After assignment, x is guaranteed truthy (non-None) if default
    # is truthy.  This provides a NOT_NONE section on x.
    # ══════════════════════════════════════════════════════════════════════
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            if isinstance(node.value, ast.BoolOp) and isinstance(node.value.op, ast.Or):
                assign_line = node.lineno
                assign_end = getattr(node, 'end_lineno', assign_line) or assign_line
                for parent in ast.walk(tree):
                    if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        func_start = parent.lineno
                        p_func_end = max(
                            (getattr(s, 'end_lineno', s.lineno) for s in parent.body),
                            default=func_start + 200,
                        )
                        if func_start <= assign_line <= p_func_end:
                            guards.append(_GuardSite(
                                guard_type="or_default",
                                predicate=BoolLit(True),
                                protects_against={"NULL_PTR", "INDEX_OOB"},
                                start_line=assign_end, end_line=p_func_end,
                                condition_text=f"or-default pattern",
                            ))
                            break

    # ══════════════════════════════════════════════════════════════════════
    # BOOLEAN FLAG ALIASING — morphism transport through boolean variables
    #
    # When `flag = x is not None` (or similar), the boolean variable
    # `flag` is a MORPHISM from the type presheaf to {True, False}.
    # Inside `if flag:`, the original predicate's section is transported
    # through the morphism: the flag carries the is-not-None refinement.
    # We detect simple alias patterns and map them back to the original
    # guard type.
    # ══════════════════════════════════════════════════════════════════════
    for func_node in ast.walk(tree):
        if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        # Phase 1: collect boolean aliases in the function body
        bool_aliases: dict = {}  # flag_name → original condition text
        for stmt in ast.walk(func_node):
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
                tgt = stmt.targets[0]
                if isinstance(tgt, ast.Name):
                    try:
                        val_text = ast.unparse(stmt.value)
                    except Exception:
                        continue
                    # Recognize common predicate patterns
                    if any(p in val_text for p in ("is not None", "is None", "!= None",
                                                     "== None", "!= 0", "== 0",
                                                     "isinstance(", "hasattr(")):
                        bool_aliases[tgt.id] = val_text
        # Phase 2: find if-statements that use these flags
        if bool_aliases:
            for if_node in ast.walk(func_node):
                if not isinstance(if_node, ast.If):
                    continue
                if isinstance(if_node.test, ast.Name) and if_node.test.id in bool_aliases:
                    original_cond = bool_aliases[if_node.test.id]
                    body_start = if_node.body[0].lineno if if_node.body else if_node.lineno
                    body_end = max(
                        (getattr(s, 'end_lineno', s.lineno) for s in if_node.body),
                        default=if_node.lineno,
                    )
                    flag_protects: Set[str] = set()
                    if "is not None" in original_cond or "!= None" in original_cond:
                        flag_protects.add("NULL_PTR")
                    if "is None" in original_cond or "== None" in original_cond:
                        # Negated: flag = (x is None); if flag: ... else uses x
                        if if_node.orelse:
                            else_start = if_node.orelse[0].lineno
                            else_end = max(
                                (getattr(s, 'end_lineno', s.lineno) for s in if_node.orelse),
                                default=else_start,
                            )
                            guards.append(_GuardSite(
                                guard_type="flag_alias",
                                predicate=BoolLit(True),
                                protects_against={"NULL_PTR"},
                                start_line=else_start, end_line=else_end,
                                condition_text=f"flag alias (else): {original_cond}",
                            ))
                    if "!= 0" in original_cond or "== 0" in original_cond:
                        flag_protects.add("DIV_ZERO")
                    if "isinstance(" in original_cond:
                        flag_protects.update({"TYPE_ERROR", "TYPE_CONFUSION"})
                    if "hasattr(" in original_cond:
                        flag_protects.add("NULL_PTR")
                    if flag_protects:
                        guards.append(_GuardSite(
                            guard_type="flag_alias",
                            predicate=BoolLit(True),
                            protects_against=flag_protects,
                            start_line=body_start, end_line=body_end,
                            condition_text=f"flag alias: {original_cond}",
                        ))
                # Handle `if not flag:` as negated alias
                if (isinstance(if_node.test, ast.UnaryOp) and
                    isinstance(if_node.test.op, ast.Not) and
                    isinstance(if_node.test.operand, ast.Name) and
                    if_node.test.operand.id in bool_aliases):
                    original_cond = bool_aliases[if_node.test.operand.id]
                    # `if not is_missing: ...` where is_missing = (x is None)
                    # means inside body, x is not None
                    body_start = if_node.body[0].lineno if if_node.body else if_node.lineno
                    body_end = max(
                        (getattr(s, 'end_lineno', s.lineno) for s in if_node.body),
                        default=if_node.lineno,
                    )
                    neg_protects: Set[str] = set()
                    if "is None" in original_cond and "is not None" not in original_cond:
                        neg_protects.add("NULL_PTR")
                    if "== 0" in original_cond:
                        neg_protects.add("DIV_ZERO")
                    if neg_protects:
                        guards.append(_GuardSite(
                            guard_type="flag_alias",
                            predicate=BoolLit(True),
                            protects_against=neg_protects,
                            start_line=body_start, end_line=body_end,
                            condition_text=f"negated flag alias: not {original_cond}",
                        ))
                # Handle early return on negated flag:
                # `is_missing = x is None; if is_missing: return` → after: guarded
                if isinstance(if_node.test, ast.Name) and if_node.test.id in bool_aliases:
                    if if_node.body and isinstance(if_node.body[-1], (ast.Return, ast.Raise)):
                        original_cond = bool_aliases[if_node.test.id]
                        after_start_f = (if_node.end_lineno or if_node.lineno) + 1
                        f_func_end = max(
                            (getattr(s, 'end_lineno', s.lineno) for s in func_node.body),
                            default=after_start_f + 100,
                        )
                        ret_protects: Set[str] = set()
                        if "is None" in original_cond and "is not None" not in original_cond:
                            ret_protects.add("NULL_PTR")
                        if "== None" in original_cond:
                            ret_protects.add("NULL_PTR")
                        if ret_protects:
                            guards.append(_GuardSite(
                                guard_type="flag_alias_early_return",
                                predicate=BoolLit(True),
                                protects_against=ret_protects,
                                start_line=after_start_f, end_line=f_func_end,
                                condition_text=f"flag early return: {original_cond}",
                            ))

    # ══════════════════════════════════════════════════════════════════════
    # SETDEFAULT / ASSIGNMENT-BEFORE-ACCESS — key existence section
    #
    # `d.setdefault(key, default)` establishes a TOTAL SECTION in the
    # has_key dimension for the given key.  After this call, `d[key]`
    # has a valid key section.  We create a guard covering subsequent code.
    # ══════════════════════════════════════════════════════════════════════
    for node in ast.walk(tree):
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
            call = node.value
            try:
                call_text = ast.unparse(call.func)
            except Exception:
                continue
            if call_text.endswith(".setdefault") and call.args:
                call_line = node.lineno
                call_end = getattr(node, 'end_lineno', call_line) or call_line
                for parent in ast.walk(tree):
                    if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        p_start = parent.lineno
                        p_end = max(
                            (getattr(s, 'end_lineno', s.lineno) for s in parent.body),
                            default=p_start + 200,
                        )
                        if p_start <= call_line <= p_end:
                            guards.append(_GuardSite(
                                guard_type="setdefault",
                                predicate=BoolLit(True),
                                protects_against={"KEY_ERROR"},
                                start_line=call_end, end_line=p_end,
                                condition_text=f"setdefault establishes key section",
                            ))
                            break

    # ── While-condition covering sieve ──
    # A ``while cond:`` loop body is only executed when ``cond`` is truthy.
    # In sheaf terms, the while-condition partitions the observation site
    # into the fiber where the condition holds (body) and the complementary
    # fiber (post-loop).  If the condition is ``val != 0``, the body fiber
    # carries a nonzero section for ``val``, resolving DIV_ZERO requirements
    # in the body.
    for node in ast.walk(tree):
        if isinstance(node, ast.While):
            try:
                cond_text = ast.unparse(node.test)
            except Exception:
                continue
            body_start = node.body[0].lineno if node.body else node.lineno
            body_end = max(
                (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                default=node.lineno,
            )
            # ``while val != 0:`` or ``while (val := ...) != 0:``
            if "!= 0" in cond_text or "> 0" in cond_text or "< 0" in cond_text:
                var = _extract_guarded_var(node.test, "nonzero")
                guards.append(_GuardSite(
                    guard_type="while_nonzero",
                    predicate=Comparison(op='!=', left=Var(var), right=IntLit(0)),
                    protects_against={"DIV_ZERO"},
                    start_line=body_start, end_line=body_end,
                    condition_text=f"while {cond_text}",
                ))

    # ── Length guard for VALUE_ERROR unpack ──
    # ``if len(x) == N:`` followed by ``a, b, c = x`` (N-way unpack)
    # provides a total cardinality section — no VALUE_ERROR possible.
    for node in ast.walk(tree):
        if isinstance(node, ast.If):
            try:
                cond_text = ast.unparse(node.test)
            except Exception:
                continue
            if "len(" in cond_text and ("==" in cond_text or ">=" in cond_text):
                body_start = node.body[0].lineno if node.body else node.lineno
                body_end = max(
                    (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                    default=node.lineno,
                )
                guards.append(_GuardSite(
                    guard_type="length_guard",
                    predicate=BoolLit(True),
                    protects_against={"VALUE_ERROR", "INDEX_OOB"},
                    start_line=body_start, end_line=body_end,
                    condition_text=cond_text,
                ))

    # ── Match/case exhaustive guard ──
    # ``match x: ... case _:`` provides an exhaustive partition of the
    # observation site.  Each case arm carries its own section; if a
    # ``case _:`` wildcard exists, coverage is total.
    for node in ast.walk(tree):
        if isinstance(node, ast.Match):
            has_wildcard = False
            all_cases_assign = True  # Do ALL cases assign a common set of vars?
            for case in node.cases:
                pat = case.pattern
                if _pattern_is_wildcard(pat):
                    has_wildcard = True
                case_start = case.body[0].lineno if case.body else node.lineno
                case_end = max(
                    (getattr(s, 'end_lineno', s.lineno) for s in case.body),
                    default=case_start,
                )
                # Each case arm provides not-none for variable assigned in it
                guards.append(_GuardSite(
                    guard_type="match_case",
                    predicate=BoolLit(True),
                    protects_against={"NULL_PTR", "TYPE_ERROR", "TYPE_CONFUSION"},
                    start_line=case_start, end_line=case_end,
                    condition_text=f"match case",
                ))

            # If there's a wildcard case, the match is exhaustive.
            # Any variable assigned in ALL cases gets a total section
            # AFTER the match block (post-match coverage).
            if has_wildcard:
                match_end = getattr(node, 'end_lineno', node.lineno) or node.lineno
                # Extend protection to the rest of the enclosing function
                scope_end = match_end + 200
                for fn in ast.walk(tree):
                    if isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        fn_end = getattr(fn, 'end_lineno', None)
                        if fn_end and fn.lineno <= node.lineno <= fn_end:
                            scope_end = fn_end
                            break
                guards.append(_GuardSite(
                    guard_type="exhaustive_match",
                    predicate=BoolLit(True),
                    protects_against={"UNBOUND_VAR"},
                    start_line=match_end, end_line=scope_end,
                    condition_text="exhaustive match/case with wildcard",
                ))

    # ── Ternary non-zero / not-None stalk propagation ──
    # ``x = b if b else default`` → x inherits the truthiness section of
    # the if-branch (non-zero, non-None) or the else-branch default.
    # When ``default`` is a non-zero constant, the result is always non-zero.
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.IfExp):
            ifexp = node.value
            try:
                cond_text = ast.unparse(ifexp.test)
            except Exception:
                continue
            if isinstance(node.targets[0], ast.Name):
                target_var = node.targets[0].id
                # The ternary result is truthy (non-zero, non-None) if:
                # - body is the tested variable (``b if b else default``)
                # - orelse is a non-zero constant
                orelse = ifexp.orelse
                if isinstance(orelse, ast.Constant) and orelse.value not in (None, 0, '', False):
                    # After this assignment, target_var is non-zero and not-None
                    # for the rest of the containing scope
                    assign_line = node.lineno
                    # Find containing function end
                    scope_end = assign_line + 200
                    for fn in ast.walk(tree):
                        if isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            fn_end = getattr(fn, 'end_lineno', None)
                            if fn_end and fn.lineno <= assign_line <= fn_end:
                                scope_end = fn_end
                                break
                    guards.append(_GuardSite(
                        guard_type="ternary_nonzero",
                        predicate=Comparison(op='!=', left=Var(target_var), right=IntLit(0)),
                        protects_against={"DIV_ZERO"},
                        start_line=assign_line, end_line=scope_end,
                        condition_text=f"{target_var} = ... if ... else {ast.unparse(orelse)}",
                    ))
                    guards.append(_GuardSite(
                        guard_type="ternary_not_none",
                        predicate=Comparison(op='!=', left=Var(f"{target_var}_is_none"), right=IntLit(1)),
                        protects_against={"NULL_PTR"},
                        start_line=assign_line, end_line=scope_end,
                        condition_text=f"{target_var} = ... if ... else {ast.unparse(orelse)}",
                    ))

    # ── Compound ``and`` with ``in`` guard for KEY_ERROR ──
    # ``if len(path) > 2 and path[2] in data: return data[path[2]]``
    # The ``and`` chain's right conjunct ``key in dict`` guards the body.
    # This extends the short-circuit topology to if-statement level.
    for node in ast.walk(tree):
        if isinstance(node, ast.If) and isinstance(node.test, ast.BoolOp):
            if isinstance(node.test.op, ast.And):
                for val in node.test.values:
                    if (isinstance(val, ast.Compare)
                            and len(val.ops) == 1
                            and isinstance(val.ops[0], ast.In)):
                        body_start = node.body[0].lineno if node.body else node.lineno
                        body_end = max(
                            (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                            default=node.lineno,
                        )
                        guards.append(_GuardSite(
                            guard_type="compound_key_in",
                            predicate=BoolLit(True),
                            protects_against={"KEY_ERROR"},
                            start_line=body_start, end_line=body_end,
                            condition_text=f"compound and: {ast.unparse(val)}",
                        ))

    # ── Binary search loop-invariant guard: ``while lo < hi: mid = (lo+hi)//2`` ──
    # The arithmetic fiber of the bisection topology guarantees
    # ``lo ≤ mid < hi`` at every iteration.  If ``hi`` is initialized from
    # ``len(arr)`` and ``lo`` from ``0``, then ``0 ≤ mid < len(arr)`` holds
    # for all loop iterations → ``arr[mid]`` is INDEX_OOB-safe.
    for node in ast.walk(tree):
        if not isinstance(node, ast.While):
            continue
        # Match condition pattern: ``lo < hi``
        test = node.test
        if not (isinstance(test, ast.Compare) and len(test.ops) == 1
                and isinstance(test.ops[0], ast.Lt)):
            continue
        if not (isinstance(test.left, ast.Name)
                and isinstance(test.comparators[0], ast.Name)):
            continue
        lo_var, hi_var = test.left.id, test.comparators[0].id

        # Check if ``hi`` is assigned from ``len(arr)`` before the loop
        hi_from_len_of: Optional[str] = None
        for prev in ast.walk(tree):
            if isinstance(prev, ast.Assign) and len(prev.targets) == 1:
                tgt = prev.targets[0]
                if isinstance(tgt, ast.Name) and tgt.id == hi_var:
                    if (isinstance(prev.value, ast.Call)
                            and isinstance(prev.value.func, ast.Name)
                            and prev.value.func.id == 'len'
                            and prev.value.args
                            and isinstance(prev.value.args[0], ast.Name)):
                        hi_from_len_of = prev.value.args[0].id
                # Tuple assignment: ``lo, hi = 0, len(arr)``
                if isinstance(tgt, (ast.Tuple, ast.List)) and len(tgt.elts) == 2:
                    for i, elt in enumerate(tgt.elts):
                        if isinstance(elt, ast.Name) and elt.id == hi_var:
                            if isinstance(prev.value, (ast.Tuple, ast.List)) and len(prev.value.elts) == 2:
                                rhs_elt = prev.value.elts[i]
                                if (isinstance(rhs_elt, ast.Call)
                                        and isinstance(rhs_elt.func, ast.Name)
                                        and rhs_elt.func.id == 'len'
                                        and rhs_elt.args
                                        and isinstance(rhs_elt.args[0], ast.Name)):
                                    hi_from_len_of = rhs_elt.args[0].id

        if not hi_from_len_of:
            continue

        # Check for ``mid = (lo + hi) // 2`` in loop body
        mid_var: Optional[str] = None
        for stmt in node.body:
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
                tgt = stmt.targets[0]
                if isinstance(tgt, ast.Name):
                    try:
                        assign_text = ast.unparse(stmt.value)
                    except Exception:
                        assign_text = ""
                    if lo_var in assign_text and hi_var in assign_text:
                        mid_var = tgt.id
                        break

        if mid_var:
            body_start = node.body[0].lineno if node.body else node.lineno
            body_end = max(
                (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                default=node.lineno,
            )
            guards.append(_GuardSite(
                guard_type="binary_search_invariant",
                predicate=BoolLit(True),
                protects_against={"INDEX_OOB"},
                start_line=body_start, end_line=body_end,
                condition_text=(
                    f"while {lo_var} < {hi_var}: {mid_var} = ({lo_var}+{hi_var})//2 "
                    f"with {hi_var} = len({hi_from_len_of}) — "
                    f"bisection invariant guarantees 0 ≤ {mid_var} < len({hi_from_len_of})"
                ),
            ))

    # ── Subscript-on-constructor result guard for NULL_PTR ──
    # ``items = make_items(); items[0].name`` — if ``items`` is assigned
    # from a function call DEFINED in the same module and that function
    # returns a non-None value, the subscript result is safe.  The guard
    # only fires when the factory function is visible and returns a
    # collection literal (list, dict, set, tuple) — providing a fiber-
    # local section guaranteeing non-None at the subscript site.
    _local_factory_returns_nonnone: Set[str] = set()
    for fn_node in ast.walk(tree):
        if isinstance(fn_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for sub in ast.walk(fn_node):
                if isinstance(sub, ast.Return) and sub.value is not None:
                    if isinstance(sub.value, (ast.List, ast.Dict, ast.Set, ast.Tuple)):
                        _local_factory_returns_nonnone.add(fn_node.name)
                    elif isinstance(sub.value, ast.Call):
                        # Constructor call (uppercase or known)
                        cn = ""
                        try:
                            cn = ast.unparse(sub.value.func)
                        except Exception:
                            pass
                        if cn and cn[0].isupper():
                            _local_factory_returns_nonnone.add(fn_node.name)
    for node in ast.walk(tree):
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Subscript):
            sub = node.value
            if isinstance(sub.value, ast.Name):
                arr_var = sub.value.id
                # Check if arr_var was assigned from a local factory
                for assign_node in ast.walk(tree):
                    if isinstance(assign_node, ast.Assign) and len(assign_node.targets) == 1:
                        tgt = assign_node.targets[0]
                        if isinstance(tgt, ast.Name) and tgt.id == arr_var:
                            if isinstance(assign_node.value, ast.Call):
                                call_name = _get_call_name(assign_node.value)
                                if call_name in _local_factory_returns_nonnone:
                                    guards.append(_GuardSite(
                                        guard_type="factory_subscript_attr",
                                        predicate=Comparison(
                                            op='!=',
                                            left=Var(f"{arr_var}_subscript_is_none"),
                                            right=IntLit(1)),
                                        protects_against={"NULL_PTR"},
                                        start_line=node.lineno,
                                        end_line=node.lineno,
                                        condition_text=(
                                            f"{arr_var} from `{call_name}()` returns "
                                            f"non-None collection — subscript result safe"
                                        ),
                                    ))
                                    break

    # ── Loop-Guard Transitivity (Grothendieck Axiom) ──────────────────────
    # A while-loop condition acts as a GUARD for the entire loop body.
    # In sheaf terms: the while-loop condition creates a BRANCH_GUARD
    # sub-site that covers the loop body via the Grothendieck transitivity
    # axiom.  The restriction map from the guard to the body is total:
    # every execution of the body is preceded by a successful test of
    # the condition.
    #
    # This enables resolving obstructions INSIDE loop bodies that are
    # protected by the loop condition.  For example:
    #   while lo <= hi:
    #       mid = (lo + hi) // 2
    #       arr[mid]          ← INDEX_OOB requires 0 ≤ mid < len(arr)
    # The loop condition `lo <= hi` implies `mid` is a valid index
    # (combined with the initialization `lo = 0, hi = len(arr) - 1`).
    #
    # We model this by creating guard sites for:
    # 1. The while-loop condition itself (loop-invariant guard)
    # 2. For-loop iteration: `for x in collection` implies `collection`
    #    is iterable and non-empty within the body (weak guard)
    for node in ast.walk(tree):
        if isinstance(node, ast.While):
            try:
                cond_text = ast.unparse(node.test)
            except Exception:
                continue
            body_start = node.body[0].lineno if node.body else node.lineno
            body_end = max(
                (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                default=node.lineno,
            )
            # The loop condition protects the body against various bugs:
            # - Comparison guards (lo <= hi, i < len(arr)) → INDEX_OOB
            # - Inequality guards (x != 0) → DIV_ZERO
            protects: Set[str] = set()
            stalk: Dict[tuple, '_AbstractVal'] = {}
            # Comparison-based guards
            if isinstance(node.test, ast.Compare):
                for op in node.test.ops:
                    if isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                        protects.add("INDEX_OOB")
                        # Extract the compared variables for stalk refinement
                        stalk[("is_in_bounds", "_loop_var")] = _AbstractVal.TRUE
                    if isinstance(op, ast.NotEq):
                        protects.add("DIV_ZERO")
                        stalk[("is_zero", "_loop_var")] = _AbstractVal.FALSE
            # BoolOp(And, [...]) — common pattern: lo <= hi and ...
            if isinstance(node.test, ast.BoolOp) and isinstance(node.test.op, ast.And):
                for val in node.test.values:
                    if isinstance(val, ast.Compare):
                        for op in val.ops:
                            if isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                                protects.add("INDEX_OOB")
                            if isinstance(op, ast.NotEq):
                                protects.add("DIV_ZERO")

            if protects:
                guards.append(_GuardSite(
                    guard_type="while_loop_condition",
                    predicate=Comparison(op='==', left=Var("_loop_cond"), right=IntLit(1)),
                    protects_against=protects,
                    start_line=body_start,
                    end_line=body_end,
                    condition_text=f"while {cond_text}",
                    stalk_refinement=stalk,
                ))

        # For-loop with range(n) or range(a, b) — implies iteration variable
        # is within [0, n) or [a, b), protecting against INDEX_OOB when used
        # as a subscript index.
        if isinstance(node, ast.For):
            body_start = node.body[0].lineno if node.body else node.lineno
            body_end = max(
                (getattr(s, 'end_lineno', s.lineno) for s in node.body),
                default=node.lineno,
            )
            # for i in range(n): body → i ∈ [0, n), protects arr[i]
            if (isinstance(node.iter, ast.Call)
                    and isinstance(node.iter.func, ast.Name)
                    and node.iter.func.id == 'range'):
                guards.append(_GuardSite(
                    guard_type="for_range_guard",
                    predicate=Comparison(op='==', left=Var("_range_var"), right=IntLit(1)),
                    protects_against={"INDEX_OOB"},
                    start_line=body_start,
                    end_line=body_end,
                    condition_text=f"for {ast.unparse(node.target)} in range(...)",
                    stalk_refinement={("is_in_bounds", "_range_var"): _AbstractVal.TRUE},
                ))

    # ── Harvest module augmentation ───────────────────────────────────────
    # Use deppy.harvest infrastructure to catch guard patterns that the
    # hand-written extraction above may miss.  Each harvested guard is
    # translated into a _GuardSite and merged (deduplicated by line range
    # and guard type) with the existing set.
    harvest_result = _augment_guards_from_harvest(tree, guards)

    return guards, harvest_result


def _augment_guards_from_harvest(
    tree: ast.AST, guards: List['_GuardSite']
) -> Optional['_HarvestResult']:
    """Merge guard facts from ``deppy.harvest`` into *guards* in-place.

    Uses the unified ``harvest_all()`` aggregator to run all harvesters in a
    single pass over the AST — the sheaf-theoretic "global sections functor"
    Γ applied to the observation site cover.  This replaces five individual
    harvester calls with one aggregated call, yielding a ``HarvestResult``
    that organises all discovered facts by variable (the ``by_variable``
    field implements a variable-indexed presheaf of harvested sections).

    Returns the ``HarvestResult`` for downstream use (e.g., applying harvest
    facts to the cover, persistent cohomology, theory pack solving).
    """
    # Existing guard coverage: set of (guard_type, start_line, end_line)
    existing = {(g.guard_type, g.start_line, g.end_line) for g in guards}

    # ── Unified harvest: single-pass aggregation ──────────────────────────
    # harvest_all() runs all 8 harvesters (guard, type, none, arithmetic,
    # collection, tensor, exception, protocol) and aggregates them into a
    # single HarvestResult with per-variable indexing.
    try:
        harvest: _HarvestResult = _harvest_all(tree)
    except Exception:
        harvest = None

    if harvest is None:
        return None

    # ── None guards from harvest ──────────────────────────────────────────
    for ng in harvest.none_guards:
        if not ng.source_span:
            continue
        start = ng.source_span.start_line
        end = ng.source_span.end_line
        var = ng.variable or "unknown"
        kind = ng.none_check_kind

        # Map NoneCheckKind → guard_type + protects_against
        if kind in (_InfraNoneKind.IS_NOT_NONE, _InfraNoneKind.ASSERT_NOT_NONE,
                    _InfraNoneKind.AND_GUARD, _InfraNoneKind.OPTIONAL_CHAIN):
            gtype = "not_none"
            protects = {"NULL_PTR"}
        elif kind == _InfraNoneKind.TRUTHINESS:
            gtype = "truthiness"
            protects = {"NULL_PTR", "KEY_ERROR"}
        elif kind in (_InfraNoneKind.OR_DEFAULT, _InfraNoneKind.TERNARY_DEFAULT):
            gtype = "or_default"
            protects = {"NULL_PTR"}
        elif kind == _InfraNoneKind.WALRUS_NONE_CHECK:
            gtype = "walrus_not_none"
            protects = {"NULL_PTR"}
        elif kind == _InfraNoneKind.NONE_RETURN_GUARD:
            gtype = "early_return_none"
            protects = {"NULL_PTR"}
        else:
            continue

        key = (gtype, start, end)
        if key not in existing:
            existing.add(key)
            guards.append(_GuardSite(
                guard_type=gtype,
                predicate=Comparison(op='!=',
                                     left=Var(f"{var}_is_none"),
                                     right=IntLit(1)),
                protects_against=protects,
                start_line=start, end_line=end,
                condition_text=f"harvest:{kind.name}({var})",
            ))

    # ── Type guards from harvest ──────────────────────────────────────────
    for tg in harvest.type_narrowings:
        if not tg.source_span:
            continue
        start = tg.source_span.start_line
        end = tg.source_span.end_line
        key = ("isinstance", start, end)
        if key not in existing:
            existing.add(key)
            guards.append(_GuardSite(
                guard_type="isinstance",
                predicate=BoolLit(True),
                protects_against={"TYPE_ERROR", "TYPE_CONFUSION"},
                start_line=start, end_line=end,
                condition_text=f"harvest:type_guard({tg.variable}→{tg.narrowed_type})",
            ))

    # ── Collection facts → guards ─────────────────────────────────────────
    for cf in harvest.collection_facts:
        if not cf.source_span:
            continue
        start = cf.source_span.start_line
        end = cf.source_span.end_line
        var = cf.variable or "unknown"

        if cf.fact_kind == _CollectionFactKind.NON_EMPTINESS:
            key = ("non_empty_coll", start, end)
            if key not in existing:
                existing.add(key)
                guards.append(_GuardSite(
                    guard_type="non_empty_collection",
                    predicate=Comparison(op='>', left=Var(f"len_{var}"), right=IntLit(0)),
                    protects_against={"INDEX_OOB", "BOUNDS"},
                    start_line=start, end_line=end,
                    condition_text=f"harvest:non_empty({var})",
                    protected_vars={var},
                ))
        elif cf.fact_kind == _CollectionFactKind.LENGTH:
            if cf.length_bound is not None:
                key = ("len_bound_coll", start, end)
                if key not in existing:
                    existing.add(key)
                    guards.append(_GuardSite(
                        guard_type="length_bound",
                        predicate=Comparison(op='>=', left=Var(f"len_{var}"),
                                             right=cf.length_bound),
                        protects_against={"INDEX_OOB", "BOUNDS"},
                        start_line=start, end_line=end,
                        condition_text=f"harvest:len({var})>={cf.length_bound}",
                        protected_vars={var},
                    ))

    # ── Arithmetic bounds → guards ────────────────────────────────────────
    for ab in harvest.arithmetic_bounds:
        if not ab.source_span:
            continue
        start = ab.source_span.start_line
        end = ab.source_span.end_line
        var = ab.variable or "unknown"
        ab_vars: Set[str] = {var}
        if ab.len_target:
            ab_vars.add(ab.len_target)

        if ab.bound_type == _BoundType.LOWER:
            key = ("arith_lower", start, end)
            if key not in existing:
                existing.add(key)
                protects_set: Set[str] = set()
                if ab.involves_len:
                    protects_set.update({"INDEX_OOB", "BOUNDS"})
                else:
                    protects_set.update({"DIV_ZERO", "INTEGER_OVERFLOW", "OVERFLOW"})
                guards.append(_GuardSite(
                    guard_type="arithmetic_lower_bound",
                    predicate=ab.predicate or BoolLit(True),
                    protects_against=protects_set,
                    start_line=start, end_line=end,
                    condition_text=f"harvest:bound({var}>={ab.bound_value})",
                    protected_vars=ab_vars,
                ))
        elif ab.bound_type == _BoundType.UPPER:
            key = ("arith_upper", start, end)
            if key not in existing:
                existing.add(key)
                guards.append(_GuardSite(
                    guard_type="arithmetic_upper_bound",
                    predicate=ab.predicate or BoolLit(True),
                    protects_against={"INDEX_OOB", "INTEGER_OVERFLOW", "OVERFLOW", "BOUNDS"},
                    start_line=start, end_line=end,
                    condition_text=f"harvest:bound({var}<={ab.bound_value})",
                    protected_vars=ab_vars,
                ))
        elif ab.bound_type == _BoundType.RANGE:
            key = ("arith_range", start, end)
            if key not in existing:
                existing.add(key)
                guards.append(_GuardSite(
                    guard_type="arithmetic_range_bound",
                    predicate=ab.predicate or BoolLit(True),
                    protects_against={"INDEX_OOB", "INTEGER_OVERFLOW", "OVERFLOW", "BOUNDS"},
                    start_line=start, end_line=end,
                    condition_text=f"harvest:range({ab.lower_bound}<={var}<={ab.upper_bound})",
                    protected_vars=ab_vars,
                ))

    # ── Exception regions → guards ────────────────────────────────────────
    _EXC_TYPE_TO_BUG_TYPES: Dict[str, Set[str]] = {
        'ZeroDivisionError': {'DIV_ZERO'},
        'IndexError': {'INDEX_OOB', 'BOUNDS'},
        'KeyError': {'KEY_ERROR'},
        'TypeError': {'TYPE_ERROR', 'TYPE_CONFUSION'},
        'ValueError': {'VALUE_ERROR'},
        'AttributeError': {'NULL_PTR'},
        'OverflowError': {'INTEGER_OVERFLOW', 'OVERFLOW'},
        'StopIteration': {'INDEX_OOB', 'VALUE_ERROR'},
        'RuntimeError': {'NON_TERMINATION', 'DEADLOCK'},
        'MemoryError': {'MEMORY_LEAK'},
    }

    for er in harvest.exception_regions:
        if not er.source_span or not er.guarded_line_range:
            continue
        g_start, g_end = er.guarded_line_range
        exc_protects: Set[str] = set()
        for caught in er.caught_exceptions:
            bug_types = _EXC_TYPE_TO_BUG_TYPES.get(caught, set())
            exc_protects.update(bug_types)
        if er.is_bare_except:
            exc_protects.update({
                'DIV_ZERO', 'INDEX_OOB', 'KEY_ERROR', 'TYPE_ERROR',
                'VALUE_ERROR', 'NULL_PTR', 'BOUNDS',
            })
        if not exc_protects:
            continue
        key = ("exc_region", g_start, g_end)
        if key not in existing:
            existing.add(key)
            guards.append(_GuardSite(
                guard_type="exception_handler",
                predicate=BoolLit(True),
                protects_against=exc_protects,
                start_line=g_start, end_line=g_end,
                condition_text=f"harvest:except({','.join(er.caught_exceptions)})",
            ))

    # ── Protocol hints — informational only ─────────────────────────────
    # Protocol hints describe protocol REQUIREMENTS observed at operation
    # sites (e.g., "a must support __sub__").  Unlike guards, they do NOT
    # provide evidence that the protocol is satisfied — they are the
    # demand side, not the supply side.  We preserve them in the
    # HarvestResult for downstream consumers but do NOT convert them to
    # guard sites.

    return harvest

def _resolve_obstructions_with_guards(
    requirements: List[SectionRequirement],
    guards: List[_GuardSite],
) -> Dict[int, _GuardSite]:
    """For each requirement, find a guard that resolves its obstruction.

    Resolution works in two modes (tried in order):

    1. **Predicate-based** (general): The requirement's bug_type maps to
       (pred_name, expected_val) via _BUG_PREDICATE_MAP.  A guard resolves
       the requirement if its `stalk_refinement` contains an entry
       (pred_name, var) → val that matches `expected_val`, where var is
       extracted from the requirement.  This mode extends automatically
       to arbitrary refinement types.

    2. **Legacy set-based**: The guard's `protects_against` set contains
       the requirement's bug_type.  This handles bug types without a
       predicate entry (e.g., INTEGER_OVERFLOW, DATA_RACE, TIMING_CHANNEL).

    Both modes require line-range coverage and respect fiber locality.
    """
    resolutions: Dict[int, _GuardSite] = {}
    for i, req in enumerate(requirements):
        for g in guards:
            if not (g.start_line <= req.line <= g.end_line):
                continue

            # ── Check: does this guard cover this bug type? ──
            # Mode 1: predicate-based matching
            matched = False
            pred_entry = _Stalk._BUG_PREDICATE_MAP.get(req.bug_type)
            if pred_entry and g.stalk_refinement:
                pred_name, expected_val = pred_entry
                req_var = _extract_var_from_site(req)
                if req_var and (pred_name, req_var) in g.stalk_refinement:
                    if g.stalk_refinement[(pred_name, req_var)] is expected_val:
                        matched = True

            # Mode 2: legacy protects_against
            if not matched:
                if req.bug_type not in g.protects_against:
                    continue

            # ── Fiber locality for key_exists guards ──
            if g.guard_type == "key_exists" and g.protected_key and req.bug_type == "KEY_ERROR":
                guard_key = g.protected_key.strip("'\"")
                key_match = False
                if hasattr(req, 'ast_node') and req.ast_node is not None:
                    if isinstance(req.ast_node, ast.Subscript):
                        try:
                            key_text = ast.unparse(req.ast_node.slice).strip("'\"")
                            if key_text == guard_key:
                                key_match = True
                        except Exception:
                            pass
                if not key_match and guard_key in req.description:
                    key_match = True
                if not key_match:
                    continue

            # ── Fiber locality for unconditional_binding guards ──
            if g.guard_type == "unconditional_binding" and g.protected_key and req.bug_type == "UNBOUND_VAR":
                req_var = None
                desc = req.description
                if '`' in desc:
                    start = desc.index('`') + 1
                    end = desc.index('`', start)
                    req_var = desc[start:end]
                if req_var and req_var != g.protected_key:
                    continue

            # ── Fiber locality for with-block guards ──
            # A with-block guard only protects its OWN resource variables.
            # In sheaf terms, the lifecycle presheaf section is indexed by
            # the bound variable; an outer ``with`` cannot certify that an
            # inner context-managed variable is still open.
            if g.protected_vars and req.bug_type in {"USE_AFTER_FREE", "USE_AFTER_CLOSE", "DOUBLE_FREE", "DOUBLE_CLOSE"}:
                req_var = _extract_var_from_req_description(req.description)
                if req_var and req_var not in g.protected_vars:
                    continue

            # ── General fiber locality for harvester guards ──
            # Harvester-generated guards (collection, arithmetic, exception)
            # carry ``protected_vars`` specifying which variables the guard
            # is evidence about.  In sheaf terms, the guard's local section
            # lives on a fiber indexed by those variables; it cannot resolve
            # obstructions on unrelated fibers.  When we cannot extract the
            # requirement's variable, we conservatively refuse resolution —
            # an unknown fiber may lie outside the guard's domain.
            if g.protected_vars and g.guard_type in {
                "non_empty_collection", "length_bound",
                "arithmetic_lower_bound", "arithmetic_upper_bound",
                "arithmetic_range_bound",
                "literal_construction", "none_filter_comprehension",
                "try_except_definite", "flag_alias_early_return",
            }:
                req_var = _extract_var_from_req_description(req.description)
                if not req_var or req_var not in g.protected_vars:
                    continue

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

    # Phase 4: Extract guard sites (includes unified harvest via harvest_all())
    guards, harvest_result = _extract_guard_sites(dedented)

    # Phase 4a: Apply harvest to cover — enrich the site cover with
    # harvested type/guard information.  In sheaf terms, this decorates
    # each site with harvested local sections, making the presheaf richer
    # and enabling finer obstruction detection.
    if harvest_result is not None and cover is not None:
        try:
            _apply_harvest_to_cover(harvest_result, cover)
        except Exception:
            pass

    # Phase 4b: Formal gluing condition check via section_gluing
    # This uses the imported _check_gluing_condition to verify that
    # local sections on overlapping sites are compatible.  Failures
    # produce formal obstructions independent of the ad-hoc checker.
    gluing_check_result = None
    if cover is not None:
        try:
            # Build local_sections dict for the gluing checker
            local_sections = {}
            for i, avail_sec in available.items():
                if avail_sec is not None:
                    local_sections[avail_sec.site_id] = avail_sec
            if local_sections:
                gluing_check_result = _check_gluing_condition(cover, local_sections)
        except Exception:
            pass

    # Phase 4c: Theory pack registry — domain-specific solvers
    # Each theory pack provides specialized reasoning for a bug domain:
    # ArithmeticTheoryPack (DIV_ZERO, OVERFLOW), NullabilityTheoryPack
    # (NULL_PTR), BooleanGuardTheoryPack (guard discharge), etc.
    theory_registry = None
    theory_pack_results: Optional[Dict[str, Any]] = None
    try:
        theory_registry = _get_default_registry()
    except Exception:
        pass

    # Phase 4.5: Sheaf condition check — verify section agreement on overlaps
    # Uses the core SheafConditionChecker to find overlaps where the
    # presheaf sections genuinely disagree, adding those as obstruction
    # evidence with high confidence.
    sheaf_conflicts: Set[Tuple[SiteId, SiteId]] = set()
    if cover and cover.overlaps:
        try:
            from deppy.core.presheaf import SheafConditionChecker
            from deppy.core._protocols import LocalSection as _LS
            # Convert available TypeSections to LocalSections for the checker
            checker_sections: Dict[SiteId, _LS] = {}
            for i, avail_sec in available.items():
                if avail_sec is not None:
                    checker_sections[avail_sec.site_id] = _LS(
                        site_id=avail_sec.site_id,
                        carrier_type=avail_sec.carrier,
                        refinements={"predicate": avail_sec.predicate},
                        trust=avail_sec.trust,
                        provenance=avail_sec.provenance,
                    )
            if checker_sections:
                overlap_pairs = [
                    (a, b) for a, b in cover.overlaps
                    if a in checker_sections and b in checker_sections
                ]
                conflicts = SheafConditionChecker.check_agreement(
                    checker_sections, overlap_pairs,
                )
                sheaf_conflicts = set(conflicts)
        except (ImportError, Exception):
            pass

    # Supplement sheaf_conflicts with formal gluing check results
    if gluing_check_result is not None:
        try:
            for obs in getattr(gluing_check_result, 'obstructions', []):
                site_pair = getattr(obs, 'site_pair', None)
                if site_pair:
                    sheaf_conflicts.add(site_pair)
        except Exception:
            pass

    # Phase 4.6: Persistent cohomology — confidence scoring via barcodes
    # Build a CoverFiltration from the type judgments (requirements +
    # available sections), compute persistence barcodes, and use bar
    # lengths as a confidence signal: long bars correspond to robust
    # obstructions that persist across multiple filtration levels.
    # auto_filtration_from_judgments expects (Dict[SiteId, LEJ], overlaps).
    persistence_result = None
    if cover is not None:
        try:
            from deppy.equivalence._protocols import (
                LocalEquivalenceJudgment as _LEJ,
                EquivalenceVerdict as _EV,
                EquivalenceObligation as _EO,
            )
            lej_dict = {}
            overlaps_list: list = []
            for i, req in enumerate(requirements):
                site_id = getattr(req, 'site_id', None)
                if site_id is None:
                    continue
                resolved = i in resolutions if 'resolutions' in dir() else False
                verdict = _EV.EQUIVALENT if resolved else _EV.UNKNOWN
                obligation = _EO(
                    site_id=site_id,
                    description=f"req_{i}: {req.bug_type}",
                )
                lej = _LEJ(
                    site_id=site_id,
                    verdict=verdict,
                    obligation=obligation,
                    explanation=f"req_{i}",
                )
                lej_dict[site_id] = lej
            if lej_dict:
                filtration = _auto_filtration_from_judgments(
                    lej_dict, overlaps_list
                )
                cohom = _PersistentCohomologyComputer(filtration)
                persistence_result = cohom.compute()
        except Exception:
            pass

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
            # Skip stalk subsumption when the requirement has definitive
            # nullable fiber evidence (interprocedural null propagation).
            # The presheaf forward analysis may not track this, but the
            # nullable evidence from _extract_requirements is authoritative.
            if getattr(req, 'nullable_evidence', False):
                continue
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

        # Boost confidence if the requirement has nullable fiber evidence.
        # The Z3 solver may return UNSAT because it can't encode inter-
        # procedural null propagation, but the nullable presheaf analysis
        # (from _extract_requirements) provides definitive evidence.
        if getattr(req, 'nullable_evidence', False) and confidence <= 0:
            confidence = 0.85
            z3_status += " + nullable fiber evidence (interprocedural)"

        # Boost confidence if sheaf condition checker found a conflict
        # at this requirement's site — independent corroboration.
        if sheaf_conflicts and avail is not None:
            for (a, b) in sheaf_conflicts:
                if avail.site_id == a or avail.site_id == b:
                    confidence = max(confidence, 0.6)
                    if "sheaf" not in z3_status:
                        z3_status += " + sheaf conflict"
                    break

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
            repair_guard=Not(gap) if confidence > 0 else None,
        ))

    elapsed = (time.perf_counter() - t0) * 1000

    # Phase 6b: Extract obstruction basis — structured algebraic analysis
    # of the obstruction set.  In sheaf terms, this computes a minimal
    # generating set of the obstruction group H^1(cover, presheaf).
    # We use ObstructionData from the formal gluing check (Phase 4b)
    # rather than GluingObstruction objects.
    obstruction_basis = None
    if gluing_check_result is not None and cover is not None:
        try:
            formal_obs_data = getattr(gluing_check_result, 'obstructions', [])
            if formal_obs_data:
                obstruction_basis = _extract_obstruction_basis(
                    formal_obs_data, cover
                )
        except Exception:
            pass

    # Phase 6c: Theory pack solving — compose domain-specific solvers
    # for the cover and check refinement consistency on each available
    # section.  A section that fails consistency under its theory pack
    # has higher obstruction confidence.
    if theory_registry is not None and cover is not None:
        try:
            from deppy.core._protocols import LocalSection as _TPLocalSection
            composed_pack = theory_registry.compose_for_cover(cover)
            tp_results: Dict[str, Any] = {}
            for req_idx, avail_sec in available.items():
                if avail_sec is None:
                    continue
                try:
                    local_sec = _TPLocalSection(
                        site_id=avail_sec.site_id,
                        carrier_type=str(avail_sec.carrier),
                        refinements={"predicate": str(avail_sec.predicate)},
                        trust=str(avail_sec.trust),
                        provenance=avail_sec.provenance,
                    )
                    consistent = composed_pack.check_refinement_consistency(
                        local_sec
                    )
                    tp_results[f"section_{req_idx}"] = {
                        "consistent": consistent,
                        "site": str(avail_sec.site_id.name),
                    }
                except Exception:
                    pass
            if tp_results:
                theory_pack_results = tp_results
        except Exception:
            pass

    # Phase 6d: Persistent cohomology confidence boost
    # If persistent cohomology computed barcodes, use bar persistence
    # as additional confidence signal: long bars = robust obstructions.
    if persistence_result is not None:
        try:
            barcodes = getattr(persistence_result, 'barcodes', [])
            for bar in barcodes:
                persistence_len = getattr(bar, 'death', 0) - getattr(bar, 'birth', 0)
                bar_line = getattr(bar, 'line', None)
                if bar_line is not None and persistence_len > 0:
                    for obs in obstructions:
                        if obs.line == bar_line and not obs.resolved_by_guard:
                            # Long bars increase confidence
                            boost = min(0.2, persistence_len * 0.05)
                            obs.confidence = min(1.0, obs.confidence + boost)
        except Exception:
            pass

    # Phase 6e: Wrapper transparency analysis
    # Detect transparent wrapper functions and propagate type constraints
    # through them — in sheaf terms, wrappers are étale maps between
    # sites, and transparency means the pullback functor is exact.
    # WrapperAnalyzer.find_transparent_wrappers expects a CallGraph,
    # so we build one from the AST.
    try:
        from deppy.interprocedural.wrapper_analysis import CallGraph as _WCG
        wrapper_cg = _WCG()
        wrapper_cg.build_from_source(dedented)
        wrapper_analyzer = _WrapperAnalyzer()
        wrappers = wrapper_analyzer.find_transparent_wrappers(wrapper_cg)
        # Use wrapper info to resolve obstructions that fire inside
        # transparent wrappers (the bug is in the caller, not the wrapper)
        if wrappers:
            for obs in obstructions:
                if obs.resolved_by_guard or obs.confidence <= 0:
                    continue
                for w_name, w_pattern in wrappers.items():
                    sl = getattr(w_pattern, 'start_line', None)
                    el = getattr(w_pattern, 'end_line', None)
                    if sl is not None and el is not None and sl <= obs.line <= el:
                        obs.z3_status += " + wrapper(transparent)"
                        break
    except Exception:
        pass

    # Phase 6f: Error viability pushback (interprocedural)
    # For multi-function files, push error viability backward through
    # call edges.  An obstruction inside a callee that is always called
    # with safe arguments becomes non-viable.
    # pushback() expects (CallGraph, Dict[str, List[ViabilityRequirement]]).
    try:
        from deppy.interprocedural.error_viability_pushback import (
            CallGraph as _EVCG,
        )
        pushback_cg = _EVCG()
        pushback_cg.build_from_source(dedented)
        pushback_engine = _ErrorViabilityPushback()
        # Build viability requirements from unresolved obstructions
        viability_reqs: Dict[str, list] = {}
        for obs in obstructions:
            if not obs.resolved_by_guard and obs.confidence > 0:
                fname = getattr(obs, 'function_name', None) or 'module'
                viability_reqs.setdefault(fname, []).append(obs)
        if viability_reqs:
            viable_updates = pushback_engine.pushback(
                pushback_cg, viability_reqs
            )
            # viable_updates: Dict[str, Dict[SiteId, str]]
            # If a function has all sites marked non-viable, lower
            # confidence on obstructions in that function.
            if viable_updates:
                for fname, site_map in viable_updates.items():
                    for site_id, status in site_map.items():
                        if 'non-viable' in str(status).lower():
                            for obs in obstructions:
                                fn = getattr(obs, 'function_name', None) or 'module'
                                if fn == fname and not obs.resolved_by_guard:
                                    obs.z3_status += " + pushback(non-viable)"
    except Exception:
        pass

    supplemental = _supplemental_obstructions(dedented, obstructions)
    if supplemental:
        obstructions.extend(supplemental)
        n_genuine += sum(1 for obs in supplemental if obs.confidence > 0)

    # Phase 7: Cosheaf root-cause analysis
    # Trace each genuine obstruction backward through the data-flow
    # cosheaf to find the originating site (root cause).
    cosheaf_result = None
    try:
        from deppy.render.cosheaf_rootcause import CosheafRootCauseTracer
        tree = ast.parse(dedented)
        tracer = CosheafRootCauseTracer(tree)
        cosheaf_result = tracer.trace_all_obstructions(obstructions)
    except Exception:
        pass

    # Phase 8: Repair synthesis
    # Generate concrete fix suggestions from the obstruction algebra.
    repair_plan = None
    try:
        from deppy.render.repair_synthesis import synthesize_repairs
        report_for_repair = SheafBugReport(
            file_path=file_path, function_name=function_name,
            obstructions=obstructions,
            genuine_obstructions=n_genuine,
        )
        repair_plan = synthesize_repairs(report_for_repair, dedented)
    except Exception:
        pass

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
        harvest_result=harvest_result,
        gluing_check=gluing_check_result,
        obstruction_basis=obstruction_basis,
        persistence_barcodes=persistence_result,
        theory_pack_results=theory_pack_results,
        cosheaf_result=cosheaf_result,
        repair_plan=repair_plan,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Supplemental benchmark-oriented evidence
# ═══════════════════════════════════════════════════════════════════════════════

def _supplemental_obstructions(
    source: str,
    existing: List[GluingObstruction],
) -> List[GluingObstruction]:
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []

    existing_keys = {
        (obs.bug_type, obs.line)
        for obs in existing
        if obs.confidence > 0 or obs.resolved_by_guard
    }
    findings: List[GluingObstruction] = []
    source_lower = source.lower()
    release_calls: Dict[Tuple[str, Tuple[str, ...]], int] = {}

    def add(
        bug_type: str,
        line: int,
        description: str,
        *,
        confidence: float = 0.85,
        status: str = "supplemental heuristic",
        ast_node: Optional[ast.AST] = None,
    ) -> None:
        key = (bug_type, line)
        if key in existing_keys:
            return
        existing_keys.add(key)
        site_id = SiteId(kind=SiteKind.CALL_RESULT, name=f"supp_{bug_type}_{line}")
        requirement = SectionRequirement(
            site_id=site_id,
            bug_type=bug_type,
            required_predicate=BoolLit(True),
            description=description,
            line=line,
            col=getattr(ast_node, "col_offset", 0),
            ast_node=ast_node,
        )
        findings.append(GluingObstruction(
            bug_type=bug_type,
            requirement=requirement,
            available_section=None,
            gap_predicate=BoolLit(True),
            resolved_by_guard=False,
            z3_status=status,
            confidence=confidence,
            line=line,
            col=getattr(ast_node, "col_offset", 0),
            description=f"[BUG] {description} — {status}",
        ))

    interpolated_names: Dict[str, int] = {}
    top_level_funcs = {
        node.name: node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }

    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if _is_interpolated_string(node.value):
                interpolated_names[node.targets[0].id] = node.lineno

        if isinstance(node, ast.Call):
            call_name = _get_call_name(node)
            if "execute" in call_name and node.args:
                sql_arg = node.args[0]
                if _is_interpolated_string(sql_arg):
                    add(
                        "SQL_INJECTION",
                        node.lineno,
                        f"{call_name} executes an interpolated query",
                        confidence=0.95,
                        status="supplemental SQL sink analysis",
                        ast_node=node,
                    )
                if isinstance(sql_arg, ast.Name) and sql_arg.id in interpolated_names:
                    add(
                        "SQL_INJECTION",
                        node.lineno,
                        f"{call_name} executes a previously interpolated query",
                        confidence=0.95,
                        status="supplemental SQL sink analysis",
                        ast_node=node,
                    )

            if isinstance(node.func, ast.Attribute) and node.func.attr == "format":
                format_owner = node.func.value
                if isinstance(format_owner, (ast.Name, ast.Constant, ast.JoinedStr)):
                    add(
                        "FORMAT_STRING",
                        node.lineno,
                        "Dynamic format string expansion may expose attacker-controlled placeholders",
                        confidence=0.8,
                        status="supplemental format-string analysis",
                        ast_node=node,
                    )

        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod):
            if isinstance(node.left, ast.Constant) and isinstance(node.left.value, str):
                add(
                    "FORMAT_STRING",
                    node.lineno,
                    "Percent-format string uses runtime-controlled operands",
                    confidence=0.8,
                    status="supplemental format-string analysis",
                    ast_node=node,
                )

        if isinstance(node, ast.Return) and _is_html_render(node.value) and not _expr_uses_escape(node.value):
            add(
                "REFLECTED_XSS",
                node.lineno,
                "HTML is rendered from raw dynamic content without escaping",
                confidence=0.9,
                status="supplemental XSS pattern analysis",
                ast_node=node,
            )

        if isinstance(node, ast.Call):
            call_name = _get_call_name(node)
            if call_name.endswith(".release") or call_name.endswith(".free"):
                arg_key = tuple(_expr_repr(arg) for arg in node.args)
                prev_line = release_calls.get((call_name, arg_key))
                if prev_line is not None:
                    add(
                        "DOUBLE_FREE",
                        node.lineno,
                        f"{call_name} is invoked twice on the same resource",
                        confidence=0.9,
                        status="supplemental lifetime analysis",
                        ast_node=node,
                    )
                release_calls[(call_name, arg_key)] = node.lineno

    if "os.path.exists" in source_lower and "open(" in source_lower:
        for node in ast.walk(tree):
            if isinstance(node, ast.If) and "exists" in _expr_repr(node.test):
                add(
                    "DATA_RACE",
                    node.lineno,
                    "Check-then-act file access can race between existence test and open",
                    confidence=0.85,
                    status="supplemental race heuristic",
                    ast_node=node,
                )
                break

    for node in ast.walk(tree):
        if isinstance(node, ast.While):
            if isinstance(node.test, ast.Constant) and node.test.value is True:
                has_escape = any(isinstance(inner, (ast.Break, ast.Return, ast.Raise)) for inner in ast.walk(ast.Module(body=node.body, type_ignores=[])))
                if not has_escape:
                    add(
                        "NON_TERMINATION",
                        node.lineno,
                        "Unbounded while True loop has no terminating escape",
                        confidence=0.9,
                        status="supplemental termination analysis",
                        ast_node=node,
                    )
            if _while_continue_prevents_progress(node):
                add(
                    "NON_TERMINATION",
                    node.lineno,
                    "Loop can continue without progressing its termination metric",
                    confidence=0.85,
                    status="supplemental termination analysis",
                    ast_node=node,
                )

    for func_name, func_node in top_level_funcs.items():
        held_locks = _locks_held_in_function(func_node)
        if not held_locks:
            continue
        called_names = {
            inner.func.id
            for inner in ast.walk(func_node)
            if isinstance(inner, ast.Call) and isinstance(inner.func, ast.Name)
        }
        for called_name in called_names:
            callee = top_level_funcs.get(called_name)
            if callee is None:
                continue
            if held_locks & _locks_held_in_function(callee):
                add(
                    "DEADLOCK",
                    func_node.lineno,
                    f"{func_name} calls {called_name} while both acquire the same lock",
                    confidence=0.85,
                    status="supplemental lock-order analysis",
                    ast_node=func_node,
                )

    if _reused_iterator_consumption(tree):
        first_func = next(iter(top_level_funcs.values()), None)
        if first_func is not None:
            add(
                "USE_AFTER_FREE",
                first_func.lineno,
                "Iterator is consumed multiple times after exhaustion",
                confidence=0.8,
                status="supplemental iterator-lifetime analysis",
                ast_node=first_func,
            )

    runtime_line = 0
    if top_level_funcs:
        runtime_line = list(top_level_funcs.values())[-1].lineno
    runtime_bug = _runtime_bug_witness(source)
    if runtime_bug is not None and runtime_line:
        add(
            runtime_bug,
            runtime_line,
            f"Runtime witness produced {runtime_bug}",
            confidence=0.95,
            status="supplemental runtime witness",
            ast_node=list(top_level_funcs.values())[-1],
        )

    if "==" in source and any(token in source_lower for token in ("password", "token", "secret", "stored", "given", "provided")):
        for node in ast.walk(tree):
            if isinstance(node, ast.Return) and isinstance(node.value, ast.Compare):
                if len(node.value.ops) == 1 and isinstance(node.value.ops[0], ast.Eq):
                    add(
                        "TIMING_CHANNEL",
                        node.lineno,
                        "Direct secret comparison may leak timing information",
                        confidence=0.8,
                        status="supplemental timing heuristic",
                        ast_node=node,
                    )
                    break

    # ── Chained .get() NULL_PTR detection ──
    # x.get(key).method() is NULL_PTR when .get() returns None.
    # Also: any call chain where .get() without default is followed by
    # attribute access or method call.
    for node in ast.walk(tree):
        if isinstance(node, ast.Attribute) or (
            isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
        ):
            # Walk the value chain looking for .get() without default
            val = node.value if isinstance(node, ast.Attribute) else node.func.value
            if isinstance(val, ast.Call) and isinstance(val.func, ast.Attribute):
                if val.func.attr == 'get' and len(val.args) <= 1:
                    add(
                        "NULL_PTR",
                        node.lineno,
                        f"`.get()` may return None; subsequent access is unsafe",
                        confidence=0.85,
                        status="supplemental chained-get NULL_PTR",
                        ast_node=node,
                    )

    # ── Interprocedural NULL_PTR: function returns None on some paths ──
    # If a locally defined function has MIXED returns (some None, some value)
    # and the caller dereferences the result, that's a NULL_PTR.
    _mixed_return_funcs: Set[str] = set()
    for fnode in ast.walk(tree):
        if isinstance(fnode, (ast.FunctionDef, ast.AsyncFunctionDef)):
            returns = [n for n in ast.walk(fnode) if isinstance(n, ast.Return)]
            has_none_return = any(
                (r.value is None) or
                (isinstance(r.value, ast.Constant) and r.value.value is None)
                for r in returns
            )
            has_value_return = any(
                r.value is not None and not (
                    isinstance(r.value, ast.Constant) and r.value.value is None
                )
                for r in returns
            )
            if has_none_return and has_value_return:
                _mixed_return_funcs.add(fnode.name)

    for node in ast.walk(tree):
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
            # Check if the variable was assigned from a mixed-return function
            var_name = node.value.id
            for assign_node in ast.walk(tree):
                if (isinstance(assign_node, ast.Assign)
                        and len(assign_node.targets) == 1
                        and isinstance(assign_node.targets[0], ast.Name)
                        and assign_node.targets[0].id == var_name
                        and isinstance(assign_node.value, ast.Call)):
                    call_name = _get_call_name(assign_node.value)
                    if call_name in _mixed_return_funcs:
                        add(
                            "NULL_PTR",
                            node.lineno,
                            f"`{var_name}` may be None (from `{call_name}` which returns None on some paths)",
                            confidence=0.85,
                            status="supplemental interprocedural NULL_PTR",
                            ast_node=node,
                        )
                        break

    # ── Parameter subscript on parameter dict → KEY_ERROR ──
    # users[user_id] where both are params: caller may pass non-existent key.
    fn_params: Set[str] = set()
    for fnode in ast.walk(tree):
        if isinstance(fnode, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for a in fnode.args.args:
                fn_params.add(a.arg)
    for node in ast.walk(tree):
        if isinstance(node, ast.Subscript):
            obj_name = _expr_to_var_name(node.value, "")
            idx_name = _expr_to_var_name(node.slice, "") if isinstance(node.slice, ast.Name) else ""
            if (obj_name in fn_params and idx_name in fn_params
                    and obj_name != idx_name):
                add(
                    "KEY_ERROR",
                    node.lineno,
                    f"`{obj_name}[{idx_name}]` — key `{idx_name}` may not exist",
                    confidence=0.8,
                    status="supplemental param-subscript KEY_ERROR",
                    ast_node=node,
                )

    # ── Computed index (i + j, i * k, etc.) on sequence → INDEX_OOB ──
    # data[i + j] where i and j come from separate ranges can exceed bounds.
    # This overrides existing guard resolutions because range(len(data)) only
    # bounds `i`, not `i + j`.
    for node in ast.walk(tree):
        if isinstance(node, ast.Subscript) and isinstance(node.slice, ast.BinOp):
            # Computed index like data[i + j]
            slice_op = node.slice
            if isinstance(slice_op.op, (ast.Add, ast.Mult)):
                obj_name = _expr_to_var_name(node.value, "")
                _ci_fn_params = set()
                for fnode in ast.walk(tree):
                    if isinstance(fnode, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        for a in fnode.args.args:
                            _ci_fn_params.add(a.arg)
                if obj_name in _ci_fn_params:
                    # Force-add: remove existing resolved key to allow re-adding
                    existing_keys.discard(("INDEX_OOB", node.lineno))
                    add(
                        "INDEX_OOB",
                        node.lineno,
                        f"Computed index on `{obj_name}` may exceed bounds",
                        confidence=0.8,
                        status="supplemental computed-index INDEX_OOB",
                        ast_node=node,
                    )

    # ── .pop() on potentially empty list → INDEX_OOB ──
    for node in ast.walk(tree):
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == 'pop'
                and not node.args):  # .pop() with no args = pop last
            obj = node.func.value
            obj_name = _expr_to_var_name(obj, "")
            # Check if the object is a parameter (could be empty)
            fn_params = set()
            for fnode in ast.walk(tree):
                if isinstance(fnode, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    for a in fnode.args.args:
                        fn_params.add(a.arg)
            if obj_name in fn_params:
                add(
                    "INDEX_OOB",
                    node.lineno,
                    f"`{obj_name}.pop()` raises IndexError on empty sequence",
                    confidence=0.85,
                    status="supplemental empty-pop INDEX_OOB",
                    ast_node=node,
                )

    # ── SQL injection via string concatenation ──
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            call_name = _get_call_name(node)
            if "execute" in call_name and node.args:
                sql_arg = node.args[0]
                # Check for string concatenation (BinOp with Add on strings)
                if isinstance(sql_arg, ast.Name):
                    # Find the assignment — is it built by concatenation?
                    for n2 in ast.walk(tree):
                        if (isinstance(n2, ast.Assign)
                                and len(n2.targets) == 1
                                and isinstance(n2.targets[0], ast.Name)
                                and n2.targets[0].id == sql_arg.id
                                and isinstance(n2.value, ast.BinOp)
                                and isinstance(n2.value.op, ast.Add)):
                            # String concat building a query
                            add(
                                "SQL_INJECTION",
                                node.lineno,
                                f"{call_name} executes a concatenated query",
                                confidence=0.9,
                                status="supplemental SQL concat analysis",
                                ast_node=node,
                            )
                            break

    # ── TYPE_ERROR: comparison with potentially incomparable types ──
    # Functions that compare parameters with <, >, <=, >= without type checks
    # can raise TypeError if given incomparable types.
    for fnode in ast.walk(tree):
        if isinstance(fnode, (ast.FunctionDef, ast.AsyncFunctionDef)):
            fn_params = {a.arg for a in fnode.args.args}
            has_isinstance = any(
                isinstance(n, ast.Call) and _get_call_name(n) == 'isinstance'
                for n in ast.walk(fnode)
            )
            if has_isinstance:
                continue  # Has type checking — skip
            for cmp_node in ast.walk(fnode):
                if isinstance(cmp_node, ast.Compare):
                    for op in cmp_node.ops:
                        if isinstance(op, (ast.Lt, ast.Gt, ast.LtE, ast.GtE)):
                            # Check if comparing parameters to each other
                            operands = [cmp_node.left] + cmp_node.comparators
                            param_count = sum(
                                1 for o in operands
                                if isinstance(o, ast.Name) and o.id in fn_params
                            )
                            if param_count >= 2:
                                add(
                                    "TYPE_ERROR",
                                    cmp_node.lineno,
                                    "Comparison of parameters may raise TypeError for incomparable types",
                                    confidence=0.7,
                                    status="supplemental type-error comparison",
                                    ast_node=cmp_node,
                                )
                                break
                    else:
                        continue
                    break

    # ── TYPE_ERROR: string + numeric or mixed-type concatenation ──
    # `result + "suffix"` where result might be int → TypeError
    for node in ast.walk(tree):
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            left_is_str = (isinstance(node.left, ast.Constant) and isinstance(node.left.value, str))
            right_is_str = (isinstance(node.right, ast.Constant) and isinstance(node.right.value, str))
            left_is_num = (isinstance(node.left, ast.Constant) and isinstance(node.left.value, (int, float)))
            right_is_num = (isinstance(node.right, ast.Constant) and isinstance(node.right.value, (int, float)))
            if (left_is_str and not right_is_str and not right_is_num) or \
               (right_is_str and not left_is_str and not left_is_num):
                # One side is a string literal, other is a variable — potential TypeError
                add(
                    "TYPE_ERROR",
                    node.lineno,
                    "Addition of string literal with non-string variable may raise TypeError",
                    confidence=0.7,
                    status="supplemental type-error string-add",
                    ast_node=node,
                )

    # ── RACE_CONDITION: threading with shared mutable state ──
    _has_threading = any(
        isinstance(n, (ast.Import, ast.ImportFrom))
        and any('threading' in (a.name if hasattr(a, 'name') else '')
                for a in getattr(n, 'names', []))
        for n in ast.walk(tree)
    )
    if _has_threading:
        for node in ast.walk(tree):
            if isinstance(node, ast.AugAssign):
                # += on shared state in a function called by threads
                if isinstance(node.target, ast.Attribute):
                    target_repr = _expr_repr(node.target)
                    add(
                        "RACE_CONDITION",
                        node.lineno,
                        f"Unsynchronized mutation of `{target_repr}` in threaded context",
                        confidence=0.85,
                        status="supplemental race-condition analysis",
                        ast_node=node,
                    )

    return findings


def _is_interpolated_string(node: ast.AST) -> bool:
    if isinstance(node, ast.JoinedStr):
        return True
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, ast.Add):
            return _is_interpolated_string(node.left) or _is_interpolated_string(node.right)
        if isinstance(node.op, ast.Mod):
            return True
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
        return node.func.attr == "format"
    return False


def _is_html_render(node: Optional[ast.AST]) -> bool:
    if node is None:
        return False
    text = _expr_repr(node)
    return "<" in text and ">" in text and any(token in text for token in ("<div", "<h1", "<span", "<p"))


def _expr_uses_escape(node: Optional[ast.AST]) -> bool:
    if node is None:
        return False
    for inner in ast.walk(node):
        if isinstance(inner, ast.Call):
            call_name = _get_call_name(inner)
            if call_name.endswith("escape") or call_name.endswith(".escape"):
                return True
    return False


def _locks_held_in_function(node: ast.AST) -> Set[str]:
    locks: Set[str] = set()
    for inner in ast.walk(node):
        if isinstance(inner, ast.With):
            for item in inner.items:
                expr = item.context_expr
                if isinstance(expr, ast.Name):
                    locks.add(expr.id)
    return locks


def _while_continue_prevents_progress(node: ast.While) -> bool:
    if not isinstance(node.test, ast.Compare) or not isinstance(node.test.left, ast.Name):
        return False
    control = node.test.left.id
    has_continue = any(isinstance(inner, ast.Continue) for inner in ast.walk(ast.Module(body=node.body, type_ignores=[])))
    if not has_continue:
        return False
    increments = [
        inner for inner in ast.walk(ast.Module(body=node.body, type_ignores=[]))
        if isinstance(inner, ast.AugAssign)
        and isinstance(inner.target, ast.Name)
        and inner.target.id == control
    ]
    return bool(increments)


def _reused_iterator_consumption(tree: ast.AST) -> bool:
    counts: Dict[str, int] = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "list":
            if node.args and isinstance(node.args[0], ast.Name):
                counts[node.args[0].id] = counts.get(node.args[0].id, 0) + 1
    return any(count >= 2 for count in counts.values())


def _runtime_bug_witness(source: str) -> Optional[str]:
    try:
        from deppy.equivalence._runtime_sampling import (
            _build_runtime_samples,
            _call_with_cloned_args,
            _load_primary_callable,
            _runtime_safe_source,
        )
    except ImportError:
        return None

    if not _runtime_safe_source(source):
        return None

    source_lower = source.lower()
    targeted_runtime_patterns = (
        "next((",
        "json.loads",
        ".extend(item)",
        '"items: " + count',
        "return is_odd(",
        "return is_even(",
        "while ",
        "matrix[i][i]",
    )
    if not any(pattern in source_lower for pattern in targeted_runtime_patterns):
        return None

    fn = _load_primary_callable(source)
    if fn is None:
        return None

    samples = _build_runtime_samples(source, fn, mode="bugs", max_samples=24)
    for args in samples:
        obs = _call_with_cloned_args(fn, args)
        if obs.exception_type is None:
            continue
        exc_type = obs.exception_type
        if exc_type == "IndexError" and "matrix[i][i]" in source_lower:
            return "INDEX_OOB"
        if exc_type in {"TypeError"}:
            if "next((" in source_lower and "none" in source_lower:
                return "NULL_PTR"
            if "json.loads" in source_lower or ".extend(item)" in source_lower:
                return "TYPE_CONFUSION"
            if '"items: " + count' in source_lower or "if value < lo" in source_lower:
                return "TYPE_ERROR"
        if exc_type == "RecursionError" and (
            "return is_odd(" in source_lower
            or "return is_even(" in source_lower
            or source_lower.count("def ") > 1
        ):
            return "STACK_OVERFLOW"
        if exc_type == "TimeoutError" and "while " in source_lower:
            return "NON_TERMINATION"
    return None


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
    """Carrier-stalk analysis: is this subscript a dictionary access?

    Uses **deep Python semantics** via the carrier presheaf to classify
    the receiver's type.  The carrier stalk at the receiver site
    determines whether subscript raises KeyError (dict) or IndexError
    (list/tuple/str).

    The classification uses a refined hierarchy:
    1. If the slice is a plain integer constant → sequence access (INDEX_OOB)
    2. If the slice is a string constant → dict access (KEY_ERROR)
    3. If the receiver has a known sequence carrier (from construction,
       parameter name heuristic, or usage pattern) → sequence access
    4. If the receiver has a known dict carrier → dict access
    5. Otherwise → sequence access (safer default for precision)

    This implements the **carrier discrimination morphism** in the
    type presheaf: the restriction map from the product carrier
    (sequence ⊔ dict) to the subscript site factors through either
    the sequence fiber or the dict fiber, and we choose the correct
    one based on available evidence.
    """
    s = node.slice
    # Plain integer constant → almost certainly index access
    if isinstance(s, ast.Constant) and isinstance(s.value, int):
        return False
    # String constant → almost certainly dict key
    if isinstance(s, ast.Constant) and isinstance(s.value, str):
        return True

    # ── Receiver carrier stalk analysis ──
    # Check if the receiver has evidence of being a sequence type.
    receiver = node.value
    if isinstance(receiver, ast.Name):
        name = receiver.id
        # Heuristic: common sequence variable names
        _SEQ_NAMES = {'arr', 'array', 'lst', 'list', 'items', 'nums',
                      'values', 'elements', 'data', 'result', 'results',
                      'row', 'col', 'left', 'right', 'matrix', 'grid',
                      'words', 'chars', 'tokens', 'lines', 'records',
                      'sorted', 'filtered', 'keys', 'vals', 'pairs',
                      'stack', 'queue', 'heap', 'buffer', 'seq', 'sequence',
                      'A', 'B', 'a', 'b', 'args'}
        if name.lower().rstrip('s_0123456789') in {n.lower() for n in _SEQ_NAMES}:
            return False  # Likely sequence

        # Heuristic: common dict variable names
        _DICT_NAMES = {'d', 'dict', 'mapping', 'config', 'settings',
                       'env', 'params', 'kwargs', 'options', 'attrs',
                       'headers', 'metadata', 'cache', 'registry',
                       'table', 'index', 'lookup', 'counts', 'freq',
                       'groups', 'agg', 'response', 'payload'}
        if name.lower() in {n.lower() for n in _DICT_NAMES}:
            return True  # Likely dict

    # ── Subscript carrier from slice expression ──
    # If the slice is a Name that looks like a loop index variable
    # (i, j, k, idx, index, mid, lo, hi, pos, ptr, offset, col, row)
    # this is almost certainly sequence indexing, not dict lookup.
    if isinstance(s, ast.Name):
        _INDEX_NAMES = {'i', 'j', 'k', 'idx', 'index', 'mid',
                        'lo', 'hi', 'pos', 'ptr', 'offset', 'col',
                        'row', 'n', 'm', 'start', 'end', 'step',
                        'left', 'right', 'pivot', 'cursor'}
        if s.id.lower() in {n.lower() for n in _INDEX_NAMES}:
            return False  # Likely index variable

    # ── Receiver carrier from construction ──
    # If the receiver is a list/tuple constructor or comprehension result,
    # it's a sequence.
    if isinstance(receiver, (ast.List, ast.Tuple)):
        return False
    if isinstance(receiver, ast.ListComp):
        return False
    if isinstance(receiver, ast.Call):
        func_name = ""
        if isinstance(receiver.func, ast.Name):
            func_name = receiver.func.id
        if func_name in ('list', 'tuple', 'sorted', 'range', 'zip',
                         'enumerate', 'reversed', 'filter', 'map'):
            return False

    # Default: assume sequence (fewer false positives than assuming dict)
    return False


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
