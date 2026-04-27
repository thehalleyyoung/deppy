"""
Deppy Sidecar Proofs — External Verification Without Library Modification
============================================================================

Write verification proofs about external libraries (sympy, torch, numpy, etc.)
in separate "sidecar" proof files.  The original library stays completely
untouched — sidecar specs and proofs live in separate ``.py`` or ``.deppy``
files and are stripped away when not needed.

Architecture
------------
- ``SidecarModule``   — container for specs, axioms, and proofs about one library
- ``ExternalSpec``    — a spec bound to an existing (external) function/method
- ``AxiomDecl``       — a trusted axiom about a library function
- ``ProofDecl``       — a proved property of a library function
- ``SidecarVerifier`` — verify all proofs in a sidecar module
- ``SidecarReport``   — structured verification results
- ``@about``          — decorator to attach specs to external functions
- ``.deppy`` file parser — declarative sidecar file format

Example
-------
    import sympy
    from deppy.proofs.sidecar import SidecarModule

    proofs = SidecarModule("sympy")

    proofs.spec(sympy.expand,
        guarantee="expand(a + b) == expand(a) + expand(b)",
        pure=True,
    )

    proofs.axiom("sympy.expand",
        "expand(expand(e)) == expand(e)",
        name="expand_idempotent",
    )

    proofs.prove(
        "expand is idempotent",
        target=sympy.expand,
        proof=lambda pb: pb.by_axiom("expand_idempotent", "sympy").conclude(),
    )

    report = proofs.verify_all()
    print(report.summary())
"""
from __future__ import annotations

import inspect
import json
import re
import textwrap
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, TypeVar

from deppy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    AxiomInvocation, Structural, Z3Proof, AxiomEntry, min_trust,
)
from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    Var, Literal, PyObjType, PyIntType,
    RefinementType, PyBoolType, PyCallableType,
)
from deppy.core.formal_ops import Op, OpCall, FormalAxiomEntry
from deppy.proofs.tactics import ProofBuilder
from deppy.proofs.sugar import (
    guarantee, requires, ensures, pure, extract_spec,
    _get_spec, _SpecMetadata, Proof,
)

F = TypeVar("F", bound=Callable)


# ═══════════════════════════════════════════════════════════════════
#  §1  ExternalSpec — bind a spec to an existing function
# ═══════════════════════════════════════════════════════════════════

def _resolve_target(dotted_path: str) -> Any:
    """Try to import and return the object at *dotted_path*."""
    if not dotted_path:
        return None
    parts = dotted_path.split('.')
    for i in range(len(parts), 0, -1):
        module_path = '.'.join(parts[:i])
        try:
            mod = __import__(module_path, fromlist=[parts[i]] if i < len(parts) else [''])
            obj = mod
            for attr in parts[i:]:
                obj = getattr(obj, attr)
            return obj
        except (ImportError, AttributeError):
            continue
    return None

@dataclass
class ExternalSpec:
    """A specification bound to an external (library) function.

    The spec lives *outside* the target library and does not modify it.
    It records guarantees, pre/postconditions, purity, and runtime safety
    declarations for an existing callable.

    Can be used as a dataclass (passing target/target_name/module_name)
    or subclassed with ``@about`` to declare laws::

        @about("sympy.core.add.Add")
        class AddSpec(ExternalSpec):
            @law
            def commutative(self, a, b):
                return self.call(a, b).equals(self.call(b, a))
    """

    target: Any = None                          # the actual function/method
    target_name: str = ""                       # qualified name ("sympy.expand")
    module_name: str = ""                       # library name ("sympy")
    guarantees: list[str] = field(default_factory=list)
    preconditions: list[Callable | str] = field(default_factory=list)
    postconditions: list[Callable | str] = field(default_factory=list)
    is_pure: bool = False
    reads: list[str] = field(default_factory=list)
    mutates_list: list[str] = field(default_factory=list)
    axioms: list[str] = field(default_factory=list)  # axiom names bound here
    verified: bool = False
    trust_level: TrustLevel = TrustLevel.UNTRUSTED

    # ── Runtime safety declarations ──────────────────────────────
    exception_free_when: list[str] = field(default_factory=list)
    raises_declarations: list[tuple[str, str]] = field(default_factory=list)
    safe_when: list[str] = field(default_factory=list)
    is_total: bool = False
    decreases: list[str] = field(default_factory=list)

    # ── User-attached Lean proofs ────────────────────────────────
    # Each entry is a 4-tuple ``(failure_kind, theorem, proof_script,
    # imports_tuple)``.  ``failure_kind`` may be a specific
    # exception-source kind (e.g. ``"ZERO_DIVISION"``) or the wildcard
    # ``"*"``; the safety pipeline tries to discharge each undischarged
    # source by running every matching proof through the kernel's
    # ``LeanProof`` term.
    lean_proofs: list[tuple[str, str, str, tuple[str, ...]]] = field(
        default_factory=list,
    )

    def __post_init__(self):
        # Auto-resolve target from @about annotation if not provided
        about_path = getattr(self.__class__, '_deppy_about', None)
        if about_path and not self.target_name:
            self.target_name = about_path
            self.module_name = about_path.rsplit('.', 1)[0] if '.' in about_path else about_path
        if about_path and self.target is None:
            self.target = _resolve_target(about_path)

    def call(self, *args, **kwargs):
        """Call the target function.  Used in @law method bodies."""
        if self.target is not None:
            return self.target(*args, **kwargs)
        about_path = getattr(self.__class__, '_deppy_about', self.target_name)
        resolved = _resolve_target(about_path)
        if resolved is not None:
            self.target = resolved
            return resolved(*args, **kwargs)
        raise RuntimeError(f"Cannot resolve target {about_path!r}")

    @property
    def qualified_name(self) -> str:
        return self.target_name

    # ── convenience accessors used by the tutorial book ──

    @property
    def precondition(self) -> str:
        """First precondition as a string (book-friendly accessor)."""
        if self.preconditions:
            p = self.preconditions[0]
            return str(p) if callable(p) else p
        return ""

    @property
    def postcondition(self) -> str:
        """First postcondition as a string (book-friendly accessor)."""
        if self.postconditions:
            p = self.postconditions[0]
            return str(p) if callable(p) else p
        return ""

    @property
    def laws(self) -> list[str]:
        """Axiom names bound to this spec (book-friendly alias)."""
        return list(self.axioms)

    def to_json(self) -> dict:
        """Serialize to JSON-compatible dict."""
        d = {
            "target_name": self.target_name,
            "module_name": self.module_name,
            "guarantees": self.guarantees,
            "preconditions": [
                str(p) if callable(p) else p for p in self.preconditions
            ],
            "postconditions": [
                str(p) if callable(p) else p for p in self.postconditions
            ],
            "is_pure": self.is_pure,
            "reads": self.reads,
            "mutates": self.mutates_list,
            "axioms": self.axioms,
            "verified": self.verified,
            "trust_level": self.trust_level.name,
        }
        if self.exception_free_when:
            d["exception_free_when"] = self.exception_free_when
        if self.raises_declarations:
            d["raises"] = [{"type": t, "when": w}
                           for t, w in self.raises_declarations]
        if self.safe_when:
            d["safe_when"] = self.safe_when
        if self.is_total:
            d["is_total"] = True
        if self.decreases:
            d["decreases"] = self.decreases
        return d

    @classmethod
    def from_json(cls, data: dict) -> ExternalSpec:
        """Deserialize from JSON dict."""
        raises = [(r["type"], r["when"]) for r in data.get("raises", [])]
        return cls(
            target=None,
            target_name=data["target_name"],
            module_name=data.get("module_name", ""),
            guarantees=data.get("guarantees", []),
            preconditions=data.get("preconditions", []),
            postconditions=data.get("postconditions", []),
            is_pure=data.get("is_pure", False),
            reads=data.get("reads", []),
            mutates_list=data.get("mutates", []),
            axioms=data.get("axioms", []),
            verified=data.get("verified", False),
            trust_level=TrustLevel[data.get("trust_level", "UNTRUSTED")],
            exception_free_when=data.get("exception_free_when", []),
            raises_declarations=raises,
            safe_when=data.get("safe_when", []),
            is_total=data.get("is_total", False),
            decreases=data.get("decreases", []),
        )


# ═══════════════════════════════════════════════════════════════════
#  §2  AxiomDecl — a trusted axiom declaration about a library
# ═══════════════════════════════════════════════════════════════════

@dataclass
class AxiomDecl:
    """A trusted axiom about an external library function."""

    name: str                   # e.g. "expand_distributive"
    target: str                 # e.g. "sympy.expand"
    statement: str              # e.g. "expand(a+b) == expand(a) + expand(b)"
    module: str = ""            # e.g. "sympy"
    precondition: str = ""      # optional guard
    # AUDIT A.3 — user-supplied Lean proof (raw tactic text).
    lean_proof: str = ""
    lean_signature: str = ""

    @property
    def qualified_name(self) -> str:
        mod = self.module or self.target.split(".")[0] if "." in self.target else ""
        return f"{mod}.{self.name}" if mod else self.name

    def to_axiom_entry(self) -> AxiomEntry:
        """Convert to a kernel AxiomEntry."""
        stmt = self.statement
        if self.precondition:
            stmt = f"{stmt}  [when {self.precondition}]"
        return AxiomEntry(
            name=self.name,
            statement=stmt,
            module=self.module,
        )

    def to_json(self) -> dict:
        return {
            "name": self.name,
            "target": self.target,
            "statement": self.statement,
            "module": self.module,
            "precondition": self.precondition,
        }

    @classmethod
    def from_json(cls, data: dict) -> AxiomDecl:
        return cls(
            name=data["name"],
            target=data["target"],
            statement=data["statement"],
            module=data.get("module", ""),
            precondition=data.get("precondition", ""),
        )


# ═══════════════════════════════════════════════════════════════════
#  §2.5  FoundationDecl — a generic mathematical foundation axiom
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FoundationDecl:
    """A foundation axiom: a generic mathematical fact (not specific to
    any library) that we admit as part of the trust surface.

    Foundations are distinguished from sidecar ``axiom``s in that an
    axiom is a claim about a specific library function (e.g.
    ``sympy.expand``), whereas a foundation is a general mathematical
    truth (e.g. ``sqrt(x)**2 == x when x >= 0``) that can be used to
    derive other claims.

    The trust chain for a Lean certificate is::

        foundations  ⟶  sidecar axioms  ⟶  proven theorems

    Foundations are the bottom of the trust chain — they are admitted
    without further justification.  Sidecar axioms about library
    behaviour can either be admitted directly OR derived from
    foundations + the library's source.  Proofs in the certificate
    discharge claims using foundations + axioms; their bodies are real
    Lean terms type-checked by the kernel.
    """
    name: str                  # e.g. "Real.sqrt_sq_nonneg"
    statement: str             # Python-syntax claim
    citation: str = ""         # e.g. URL or textbook reference
    # AUDIT A.2 — user-supplied Lean proof (raw tactic text).
    # When set, the certificate emits a real ``theorem`` with this
    # body; when empty, the foundation is admitted as an axiom.
    lean_proof: str = ""
    lean_signature: str = ""   # optional Lean type override

    def to_json(self) -> dict:
        return {
            "name": self.name,
            "statement": self.statement,
            "citation": self.citation,
            "lean_proof": self.lean_proof,
            "lean_signature": self.lean_signature,
        }

    @classmethod
    def from_json(cls, data: dict) -> "FoundationDecl":
        return cls(
            name=data["name"],
            statement=data["statement"],
            citation=data.get("citation", ""),
            lean_proof=data.get("lean_proof", ""),
            lean_signature=data.get("lean_signature", ""),
        )


# ═══════════════════════════════════════════════════════════════════
#  §2.6  VerifyDecl — directly connect a function to a Lean property
# ═══════════════════════════════════════════════════════════════════

@dataclass
class LemmaDecl:
    """A user-defined intermediate lemma.

    A lemma can be either:

      * **Admitted** (no ``lean_proof`` text): treated as a sidecar
        axiom with the given statement.

      * **Proved by user-supplied Lean** (``lean_proof`` text):
        the certificate emits a real ``theorem L : <stmt> := <proof>``
        which Lean's kernel type-checks.  This is the escape hatch
        for any property a human or LLM can write a Lean proof for.

    The ``lean_signature`` field lets the user override deppy's
    auto-derived Lean type for the lemma; when empty, deppy uses the
    statement string as the Lean Prop.
    """
    name: str
    statement: str = ""
    proof: str = ""              # optional inline ``by:`` clause
    lean_proof: str = ""         # multi-line raw Lean tactic script
    lean_signature: str = ""     # optional Lean type override
    lean_imports: list[str] = field(default_factory=list)  # per-lemma imports


@dataclass
class VerifyDecl:
    """A code-property verification block.

    ``VerifyDecl`` is the .deppy form that most directly says
    "verify that *this* function in the library satisfies *this*
    property, using *this* foundation, checked by deppy's kernel".

    Sidecar-syntax form::

        verify NAME:
          function: <dotted path to method>           # e.g. sympy.geometry.point.Point.distance
          property: "<Python-syntax predicate>"       # e.g. "Point.distance(p, q) >= 0"
          via:      foundation <foundation-name>      # cites a registered foundation
          fibration: isinstance <Type>                # optional — descent over isinstance
          cubical:  true | false                      # optional — request cubical analysis

    The certificate uses this to:

      1. ``inspect.getsource`` the named function.
      2. Translate the body via ``deppy.lean.body_translation``.
      3. Build a deppy ``ProofTerm`` whose head cites the foundation.
      4. Run it through ``ProofKernel.verify``.
      5. When the kernel returns ``success=True``, emit a Lean
         theorem whose statement is the property and whose proof
         body documents the kernel-verified ProofTerm tree.

    All five steps are existing deppy infrastructure — no
    library-specific code.
    """
    name: str                                  # e.g. "dist_pythagoras_verify"
    function: str                              # dotted path
    property: str                              # Python predicate string
    foundation: str = ""                       # foundation cited via ``via:``
    fibration_type: str = ""                   # isinstance type for fibration descent
    use_cubical: bool = False                  # request cubical analysis
    # F9 — type annotations + requires/ensures
    binders: dict[str, str] = field(default_factory=dict)   # e.g. {"p": "Point", "q": "Point"}
    requires: str = ""                         # precondition (Python expr)
    ensures: str = ""                          # postcondition (Python expr)
    # F10 — tactic block for hard cases
    by_lean: str = ""                          # multi-line Lean tactic script
    # PSDL — Python-Semantic Deppy Language proof script (the
    # *strong* proof language — Python-shaped, compiles to deppy
    # ProofTerm + Lean tactic).
    psdl_proof: str = ""
    # F12 — implementation hash pinning
    expects_sha256: str = ""                   # if non-empty, certificate fails on hash drift
    # F14 — effect / termination / Z3 hint annotations
    effect: str = ""                           # "pure" / "may_raise TypeError" / etc.
    decreases: str = ""                        # well-founded measure
    z3_binders: dict[str, str] = field(default_factory=dict)   # explicit Z3 sorts
    # F15 — cubical / cohomology hints
    cubical_dim: int = 0                       # request specific cubical dimension
    cohomology_level: int = 0                  # request specific cocycle level
    # F15 — counterexample directives
    expecting_counterexample: bool = False     # if True, certificate fails when none found
    notes: list[str] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════
#  §3  ProofDecl — a proof about an external library function
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProofDecl:
    """A proof of a property about an external library function.

    The ``by_clause`` field captures the user's chosen proof tactic
    in a generic, library-independent vocabulary.  Recognised forms:

      * ``axiom <NAME>``                   — cite a sidecar axiom
      * ``foundation <NAME>``              — cite a foundation axiom
      * ``refl``                           — definitional equality (``rfl``)
      * ``chain <F1>, <F2>, ...``          — transitive composition of axioms
      * ``rewrite <F> then cite <A>``      — rewrite + axiom citation
      * ``composition <F1> & <F2> & ...``  — conjunction (And.intro)

    The first matching form is honoured; unrecognised forms produce a
    proof body of ``sorry`` honestly admitting non-discharge.
    """

    claim: str                              # human-readable claim
    target: Any | None = None               # the function (optional)
    target_name: str = ""                   # qualified name
    proof_fn: Callable | None = None        # proof builder callback
    proof_term: ProofTerm | None = None     # direct proof term
    axiom_name: str = ""                    # prove by axiom shortcut
    axiom_module: str = ""                  # axiom module for shortcut
    by_clause: str = ""                     # raw ``by:`` text, e.g. "chain F1, F2"
    foundation_name: str = ""               # filled when by-form is ``foundation X``
    chain_axioms: list[str] = field(default_factory=list)
    rewrite_with: str = ""                  # foundation used to rewrite
    rewrite_then_cite: str = ""             # axiom cited after rewrite
    result: VerificationResult | None = None

    def to_json(self) -> dict:
        d: dict[str, Any] = {
            "claim": self.claim,
            "target_name": self.target_name,
        }
        if self.axiom_name:
            d["axiom_name"] = self.axiom_name
            d["axiom_module"] = self.axiom_module
        if self.result is not None:
            d["result"] = {
                "success": self.result.success,
                "trust_level": self.result.trust_level.name,
                "message": self.result.message,
                "axioms_used": self.result.axioms_used,
            }
        return d

    @classmethod
    def from_json(cls, data: dict) -> ProofDecl:
        pd = cls(
            claim=data["claim"],
            target_name=data.get("target_name", ""),
        )
        if "axiom_name" in data:
            pd.axiom_name = data["axiom_name"]
            pd.axiom_module = data.get("axiom_module", "")
        return pd


# ═══════════════════════════════════════════════════════════════════
#  §4  SpecResult — result for one spec/proof verification
# ═══════════════════════════════════════════════════════════════════

@dataclass
class SpecResult:
    """Verification result for a single spec or proof."""

    name: str
    kind: str                               # "spec", "axiom", "proof"
    target_name: str
    success: bool
    trust_level: TrustLevel
    message: str = ""
    axioms_used: list[str] = field(default_factory=list)

    def to_json(self) -> dict:
        return {
            "name": self.name,
            "kind": self.kind,
            "target_name": self.target_name,
            "success": self.success,
            "trust_level": self.trust_level.name,
            "message": self.message,
            "axioms_used": self.axioms_used,
        }


# ═══════════════════════════════════════════════════════════════════
#  §5  SidecarReport — aggregate verification report
# ═══════════════════════════════════════════════════════════════════

@dataclass
class SidecarReport:
    """Aggregate verification results for a sidecar module."""

    module_name: str
    total_specs: int = 0
    verified: int = 0
    failed: int = 0
    axiom_only: int = 0     # trusted but not proven
    results: list[SpecResult] = field(default_factory=list)

    def summary(self) -> str:
        """Human-readable summary."""
        lines = [
            f"╔══ Sidecar Report: {self.module_name} ══╗",
            f"  Total specs : {self.total_specs}",
            f"  Verified    : {self.verified}",
            f"  Failed      : {self.failed}",
            f"  Axiom-only  : {self.axiom_only}",
        ]
        if self.results:
            lines.append("  ────────────────────────────────")
            for r in self.results:
                icon = "✓" if r.success else "✗"
                tag = f"[{r.trust_level.name}]"
                lines.append(f"  {icon} {tag:20s} {r.kind:6s}  {r.name}")
        lines.append(f"╚{'═' * (len(lines[0]) - 2)}╝")
        return "\n".join(lines)

    def to_json(self) -> dict:
        return {
            "module_name": self.module_name,
            "total_specs": self.total_specs,
            "verified": self.verified,
            "failed": self.failed,
            "axiom_only": self.axiom_only,
            "results": [r.to_json() for r in self.results],
        }

    @classmethod
    def from_json(cls, data: dict) -> SidecarReport:
        return cls(
            module_name=data["module_name"],
            total_specs=data.get("total_specs", 0),
            verified=data.get("verified", 0),
            failed=data.get("failed", 0),
            axiom_only=data.get("axiom_only", 0),
        )


# ═══════════════════════════════════════════════════════════════════
#  §5b  SidecarVerificationBackend — discharge axioms instead of trusting
# ═══════════════════════════════════════════════════════════════════

class SidecarVerificationBackend:
    """Backend that can discharge sidecar axioms via Z3, computation, or Lean.

    Instead of blindly trusting axioms, the backend attempts to verify them
    and assigns trust levels based on the verification method:

      - Z3 discharge          → Z3_VERIFIED
      - Computational testing → LLM_CHECKED (evidence from test execution)
      - Counterexample found  → fail (axiom is false)
      - Lean export           → KERNEL (when no sorry)
      - Fallback: trusted     → AXIOM_TRUSTED
    """

    def __init__(
        self,
        *,
        enable_z3: bool = True,
        enable_computational: bool = True,
        computational_samples: int = 50,
        enable_counterexample: bool = True,
        counterexample_samples: int = 100,
    ) -> None:
        self.enable_z3 = enable_z3
        self.enable_computational = enable_computational
        self.computational_samples = computational_samples
        self.enable_counterexample = enable_counterexample
        self.counterexample_samples = counterexample_samples
        self._z3_available: bool | None = None

    @property
    def z3_available(self) -> bool:
        if self._z3_available is None:
            try:
                import z3  # noqa: F401
                self._z3_available = True
            except ImportError:
                self._z3_available = False
        return self._z3_available

    def discharge_axiom(
        self,
        axiom: AxiomDecl,
        kernel: ProofKernel,
        *,
        test_fn: Any | None = None,
    ) -> tuple[bool, TrustLevel, str]:
        """Try to discharge an axiom. Returns (success, trust_level, message).

        Attempts verification in this order:
          1. Z3 (if formula is encodable)
          2. Computational testing (if test_fn or target is callable)
          3. Counterexample search
          4. Fallback to trusted

        Args:
            axiom: The axiom to discharge.
            kernel: The proof kernel.
            test_fn: Optional callable that tests the axiom on concrete inputs.
                     Should return True if the axiom holds, raise if it doesn't.
        """
        # 1. Try Z3 discharge
        if self.enable_z3 and self.z3_available:
            success, msg = self._try_z3_discharge(axiom)
            if success:
                return True, TrustLevel.Z3_VERIFIED, f"Z3 proved: {msg}"
            # Z3 failure is not conclusive — formula may not be encodable

        # 2. Try computational testing
        if self.enable_computational and test_fn is not None:
            success, msg = self._try_computational(axiom, test_fn)
            if not success:
                return False, TrustLevel.UNTRUSTED, f"Computational falsified: {msg}"
            # Success upgrades to LLM_CHECKED (evidence from execution)
            return True, TrustLevel.LLM_CHECKED, f"Computational ({msg})"

        # 3. Try counterexample search on the target
        if self.enable_counterexample:
            target = _resolve_target(axiom.target) if axiom.target else None
            if target is not None and callable(target):
                found, msg = self._try_counterexample(axiom, target)
                if found:
                    return False, TrustLevel.UNTRUSTED, f"Counterexample: {msg}"

        # 4. Fallback: trust the axiom
        return True, TrustLevel.AXIOM_TRUSTED, f"Trusted axiom (not discharged)"

    def _try_z3_discharge(self, axiom: AxiomDecl) -> tuple[bool, str]:
        """Attempt to prove axiom via Z3."""
        if not self.z3_available:
            return False, "Z3 not available"
        try:
            from z3 import Solver, Int, Real, Bool, sat, unsat, unknown
            # Try to parse the axiom as a Z3 formula
            # We attempt common patterns: "a op b" style assertions
            stmt = axiom.statement.strip()
            # Skip complex / non-arithmetic axioms
            if any(kw in stmt for kw in [
                "for all", "for each", "iff", "returns", "passes through",
                "collinear", "perpendicular", "intersection",
            ]):
                return False, "formula too complex for Z3 quick discharge"

            # Try to evaluate as Z3 expression
            solver = Solver()
            # Create variables from any identifiers used
            import re as _re
            idents = set(_re.findall(r'\b([a-zA-Z_]\w*)\b', stmt))
            reserved = {'True', 'False', 'None', 'and', 'or', 'not',
                        'if', 'else', 'for', 'in', 'is', 'when', 'raises',
                        'sqrt', 'abs', 'len', 'min', 'max', 'sum', 'pi'}
            var_names = sorted(idents - reserved)
            z3_vars = {}
            for vn in var_names:
                z3_vars[vn] = Real(vn)

            # Try to build and negate the formula
            try:
                z3_expr = eval(stmt, {"__builtins__": {}}, z3_vars)
                solver.add(z3_vars.get('__not__', lambda e: e)(z3_expr)
                           if False else True)
                # Actually: negate and check unsat
                from z3 import Not
                solver.push()
                solver.add(Not(z3_expr))
                result = solver.check()
                solver.pop()
                if result == unsat:
                    return True, f"proved: {stmt[:60]}"
                elif result == sat:
                    return False, f"counterexample found"
                return False, "Z3 returned unknown"
            except Exception:
                return False, "formula not Z3-encodable"
        except Exception as e:
            return False, f"Z3 error: {e}"

    def _try_computational(
        self, axiom: AxiomDecl, test_fn: Any,
    ) -> tuple[bool, str]:
        """Run computational tests on the axiom."""
        passed = 0
        failed = 0
        for i in range(self.computational_samples):
            try:
                result = test_fn()
                if result is False:
                    failed += 1
                    return False, f"test {i+1} returned False"
                passed += 1
            except AssertionError as e:
                return False, f"test {i+1} assertion failed: {e}"
            except Exception as e:
                # Exception during testing — not necessarily a failure
                # of the axiom, could be a test setup issue
                failed += 1
                if failed > self.computational_samples // 4:
                    return False, f"too many test failures: {e}"
        return True, f"{passed}/{passed + failed} tests passed"

    def _try_counterexample(
        self, axiom: AxiomDecl, target: Any,
    ) -> tuple[bool, str]:
        """Try to find a counterexample by calling the target."""
        # Only attempt for simple function calls
        import random
        for _ in range(self.counterexample_samples):
            try:
                # Generate random inputs
                args = [random.uniform(-100, 100) for _ in range(2)]
                target(*args)
            except TypeError:
                break  # wrong arity / types — can't test this way
            except Exception as e:
                # Found an exception — might be a counterexample
                return True, f"target raised {type(e).__name__}: {e}"
        return False, "no counterexample found"
#  §6  SidecarModule — the main container
# ═══════════════════════════════════════════════════════════════════

def _resolve_target_name(func_or_class: Any) -> str:
    """Resolve a qualified name for a callable or class."""
    if isinstance(func_or_class, str):
        return func_or_class
    mod = getattr(func_or_class, "__module__", "") or ""
    qual = getattr(func_or_class, "__qualname__", "") or ""
    name = getattr(func_or_class, "__name__", "") or ""
    if mod and qual:
        return f"{mod}.{qual}"
    if mod and name:
        return f"{mod}.{name}"
    return qual or name or str(func_or_class)


class SidecarModule:
    """A collection of specs, axioms, and proofs about an external library.

    The target library is never modified.  All verification artefacts live
    in this module and can be serialized, cached, and shared.

    Usage::

        import sympy
        proofs = SidecarModule("sympy")

        proofs.spec(sympy.expand,
            guarantee="distributes over addition",
            pure=True,
        )

        proofs.axiom("sympy.expand",
            "expand(a + b) == expand(a) + expand(b)",
            name="expand_distributive",
        )

        proofs.prove("expand is idempotent",
            target=sympy.expand,
            proof=lambda pb: pb.conclude(
                pb.axiom("expand_idempotent", "sympy")
            ),
        )

        report = proofs.verify_all()
        print(report.summary())
    """

    def __init__(
        self,
        name: str,
        *,
        target_module: str | None = None,
        version: str = "",
    ) -> None:
        self.name = name
        self.target_module = target_module or name
        self.version = version
        self._specs: dict[str, ExternalSpec] = {}
        self._axioms: dict[str, AxiomDecl] = {}
        self._foundations: dict[str, "FoundationDecl"] = {}
        self._proofs: list[ProofDecl] = []
        self._verifies: list["VerifyDecl"] = []
        self._lemmas: list["LemmaDecl"] = []
        self._foundation_deps: dict[str, list[str]] = {}
        self._imports: list[str] = []
        self._symbolic_constants: dict[str, str] = {}
        self._predicates: dict[str, str] = {}
        # CODE-TYPES — typed signatures for code methods PSDL uses.
        # Maps name → Lean signature string (e.g.
        # ``"sqrt": "Int → Int"``, ``"sum_zip_sub_sq": "Point → Point → Int"``).
        self._code_types: dict[str, str] = {}
        # Lean import lines pulled in via top-level ``lean_imports: |``.
        self._lean_imports: list[str] = []
        # Lean preamble injected via top-level ``lean_preamble: |``.
        self._lean_preamble: str = ""
        self._about_specs: list[tuple[Any, _SpecMetadata]] = []

    # ── loading from files ────────────────────────────────────────

    @classmethod
    def load(cls, path: str) -> "SidecarModule":
        """Load a sidecar module from a .deppy file.

        Usage::

            math_sidecar = SidecarModule.load("sidecars/math.deppy")
        """
        import os
        name = os.path.splitext(os.path.basename(path))[0]
        mod = cls(name)
        mod._source_path = path
        # In a full implementation, this would parse the .deppy file
        # and populate specs/axioms/proofs. For now, create the module object.
        return mod

    def get_spec(self, target: str):
        """Get the spec for a given target function."""
        return self._specs.get(target)

    @property
    def specs(self):
        """All registered specs."""
        return self._specs

    # ── spec registration ────────────────────────────────────────

    def spec(
        self,
        func_or_class: Any,
        *,
        guarantee: str | list[str] | None = None,
        requires: Callable | str | None = None,
        ensures: Callable | str | None = None,
        pure: bool = False,
        reads: list[str] | None = None,
        mutates: list[str] | None = None,
    ) -> ExternalSpec:
        """Bind a specification to an existing function or method.

        The function itself is NOT modified.  The spec is recorded
        in this sidecar module for verification and documentation.

        Args:
            func_or_class: The external function/method to spec.
            guarantee: Postcondition(s) as NL strings.
            requires: Precondition callable or string.
            ensures: Postcondition callable or string.
            pure: Whether the function is pure.
            reads: List of state the function reads.
            mutates: List of state the function mutates.

        Returns:
            The created ExternalSpec.
        """
        target_name = _resolve_target_name(func_or_class)

        guarantees: list[str] = []
        if guarantee is not None:
            if isinstance(guarantee, str):
                guarantees = [guarantee]
            else:
                guarantees = list(guarantee)

        preconditions: list[Callable | str] = []
        if requires is not None:
            preconditions = [requires]

        postconditions: list[Callable | str] = []
        if ensures is not None:
            postconditions = [ensures]

        es = ExternalSpec(
            target=func_or_class,
            target_name=target_name,
            module_name=self.name,
            guarantees=guarantees,
            preconditions=preconditions,
            postconditions=postconditions,
            is_pure=pure,
            reads=reads or [],
            mutates_list=mutates or [],
        )
        self._specs[target_name] = es
        return es

    # ── foundation registration ──────────────────────────────────

    def foundation(
        self,
        name: str,
        statement: str,
        *,
        citation: str = "",
    ) -> FoundationDecl:
        """Register a generic mathematical foundation axiom.

        Foundations sit at the bottom of the trust chain — they are
        admitted without further justification and used to derive
        sidecar axioms (or close proof obligations directly).

        Args:
            name: Foundation name, e.g. ``"Real.sqrt_sq_nonneg"``.
            statement: The mathematical statement (Python syntax).
            citation: Optional pointer to a textbook/url.
        """
        f = FoundationDecl(name=name, statement=statement, citation=citation)
        self._foundations[name] = f
        return f

    @property
    def foundations(self) -> dict[str, FoundationDecl]:
        return self._foundations

    # ── axiom registration ───────────────────────────────────────

    def axiom(
        self,
        target: str,
        statement: str,
        *,
        name: str,
        precondition: str = "",
    ) -> AxiomDecl:
        """Register a trusted axiom about a library function.

        Args:
            target: Qualified function name (e.g. "sympy.expand").
            statement: The axiom statement as a string.
            name: Axiom name (must be unique within this module).
            precondition: Optional guard clause.

        Returns:
            The created AxiomDecl.
        """
        module = target.split(".")[0] if "." in target else self.name
        ax = AxiomDecl(
            name=name,
            target=target,
            statement=statement,
            module=module,
            precondition=precondition,
        )
        self._axioms[name] = ax

        # Also link the axiom to the spec, if one exists
        if target in self._specs:
            self._specs[target].axioms.append(name)

        return ax

    # ── proof registration ───────────────────────────────────────

    def prove(
        self,
        claim: str,
        *,
        target: Any | None = None,
        proof: Callable[[ProofBuilder], VerificationResult] | None = None,
        proof_term: ProofTerm | None = None,
        by_axiom: str | None = None,
        axiom_module: str | None = None,
        by_clause: str = "",
        foundation_name: str = "",
        chain_axioms: list[str] | None = None,
        rewrite_with: str = "",
        rewrite_then_cite: str = "",
    ) -> ProofDecl:
        """Register a proof about a library function.

        The proof can be specified as:
        - A callback ``proof`` that receives a ProofBuilder and returns
          a VerificationResult.
        - A direct ``proof_term``.
        - A shorthand ``by_axiom`` name.

        Args:
            claim: Human-readable claim to prove.
            target: The function the claim is about (optional).
            proof: Proof callback (receives ProofBuilder).
            proof_term: Direct proof term.
            by_axiom: Axiom name to prove by.
            axiom_module: Module for the axiom (defaults to self.name).

        Returns:
            The created ProofDecl.
        """
        target_name = _resolve_target_name(target) if target else ""

        pd = ProofDecl(
            claim=claim,
            target=target,
            target_name=target_name,
            proof_fn=proof,
            proof_term=proof_term,
            axiom_name=by_axiom or "",
            axiom_module=axiom_module or self.name,
            by_clause=by_clause,
            foundation_name=foundation_name,
            chain_axioms=list(chain_axioms or []),
            rewrite_with=rewrite_with,
            rewrite_then_cite=rewrite_then_cite,
        )
        self._proofs.append(pd)
        return pd

    # ── about-decorated spec registration ────────────────────────

    def register_about(self, target: Any, meta: _SpecMetadata) -> None:
        """Register a spec from an @about-decorated function."""
        self._about_specs.append((target, meta))
        target_name = _resolve_target_name(target)
        if target_name not in self._specs:
            self.spec(
                target,
                guarantee=meta.guarantees if meta.guarantees else None,
                pure=(meta.effect == "Pure"),
            )
        else:
            es = self._specs[target_name]
            es.guarantees.extend(meta.guarantees)
            if meta.effect == "Pure":
                es.is_pure = True

    # ── verification ─────────────────────────────────────────────

    def verify_all(
        self,
        kernel: ProofKernel | None = None,
        *,
        backend: SidecarVerificationBackend | None = None,
        axiom_tests: dict[str, Any] | None = None,
    ) -> SidecarReport:
        """Verify all specs, axioms, and proofs in this sidecar module.

        Args:
            kernel: The proof kernel to use.
            backend: Optional verification backend that can discharge
                axioms via Z3/computational testing instead of trusting.
            axiom_tests: Optional mapping from axiom name → test callable
                for computational verification.

        Returns a SidecarReport with per-item results.
        """
        kernel = kernel or ProofKernel()
        self.install(kernel)

        results: list[SpecResult] = []
        axiom_tests = axiom_tests or {}

        # Verify specs (structural check: the spec is well-formed)
        for name, es in self._specs.items():
            for g in es.guarantees:
                vr = self._verify_guarantee(kernel, es, g)
                results.append(SpecResult(
                    name=f"{name}: {g[:50]}",
                    kind="spec",
                    target_name=name,
                    success=vr.success,
                    trust_level=vr.trust_level,
                    message=vr.message,
                    axioms_used=vr.axioms_used,
                ))

        # Axioms — use backend to discharge if available, else trust
        for ax_name, ax in self._axioms.items():
            if backend is not None:
                test_fn = axiom_tests.get(ax_name)
                success, trust, msg = backend.discharge_axiom(
                    ax, kernel, test_fn=test_fn,
                )
                results.append(SpecResult(
                    name=ax_name,
                    kind="axiom",
                    target_name=ax.target,
                    success=success,
                    trust_level=trust,
                    message=msg,
                ))
            else:
                results.append(SpecResult(
                    name=ax_name,
                    kind="axiom",
                    target_name=ax.target,
                    success=True,
                    trust_level=TrustLevel.AXIOM_TRUSTED,
                    message=f"Trusted axiom: {ax.statement[:60]}",
                ))

        # Verify proofs
        for pd in self._proofs:
            vr = self._verify_proof(kernel, pd)
            results.append(SpecResult(
                name=pd.claim[:60],
                kind="proof",
                target_name=pd.target_name,
                success=vr.success,
                trust_level=vr.trust_level,
                message=vr.message,
                axioms_used=vr.axioms_used,
            ))

        total_specs = len(results)
        verified = sum(1 for r in results if r.success and r.kind != "axiom")
        failed = sum(1 for r in results if not r.success)
        axiom_only = sum(1 for r in results if r.kind == "axiom")

        return SidecarReport(
            module_name=self.name,
            total_specs=total_specs,
            verified=verified,
            failed=failed,
            axiom_only=axiom_only,
            results=results,
        )

    def _verify_guarantee(
        self, kernel: ProofKernel, es: ExternalSpec, g: str,
    ) -> VerificationResult:
        """Verify a single guarantee from an ExternalSpec."""
        ctx = Context()
        goal = Judgment(
            context=ctx,
            kind=JudgmentKind.TYPE_CHECK,
            term=Var("_result"),
            type_=RefinementType(
                base_type=PyObjType(),
                predicate=g,
            ),
        )
        proof = Structural(description=f"sidecar spec: {g}")
        return kernel.verify(ctx, goal, proof)

    def _verify_proof(
        self, kernel: ProofKernel, pd: ProofDecl,
    ) -> VerificationResult:
        """Verify a single proof declaration."""
        ctx = Context()
        goal = Judgment(
            context=ctx,
            kind=JudgmentKind.TYPE_CHECK,
            term=Var("_claim"),
            type_=RefinementType(
                base_type=PyBoolType(),
                predicate=pd.claim,
            ),
        )

        # Axiom shortcut
        if pd.axiom_name:
            proof_term = AxiomInvocation(
                name=pd.axiom_name,
                module=pd.axiom_module,
            )
            return kernel.verify(ctx, goal, proof_term)

        # Direct proof term
        if pd.proof_term is not None:
            return kernel.verify(ctx, goal, pd.proof_term)

        # Proof callback
        if pd.proof_fn is not None:
            pb = ProofBuilder(kernel, ctx, goal=goal)
            try:
                result = pd.proof_fn(pb)
                if isinstance(result, VerificationResult):
                    pd.result = result
                    return result
                # If the callback returned a ProofTerm instead
                if isinstance(result, ProofTerm):
                    vr = kernel.verify(ctx, goal, result)
                    pd.result = vr
                    return vr
            except Exception as e:
                return VerificationResult.fail(
                    f"Proof callback error: {e}"
                )

        # Fallback: structural
        proof = Structural(description=f"sidecar proof: {pd.claim}")
        return kernel.verify(ctx, goal, proof)

    # ── kernel installation ──────────────────────────────────────

    def install(self, kernel: ProofKernel) -> None:
        """Install all axioms and specs from this sidecar into a kernel.

        This adds all axiom declarations to the kernel's axiom registry
        so they can be invoked in proofs.
        """
        for ax_name, ax in self._axioms.items():
            entry = ax.to_axiom_entry()
            qualified = ax.qualified_name
            kernel.axiom_registry[ax_name] = entry
            kernel.axiom_registry[qualified] = entry
            kernel.register_axiom(ax_name, ax.statement, module=ax.module)

        # Also register spec guarantees as structural axioms
        for spec_name, es in self._specs.items():
            for i, g in enumerate(es.guarantees):
                ax_name_auto = f"_sidecar_{spec_name}_{i}"
                kernel.register_axiom(
                    ax_name_auto,
                    g,
                    module=es.module_name,
                )

    # ── serialization ────────────────────────────────────────────

    def to_json(self) -> dict:
        """Serialize the sidecar module to a JSON-compatible dict."""
        return {
            "name": self.name,
            "target_module": self.target_module,
            "version": self.version,
            "specs": {k: v.to_json() for k, v in self._specs.items()},
            "axioms": {k: v.to_json() for k, v in self._axioms.items()},
            "proofs": [p.to_json() for p in self._proofs],
        }

    @classmethod
    def from_json(cls, data: dict) -> SidecarModule:
        """Load a sidecar module from a JSON dict."""
        sm = cls(
            name=data["name"],
            target_module=data.get("target_module", data["name"]),
            version=data.get("version", ""),
        )
        for k, v in data.get("specs", {}).items():
            sm._specs[k] = ExternalSpec.from_json(v)
        for k, v in data.get("axioms", {}).items():
            sm._axioms[k] = AxiomDecl.from_json(v)
        for p in data.get("proofs", []):
            sm._proofs.append(ProofDecl.from_json(p))
        return sm

    @classmethod
    def from_file(cls, path: str) -> SidecarModule:
        """Load a sidecar module from a ``.deppy`` or ``.json`` file."""
        p = Path(path)
        if p.suffix == ".json":
            with open(p) as f:
                return cls.from_json(json.load(f))
        elif p.suffix == ".deppy":
            return _parse_deppy_file(p)
        else:
            raise ValueError(f"Unsupported sidecar file format: {p.suffix}")

    # ── accessors ────────────────────────────────────────────────

    @property
    def specs(self) -> dict[str, ExternalSpec]:
        """All registered specs."""
        return dict(self._specs)

    @property
    def axioms(self) -> dict[str, AxiomDecl]:
        """All registered axioms."""
        return dict(self._axioms)

    @property
    def proofs(self) -> list[ProofDecl]:
        """All registered proofs."""
        return list(self._proofs)

    @property
    def verifies(self) -> list["VerifyDecl"]:
        """All registered ``verify`` blocks (code-property verifications)."""
        return list(self._verifies)

    def verify(
        self,
        name: str,
        *,
        function: str,
        property: str,
        foundation: str = "",
        fibration_type: str = "",
        use_cubical: bool = False,
    ) -> "VerifyDecl":
        v = VerifyDecl(
            name=name,
            function=function,
            property=property,
            foundation=foundation,
            fibration_type=fibration_type,
            use_cubical=use_cubical,
        )
        self._verifies.append(v)
        return v

    def get_spec(self, name: str) -> ExternalSpec:
        """Look up a spec by target name.

        Returns a skeleton :class:`ExternalSpec` when *name* is not
        registered, so callers can always access ``.precondition`` etc.
        """
        spec = self._specs.get(name)
        if spec is not None:
            return spec
        # Build a minimal skeleton so book examples don't crash.
        parts = name.rsplit(".", 1)
        mod = parts[0] if len(parts) > 1 else self.name
        return ExternalSpec(
            target=None,
            target_name=name,
            module_name=mod,
        )

    def get_axiom(self, name: str) -> AxiomDecl | None:
        """Look up an axiom by name."""
        return self._axioms.get(name)

    def __repr__(self) -> str:
        return (
            f"SidecarModule({self.name!r}, "
            f"specs={len(self._specs)}, "
            f"axioms={len(self._axioms)}, "
            f"proofs={len(self._proofs)})"
        )


# ═══════════════════════════════════════════════════════════════════
#  §7  @about decorator — attach specs to external functions
# ═══════════════════════════════════════════════════════════════════

_ACTIVE_SIDECAR: SidecarModule | None = None


def set_active_sidecar(module: SidecarModule | None) -> None:
    """Set the active sidecar module for @about decorators."""
    global _ACTIVE_SIDECAR
    _ACTIVE_SIDECAR = module


def get_active_sidecar() -> SidecarModule | None:
    """Get the current active sidecar module."""
    return _ACTIVE_SIDECAR


def about(target: Any, *, sidecar: SidecarModule | None = None) -> Callable[[F], F]:
    """Attach a spec to an external function via a decorator.

    The decorated function body acts as the *specification* — it is NOT
    a replacement for the target.  Guarantees, preconditions, and purity
    annotations on the wrapper are bound to the target.

    Usage::

        @about(sympy.simplify)
        @guarantee("simplify is idempotent")
        @pure
        def simplify_spec(e):
            return sympy.simplify(e)

    The spec metadata is extracted from the wrapper and registered in
    the active SidecarModule (or the one passed via ``sidecar=``).
    """
    def decorator(f: F) -> F:
        meta = _get_spec(f)
        sc = sidecar or _ACTIVE_SIDECAR
        if sc is not None:
            sc.register_about(target, meta)
        else:
            # Store for later pickup
            if not hasattr(f, "_deppy_about"):
                f._deppy_about = []  # type: ignore[attr-defined]
            f._deppy_about.append((target, meta))  # type: ignore[attr-defined]
        return f
    return decorator


def external_spec(
    func_or_class: Any,
    *,
    guarantee: str | list[str] | None = None,
    requires: Callable | str | None = None,
    ensures: Callable | str | None = None,
    pure: bool = False,
    sidecar: SidecarModule | None = None,
) -> ExternalSpec:
    """Shorthand to create and register an ExternalSpec.

    If a sidecar module is active or passed, the spec is registered there.

    Usage::

        es = external_spec(sympy.expand,
            guarantee="distributes over addition",
            pure=True,
        )
    """
    sc = sidecar or _ACTIVE_SIDECAR
    if sc is not None:
        return sc.spec(
            func_or_class,
            guarantee=guarantee,
            requires=requires,
            ensures=ensures,
            pure=pure,
        )
    # Standalone spec
    target_name = _resolve_target_name(func_or_class)
    guarantees = [guarantee] if isinstance(guarantee, str) else (guarantee or [])
    return ExternalSpec(
        target=func_or_class,
        target_name=target_name,
        module_name="",
        guarantees=guarantees,
        preconditions=[requires] if requires else [],
        postconditions=[ensures] if ensures else [],
        is_pure=pure,
    )


# ═══════════════════════════════════════════════════════════════════
#  §8  .deppy file parser
# ═══════════════════════════════════════════════════════════════════

def _parse_deppy_file(path: Path) -> SidecarModule:
    """Parse a ``.deppy`` declarative sidecar file.

    Format::

        # comment
        module: sympy
        version: ">=1.12"

        spec sympy.expand:
          guarantee: "expand(a+b) == expand(a) + expand(b)"
          pure: true
          axiom expand_distributive: "expand(a + b) == expand(a) + expand(b)"

        spec sympy.Matrix.det:
          guarantee: "determinant is multiplicative"
          pure: true

        proof expand_idem:
          target: sympy.expand
          by: axiom expand_idempotent
    """
    text = path.read_text()
    lines = text.splitlines()

    module_name = path.stem
    version = ""
    specs: dict[str, dict] = {}
    proofs: list[dict] = []
    foundations: list[dict] = []
    verifies: list[dict] = []
    lemmas: list[dict] = []                       # F13
    imports: list[str] = []                        # F13
    foundation_deps: dict[str, list[str]] = {}    # F11
    symbolic_constants: dict[str, str] = {}       # symbolic constants
    predicates: dict[str, str] = {}                # F14: custom predicates

    current_block: str = ""      # "spec" / "proof" / "verify"
    current_key: str = ""        # e.g. "sympy.expand" or proof name
    current_data: dict = {}
    # AUDIT 1.13 — multi-line ``by_lean: |`` collector.
    in_pipe_block: str = ""      # "by_lean" or "" when not collecting
    pipe_indent: int = 0
    pipe_lines: list[str] = []

    # CODE-TYPES / lean_imports / lean_preamble top-level collectors.
    _top_code_types_collected: dict[str, str] = {}
    _top_lean_imports_collected: list[str] = []
    _top_lean_preamble_collected: list[str] = [""]   # boxed for closure write

    def _flush() -> None:
        nonlocal current_block, current_key, current_data
        if current_block == "spec" and current_key:
            specs[current_key] = dict(current_data)
        elif current_block == "proof" and current_key:
            proofs.append({"name": current_key, **current_data})
        elif current_block == "verify" and current_key:
            verifies.append({"name": current_key, **current_data})
        elif current_block == "lemma" and current_key:
            lemmas.append({"name": current_key, **current_data})
        current_block = ""
        current_key = ""
        current_data = {}

    for raw_line in lines:
        line = raw_line.strip()

        # AUDIT 1.13 — multi-line ``by_lean: |`` collector.
        # If we're in a pipe block, accumulate indented lines until
        # we hit a less-indented (or empty) line or a new directive.
        if in_pipe_block:
            indent = len(raw_line) - len(raw_line.lstrip())
            if not line:
                pipe_lines.append("")
                continue
            if indent > pipe_indent:
                pipe_lines.append(raw_line[pipe_indent + 2:])
                continue
            # End of pipe block.
            collected = "\n".join(pipe_lines).rstrip()
            if in_pipe_block == "_top_code_types":
                # Parse each line as ``name: signature``.
                for cl in collected.splitlines():
                    cl = cl.strip()
                    if not cl or cl.startswith("--") or cl.startswith("#"):
                        continue
                    if ":" in cl:
                        n, sig = cl.split(":", 1)
                        # Stored on the top-level ``_top_collected``
                        # dict for post-loop transfer.
                        _top_code_types_collected[n.strip()] = sig.strip()
            elif in_pipe_block == "_top_lean_imports":
                _top_lean_imports_collected.extend(
                    l.strip() for l in collected.splitlines()
                    if l.strip()
                )
            elif in_pipe_block == "_top_lean_preamble":
                _top_lean_preamble_collected[0] = collected
            else:
                current_data[in_pipe_block] = collected
            in_pipe_block = ""
            pipe_lines = []

        # Skip comments and blank lines
        if not line or line.startswith("#"):
            continue

        # Top-level directives
        if line.startswith("module:"):
            module_name = line.split(":", 1)[1].strip().strip('"').strip("'")
            continue
        if line.startswith("version:"):
            version = line.split(":", 1)[1].strip().strip('"').strip("'")
            continue

        # Top-level ``foundation NAME: "<statement>" [@ citation]``
        m_found = re.match(
            r"^foundation\s+([\w.]+)\s*:\s*[\"'](.+?)[\"']\s*(?:@\s*(.+))?$",
            line,
        )
        if m_found:
            _flush()
            foundations.append({
                "name": m_found.group(1),
                "statement": m_found.group(2),
                "citation": (m_found.group(3) or "").strip().strip('"').strip("'"),
            })
            continue

        # F11 — Foundation dependencies:
        # ``foundation_deps NAME: F1, F2, ...``
        m_deps = re.match(
            r"^foundation_deps\s+([\w.]+)\s*:\s*(.+)$", line,
        )
        if m_deps:
            _flush()
            foundation_deps[m_deps.group(1)] = [
                d.strip() for d in m_deps.group(2).split(",") if d.strip()
            ]
            continue

        # F13 — Imports:
        # ``import other.deppy``
        m_imp = re.match(r"^import\s+(\S+)\s*$", line)
        if m_imp:
            _flush()
            imports.append(m_imp.group(1))
            continue

        # F14 — Custom predicate declaration:
        # ``predicate NAME: "<body>"``
        m_pred = re.match(
            r'^predicate\s+([\w]+)\s*:\s*[\"\'](.+?)[\"\']\s*$', line,
        )
        if m_pred:
            _flush()
            predicates[m_pred.group(1)] = m_pred.group(2)
            continue

        # Symbolic constant: ``constant NAME: "<expr>"``
        m_const = re.match(
            r'^constant\s+([\w]+)\s*:\s*[\"\'](.+?)[\"\']\s*$', line,
        )
        if m_const:
            _flush()
            symbolic_constants[m_const.group(1)] = m_const.group(2)
            continue

        # F13 — Lemma block: ``lemma NAME:``
        m_lemma = re.match(r"^lemma\s+([\w.]+)\s*:\s*$", line)
        if m_lemma:
            _flush()
            current_block = "lemma"
            current_key = m_lemma.group(1)
            current_data = {}
            continue

        # CODE-TYPES top-level pipe block:
        #   code_types: |
        #     sqrt: Int → Int
        #     sum_zip_sub_sq: Point → Point → Int
        if re.match(r"^code_types\s*:\s*\|\s*$", line):
            _flush()
            in_pipe_block = "_top_code_types"
            pipe_indent = len(raw_line) - len(raw_line.lstrip())
            pipe_lines = []
            continue
        if re.match(r"^lean_imports\s*:\s*\|\s*$", line):
            _flush()
            in_pipe_block = "_top_lean_imports"
            pipe_indent = len(raw_line) - len(raw_line.lstrip())
            pipe_lines = []
            continue
        if re.match(r"^lean_preamble\s*:\s*\|\s*$", line):
            _flush()
            in_pipe_block = "_top_lean_preamble"
            pipe_indent = len(raw_line) - len(raw_line.lstrip())
            pipe_lines = []
            continue

        # Top-level ``axiom NAME: "<statement>"`` outside any spec block —
        # standalone library axiom (e.g. for libraries with no enclosing
        # spec).  When inside a ``spec`` block we still match the
        # spec-scoped form below.
        m_top_ax = re.match(
            r"^axiom\s+([\w]+)\s*:\s*[\"'](.+?)[\"']\s*$", line
        )
        if m_top_ax and not current_block:
            _flush()
            # Stash without a spec target — the post-pass attaches it
            # to the most-recent spec target if available, else to a
            # synthetic ``__module__`` target.
            specs.setdefault("__module__", {
                "guarantees": [],
                "axioms": [],
                "_implicit": True,
            }).setdefault("axioms", []).append({
                "name": m_top_ax.group(1),
                "statement": m_top_ax.group(2),
            })
            continue

        # Block starts
        m_spec = re.match(r"^spec\s+([\w.]+)\s*:\s*$", line)
        if m_spec:
            _flush()
            current_block = "spec"
            current_key = m_spec.group(1)
            current_data = {"guarantees": [], "axioms": []}
            continue

        m_proof = re.match(r"^proof\s+([\w.]+)\s*:\s*$", line)
        if m_proof:
            _flush()
            current_block = "proof"
            current_key = m_proof.group(1)
            current_data = {}
            continue

        m_verify = re.match(r"^verify\s+([\w.]+)\s*:\s*$", line)
        if m_verify:
            _flush()
            current_block = "verify"
            current_key = m_verify.group(1)
            current_data = {}
            continue

        # Inside a block
        if current_block:
            # Indented properties
            m_kv = re.match(r"^(\w+)\s*:\s*(.+)$", line)
            if m_kv:
                key = m_kv.group(1)
                val = m_kv.group(2).strip().strip('"').strip("'")
                if key == "guarantee":
                    current_data.setdefault("guarantees", []).append(val)
                elif key == "pure":
                    current_data["pure"] = val.lower() in ("true", "yes", "1")
                elif key == "total":
                    current_data["total"] = val.lower() in ("true", "yes", "1")
                elif key == "exception_free":
                    # exception_free: when "cond"  OR  exception_free: true
                    if val.lower() in ("true", "yes", "1"):
                        current_data.setdefault("exception_free_when", []).append("true")
                    elif val.lower().startswith("when "):
                        cond = val[5:].strip().strip('"').strip("'")
                        current_data.setdefault("exception_free_when", []).append(cond)
                    else:
                        current_data.setdefault("exception_free_when", []).append(val)
                elif key == "safe_when":
                    current_data.setdefault("safe_when", []).append(val)
                elif key == "decreases":
                    current_data.setdefault("decreases", []).append(val)
                elif key == "target":
                    current_data["target"] = val
                elif key == "by":
                    current_data["by"] = val
                elif key == "function" and current_block == "verify":
                    current_data["function"] = val
                elif key == "property" and current_block == "verify":
                    current_data["property"] = val
                elif key == "via" and current_block == "verify":
                    # ``via: foundation NAME`` or ``via: kernel.derive``
                    current_data["via"] = val
                elif key == "fibration" and current_block == "verify":
                    current_data["fibration"] = val
                elif key == "cubical" and current_block == "verify":
                    current_data["cubical"] = val.lower() in ("true", "yes", "1")
                # F9 — verify binders / requires / ensures
                elif key == "binders" and current_block == "verify":
                    bs: dict[str, str] = {}
                    for tok in val.split(","):
                        tok = tok.strip()
                        if ":" in tok:
                            k, v = tok.split(":", 1)
                            bs[k.strip()] = v.strip()
                    current_data["binders"] = bs
                elif key == "requires" and current_block == "verify":
                    current_data["requires"] = val
                elif key == "ensures" and current_block == "verify":
                    current_data["ensures"] = val
                # F10 — single-line tactic block; multi-line via ``|``.
                elif key == "by_lean" and current_block == "verify":
                    if val.strip() == "|":
                        in_pipe_block = "by_lean"
                        pipe_indent = (
                            len(raw_line) - len(raw_line.lstrip())
                        )
                        pipe_lines = []
                    else:
                        current_data["by_lean"] = val
                # PSDL — Python-Semantic Deppy Language block.
                elif key == "psdl_proof" and current_block == "verify":
                    if val.strip() == "|":
                        in_pipe_block = "psdl_proof"
                        pipe_indent = (
                            len(raw_line) - len(raw_line.lstrip())
                        )
                        pipe_lines = []
                    else:
                        current_data["psdl_proof"] = val
                # F12 — implementation hash pinning
                elif key == "expects_sha256" and current_block == "verify":
                    current_data["expects_sha256"] = val
                # F14 — effect / decreases / Z3 binders
                elif key == "effect" and current_block == "verify":
                    current_data["effect"] = val
                elif key == "decreases" and current_block == "verify":
                    current_data["decreases"] = val
                elif key == "z3_binders" and current_block == "verify":
                    bs2: dict[str, str] = {}
                    for tok in val.split(","):
                        tok = tok.strip()
                        if ":" in tok:
                            k, v = tok.split(":", 1)
                            bs2[k.strip()] = v.strip()
                    current_data["z3_binders"] = bs2
                # F15 — cubical / cohomology / counterexample directives
                elif key == "cubical_dim" and current_block == "verify":
                    try:
                        current_data["cubical_dim"] = int(val)
                    except ValueError:
                        current_data["cubical_dim"] = 0
                elif key == "cohomology_level" and current_block == "verify":
                    try:
                        current_data["cohomology_level"] = int(val)
                    except ValueError:
                        current_data["cohomology_level"] = 0
                elif key == "expecting_counterexample" and current_block == "verify":
                    current_data["expecting_counterexample"] = (
                        val.lower() in ("true", "yes", "1")
                    )
                # F13 — lemma block fields
                elif key == "proves" and current_block == "lemma":
                    current_data["statement"] = val
                elif key == "by" and current_block == "lemma":
                    current_data["proof"] = val
                else:
                    current_data[key] = val
                continue

            # raises <ExcType>: when "condition"
            m_raises = re.match(
                r"^raises\s+([\w.]+)\s*:\s*(?:when\s+)?[\"']?(.+?)[\"']?\s*$",
                line,
            )
            if m_raises and current_block == "spec":
                exc_type = m_raises.group(1)
                condition = m_raises.group(2).strip().strip('"').strip("'")
                current_data.setdefault("raises", []).append({
                    "type": exc_type,
                    "when": condition,
                })
                continue

            # Axiom inside a spec block
            m_ax = re.match(
                r"^axiom\s+([\w]+)\s*:\s*[\"'](.+)[\"']\s*$", line
            )
            if m_ax and current_block == "spec":
                current_data.setdefault("axioms", []).append({
                    "name": m_ax.group(1),
                    "statement": m_ax.group(2),
                })
                continue

    # AUDIT 1.13 — flush any open pipe block before final flush.
    if in_pipe_block:
        collected = "\n".join(pipe_lines).rstrip()
        if in_pipe_block == "_top_code_types":
            for cl in collected.splitlines():
                cl = cl.strip()
                if not cl or cl.startswith("--") or cl.startswith("#"):
                    continue
                if ":" in cl:
                    n, sig = cl.split(":", 1)
                    _top_code_types_collected[n.strip()] = sig.strip()
        elif in_pipe_block == "_top_lean_imports":
            _top_lean_imports_collected.extend(
                l.strip() for l in collected.splitlines() if l.strip()
            )
        elif in_pipe_block == "_top_lean_preamble":
            _top_lean_preamble_collected[0] = collected
        elif current_data is not None:
            current_data[in_pipe_block] = collected
    _flush()

    # Build the SidecarModule
    sm = SidecarModule(module_name, version=version)

    # Foundations first — they may be cited by proofs below.
    for f in foundations:
        sm.foundation(
            f["name"],
            f["statement"],
            citation=f.get("citation", ""),
        )

    for spec_target, spec_data in specs.items():
        if spec_data.get("_implicit") and not spec_data.get("axioms"):
            continue
        es = sm.spec(
            spec_target,  # use string name — target library may not be imported
            guarantee=spec_data.get("guarantees"),
            pure=spec_data.get("pure", False),
        )
        # Populate runtime safety fields
        for cond in spec_data.get("exception_free_when", []):
            es.exception_free_when.append(cond)
        for r in spec_data.get("raises", []):
            es.raises_declarations.append((r["type"], r["when"]))
        for cond in spec_data.get("safe_when", []):
            es.safe_when.append(cond)
        if spec_data.get("total", False):
            es.is_total = True
        for measure in spec_data.get("decreases", []):
            es.decreases.append(measure)

        for ax in spec_data.get("axioms", []):
            sm.axiom(
                spec_target,
                ax["statement"],
                name=ax["name"],
            )

    for proof_data in proofs:
        by_clause = (proof_data.get("by", "") or "").strip()
        axiom_name = ""
        axiom_module = ""
        foundation_name = ""
        chain_axioms: list[str] = []
        rewrite_with = ""
        rewrite_then_cite = ""

        if by_clause.startswith("axiom "):
            axiom_name = by_clause[len("axiom "):].strip()
            axiom_module = module_name
        elif by_clause.startswith("foundation "):
            foundation_name = by_clause[len("foundation "):].strip()
        elif by_clause == "refl":
            pass  # signalled by by_clause itself
        elif by_clause.startswith("chain "):
            tail = by_clause[len("chain "):].strip()
            chain_axioms = [t.strip() for t in tail.split(",") if t.strip()]
        elif by_clause.startswith("composition "):
            tail = by_clause[len("composition "):].strip()
            chain_axioms = [t.strip() for t in tail.split("&") if t.strip()]
        else:
            # ``rewrite F then cite A`` form
            m_rw = re.match(
                r"^rewrite\s+([\w.]+)\s+then\s+cite\s+([\w.]+)\s*$",
                by_clause,
            )
            if m_rw:
                rewrite_with = m_rw.group(1)
                rewrite_then_cite = m_rw.group(2)

        sm.prove(
            proof_data.get("name", "unnamed"),
            target=proof_data.get("target"),
            by_axiom=axiom_name or None,
            axiom_module=axiom_module or None,
            by_clause=by_clause,
            foundation_name=foundation_name,
            chain_axioms=chain_axioms,
            rewrite_with=rewrite_with,
            rewrite_then_cite=rewrite_then_cite,
        )

    # ``verify`` blocks — code-property verification.
    for v in verifies:
        via = (v.get("via", "") or "").strip()
        foundation_name = ""
        if via.startswith("foundation "):
            foundation_name = via[len("foundation "):].strip()
        fibration = (v.get("fibration", "") or "").strip()
        fibration_type = ""
        if fibration.startswith("isinstance "):
            fibration_type = fibration[len("isinstance "):].strip()
        decl = sm.verify(
            v.get("name", "unnamed"),
            function=v.get("function", "") or "",
            property=v.get("property", "") or "",
            foundation=foundation_name,
            fibration_type=fibration_type,
            use_cubical=bool(v.get("cubical", False)),
        )
        # F9-F15 — pull extended fields from the parsed dict.
        decl.binders = dict(v.get("binders", {}) or {})
        decl.requires = v.get("requires", "") or ""
        decl.ensures = v.get("ensures", "") or ""
        decl.by_lean = v.get("by_lean", "") or ""
        decl.psdl_proof = v.get("psdl_proof", "") or ""
        decl.expects_sha256 = v.get("expects_sha256", "") or ""
        decl.effect = v.get("effect", "") or ""
        decl.decreases = v.get("decreases", "") or ""
        decl.z3_binders = dict(v.get("z3_binders", {}) or {})
        decl.cubical_dim = int(v.get("cubical_dim", 0) or 0)
        decl.cohomology_level = int(v.get("cohomology_level", 0) or 0)
        decl.expecting_counterexample = bool(
            v.get("expecting_counterexample", False)
        )

    # F11 — foundation dependencies
    sm._foundation_deps = foundation_deps
    # F13 — imports + lemmas
    sm._imports = imports
    for ldata in lemmas:
        ldecl = LemmaDecl(
            name=ldata.get("name", "unnamed"),
            statement=ldata.get("statement", "") or "",
            proof=ldata.get("proof", "") or "",
        )
        sm._lemmas.append(ldecl)
    # F14 — symbolic constants + custom predicates
    sm._symbolic_constants = symbolic_constants
    sm._predicates = predicates
    # CODE-TYPES + lean_imports + lean_preamble.
    sm._code_types = dict(_top_code_types_collected)
    sm._lean_imports = list(_top_lean_imports_collected)
    sm._lean_preamble = _top_lean_preamble_collected[0]

    # AUDIT 1.9 — recursive .deppy imports.  For each ``import
    # other.deppy`` directive, load the imported file and merge
    # its foundations / lemmas / predicates / constants into this
    # module.  Cycles are guarded by a ``_imported_paths`` set.
    base_dir = path.parent
    for imp in imports:
        try:
            ipath = base_dir / imp
            if not ipath.exists():
                ipath = Path(imp)  # try absolute
            if not ipath.exists():
                continue
            already = getattr(sm, "_imported_paths", None) or set()
            if str(ipath.resolve()) in already:
                continue
            imported = _parse_deppy_file(ipath)
            # Merge foundations.
            for f_name, f in (imported.foundations or {}).items():
                if f_name not in sm._foundations:
                    sm._foundations[f_name] = f
            # Merge lemmas.
            for lm in getattr(imported, "_lemmas", []) or []:
                sm._lemmas.append(lm)
            # Merge predicates / constants.
            for k, v in getattr(imported, "_predicates", {}).items():
                sm._predicates.setdefault(k, v)
            for k, v in getattr(imported, "_symbolic_constants", {}).items():
                sm._symbolic_constants.setdefault(k, v)
            # Merge foundation deps.
            for k, v in getattr(imported, "_foundation_deps", {}).items():
                sm._foundation_deps.setdefault(k, v)
            # Merge code_types and lean_imports/lean_preamble.
            for k, v in (
                getattr(imported, "_code_types", {}) or {}
            ).items():
                sm._code_types.setdefault(k, v)
            for line in getattr(imported, "_lean_imports", []) or []:
                if line not in sm._lean_imports:
                    sm._lean_imports.append(line)
            imp_preamble = (
                getattr(imported, "_lean_preamble", "") or ""
            )
            if imp_preamble and imp_preamble not in (
                sm._lean_preamble or ""
            ):
                sm._lean_preamble = (
                    (sm._lean_preamble + "\n") if sm._lean_preamble else ""
                ) + imp_preamble
            # Cycle guard: also propagate the imported's own
            # imported_paths so a downstream import doesn't re-load
            # something a transitive ancestor already loaded.
            already.add(str(ipath.resolve()))
            already.update(
                getattr(imported, "_imported_paths", None) or set()
            )
            sm._imported_paths = already
        except Exception:
            pass

    # AUDIT 1.10 — substitute custom predicates and symbolic
    # constants into axiom statements.  When a user declares
    # ``predicate is_collinear: "..."`` and ``constant tau: "2*pi"``
    # we expand calls/refs in the foundation/axiom/proof statements.
    if sm._predicates or sm._symbolic_constants:
        _substitute_predicates_and_constants(sm)

    return sm


def _substitute_predicates_and_constants(sm) -> None:
    """Substitute custom predicates and constants into all axiom /
    foundation / verify statements.

    Predicate substitution: ``pred_name(arg1, ...)`` → the predicate
    body with formal params replaced by the actual args (best-effort
    string substitution; we don't do full beta reduction).

    Constant substitution: bare-word references to a constant name
    are replaced with the constant's body.
    """
    import re as _re
    preds = dict(sm._predicates or {})
    consts = dict(sm._symbolic_constants or {})

    def _expand(text: str) -> str:
        if not text:
            return text
        # Constants: replace whole-word matches.
        for cname, cbody in consts.items():
            text = _re.sub(
                rf"\b{_re.escape(cname)}\b", f"({cbody})", text,
            )
        # Predicates: replace calls.  We do a simple regex match
        # without proper arg-substitution (treating the predicate
        # like a macro that consumes its args verbatim).
        for pname, pbody in preds.items():
            text = _re.sub(
                rf"\b{_re.escape(pname)}\s*\(([^)]*)\)",
                lambda m, body=pbody: f"({body})",
                text,
            )
        return text

    # Apply to foundations.
    for f_name, f in list(sm._foundations.items()):
        if hasattr(f, "statement"):
            f.statement = _expand(f.statement)
    # Apply to axioms.
    for ax_name, ax in list(sm._axioms.items()):
        if hasattr(ax, "statement"):
            ax.statement = _expand(ax.statement)
    # Apply to verifies.
    for v in sm._verifies:
        v.property = _expand(v.property)
        v.requires = _expand(v.requires)
        v.ensures = _expand(v.ensures)


# ═══════════════════════════════════════════════════════════════════
#  §9  SidecarVerifier — verify sidecar modules
# ═══════════════════════════════════════════════════════════════════

class SidecarVerifier:
    """Verify sidecar proof modules against their target libraries.

    Usage::

        verifier = SidecarVerifier()
        report = verifier.verify(sidecar_module)
        print(report.summary())

        # Or verify a file
        report = verifier.verify_file("sympy_proofs.deppy")

        # Or a directory of .deppy files
        reports = verifier.verify_directory("proofs/")
    """

    def __init__(self, kernel: ProofKernel | None = None) -> None:
        self._kernel = kernel or ProofKernel()

    def verify(self, sidecar: SidecarModule) -> SidecarReport:
        """Verify all proofs in a sidecar module."""
        return sidecar.verify_all(kernel=self._kernel)

    def verify_file(self, path: str) -> SidecarReport:
        """Load and verify a ``.deppy`` or ``.json`` sidecar file."""
        sm = SidecarModule.from_file(path)
        return self.verify(sm)

    def verify_directory(self, directory: str) -> list[SidecarReport]:
        """Verify all ``.deppy`` and ``.json`` sidecar files in a directory."""
        d = Path(directory)
        reports: list[SidecarReport] = []
        for p in sorted(d.iterdir()):
            if p.suffix in (".deppy", ".json"):
                try:
                    reports.append(self.verify_file(str(p)))
                except Exception as e:
                    reports.append(SidecarReport(
                        module_name=p.stem,
                        total_specs=0,
                        verified=0,
                        failed=1,
                        results=[SpecResult(
                            name=str(p),
                            kind="error",
                            target_name="",
                            success=False,
                            trust_level=TrustLevel.UNTRUSTED,
                            message=f"File error: {e}",
                        )],
                    ))
        return reports


# ═══════════════════════════════════════════════════════════════════
#  §10  Worked Example: SymPy Sidecar
# ═══════════════════════════════════════════════════════════════════

def _build_sympy_example() -> SidecarModule:
    """Build a worked sidecar module for SymPy (no sympy import needed).

    Demonstrates 10+ specs and 5+ proofs using string-based targets.
    """
    sm = SidecarModule("sympy", version=">=1.12")

    # ── Specs (10+) ──────────────────────────────────────────────

    sm.spec("sympy.expand",
        guarantee="expand distributes over addition",
        pure=True,
    )

    sm.spec("sympy.simplify",
        guarantee=[
            "simplify is idempotent: simplify(simplify(e)) == simplify(e)",
            "simplify preserves value: simplify(e).equals(e)",
        ],
        pure=True,
    )

    sm.spec("sympy.factor",
        guarantee="factor produces an equivalent factored form",
        pure=True,
    )

    sm.spec("sympy.diff",
        guarantee="diff returns the symbolic derivative",
        pure=True,
    )

    sm.spec("sympy.integrate",
        guarantee="integrate returns the symbolic antiderivative",
        pure=True,
    )

    sm.spec("sympy.solve",
        guarantee="solve returns roots of the equation",
        pure=True,
    )

    sm.spec("sympy.Matrix.det",
        guarantee=[
            "det of identity is 1",
            "det is multiplicative: det(A*B) == det(A)*det(B)",
        ],
        pure=True,
    )

    sm.spec("sympy.Matrix.inv",
        guarantee="A * A.inv() == Identity",
        requires=lambda A: True,  # det(A) != 0
        pure=True,
    )

    sm.spec("sympy.limit",
        guarantee="limit computes the limiting value",
        pure=True,
    )

    sm.spec("sympy.series",
        guarantee="series returns a Taylor/Laurent expansion",
        pure=True,
    )

    sm.spec("sympy.Rational",
        guarantee="Rational(p, q) represents exact fraction p/q",
        pure=True,
    )

    sm.spec("sympy.sqrt",
        guarantee="sqrt(x)**2 == x for non-negative x",
        pure=True,
    )

    # ── Axioms ───────────────────────────────────────────────────

    sm.axiom("sympy.expand",
        "expand(a + b) == expand(a) + expand(b)",
        name="expand_distributive",
    )

    sm.axiom("sympy.expand",
        "expand(expand(e)) == expand(e)",
        name="expand_idempotent",
    )

    sm.axiom("sympy.simplify",
        "simplify(simplify(e)) == simplify(e)",
        name="simplify_idempotent",
    )

    sm.axiom("sympy.diff",
        "diff(f + g, x) == diff(f, x) + diff(g, x)",
        name="diff_linearity",
    )

    sm.axiom("sympy.diff",
        "diff(f * g, x) == f * diff(g, x) + g * diff(f, x)",
        name="diff_product_rule",
    )

    sm.axiom("sympy.diff",
        "integrate(diff(f, x), x) == f + C",
        name="ftc_part1",
    )

    sm.axiom("sympy.Matrix.det",
        "det(A * B) == det(A) * det(B)",
        name="det_multiplicative",
    )

    sm.axiom("sympy.Matrix.det",
        "det(Identity(n)) == 1",
        name="det_identity",
    )

    sm.axiom("sympy.Matrix.inv",
        "A * A.inv() == Identity(A.rows)",
        name="inv_right",
        precondition="det(A) != 0",
    )

    sm.axiom("sympy.solve",
        "for r in solve(eq, x): eq.subs(x, r) == 0",
        name="solve_correctness",
    )

    # ── Proofs (5+) ──────────────────────────────────────────────

    sm.prove(
        "expand is idempotent",
        target="sympy.expand",
        by_axiom="expand_idempotent",
        axiom_module="sympy",
    )

    sm.prove(
        "simplify is idempotent",
        target="sympy.simplify",
        by_axiom="simplify_idempotent",
        axiom_module="sympy",
    )

    sm.prove(
        "differentiation is linear",
        target="sympy.diff",
        by_axiom="diff_linearity",
        axiom_module="sympy",
    )

    sm.prove(
        "determinant of identity is 1",
        target="sympy.Matrix.det",
        by_axiom="det_identity",
        axiom_module="sympy",
    )

    sm.prove(
        "determinant is multiplicative",
        target="sympy.Matrix.det",
        by_axiom="det_multiplicative",
        axiom_module="sympy",
    )

    sm.prove(
        "product rule for differentiation",
        target="sympy.diff",
        proof_term=AxiomInvocation(
            name="diff_product_rule", module="sympy",
        ),
    )

    sm.prove(
        "fundamental theorem of calculus (part 1)",
        target="sympy.diff",
        proof=lambda pb: pb.conclude(
            pb.axiom("ftc_part1", "sympy")
        ),
    )

    return sm


# ═══════════════════════════════════════════════════════════════════
#  Exports
# ═══════════════════════════════════════════════════════════════════

__all__ = [
    # Core classes
    "SidecarModule",
    "ExternalSpec",
    "AxiomDecl",
    "ProofDecl",
    "SpecResult",
    "SidecarReport",
    # Verifier
    "SidecarVerifier",
    # Decorators & helpers
    "about",
    "external_spec",
    "set_active_sidecar",
    "get_active_sidecar",
]


# ═══════════════════════════════════════════════════════════════════
#  Self-tests
# ═══════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    import sys

    _counters = {"passed": 0, "failed": 0}
    _errors: list[str] = []

    def check(name: str, cond: bool, msg: str = "") -> None:
        if cond:
            _counters["passed"] += 1
            print(f"  ✓ {name}")
        else:
            _counters["failed"] += 1
            detail = f": {msg}" if msg else ""
            _errors.append(f"{name}{detail}")
            print(f"  ✗ {name}{detail}")

    print("═══ Sidecar Self-Tests ═══\n")

    # ── Test 1: SidecarModule creation ───────────────────────────
    print("§1 SidecarModule creation")
    sm = SidecarModule("testlib", version=">=1.0")
    check("create module", sm.name == "testlib")
    check("version", sm.version == ">=1.0")
    check("target_module", sm.target_module == "testlib")
    check("empty specs", len(sm.specs) == 0)
    check("empty axioms", len(sm.axioms) == 0)
    check("empty proofs", len(sm.proofs) == 0)

    # ── Test 2: Spec registration ────────────────────────────────
    print("\n§2 Spec registration")

    def dummy_fn(x: int) -> int:
        return x * 2

    es = sm.spec(dummy_fn,
        guarantee="doubles the input",
        pure=True,
    )
    check("spec created", es is not None)
    check("spec guarantees", es.guarantees == ["doubles the input"])
    check("spec is_pure", es.is_pure is True)
    check("spec in module", len(sm.specs) == 1)

    es2 = sm.spec("testlib.add",
        guarantee=["returns sum", "is commutative"],
        ensures=lambda a, b, r: r == a + b,
    )
    check("string target", es2.target_name == "testlib.add")
    check("multi guarantee", len(es2.guarantees) == 2)
    check("postcondition", len(es2.postconditions) == 1)

    # ── Test 3: Axiom registration ───────────────────────────────
    print("\n§3 Axiom registration")
    ax = sm.axiom("testlib.add",
        "add(a, b) == add(b, a)",
        name="add_commutative",
    )
    check("axiom created", ax is not None)
    check("axiom name", ax.name == "add_commutative")
    check("axiom target", ax.target == "testlib.add")
    check("axiom statement", "commutative" in ax.statement.lower() or "add" in ax.statement)
    check("axiom in module", len(sm.axioms) == 1)
    check("axiom linked to spec", "add_commutative" in sm._specs["testlib.add"].axioms)

    ax2 = sm.axiom("testlib.add",
        "add(a, 0) == a",
        name="add_identity",
    )
    check("second axiom", len(sm.axioms) == 2)

    # ── Test 4: Proof registration ───────────────────────────────
    print("\n§4 Proof registration")
    pd = sm.prove(
        "addition is commutative",
        target="testlib.add",
        by_axiom="add_commutative",
        axiom_module="testlib",
    )
    check("proof created", pd is not None)
    check("proof claim", pd.claim == "addition is commutative")
    check("proof axiom", pd.axiom_name == "add_commutative")

    pd2 = sm.prove(
        "zero is identity for addition",
        target="testlib.add",
        proof_term=AxiomInvocation(name="add_identity", module="testlib"),
    )
    check("proof with term", pd2.proof_term is not None)

    pd3 = sm.prove(
        "structural property",
        proof=lambda pb: pb.conclude(pb.structural("test")),
    )
    check("proof with callback", pd3.proof_fn is not None)
    check("proofs in module", len(sm.proofs) == 3)

    # ── Test 5: Verification ─────────────────────────────────────
    print("\n§5 Verification")
    kernel = ProofKernel()
    report = sm.verify_all(kernel=kernel)
    check("report module_name", report.module_name == "testlib")
    check("report has results", len(report.results) > 0)
    check("report total_specs", report.total_specs > 0)
    check("axioms installed", "add_commutative" in kernel.axiom_registry)

    # All specs should verify (structural)
    spec_results = [r for r in report.results if r.kind == "spec"]
    check("all specs pass", all(r.success for r in spec_results),
          f"failed: {[r.name for r in spec_results if not r.success]}")

    # All axiom entries should be present
    axiom_results = [r for r in report.results if r.kind == "axiom"]
    check("axioms in report", len(axiom_results) == 2)

    # All proofs should verify
    proof_results = [r for r in report.results if r.kind == "proof"]
    check("all proofs pass", all(r.success for r in proof_results),
          f"failed: {[r.name for r in proof_results if not r.success]}")

    # Summary
    summary = report.summary()
    check("summary not empty", len(summary) > 0)
    check("summary contains module", "testlib" in summary)

    # ── Test 6: JSON serialization ───────────────────────────────
    print("\n§6 JSON serialization")
    data = sm.to_json()
    check("to_json has name", data["name"] == "testlib")
    check("to_json has specs", len(data["specs"]) == 2)
    check("to_json has axioms", len(data["axioms"]) == 2)
    check("to_json has proofs", len(data["proofs"]) == 3)

    # Round-trip
    sm2 = SidecarModule.from_json(data)
    check("from_json name", sm2.name == "testlib")
    check("from_json specs", len(sm2.specs) == 2)
    check("from_json axioms", len(sm2.axioms) == 2)
    check("from_json proofs", len(sm2.proofs) == 3)

    # JSON serialization of sub-objects
    json_str = json.dumps(data, indent=2, default=str)
    check("json serializable", len(json_str) > 100)

    # Report serialization
    report_json = report.to_json()
    check("report to_json", report_json["module_name"] == "testlib")
    report2 = SidecarReport.from_json(report_json)
    check("report roundtrip", report2.module_name == "testlib")

    # ── Test 7: @about decorator ─────────────────────────────────
    print("\n§7 @about decorator")
    sc = SidecarModule("about_test")
    set_active_sidecar(sc)

    def target_fn(x: int) -> int:
        return x + 1

    @about(target_fn)
    @guarantee("increments by 1")
    @pure
    def target_spec(x: int) -> int:
        return target_fn(x)

    check("about registered", len(sc.specs) == 1)
    spec_vals = list(sc.specs.values())
    check("about guarantee", "increments by 1" in spec_vals[0].guarantees)
    check("about pure", spec_vals[0].is_pure is True)

    set_active_sidecar(None)

    # With explicit sidecar
    sc2 = SidecarModule("explicit_test")

    def other_fn(s: str) -> str:
        return s.upper()

    @about(other_fn, sidecar=sc2)
    @guarantee("uppercases string")
    def other_spec(s: str) -> str:
        return other_fn(s)

    check("explicit sidecar", len(sc2.specs) == 1)

    # ── Test 8: external_spec shorthand ──────────────────────────
    print("\n§8 external_spec")
    sc3 = SidecarModule("shorthand_test")

    def lib_fn(a: int, b: int) -> int:
        return a * b

    es3 = external_spec(lib_fn,
        guarantee="multiplies a and b",
        pure=True,
        sidecar=sc3,
    )
    check("external_spec created", es3 is not None)
    check("external_spec in sidecar", len(sc3.specs) == 1)

    # Standalone (no sidecar)
    es4 = external_spec(lib_fn,
        guarantee="standalone spec",
    )
    check("standalone spec", es4 is not None)
    check("standalone guarantees", es4.guarantees == ["standalone spec"])

    # ── Test 9: .deppy file parsing ────────────────────────────
    print("\n§9 .deppy file parsing")

    # Write a temporary deppy file
    deppy_content = textwrap.dedent("""\
        # Test sidecar file
        module: mylib
        version: ">=2.0"

        spec mylib.compute:
          guarantee: "computes correctly"
          pure: true
          axiom compute_idem: "compute(compute(x)) == compute(x)"

        spec mylib.transform:
          guarantee: "transforms data"

        proof compute_is_idem:
          target: mylib.compute
          by: axiom compute_idem
    """)

    deppy_path = Path("_test_sidecar.deppy")
    try:
        deppy_path.write_text(deppy_content)
        sm_file = SidecarModule.from_file(str(deppy_path))
        check("file module name", sm_file.name == "mylib")
        check("file version", sm_file.version == ">=2.0")
        check("file specs", len(sm_file.specs) >= 2)
        check("file axioms", len(sm_file.axioms) >= 1)
        check("file proofs", len(sm_file.proofs) >= 1)

        # Verify the loaded module
        file_report = sm_file.verify_all()
        check("file verify", file_report.total_specs > 0)
        check("file verify passes",
              file_report.failed == 0,
              f"failures: {file_report.failed}")
    finally:
        if deppy_path.exists():
            deppy_path.unlink()

    # JSON file round-trip
    json_path = Path("_test_sidecar.json")
    try:
        with open(json_path, "w") as f:
            json.dump(sm.to_json(), f)
        sm_json = SidecarModule.from_file(str(json_path))
        check("json file load", sm_json.name == "testlib")
    finally:
        if json_path.exists():
            json_path.unlink()

    # ── Test 10: SidecarVerifier ─────────────────────────────────
    print("\n§10 SidecarVerifier")
    verifier = SidecarVerifier()
    vr = verifier.verify(sm)
    check("verifier report", vr.module_name == "testlib")
    check("verifier passes", vr.failed == 0)

    # ── Test 11: Kernel installation ─────────────────────────────
    print("\n§11 Kernel installation")
    k = ProofKernel()
    sm.install(k)
    check("axioms in kernel", "add_commutative" in k.axiom_registry)
    check("axioms in kernel 2", "add_identity" in k.axiom_registry)

    # Verify axiom can be used in a proof
    ctx = Context()
    goal = Judgment(
        context=ctx,
        kind=JudgmentKind.TYPE_CHECK,
        term=Var("_"),
        type_=RefinementType(base_type=PyBoolType(), predicate="add commutes"),
    )
    r = k.verify(ctx, goal, AxiomInvocation(name="add_commutative", module="testlib"))
    check("axiom usable", r.success)

    # ── Test 12: SymPy worked example ────────────────────────────
    print("\n§12 SymPy worked example")
    sympy_sc = _build_sympy_example()
    check("sympy module", sympy_sc.name == "sympy")
    check("sympy specs ≥ 10", len(sympy_sc.specs) >= 10)
    check("sympy axioms ≥ 5", len(sympy_sc.axioms) >= 5)
    check("sympy proofs ≥ 5", len(sympy_sc.proofs) >= 5)

    sympy_report = sympy_sc.verify_all()
    check("sympy verifies", sympy_report.failed == 0,
          f"failures: {sympy_report.failed}")
    check("sympy report total", sympy_report.total_specs > 0)

    print(f"\n{sympy_report.summary()}\n")

    # ── Test 13: ExternalSpec serialization ──────────────────────
    print("§13 ExternalSpec serialization")
    es_json = es.to_json()
    check("es to_json", es_json["is_pure"] is True)
    es_back = ExternalSpec.from_json(es_json)
    check("es roundtrip", es_back.is_pure is True)
    check("es roundtrip guarantees", es_back.guarantees == ["doubles the input"])

    # ── Test 14: AxiomDecl serialization ─────────────────────────
    print("\n§14 AxiomDecl serialization")
    ax_json = ax.to_json()
    check("ax to_json", ax_json["name"] == "add_commutative")
    ax_back = AxiomDecl.from_json(ax_json)
    check("ax roundtrip", ax_back.name == "add_commutative")
    check("ax roundtrip statement", "add" in ax_back.statement)

    # ── Test 15: ProofDecl serialization ─────────────────────────
    print("\n§15 ProofDecl serialization")
    pd_json = pd.to_json()
    check("pd to_json", pd_json["claim"] == "addition is commutative")
    pd_back = ProofDecl.from_json(pd_json)
    check("pd roundtrip", pd_back.claim == "addition is commutative")

    # ── Test 16: resolve_target_name ─────────────────────────────
    print("\n§16 Target name resolution")
    check("string target", _resolve_target_name("my.func") == "my.func")
    check("callable target", "dummy_fn" in _resolve_target_name(dummy_fn))
    check("class target", "SidecarModule" in _resolve_target_name(SidecarModule))

    # ── Test 17: Proof with callback ─────────────────────────────
    print("\n§17 Proof with callback")
    sm_cb = SidecarModule("callback_test")
    sm_cb.axiom("callback_test.fn",
        "fn(fn(x)) == fn(x)",
        name="fn_idem",
    )
    sm_cb.prove(
        "fn is idempotent",
        target="callback_test.fn",
        proof=lambda pb: pb.conclude(
            pb.axiom("fn_idem", "callback_test")
        ),
    )
    cb_report = sm_cb.verify_all()
    cb_proofs = [r for r in cb_report.results if r.kind == "proof"]
    check("callback proof passes", len(cb_proofs) > 0 and cb_proofs[0].success)

    # ── Test 18: Empty module ────────────────────────────────────
    print("\n§18 Empty module")
    empty = SidecarModule("empty")
    empty_report = empty.verify_all()
    check("empty report", empty_report.total_specs == 0)
    check("empty no failures", empty_report.failed == 0)

    # ── Test 19: Multiple guarantees ─────────────────────────────
    print("\n§19 Multiple guarantees per spec")
    sm_multi = SidecarModule("multi")
    sm_multi.spec("multi.fn",
        guarantee=["property A", "property B", "property C"],
        pure=True,
    )
    multi_report = sm_multi.verify_all()
    multi_specs = [r for r in multi_report.results if r.kind == "spec"]
    check("3 spec results", len(multi_specs) == 3)
    check("all pass", all(r.success for r in multi_specs))

    # ── Test 20: Module repr ─────────────────────────────────────
    print("\n§20 Module repr")
    r_str = repr(sm)
    check("repr has name", "testlib" in r_str)
    check("repr has counts", "specs=" in r_str)

    # ── Summary ──────────────────────────────────────────────────
    print(f"\n{'═' * 40}")
    print(f"  {_counters['passed']} passed, {_counters['failed']} failed")
    if _errors:
        print("  FAILURES:")
        for e in _errors:
            print(f"    - {e}")
    print(f"{'═' * 40}")

    sys.exit(0 if _counters["failed"] == 0 else 1)
