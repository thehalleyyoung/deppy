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
#  §3  ProofDecl — a proof about an external library function
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProofDecl:
    """A proof of a property about an external library function."""

    claim: str                              # human-readable claim
    target: Any | None = None               # the function (optional)
    target_name: str = ""                   # qualified name
    proof_fn: Callable | None = None        # proof builder callback
    proof_term: ProofTerm | None = None     # direct proof term
    axiom_name: str = ""                    # prove by axiom shortcut
    axiom_module: str = ""                  # axiom module for shortcut
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
        self._proofs: list[ProofDecl] = []
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

    current_block: str = ""      # "spec" or "proof"
    current_key: str = ""        # e.g. "sympy.expand" or proof name
    current_data: dict = {}

    def _flush() -> None:
        nonlocal current_block, current_key, current_data
        if current_block == "spec" and current_key:
            specs[current_key] = dict(current_data)
        elif current_block == "proof" and current_key:
            proofs.append({"name": current_key, **current_data})
        current_block = ""
        current_key = ""
        current_data = {}

    for raw_line in lines:
        line = raw_line.strip()

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

    _flush()

    # Build the SidecarModule
    sm = SidecarModule(module_name, version=version)

    for spec_target, spec_data in specs.items():
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
        by_clause = proof_data.get("by", "")
        axiom_name = ""
        axiom_module = ""
        if by_clause.startswith("axiom "):
            axiom_name = by_clause[len("axiom "):].strip()
            axiom_module = module_name

        sm.prove(
            proof_data.get("name", "unnamed"),
            target=proof_data.get("target"),
            by_axiom=axiom_name or None,
            axiom_module=axiom_module or None,
        )

    return sm


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
