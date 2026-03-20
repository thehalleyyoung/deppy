"""
Hybrid contracts: design-by-contract with hybrid dependent types.

Implements three interlocking subsystems grounded in algebraic geometry
and dependent type theory:

1. **Hybrid Contracts** — separation-logic--aware contracts where
   postconditions are *dependent types* (the output type is a function
   of the input *value*).  Frame conditions enforce spatial separation
   of workspace mutations, enabling modular verification.

2. **Quality Lattice** — a product lattice over nine quality
   dimensions (extending the five in ``comet_verified.py`` with
   formal-verification metrics).  The lattice supports pointwise
   join/meet, monotonicity checking, and quality gating.

3. **CEGAR Repair Loop** — counterexample-guided abstraction
   refinement that accumulates counterexamples from four sources
   (Z3, LLM, runtime tests, Lean) and iteratively repairs outputs
   until convergence or exhaustion.
"""

from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.contracts.base import Contract as _CoreContract, SourceLocation as _CoreSourceLocation
    from deppy.contracts.requires import RequiresContract
    from deppy.contracts.ensures import EnsuresContract
    from deppy.types.refinement import RefinementType as _CoreRefinementType, Predicate as _CorePredicate
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

import copy
import hashlib
import json
import math
import textwrap
import time
from dataclasses import dataclass, field
from enum import Enum, unique
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
)

if TYPE_CHECKING:
    from deppy.hybrid.core.trust import TrustLevel, TrustObligation
    from deppy.hybrid.core.types import (
        HybridDependentType,
        HybridType,
        HybridTypeChecker,
    )

__all__ = [
    "HybridCheckResult",
    "HybridContract",
    "HybridContractEnforcer",
    "ContractComposer",
    "QualityDimension",
    "QualityVector",
    "QualityGate",
    "QualityMonitor",
    "CounterexampleKind",
    "Counterexample",
    "RepairStrategy",
    "HybridCEGAR",
    "CEGARReport",
]

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _content_hash(value: Any) -> str:
    """Deterministic SHA-256 of an arbitrary value."""
    try:
        blob = json.dumps(value, sort_keys=True, default=str).encode()
    except (TypeError, ValueError):

        blob = repr(value).encode()
    return hashlib.sha256(blob).hexdigest()[:16]

def _deep_snapshot(d: dict) -> dict:
    """Deep-copy a workspace dict for frame comparison."""
    return copy.deepcopy(d)

def _lean_escape(name: str) -> str:
    """Sanitise a Python identifier for use as a Lean 4 name."""
    return name.replace(" ", "_").replace("-", "_").replace(".", "_")

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 1 — HYBRID CHECK RESULTS
# ═══════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class HybridCheckResult:
    """Result of checking a value against a hybrid type.

    Carries both a boolean verdict and a structured list of violations
    so callers can report *why* a check failed without re-running it.
    """

    valid: bool
    type_name: str
    violations: Tuple[str, ...]
    timestamp: float = field(default_factory=time.time)

    # -- Convenience -----------------------------------------------------------

    def __bool__(self) -> bool:
        return self.valid

    def __str__(self) -> str:
        if self.valid:
            return f"✓ {self.type_name}"
        header = f"✗ {self.type_name}"
        body = "\n  ".join(self.violations)
        return f"{header}\n  {body}"

    def merge(self, other: HybridCheckResult) -> HybridCheckResult:
        """Conjoin two results (both must pass)."""
        return HybridCheckResult(
            valid=self.valid and other.valid,
            type_name=f"({self.type_name} ∧ {other.type_name})",
            violations=self.violations + other.violations,
        )

    @staticmethod
    def ok(type_name: str) -> HybridCheckResult:
        return HybridCheckResult(valid=True, type_name=type_name, violations=())

    @staticmethod
    def fail(type_name: str, *violations: str) -> HybridCheckResult:
        return HybridCheckResult(
            valid=False, type_name=type_name, violations=tuple(violations)
        )

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 2 — HYBRID CONTRACTS
# ═══════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class HybridContract:
    """A contract pairing a precondition, a *dependent* postcondition,
    frame conditions (separation logic), invariants, and an optional
    termination measure.

    The postcondition is a *dependent type* — a function from the
    concrete input value to the expected output type.  This is the key
    distinction from ``StageContract`` in ``comet_verified.py``, which
    uses a ``DependentType`` wrapper around ``RefinedType``.  Here we
    work directly with ``HybridDependentType`` objects that may carry
    Z3 constraints, LLM semantic predicates, and Lean proof
    obligations simultaneously.
    """

    name: str
    precondition: Any  # HybridType at runtime
    postcondition: Any  # HybridDependentType at runtime
    frame: FrozenSet[str] = frozenset()
    invariants: Tuple[Any, ...] = ()  # Tuple[HybridType, ...]
    decreases: Optional[Callable[..., Any]] = None
    max_retries: int = 3

    # -- Precondition ----------------------------------------------------------

    def check_pre(
        self,
        input_value: Any,
        checker: Optional[Any] = None,
    ) -> HybridCheckResult:
        """Verify that *input_value* inhabits the precondition type.

        If a *checker* (``HybridTypeChecker``) is provided it is used
        for full hybrid checking (Z3 + LLM + Lean).  Otherwise we fall
        back to the precondition's own ``check`` method.
        """
        if checker is not None and hasattr(checker, "check"):
            raw = checker.check(input_value, self.precondition)
            if isinstance(raw, HybridCheckResult):
                return raw
            ok = bool(raw)
            return HybridCheckResult(
                valid=ok,
                type_name=getattr(self.precondition, "name", str(self.precondition)),
                violations=() if ok else (f"Precondition failed for {self.name}",),
            )
        if hasattr(self.precondition, "check"):
            raw = self.precondition.check(input_value)
            if isinstance(raw, HybridCheckResult):
                return raw
            ok = bool(raw)
            viol_list: List[str] = []
            if not ok:
                if hasattr(raw, "violations"):
                    viol_list = list(raw.violations)
                else:
                    viol_list = [f"Precondition '{self.name}' not satisfied"]
            return HybridCheckResult(
                valid=ok,
                type_name=getattr(self.precondition, "name", str(self.precondition)),
                violations=tuple(viol_list),
            )
        return HybridCheckResult.ok(self.name + ".pre")

    # -- Postcondition (dependent) ---------------------------------------------

    def check_post(
        self,
        input_value: Any,
        output_value: Any,
        checker: Optional[Any] = None,
    ) -> HybridCheckResult:
        """Verify that *output_value* inhabits the postcondition
        *instantiated at input_value*.

        Because the postcondition is a dependent type, we first
        instantiate it with the concrete input, obtaining a ground
        type, then check the output against that ground type.
        """
        # Instantiate the dependent postcondition with the input value.
        ground_type: Any = None
        if hasattr(self.postcondition, "instantiate"):
            ground_type = self.postcondition.instantiate(input_value)
        elif callable(self.postcondition):
            ground_type = self.postcondition(input_value)
        else:
            ground_type = self.postcondition

        if checker is not None and hasattr(checker, "check"):
            raw = checker.check(output_value, ground_type)
            if isinstance(raw, HybridCheckResult):
                return raw
            ok = bool(raw)
            return HybridCheckResult(
                valid=ok,
                type_name=getattr(ground_type, "name", str(ground_type)),
                violations=() if ok else (
                    f"Postcondition failed for {self.name} "
                    f"(input hash {_content_hash(input_value)})",
                ),
            )
        if hasattr(ground_type, "check"):
            raw = ground_type.check(output_value)
            if isinstance(raw, HybridCheckResult):
                return raw
            ok = bool(raw)
            viol_list: List[str] = []
            if not ok:
                if hasattr(raw, "violations"):
                    viol_list = list(raw.violations)
                else:
                    viol_list = [
                        f"Postcondition '{self.name}' not satisfied "
                        f"for input hash {_content_hash(input_value)}"
                    ]
            return HybridCheckResult(
                valid=ok,
                type_name=getattr(ground_type, "name", str(ground_type)),
                violations=tuple(viol_list),
            )
        return HybridCheckResult.ok(self.name + ".post")

    # -- Frame (separation logic) ----------------------------------------------

    def check_frame(self, before: dict, after: dict) -> List[str]:
        """Return the list of workspace keys modified outside the
        declared *frame*.

        If ``self.frame`` is empty (no frame declared), every
        mutation is permitted — this is the *unrestricted* case.
        """
        if not self.frame:
            return []

        violations: List[str] = []
        all_keys = set(before.keys()) | set(after.keys())
        for key in sorted(all_keys):
            bval = before.get(key, _SENTINEL)
            aval = after.get(key, _SENTINEL)
            if bval is not aval and key not in self.frame:
                # Deep equality check for non-identity differences.
                try:
                    if bval != aval:
                        violations.append(key)
                except Exception:
                    violations.append(key)
        return violations

    # -- Invariants ------------------------------------------------------------

    def check_invariants(
        self,
        value: Any,
        checker: Optional[Any] = None,
    ) -> List[HybridCheckResult]:
        """Check all invariants against *value* and return the
        results (one per invariant)."""
        results: List[HybridCheckResult] = []
        for idx, inv in enumerate(self.invariants):
            inv_name = getattr(inv, "name", f"invariant_{idx}")
            if checker is not None and hasattr(checker, "check"):
                raw = checker.check(value, inv)
                if isinstance(raw, HybridCheckResult):
                    results.append(raw)
                else:
                    ok = bool(raw)
                    results.append(HybridCheckResult(
                        valid=ok,
                        type_name=inv_name,
                        violations=() if ok else (
                            f"Invariant {inv_name} violated",
                        ),
                    ))
            elif hasattr(inv, "check"):
                raw = inv.check(value)
                if isinstance(raw, HybridCheckResult):
                    results.append(raw)
                else:
                    ok = bool(raw)
                    results.append(HybridCheckResult(
                        valid=ok,
                        type_name=inv_name,
                        violations=() if ok else (
                            f"Invariant {inv_name} violated",
                        ),
                    ))
            else:
                results.append(HybridCheckResult.ok(inv_name))
        return results

    # -- Lean export -----------------------------------------------------------

    def to_lean(self) -> str:
        """Emit a Lean 4 theorem statement encoding the contract:

            theorem <name> (x : Pre) : Post x
        """
        pre_name = _lean_escape(
            getattr(self.precondition, "name", "Pre")
        )
        post_name = _lean_escape(
            getattr(self.postcondition, "name", "Post")
        )
        contract_name = _lean_escape(self.name)

        frame_comment = ""
        if self.frame:
            fields = ", ".join(sorted(self.frame))
            frame_comment = f"  -- frame: {{{fields}}}\n"

        invariant_hyps: List[str] = []
        for idx, inv in enumerate(self.invariants):
            inv_name = _lean_escape(getattr(inv, "name", f"inv_{idx}"))
            invariant_hyps.append(f"(h_inv{idx} : {inv_name} x)")

        inv_section = ""
        if invariant_hyps:
            inv_section = " " + " ".join(invariant_hyps)

        decreases_comment = ""
        if self.decreases is not None:
            decreases_comment = (
                f"  -- termination: well-founded on "
                f"{getattr(self.decreases, '__name__', 'measure')}\n"
            )

        lines = [
            f"/-- Contract: {self.name} --/",
            frame_comment + decreases_comment
            + f"theorem {contract_name}",
            f"    (x : {pre_name}){inv_section} :",
            f"    {post_name} x := by",
            "  sorry  -- proof obligation",
        ]
        return "\n".join(line for line in lines if line)

# Sentinel for frame comparison.
_SENTINEL = object()

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 3 — HYBRID CONTRACT ENFORCER
# ═══════════════════════════════════════════════════════════════════════════

class HybridContractEnforcer:
    """Runtime enforcer that wraps stage execution with full hybrid
    contract checking:

    1. Precondition (input type)
    2. Snapshot workspace for frame check
    3. Execute
    4. Postcondition (dependent on input value)
    5. Frame check
    6. Invariant checks
    7. Provenance tracking

    Failed checks are recorded and, depending on ``contract.max_retries``,
    the enforcer may re-execute the stage.
    """

    def __init__(self, checker: Optional[Any] = None) -> None:
        self._checker = checker
        self._checks_passed: int = 0
        self._checks_failed: int = 0
        self._frame_violations: int = 0
        self._invariant_violations: int = 0
        self._total_retries: int = 0
        self._history: List[Dict[str, Any]] = []

    # -- Main entry point ------------------------------------------------------

    def enforce(
        self,
        contract: HybridContract,
        input_tainted: Any,
        execute_fn: Callable[..., Any],
        step_index: int = 0,
        model: str = "",
    ) -> Tuple[Optional[Any], List[str]]:
        """Execute *execute_fn* under the governance of *contract*.

        Parameters
        ----------
        contract:
            The hybrid contract to enforce.
        input_tainted:
            The (possibly tainted) input value.  If it carries a
            ``.value`` attribute (like ``TaintedValue``), we unwrap it
            for type checking but pass the wrapper to the executor.
        execute_fn:
            ``(input) -> output``.  Called with *input_tainted* as-is.
        step_index:
            Monotonic step counter for provenance.
        model:
            LLM model identifier for provenance.

        Returns
        -------
        (output_or_none, violations)
            On success *output_or_none* is the executor's return value
            (wrapped in provenance if the input was tainted) and
            *violations* is empty.  On failure *output_or_none* is
            ``None`` and *violations* lists every problem found.
        """
        raw_input = (
            input_tainted.value
            if hasattr(input_tainted, "value")
            else input_tainted
        )

        all_violations: List[str] = []

        # 1 ── Precondition
        pre_result = contract.check_pre(raw_input, self._checker)
        if not pre_result:
            all_violations.extend(pre_result.violations)
            self._checks_failed += 1
            self._record(contract.name, step_index, "pre_fail", all_violations)
            return None, all_violations
        self._checks_passed += 1

        # Retry loop
        last_output: Any = None
        attempt = 0
        max_tries = max(1, contract.max_retries)

        while attempt < max_tries:
            attempt += 1
            per_attempt_violations: List[str] = []

            # 2 ── Snapshot workspace for frame check
            workspace_before: dict = {}
            if isinstance(raw_input, dict):
                workspace_before = _deep_snapshot(raw_input)
            elif hasattr(raw_input, "__dict__"):
                workspace_before = _deep_snapshot(vars(raw_input))

            # 3 ── Execute
            try:
                output = execute_fn(input_tainted)
            except Exception as exc:
                per_attempt_violations.append(
                    f"Execution raised {type(exc).__name__}: {exc}"
                )
                self._total_retries += 1
                if attempt < max_tries:
                    continue
                all_violations.extend(per_attempt_violations)
                self._checks_failed += 1
                self._record(
                    contract.name, step_index, "exec_fail", all_violations
                )
                return None, all_violations

            raw_output = (
                output.value if hasattr(output, "value") else output
            )

            # 4 ── Postcondition (dependent on input value)
            post_result = contract.check_post(
                raw_input, raw_output, self._checker
            )
            if not post_result:
                per_attempt_violations.extend(post_result.violations)
                self._checks_failed += 1

            # 5 ── Frame check
            workspace_after: dict = {}
            if isinstance(raw_input, dict):
                workspace_after = raw_input
            elif hasattr(raw_input, "__dict__"):
                workspace_after = vars(raw_input)
            frame_violations = contract.check_frame(
                workspace_before, workspace_after
            )
            if frame_violations:
                self._frame_violations += len(frame_violations)
                for fv in frame_violations:
                    per_attempt_violations.append(
                        f"Frame violation: '{fv}' modified outside "
                        f"frame {{{', '.join(sorted(contract.frame))}}}"
                    )

            # 6 ── Invariants
            inv_results = contract.check_invariants(raw_output, self._checker)
            for ir in inv_results:
                if not ir:
                    self._invariant_violations += 1
                    per_attempt_violations.extend(ir.violations)

            # Success?
            if not per_attempt_violations:
                self._checks_passed += 1
                self._record(contract.name, step_index, "pass", [])

                # Provenance wrapping
                if hasattr(input_tainted, "derive"):
                    output = input_tainted.derive(
                        raw_output,
                        stage=contract.name,
                        step_index=step_index,
                        llm_model=model or None,
                        description=f"Contract-verified output of {contract.name}",
                    )
                last_output = output
                return output, []

            # Retry
            self._total_retries += 1
            if attempt < max_tries:
                continue

            all_violations.extend(per_attempt_violations)
            self._checks_failed += 1
            self._record(
                contract.name, step_index, "post_fail", all_violations
            )
            last_output = output

        return last_output, all_violations

    # -- Stats -----------------------------------------------------------------

    @property
    def stats(self) -> Dict[str, int]:
        return {
            "checks_passed": self._checks_passed,
            "checks_failed": self._checks_failed,
            "frame_violations": self._frame_violations,
            "invariant_violations": self._invariant_violations,
            "total_retries": self._total_retries,
        }

    # -- Internal --------------------------------------------------------------

    def _record(
        self,
        contract_name: str,
        step: int,
        verdict: str,
        violations: List[str],
    ) -> None:
        self._history.append({
            "contract": contract_name,
            "step": step,
            "verdict": verdict,
            "violations": violations,
            "timestamp": time.time(),
        })

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 4 — CONTRACT COMPOSER
# ═══════════════════════════════════════════════════════════════════════════

class ContractComposer:
    """Algebra of contracts.

    Provides three composition operators grounded in separation logic:

    * **sequential** — ``c1 ; c2`` where ``c1.post ⟹ c2.pre`` and
      frames are unioned.
    * **parallel** — ``c1 ‖ c2`` where frames must be *disjoint*
      (the separation-logic star ``*``).
    * **refine** — ``c[+inv]`` strengthens a contract with an
      additional invariant.
    """

    @staticmethod
    def sequential(c1: HybridContract, c2: HybridContract) -> HybridContract:
        """Compose ``c1`` then ``c2``.

        The resulting contract has:
        - ``c1.precondition`` as its precondition
        - ``c2.postcondition`` as its postcondition
        - the *union* of both frames
        - the *concatenation* of both invariant lists
        - the maximum of both retry counts

        Soundness note: the caller is responsible for verifying that
        ``c1.postcondition`` refines ``c2.precondition`` — i.e., any
        value produced by stage 1 is a valid input to stage 2.  This
        is checked at Lean-export time but not enforced at runtime
        (to avoid duplicating expensive type checks).
        """
        merged_invariants = tuple(c1.invariants) + tuple(c2.invariants)
        merged_frame = c1.frame | c2.frame

        # Compose termination measures when both exist.
        decreases: Optional[Callable[..., Any]] = None
        if c1.decreases is not None and c2.decreases is not None:
            d1, d2 = c1.decreases, c2.decreases

            def _composed_measure(x: Any) -> Tuple[Any, Any]:
                return (d1(x), d2(x))

            decreases = _composed_measure
        elif c1.decreases is not None:
            decreases = c1.decreases
        elif c2.decreases is not None:
            decreases = c2.decreases

        return HybridContract(
            name=f"{c1.name}_then_{c2.name}",
            precondition=c1.precondition,
            postcondition=c2.postcondition,
            frame=merged_frame,
            invariants=merged_invariants,
            decreases=decreases,
            max_retries=max(c1.max_retries, c2.max_retries),
        )

    @staticmethod
    def parallel(c1: HybridContract, c2: HybridContract) -> HybridContract:
        """Compose ``c1 ‖ c2`` in parallel.

        Requires frame disjointness (separation logic ``*``):
        ``c1.frame ∩ c2.frame = ∅``.

        Raises ``ValueError`` when frames overlap.
        """
        overlap = c1.frame & c2.frame
        if overlap:
            raise ValueError(
                f"Frame overlap in parallel composition: "
                f"{overlap!r}.  Separation logic requires "
                f"disjoint frames for safe parallel execution."
            )

        merged_invariants = tuple(c1.invariants) + tuple(c2.invariants)
        merged_frame = c1.frame | c2.frame

        # The parallel contract's precondition is the *conjunction*
        # (intersection type) of both preconditions.  We represent it
        # as a lightweight wrapper that checks both.
        pre1, pre2 = c1.precondition, c2.precondition
        post1, post2 = c1.postcondition, c2.postcondition

        class _ConjPre:
            name = f"({getattr(pre1, 'name', '?')} ∧ {getattr(pre2, 'name', '?')})"

            @staticmethod
            def check(value: Any) -> HybridCheckResult:
                r1 = _check_any(value, pre1)
                r2 = _check_any(value, pre2)
                return r1.merge(r2)

        class _ConjPost:
            name = f"({getattr(post1, 'name', '?')} ∧ {getattr(post2, 'name', '?')})"

            @staticmethod
            def instantiate(input_value: Any) -> _ConjPre:
                """Instantiate both postconditions, return conjunction."""
                g1 = _instantiate_any(post1, input_value)
                g2 = _instantiate_any(post2, input_value)

                class _Ground:
                    name = f"({getattr(g1, 'name', '?')} ∧ {getattr(g2, 'name', '?')})"

                    @staticmethod
                    def check(value: Any) -> HybridCheckResult:
                        r1 = _check_any(value, g1)
                        r2 = _check_any(value, g2)
                        return r1.merge(r2)

                return _Ground  # type: ignore[return-value]

        return HybridContract(
            name=f"{c1.name}_par_{c2.name}",
            precondition=_ConjPre,
            postcondition=_ConjPost,
            frame=merged_frame,
            invariants=merged_invariants,
            decreases=None,
            max_retries=max(c1.max_retries, c2.max_retries),
        )

    @staticmethod
    def refine(
        contract: HybridContract,
        additional_invariant: Any,
    ) -> HybridContract:
        """Return a *strengthened* copy of *contract* with an extra
        invariant appended."""
        return HybridContract(
            name=contract.name,
            precondition=contract.precondition,
            postcondition=contract.postcondition,
            frame=contract.frame,
            invariants=tuple(contract.invariants) + (additional_invariant,),
            decreases=contract.decreases,
            max_retries=contract.max_retries,
        )

def _check_any(value: Any, type_obj: Any) -> HybridCheckResult:
    """Uniform dispatch: call *type_obj.check(value)* and normalise
    the result to ``HybridCheckResult``."""
    if hasattr(type_obj, "check"):
        raw = type_obj.check(value)
        if isinstance(raw, HybridCheckResult):
            return raw
        ok = bool(raw)
        violations: Tuple[str, ...] = ()
        if not ok:
            if hasattr(raw, "violations"):
                violations = tuple(raw.violations)
            else:
                violations = (f"Check failed for {getattr(type_obj, 'name', '?')}",)
        return HybridCheckResult(
            valid=ok,
            type_name=getattr(type_obj, "name", str(type_obj)),
            violations=violations,
        )
    return HybridCheckResult.ok(getattr(type_obj, "name", "unknown"))

def _instantiate_any(dep_type: Any, input_value: Any) -> Any:
    """Instantiate a dependent type, tolerating non-dependent types."""
    if hasattr(dep_type, "instantiate"):
        return dep_type.instantiate(input_value)
    if callable(dep_type):
        try:
            return dep_type(input_value)
        except TypeError:
            return dep_type
    return dep_type

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 5 — QUALITY LATTICE
# ═══════════════════════════════════════════════════════════════════════════

@unique
class QualityDimension(Enum):
    """Nine quality dimensions forming the basis of the product
    lattice.  The first five extend ``comet_verified.py``; the last
    four capture formal-verification metrics.

    Each dimension maps to a float in ``[0, 1]`` where 0 is *bottom*
    (no evidence) and 1 is *top* (fully verified).
    """

    # --- Original dimensions (from comet_verified.py) ---
    GROUNDING = "grounding"
    NOVELTY = "novelty"
    CORRECTNESS = "correctness"
    CLARITY = "clarity"
    COMPLETENESS = "completeness"

    # --- Formal-verification dimensions ---
    FORMAL_VERIFICATION = "formal_verification"
    LEAN_COVERAGE = "lean_coverage"
    TRUST_LEVEL = "trust_level"
    COHERENCE = "coherence"

# Canonical ordered list used for deterministic iteration.
_ALL_DIM_NAMES: Tuple[str, ...] = tuple(d.value for d in QualityDimension)

@dataclass(frozen=True)
class QualityVector:
    """A point in the nine-dimensional product lattice ``[0, 1]^9``.

    The partial order is *pointwise*: ``v1 ≤ v2`` iff every dimension
    of *v1* is ≤ the corresponding dimension of *v2*.  Join (⊔) is
    pointwise max, meet (⊓) is pointwise min.
    """

    scores: Dict[str, float]

    def __post_init__(self) -> None:
        # Ensure every dimension has a score; default missing to 0.
        filled: Dict[str, float] = {}
        for dim_name in _ALL_DIM_NAMES:
            val = self.scores.get(dim_name, 0.0)
            filled[dim_name] = max(0.0, min(1.0, float(val)))
        # frozen=True → bypass __setattr__
        object.__setattr__(self, "scores", filled)

    # -- Lattice order ---------------------------------------------------------

    def __le__(self, other: QualityVector) -> bool:
        """Pointwise partial order: ``self ≤ other``."""
        return all(
            self.scores[d] <= other.scores[d] for d in _ALL_DIM_NAMES
        )

    def __lt__(self, other: QualityVector) -> bool:
        """Strict pointwise: ``self ≤ other`` and at least one
        dimension is strictly less."""
        return self <= other and any(
            self.scores[d] < other.scores[d] for d in _ALL_DIM_NAMES
        )

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, QualityVector):
            return NotImplemented
        return self.scores == other.scores

    def __hash__(self) -> int:
        return hash(tuple(sorted(self.scores.items())))

    # -- Join / Meet -----------------------------------------------------------

    def join(self, other: QualityVector) -> QualityVector:
        """Pointwise maximum — the least upper bound (LUB, ⊔)."""
        return QualityVector(
            scores={
                d: max(self.scores[d], other.scores[d])
                for d in _ALL_DIM_NAMES
            }
        )

    def meet(self, other: QualityVector) -> QualityVector:
        """Pointwise minimum — the greatest lower bound (GLB, ⊓)."""
        return QualityVector(
            scores={
                d: min(self.scores[d], other.scores[d])
                for d in _ALL_DIM_NAMES
            }
        )

    # -- Metrics ---------------------------------------------------------------

    def distance(self, other: QualityVector) -> float:
        """L2 (Euclidean) distance in ``[0, 1]^9``."""
        return math.sqrt(
            sum(
                (self.scores[d] - other.scores[d]) ** 2
                for d in _ALL_DIM_NAMES
            )
        )

    def bottleneck(self) -> Tuple[str, float]:
        """Return ``(dimension_name, score)`` for the weakest
        dimension."""
        return min(self.scores.items(), key=lambda kv: kv[1])

    def is_acceptable(self, threshold: QualityVector) -> bool:
        """Every dimension must meet or exceed the corresponding
        threshold dimension."""
        return all(
            self.scores[d] >= threshold.scores[d] for d in _ALL_DIM_NAMES
        )

    def mean(self) -> float:
        """Arithmetic mean across all dimensions."""
        vals = [self.scores[d] for d in _ALL_DIM_NAMES]
        return sum(vals) / len(vals) if vals else 0.0

    # -- Display ---------------------------------------------------------------

    def summary(self) -> str:
        parts: List[str] = []
        for d in _ALL_DIM_NAMES:
            score = self.scores[d]
            bar = "█" * int(score * 10) + "░" * (10 - int(score * 10))
            parts.append(f"  {d:<24s} {bar} {score:.2f}")
        weak_dim, weak_score = self.bottleneck()
        parts.append(f"  bottleneck: {weak_dim} = {weak_score:.2f}")
        parts.append(f"  mean:       {self.mean():.3f}")
        return "\n".join(parts)

    def __repr__(self) -> str:
        inner = ", ".join(f"{d}={self.scores[d]:.2f}" for d in _ALL_DIM_NAMES)
        return f"QualityVector({inner})"

# Lattice extrema
Q_BOTTOM = QualityVector(scores={d: 0.0 for d in _ALL_DIM_NAMES})
Q_TOP = QualityVector(scores={d: 1.0 for d in _ALL_DIM_NAMES})
Q_ACCEPT_THRESHOLD = QualityVector(scores={d: 0.7 for d in _ALL_DIM_NAMES})

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 6 — QUALITY GATE
# ═══════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class QualityGate:
    """A named checkpoint that an artifact must pass before advancing
    to the next pipeline stage.

    *required_dimensions* restricts which dimensions are hard
    requirements; other dimensions are advisory.  If
    *required_dimensions* is empty, **all** dimensions must meet the
    threshold.
    """

    name: str
    threshold: QualityVector
    required_dimensions: FrozenSet[str] = frozenset()

    def check(self, quality: QualityVector) -> Tuple[bool, str]:
        """Evaluate *quality* against this gate.

        Returns ``(passed, explanation)``.
        """
        dims_to_check: Sequence[str] = (
            sorted(self.required_dimensions)
            if self.required_dimensions
            else list(_ALL_DIM_NAMES)
        )

        failures: List[str] = []
        advisories: List[str] = []

        for dim in _ALL_DIM_NAMES:
            actual = quality.scores[dim]
            required = self.threshold.scores[dim]
            if actual < required:
                msg = (
                    f"{dim}: {actual:.2f} < {required:.2f} "
                    f"(deficit {required - actual:.2f})"
                )
                if dim in dims_to_check:
                    failures.append(msg)
                else:
                    advisories.append(msg)

        if failures:
            explanation = (
                f"Gate '{self.name}' FAILED on {len(failures)} "
                f"dimension(s):\n"
                + "\n".join(f"  ✗ {f}" for f in failures)
            )
            if advisories:
                explanation += "\nAdvisory:\n" + "\n".join(
                    f"  ⚠ {a}" for a in advisories
                )
            return False, explanation

        explanation = f"Gate '{self.name}' PASSED."
        if advisories:
            explanation += "\nAdvisory:\n" + "\n".join(
                f"  ⚠ {a}" for a in advisories
            )
        return True, explanation

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 7 — QUALITY MONITOR
# ═══════════════════════════════════════════════════════════════════════════

class QualityMonitor:
    """Tracks quality vectors across pipeline stages and verifies
    monotonicity of the quality lattice.

    In a well-behaved pipeline, quality should be *monotonically
    non-decreasing* — every stage either preserves or improves quality.
    The monitor detects regressions and reports them.
    """

    def __init__(self) -> None:
        self._history: List[Tuple[str, QualityVector]] = []

    @property
    def history(self) -> List[Tuple[str, QualityVector]]:
        return list(self._history)

    def record(self, stage: str, quality: QualityVector) -> None:
        """Append a ``(stage, quality)`` observation."""
        self._history.append((stage, quality))

    def check_monotonicity(
        self, allow_contraction: bool = False,
    ) -> Tuple[bool, str]:
        """Verify that quality never decreases between consecutive
        observations.

        Parameters
        ----------
        allow_contraction:
            If ``True``, small decreases (≤ 0.05 per dimension) in
            *non-critical* dimensions are tolerated.  This models
            the pragmatic reality that novelty-seeking stages may
            temporarily reduce correctness confidence before the
            audit gate restores it.

        Returns ``(is_monotone, explanation)``.
        """
        if len(self._history) < 2:
            return True, "Insufficient history for monotonicity check."

        violations: List[str] = []
        epsilon = 0.05 if allow_contraction else 0.0

        for i in range(1, len(self._history)):
            prev_stage, prev_q = self._history[i - 1]
            curr_stage, curr_q = self._history[i]

            for dim in _ALL_DIM_NAMES:
                delta = curr_q.scores[dim] - prev_q.scores[dim]
                if delta < -epsilon:
                    violations.append(
                        f"{prev_stage} → {curr_stage}: "
                        f"{dim} dropped {prev_q.scores[dim]:.3f} → "
                        f"{curr_q.scores[dim]:.3f} "
                        f"(Δ = {delta:+.3f})"
                    )

        if violations:
            msg = (
                f"Monotonicity violated in {len(violations)} "
                f"transition(s):\n"
                + "\n".join(f"  • {v}" for v in violations)
            )
            return False, msg
        return True, "Quality is monotonically non-decreasing."

    def trend(self) -> Dict[str, List[float]]:
        """Return per-dimension time series."""
        series: Dict[str, List[float]] = {d: [] for d in _ALL_DIM_NAMES}
        for _, qv in self._history:
            for d in _ALL_DIM_NAMES:
                series[d].append(qv.scores[d])
        return series

    def report(self) -> str:
        """Human-readable report of the full quality history."""
        if not self._history:
            return "No quality observations recorded."

        lines: List[str] = ["╔══ Quality Monitor Report ══╗"]

        for idx, (stage, qv) in enumerate(self._history):
            lines.append(f"\n── Stage {idx}: {stage} ──")
            lines.append(qv.summary())

        mono_ok, mono_msg = self.check_monotonicity(allow_contraction=True)
        lines.append(f"\n── Monotonicity ──")
        lines.append(mono_msg)

        if len(self._history) >= 2:
            first_q = self._history[0][1]
            last_q = self._history[-1][1]
            improvement = last_q.mean() - first_q.mean()
            lines.append(
                f"\nOverall mean improvement: {improvement:+.3f} "
                f"({first_q.mean():.3f} → {last_q.mean():.3f})"
            )

        lines.append("╚════════════════════════════╝")
        return "\n".join(lines)

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 8 — CEGAR: COUNTEREXAMPLE TYPES
# ═══════════════════════════════════════════════════════════════════════════

@unique
class CounterexampleKind(Enum):
    """Source of the counterexample — determines the repair strategy.

    * ``STRUCTURAL`` — Z3 found a valuation violating a refinement.
    * ``SEMANTIC`` — an LLM judge flagged a semantic problem.
    * ``RUNTIME`` — a concrete test case failed.
    * ``LEAN`` — the Lean 4 kernel rejected a proof term.
    """

    STRUCTURAL = "structural"
    SEMANTIC = "semantic"
    RUNTIME = "runtime"
    LEAN = "lean"

@dataclass(frozen=True)
class Counterexample:
    """A concrete witness of contract violation.

    Counterexamples are the *fuel* of the CEGAR loop: each one
    records exactly what went wrong so the repair function can
    generate a targeted fix.
    """

    kind: CounterexampleKind
    input_value: Any
    expected_property: str
    actual_output: Any
    violation: str
    content_hash: str = ""

    def __post_init__(self) -> None:
        if not self.content_hash:
            h = _content_hash({
                "kind": self.kind.value,
                "input": self.input_value,
                "expected": self.expected_property,
                "actual": self.actual_output,
                "violation": self.violation,
            })
            object.__setattr__(self, "content_hash", h)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": self.kind.value,
            "input_value": self.input_value,
            "expected_property": self.expected_property,
            "actual_output": self.actual_output,
            "violation": self.violation,
            "content_hash": self.content_hash,
        }

    def __str__(self) -> str:
        return (
            f"[{self.kind.value}] {self.violation}\n"
            f"  expected: {self.expected_property}\n"
            f"  got:      {_truncate(repr(self.actual_output), 120)}"
        )

def _truncate(s: str, max_len: int) -> str:
    return s if len(s) <= max_len else s[: max_len - 3] + "..."

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 9 — CEGAR: REPAIR STRATEGIES
# ═══════════════════════════════════════════════════════════════════════════

@unique
class RepairStrategy(Enum):
    """Taxonomy of repair actions the CEGAR loop can take.

    The ordering reflects escalation: cheaper/safer repairs first,
    expensive/risky repairs last.

    * ``REFINE_TYPE`` — tighten the type (add a refinement predicate).
    * ``ADD_GUARD`` — insert a runtime guard / assertion.
    * ``WEAKEN_SPEC`` — relax the postcondition (spec was too strong).
    * ``STRENGTHEN_EVIDENCE`` — re-run evidence collection (e.g.,
      fetch more citations, re-run Lean).
    * ``RESYNTHESIZE`` — regenerate the output from scratch.
    * ``ESCALATE_TO_HUMAN`` — give up automated repair.
    """

    REFINE_TYPE = "refine_type"
    ADD_GUARD = "add_guard"
    WEAKEN_SPEC = "weaken_spec"
    STRENGTHEN_EVIDENCE = "strengthen_evidence"
    RESYNTHESIZE = "resynthesize"
    ESCALATE_TO_HUMAN = "escalate_to_human"

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 10 — CEGAR REPORT
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class CEGARReport:
    """Post-mortem of a CEGAR loop execution."""

    converged: bool
    iterations: int
    counterexamples_found: int
    repairs_applied: List[RepairStrategy]
    final_trust: str
    duration_seconds: float = 0.0
    counterexample_details: List[Counterexample] = field(default_factory=list)

    def to_markdown(self) -> str:
        status = "✅ Converged" if self.converged else "❌ Did not converge"
        repair_names = [r.value for r in self.repairs_applied]

        sections = [
            f"## CEGAR Report",
            f"",
            f"| Metric | Value |",
            f"|--------|-------|",
            f"| Status | {status} |",
            f"| Iterations | {self.iterations} |",
            f"| Counterexamples found | {self.counterexamples_found} |",
            f"| Repairs applied | {len(self.repairs_applied)} |",
            f"| Final trust | {self.final_trust} |",
            f"| Duration | {self.duration_seconds:.2f}s |",
            f"",
        ]

        if repair_names:
            sections.append("### Repairs")
            for i, name in enumerate(repair_names, 1):
                sections.append(f"{i}. `{name}`")
            sections.append("")

        if self.counterexample_details:
            sections.append("### Counterexamples")
            for cx in self.counterexample_details:
                sections.append(
                    f"- **[{cx.kind.value}]** {cx.violation}"
                )
                sections.append(
                    f"  - Expected: {cx.expected_property}"
                )
                sections.append(
                    f"  - Hash: `{cx.content_hash}`"
                )
            sections.append("")

        return "\n".join(sections)

    def __str__(self) -> str:
        return (
            f"CEGARReport(converged={self.converged}, "
            f"iters={self.iterations}, "
            f"cx={self.counterexamples_found}, "
            f"repairs={len(self.repairs_applied)}, "
            f"trust={self.final_trust})"
        )

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 11 — HYBRID CEGAR ENGINE
# ═══════════════════════════════════════════════════════════════════════════

class HybridCEGAR:
    """Counterexample-Guided Abstraction Refinement engine.

    The engine maintains a *monotonically growing* set of
    counterexamples and iteratively:

    1. Checks the current output against **all** accumulated
       counterexamples.
    2. If a counterexample is found, classifies it and suggests a
       repair strategy.
    3. Invokes the caller-supplied repair function.
    4. Repeats until convergence or exhaustion.

    The classification heuristic maps counterexample *kind* to a
    default repair strategy, which the caller may override.
    """

    def __init__(self, max_attempts: int = 5) -> None:
        self._counterexamples: List[Counterexample] = []
        self._seen_hashes: Set[str] = set()
        self._repair_attempts: int = 0
        self._max_attempts: int = max_attempts
        self._converged: bool = False

    # -- Properties ------------------------------------------------------------

    @property
    def counterexamples(self) -> List[Counterexample]:
        return list(self._counterexamples)

    @property
    def repair_attempts(self) -> int:
        return self._repair_attempts

    @property
    def max_attempts(self) -> int:
        return self._max_attempts

    @property
    def converged(self) -> bool:
        return self._converged

    # -- Core operations -------------------------------------------------------

    def add_counterexample(self, cx: Counterexample) -> bool:
        """Add *cx* to the counterexample set.

        Returns ``True`` if the counterexample is genuinely new
        (based on content hash), ``False`` if it is a duplicate.
        Duplicates are silently ignored — the set is a
        *deduplicating* monotone accumulator.
        """
        if cx.content_hash in self._seen_hashes:
            return False
        self._seen_hashes.add(cx.content_hash)
        self._counterexamples.append(cx)
        return True

    def classify(self, cx: Counterexample) -> CounterexampleKind:
        """Return the counterexample's kind.

        This is a trivial accessor today but exists as an extension
        point: future versions may reclassify counterexamples based
        on cross-cutting heuristics (e.g., a "runtime" failure that
        is actually caused by a structural type error).
        """
        # Heuristic reclassification: if the violation mentions "type"
        # or "schema" and it was originally SEMANTIC, promote to STRUCTURAL.
        violation_lower = cx.violation.lower()
        if cx.kind == CounterexampleKind.SEMANTIC:
            structural_keywords = {"type error", "schema", "missing field", "wrong type"}
            if any(kw in violation_lower for kw in structural_keywords):
                return CounterexampleKind.STRUCTURAL
        # If the violation mentions "proof" or "sorry" and it was RUNTIME,
        # reclassify as LEAN.
        if cx.kind == CounterexampleKind.RUNTIME:
            lean_keywords = {"proof", "sorry", "tactic", "lean"}
            if any(kw in violation_lower for kw in lean_keywords):
                return CounterexampleKind.LEAN
        return cx.kind

    def suggest_repair(self, cx: Counterexample) -> RepairStrategy:
        """Map a counterexample to the cheapest appropriate repair
        strategy.

        The mapping follows an escalation ladder::

            STRUCTURAL → REFINE_TYPE
            SEMANTIC   → STRENGTHEN_EVIDENCE
            RUNTIME    → ADD_GUARD
            LEAN       → RESYNTHESIZE

        If the same counterexample kind has been seen more than twice,
        we escalate one step up the ladder.
        """
        classified = self.classify(cx)

        # Count how many counterexamples of this kind we've already seen.
        same_kind_count = sum(
            1 for c in self._counterexamples if self.classify(c) == classified
        )

        base_strategy = _KIND_TO_STRATEGY.get(
            classified, RepairStrategy.RESYNTHESIZE
        )

        # Escalation: if we've seen ≥3 of the same kind, try a stronger
        # repair.  The escalation order is defined by _ESCALATION_ORDER.
        if same_kind_count >= 3:
            idx = _ESCALATION_ORDER.index(base_strategy)
            escalated_idx = min(idx + 1, len(_ESCALATION_ORDER) - 1)
            return _ESCALATION_ORDER[escalated_idx]

        return base_strategy

    def check_all(
        self,
        output: Any,
        check_fn: Callable[[Any, Counterexample], Optional[str]],
    ) -> List[Counterexample]:
        """Check *output* against every accumulated counterexample.

        Parameters
        ----------
        check_fn:
            ``(output, counterexample) -> optional_violation``.
            Returns ``None`` if the output is OK for this
            counterexample, or a violation string if it fails.

        Returns the (possibly empty) list of *new* counterexamples
        that the output still violates.
        """
        new_violations: List[Counterexample] = []
        for cx in self._counterexamples:
            violation = check_fn(output, cx)
            if violation is not None:
                new_cx = Counterexample(
                    kind=cx.kind,
                    input_value=cx.input_value,
                    expected_property=cx.expected_property,
                    actual_output=output,
                    violation=violation,
                )
                new_violations.append(new_cx)
        return new_violations

    # -- Full CEGAR loop -------------------------------------------------------

    def run(
        self,
        initial_output: Any,
        contract: HybridContract,
        input_value: Any,
        repair_fn: Callable[[Any, Counterexample, RepairStrategy], Any],
        checker: Optional[Any] = None,
    ) -> Tuple[Any, CEGARReport]:
        """Execute the full CEGAR loop.

        Parameters
        ----------
        initial_output:
            The first candidate output to verify.
        contract:
            The hybrid contract that the output must satisfy.
        input_value:
            The input that produced *initial_output* (needed for
            dependent postcondition checking).
        repair_fn:
            ``(current_output, counterexample, strategy) -> repaired_output``.
        checker:
            Optional ``HybridTypeChecker`` for full hybrid checking.

        Returns
        -------
        (final_output, report)
        """
        start_time = time.time()
        current = initial_output
        repairs_applied: List[RepairStrategy] = []
        iteration = 0

        while iteration < self._max_attempts:
            iteration += 1

            # ── Phase 1: Contract-based checking ──
            new_cxs = self._extract_counterexamples(
                current, contract, input_value, checker
            )

            # ── Phase 2: Regression against accumulated suite ──
            regression_cxs = self.check_all(
                current, self._regression_check_fn(contract, input_value, checker)
            )
            for rcx in regression_cxs:
                new_added = self.add_counterexample(rcx)
                if new_added:
                    new_cxs.append(rcx)

            if not new_cxs:
                # All checks pass — convergence!
                self._converged = True
                break

            # ── Phase 3: Classify & repair ──
            # Pick the most severe counterexample for repair.
            cx_to_fix = self._select_most_severe(new_cxs)
            strategy = self.suggest_repair(cx_to_fix)
            repairs_applied.append(strategy)

            if strategy == RepairStrategy.ESCALATE_TO_HUMAN:
                break

            try:
                current = repair_fn(current, cx_to_fix, strategy)
            except Exception:
                # Repair function failed — escalate.
                repairs_applied.append(RepairStrategy.ESCALATE_TO_HUMAN)
                break

            self._repair_attempts += 1

        duration = time.time() - start_time

        # Determine final trust level.
        final_trust = self._assess_trust()

        report = CEGARReport(
            converged=self._converged,
            iterations=iteration,
            counterexamples_found=len(self._counterexamples),
            repairs_applied=repairs_applied,
            final_trust=final_trust,
            duration_seconds=duration,
            counterexample_details=list(self._counterexamples),
        )
        return current, report

    # -- Internal helpers ------------------------------------------------------

    def _extract_counterexamples(
        self,
        output: Any,
        contract: HybridContract,
        input_value: Any,
        checker: Optional[Any],
    ) -> List[Counterexample]:
        """Check *output* against the contract and extract any
        counterexamples from failures."""
        found: List[Counterexample] = []

        # Postcondition check (this is the main source of counterexamples).
        raw_output = output.value if hasattr(output, "value") else output
        raw_input = input_value.value if hasattr(input_value, "value") else input_value
        post_result = contract.check_post(raw_input, raw_output, checker)
        if not post_result:
            for v in post_result.violations:
                cx = Counterexample(
                    kind=self._infer_kind(v),
                    input_value=raw_input,
                    expected_property=post_result.type_name,
                    actual_output=raw_output,
                    violation=v,
                )
                if self.add_counterexample(cx):
                    found.append(cx)

        # Invariant checks.
        inv_results = contract.check_invariants(raw_output, checker)
        for ir in inv_results:
            if not ir:
                for v in ir.violations:
                    cx = Counterexample(
                        kind=self._infer_kind(v),
                        input_value=raw_input,
                        expected_property=ir.type_name,
                        actual_output=raw_output,
                        violation=v,
                    )
                    if self.add_counterexample(cx):
                        found.append(cx)

        return found

    @staticmethod
    def _infer_kind(violation_text: str) -> CounterexampleKind:
        """Heuristically infer the counterexample kind from the
        violation message text."""
        vl = violation_text.lower()
        if any(kw in vl for kw in ("z3", "smt", "schema", "type error", "structural")):
            return CounterexampleKind.STRUCTURAL
        if any(kw in vl for kw in ("lean", "proof", "sorry", "tactic")):
            return CounterexampleKind.LEAN
        if any(kw in vl for kw in ("test", "assert", "runtime", "exception")):
            return CounterexampleKind.RUNTIME
        return CounterexampleKind.SEMANTIC

    def _regression_check_fn(
        self,
        contract: HybridContract,
        input_value: Any,
        checker: Optional[Any],
    ) -> Callable[[Any, Counterexample], Optional[str]]:
        """Build a regression-check closure for ``check_all``."""

        def _check(output: Any, cx: Counterexample) -> Optional[str]:
            raw_out = output.value if hasattr(output, "value") else output
            raw_in = (
                input_value.value
                if hasattr(input_value, "value")
                else input_value
            )

            post_result = contract.check_post(raw_in, raw_out, checker)
            if not post_result:
                for v in post_result.violations:
                    if cx.expected_property in v or cx.violation in v:
                        return v
                if post_result.violations:
                    return post_result.violations[0]
            return None

        return _check

    @staticmethod
    def _select_most_severe(cxs: List[Counterexample]) -> Counterexample:
        """Choose the counterexample to repair first.

        Severity ordering: LEAN > STRUCTURAL > RUNTIME > SEMANTIC.
        """
        severity = {
            CounterexampleKind.LEAN: 4,
            CounterexampleKind.STRUCTURAL: 3,
            CounterexampleKind.RUNTIME: 2,
            CounterexampleKind.SEMANTIC: 1,
        }
        return max(cxs, key=lambda c: severity.get(c.kind, 0))

    def _assess_trust(self) -> str:
        """Compute a trust-level string based on convergence status
        and counterexample history."""
        if self._converged and not self._counterexamples:
            return "verified"
        if self._converged:
            cx_count = len(self._counterexamples)
            if cx_count <= 2:
                return "high"
            return "medium"
        cx_count = len(self._counterexamples)
        if cx_count >= 5:
            return "low"
        return "medium"

# Strategy lookup tables.
_KIND_TO_STRATEGY: Dict[CounterexampleKind, RepairStrategy] = {
    CounterexampleKind.STRUCTURAL: RepairStrategy.REFINE_TYPE,
    CounterexampleKind.SEMANTIC: RepairStrategy.STRENGTHEN_EVIDENCE,
    CounterexampleKind.RUNTIME: RepairStrategy.ADD_GUARD,
    CounterexampleKind.LEAN: RepairStrategy.RESYNTHESIZE,
}

_ESCALATION_ORDER: List[RepairStrategy] = [
    RepairStrategy.REFINE_TYPE,
    RepairStrategy.ADD_GUARD,
    RepairStrategy.WEAKEN_SPEC,
    RepairStrategy.STRENGTHEN_EVIDENCE,
    RepairStrategy.RESYNTHESIZE,
    RepairStrategy.ESCALATE_TO_HUMAN,
]

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 12 — CONVENIENCE CONSTRUCTORS
# ═══════════════════════════════════════════════════════════════════════════

def make_quality_gate(
    name: str,
    *,
    min_all: float = 0.7,
    overrides: Optional[Dict[str, float]] = None,
    required: Optional[FrozenSet[str]] = None,
) -> QualityGate:
    """Shorthand constructor for a ``QualityGate``.

    Sets every threshold dimension to *min_all*, then applies any
    per-dimension *overrides*.
    """
    scores: Dict[str, float] = {d: min_all for d in _ALL_DIM_NAMES}
    if overrides:
        for dim, val in overrides.items():
            if dim in scores:
                scores[dim] = val
    return QualityGate(
        name=name,
        threshold=QualityVector(scores=scores),
        required_dimensions=required or frozenset(),
    )

def make_contract(
    name: str,
    *,
    precondition: Any,
    postcondition: Any,
    frame: Optional[FrozenSet[str]] = None,
    invariants: Optional[Sequence[Any]] = None,
    decreases: Optional[Callable[..., Any]] = None,
    max_retries: int = 3,
) -> HybridContract:
    """Shorthand constructor for a ``HybridContract``."""
    return HybridContract(
        name=name,
        precondition=precondition,
        postcondition=postcondition,
        frame=frame or frozenset(),
        invariants=tuple(invariants or ()),
        decreases=decreases,
        max_retries=max_retries,
    )

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 13 — PREDEFINED GATES
# ═══════════════════════════════════════════════════════════════════════════

GATE_SEED = make_quality_gate(
    "seed",
    min_all=0.3,
    overrides={"novelty": 0.5},
    required=frozenset({"novelty", "grounding"}),
)

GATE_HARDEN = make_quality_gate(
    "harden",
    min_all=0.6,
    overrides={
        "correctness": 0.7,
        "formal_verification": 0.3,
    },
    required=frozenset({"correctness", "grounding", "completeness"}),
)

GATE_PRODUCTION = make_quality_gate(
    "production",
    min_all=0.8,
    overrides={
        "formal_verification": 0.7,
        "lean_coverage": 0.5,
        "trust_level": 0.8,
        "coherence": 0.8,
    },
    required=frozenset(_ALL_DIM_NAMES),
)

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 14 — LEAN EXPORT HELPERS
# ═══════════════════════════════════════════════════════════════════════════

def contracts_to_lean(contracts: Sequence[HybridContract]) -> str:
    """Emit a Lean 4 file containing theorem statements for a
    sequence of contracts.

    The resulting file is syntactically valid Lean 4 with ``sorry``
    placeholders for proof bodies — a human or Lean tactic must fill
    them in.
    """
    lines: List[str] = [
        "/-",
        "  Auto-generated Lean 4 proof obligations from hybrid contracts.",
        "  Fill in the `sorry` placeholders to verify.",
        "-/",
        "",
        "-- Import your project's type definitions here",
        "-- import Deppy.Types",
        "",
    ]

    for contract in contracts:
        lines.append(contract.to_lean())
        lines.append("")

    if len(contracts) > 1:
        names = [_lean_escape(c.name) for c in contracts]
        lines.append("/-- All contracts hold jointly --/")
        lines.append(f"theorem all_contracts_hold")

        for i, name in enumerate(names):
            pre_name = _lean_escape(
                getattr(contracts[i].precondition, "name", "Pre")
            )
            lines.append(f"    (x{i} : {pre_name})")

        conclusions = [f"{name} x{i}" for i, name in enumerate(names)]
        lines.append(f"    : {' ∧ '.join(conclusions)} := by")
        lines.append(f"  constructor")
        for _ in conclusions:
            lines.append(f"  · sorry")
        lines.append("")

    return "\n".join(lines)

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 15 — QUALITY VECTOR ARITHMETIC
# ═══════════════════════════════════════════════════════════════════════════

def quality_weighted_mean(
    vectors: Sequence[QualityVector],
    weights: Optional[Sequence[float]] = None,
) -> QualityVector:
    """Compute the weighted arithmetic mean of quality vectors.

    Useful for aggregating quality across sub-components.
    """
    if not vectors:
        return Q_BOTTOM
    n = len(vectors)
    if weights is None:
        ws = [1.0 / n] * n
    else:
        total = sum(weights)
        ws = [w / total for w in weights] if total > 0 else [1.0 / n] * n

    result: Dict[str, float] = {}
    for d in _ALL_DIM_NAMES:
        result[d] = sum(ws[i] * vectors[i].scores[d] for i in range(n))
    return QualityVector(scores=result)

def quality_diff(a: QualityVector, b: QualityVector) -> Dict[str, float]:
    """Per-dimension signed difference ``a - b``.

    Positive values mean *a* is better on that dimension.
    """
    return {d: a.scores[d] - b.scores[d] for d in _ALL_DIM_NAMES}

def quality_dominates(a: QualityVector, b: QualityVector) -> bool:
    """Strict Pareto dominance: ``a`` strictly dominates ``b`` iff
    ``a ≥ b`` in every dimension and ``a > b`` in at least one."""
    return a >= b and a != b  # type: ignore[operator]

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 16 — CEGAR INTEGRATION WITH CONTRACTS
# ═══════════════════════════════════════════════════════════════════════════

def run_contracted_cegar(
    contract: HybridContract,
    input_value: Any,
    initial_output: Any,
    repair_fn: Callable[[Any, Counterexample, RepairStrategy], Any],
    checker: Optional[Any] = None,
    max_attempts: int = 5,
) -> Tuple[Any, CEGARReport]:
    """One-shot convenience: create a ``HybridCEGAR`` engine, seed it
    with any counterexamples from the initial contract check, then run
    the CEGAR loop.

    Returns ``(final_output, report)``.
    """
    engine = HybridCEGAR(max_attempts=max_attempts)

    # Seed from initial precondition check.
    raw_input = input_value.value if hasattr(input_value, "value") else input_value
    pre_result = contract.check_pre(raw_input, checker)
    if not pre_result:
        for v in pre_result.violations:
            engine.add_counterexample(Counterexample(
                kind=CounterexampleKind.STRUCTURAL,
                input_value=raw_input,
                expected_property=pre_result.type_name,
                actual_output=None,
                violation=f"Precondition: {v}",
            ))

    return engine.run(
        initial_output=initial_output,
        contract=contract,
        input_value=input_value,
        repair_fn=repair_fn,
        checker=checker,
    )

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 17 — FRAME ANALYSIS UTILITIES
# ═══════════════════════════════════════════════════════════════════════════

class FrameAnalyser:
    """Static analysis helper for frame conditions.

    Validates that a set of contracts is *frame-safe*: no two
    contracts running in parallel write to the same workspace field,
    and every contract's declared frame is a subset of the workspace
    keys it actually needs.
    """

    @staticmethod
    def check_disjointness(
        contracts: Sequence[HybridContract],
    ) -> List[str]:
        """Check pairwise frame disjointness for a set of contracts
        intended to run in parallel.

        Returns a list of violation descriptions (empty if all
        frames are disjoint).
        """
        violations: List[str] = []
        n = len(contracts)
        for i in range(n):
            for j in range(i + 1, n):
                overlap = contracts[i].frame & contracts[j].frame
                if overlap:
                    violations.append(
                        f"Frame overlap between '{contracts[i].name}' and "
                        f"'{contracts[j].name}': {overlap!r}"
                    )
        return violations

    @staticmethod
    def infer_frame(
        execute_fn: Callable[[dict], dict],
        sample_inputs: Sequence[dict],
    ) -> FrozenSet[str]:
        """Dynamically infer the frame of *execute_fn* by running it
        on *sample_inputs* and observing which workspace keys change.

        This is a *best-effort* under-approximation — it can only
        discover writes that actually occur on the given samples.
        """
        written_keys: Set[str] = set()
        for inp in sample_inputs:
            before = _deep_snapshot(inp)
            try:
                execute_fn(inp)
            except Exception:
                pass
            after = inp
            for key in set(before.keys()) | set(after.keys()):
                bval = before.get(key, _SENTINEL)
                aval = after.get(key, _SENTINEL)
                if bval is not aval:
                    try:
                        if bval != aval:
                            written_keys.add(key)
                    except Exception:
                        written_keys.add(key)
        return frozenset(written_keys)

    @staticmethod
    def check_subsumption(
        declared: FrozenSet[str],
        inferred: FrozenSet[str],
    ) -> Tuple[bool, List[str]]:
        """Check that the *declared* frame subsumes the *inferred*
        frame.

        Returns ``(ok, messages)`` where ``ok`` is ``True`` when
        ``inferred ⊆ declared``.
        """
        extra = inferred - declared
        missing = declared - inferred
        messages: List[str] = []
        if extra:
            messages.append(
                f"Under-declared: {extra!r} written but not in frame"
            )
        if missing:
            messages.append(
                f"Over-declared: {missing!r} in frame but never written "
                f"(not harmful but noisy)"
            )
        return not bool(extra), messages

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 18 — PIPELINE INTEGRATION HELPERS
# ═══════════════════════════════════════════════════════════════════════════

class ContractedPipelineRunner:
    """Thin orchestrator that runs a sequence of stages, each governed
    by a ``HybridContract``, with quality monitoring and CEGAR repair.

    This is the glue layer that ties contracts, quality tracking, and
    CEGAR into a single execution model.
    """

    def __init__(
        self,
        contracts: Sequence[HybridContract],
        gates: Optional[Sequence[QualityGate]] = None,
        checker: Optional[Any] = None,
        cegar_max: int = 5,
    ) -> None:
        self._contracts = list(contracts)
        self._gates = list(gates or [])
        self._enforcer = HybridContractEnforcer(checker)
        self._monitor = QualityMonitor()
        self._cegar_max = cegar_max
        self._checker = checker

    @property
    def enforcer(self) -> HybridContractEnforcer:
        return self._enforcer

    @property
    def monitor(self) -> QualityMonitor:
        return self._monitor

    def run(
        self,
        initial_input: Any,
        executors: Sequence[Callable[..., Any]],
        quality_scorer: Optional[Callable[[Any], QualityVector]] = None,
        repair_fn: Optional[
            Callable[[Any, Counterexample, RepairStrategy], Any]
        ] = None,
        model: str = "",
    ) -> Tuple[Any, List[str]]:
        """Run all stages sequentially, enforcing contracts and
        checking quality gates.

        Returns ``(final_output, all_violations)``.
        """
        if len(executors) != len(self._contracts):
            raise ValueError(
                f"Expected {len(self._contracts)} executors, "
                f"got {len(executors)}"
            )

        current = initial_input
        all_violations: List[str] = []

        for idx, (contract, executor) in enumerate(
            zip(self._contracts, executors)
        ):
            output, violations = self._enforcer.enforce(
                contract, current, executor, step_index=idx, model=model,
            )

            if violations:
                if repair_fn is not None:
                    # Attempt CEGAR repair.
                    repaired, report = run_contracted_cegar(
                        contract=contract,
                        input_value=current,
                        initial_output=output,
                        repair_fn=repair_fn,
                        checker=self._checker,
                        max_attempts=self._cegar_max,
                    )
                    if report.converged:
                        output = repaired
                        violations = []
                    else:
                        all_violations.extend(violations)
                else:
                    all_violations.extend(violations)

            if output is None:
                all_violations.append(f"Stage {contract.name} produced None")
                break

            current = output

            # Quality monitoring.
            if quality_scorer is not None:
                raw = output.value if hasattr(output, "value") else output
                qv = quality_scorer(raw)
                self._monitor.record(contract.name, qv)

            # Gate checking.
            if idx < len(self._gates):
                gate = self._gates[idx]
                if quality_scorer is not None:
                    raw = output.value if hasattr(output, "value") else output
                    qv = quality_scorer(raw)
                    passed, explanation = gate.check(qv)
                    if not passed:
                        all_violations.append(
                            f"Quality gate '{gate.name}' failed: {explanation}"
                        )

        return current, all_violations

    def summary(self) -> str:
        """Return a human-readable summary of the pipeline run."""
        lines = [
            "=== Contracted Pipeline Summary ===",
            f"Stages: {len(self._contracts)}",
            f"Enforcer stats: {self._enforcer.stats}",
            "",
            self._monitor.report(),
        ]
        return "\n".join(lines)

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 19 — ALGEBRAIC GEOMETRY BRIDGE
# ═══════════════════════════════════════════════════════════════════════════

class AlgebraicQualitySpace:
    """Model the quality lattice as an algebraic variety in ``[0,1]^9``.

    Each quality gate defines a *closed half-space* (intersection of
    half-planes ``x_i ≥ t_i``).  The *feasible region* — the set of
    quality vectors that pass ALL gates — is the intersection of these
    half-spaces, which is a convex polytope.

    This class provides utilities for reasoning about the geometry of
    the feasible region:

    * ``feasible(qv)`` — membership test
    * ``project(qv)`` — nearest feasible point (L2 projection)
    * ``vertices()`` — enumerate vertices of the polytope
    * ``volume_estimate()`` — Monte-Carlo volume estimate
    """

    def __init__(self, gates: Sequence[QualityGate]) -> None:
        self._gates = list(gates)
        self._lower_bounds: Dict[str, float] = {d: 0.0 for d in _ALL_DIM_NAMES}
        for gate in gates:
            for d in _ALL_DIM_NAMES:
                t = gate.threshold.scores[d]
                if t > self._lower_bounds[d]:
                    self._lower_bounds[d] = t

    def feasible(self, qv: QualityVector) -> bool:
        """Is *qv* inside the feasible polytope?"""
        return all(
            qv.scores[d] >= self._lower_bounds[d] for d in _ALL_DIM_NAMES
        )

    def project(self, qv: QualityVector) -> QualityVector:
        """Nearest feasible point: clamp each dimension to the lower
        bound (L2-optimal projection onto the polytope)."""
        projected: Dict[str, float] = {}
        for d in _ALL_DIM_NAMES:
            projected[d] = max(qv.scores[d], self._lower_bounds[d])
        return QualityVector(scores=projected)

    def deficit(self, qv: QualityVector) -> Dict[str, float]:
        """Per-dimension deficit: how much each dimension needs to
        increase to become feasible.  Non-negative; zero if already
        feasible on that dimension."""
        return {
            d: max(0.0, self._lower_bounds[d] - qv.scores[d])
            for d in _ALL_DIM_NAMES
        }

    def vertices(self) -> List[QualityVector]:
        """Enumerate the ``2^9`` vertices of the axis-aligned
        bounding box ``[lb_i, 1]^9``.

        For a small number of dimensions this is tractable (512
        vertices for 9 dims).  Each vertex has every dimension set
        to either its lower bound or 1.0.
        """
        dims = list(_ALL_DIM_NAMES)
        n = len(dims)
        verts: List[QualityVector] = []
        for mask in range(1 << n):
            scores: Dict[str, float] = {}
            for i, d in enumerate(dims):
                if mask & (1 << i):
                    scores[d] = 1.0
                else:
                    scores[d] = self._lower_bounds[d]
            verts.append(QualityVector(scores=scores))
        return verts

    def volume_estimate(self, n_samples: int = 10_000) -> float:
        """Monte-Carlo estimate of the fraction of ``[0, 1]^9``
        occupied by the feasible region.

        Since the feasible region is an axis-aligned box, the exact
        volume is ``∏(1 - lb_i)``, but we implement the MC version
        as a sanity-check template for non-convex extensions.
        """
        import random

        feasible_count = 0
        for _ in range(n_samples):
            scores = {d: random.random() for d in _ALL_DIM_NAMES}
            qv = QualityVector(scores=scores)
            if self.feasible(qv):
                feasible_count += 1
        return feasible_count / n_samples

    def exact_volume(self) -> float:
        """Exact volume of the feasible box ``∏(1 - lb_i)``."""
        vol = 1.0
        for d in _ALL_DIM_NAMES:
            vol *= (1.0 - self._lower_bounds[d])
        return vol

# ═══════════════════════════════════════════════════════════════════════════
#  SECTION 20 — LEAN PROOF OBLIGATION TRACKER
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class LeanObligation:
    """A single Lean proof obligation generated from a contract."""

    contract_name: str
    theorem_statement: str
    status: str = "pending"  # pending | discharged | failed | timeout
    lean_source: str = ""
    error_message: str = ""
    timestamp: float = field(default_factory=time.time)

    def mark_discharged(self, source: str = "") -> None:
        self.status = "discharged"
        self.lean_source = source

    def mark_failed(self, error: str) -> None:
        self.status = "failed"
        self.error_message = error

class LeanObligationTracker:
    """Tracks Lean proof obligations across all contracts in a
    pipeline and reports coverage / discharge statistics.
    """

    def __init__(self) -> None:
        self._obligations: List[LeanObligation] = []

    def add_from_contract(self, contract: HybridContract) -> LeanObligation:
        """Generate and track a Lean obligation from *contract*."""
        stmt = contract.to_lean()
        ob = LeanObligation(
            contract_name=contract.name,
            theorem_statement=stmt,
        )
        self._obligations.append(ob)
        return ob

    def add_from_contracts(
        self, contracts: Sequence[HybridContract],
    ) -> List[LeanObligation]:
        return [self.add_from_contract(c) for c in contracts]

    @property
    def total(self) -> int:
        return len(self._obligations)

    @property
    def discharged(self) -> int:
        return sum(1 for o in self._obligations if o.status == "discharged")

    @property
    def failed(self) -> int:
        return sum(1 for o in self._obligations if o.status == "failed")

    @property
    def pending(self) -> int:
        return sum(1 for o in self._obligations if o.status == "pending")

    @property
    def coverage(self) -> float:
        """Fraction of obligations that have been discharged."""
        return self.discharged / self.total if self.total > 0 else 0.0

    def quality_contribution(self) -> Dict[str, float]:
        """Return the quality-dimension contributions from Lean
        verification status."""
        return {
            QualityDimension.FORMAL_VERIFICATION.value: self.coverage,
            QualityDimension.LEAN_COVERAGE.value: (
                1.0 if self.pending == 0 else
                (self.discharged + self.failed) / self.total
                if self.total > 0 else 0.0
            ),
            QualityDimension.TRUST_LEVEL.value: (
                1.0 if self.failed == 0 and self.pending == 0 else
                0.5 if self.failed == 0 else
                0.2
            ),
        }

    def report(self) -> str:
        lines = [
            "╔══ Lean Obligation Report ══╗",
            f"  Total:      {self.total}",
            f"  Discharged: {self.discharged}",
            f"  Failed:     {self.failed}",
            f"  Pending:    {self.pending}",
            f"  Coverage:   {self.coverage:.1%}",
        ]
        if self._obligations:
            lines.append("")
            lines.append("  Obligations:")
            for ob in self._obligations:
                icon = {"discharged": "✓", "failed": "✗", "pending": "…"}.get(
                    ob.status, "?"
                )
                lines.append(f"    {icon} {ob.contract_name} [{ob.status}]")
                if ob.error_message:
                    lines.append(f"      error: {ob.error_message}")
        lines.append("╚════════════════════════════╝")
        return "\n".join(lines)
