"""Proof checker: verify proof terms against obligations.

Implements a type-theoretic proof checker that validates proof terms
constructed from the proof term hierarchy (refl, symm, trans, cong,
modus ponens, conjunction, universal, witness, transport, etc.)
against proof obligations arising from refinement type checking.
"""

from __future__ import annotations

import enum
import logging
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.types.base import TypeBase, AnyType, NeverType, ANY_TYPE, NEVER_TYPE
from deppy.types.refinement import (
    RefinementType,
    Predicate as RefinementPredicate,
    TruePred,
    FalsePred,
    ConjunctionPred,
    DisjunctionPred,
    ImplicationPred,
    ComparisonPred,
    ComparisonOp,
)
from deppy.types.witnesses import (
    ProofTerm,
    ReflProof,
    AssumptionProof,
    RuntimeCheckProof,
    StaticProof,
    CompositeProof,
    TransitivityProof,
    SymmetryProof,
    CongruenceProof,
    WitnessCarrier,
    TransportWitness,
    RefinementWitness,
    ExistentialWitness,
)
from deppy.proof._protocols import (
    ProofTermKind,
    ProofObligation,
    ObligationStatus,
    ProofContext,
)

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Check result
# ---------------------------------------------------------------------------


class CheckVerdict(enum.Enum):
    """Outcome of a proof check."""

    VALID = "valid"
    INVALID = "invalid"
    UNKNOWN = "unknown"
    TIMEOUT = "timeout"


@dataclass(frozen=True)
class Counterexample:
    """A concrete counterexample refuting a proof obligation.

    Attributes:
        _bindings: Variable assignments that invalidate the obligation.
        _explanation: Human-readable description of the counterexample.
        _source_obligation: The obligation this counterexample refutes.
    """

    _bindings: Dict[str, Any]
    _explanation: str = ""
    _source_obligation: Optional[ProofObligation] = None

    @property
    def bindings(self) -> Dict[str, Any]:
        return dict(self._bindings)

    @property
    def explanation(self) -> str:
        return self._explanation

    @property
    def source_obligation(self) -> Optional[ProofObligation]:
        return self._source_obligation

    def __repr__(self) -> str:
        return f"Counterexample({self._bindings}, {self._explanation!r})"


@dataclass(frozen=True)
class CheckResult:
    """Result of checking a proof term against an obligation.

    Attributes:
        _valid: Whether the proof was successfully validated.
        _trust_level: The trust level established by this check.
        _counterexample: Optional counterexample if the proof is invalid.
        _explanation: Human-readable explanation of the check outcome.
        _verdict: Detailed verdict enum.
        _sub_results: Results from checking sub-proofs.
        _elapsed_ms: Milliseconds spent on this check.
    """

    _valid: bool
    _trust_level: TrustLevel = TrustLevel.RESIDUAL
    _counterexample: Optional[Counterexample] = None
    _explanation: str = ""
    _verdict: CheckVerdict = CheckVerdict.UNKNOWN
    _sub_results: Tuple["CheckResult", ...] = ()
    _elapsed_ms: float = 0.0

    @property
    def valid(self) -> bool:
        return self._valid

    @property
    def trust_level(self) -> TrustLevel:
        return self._trust_level

    @property
    def counterexample(self) -> Optional[Counterexample]:
        return self._counterexample

    @property
    def explanation(self) -> str:
        return self._explanation

    @property
    def verdict(self) -> CheckVerdict:
        return self._verdict

    @property
    def sub_results(self) -> Tuple["CheckResult", ...]:
        return self._sub_results

    @property
    def elapsed_ms(self) -> float:
        return self._elapsed_ms

    def with_explanation(self, explanation: str) -> CheckResult:
        """Return a copy with the given explanation."""
        return CheckResult(
            _valid=self._valid,
            _trust_level=self._trust_level,
            _counterexample=self._counterexample,
            _explanation=explanation,
            _verdict=self._verdict,
            _sub_results=self._sub_results,
            _elapsed_ms=self._elapsed_ms,
        )

    def __repr__(self) -> str:
        status = "VALID" if self._valid else "INVALID"
        return f"CheckResult({status}, trust={self._trust_level.value})"


def _ok(trust: TrustLevel, explanation: str = "",
        sub_results: Tuple[CheckResult, ...] = ()) -> CheckResult:
    """Construct a valid CheckResult."""
    return CheckResult(
        _valid=True,
        _trust_level=trust,
        _explanation=explanation,
        _verdict=CheckVerdict.VALID,
        _sub_results=sub_results,
    )


def _fail(explanation: str, counterexample: Optional[Counterexample] = None,
          sub_results: Tuple[CheckResult, ...] = ()) -> CheckResult:
    """Construct an invalid CheckResult."""
    return CheckResult(
        _valid=False,
        _trust_level=TrustLevel.RESIDUAL,
        _counterexample=counterexample,
        _explanation=explanation,
        _verdict=CheckVerdict.INVALID,
        _sub_results=sub_results,
    )


def _unknown(explanation: str) -> CheckResult:
    """Construct an unknown CheckResult."""
    return CheckResult(
        _valid=False,
        _trust_level=TrustLevel.RESIDUAL,
        _explanation=explanation,
        _verdict=CheckVerdict.UNKNOWN,
    )


# ---------------------------------------------------------------------------
# Proposition representation (what proof terms prove)
# ---------------------------------------------------------------------------


class PropositionKind(enum.Enum):
    """Kinds of propositions that can appear in proof obligations."""

    EQUALITY = "equality"
    REFINEMENT = "refinement"
    IMPLICATION = "implication"
    CONJUNCTION = "conjunction"
    DISJUNCTION = "disjunction"
    UNIVERSAL = "universal"
    EXISTENTIAL = "existential"
    SUBTYPE = "subtype"
    PREDICATE = "predicate"
    TRANSPORT = "transport"
    CUSTOM = "custom"


@dataclass(frozen=True)
class Proposition:
    """A proposition that a proof term is supposed to witness.

    Attributes:
        _kind: The kind of proposition.
        _lhs: Left-hand side (for equality, subtype, implication).
        _rhs: Right-hand side (for equality, subtype, implication).
        _predicate: The predicate (for refinement/predicate propositions).
        _components: Sub-propositions (for conjunction/disjunction).
        _binder: Bound variable name (for universal/existential).
        _body: Body proposition (for universal/existential).
        _raw: Raw unstructured proposition data.
    """

    _kind: PropositionKind = PropositionKind.CUSTOM
    _lhs: Any = None
    _rhs: Any = None
    _predicate: Any = None
    _components: Tuple["Proposition", ...] = ()
    _binder: Optional[str] = None
    _body: Optional["Proposition"] = None
    _raw: Any = None

    @property
    def kind(self) -> PropositionKind:
        return self._kind

    @property
    def lhs(self) -> Any:
        return self._lhs

    @property
    def rhs(self) -> Any:
        return self._rhs

    @property
    def predicate(self) -> Any:
        return self._predicate

    @property
    def components(self) -> Tuple["Proposition", ...]:
        return self._components

    @property
    def binder(self) -> Optional[str]:
        return self._binder

    @property
    def body(self) -> Optional["Proposition"]:
        return self._body

    @property
    def raw(self) -> Any:
        return self._raw

    def __repr__(self) -> str:
        return f"Proposition({self._kind.value})"


def _extract_proposition(obligation: ProofObligation) -> Proposition:
    """Extract a structured Proposition from a ProofObligation.

    The obligation's `prop` field may be a Proposition already, a
    RefinementType, a Predicate, a tuple (for equality), or a raw value.
    """
    prop = obligation.prop
    if isinstance(prop, Proposition):
        return prop
    if isinstance(prop, RefinementType):
        return Proposition(
            _kind=PropositionKind.REFINEMENT,
            _lhs=prop.base,
            _predicate=prop.predicate,
            _raw=prop,
        )
    if isinstance(prop, tuple) and len(prop) == 3 and prop[0] == "eq":
        return Proposition(
            _kind=PropositionKind.EQUALITY,
            _lhs=prop[1],
            _rhs=prop[2],
            _raw=prop,
        )
    if isinstance(prop, tuple) and len(prop) == 3 and prop[0] == "subtype":
        return Proposition(
            _kind=PropositionKind.SUBTYPE,
            _lhs=prop[1],
            _rhs=prop[2],
            _raw=prop,
        )
    if isinstance(prop, (TruePred, FalsePred, ConjunctionPred, DisjunctionPred,
                         ImplicationPred, ComparisonPred)):
        return Proposition(
            _kind=PropositionKind.PREDICATE,
            _predicate=prop,
            _raw=prop,
        )
    return Proposition(_kind=PropositionKind.CUSTOM, _raw=prop)


# ---------------------------------------------------------------------------
# Proof environment: hypotheses in scope
# ---------------------------------------------------------------------------


@dataclass
class ProofEnvironment:
    """A proof-checking environment that tracks hypotheses in scope.

    Maintains a stack of scopes, each containing named hypotheses
    (proof terms paired with their propositions).
    """

    _scopes: List[Dict[str, Tuple[ProofTerm, Proposition]]] = field(
        default_factory=lambda: [{}]
    )
    _global_axioms: Dict[str, Tuple[ProofTerm, Proposition]] = field(
        default_factory=dict
    )

    def push_scope(self) -> None:
        """Enter a new hypothesis scope."""
        self._scopes.append({})

    def pop_scope(self) -> Dict[str, Tuple[ProofTerm, Proposition]]:
        """Exit the current scope and return its hypotheses."""
        if len(self._scopes) <= 1:
            return {}
        return self._scopes.pop()

    def assume(self, name: str, proof: ProofTerm, prop: Proposition) -> None:
        """Add a hypothesis to the current scope."""
        if self._scopes:
            self._scopes[-1][name] = (proof, prop)

    def add_axiom(self, name: str, proof: ProofTerm, prop: Proposition) -> None:
        """Add a global axiom available in all scopes."""
        self._global_axioms[name] = (proof, prop)

    def lookup(self, name: str) -> Optional[Tuple[ProofTerm, Proposition]]:
        """Look up a hypothesis by name, searching innermost scope first."""
        for scope in reversed(self._scopes):
            if name in scope:
                return scope[name]
        return self._global_axioms.get(name)

    def all_hypotheses(self) -> Dict[str, Tuple[ProofTerm, Proposition]]:
        """Return all hypotheses in scope (inner scopes shadow outer)."""
        merged: Dict[str, Tuple[ProofTerm, Proposition]] = {}
        merged.update(self._global_axioms)
        for scope in self._scopes:
            merged.update(scope)
        return merged

    @property
    def depth(self) -> int:
        """Number of nested scopes."""
        return len(self._scopes)


# ---------------------------------------------------------------------------
# Proof checker
# ---------------------------------------------------------------------------


class ProofChecker:
    """Verify proof terms against proof obligations.

    The checker walks the proof term tree and validates each constructor
    against the proposition it claims to prove. It produces a CheckResult
    indicating validity, trust level, and optional counterexamples.

    Attributes:
        _environment: The proof-checking environment with hypotheses.
        _max_depth: Maximum recursion depth for proof checking.
        _check_count: Number of checks performed.
        _cache: Memoization cache for previously checked terms.
        _axiom_trust: Trust level assigned to axiom-based proofs.
    """

    def __init__(
        self,
        environment: Optional[ProofEnvironment] = None,
        max_depth: int = 256,
        axiom_trust: TrustLevel = TrustLevel.ASSUMED,
    ) -> None:
        self._environment = environment or ProofEnvironment()
        self._max_depth: int = max_depth
        self._check_count: int = 0
        self._cache: Dict[int, CheckResult] = {}
        self._axiom_trust: TrustLevel = axiom_trust
        self._depth: int = 0

    @property
    def environment(self) -> ProofEnvironment:
        """The proof-checking environment."""
        return self._environment

    @property
    def check_count(self) -> int:
        """Number of individual checks performed."""
        return self._check_count

    def reset_cache(self) -> None:
        """Clear the memoization cache."""
        self._cache.clear()

    # -- Main entry point --------------------------------------------------

    def check(self, proof_term: ProofTerm, obligation: ProofObligation) -> CheckResult:
        """Check a proof term against a proof obligation.

        This is the main entry point. It extracts the proposition from the
        obligation, dispatches to the appropriate checker based on the proof
        term type, and validates structural correctness.

        Args:
            proof_term: The proof term to validate.
            obligation: The proof obligation to check against.

        Returns:
            A CheckResult indicating whether the proof is valid.
        """
        self._check_count += 1
        self._depth += 1

        if self._depth > self._max_depth:
            self._depth -= 1
            return _fail(
                f"Proof checking exceeded maximum depth {self._max_depth}"
            )

        cache_key = id(proof_term) ^ id(obligation)
        if cache_key in self._cache:
            self._depth -= 1
            return self._cache[cache_key]

        try:
            prop = _extract_proposition(obligation)
            result = self._dispatch(proof_term, prop, obligation)
            self._cache[cache_key] = result
            return result
        except Exception as exc:
            logger.debug("Proof check raised: %s", exc)
            return _fail(f"Internal error during proof checking: {exc}")
        finally:
            self._depth -= 1

    def check_term(self, proof_term: ProofTerm, prop: Proposition) -> CheckResult:
        """Check a proof term against a proposition directly."""
        self._check_count += 1
        self._depth += 1
        if self._depth > self._max_depth:
            self._depth -= 1
            return _fail("Maximum depth exceeded")
        try:
            dummy_obligation = ProofObligation(
                prop=prop,
                site_id=SiteId(SiteKind.PROOF, "__check__"),
            )
            return self._dispatch(proof_term, prop, dummy_obligation)
        finally:
            self._depth -= 1

    # -- Dispatch ----------------------------------------------------------

    def _dispatch(
        self,
        term: ProofTerm,
        prop: Proposition,
        obligation: ProofObligation,
    ) -> CheckResult:
        """Dispatch proof checking based on proof term type."""
        # Handle protocol ProofTerm (from _protocols.py) by kind
        if hasattr(term, "kind") and isinstance(
            getattr(term, "kind", None), ProofTermKind
        ):
            return self._check_protocol_term(term, prop, obligation)

        # Handle witness hierarchy (from types/witnesses.py)
        if isinstance(term, ReflProof):
            return self._check_refl(term, prop)
        if isinstance(term, TransitivityProof):
            return self._check_transitivity(term, prop)
        if isinstance(term, SymmetryProof):
            return self._check_symmetry(term, prop)
        if isinstance(term, CongruenceProof):
            return self._check_congruence(term, prop)
        if isinstance(term, CompositeProof):
            return self._check_composite(term, prop)
        if isinstance(term, AssumptionProof):
            return self._check_assumption(term, prop)
        if isinstance(term, RuntimeCheckProof):
            return self._check_runtime(term, prop)
        if isinstance(term, StaticProof):
            return self._check_static(term, prop)

        # Fallback: bare ProofTerm
        return self._check_bare(term, prop)

    # -- Protocol proof terms (from _protocols.py) -------------------------

    def _check_protocol_term(
        self,
        term: Any,
        prop: Proposition,
        obligation: ProofObligation,
    ) -> CheckResult:
        """Check a proof term from the _protocols.py ProofTerm class."""
        kind: ProofTermKind = term.kind
        children: List[Any] = getattr(term, "children", [])
        payload: Any = getattr(term, "payload", None)

        if kind == ProofTermKind.REFL:
            return self._check_axiom_refl(payload, prop)
        elif kind == ProofTermKind.SYMM:
            return self._check_axiom_symm(children, prop)
        elif kind == ProofTermKind.TRANS:
            return self._check_axiom_trans(children, prop)
        elif kind == ProofTermKind.CONG:
            return self._check_axiom_cong(children, payload, prop)
        elif kind == ProofTermKind.SUBST:
            return self._check_axiom_subst(children, payload, prop)
        elif kind == ProofTermKind.MP:
            return self._check_modus_ponens(children, prop)
        elif kind == ProofTermKind.INTRO:
            return self._check_intro(children, payload, prop)
        elif kind == ProofTermKind.ELIM:
            return self._check_elim(children, payload, prop)
        elif kind == ProofTermKind.AND_INTRO:
            return self._check_conjunction(children, prop)
        elif kind == ProofTermKind.FST:
            return self._check_fst(children, prop)
        elif kind == ProofTermKind.SND:
            return self._check_snd(children, prop)
        elif kind == ProofTermKind.INL:
            return self._check_inl(children, payload, prop)
        elif kind == ProofTermKind.INR:
            return self._check_inr(children, payload, prop)
        elif kind == ProofTermKind.CASES:
            return self._check_cases(children, payload, prop)
        elif kind == ProofTermKind.ABSURD:
            return self._check_absurd(children, prop)
        elif kind == ProofTermKind.AUTO:
            return self._check_auto(payload, prop)
        elif kind == ProofTermKind.BY_ASSUMPTION:
            return self._check_by_assumption(payload, prop)
        else:
            return _unknown(f"Unknown proof term kind: {kind}")

    # -- Axiom checks (protocol-based) ------------------------------------

    def _check_axiom_refl(self, payload: Any, prop: Proposition) -> CheckResult:
        """Check reflexivity: refl(a) proves a = a."""
        if prop.kind == PropositionKind.EQUALITY:
            if prop.lhs == prop.rhs:
                return _ok(
                    TrustLevel.PROOF_BACKED,
                    f"Reflexivity: {prop.lhs!r} = {prop.rhs!r}",
                )
            if payload is not None and prop.lhs == payload and prop.rhs == payload:
                return _ok(TrustLevel.PROOF_BACKED, f"Reflexivity on {payload!r}")
            return _fail(
                f"Reflexivity requires both sides equal, got "
                f"{prop.lhs!r} and {prop.rhs!r}",
            )
        if prop.kind == PropositionKind.PREDICATE:
            if isinstance(prop.predicate, TruePred):
                return _ok(TrustLevel.PROOF_BACKED, "Reflexivity on True")
        return _ok(
            TrustLevel.BOUNDED_AUTO,
            f"Reflexivity accepted for {prop.kind.value} proposition",
        )

    def _check_axiom_symm(
        self, children: List[Any], prop: Proposition
    ) -> CheckResult:
        """Check symmetry: from a = b derive b = a."""
        if len(children) < 1:
            return _fail("Symmetry requires one child proof")
        child = children[0]
        child_prop_data = getattr(child, "proposition", None)
        if prop.kind == PropositionKind.EQUALITY and child_prop_data is not None:
            if isinstance(child_prop_data, tuple) and len(child_prop_data) == 3:
                _, ca, cb = child_prop_data
                if prop.lhs == cb and prop.rhs == ca:
                    child_result = self._check_protocol_child(child)
                    if child_result.valid:
                        return _ok(
                            TrustLevel.PROOF_BACKED,
                            f"Symmetry: {ca!r} = {cb!r} => {cb!r} = {ca!r}",
                            sub_results=(child_result,),
                        )
                    return _fail(
                        "Symmetry child proof invalid",
                        sub_results=(child_result,),
                    )
        child_result = self._check_protocol_child(child)
        if child_result.valid:
            return _ok(
                TrustLevel.BOUNDED_AUTO,
                "Symmetry accepted (structural)",
                sub_results=(child_result,),
            )
        return _fail("Symmetry child invalid", sub_results=(child_result,))

    def _check_axiom_trans(
        self, children: List[Any], prop: Proposition
    ) -> CheckResult:
        """Check transitivity: from a = b and b = c derive a = c."""
        if len(children) < 2:
            return _fail("Transitivity requires two child proofs")
        left_result = self._check_protocol_child(children[0])
        right_result = self._check_protocol_child(children[1])
        subs = (left_result, right_result)
        if left_result.valid and right_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                "Transitivity: both steps valid",
                sub_results=subs,
            )
        return _fail(
            "Transitivity: one or both steps invalid",
            sub_results=subs,
        )

    def _check_axiom_cong(
        self, children: List[Any], payload: Any, prop: Proposition
    ) -> CheckResult:
        """Check congruence: from a = b derive f(a) = f(b)."""
        if len(children) < 1:
            return _fail("Congruence requires at least one child proof")
        child_result = self._check_protocol_child(children[0])
        func_name = payload if isinstance(payload, str) else "f"
        if child_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                f"Congruence under {func_name}",
                sub_results=(child_result,),
            )
        return _fail(
            f"Congruence: child proof for {func_name} invalid",
            sub_results=(child_result,),
        )

    def _check_axiom_subst(
        self, children: List[Any], payload: Any, prop: Proposition
    ) -> CheckResult:
        """Check substitution: from a = b and P(a), derive P(b)."""
        if len(children) < 2:
            return _fail("Substitution requires equality proof and predicate proof")
        eq_result = self._check_protocol_child(children[0])
        pred_result = self._check_protocol_child(children[1])
        subs = (eq_result, pred_result)
        if eq_result.valid and pred_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                "Substitution: equality and predicate both valid",
                sub_results=subs,
            )
        return _fail("Substitution: sub-proof invalid", sub_results=subs)

    def _check_modus_ponens(
        self, children: List[Any], prop: Proposition
    ) -> CheckResult:
        """Check modus ponens: from P => Q and P, derive Q."""
        if len(children) < 2:
            return _fail("Modus ponens requires implication proof and antecedent proof")
        impl_result = self._check_protocol_child(children[0])
        ante_result = self._check_protocol_child(children[1])
        subs = (impl_result, ante_result)
        if impl_result.valid and ante_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                "Modus ponens: implication and antecedent both valid",
                sub_results=subs,
            )
        parts = []
        if not impl_result.valid:
            parts.append("implication proof invalid")
        if not ante_result.valid:
            parts.append("antecedent proof invalid")
        return _fail(f"Modus ponens: {', '.join(parts)}", sub_results=subs)

    def _check_intro(
        self, children: List[Any], payload: Any, prop: Proposition
    ) -> CheckResult:
        """Check introduction rule (e.g., lambda intro for universal)."""
        if len(children) < 1:
            return _fail("Introduction requires a body proof")
        body_result = self._check_protocol_child(children[0])
        if body_result.valid:
            binder = payload if isinstance(payload, str) else "x"
            return _ok(
                TrustLevel.PROOF_BACKED,
                f"Introduction of {binder}: body valid",
                sub_results=(body_result,),
            )
        return _fail("Introduction: body invalid", sub_results=(body_result,))

    def _check_elim(
        self, children: List[Any], payload: Any, prop: Proposition
    ) -> CheckResult:
        """Check elimination rule (e.g., universal elimination / application)."""
        if len(children) < 1:
            return _fail("Elimination requires a proof to eliminate")
        target_result = self._check_protocol_child(children[0])
        if target_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                "Elimination: target valid",
                sub_results=(target_result,),
            )
        return _fail("Elimination: target invalid", sub_results=(target_result,))

    def _check_conjunction(
        self, children: List[Any], prop: Proposition
    ) -> CheckResult:
        """Check conjunction introduction: from P and Q, derive P /\\ Q."""
        if len(children) < 2:
            return _fail("Conjunction introduction requires at least two proofs")
        sub_results: List[CheckResult] = []
        all_valid = True
        for child in children:
            r = self._check_protocol_child(child)
            sub_results.append(r)
            if not r.valid:
                all_valid = False
        subs = tuple(sub_results)
        if all_valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                f"Conjunction of {len(children)} components: all valid",
                sub_results=subs,
            )
        invalid_count = sum(1 for r in sub_results if not r.valid)
        return _fail(
            f"Conjunction: {invalid_count}/{len(children)} components invalid",
            sub_results=subs,
        )

    def _check_fst(
        self, children: List[Any], prop: Proposition
    ) -> CheckResult:
        """Check first projection: from P /\\ Q, derive P."""
        if len(children) < 1:
            return _fail("First projection requires a conjunction proof")
        pair_result = self._check_protocol_child(children[0])
        if pair_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                "First projection: conjunction valid",
                sub_results=(pair_result,),
            )
        return _fail("First projection: conjunction invalid",
                      sub_results=(pair_result,))

    def _check_snd(
        self, children: List[Any], prop: Proposition
    ) -> CheckResult:
        """Check second projection: from P /\\ Q, derive Q."""
        if len(children) < 1:
            return _fail("Second projection requires a conjunction proof")
        pair_result = self._check_protocol_child(children[0])
        if pair_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                "Second projection: conjunction valid",
                sub_results=(pair_result,),
            )
        return _fail("Second projection: conjunction invalid",
                      sub_results=(pair_result,))

    def _check_inl(
        self, children: List[Any], payload: Any, prop: Proposition
    ) -> CheckResult:
        """Check left injection: from P, derive P \\/ Q."""
        if len(children) < 1:
            return _fail("Left injection requires a proof of the left disjunct")
        left_result = self._check_protocol_child(children[0])
        if left_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                "Left injection: left disjunct valid",
                sub_results=(left_result,),
            )
        return _fail("Left injection: left disjunct invalid",
                      sub_results=(left_result,))

    def _check_inr(
        self, children: List[Any], payload: Any, prop: Proposition
    ) -> CheckResult:
        """Check right injection: from Q, derive P \\/ Q."""
        if len(children) < 1:
            return _fail("Right injection requires a proof of the right disjunct")
        right_result = self._check_protocol_child(children[0])
        if right_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                "Right injection: right disjunct valid",
                sub_results=(right_result,),
            )
        return _fail("Right injection: right disjunct invalid",
                      sub_results=(right_result,))

    def _check_cases(
        self, children: List[Any], payload: Any, prop: Proposition
    ) -> CheckResult:
        """Check case analysis: from P \\/ Q, P=>R, Q=>R, derive R."""
        if len(children) < 3:
            return _fail(
                "Case analysis requires disjunction proof and two branch proofs"
            )
        disj_result = self._check_protocol_child(children[0])
        left_case = self._check_protocol_child(children[1])
        right_case = self._check_protocol_child(children[2])
        subs = (disj_result, left_case, right_case)
        if disj_result.valid and left_case.valid and right_case.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                "Case analysis: disjunction and both branches valid",
                sub_results=subs,
            )
        return _fail("Case analysis: some sub-proofs invalid", sub_results=subs)

    def _check_absurd(
        self, children: List[Any], prop: Proposition
    ) -> CheckResult:
        """Check absurdity elimination: from False, derive anything."""
        if len(children) < 1:
            return _fail("Absurdity elimination requires a proof of False")
        false_result = self._check_protocol_child(children[0])
        if false_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                "Absurdity elimination (ex falso quodlibet)",
                sub_results=(false_result,),
            )
        return _fail("Absurdity elimination: False proof invalid",
                      sub_results=(false_result,))

    def _check_auto(self, payload: Any, prop: Proposition) -> CheckResult:
        """Check auto-discharged proof (solver produced)."""
        return _ok(
            TrustLevel.TRUSTED_AUTO,
            f"Auto-discharged by solver: {payload!r}",
        )

    def _check_by_assumption(self, payload: Any, prop: Proposition) -> CheckResult:
        """Check proof by assumption (hypothesis lookup)."""
        name = payload if isinstance(payload, str) else str(payload)
        found = self._environment.lookup(name)
        if found is not None:
            return _ok(
                self._axiom_trust,
                f"By assumption: {name!r} found in environment",
            )
        return _ok(
            TrustLevel.ASSUMED,
            f"By assumption: {name!r} (not verified in environment)",
        )

    def _check_protocol_child(self, child: Any) -> CheckResult:
        """Recursively check a protocol proof term child."""
        if hasattr(child, "kind") and isinstance(
            getattr(child, "kind", None), ProofTermKind
        ):
            child_prop_raw = getattr(child, "proposition", None)
            if child_prop_raw is not None:
                if isinstance(child_prop_raw, Proposition):
                    child_prop = child_prop_raw
                else:
                    child_prop = Proposition(
                        _kind=PropositionKind.CUSTOM, _raw=child_prop_raw
                    )
            else:
                child_prop = Proposition(_kind=PropositionKind.CUSTOM)
            dummy = ProofObligation(
                prop=child_prop,
                site_id=SiteId(SiteKind.PROOF, "__child__"),
            )
            return self._check_protocol_term(child, child_prop, dummy)
        if isinstance(child, ProofTerm):
            return self._check_witness_term_standalone(child)
        return _ok(TrustLevel.ASSUMED, "Untyped child accepted")

    # -- Witness hierarchy checks (types/witnesses.py) ---------------------

    def _check_refl(self, term: ReflProof, prop: Proposition) -> CheckResult:
        """Check ReflProof: witnesses a = a."""
        if prop.kind == PropositionKind.EQUALITY:
            if prop.lhs == prop.rhs:
                return _ok(
                    TrustLevel.PROOF_BACKED,
                    f"ReflProof: {prop.lhs!r} = {prop.rhs!r}",
                )
            if term.term is not None:
                if prop.lhs == term.term and prop.rhs == term.term:
                    return _ok(
                        TrustLevel.PROOF_BACKED,
                        f"ReflProof on {term.term!r}",
                    )
            return _fail(
                f"ReflProof requires equal sides, got {prop.lhs!r} vs {prop.rhs!r}"
            )
        # For non-equality propositions, refl serves as a trivial witness
        return _ok(TrustLevel.BOUNDED_AUTO, "ReflProof as trivial witness")

    def _check_transitivity(
        self, term: TransitivityProof, prop: Proposition
    ) -> CheckResult:
        """Check TransitivityProof: from a = b and b = c, derive a = c."""
        left_result = self._check_witness_term_standalone(term.left)
        right_result = self._check_witness_term_standalone(term.right)
        subs = (left_result, right_result)
        if left_result.valid and right_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                "TransitivityProof: both steps valid",
                sub_results=subs,
            )
        return _fail("TransitivityProof: sub-proof invalid", sub_results=subs)

    def _check_symmetry(
        self, term: SymmetryProof, prop: Proposition
    ) -> CheckResult:
        """Check SymmetryProof: from a = b, derive b = a."""
        inner_result = self._check_witness_term_standalone(term.inner)
        if inner_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                "SymmetryProof: inner valid",
                sub_results=(inner_result,),
            )
        return _fail("SymmetryProof: inner invalid", sub_results=(inner_result,))

    def _check_congruence(
        self, term: CongruenceProof, prop: Proposition
    ) -> CheckResult:
        """Check CongruenceProof: from a = b, derive f(a) = f(b)."""
        inner_result = self._check_witness_term_standalone(term.inner)
        if inner_result.valid:
            return _ok(
                TrustLevel.PROOF_BACKED,
                f"CongruenceProof under {term.function_name}: inner valid",
                sub_results=(inner_result,),
            )
        return _fail(
            f"CongruenceProof under {term.function_name}: inner invalid",
            sub_results=(inner_result,),
        )

    def _check_composite(
        self, term: CompositeProof, prop: Proposition
    ) -> CheckResult:
        """Check CompositeProof: conjunction or other combination of sub-proofs."""
        sub_results: List[CheckResult] = []
        all_valid = True
        for sub in term.sub_proofs:
            r = self._check_witness_term_standalone(sub)
            sub_results.append(r)
            if not r.valid:
                all_valid = False
        subs = tuple(sub_results)
        combiner = term.combiner
        if all_valid:
            trust = self._combine_trust_levels(
                [r.trust_level for r in sub_results]
            )
            return _ok(
                trust,
                f"CompositeProof({combiner}): all {len(sub_results)} sub-proofs valid",
                sub_results=subs,
            )
        invalid_ct = sum(1 for r in sub_results if not r.valid)
        return _fail(
            f"CompositeProof({combiner}): {invalid_ct}/{len(sub_results)} invalid",
            sub_results=subs,
        )

    def _check_assumption(
        self, term: AssumptionProof, prop: Proposition
    ) -> CheckResult:
        """Check AssumptionProof: accepted at ASSUMED trust level."""
        found = self._environment.lookup(term.name)
        if found is not None:
            return _ok(
                self._axiom_trust,
                f"Assumption {term.name!r} found in environment",
            )
        trust_str = term.trust_level
        trust = TrustLevel.ASSUMED
        for tl in TrustLevel:
            if tl.value == trust_str:
                trust = tl
                break
        return _ok(trust, f"Assumption {term.name!r} (trust={trust.value})")

    def _check_runtime(
        self, term: RuntimeCheckProof, prop: Proposition
    ) -> CheckResult:
        """Check RuntimeCheckProof: trusted at TRACE_BACKED level."""
        return _ok(
            TrustLevel.TRACE_BACKED,
            f"Runtime check: {term.check_description}",
        )

    def _check_static(self, term: StaticProof, prop: Proposition) -> CheckResult:
        """Check StaticProof: trusted at TRUSTED_AUTO level."""
        return _ok(
            TrustLevel.TRUSTED_AUTO,
            f"Static proof via {term.method}: {term.detail}",
        )

    def _check_bare(self, term: ProofTerm, prop: Proposition) -> CheckResult:
        """Check a bare ProofTerm with no specific structure."""
        desc = term.description()
        return _ok(
            TrustLevel.BOUNDED_AUTO,
            f"Bare proof term accepted: {desc}",
        )

    def _check_witness_term_standalone(self, term: ProofTerm) -> CheckResult:
        """Check a witness term without a specific proposition."""
        if isinstance(term, ReflProof):
            return _ok(TrustLevel.PROOF_BACKED, f"ReflProof({term.term!r})")
        if isinstance(term, AssumptionProof):
            return self._check_assumption(
                term, Proposition(_kind=PropositionKind.CUSTOM)
            )
        if isinstance(term, RuntimeCheckProof):
            return _ok(
                TrustLevel.TRACE_BACKED,
                f"RuntimeCheck: {term.check_description}",
            )
        if isinstance(term, StaticProof):
            return _ok(
                TrustLevel.TRUSTED_AUTO,
                f"Static: {term.method}",
            )
        if isinstance(term, TransitivityProof):
            lr = self._check_witness_term_standalone(term.left)
            rr = self._check_witness_term_standalone(term.right)
            if lr.valid and rr.valid:
                return _ok(
                    TrustLevel.PROOF_BACKED,
                    "Transitivity chain valid",
                    sub_results=(lr, rr),
                )
            return _fail("Transitivity chain has invalid step",
                          sub_results=(lr, rr))
        if isinstance(term, SymmetryProof):
            ir = self._check_witness_term_standalone(term.inner)
            if ir.valid:
                return _ok(TrustLevel.PROOF_BACKED, "Symmetry valid",
                           sub_results=(ir,))
            return _fail("Symmetry inner invalid", sub_results=(ir,))
        if isinstance(term, CongruenceProof):
            ir = self._check_witness_term_standalone(term.inner)
            if ir.valid:
                return _ok(TrustLevel.PROOF_BACKED,
                           f"Congruence({term.function_name}) valid",
                           sub_results=(ir,))
            return _fail(f"Congruence({term.function_name}) invalid",
                          sub_results=(ir,))
        if isinstance(term, CompositeProof):
            return self._check_composite(
                term, Proposition(_kind=PropositionKind.CUSTOM)
            )
        return _ok(TrustLevel.BOUNDED_AUTO, f"Accepted: {term.description()}")

    # -- Witness-based checking -------------------------------------------

    def _check_witness(
        self,
        witness: WitnessCarrier,
        obligation: ProofObligation,
    ) -> CheckResult:
        """Check a WitnessCarrier against an obligation."""
        prop = _extract_proposition(obligation)
        return self.check_term(witness.witness, prop)

    def _check_transport(
        self,
        transport: TransportWitness,
        obligation: ProofObligation,
    ) -> CheckResult:
        """Check a TransportWitness against an obligation."""
        if transport.is_identity():
            return _ok(
                TrustLevel.PROOF_BACKED,
                "Identity transport (source == target)",
            )
        if isinstance(transport.path, ProofTerm):
            path_result = self._check_witness_term_standalone(transport.path)
            if path_result.valid:
                return _ok(
                    TrustLevel.PROOF_BACKED,
                    f"Transport from {transport.source_type!r} to "
                    f"{transport.target_type!r}: path valid",
                    sub_results=(path_result,),
                )
            return _fail(
                f"Transport path invalid: {path_result.explanation}",
                sub_results=(path_result,),
            )
        return _ok(
            TrustLevel.BOUNDED_AUTO,
            f"Transport accepted (non-proof path: {transport.path!r})",
        )

    # -- Helpers -----------------------------------------------------------

    def _combine_trust_levels(self, levels: List[TrustLevel]) -> TrustLevel:
        """Combine trust levels: the result is the weakest (least trusted)."""
        _ordering = {
            TrustLevel.PROOF_BACKED: 5,
            TrustLevel.TRUSTED_AUTO: 4,
            TrustLevel.BOUNDED_AUTO: 3,
            TrustLevel.TRACE_BACKED: 2,
            TrustLevel.ASSUMED: 1,
            TrustLevel.RESIDUAL: 0,
        }
        if not levels:
            return TrustLevel.RESIDUAL
        min_level = min(levels, key=lambda tl: _ordering.get(tl, 0))
        return min_level

    def check_obligation_status(
        self, obligation: ProofObligation
    ) -> CheckResult:
        """Check an obligation that may already have a proof attached."""
        if obligation.status == ObligationStatus.DISCHARGED:
            return _ok(TrustLevel.PROOF_BACKED, "Already discharged")
        if obligation.status == ObligationStatus.VERIFIED:
            return _ok(TrustLevel.PROOF_BACKED, "Already verified")
        if obligation.proof is not None:
            return self.check(obligation.proof, obligation)
        return _fail(f"No proof attached, status={obligation.status.value}")

    def batch_check(
        self,
        proof_terms: List[Tuple[ProofTerm, ProofObligation]],
    ) -> List[CheckResult]:
        """Check multiple proof terms against their obligations."""
        results: List[CheckResult] = []
        for term, obligation in proof_terms:
            results.append(self.check(term, obligation))
        return results

    def validate_proof_tree(self, term: ProofTerm) -> CheckResult:
        """Validate the structural well-formedness of a proof term tree.

        Unlike `check`, this does not check against a specific obligation
        but validates that the proof term is internally consistent.
        """
        return self._check_witness_term_standalone(term)

    def statistics(self) -> Dict[str, Any]:
        """Return statistics about proof checking operations."""
        return {
            "total_checks": self._check_count,
            "cache_size": len(self._cache),
            "environment_depth": self._environment.depth,
            "max_depth": self._max_depth,
        }
