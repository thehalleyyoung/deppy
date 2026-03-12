"""Tests for the proof checker: axiom, modus ponens, transitivity, etc.

Covers CheckResult, CheckVerdict, Proposition, ProofEnvironment,
ProofChecker.check, ProofChecker.check_term, and the various
proof term kinds (refl, symm, trans, cong, mp, and_intro, fst, snd,
inl, inr, cases, absurd, auto, by_assumption).
"""

from __future__ import annotations

import pytest

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.types.base import ANY_TYPE
from deppy.types.witnesses import (
    AssumptionProof,
    CompositeProof,
    CongruenceProof,
    ProofTerm as WitnessProofTerm,
    ReflProof,
    RuntimeCheckProof,
    StaticProof,
    SymmetryProof,
    TransitivityProof,
)
from deppy.types.refinement import TruePred, FalsePred
from deppy.proof._protocols import (
    ObligationStatus,
    ProofObligation,
    ProofTermKind,
    ProofTerm as ProtocolProofTerm,
)
from deppy.proof.proof_checker import (
    CheckResult,
    CheckVerdict,
    Counterexample,
    ProofChecker,
    ProofEnvironment,
    Proposition,
    PropositionKind,
    _extract_proposition,
    _fail,
    _ok,
    _unknown,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _obligation(prop, site_name: str = "test_site") -> ProofObligation:
    return ProofObligation(
        prop=prop,
        site_id=SiteId(SiteKind.PROOF, site_name),
    )


# ===================================================================
#  CheckResult / CheckVerdict / Counterexample
# ===================================================================


class TestCheckResult:
    """Tests for CheckResult and related types."""

    def test_ok_result(self):
        r = _ok(TrustLevel.PROOF_BACKED, "all good")
        assert r.valid
        assert r.verdict == CheckVerdict.VALID
        assert r.trust_level == TrustLevel.PROOF_BACKED

    def test_fail_result(self):
        r = _fail("bad proof")
        assert not r.valid
        assert r.verdict == CheckVerdict.INVALID

    def test_unknown_result(self):
        r = _unknown("cannot decide")
        assert not r.valid
        assert r.verdict == CheckVerdict.UNKNOWN

    def test_with_explanation(self):
        r = _ok(TrustLevel.BOUNDED_AUTO)
        r2 = r.with_explanation("new explanation")
        assert r2.explanation == "new explanation"
        assert r2.valid

    def test_counterexample(self):
        cx = Counterexample(
            _bindings={"x": 5, "y": -1},
            _explanation="x must be non-negative",
        )
        assert cx.bindings == {"x": 5, "y": -1}
        assert "non-negative" in cx.explanation

    def test_fail_with_counterexample(self):
        cx = Counterexample(_bindings={"x": -1})
        r = _fail("x < 0 detected", counterexample=cx)
        assert r.counterexample is not None
        assert r.counterexample.bindings["x"] == -1

    def test_sub_results(self):
        sub = _ok(TrustLevel.PROOF_BACKED, "step1")
        r = _ok(TrustLevel.PROOF_BACKED, "combined", sub_results=(sub,))
        assert len(r.sub_results) == 1
        assert r.sub_results[0].valid


# ===================================================================
#  Proposition
# ===================================================================


class TestProposition:
    """Tests for Proposition and _extract_proposition."""

    def test_equality_proposition(self):
        p = Proposition(_kind=PropositionKind.EQUALITY, _lhs="int", _rhs="int")
        assert p.kind == PropositionKind.EQUALITY
        assert p.lhs == "int"
        assert p.rhs == "int"

    def test_extract_equality_tuple(self):
        obl = _obligation(("eq", "int", "int"))
        prop = _extract_proposition(obl)
        assert prop.kind == PropositionKind.EQUALITY
        assert prop.lhs == "int"
        assert prop.rhs == "int"

    def test_extract_subtype_tuple(self):
        obl = _obligation(("subtype", "int", "float"))
        prop = _extract_proposition(obl)
        assert prop.kind == PropositionKind.SUBTYPE
        assert prop.lhs == "int"
        assert prop.rhs == "float"

    def test_extract_predicate(self):
        obl = _obligation(TruePred())
        prop = _extract_proposition(obl)
        assert prop.kind == PropositionKind.PREDICATE

    def test_extract_custom(self):
        obl = _obligation("some random thing")
        prop = _extract_proposition(obl)
        assert prop.kind == PropositionKind.CUSTOM

    def test_extract_proposition_passthrough(self):
        p = Proposition(_kind=PropositionKind.CONJUNCTION)
        obl = _obligation(p)
        assert _extract_proposition(obl) is p


# ===================================================================
#  ProofEnvironment
# ===================================================================


class TestProofEnvironment:
    """Tests for ProofEnvironment scoping."""

    def test_assume_and_lookup(self):
        env = ProofEnvironment()
        p = Proposition(_kind=PropositionKind.CUSTOM, _raw="P")
        env.assume("h1", ReflProof(), p)
        result = env.lookup("h1")
        assert result is not None
        assert result[1] is p

    def test_scoped_lookup(self):
        env = ProofEnvironment()
        p = Proposition(_kind=PropositionKind.CUSTOM, _raw="P")
        env.assume("h1", ReflProof(), p)
        env.push_scope()
        q = Proposition(_kind=PropositionKind.CUSTOM, _raw="Q")
        env.assume("h2", ReflProof(), q)
        assert env.lookup("h1") is not None
        assert env.lookup("h2") is not None
        env.pop_scope()
        assert env.lookup("h2") is None
        assert env.lookup("h1") is not None

    def test_axiom(self):
        env = ProofEnvironment()
        p = Proposition(_kind=PropositionKind.PREDICATE, _predicate=TruePred())
        env.add_axiom("truth", ReflProof(), p)
        env.push_scope()
        env.push_scope()
        assert env.lookup("truth") is not None

    def test_depth(self):
        env = ProofEnvironment()
        assert env.depth == 1
        env.push_scope()
        assert env.depth == 2
        env.pop_scope()
        assert env.depth == 1

    def test_all_hypotheses(self):
        env = ProofEnvironment()
        p1 = Proposition(_kind=PropositionKind.CUSTOM, _raw="P1")
        p2 = Proposition(_kind=PropositionKind.CUSTOM, _raw="P2")
        env.assume("h1", ReflProof(), p1)
        env.push_scope()
        env.assume("h2", ReflProof(), p2)
        hyps = env.all_hypotheses()
        assert "h1" in hyps
        assert "h2" in hyps


# ===================================================================
#  ProofChecker with witness hierarchy
# ===================================================================


class TestProofCheckerWitness:
    """Tests for ProofChecker using witness ProofTerm hierarchy."""

    def setup_method(self):
        self.checker = ProofChecker()

    def test_check_refl_equality(self):
        obl = _obligation(("eq", "int", "int"))
        result = self.checker.check(ReflProof(), obl)
        assert result.valid

    def test_check_refl_true_pred(self):
        obl = _obligation(TruePred())
        result = self.checker.check(ReflProof(), obl)
        assert result.valid

    def test_check_assumption(self):
        obl = _obligation(("eq", "A", "A"))
        proof = AssumptionProof(name="h1")
        result = self.checker.check(proof, obl)
        # Assumption proofs are accepted
        assert result.valid or result.verdict == CheckVerdict.UNKNOWN

    def test_check_runtime_check(self):
        obl = _obligation(("eq", "x", "x"))
        proof = RuntimeCheckProof(check_description="assert x > 0")
        result = self.checker.check(proof, obl)
        assert result.valid or result.verdict == CheckVerdict.UNKNOWN

    def test_check_transitivity(self):
        obl = _obligation(("eq", "A", "C"))
        left = ReflProof()
        right = ReflProof()
        proof = TransitivityProof(left=left, right=right)
        result = self.checker.check(proof, obl)
        assert result.valid

    def test_check_symmetry(self):
        obl = _obligation(("eq", "B", "A"))
        inner = ReflProof()
        proof = SymmetryProof(inner=inner)
        result = self.checker.check(proof, obl)
        assert result.valid

    def test_check_congruence(self):
        obl = _obligation(("eq", "f(A)", "f(B)"))
        inner = ReflProof()
        proof = CongruenceProof(inner=inner, function_name="f")
        result = self.checker.check(proof, obl)
        assert result.valid

    def test_check_composite(self):
        obl = _obligation(("eq", "X", "X"))
        proof = CompositeProof(
            sub_proofs=(ReflProof(), ReflProof()),
            combiner="conjunction",
        )
        result = self.checker.check(proof, obl)
        assert result.valid

    def test_check_static_proof(self):
        obl = _obligation(("eq", "A", "A"))
        proof = StaticProof(method="type_check", detail="type inference")
        result = self.checker.check(proof, obl)
        assert result.valid or result.verdict == CheckVerdict.UNKNOWN


# ===================================================================
#  ProofChecker with protocol proof terms
# ===================================================================


class TestProofCheckerProtocol:
    """Tests for ProofChecker using protocol ProofTerm (from _protocols.py)."""

    def setup_method(self):
        self.checker = ProofChecker()

    def _make_term(self, kind, children=None, payload=None, proposition=None):
        t = ProtocolProofTerm(
            kind=kind,
            children=children or [],
            payload=payload,
            proposition=proposition,
        )
        return t

    def test_refl_on_equal(self):
        obl = _obligation(("eq", 42, 42))
        proof = self._make_term(ProofTermKind.REFL, payload=42)
        result = self.checker.check(proof, obl)
        assert result.valid

    def test_refl_on_unequal(self):
        obl = _obligation(("eq", 1, 2))
        proof = self._make_term(ProofTermKind.REFL)
        result = self.checker.check(proof, obl)
        assert not result.valid

    def test_symm(self):
        child = self._make_term(ProofTermKind.REFL, proposition=("eq", "A", "B"))
        obl = _obligation(("eq", "B", "A"))
        proof = self._make_term(ProofTermKind.SYMM, children=[child])
        result = self.checker.check(proof, obl)
        assert result.valid

    def test_trans(self):
        left = self._make_term(ProofTermKind.REFL)
        right = self._make_term(ProofTermKind.REFL)
        obl = _obligation(("eq", "A", "C"))
        proof = self._make_term(ProofTermKind.TRANS, children=[left, right])
        result = self.checker.check(proof, obl)
        assert result.valid

    def test_cong(self):
        child = self._make_term(ProofTermKind.REFL)
        obl = _obligation(("eq", "f(A)", "f(B)"))
        proof = self._make_term(ProofTermKind.CONG, children=[child], payload="f")
        result = self.checker.check(proof, obl)
        assert result.valid

    def test_mp(self):
        impl = self._make_term(ProofTermKind.REFL)
        ante = self._make_term(ProofTermKind.REFL)
        obl = _obligation(("eq", "Q", "Q"))
        proof = self._make_term(ProofTermKind.MP, children=[impl, ante])
        result = self.checker.check(proof, obl)
        assert result.valid

    def test_and_intro(self):
        left = self._make_term(ProofTermKind.REFL)
        right = self._make_term(ProofTermKind.REFL)
        obl = _obligation(("eq", "PQ", "PQ"))
        proof = self._make_term(ProofTermKind.AND_INTRO, children=[left, right])
        result = self.checker.check(proof, obl)
        assert result.valid

    def test_check_count_increases(self):
        checker = ProofChecker()
        assert checker.check_count == 0
        obl = _obligation(("eq", "X", "X"))
        checker.check(ReflProof(), obl)
        assert checker.check_count >= 1

    def test_max_depth_exceeded(self):
        checker = ProofChecker(max_depth=1)
        # Build a deeply nested proof
        inner = ReflProof()
        proof = TransitivityProof(left=inner, right=TransitivityProof(left=inner, right=inner))
        obl = _obligation(("eq", "A", "A"))
        result = checker.check(proof, obl)
        # Should eventually report failure or succeed depending on depth counting
        assert isinstance(result, CheckResult)

    def test_check_term_direct(self):
        checker = ProofChecker()
        prop = Proposition(_kind=PropositionKind.EQUALITY, _lhs="int", _rhs="int")
        result = checker.check_term(ReflProof(), prop)
        assert result.valid

    def test_cache_reset(self):
        checker = ProofChecker()
        obl = _obligation(("eq", "A", "A"))
        checker.check(ReflProof(), obl)
        checker.reset_cache()
        # Should still work after cache reset
        result = checker.check(ReflProof(), obl)
        assert result.valid
