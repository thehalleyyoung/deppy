"""Tests for witness combinators: transitivity, symmetry, congruence, etc.

Covers TransitivityWitness, SymmetryWitness, CongruenceWitness,
ExistentialPackWitness, UniversalWitness, PairWitness, ProjectionWitness,
ModusPonensWitness, and the composition/simplification functions.
"""

from __future__ import annotations

import pytest

from deppy.types.base import ANY_TYPE, AnyType
from deppy.types.witnesses import (
    AssumptionProof,
    CompositeProof,
    CongruenceProof,
    ProofTerm,
    ReflProof,
    SymmetryProof,
    TransitivityProof,
)
from deppy.proof.witness_combinators import (
    AbsurdityWitness,
    CaseAnalysisWitness,
    CongruenceWitness,
    ExistentialPackWitness,
    LeftInjectionWitness,
    ModusPonensWitness,
    PairWitness,
    ProjectionWitness,
    RightInjectionWitness,
    SymmetryWitness,
    TransitivityWitness,
    TransportProofWitness,
    UniversalWitness,
    compose_symmetry,
    compose_transitivity,
    lift_congruence,
    lift_congruence_multi,
    make_absurdity,
    make_case_analysis,
    make_existential,
    make_left_injection,
    make_modus_ponens,
    make_right_injection,
    make_transport,
    make_universal,
    pack_witness,
    proof_size,
    simplify_proof,
    unpack_witness,
)


# ===================================================================
#  TransitivityWitness
# ===================================================================


class TestTransitivityWitness:
    """Tests for TransitivityWitness."""

    def test_basic(self):
        p1 = AssumptionProof(name="ab")
        p2 = AssumptionProof(name="bc")
        tw = TransitivityWitness(_left=p1, _right=p2)
        assert tw.left is p1
        assert tw.right is p2
        assert len(tw.chain) == 2

    def test_description(self):
        tw = TransitivityWitness(
            _left=AssumptionProof(name="h1"),
            _right=AssumptionProof(name="h2"),
        )
        desc = tw.description()
        assert "trans" in desc

    def test_extend(self):
        p1 = AssumptionProof(name="ab")
        p2 = AssumptionProof(name="bc")
        tw = TransitivityWitness(_left=p1, _right=p2)
        p3 = AssumptionProof(name="cd")
        extended = tw.extend(p3)
        assert len(extended.chain) == 3

    def test_to_transitivity_proof(self):
        p1 = ReflProof()
        p2 = ReflProof()
        tw = TransitivityWitness(_left=p1, _right=p2)
        tp = tw.to_transitivity_proof()
        assert isinstance(tp, TransitivityProof)


# ===================================================================
#  SymmetryWitness
# ===================================================================


class TestSymmetryWitness:
    """Tests for SymmetryWitness."""

    def test_basic(self):
        inner = AssumptionProof(name="ab")
        sw = SymmetryWitness(_inner=inner)
        assert sw.inner is inner

    def test_description(self):
        sw = SymmetryWitness(_inner=ReflProof())
        assert "sym" in sw.description()

    def test_double_negate(self):
        inner = AssumptionProof(name="p")
        sw1 = SymmetryWitness(_inner=inner)
        sw2 = SymmetryWitness(_inner=sw1)
        result = sw2.double_negate()
        assert result is inner

    def test_double_negate_base_symmetry(self):
        inner = AssumptionProof(name="p")
        sp = SymmetryProof(inner=inner)
        sw = SymmetryWitness(_inner=sp)
        result = sw.double_negate()
        assert result is inner

    def test_to_symmetry_proof(self):
        sw = SymmetryWitness(_inner=ReflProof())
        sp = sw.to_symmetry_proof()
        assert isinstance(sp, SymmetryProof)


# ===================================================================
#  CongruenceWitness
# ===================================================================


class TestCongruenceWitness:
    """Tests for CongruenceWitness."""

    def test_basic(self):
        inner = AssumptionProof(name="ab")
        cw = CongruenceWitness(_inner=inner, _function_name="f")
        assert cw.inner is inner
        assert cw.function_name == "f"

    def test_description(self):
        cw = CongruenceWitness(_inner=ReflProof(), _function_name="len")
        assert "cong" in cw.description()
        assert "len" in cw.description()

    def test_compose_congruence(self):
        cw = CongruenceWitness(_inner=ReflProof(), _function_name="f")
        composed = cw.compose_congruence("g")
        assert "g(f)" in composed.function_name

    def test_to_congruence_proof(self):
        cw = CongruenceWitness(_inner=ReflProof(), _function_name="h")
        cp = cw.to_congruence_proof()
        assert isinstance(cp, CongruenceProof)
        assert cp.function_name == "h"


# ===================================================================
#  compose_transitivity / compose_symmetry / lift_congruence
# ===================================================================


class TestCompositionFunctions:
    """Tests for the composition helper functions."""

    def test_compose_trans_refl_left(self):
        p = AssumptionProof(name="ab")
        result = compose_transitivity(ReflProof(), p)
        assert result is p

    def test_compose_trans_refl_right(self):
        p = AssumptionProof(name="ab")
        result = compose_transitivity(p, ReflProof())
        assert result is p

    def test_compose_trans_both_refl(self):
        result = compose_transitivity(ReflProof(), ReflProof())
        assert isinstance(result, ReflProof)

    def test_compose_trans_normal(self):
        p1 = AssumptionProof(name="ab")
        p2 = AssumptionProof(name="bc")
        result = compose_transitivity(p1, p2)
        assert isinstance(result, TransitivityWitness)

    def test_compose_trans_flattens(self):
        p1 = AssumptionProof(name="ab")
        p2 = AssumptionProof(name="bc")
        p3 = AssumptionProof(name="cd")
        tw = TransitivityWitness(_left=p1, _right=p2)
        result = compose_transitivity(tw, p3)
        assert isinstance(result, TransitivityWitness)
        assert len(result.chain) == 3

    def test_compose_sym_refl(self):
        result = compose_symmetry(ReflProof())
        assert isinstance(result, ReflProof)

    def test_compose_sym_normal(self):
        p = AssumptionProof(name="ab")
        result = compose_symmetry(p)
        assert isinstance(result, SymmetryWitness)

    def test_compose_sym_double(self):
        p = AssumptionProof(name="ab")
        s1 = compose_symmetry(p)
        s2 = compose_symmetry(s1)
        assert s2 is p

    def test_lift_congruence_refl(self):
        result = lift_congruence(ReflProof(), "f")
        assert isinstance(result, ReflProof)

    def test_lift_congruence_normal(self):
        p = AssumptionProof(name="ab")
        result = lift_congruence(p, "f")
        assert isinstance(result, CongruenceWitness)

    def test_lift_congruence_multi_all_refl(self):
        result = lift_congruence_multi([ReflProof(), ReflProof()], "f")
        assert isinstance(result, ReflProof)

    def test_lift_congruence_multi_one(self):
        p = AssumptionProof(name="ab")
        result = lift_congruence_multi([p], "f")
        assert isinstance(result, CongruenceWitness)


# ===================================================================
#  PairWitness / ProjectionWitness / pack / unpack
# ===================================================================


class TestPairAndPacking:
    """Tests for pairing, projection, packing, and unpacking."""

    def test_pair_witness(self):
        p1 = AssumptionProof(name="P")
        p2 = AssumptionProof(name="Q")
        pw = PairWitness(_first=p1, _second=p2)
        assert pw.fst() is p1
        assert pw.snd() is p2

    def test_pair_to_composite(self):
        pw = PairWitness(_first=ReflProof(), _second=ReflProof())
        cp = pw.to_composite_proof()
        assert isinstance(cp, CompositeProof)

    def test_projection_resolve(self):
        pw = PairWitness(_first=ReflProof(), _second=AssumptionProof(name="Q"))
        proj0 = ProjectionWitness(_pair=pw, _index=0)
        assert isinstance(proj0.resolve(), ReflProof)
        proj1 = ProjectionWitness(_pair=pw, _index=1)
        assert isinstance(proj1.resolve(), AssumptionProof)

    def test_pack_empty(self):
        result = pack_witness([])
        assert isinstance(result, ReflProof)

    def test_pack_one(self):
        p = AssumptionProof(name="h")
        result = pack_witness([p])
        assert result is p

    def test_pack_two(self):
        p1 = AssumptionProof(name="P")
        p2 = AssumptionProof(name="Q")
        result = pack_witness([p1, p2])
        assert isinstance(result, PairWitness)

    def test_pack_three(self):
        proofs = [AssumptionProof(name=f"h{i}") for i in range(3)]
        result = pack_witness(proofs)
        assert isinstance(result, PairWitness)

    def test_unpack_roundtrip(self):
        proofs = [AssumptionProof(name=f"h{i}") for i in range(3)]
        packed = pack_witness(proofs)
        unpacked = unpack_witness(packed, 3)
        assert len(unpacked) == 3
        for orig, unp in zip(proofs, unpacked):
            assert orig.description() == unp.description()


# ===================================================================
#  ModusPonens / Existential / Universal / etc.
# ===================================================================


class TestAdvancedCombinators:
    """Tests for modus ponens, existential, universal, and other combinators."""

    def test_modus_ponens(self):
        result = make_modus_ponens(ReflProof(), AssumptionProof(name="P"))
        assert isinstance(result, ModusPonensWitness)
        assert "mp" in result.description()

    def test_universal(self):
        result = make_universal("x", ANY_TYPE, ReflProof())
        assert isinstance(result, UniversalWitness)
        assert result.binder_name == "x"

    def test_universal_instantiate(self):
        uw = UniversalWitness(_binder_name="x", _body_proof=ReflProof())
        inst = uw.instantiate(42)
        assert "42" in inst.description()

    def test_existential(self):
        result = make_existential("x", 42, ANY_TYPE, ReflProof())
        assert isinstance(result, ExistentialPackWitness)
        assert result.witness_term == 42

    def test_case_analysis(self):
        result = make_case_analysis(ReflProof(), ReflProof(), ReflProof())
        assert isinstance(result, CaseAnalysisWitness)

    def test_absurdity(self):
        result = make_absurdity(ReflProof())
        assert isinstance(result, AbsurdityWitness)

    def test_transport(self):
        result = make_transport(ReflProof(), source_type=ANY_TYPE)
        assert isinstance(result, TransportProofWitness)

    def test_left_injection(self):
        result = make_left_injection(ReflProof())
        assert isinstance(result, LeftInjectionWitness)

    def test_right_injection(self):
        result = make_right_injection(ReflProof())
        assert isinstance(result, RightInjectionWitness)


# ===================================================================
#  simplify_proof / proof_size
# ===================================================================


class TestSimplifyAndSize:
    """Tests for proof simplification and size calculation."""

    def test_simplify_sym_sym(self):
        inner = AssumptionProof(name="ab")
        double_sym = SymmetryWitness(_inner=SymmetryWitness(_inner=inner))
        result = simplify_proof(double_sym)
        assert result.description() == inner.description()

    def test_simplify_trans_refl_left(self):
        p = AssumptionProof(name="ab")
        tw = TransitivityWitness(_left=ReflProof(), _right=p)
        result = simplify_proof(tw)
        assert result.description() == p.description()

    def test_simplify_cong_refl(self):
        cw = CongruenceWitness(_inner=ReflProof(), _function_name="f")
        result = simplify_proof(cw)
        assert isinstance(result, ReflProof)

    def test_simplify_projection(self):
        pw = PairWitness(_first=AssumptionProof(name="A"), _second=AssumptionProof(name="B"))
        proj = ProjectionWitness(_pair=pw, _index=0)
        result = simplify_proof(proj)
        assert result.description() == "assume(A, assumed)"

    def test_proof_size_refl(self):
        assert proof_size(ReflProof()) == 1

    def test_proof_size_assumption(self):
        assert proof_size(AssumptionProof(name="h")) == 1

    def test_proof_size_pair(self):
        pw = PairWitness(_first=ReflProof(), _second=ReflProof())
        assert proof_size(pw) == 3

    def test_proof_size_transitivity(self):
        tw = TransitivityWitness(
            _left=AssumptionProof(name="ab"),
            _right=AssumptionProof(name="bc"),
        )
        assert proof_size(tw) == 3

    def test_proof_size_congruence(self):
        cw = CongruenceWitness(_inner=AssumptionProof(name="ab"), _function_name="f")
        assert proof_size(cw) == 2

    def test_proof_size_modus_ponens(self):
        mp = ModusPonensWitness(
            _implication=ReflProof(), _antecedent=AssumptionProof(name="P"),
        )
        assert proof_size(mp) == 3
