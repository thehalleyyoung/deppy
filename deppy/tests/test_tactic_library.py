"""Tests for the reusable tactic library at
:mod:`deppy.proofs.tactic_library`.

The library provides four closed-form tactics — ``induction_on_list``,
``well_founded_on_len``, ``equational_chain``, ``transport_along`` —
each producing a kernel ProofTerm.  The PSDL ``assert P, "by <name>"``
syntax dispatches through :func:`tactic_library.invoke_by_name`.

Test coverage
-------------
* Each tactic invoked directly produces a non-trivial ProofTerm of
  the expected shape.
* Each tactic is reachable via ``compile_psdl`` and lands in the
  expected ``Cut`` body.
* Edge cases: empty equational chain, single-element chain,
  identity transport (``x = y`` syntactically).
* Regression: existing ``"by lemma X"`` and ``"by foundation X"``
  syntaxes still work.
"""
from __future__ import annotations

import pytest

from deppy.core.kernel import (
    ProofTerm,
    Refl, Cut, ListInduction, NatInduction,
    PathComp, TransportProof, AxiomInvocation, Structural,
)
from deppy.core.types import Var, Literal
from deppy.proofs.tactic_library import (
    induction_on_list,
    well_founded_on_len,
    equational_chain,
    transport_along,
    TACTIC_REGISTRY,
    is_tactic,
    invoke_by_name,
)
from deppy.proofs.psdl import compile_psdl


# ─────────────────────────────────────────────────────────────────────
#  Direct invocation: the four tactics produce the right ProofTerm
# ─────────────────────────────────────────────────────────────────────


class TestDirectInvocation:
    def test_induction_on_list_returns_ListInduction(self):
        pt = induction_on_list(
            xs="xs",
            base=Refl(Var("nil")),
            step=Refl(Var("cons")),
        )
        assert isinstance(pt, ListInduction)
        assert pt.var == "xs"
        # The base/step proofs flow through unchanged.
        assert isinstance(pt.nil_proof, Refl)
        assert isinstance(pt.cons_proof, Refl)

    def test_induction_on_list_wraps_string_obligations(self):
        # When the caller passes raw strings, they get lifted to
        # Structural placeholders — and the result is still a
        # well-formed ListInduction.
        pt = induction_on_list(
            xs="lst", base="empty case", step="cons case",
        )
        assert isinstance(pt, ListInduction)
        assert isinstance(pt.nil_proof, Structural)
        assert isinstance(pt.cons_proof, Structural)
        assert "empty" in pt.nil_proof.description

    def test_well_founded_on_len_returns_Cut_around_NatInduction(self):
        pt = well_founded_on_len(xs="xs", P="P xs")
        # The well-foundedness obligation lives on the outer Cut.
        assert isinstance(pt, Cut)
        assert "decreases" in pt.hyp_type.predicate
        # The inner body carries a NatInduction on len(xs).
        assert isinstance(pt.body_proof, NatInduction)
        assert pt.body_proof.var.startswith("len_")

    def test_equational_chain_three_steps_returns_PathComp(self):
        # a = b = c = d  →  ((p_ab · p_bc) · p_cd)
        pt = equational_chain(["a", "b", "c", "d"])
        assert isinstance(pt, PathComp)
        # The leftmost subtree is itself a PathComp (left-assoc).
        assert isinstance(pt.left_path, PathComp)
        # The innermost leaves are Refl placeholders.
        innermost = pt.left_path.left_path
        assert isinstance(innermost, Refl)

    def test_transport_along_returns_TransportProof(self):
        pt = transport_along(eq="path_eq", P="P", x="a", y="b")
        assert isinstance(pt, TransportProof)
        # The type family / path / base proof slots are all populated.
        assert pt.type_family is not None
        assert isinstance(pt.path_proof, ProofTerm)
        assert isinstance(pt.base_proof, ProofTerm)


# ─────────────────────────────────────────────────────────────────────
#  Edge cases
# ─────────────────────────────────────────────────────────────────────


class TestEdgeCases:
    def test_equational_chain_empty_returns_Structural(self):
        pt = equational_chain([])
        assert isinstance(pt, Structural)
        assert "empty" in pt.description.lower()

    def test_equational_chain_singleton_returns_Refl(self):
        # A length-1 chain ``[a]`` is the degenerate proof a = a.
        pt = equational_chain(["lonely"])
        assert isinstance(pt, Refl)

    def test_equational_chain_two_elements_returns_single_Refl_step(self):
        # Two-element chain produces a single Refl step (no PathComp
        # composition is needed).
        pt = equational_chain(["a", "b"])
        assert isinstance(pt, Refl)

    def test_transport_along_identity_short_circuits_to_Refl(self):
        # When x and y are syntactically equal, transp(P, refl, d) ≡ d
        # collapses to Refl.
        pt = transport_along(eq="any", P="P", x="x", y="x")
        assert isinstance(pt, Refl)

    def test_induction_on_list_with_SynTerm_xs(self):
        # The xs argument may be a SynTerm (Var) — the tactic should
        # extract the variable name.
        pt = induction_on_list(
            xs=Var("nums"),
            base=Refl(Var("base")),
            step=Refl(Var("step")),
        )
        assert isinstance(pt, ListInduction)
        assert pt.var == "nums"


# ─────────────────────────────────────────────────────────────────────
#  Registry & dispatcher API
# ─────────────────────────────────────────────────────────────────────


class TestRegistry:
    def test_registry_contains_all_four_tactics(self):
        assert set(TACTIC_REGISTRY.keys()) == {
            "induction_on_list",
            "well_founded_on_len",
            "equational_chain",
            "transport_along",
        }

    def test_is_tactic_true_for_registered_names(self):
        assert is_tactic("induction_on_list")
        assert is_tactic("well_founded_on_len")
        assert is_tactic("equational_chain")
        assert is_tactic("transport_along")

    def test_is_tactic_false_for_unknown(self):
        assert not is_tactic("foundation")
        assert not is_tactic("MyLemma")
        assert not is_tactic("")
        assert not is_tactic("induction_on_nat")  # close, but not registered

    def test_invoke_by_name_dispatches_to_each_tactic(self):
        ind = invoke_by_name("induction_on_list", claim="P xs")
        assert isinstance(ind, ListInduction)

        wf = invoke_by_name("well_founded_on_len", claim="P xs")
        assert isinstance(wf, Cut)

        eq = invoke_by_name("equational_chain", claim="a = c")
        assert isinstance(eq, PathComp)

        tr = invoke_by_name("transport_along", claim="P y")
        assert isinstance(tr, TransportProof)

    def test_invoke_by_name_unknown_raises_KeyError(self):
        with pytest.raises(KeyError):
            invoke_by_name("not_a_real_tactic")


# ─────────────────────────────────────────────────────────────────────
#  PSDL integration: ``assert P, "by <name>"`` compiles correctly
# ─────────────────────────────────────────────────────────────────────


def _compile(src: str, **kwargs):
    """Helper: compile a PSDL fragment, asserting no errors."""
    res = compile_psdl(src, **kwargs)
    assert res.errors == [], f"unexpected errors: {res.errors}"
    return res


def _find_tactic_proof(pt: ProofTerm) -> ProofTerm:
    """Walk down a Cut chain to find the first non-Cut/Refl payload.

    The PSDL compiler chains every assert into a ``Cut`` whose
    lemma_proof is the discharge.  We dig past any wrapping Cut
    layers to find the actual tactic-built ProofTerm.
    """
    seen = []
    cur = pt
    while isinstance(cur, Cut):
        seen.append(cur.lemma_proof)
        cur = cur.body_proof
    # Return the first non-trivial lemma in the chain.
    for lp in seen:
        if not isinstance(lp, Refl):
            return lp
    return seen[0] if seen else pt


class TestPSDLDispatch:
    def test_assert_by_induction_on_list(self):
        src = (
            "def f(xs: list):\n"
            "    assert len(xs) >= 0, 'by induction_on_list'\n"
        )
        res = _compile(src)
        inner = _find_tactic_proof(res.proof_term)
        assert isinstance(inner, ListInduction), (
            f"expected ListInduction, got {type(inner).__name__}: {inner}"
        )

    def test_assert_by_well_founded_on_len(self):
        src = (
            "def f(xs: list):\n"
            "    assert len(xs) >= 0, 'by well_founded_on_len'\n"
        )
        res = _compile(src)
        inner = _find_tactic_proof(res.proof_term)
        # The outer is a Cut wrapping a NatInduction.
        assert isinstance(inner, Cut)
        assert isinstance(inner.body_proof, NatInduction)

    def test_assert_by_equational_chain(self):
        src = (
            "def f(a: int, b: int):\n"
            "    assert a == b, 'by equational_chain'\n"
        )
        res = _compile(src)
        inner = _find_tactic_proof(res.proof_term)
        assert isinstance(inner, PathComp)

    def test_assert_by_transport_along(self):
        src = (
            "def f(x: int, y: int):\n"
            "    assert x == y, 'by transport_along'\n"
        )
        res = _compile(src)
        inner = _find_tactic_proof(res.proof_term)
        assert isinstance(inner, TransportProof)


# ─────────────────────────────────────────────────────────────────────
#  Backwards compatibility: existing dispatch modes still work
# ─────────────────────────────────────────────────────────────────────


class TestBackwardCompat:
    def test_by_foundation_X_still_works(self):
        src = (
            "def f(x: int):\n"
            "    assert x > 0, 'by foundation MyAx'\n"
        )
        res = _compile(src, foundations={"MyAx": object()})
        # A foundation citation should *not* land in the tactic
        # library — it should still produce an AxiomInvocation.
        inner = _find_tactic_proof(res.proof_term)
        assert isinstance(inner, AxiomInvocation), (
            f"foundation cite regressed into {type(inner).__name__}"
        )

    def test_by_lemma_X_still_works(self):
        src = (
            "def f(x: int):\n"
            "    assert x > 0, 'by lemma my_lemma'\n"
        )
        res = _compile(src)
        inner = _find_tactic_proof(res.proof_term)
        assert isinstance(inner, AxiomInvocation)
        # The lemma branch sets module="" (vs. "foundations").
        assert inner.module == ""

    def test_bare_assert_still_dispatches_to_z3(self):
        src = (
            "def f(x: int):\n"
            "    assert x > 0\n"
        )
        res = _compile(src)
        # Bare assert should still go through the Z3 branch (its
        # lemma_proof is a Z3Proof, not a tactic).
        from deppy.core.kernel import Z3Proof
        inner = _find_tactic_proof(res.proof_term)
        assert isinstance(inner, Z3Proof)

    def test_assert_with_qed_closer_still_works(self):
        src = (
            "def f(x: int):\n"
            "    assert x > 0, 'qed'\n"
        )
        res = _compile(src)
        # qed mode still produces a Cut with a Refl-wrapping
        # closer placeholder.
        assert res.proof_term is not None
        assert isinstance(res.proof_term, Cut)
