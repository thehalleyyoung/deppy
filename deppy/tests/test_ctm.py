"""Tests for the deppy.core.ctm De Bruijn closure-body language and the
SynTerm ↔ CTm bridge.

These tests exercise the runtime mirror of the Lean metatheory's CTm
calculus from ``Deppy.lean §39-§50``.  Each test corresponds to a
property the Lean theorems prove (alpha-equivalence-is-syntactic,
substitution lemma, CBV determinism, beta-reduction sound).
"""
from __future__ import annotations

import pytest

from deppy.core.ctm import (
    CTm, BVar, FVar, CNat, CBool, CStr, App, Lam, Fix,
    TNat, TBool, TString, TArrow,
    lift, subst, is_value, cbv_step, beta_normalize, alpha_eq,
    free_vars, is_closed,
)
from deppy.core.ctm_bridge import (
    to_ctm, from_ctm, alpha_equivalent_syn, beta_normalize_syn,
)


# ═══════════════════════════════════════════════════════════════════
#  Value classification (mirrors CTm.isValue from Lean)
# ═══════════════════════════════════════════════════════════════════

def test_lambda_is_value():
    assert is_value(Lam(TNat(), BVar(0)))


def test_nat_is_value():
    assert is_value(CNat(42))


def test_bool_is_value():
    assert is_value(CBool(True))


def test_str_is_value():
    assert is_value(CStr("hello"))


def test_fvar_is_value():
    assert is_value(FVar("x"))


def test_app_is_not_value():
    assert not is_value(App(Lam(TNat(), BVar(0)), CNat(1)))


def test_fix_is_not_value():
    assert not is_value(Fix(Lam(TNat(), BVar(0))))


def test_bvar_is_not_value():
    assert not is_value(BVar(0))


# ═══════════════════════════════════════════════════════════════════
#  Lift (mirrors Lean ``CTm.lift``)
# ═══════════════════════════════════════════════════════════════════

def test_lift_bvar_below_cutoff_unchanged():
    assert lift(BVar(0), 1) == BVar(0)


def test_lift_bvar_at_cutoff_shifts_up():
    assert lift(BVar(1), 1) == BVar(2)


def test_lift_fvar_unchanged():
    assert lift(FVar("x"), 5) == FVar("x")


def test_lift_distributes_over_app():
    t = App(BVar(2), BVar(0))
    assert lift(t, 1) == App(BVar(3), BVar(0))


def test_lift_descends_under_lambda_with_cutoff_plus_one():
    # lambda body sees the inserted variable as one position deeper.
    t = Lam(TNat(), BVar(2))   # outer scope: BVar(1) becomes
    assert lift(t, 1) == Lam(TNat(), BVar(3))


def test_lift_distributes_over_fix():
    assert lift(Fix(BVar(0)), 0) == Fix(BVar(1))


# ═══════════════════════════════════════════════════════════════════
#  Substitution (mirrors Lean ``CTm.subst``)
# ═══════════════════════════════════════════════════════════════════

def test_subst_zero_bvar_zero_returns_substituent():
    # Lean: subst_zero_bvar_zero
    assert subst(BVar(0), CNat(42), 0) == CNat(42)


def test_subst_skip_bvar_zero_when_index_differs():
    assert subst(BVar(0), CNat(42), 1) == BVar(0)


def test_subst_decrements_above_target():
    # bvar 2 substituted at index 0 becomes bvar 1.
    assert subst(BVar(2), CNat(42), 0) == BVar(1)


def test_subst_lifts_substituent_under_lambda():
    # Substituting inside a lambda body: the substituent gets lifted
    # by 1 to account for the new binder.
    body = BVar(1)
    lam = Lam(TNat(), body)
    # subst(Lam T body, u, j) = Lam T (subst body (u.lift 0) (j+1))
    # Here body=BVar(1), u=FVar("x"), j=0.
    # So inner call: subst(BVar(1), FVar("x"), 1).
    # BVar(1).index == 1 == j, so substitute with u = FVar("x")
    # (lift on FVar is identity).
    result = subst(lam, FVar("x"), 0)
    assert result == Lam(TNat(), FVar("x"))


def test_subst_under_lambda_decrements_higher_bvar():
    # Body has BVar(2), substituent index j=0.  Inside lambda,
    # j becomes 1.  BVar(2) > 1, so it decrements to BVar(1).
    body = BVar(2)
    lam = Lam(TNat(), body)
    result = subst(lam, FVar("x"), 0)
    assert result == Lam(TNat(), BVar(1))


def test_subst_app_distributes():
    t = App(BVar(0), BVar(1))
    result = subst(t, CNat(7), 0)
    assert result == App(CNat(7), BVar(0))


# ═══════════════════════════════════════════════════════════════════
#  CBV step (mirrors Lean ``CBV``)
# ═══════════════════════════════════════════════════════════════════

def test_cbv_step_value_stays_none():
    assert cbv_step(CNat(42)) is None
    assert cbv_step(Lam(TNat(), BVar(0))) is None


def test_cbv_step_beta():
    # (λ x. x) 42 → 42
    identity = Lam(TNat(), BVar(0))
    redex = App(identity, CNat(42))
    assert cbv_step(redex) == CNat(42)


def test_cbv_step_const_function():
    # (λ x. λ y. x) 1 → λ y. 1
    const = Lam(TNat(), Lam(TNat(), BVar(1)))
    redex = App(const, CNat(1))
    # Substituting CNat(1) at index 0 in (Lam (BVar 1)):
    # → Lam (subst (BVar 1) (CNat 1).lift 0 1)
    # → Lam (CNat 1)  (since BVar 1 == j=1, substituent = CNat(1).lift(0) = CNat(1))
    expected = Lam(TNat(), CNat(1))
    assert cbv_step(redex) == expected


def test_cbv_step_fix_unfolds():
    # fix f → app f (fix f)
    f = Lam(TNat(), BVar(0))
    fx = Fix(f)
    assert cbv_step(fx) == App(f, fx)


def test_cbv_step_congruence_in_function():
    # (fix f) v → reduces fix first
    f = Lam(TNat(), BVar(0))
    fx = Fix(f)
    redex = App(fx, CNat(42))
    # Step: cong_app_l → app f' arg
    expected = App(App(f, fx), CNat(42))
    assert cbv_step(redex) == expected


def test_cbv_step_congruence_in_argument():
    # f (fix g)  with f a value (lambda) and (fix g) reduces
    f = Lam(TNat(), BVar(0))
    g = Lam(TNat(), BVar(0))
    fx = Fix(g)
    redex = App(f, fx)
    # f is a value → step in the arg.
    expected = App(f, App(g, fx))
    assert cbv_step(redex) == expected


def test_cbv_step_stuck_app_value_to_value_non_lam():
    # FVar applied to a value: stuck (no rule fires).
    redex = App(FVar("g"), CNat(42))
    assert cbv_step(redex) is None


# ═══════════════════════════════════════════════════════════════════
#  Beta-normalize iteration
# ═══════════════════════════════════════════════════════════════════

def test_beta_normalize_identity():
    redex = App(Lam(TNat(), BVar(0)), CNat(7))
    assert beta_normalize(redex) == CNat(7)


def test_beta_normalize_double_application():
    # ((λ x. λ y. x) 1) 2 → 1
    const = Lam(TNat(), Lam(TNat(), BVar(1)))
    redex = App(App(const, CNat(1)), CNat(2))
    assert beta_normalize(redex) == CNat(1)


def test_beta_normalize_budget_caps_runaway():
    # fix (λ f. f) — diverges under unconditional fix unfolding.
    diverge = Fix(Lam(TArrow(TNat(), TNat()), BVar(0)))
    result = beta_normalize(diverge, max_steps=5)
    # We just check we don't crash and we got something back.
    assert result is not None


# ═══════════════════════════════════════════════════════════════════
#  Free variables and closedness
# ═══════════════════════════════════════════════════════════════════

def test_free_vars_picks_up_fvar():
    assert free_vars(FVar("z")) == {"z"}


def test_free_vars_skips_bvar():
    assert free_vars(BVar(0)) == set()


def test_free_vars_under_lambda():
    # λ. x   has free var x (BVar 0 is bound, FVar x is free)
    t = Lam(TNat(), FVar("x"))
    assert free_vars(t) == {"x"}


def test_is_closed_lambda_with_only_bvar_zero():
    # λ. #0 — closed.
    t = Lam(TNat(), BVar(0))
    assert is_closed(t)


def test_is_closed_lambda_with_escaped_bvar_one():
    # λ. #1 — escapes; not closed.
    t = Lam(TNat(), BVar(1))
    assert not is_closed(t)


def test_is_closed_app_of_closed_terms():
    t = App(Lam(TNat(), BVar(0)), CNat(42))
    assert is_closed(t)


# ═══════════════════════════════════════════════════════════════════
#  α-equivalence
# ═══════════════════════════════════════════════════════════════════

def test_alpha_eq_via_de_bruijn_strips_param_names():
    # Two named lambdas λ x. x  and  λ y. y  encode to the same CTm.
    t1 = Lam(TNat(), BVar(0))
    t2 = Lam(TNat(), BVar(0))
    assert alpha_eq(t1, t2)


def test_alpha_inequality_when_structures_differ():
    t1 = Lam(TNat(), BVar(0))    # λ. #0
    t2 = Lam(TNat(), CNat(0))     # λ. 0
    assert not alpha_eq(t1, t2)


# ═══════════════════════════════════════════════════════════════════
#  Bridge: SynTerm  →  CTm
# ═══════════════════════════════════════════════════════════════════

def test_bridge_named_var_to_fvar():
    from deppy.core.types import Var
    assert to_ctm(Var("x")) == FVar("x")


def test_bridge_named_lambda_id_to_bvar_zero():
    from deppy.core.types import Var, Lam as SynLam, PyIntType
    syn = SynLam(param="x", param_type=PyIntType(), body=Var("x"))
    expected = Lam(TNat(), BVar(0))
    assert to_ctm(syn) == expected


def test_bridge_named_const_function():
    # λ x. λ y. x   →   Lam (Lam (BVar 1))
    from deppy.core.types import Var, Lam as SynLam, PyIntType
    inner = SynLam(param="y", param_type=PyIntType(), body=Var("x"))
    outer = SynLam(param="x", param_type=PyIntType(), body=inner)
    expected = Lam(TNat(), Lam(TNat(), BVar(1)))
    assert to_ctm(outer) == expected


def test_bridge_app_distributes():
    from deppy.core.types import Var, App as SynApp, Lam as SynLam, PyIntType
    syn = SynApp(
        func=SynLam(param="x", param_type=PyIntType(), body=Var("x")),
        arg=Var("y"),
    )
    expected = App(Lam(TNat(), BVar(0)), FVar("y"))
    assert to_ctm(syn) == expected


def test_bridge_literal_int_to_cnat():
    from deppy.core.types import Literal, PyIntType
    assert to_ctm(Literal(value=42, type_=PyIntType())) == CNat(42)


def test_bridge_literal_bool_to_cbool():
    from deppy.core.types import Literal, PyBoolType
    assert to_ctm(Literal(value=True, type_=PyBoolType())) == CBool(True)


def test_bridge_literal_str_to_cstr():
    from deppy.core.types import Literal, PyStrType
    assert to_ctm(Literal(value="hi", type_=PyStrType())) == CStr("hi")


# ═══════════════════════════════════════════════════════════════════
#  Bridge: CTm  →  SynTerm  →  α-equivalence round-trip
# ═══════════════════════════════════════════════════════════════════

def test_round_trip_preserves_structure_for_lambda_id():
    from deppy.core.types import Var, Lam as SynLam, PyIntType
    syn_in = SynLam(param="x", param_type=PyIntType(), body=Var("x"))
    ctm = to_ctm(syn_in)
    syn_out = from_ctm(ctm)
    # Round-trip through De Bruijn collapses α-equivalence.  The
    # parameter name may differ but the structure is identical.
    assert isinstance(syn_out, SynLam)
    assert isinstance(syn_out.body, Var)
    # Names match because our fresh-name pool starts with "x".
    assert syn_out.param == syn_out.body.name


def test_round_trip_through_de_bruijn_proves_alpha_equivalence():
    from deppy.core.types import Var, Lam as SynLam, PyIntType
    a = SynLam(param="x", param_type=PyIntType(), body=Var("x"))
    b = SynLam(param="y", param_type=PyIntType(), body=Var("y"))
    # Different param names, same structure → α-equivalent.
    assert alpha_equivalent_syn(a, b)


def test_alpha_inequivalent_when_body_differs():
    from deppy.core.types import Var, Lam as SynLam, PyIntType
    a = SynLam(param="x", param_type=PyIntType(), body=Var("x"))
    b = SynLam(param="x", param_type=PyIntType(), body=Var("y"))
    # Same param name, different body — a is identity, b is constant.
    assert not alpha_equivalent_syn(a, b)


# ═══════════════════════════════════════════════════════════════════
#  Bridge: end-to-end β reduction via the De Bruijn engine
# ═══════════════════════════════════════════════════════════════════

def test_beta_normalize_syn_identity():
    from deppy.core.types import (
        Var, Literal, Lam as SynLam, App as SynApp,
        PyIntType,
    )
    syn = SynApp(
        func=SynLam(param="x", param_type=PyIntType(), body=Var("x")),
        arg=Literal(value=42, type_=PyIntType()),
    )
    result = beta_normalize_syn(syn)
    assert isinstance(result, Literal)
    assert result.value == 42


def test_beta_normalize_syn_const():
    # ((λ x. λ y. x) 1) 2 → 1
    from deppy.core.types import (
        Var, Literal, Lam as SynLam, App as SynApp,
        PyIntType,
    )
    inner = SynLam(param="y", param_type=PyIntType(), body=Var("x"))
    const = SynLam(param="x", param_type=PyIntType(), body=inner)
    redex = SynApp(
        func=SynApp(func=const, arg=Literal(value=1, type_=PyIntType())),
        arg=Literal(value=2, type_=PyIntType()),
    )
    result = beta_normalize_syn(redex)
    assert isinstance(result, Literal)
    assert result.value == 1
