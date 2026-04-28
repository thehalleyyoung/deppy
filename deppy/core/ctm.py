"""
deppy.core.ctm — Python mirror of the Lean ``CTm`` calculus from
``metatheory/Deppy.lean §39``.

This module is the *runtime* counterpart to the Lean metatheory's
closure-body language.  By representing closures as ``CTm`` instances
on the Python side, we can:

  1. Run β-reduction on closures structurally (no opaque ``Closure``).
  2. Compute α-equivalence as syntactic equality (a property the Lean
     theorem ``alpha_equiv_is_syntactic_eq`` proves).
  3. Round-trip closures through Lean export with the metatheory's
     theorems (``soundness_rich'``, ``richobj'_cl_inj``, etc.) directly
     applicable.

The mirror is faithful: every Python ``CTm`` constructor maps to a
Lean ``CTm`` constructor with the same name and arity.  Substitution
and lifting follow the same De Bruijn arithmetic as
``CTm.lift`` / ``CTm.subst`` in the Lean file.

Public surface::

    class CTm                # the De Bruijn ADT (frozen dataclass)
    class CTy                # type universe (matches Lean §39)
    def lift(t, c)           # CTm.lift c t  in Lean
    def subst(t, u, j)       # t.subst u j  in Lean
    def is_value(t)          # CTm.isValue
    def cbv_step(t)          # CBV one-step; None for stuck/value
    def beta_normalize(t, *, max_steps=1000)
                             # iterate cbv_step until value or budget
    def alpha_eq(a, b)       # syntactic equality on De Bruijn (= ==)
    def free_vars(t)         # the set of fvar names appearing free

The companion module ``deppy.core.ctm_bridge`` provides
``to_ctm(syn_term)`` and ``from_ctm(ctm)`` for the
``deppy.core.types.SynTerm`` (named-variable) representation used
elsewhere in the kernel.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Union


# ───────────────────────────────────────────────────────────────────
#  Types (mirrors Lean ``CTy``)
# ───────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class CTy:
    """Base class for closure-body types.  Instantiated as one of
    ``TNat``, ``TBool``, ``TString``, ``TArrow``."""

    def __repr__(self) -> str:  # pragma: no cover - cosmetic
        return self.render()

    def render(self) -> str:
        raise NotImplementedError


@dataclass(frozen=True)
class TNat(CTy):
    def render(self) -> str:
        return "Int"


@dataclass(frozen=True)
class TBool(CTy):
    def render(self) -> str:
        return "Bool"


@dataclass(frozen=True)
class TString(CTy):
    def render(self) -> str:
        return "String"


@dataclass(frozen=True)
class TArrow(CTy):
    """``T → U`` — function type."""
    domain: CTy
    codomain: CTy

    def render(self) -> str:
        return f"({self.domain.render()} → {self.codomain.render()})"


# ───────────────────────────────────────────────────────────────────
#  Terms (mirrors Lean ``CTm``)
# ───────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class CTm:
    """Base class for closure-body terms.  Instantiated as one of
    ``BVar``, ``FVar``, ``Nat``, ``Bool``, ``Str``, ``App``, ``Lam``,
    ``Fix``."""

    def __repr__(self) -> str:  # pragma: no cover - cosmetic
        return self.render()

    def render(self) -> str:
        raise NotImplementedError

    def is_value(self) -> bool:
        """Mirrors Lean ``CTm.isValue``: lambdas, primitives, free
        variables are values; bvars / app / fix are not."""
        return False


@dataclass(frozen=True)
class BVar(CTm):
    """De Bruijn-indexed bound variable."""
    index: int

    def render(self) -> str:
        return f"#{self.index}"


@dataclass(frozen=True)
class FVar(CTm):
    """Free name (resolved in the surrounding lexical scope; treated
    as a value during reduction, matching Lean's ``CTm.isValue``
    classification of ``fvar``)."""
    name: str

    def render(self) -> str:
        return self.name

    def is_value(self) -> bool:
        return True


@dataclass(frozen=True)
class CNat(CTm):
    """Integer literal."""
    value: int

    def render(self) -> str:
        return str(self.value)

    def is_value(self) -> bool:
        return True


@dataclass(frozen=True)
class CBool(CTm):
    """Boolean literal."""
    value: bool

    def render(self) -> str:
        return str(self.value)

    def is_value(self) -> bool:
        return True


@dataclass(frozen=True)
class CStr(CTm):
    """String literal."""
    value: str

    def render(self) -> str:
        return repr(self.value)

    def is_value(self) -> bool:
        return True


@dataclass(frozen=True)
class App(CTm):
    """Function application ``f a``."""
    func: CTm
    arg: CTm

    def render(self) -> str:
        return f"({self.func.render()} {self.arg.render()})"


@dataclass(frozen=True)
class Lam(CTm):
    """Lambda abstraction ``λ (x : T). body``.

    Body uses ``BVar(0)`` to refer to the bound parameter and
    ``BVar(n+1)`` to refer to the n-th outer binder.  This mirrors
    Lean's ``CTm.lam : CTy → CTm → CTm`` constructor exactly.
    """
    param_type: CTy
    body: CTm

    def render(self) -> str:
        return f"(λ {self.param_type.render()}. {self.body.render()})"

    def is_value(self) -> bool:
        return True


@dataclass(frozen=True)
class Fix(CTm):
    """Recursive fixed-point ``fix f``.  Reduction rule:
    ``fix f → app f (fix f)``.  Mirrors Lean's ``CTm.fix``."""
    func: CTm

    def render(self) -> str:
        return f"(fix {self.func.render()})"


# ───────────────────────────────────────────────────────────────────
#  Lift and substitution (mirrors Lean ``CTm.lift`` / ``CTm.subst``)
# ───────────────────────────────────────────────────────────────────

def lift(t: CTm, cutoff: int = 0) -> CTm:
    """Shift every bound-variable index ≥ ``cutoff`` in ``t`` up by 1.

    Used when descending into a binder during substitution.  This is
    the Python translation of the Lean definition::

        def CTm.lift : CTm → Nat → CTm
          | .bvar i,      c => if i < c then .bvar i else .bvar (i + 1)
          | .fvar s,      _ => .fvar s
          | …

    The translation is purely structural; ``frozen=True`` dataclasses
    make the result hashable.
    """
    if isinstance(t, BVar):
        return BVar(t.index) if t.index < cutoff else BVar(t.index + 1)
    if isinstance(t, (FVar, CNat, CBool, CStr)):
        return t
    if isinstance(t, App):
        return App(lift(t.func, cutoff), lift(t.arg, cutoff))
    if isinstance(t, Lam):
        return Lam(t.param_type, lift(t.body, cutoff + 1))
    if isinstance(t, Fix):
        return Fix(lift(t.func, cutoff))
    raise TypeError(f"unknown CTm node: {type(t).__name__}")


def subst(t: CTm, u: CTm, j: int) -> CTm:
    """Substitute ``u`` for the bound variable indexed by ``j`` in ``t``.

    Indices above ``j`` are decremented by 1 (collapsing the now-removed
    binder slot).  When recursing under a ``Lam``, the substituent is
    lifted by 1 to account for the added binder.

    Mirrors Lean's::

        def CTm.subst : CTm → CTm → Nat → CTm
          | .bvar i, u, j =>
              if i = j then u
              else if i > j then .bvar (i - 1)
              else .bvar i
          | .lam T body, u, j =>
              .lam T (body.subst (u.lift 0) (j + 1))
          | …
    """
    if isinstance(t, BVar):
        if t.index == j:
            return u
        if t.index > j:
            return BVar(t.index - 1)
        return BVar(t.index)
    if isinstance(t, (FVar, CNat, CBool, CStr)):
        return t
    if isinstance(t, App):
        return App(subst(t.func, u, j), subst(t.arg, u, j))
    if isinstance(t, Lam):
        return Lam(t.param_type, subst(t.body, lift(u, 0), j + 1))
    if isinstance(t, Fix):
        return Fix(subst(t.func, u, j))
    raise TypeError(f"unknown CTm node: {type(t).__name__}")


# ───────────────────────────────────────────────────────────────────
#  Reduction (mirrors Lean ``CBV``)
# ───────────────────────────────────────────────────────────────────

def is_value(t: CTm) -> bool:
    """Forward to ``t.is_value()``.  Mirrors ``CTm.isValue`` from Lean."""
    return t.is_value()


def cbv_step(t: CTm) -> Optional[CTm]:
    """Take one call-by-value reduction step, or return ``None`` if
    ``t`` is a value or stuck.

    Mirrors Lean's ``CBV`` inductive relation:

      * ``app (lam T body) v → body[v/0]`` (when v is a value)
      * ``fix f → app f (fix f)``
      * ``app f a → app f' a``  if ``f → f'``
      * ``app v a → app v a'``  if v value, ``a → a'``

    Determinism is proved in Lean as ``cbv_deterministic``.  The
    Python implementation follows the same constructor priority.
    """
    if t.is_value():
        return None
    if isinstance(t, BVar):
        # bvars are stuck — well-typed closed terms shouldn't have free
        # bvars at the top level.
        return None
    if isinstance(t, Fix):
        # fix f → app f (fix f) — unconditional unfolding (matches Lean
        # CBV after dropping the ambiguous cong_fix rule).
        return App(t.func, t)
    if isinstance(t, App):
        # 1. Try f → f' (cong_app_l).
        f_step = cbv_step(t.func)
        if f_step is not None:
            return App(f_step, t.arg)
        # 2. f is a value.  Try a → a' (cong_app_r).
        a_step = cbv_step(t.arg)
        if a_step is not None:
            return App(t.func, a_step)
        # 3. Both are values.  If f is a lambda, fire β.
        if isinstance(t.func, Lam) and t.arg.is_value():
            return subst(t.func.body, t.arg, 0)
        # 4. f is a non-lambda value (FVar, primitive) applied to a
        #    value — stuck.
        return None
    return None


def beta_normalize(t: CTm, *, max_steps: int = 1000) -> CTm:
    """Iterate ``cbv_step`` until the term is a value or stuck, or
    until ``max_steps`` steps have been taken.

    Returns the (possibly partial) reduct.  The step budget guards
    against ``fix`` recursion in untyped or ill-typed terms (Python
    being Turing-complete by design — termination isn't guaranteed).
    """
    cur = t
    for _ in range(max_steps):
        nxt = cbv_step(cur)
        if nxt is None:
            return cur
        cur = nxt
    return cur


# ───────────────────────────────────────────────────────────────────
#  Equivalence and free variables
# ───────────────────────────────────────────────────────────────────

def alpha_eq(a: CTm, b: CTm) -> bool:
    """α-equivalence on De Bruijn-encoded terms.  Per the Lean theorem
    ``alpha_equiv_is_syntactic_eq``, this is just structural equality.
    The frozen-dataclass ``__eq__`` does the right thing."""
    return a == b


def free_vars(t: CTm) -> set[str]:
    """Return the set of ``FVar`` names appearing in ``t``.  ``BVar``
    indices are *bound* and don't appear in this set; ``FVar`` names
    are free (resolved in surrounding scope)."""
    if isinstance(t, FVar):
        return {t.name}
    if isinstance(t, (BVar, CNat, CBool, CStr)):
        return set()
    if isinstance(t, App):
        return free_vars(t.func) | free_vars(t.arg)
    if isinstance(t, Lam):
        return free_vars(t.body)
    if isinstance(t, Fix):
        return free_vars(t.func)
    return set()


def is_closed(t: CTm) -> bool:
    """A term is *closed* when no bvar escapes its binders.  We check
    by walking the term and tracking the depth of enclosing binders;
    every ``BVar(i)`` must have ``i < depth`` at its position."""
    def walk(node: CTm, depth: int) -> bool:
        if isinstance(node, BVar):
            return node.index < depth
        if isinstance(node, (FVar, CNat, CBool, CStr)):
            return True
        if isinstance(node, App):
            return walk(node.func, depth) and walk(node.arg, depth)
        if isinstance(node, Lam):
            return walk(node.body, depth + 1)
        if isinstance(node, Fix):
            return walk(node.func, depth)
        return False
    return walk(t, 0)


__all__ = [
    "CTy", "TNat", "TBool", "TString", "TArrow",
    "CTm", "BVar", "FVar", "CNat", "CBool", "CStr", "App", "Lam", "Fix",
    "lift", "subst",
    "is_value", "cbv_step", "beta_normalize",
    "alpha_eq", "free_vars", "is_closed",
]
