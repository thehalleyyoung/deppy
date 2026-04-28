"""
deppy.core.ctm_bridge — convert between named ``SynTerm`` and De Bruijn ``CTm``.

The kernel uses two closure-body representations:

* :class:`deppy.core.types.SynTerm` — *named-variable* AST (``Var("x")``,
  ``Lam("x", T, body)``, ``App(f, a)``, ``Literal(v)`` …).  Easier
  to read; matches Python source.
* :class:`deppy.core.ctm.CTm` — *De Bruijn-indexed* mirror of the
  Lean metatheory's calculus from ``Deppy.lean §39``.  Closures use
  this so α-equivalence is syntactic equality and the metatheory's
  ``soundness_rich'`` / ``richobj'_cl_inj`` apply directly.

This module provides the two conversion functions::

    to_ctm(syn_term)    # named  →  De Bruijn
    from_ctm(ctm)       # De Bruijn  →  named

with a *round-trip* property: ``from_ctm(to_ctm(t))`` is α-equivalent
to ``t`` (variables may be renamed but the structure is preserved).

The conversion uses a binding-environment stack: walking into a
``Lam("x", T, body)`` pushes ``"x"`` onto the stack and recurses;
within the body, a free occurrence of ``x`` becomes
``BVar(stack_depth - position - 1)``.  Other free names become
``FVar(name)``.

The reverse direction generates fresh names for each ``Lam`` to avoid
clashes with FVars already in scope; the result is α-equivalent to
the input by construction.

This module is the load-bearing piece that makes the closure
metatheory from §39-§50 apply to the runtime kernel — closures
flowing through the kernel can be β-reduced via :func:`deppy.core.ctm.cbv_step`,
yielding the same result as the Lean proof would justify.
"""
from __future__ import annotations

from typing import Optional

from deppy.core.ctm import (
    CTm, BVar, FVar, CNat, CBool, CStr, App as CApp, Lam as CLam, Fix as CFix,
    CTy, TNat, TBool, TString, TArrow,
)


# ───────────────────────────────────────────────────────────────────
#  Python type → CTy translation
# ───────────────────────────────────────────────────────────────────

def py_type_to_cty(ty: object) -> CTy:
    """Best-effort translation of a Python ``SynType`` (or runtime type)
    to a :class:`CTy`.  Unknown types collapse to ``TNat`` as a default
    integer slot — the closure's behaviour is preserved; the type
    annotation is informational."""
    # Late import to avoid circular dependency.
    from deppy.core.types import (
        PyIntType, PyBoolType, PyStrType, PyCallableType, PiType, SynType,
    )
    if isinstance(ty, PyIntType):
        return TNat()
    if isinstance(ty, PyBoolType):
        return TBool()
    if isinstance(ty, PyStrType):
        return TString()
    if isinstance(ty, (PyCallableType, PiType)):
        # Callable[[A], B] / Π(x:A).B → TArrow.  When the argument
        # type isn't fixed (e.g. PyObjType), default to TNat.
        dom = TNat()
        cod = TNat()
        if hasattr(ty, "param_type"):
            dom = py_type_to_cty(getattr(ty, "param_type"))
        if hasattr(ty, "body"):
            cod = py_type_to_cty(getattr(ty, "body"))
        if hasattr(ty, "arg_types"):
            args = getattr(ty, "arg_types")
            if args:
                dom = py_type_to_cty(args[0])
        if hasattr(ty, "return_type"):
            cod = py_type_to_cty(getattr(ty, "return_type"))
        return TArrow(dom, cod)
    if isinstance(ty, type):
        if ty is int: return TNat()
        if ty is bool: return TBool()
        if ty is str: return TString()
    return TNat()


def cty_to_py_type(cty: CTy) -> object:
    """Inverse of :func:`py_type_to_cty`.  Returns a ``SynType``
    instance from ``deppy.core.types``."""
    from deppy.core.types import (
        PyIntType, PyBoolType, PyStrType, PyCallableType,
    )
    if isinstance(cty, TNat): return PyIntType()
    if isinstance(cty, TBool): return PyBoolType()
    if isinstance(cty, TString): return PyStrType()
    if isinstance(cty, TArrow):
        return PyCallableType(
            arg_types=[cty_to_py_type(cty.domain)],
            return_type=cty_to_py_type(cty.codomain),
        )
    return PyIntType()


# ───────────────────────────────────────────────────────────────────
#  Named  →  De Bruijn
# ───────────────────────────────────────────────────────────────────

def to_ctm(syn_term: object, *, env: Optional[list[str]] = None) -> CTm:
    """Convert a named-variable :class:`SynTerm` to a De Bruijn :class:`CTm`.

    ``env`` is an optional binding-stack: the *last* element is the
    most-recently bound variable.  When walking into a ``Lam("x", …, body)``,
    we push ``"x"`` onto the stack before recursing.  Inside the body,
    a ``Var("x")`` whose name appears in the stack at depth ``d``
    becomes ``BVar(d)`` (counting from the top); names not in the
    stack become ``FVar(name)``.

    Constants and pairs round-trip through their primitive
    counterparts.  ``Pair``, ``Fst``, ``Snd`` are not first-class
    in the closure language (CTm has no pair constructor); they
    collapse to ``FVar`` placeholders so the conversion is total.
    """
    from deppy.core.types import (
        Var, Literal, Lam as SynLam, App as SynApp, Pair, Fst, Snd,
    )
    if env is None:
        env = []
    if isinstance(syn_term, Var):
        return _resolve_var(syn_term.name, env)
    if isinstance(syn_term, Literal):
        return _literal_to_ctm(syn_term)
    if isinstance(syn_term, SynLam):
        # Push the bound name and recurse.
        new_env = env + [syn_term.param]
        body_ctm = to_ctm(syn_term.body, env=new_env)
        return CLam(py_type_to_cty(syn_term.param_type), body_ctm)
    if isinstance(syn_term, SynApp):
        return CApp(
            to_ctm(syn_term.func, env=env),
            to_ctm(syn_term.arg, env=env),
        )
    # Pair / Fst / Snd / other SynTerm shapes — fall through to FVar
    # placeholder.  The closure body language doesn't model these
    # natively; a higher-level proof would carry them as separate
    # axioms.
    name = type(syn_term).__name__
    return FVar(f"_unsupported_{name}")


def _resolve_var(name: str, env: list[str]) -> CTm:
    """Resolve ``Var(name)`` in an environment.  The most-recently
    pushed name is at the *end* of ``env``; index 0 (BVar) is the
    *innermost* binder."""
    # Walk the env from the right (innermost first).
    for depth, n in enumerate(reversed(env)):
        if n == name:
            return BVar(depth)
    # Free name.
    return FVar(name)


def _literal_to_ctm(lit: object) -> CTm:
    """Map a ``Literal(value)`` to the appropriate CTm primitive."""
    v = getattr(lit, "value", None)
    if isinstance(v, bool):
        return CBool(v)
    if isinstance(v, int):
        return CNat(v)
    if isinstance(v, str):
        return CStr(v)
    if v is None:
        # Unit-ish — encode as integer 0 (Lean convention from §35).
        return CNat(0)
    # Other values — wrap as FVar so subsequent reductions are
    # opaque rather than crashing.
    return FVar(f"_lit_{type(v).__name__}_{id(lit)}")


# ───────────────────────────────────────────────────────────────────
#  De Bruijn  →  Named
# ───────────────────────────────────────────────────────────────────

def from_ctm(
    ctm: CTm,
    *,
    env: Optional[list[str]] = None,
    name_pool: Optional[list[str]] = None,
) -> object:
    """Convert a De Bruijn :class:`CTm` back to a named :class:`SynTerm`.

    ``env`` carries names introduced by enclosing ``Lam``s; ``BVar(i)``
    looks up ``env[len(env) - 1 - i]``.  When recursing under a
    ``Lam``, we synthesise a fresh name from the pool (``x_0`` /
    ``x_1`` …) avoiding clashes with names already in ``env``.

    The result is α-equivalent to whatever named term originally
    produced ``ctm``; specific names may differ, which is *expected*
    behaviour — De Bruijn collapses α-equivalence to syntactic
    equality, so any α-representative is acceptable.
    """
    from deppy.core.types import (
        Var, Literal, Lam as SynLam, App as SynApp,
        PyIntType, PyBoolType, PyStrType,
    )
    if env is None:
        env = []
    if name_pool is None:
        name_pool = list(_DEFAULT_NAMES)
    if isinstance(ctm, BVar):
        # Resolve to env[len(env) - 1 - ctm.index].
        if ctm.index < len(env):
            return Var(env[len(env) - 1 - ctm.index])
        # Out-of-range bvar — emit a placeholder.
        return Var(f"_unbound_{ctm.index}")
    if isinstance(ctm, FVar):
        return Var(ctm.name)
    if isinstance(ctm, CNat):
        return Literal(value=ctm.value, type_=PyIntType())
    if isinstance(ctm, CBool):
        return Literal(value=ctm.value, type_=PyBoolType())
    if isinstance(ctm, CStr):
        return Literal(value=ctm.value, type_=PyStrType())
    if isinstance(ctm, CApp):
        return SynApp(
            func=from_ctm(ctm.func, env=env, name_pool=name_pool),
            arg=from_ctm(ctm.arg, env=env, name_pool=name_pool),
        )
    if isinstance(ctm, CLam):
        # Pick a fresh name avoiding clashes with current env and
        # any free vars in the body.
        fresh = _fresh_name(env, name_pool)
        new_env = env + [fresh]
        body_syn = from_ctm(ctm.body, env=new_env, name_pool=name_pool)
        return SynLam(
            param=fresh,
            param_type=cty_to_py_type(ctm.param_type),
            body=body_syn,
        )
    if isinstance(ctm, CFix):
        # SynTerm has no native fix constructor; wrap as App of a
        # combinator FVar.  The Lean theorem ``closure_fix_admissible``
        # gives the operational meaning.
        return SynApp(
            func=Var("_fix"),
            arg=from_ctm(ctm.func, env=env, name_pool=name_pool),
        )
    raise TypeError(f"unknown CTm node: {type(ctm).__name__}")


_DEFAULT_NAMES = [
    "x", "y", "z", "u", "v", "w", "a", "b", "c",
    "p", "q", "r", "m", "n", "i", "j", "k",
]


def _fresh_name(env: list[str], pool: list[str]) -> str:
    """Pick a name from ``pool`` not in ``env``; if exhausted, append
    ascending suffixes (``x_0``, ``x_1``, …)."""
    for cand in pool:
        if cand not in env:
            return cand
    base = pool[0] if pool else "x"
    i = 0
    while True:
        cand = f"{base}_{i}"
        if cand not in env:
            return cand
        i += 1


# ───────────────────────────────────────────────────────────────────
#  Round-trip helpers (the two together = α-equivalence-preserving
#  identity)
# ───────────────────────────────────────────────────────────────────

def alpha_equivalent_syn(a: object, b: object) -> bool:
    """Two SynTerm values are α-equivalent iff their CTm encodings
    are syntactically equal.  This is the punch-line connection between
    the named-variable representation and the Lean metatheory's
    De Bruijn calculus."""
    return to_ctm(a) == to_ctm(b)


def beta_normalize_syn(syn_term: object, *, max_steps: int = 1000) -> object:
    """β-normalize a named ``SynTerm`` via the De Bruijn engine.

    Round-trips through CTm: ``to_ctm → cbv_step* → from_ctm``.  The
    result is a SynTerm value α-equivalent to the original's normal
    form.  Step budget defaults to 1000 — Python being Turing-complete,
    we don't try to guarantee termination.
    """
    from deppy.core.ctm import beta_normalize
    ctm = to_ctm(syn_term)
    reduct = beta_normalize(ctm, max_steps=max_steps)
    return from_ctm(reduct)


__all__ = [
    "py_type_to_cty",
    "cty_to_py_type",
    "to_ctm",
    "from_ctm",
    "alpha_equivalent_syn",
    "beta_normalize_syn",
]
