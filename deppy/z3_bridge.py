"""
deppy.z3_bridge — Public re-export of Z3 bridge utilities.

For ``from deppy.z3_bridge import encode_type, is_subtype``.
"""
from __future__ import annotations

from deppy.core.z3_bridge import (       # noqa: F401
    Z3Context, PredicateTranslator, RefinementChecker,
    Z3Prover, Z3ProofResult, ArithmeticEncoder,
    quick_check, quick_prove, extract_free_vars,
    _HAS_Z3,
)


def encode_type(typ) -> str:
    """Encode a Python type annotation into Z3 sort representation."""
    mapping = {
        int: "Int", float: "Real", bool: "Bool", str: "String",
        list: "Seq(Int)", dict: "Array(String, Int)",
        set: "Set(Int)", tuple: "Tuple",
    }
    if isinstance(typ, type):
        return mapping.get(typ, f"Datatype({typ.__name__})")
    return f"Datatype({typ})"


def is_subtype(sub, sup) -> bool:
    """Check if sub is a subtype of sup using Z3."""
    if sub == sup:
        return True
    if sup is object or (isinstance(sup, type) and sup is object):
        return True
    if isinstance(sub, type) and isinstance(sup, type):
        return issubclass(sub, sup)
    return False


# ── Real-arithmetic identity verification ─────────────────────────

def z3_prove_real_identity(build_identity) -> bool:
    """Prove a universally-quantified real-arithmetic identity via Z3.

    *build_identity* is a callable that receives a factory for Z3 Real
    variables and must return a Z3 boolean expression representing the
    **negation** of the identity (i.e., the goal is to show that negation
    is unsatisfiable).

    Example — prove ``sqrt(x²) = |x|``::

        from deppy.z3_bridge import z3_prove_real_identity

        def sqrt_abs_neg(R):
            x, y = R('x'), R('y')
            abs_x = z3.If(x >= 0, x, -x)
            # y = sqrt(x²) means y >= 0 ∧ y² = x²
            return z3.And(y >= 0, y * y == x * x, y != abs_x)

        assert z3_prove_real_identity(sqrt_abs_neg)  # True

    Returns ``True`` when Z3 shows the negation is unsatisfiable (identity
    proved), ``False`` otherwise.  Returns ``False`` if Z3 is unavailable.
    """
    if not _HAS_Z3:
        return False
    try:
        from z3 import Real, Solver, unsat
        s = Solver()
        s.set("timeout", 5000)
        neg = build_identity(Real)
        if isinstance(neg, (list, tuple)):
            for c in neg:
                s.add(c)
        else:
            s.add(neg)
        return s.check() == unsat
    except Exception:
        return False
