"""
synhopy.z3_bridge — Public re-export of Z3 bridge utilities.

For ``from synhopy.z3_bridge import encode_type, is_subtype``.
"""
from __future__ import annotations

from synhopy.core.z3_bridge import (       # noqa: F401
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
