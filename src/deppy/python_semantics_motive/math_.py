"""Interpretation of Python math module in the motive framework."""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

MATH_OPS = {
    # Basic arithmetic
    'ceil': ('Num.ceil', (Sort.NUM,), Sort.NUM, frozenset({Refinement.IDEMPOTENT}), Effect.PURE),
    'floor': ('Num.floor', (Sort.NUM,), Sort.NUM, frozenset({Refinement.IDEMPOTENT}), Effect.PURE),
    'trunc': ('Num.trunc', (Sort.NUM,), Sort.NUM, frozenset({Refinement.IDEMPOTENT}), Effect.PURE),
    'fabs': ('Num.abs', (Sort.NUM,), Sort.NUM, frozenset({Refinement.IDEMPOTENT}), Effect.PURE),
    'factorial': ('Num.factorial', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'gcd': ('Num.gcd', (Sort.NUM, Sort.NUM), Sort.NUM,
            frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'lcm': ('Num.lcm', (Sort.NUM, Sort.NUM), Sort.NUM,
            frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'comb': ('Num.comb', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'perm': ('Num.perm', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'copysign': ('Num.copysign', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'fmod': ('Num.fmod', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'remainder': ('Num.remainder', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'fsum': ('Accum.sum', (Sort.ITER,), Sort.NUM,
             frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'prod': ('Accum.product', (Sort.ITER,), Sort.NUM,
             frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'isqrt': ('Num.isqrt', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),

    # Power and logarithmic
    'exp': ('Num.exp', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'exp2': ('Num.exp', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'expm1': ('Num.exp', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'log': ('Num.log', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'log2': ('Num.log', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'log10': ('Num.log', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'log1p': ('Num.log', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'pow': ('Num.pow', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'sqrt': ('Num.sqrt', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),

    # Trigonometric
    'sin': ('Num.trig', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'cos': ('Num.trig', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'tan': ('Num.trig', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'asin': ('Num.trig_inv', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'acos': ('Num.trig_inv', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'atan': ('Num.trig_inv', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'atan2': ('Num.trig_inv', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'sinh': ('Num.trig_hyp', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'cosh': ('Num.trig_hyp', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'tanh': ('Num.trig_hyp', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'asinh': ('Num.trig_hyp_inv', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'acosh': ('Num.trig_hyp_inv', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'atanh': ('Num.trig_hyp_inv', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'hypot': ('Num.hypot', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'dist': ('Num.dist', (Sort.SEQ, Sort.SEQ), Sort.NUM, frozenset(), Effect.PURE),

    # Angular conversion
    'degrees': ('Num.degrees', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'radians': ('Num.radians', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),

    # Special functions
    'gamma': ('Num.gamma', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'lgamma': ('Num.lgamma', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'erf': ('Num.erf', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
    'erfc': ('Num.erfc', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),

    # Classification
    'isnan': ('Num.isnan', (Sort.NUM,), Sort.BOOL, frozenset(), Effect.PURE),
    'isinf': ('Num.isinf', (Sort.NUM,), Sort.BOOL, frozenset(), Effect.PURE),
    'isfinite': ('Num.isfinite', (Sort.NUM,), Sort.BOOL, frozenset(), Effect.PURE),
    'isclose': ('Num.isclose', (Sort.NUM, Sort.NUM), Sort.BOOL,
                frozenset({Refinement.COMMUTATIVE}), Effect.PURE),

    # Representation
    'frexp': ('Num.frexp', (Sort.NUM,), Sort.SEQ, frozenset(), Effect.PURE),
    'ldexp': ('Num.ldexp', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'modf': ('Num.modf', (Sort.NUM,), Sort.SEQ, frozenset(), Effect.PURE),
    'nextafter': ('Num.nextafter', (Sort.NUM, Sort.NUM), Sort.NUM, frozenset(), Effect.PURE),
    'ulp': ('Num.ulp', (Sort.NUM,), Sort.NUM, frozenset(), Effect.PURE),
}

# Constants
MATH_CONSTANTS = {
    'pi': Sort.NUM,
    'e': Sort.NUM,
    'tau': Sort.NUM,
    'inf': Sort.NUM,
    'nan': Sort.NUM,
}
