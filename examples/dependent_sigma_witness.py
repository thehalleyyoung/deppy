"""Non-refinement dependent example: a Sigma-style witness/result pair.

This is here to show that DepPy's native-Python surface is not limited to
refinement predicates; it can carry richer dependent signatures too.
"""

@deppy.signature("(n : Nat) -> Vec(Int, n) -> (k : Nat) ** Vec(Int, k)")
def expose_length_and_values(xs):
    return xs
