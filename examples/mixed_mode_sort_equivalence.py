"""Benchmark paired proof-explicit and code-inferred sort implementations."""
import torch


@deppy.guarantee({
    "parameters": [{"name": "xs", "type": "Vec(Int, n)"}],
    "return": "Vec(Int, n)",
    "signature": "(n : Nat) -> (xs : Vec(Int, n)) -> Vec(Int, n)",
    "proof_goals": ["sorted(result)", "perm(result, xs)"],
    "postconditions": ["len(result) >= 0"],
})
def explicit_sorted_values(xs):
    values, _indices = torch.sort(xs, dim=-1)
    return values


def inferred_sorted_values(xs):
    values, _indices = torch.sort(xs, dim=-1)
    return values
