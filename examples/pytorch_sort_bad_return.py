"""TensorGuard-style PyTorch sorting example with an obvious type bug.

The dependent signature says the result should be a vector with the same
length as the input, but the implementation returns a string.
"""
import torch
import torch.nn as nn


class BuggySortingModule(nn.Module):
    @deppy.guarantee({
        "parameters": [{"name": "xs", "type": "Vec(Int, n)"}],
        "return": "Vec(Int, n)",
        "signature": "(n : Nat) -> (xs : Vec(Int, n)) -> Vec(Int, n)",
        "proof_goals": ["sorted(result)", "perm(result, xs)"],
        "postconditions": ["len(result) >= 0"]
    })
    def forward(self, xs):
        values, _indices = torch.sort(xs, dim=-1)
        _ = values
        return "not-a-vector"
