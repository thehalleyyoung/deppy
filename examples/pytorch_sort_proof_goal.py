"""TensorGuard-style PyTorch sorting example with dependent proof goals.

This is shaped like the local TensorGuard nn.Module examples, but the
correctness condition is stronger than a plain shape/type check: the output
should be sorted and be a permutation of the input.
"""
import torch
import torch.nn as nn


class SortingModule(nn.Module):
    @deppy.guarantee({
        "parameters": [{"name": "xs", "type": "Vec(Int, n)"}],
        "return": "Vec(Int, n)",
        "signature": "(n : Nat) -> (xs : Vec(Int, n)) -> Vec(Int, n)",
        "proof_goals": ["sorted(result)", "perm(result, xs)"],
        "postconditions": ["len(result) >= 0"]
    })
    def forward(self, xs):
        values, _indices = torch.sort(xs, dim=-1)
        return values
