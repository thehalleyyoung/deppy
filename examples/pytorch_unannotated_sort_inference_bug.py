"""Unannotated PyTorch example that goes beyond TensorGuard-style shape checking.

DepPy should infer sorted-value semantics for `infer_sorted_values` and then
statically reject the buggy function for mixing sorted values with sort indices.
"""
import torch


def infer_sorted_values(xs):
    values, _indices = torch.sort(xs, dim=-1)
    return values


def buggy_sort_or_indices(xs, take_indices):
    values, indices = torch.sort(xs, dim=-1)
    result = values
    if take_indices:
        result = indices
    return result
