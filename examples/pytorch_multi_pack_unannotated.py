"""Unannotated PyTorch benchmark exercising the decomposed semantic theory packs."""
import torch


def sort_values(xs):
    values, _indices = torch.sort(xs, dim=-1)
    return values


def flatten_view(xs):
    reshaped = xs.view(-1)
    return reshaped


def take_first(xs):
    first = xs[0]
    return first
