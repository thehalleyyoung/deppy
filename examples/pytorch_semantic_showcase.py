"""Optimization-based semantic typing showcase for ordinary PyTorch code.

This example is intentionally close to what a regular user or an LLM might
write without any semantic annotations:

- `infer_ranked_scores` obtains sorted values from `torch.sort`.
- `canonicalize_ranked_scores` and `serving_ranked_scores` are plain wrappers.
- `flatten_serving_scores` and `top1_score` layer shape and indexing behavior
  on top of the ranking pipeline.
- `buggy_debug_payload` contains a latent bug: it sometimes returns sort
  indices where the value pipeline expects sorted values.

DepPy's monograph pipeline should:
- infer `sorted(result)` / `perm(result, scores)` for the ranking helpers,
- propagate those facts interprocedurally across the wrapper chain,
- activate shape and indexing theories for the downstream helpers,
- and statically flag the values-versus-indices bug.
"""

import torch


def infer_ranked_scores(scores):
    values, _indices = torch.sort(scores, dim=-1)
    return values


def canonicalize_ranked_scores(scores):
    return infer_ranked_scores(scores)


def serving_ranked_scores(scores):
    return canonicalize_ranked_scores(scores)


def flatten_serving_scores(scores):
    ranked = serving_ranked_scores(scores)
    return ranked.view(-1)


def top1_score(scores):
    flat = flatten_serving_scores(scores)
    return flat[0]


def buggy_debug_payload(scores, include_indices):
    values, indices = torch.sort(scores, dim=-1)
    payload = values
    if include_indices:
        payload = indices
    return payload
