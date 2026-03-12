"""Long-form capability audit for DepPy's automatic semantic typing.

The point of this file is not just to provide another small demo; it is to
exercise several distinct capabilities and limitations in one ordinary PyTorch
program:

1. automatic return-type refinement from `torch.sort`
2. automatic semantic goals such as `sorted(result)`, `perm(result, scores)`,
   and `argsort(result, scores)`
3. interprocedural propagation through direct-return wrappers
4. automatic shape and indexing theory activation for `view`, scalar indexing,
   and slicing
5. synthesized user-facing `@deppy.ensures(...)` annotations from optimized
   frontiers
6. regression cases that used to fail but now preserve semantics through local
   alias wrappers and nested theory-triggering expressions
7. static detection of a real values-vs-indices bug

This is intentionally longer than the earlier showcase so the tests can audit
what DepPy can infer, synthesize, optimize, and now preserve across alias-heavy
ordinary code.
"""

import torch


def rank_scores(scores):
    values, _indices = torch.sort(scores, dim=-1)
    return values


def rank_indices(scores):
    _values, indices = torch.sort(scores, dim=-1)
    return indices


def direct_rank(scores):
    return rank_scores(scores)


def direct_rank_indices(scores):
    return rank_indices(scores)


def serving_rank(scores):
    return direct_rank(scores)


def serving_rank_indices(scores):
    return direct_rank_indices(scores)


def local_rank(scores):
    ranked = rank_scores(scores)
    return ranked


def local_rank_indices(scores):
    idx = rank_indices(scores)
    return idx


def flatten_supported(scores):
    ranked = serving_rank(scores)
    flat = ranked.view(-1)
    return flat


def flatten_nested(scores):
    return serving_rank(scores).view(-1)


def head_score(scores):
    flat = flatten_supported(scores)
    return flat[0]


def head_window(scores):
    flat = flatten_supported(scores)
    return flat[:4]


def argsort_head(scores):
    idx = serving_rank_indices(scores)
    flat_idx = idx.view(-1)
    return flat_idx[0]


def branch_mix_bug(scores, debug_indices):
    payload = rank_scores(scores)
    if debug_indices:
        payload = rank_indices(scores)
    return payload
