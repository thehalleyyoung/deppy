"""Hard equivalence benchmark suite: 50 equivalent + 50 non-equivalent pairs.

This suite packages the repository's existing hard equivalence corpus into the
same source-string format used by the benchmark harnesses.
"""

from __future__ import annotations

import importlib.util
import inspect
import textwrap
from pathlib import Path
from types import ModuleType

ROOT = Path(__file__).resolve().parent.parent
HARD_PAIR_PATH = ROOT / "tests" / "test_equivalence" / "test_hard_eq_pairs.py"

IMPORT_PREAMBLE = textwrap.dedent(
    """\
    from __future__ import annotations

    import bisect
    import collections
    import contextlib
    import copy
    import functools
    import hashlib
    import heapq
    import io
    import itertools
    import math
    import operator
    import re
    import struct
    import sys
    import textwrap
    import typing
    from collections import Counter, OrderedDict, defaultdict, deque
    from functools import partial, reduce
    from itertools import accumulate, chain, combinations, groupby, product
    """
)


def _load_hard_module() -> ModuleType:
    spec = importlib.util.spec_from_file_location("deppy_hard_eq_pairs", HARD_PAIR_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Unable to load hard pair module from {HARD_PAIR_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_HARD = _load_hard_module()


def _source_of(fn: object) -> str:
    return IMPORT_PREAMBLE + "\n\n" + textwrap.dedent(inspect.getsource(fn))


def _manual_source(source: str) -> str:
    return IMPORT_PREAMBLE + "\n\n" + textwrap.dedent(source)


EQ_BENCHMARKS: list[tuple[str, str, str, bool]] = [
    (
        f"hard_eq_{idx:02d}_{func_a.__name__}_vs_{func_b.__name__}",
        _source_of(func_a),
        _source_of(func_b),
        True,
    )
    for idx, (func_a, func_b, _arg_sets) in enumerate(_HARD.EQ_PAIRS, start=1)
]


NEQ_BENCHMARKS: list[tuple[str, str, str, bool]] = [
    (
        f"hard_neq_{idx:02d}_{func_a.__name__}_vs_{func_b.__name__}",
        _source_of(func_a),
        _source_of(func_b),
        False,
    )
    for idx, (func_a, func_b, _witness_args, _description) in enumerate(
        _HARD.NEQ_PAIRS,
        start=1,
    )
]


NEQ_BENCHMARKS.extend(
    [
        (
            "hard_neq_45_neq07a_vs_neq07b",
            _source_of(_HARD.neq07a),
            _source_of(_HARD.neq07b),
            False,
        ),
        (
            "hard_neq_46_neq13a_vs_neq13b",
            _source_of(_HARD.neq13a),
            _source_of(_HARD.neq13b),
            False,
        ),
        (
            "hard_neq_47_neq24a_vs_neq24b",
            _source_of(_HARD.neq24a),
            _source_of(_HARD.neq24b),
            False,
        ),
        (
            "hard_neq_48_neq46a_vs_neq46b",
            _source_of(_HARD.neq46a),
            _source_of(_HARD.neq46b),
            False,
        ),
        (
            "hard_neq_49_neq48a_vs_neq48b",
            _source_of(_HARD.neq48a),
            _source_of(_HARD.neq48b),
            False,
        ),
        (
            "hard_neq_50_generator_reuse_vs_materialization",
            _manual_source(
                """\
                def f(data):
                    gen = (x * x for x in data)
                    total = sum(gen)
                    return total, list(gen)
                """
            ),
            _manual_source(
                """\
                def g(data):
                    items = [x * x for x in data]
                    total = sum(items)
                    return total, list(items)
                """
            ),
            False,
        ),
    ]
)


EQUIV_PAIRS: list[tuple[str, str, str, bool]] = EQ_BENCHMARKS + NEQ_BENCHMARKS

assert len(EQ_BENCHMARKS) == 50, f"Expected 50 equivalent pairs, got {len(EQ_BENCHMARKS)}"
assert len(NEQ_BENCHMARKS) == 50, f"Expected 50 non-equivalent pairs, got {len(NEQ_BENCHMARKS)}"
assert len(EQUIV_PAIRS) == 100, f"Expected 100 hard pairs, got {len(EQUIV_PAIRS)}"
assert len({name for name, _, _, _ in EQUIV_PAIRS}) == 100, "Benchmark names must be unique"
