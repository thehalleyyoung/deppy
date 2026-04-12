"""Interpretation of Python's builtin functions in the motive framework.

Every builtin function (len, sorted, sum, min, max, ...) is mapped to a
TypedOp specification: (op_name, result_sort, refinements, effect).
"""

from __future__ import annotations

from typing import FrozenSet, Tuple

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement


# ── Builtin function → result Sort ──────────────────────────────

BUILTIN_FUNC_SORTS = {
    # Constructors
    'int': Sort.NUM,
    'float': Sort.NUM,
    'complex': Sort.NUM,
    'bool': Sort.BOOL,
    'str': Sort.STR,
    'bytes': Sort.STR,
    'bytearray': Sort.STR,
    'list': Sort.SEQ,
    'tuple': Sort.SEQ,
    'dict': Sort.MAP,
    'set': Sort.SET,
    'frozenset': Sort.SET,
    'range': Sort.SEQ,
    'memoryview': Sort.SEQ,
    'slice': Sort.TOP,
    'type': Sort.FUNC,
    'object': Sort.TOP,
    'property': Sort.FUNC,
    'staticmethod': Sort.FUNC,
    'classmethod': Sort.FUNC,
    'super': Sort.TOP,

    # Numeric functions
    'abs': Sort.NUM,
    'divmod': Sort.SEQ,
    'pow': Sort.NUM,
    'round': Sort.NUM,
    'bin': Sort.STR,
    'oct': Sort.STR,
    'hex': Sort.STR,

    # Sequence operations
    'len': Sort.NUM,
    'sorted': Sort.SEQ,
    'reversed': Sort.ITER,
    'enumerate': Sort.ITER,
    'zip': Sort.ITER,
    'map': Sort.ITER,
    'filter': Sort.ITER,
    'iter': Sort.ITER,
    'next': Sort.TOP,

    # Reduction functions
    'sum': Sort.NUM,
    'min': Sort.TOP,
    'max': Sort.TOP,
    'any': Sort.BOOL,
    'all': Sort.BOOL,

    # String/repr
    'repr': Sort.STR,
    'ascii': Sort.STR,
    'chr': Sort.STR,
    'ord': Sort.NUM,
    'format': Sort.STR,

    # Type checking
    'isinstance': Sort.BOOL,
    'issubclass': Sort.BOOL,
    'callable': Sort.BOOL,
    'hasattr': Sort.BOOL,
    'getattr': Sort.TOP,
    'setattr': Sort.NONE,
    'delattr': Sort.NONE,

    # Object identity
    'id': Sort.NUM,
    'hash': Sort.NUM,

    # I/O
    'print': Sort.NONE,
    'input': Sort.STR,
    'open': Sort.TOP,

    # Introspection
    'dir': Sort.SEQ,
    'vars': Sort.MAP,
    'globals': Sort.MAP,
    'locals': Sort.MAP,
    'help': Sort.NONE,

    # Compilation
    'compile': Sort.TOP,
    'eval': Sort.TOP,
    'exec': Sort.NONE,
    '__import__': Sort.TOP,

    # Itertools-style builtins
    'zip_longest': Sort.ITER,

    # collections
    'defaultdict': Sort.MAP,
    'OrderedDict': Sort.MAP,
    'Counter': Sort.MAP,
    'deque': Sort.SEQ,
    'namedtuple': Sort.FUNC,
    'ChainMap': Sort.MAP,

    # functools
    'reduce': Sort.TOP,
    'partial': Sort.FUNC,
    'lru_cache': Sort.FUNC,
    'cache': Sort.FUNC,
    'wraps': Sort.FUNC,
    'total_ordering': Sort.FUNC,
    'cmp_to_key': Sort.FUNC,

    # math
    'sqrt': Sort.NUM,
    'log': Sort.NUM,
    'log2': Sort.NUM,
    'log10': Sort.NUM,
    'exp': Sort.NUM,
    'sin': Sort.NUM,
    'cos': Sort.NUM,
    'tan': Sort.NUM,
    'asin': Sort.NUM,
    'acos': Sort.NUM,
    'atan': Sort.NUM,
    'atan2': Sort.NUM,
    'ceil': Sort.NUM,
    'floor': Sort.NUM,
    'trunc': Sort.NUM,
    'gcd': Sort.NUM,
    'lcm': Sort.NUM,
    'factorial': Sort.NUM,
    'comb': Sort.NUM,
    'perm': Sort.NUM,
    'isnan': Sort.BOOL,
    'isinf': Sort.BOOL,
    'isfinite': Sort.BOOL,
    'isclose': Sort.BOOL,
    'fabs': Sort.NUM,
    'fmod': Sort.NUM,
    'modf': Sort.SEQ,
    'frexp': Sort.SEQ,
    'ldexp': Sort.NUM,
    'copysign': Sort.NUM,
    'hypot': Sort.NUM,
    'degrees': Sort.NUM,
    'radians': Sort.NUM,
    'pi': Sort.NUM,
    'e': Sort.NUM,
    'inf': Sort.NUM,
    'nan': Sort.NUM,
    'tau': Sort.NUM,

    # heapq
    'heappush': Sort.NONE,
    'heappop': Sort.TOP,
    'heapify': Sort.NONE,
    'heapreplace': Sort.TOP,
    'heappushpop': Sort.TOP,
    'nlargest': Sort.SEQ,
    'nsmallest': Sort.SEQ,
    'merge': Sort.ITER,

    # bisect
    'bisect': Sort.NUM,
    'bisect_left': Sort.NUM,
    'bisect_right': Sort.NUM,
    'insort': Sort.NONE,
    'insort_left': Sort.NONE,
    'insort_right': Sort.NONE,

    # copy
    'copy': Sort.TOP,
    'deepcopy': Sort.TOP,

    # itertools
    'chain': Sort.ITER,
    'combinations': Sort.ITER,
    'combinations_with_replacement': Sort.ITER,
    'permutations': Sort.ITER,
    'product': Sort.ITER,
    'accumulate': Sort.ITER,
    'groupby': Sort.ITER,
    'starmap': Sort.ITER,
    'takewhile': Sort.ITER,
    'dropwhile': Sort.ITER,
    'islice': Sort.ITER,
    'count': Sort.ITER,
    'cycle': Sort.ITER,
    'repeat': Sort.ITER,
    'tee': Sort.SEQ,
    'filterfalse': Sort.ITER,
    'compress': Sort.ITER,
    'pairwise': Sort.ITER,
    'batched': Sort.ITER,

    # operator module
    'itemgetter': Sort.FUNC,
    'attrgetter': Sort.FUNC,
    'methodcaller': Sort.FUNC,

    # re module
    'match': Sort.TOP,
    'search': Sort.TOP,
    'findall': Sort.SEQ,
    'finditer': Sort.ITER,
    'sub': Sort.STR,
    'subn': Sort.SEQ,
    'fullmatch': Sort.TOP,

    # json
    'dumps': Sort.STR,
    'loads': Sort.TOP,
    'dump': Sort.NONE,
    'load': Sort.TOP,

    # Decimal
    'Decimal': Sort.NUM,
}

# ── Full operation specifications ─────────────────────────────────

_FUNC_OPS: dict[str, Tuple[str, FrozenSet[Refinement], Effect]] = {
    # Length
    'len': ('Measure.length', frozenset(), Effect.PURE),

    # Sorting
    'sorted': ('Seq.sort', frozenset({Refinement.SORTED}), Effect.ALLOCATE),
    'reversed': ('Seq.reverse_iter', frozenset({Refinement.REVERSED}), Effect.PURE),

    # Iteration
    'enumerate': ('Seq.enumerate', frozenset(), Effect.PURE),
    'zip': ('Seq.zip', frozenset(), Effect.PURE),
    'map': ('Func.map', frozenset({Refinement.MAPPED}), Effect.PURE),
    'filter': ('Func.filter', frozenset({Refinement.FILTERED}), Effect.PURE),
    'iter': ('Seq.iter', frozenset(), Effect.PURE),
    'next': ('Iter.next', frozenset(), Effect.MUTATE),

    # Reductions
    'sum': ('Accum.sum', frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'min': ('Accum.min', frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT}), Effect.PURE),
    'max': ('Accum.max', frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE, Refinement.IDEMPOTENT}), Effect.PURE),
    'any': ('Accum.any', frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'all': ('Accum.all', frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'reduce': ('Accum.fold', frozenset(), Effect.PURE),

    # Numeric
    'abs': ('Num.abs', frozenset({Refinement.IDEMPOTENT}), Effect.PURE),
    'pow': ('Num.pow', frozenset(), Effect.PURE),
    'round': ('Num.round', frozenset({Refinement.IDEMPOTENT}), Effect.PURE),
    'divmod': ('Num.divmod', frozenset(), Effect.PURE),

    # Constructors
    'int': ('Cast.to_num', frozenset(), Effect.PURE),
    'float': ('Cast.to_num', frozenset(), Effect.PURE),
    'complex': ('Cast.to_num', frozenset(), Effect.PURE),
    'bool': ('Cast.to_bool', frozenset(), Effect.PURE),
    'str': ('Cast.to_str', frozenset(), Effect.PURE),
    'bytes': ('Cast.to_str', frozenset(), Effect.PURE),
    'list': ('Cast.to_seq', frozenset(), Effect.ALLOCATE),
    'tuple': ('Cast.to_seq', frozenset(), Effect.ALLOCATE),
    'dict': ('Cast.to_map', frozenset(), Effect.ALLOCATE),
    'set': ('Cast.to_set', frozenset(), Effect.ALLOCATE),
    'frozenset': ('Cast.to_set', frozenset(), Effect.ALLOCATE),
    'range': ('Seq.range', frozenset({Refinement.SORTED}), Effect.PURE),

    # String representation
    'repr': ('Cast.to_repr', frozenset(), Effect.PURE),
    'ascii': ('Cast.to_str', frozenset(), Effect.PURE),
    'chr': ('Cast.chr', frozenset(), Effect.PURE),
    'ord': ('Cast.ord', frozenset(), Effect.PURE),
    'bin': ('Cast.to_str', frozenset(), Effect.PURE),
    'oct': ('Cast.to_str', frozenset(), Effect.PURE),
    'hex': ('Cast.to_str', frozenset(), Effect.PURE),
    'format': ('Cast.to_str', frozenset(), Effect.PURE),

    # Type checks
    'isinstance': ('Type.isinstance', frozenset(), Effect.PURE),
    'issubclass': ('Type.issubclass', frozenset(), Effect.PURE),
    'callable': ('Type.callable', frozenset(), Effect.PURE),
    'hasattr': ('Type.hasattr', frozenset(), Effect.PURE),
    'getattr': ('Type.getattr', frozenset(), Effect.PURE),
    'setattr': ('Type.setattr', frozenset(), Effect.MUTATE),
    'delattr': ('Type.delattr', frozenset(), Effect.MUTATE),

    # Identity
    'id': ('Type.id', frozenset(), Effect.PURE),
    'hash': ('Type.hash', frozenset(), Effect.PURE),

    # I/O
    'print': ('IO.print', frozenset(), Effect.IO),
    'input': ('IO.input', frozenset(), Effect.IO),
    'open': ('IO.open', frozenset(), Effect.IO),

    # Introspection
    'dir': ('Type.dir', frozenset(), Effect.PURE),
    'vars': ('Type.vars', frozenset(), Effect.PURE),
    'globals': ('Type.globals', frozenset(), Effect.PURE),
    'locals': ('Type.locals', frozenset(), Effect.PURE),

    # Collections
    'defaultdict': ('Cast.to_map', frozenset(), Effect.ALLOCATE),
    'OrderedDict': ('Cast.to_map', frozenset({Refinement.SORTED}), Effect.ALLOCATE),
    'Counter': ('Cast.to_map', frozenset(), Effect.ALLOCATE),
    'deque': ('Cast.to_seq', frozenset(), Effect.ALLOCATE),

    # Functools
    'partial': ('Func.partial', frozenset(), Effect.PURE),
    'lru_cache': ('Func.memoize', frozenset(), Effect.PURE),
    'cache': ('Func.memoize', frozenset(), Effect.PURE),

    # Heapq
    'heappush': ('Heap.push', frozenset({Refinement.SORTED}), Effect.MUTATE),
    'heappop': ('Heap.pop', frozenset({Refinement.SORTED}), Effect.MUTATE),
    'heapify': ('Heap.heapify', frozenset({Refinement.SORTED}), Effect.MUTATE),
    'heapreplace': ('Heap.replace', frozenset({Refinement.SORTED}), Effect.MUTATE),
    'heappushpop': ('Heap.pushpop', frozenset({Refinement.SORTED}), Effect.MUTATE),
    'nlargest': ('Heap.nlargest', frozenset({Refinement.SORTED}), Effect.PURE),
    'nsmallest': ('Heap.nsmallest', frozenset({Refinement.SORTED}), Effect.PURE),

    # Bisect
    'bisect': ('Search.bisect', frozenset({Refinement.SORTED}), Effect.PURE),
    'bisect_left': ('Search.bisect', frozenset({Refinement.SORTED}), Effect.PURE),
    'bisect_right': ('Search.bisect', frozenset({Refinement.SORTED}), Effect.PURE),
    'insort': ('Search.insort', frozenset({Refinement.SORTED}), Effect.MUTATE),
    'insort_left': ('Search.insort', frozenset({Refinement.SORTED}), Effect.MUTATE),
    'insort_right': ('Search.insort', frozenset({Refinement.SORTED}), Effect.MUTATE),

    # Copy
    'copy': ('Clone.shallow', frozenset(), Effect.ALLOCATE),
    'deepcopy': ('Clone.deep', frozenset(), Effect.ALLOCATE),

    # Itertools
    'chain': ('Iter.chain', frozenset(), Effect.PURE),
    'combinations': ('Iter.combinations', frozenset(), Effect.PURE),
    'combinations_with_replacement': ('Iter.combinations', frozenset(), Effect.PURE),
    'permutations': ('Iter.permutations', frozenset(), Effect.PURE),
    'product': ('Iter.product', frozenset(), Effect.PURE),
    'accumulate': ('Iter.accumulate', frozenset(), Effect.PURE),
    'groupby': ('Iter.groupby', frozenset(), Effect.PURE),
    'starmap': ('Iter.starmap', frozenset(), Effect.PURE),
    'takewhile': ('Iter.takewhile', frozenset({Refinement.FILTERED}), Effect.PURE),
    'dropwhile': ('Iter.dropwhile', frozenset({Refinement.FILTERED}), Effect.PURE),
    'islice': ('Iter.islice', frozenset(), Effect.PURE),
    'count': ('Iter.count', frozenset(), Effect.PURE),
    'cycle': ('Iter.cycle', frozenset(), Effect.PURE),
    'repeat': ('Iter.repeat', frozenset(), Effect.PURE),
    'filterfalse': ('Iter.filterfalse', frozenset({Refinement.FILTERED}), Effect.PURE),
    'compress': ('Iter.compress', frozenset({Refinement.FILTERED}), Effect.PURE),

    # Math
    'sqrt': ('Num.sqrt', frozenset(), Effect.PURE),
    'log': ('Num.log', frozenset(), Effect.PURE),
    'log2': ('Num.log', frozenset(), Effect.PURE),
    'log10': ('Num.log', frozenset(), Effect.PURE),
    'exp': ('Num.exp', frozenset(), Effect.PURE),
    'sin': ('Num.trig', frozenset(), Effect.PURE),
    'cos': ('Num.trig', frozenset(), Effect.PURE),
    'tan': ('Num.trig', frozenset(), Effect.PURE),
    'asin': ('Num.trig', frozenset(), Effect.PURE),
    'acos': ('Num.trig', frozenset(), Effect.PURE),
    'atan': ('Num.trig', frozenset(), Effect.PURE),
    'atan2': ('Num.trig', frozenset(), Effect.PURE),
    'ceil': ('Num.round', frozenset(), Effect.PURE),
    'floor': ('Num.round', frozenset(), Effect.PURE),
    'trunc': ('Num.round', frozenset(), Effect.PURE),
    'gcd': ('Num.gcd', frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'lcm': ('Num.lcm', frozenset({Refinement.COMMUTATIVE, Refinement.ASSOCIATIVE}), Effect.PURE),
    'factorial': ('Num.factorial', frozenset(), Effect.PURE),
    'fabs': ('Num.abs', frozenset({Refinement.IDEMPOTENT}), Effect.PURE),

    # Decimal
    'Decimal': ('Cast.to_num', frozenset(), Effect.PURE),

    # JSON
    'dumps': ('Serialize.encode', frozenset(), Effect.PURE),
    'loads': ('Serialize.decode', frozenset(), Effect.PURE),
    'dump': ('Serialize.encode', frozenset(), Effect.IO),
    'load': ('Serialize.decode', frozenset(), Effect.IO),
}


def builtin_func_to_typed_op(
        name: str,
        arg_sorts: Tuple[Sort, ...],
) -> Tuple[str, FrozenSet[Refinement], Effect]:
    """Return (op_name, refinements, effect) for a builtin function call."""
    if name in _FUNC_OPS:
        return _FUNC_OPS[name]
    return (f'Call.{name}', frozenset(), Effect.PURE)
