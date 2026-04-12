"""Interpretation of Python control flow in the motive framework.

Control flow constructs (if/elif/else, for, while, try/except, with,
match/case) are typed operations with specific effects.
"""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

# ── Control flow operations ──────────────────────────────────────
# Each entry: (op_name, input_sorts, output_sort, refinements, effect)

CONTROL_FLOW_OPS = {
    # Branching
    'if': ('Branch.test', (Sort.BOOL,), Sort.TOP, frozenset(), Effect.PURE),
    'elif': ('Branch.test', (Sort.BOOL,), Sort.TOP, frozenset(), Effect.PURE),
    'else': ('Branch.default', (), Sort.TOP, frozenset(), Effect.PURE),
    'ternary': ('Branch.ternary', (Sort.BOOL, Sort.TOP, Sort.TOP), Sort.TOP, frozenset(), Effect.PURE),

    # Iteration
    'for': ('Loop.iterate', (Sort.ITER,), Sort.TOP, frozenset(), Effect.ITERATE),
    'while': ('Loop.while', (Sort.BOOL,), Sort.TOP, frozenset(), Effect.ITERATE),
    'break': ('Loop.break', (), Sort.NONE, frozenset(), Effect.PURE),
    'continue': ('Loop.continue', (), Sort.NONE, frozenset(), Effect.PURE),

    # Exception handling
    'try': ('Exception.try', (), Sort.TOP, frozenset(), Effect.PURE),
    'except': ('Exception.catch', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),
    'finally': ('Exception.finally', (), Sort.NONE, frozenset(), Effect.PURE),
    'raise': ('Exception.raise', (Sort.TOP,), Sort.NONE, frozenset(), Effect.IO),

    # Context management
    'with': ('Context.enter', (Sort.TOP,), Sort.TOP, frozenset(), Effect.IO),
    'async_with': ('Context.async_enter', (Sort.TOP,), Sort.TOP, frozenset(), Effect.IO),

    # Pattern matching (Python 3.10+)
    'match': ('Match.subject', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),
    'case': ('Match.case', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),
    'case_guard': ('Match.guard', (Sort.BOOL,), Sort.TOP, frozenset(), Effect.PURE),

    # Function definition
    'def': ('Func.define', (), Sort.FUNC, frozenset(), Effect.ALLOCATE),
    'lambda': ('Func.lambda', (), Sort.FUNC, frozenset(), Effect.ALLOCATE),
    'return': ('Func.return', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),
    'yield': ('Func.yield', (Sort.TOP,), Sort.TOP, frozenset(), Effect.ITERATE),
    'yield_from': ('Func.yield_from', (Sort.ITER,), Sort.TOP, frozenset(), Effect.ITERATE),
    'await': ('Func.await', (Sort.TOP,), Sort.TOP, frozenset(), Effect.IO),

    # Class definition
    'class': ('Type.define', (), Sort.FUNC, frozenset(), Effect.ALLOCATE),

    # Import
    'import': ('Module.import', (), Sort.TOP, frozenset(), Effect.IO),
    'from_import': ('Module.from_import', (), Sort.TOP, frozenset(), Effect.IO),

    # Assertions
    'assert': ('Assert.check', (Sort.BOOL,), Sort.NONE, frozenset(), Effect.PURE),

    # Deletion
    'del': ('Mem.free', (Sort.TOP,), Sort.NONE, frozenset(), Effect.MUTATE),

    # Assignment (structural)
    'assign': ('Assign.bind', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),
    'augmented_assign': ('Assign.rebind', (Sort.TOP, Sort.TOP), Sort.TOP, frozenset(), Effect.MUTATE),
    'walrus': ('Assign.walrus', (Sort.TOP,), Sort.TOP, frozenset(), Effect.PURE),
    'unpack': ('Destructure.unpack', (Sort.SEQ,), Sort.TOP, frozenset(), Effect.PURE),
    'star_unpack': ('Destructure.splat', (Sort.SEQ,), Sort.SEQ, frozenset(), Effect.PURE),

    # Global/nonlocal
    'global': ('Scope.global', (), Sort.NONE, frozenset(), Effect.PURE),
    'nonlocal': ('Scope.nonlocal', (), Sort.NONE, frozenset(), Effect.PURE),

    # Pass
    'pass': ('Noop', (), Sort.NONE, frozenset(), Effect.PURE),
}
