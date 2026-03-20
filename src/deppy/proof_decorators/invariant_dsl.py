
from __future__ import annotations

import inspect
from dataclasses import dataclass

from deppy.predicates import Comparison, IntLit, NonEmpty, Sorted, Var


@dataclass(frozen=True)
class CompiledInvariant:
    source: str
    predicate: object | None
    description: str


def compile_invariant(invariant) -> CompiledInvariant:
    try:
        source = inspect.getsource(invariant).strip()
    except Exception:
        source = getattr(invariant, '__name__', repr(invariant))
    lowered = source.lower()
    if 'sorted' in lowered:
        return CompiledInvariant(source, Sorted(Var('result')), 'sorted result')
    if 'len(' in lowered and '> 0' in lowered:
        return CompiledInvariant(source, NonEmpty(Var('result')), 'non-empty result')
    if '>=' in lowered and 'result' in lowered:
        return CompiledInvariant(source, Comparison('>=', Var('result'), IntLit(0)), 'non-negative result')
    return CompiledInvariant(source, None, 'opaque runtime invariant')
