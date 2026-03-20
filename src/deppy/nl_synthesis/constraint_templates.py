
from __future__ import annotations

from typing import Annotated, Any

from deppy.predicates import Comparison, IntLit, NonEmpty, Sorted, Var

from .models import DocstringFragment, NLConstraint


class SortedConstraint: ...
class NonEmptyConstraint: ...
class PositiveConstraint: ...
class InPlaceConstraint: ...
class ImmutableConstraint: ...


def constraint_from_fragment(fragment: DocstringFragment, return_type: Any = object) -> NLConstraint | None:
    text = fragment.text.lower()
    if 'sorted' in text:
        return NLConstraint(fragment.text, fragment.intent, 'sorted', Annotated[return_type, SortedConstraint], Sorted(Var('result')), 'sorted', 0.95)
    if 'non-empty' in text or 'nonempty' in text:
        return NLConstraint(fragment.text, fragment.intent, 'non_empty', Annotated[return_type, NonEmptyConstraint], NonEmpty(Var('result')), 'non_empty', 0.9)
    if 'positive' in text or 'non-negative' in text or 'nonnegative' in text:
        return NLConstraint(fragment.text, fragment.intent, 'positive', Annotated[return_type, PositiveConstraint], Comparison('>=', Var('result'), IntLit(0)), 'positive', 0.85)
    if 'in-place' in text or 'in place' in text:
        return NLConstraint(fragment.text, fragment.intent, 'in_place', Annotated[return_type, InPlaceConstraint], None, 'in_place', 0.8)
    if 'immutable' in text or 'does not mutate' in text:
        return NLConstraint(fragment.text, fragment.intent, 'immutable', Annotated[return_type, ImmutableConstraint], None, 'immutable', 0.8)
    return None
