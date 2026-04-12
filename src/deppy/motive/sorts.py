"""Sort lattice — the abstract domain of computational motives.

From Lawvere's functorial semantics: programs operate on a finitary algebra
whose carrier sorts form a lattice under subsorting.  This module defines
that lattice and its operations.

The lattice is:

        TOP
      / | | \\
   FUNC ITER MAP SET SEQ STR NUM BOOL NONE
      \\  |  / |  /    |   /   /
        BOT

Key relationships:
  BOOL ⊑ NUM   (booleans are numeric in Python)
  STR  ⊑ SEQ   (strings are iterable sequences)
  BOT  ⊑ *     (bottom is subtype of everything)
  *    ⊑ TOP   (everything is subtype of top)
"""

from __future__ import annotations

from enum import IntEnum, auto
from typing import Dict, Set


class Sort(IntEnum):
    """Abstract sorts forming the carrier lattice of the Lawvere theory."""
    BOT   = 0
    NONE  = auto()
    BOOL  = auto()
    NUM   = auto()
    STR   = auto()
    SEQ   = auto()
    MAP   = auto()
    SET   = auto()
    ITER  = auto()
    FUNC  = auto()
    TOP   = auto()


# Subsorting relation: _SUBSORT[s] = set of sorts that s is a subtype of
_SUBSORT: Dict[Sort, Set[Sort]] = {
    Sort.BOT:  set(Sort),
    Sort.BOOL: {Sort.BOOL, Sort.NUM, Sort.TOP},
    Sort.NONE: {Sort.NONE, Sort.TOP},
    Sort.NUM:  {Sort.NUM, Sort.TOP},
    Sort.STR:  {Sort.STR, Sort.SEQ, Sort.TOP},
    Sort.SEQ:  {Sort.SEQ, Sort.TOP},
    Sort.MAP:  {Sort.MAP, Sort.TOP},
    Sort.SET:  {Sort.SET, Sort.TOP},
    Sort.ITER: {Sort.ITER, Sort.TOP},
    Sort.FUNC: {Sort.FUNC, Sort.TOP},
    Sort.TOP:  {Sort.TOP},
}

# Direct supertypes for join/meet computation
_PARENT: Dict[Sort, Sort] = {
    Sort.BOT: Sort.BOT,
    Sort.NONE: Sort.TOP,
    Sort.BOOL: Sort.NUM,
    Sort.NUM: Sort.TOP,
    Sort.STR: Sort.SEQ,
    Sort.SEQ: Sort.TOP,
    Sort.MAP: Sort.TOP,
    Sort.SET: Sort.TOP,
    Sort.ITER: Sort.TOP,
    Sort.FUNC: Sort.TOP,
    Sort.TOP: Sort.TOP,
}


def sorts_compatible(a: Sort, b: Sort) -> bool:
    """Check if two sorts are compatible (have a common upper bound ≠ TOP).

    Two sorts are compatible when they could describe the same runtime value.
    This is the key predicate for the Čech coboundary map δ⁰.
    """
    if a == b:
        return True
    if a == Sort.BOT or b == Sort.BOT:
        return True
    if a == Sort.TOP or b == Sort.TOP:
        return True
    return bool(_SUBSORT.get(a, set()) & _SUBSORT.get(b, set()) - {Sort.TOP})


def sort_join(a: Sort, b: Sort) -> Sort:
    """Compute the join (least upper bound) of two sorts."""
    if a == b:
        return a
    if a == Sort.BOT:
        return b
    if b == Sort.BOT:
        return a
    if b in _SUBSORT.get(a, set()):
        return b
    if a in _SUBSORT.get(b, set()):
        return a
    return Sort.TOP


def sort_meet(a: Sort, b: Sort) -> Sort:
    """Compute the meet (greatest lower bound) of two sorts."""
    if a == b:
        return a
    if a == Sort.TOP:
        return b
    if b == Sort.TOP:
        return a
    if b in _SUBSORT.get(a, set()):
        return a
    if a in _SUBSORT.get(b, set()):
        return b
    return Sort.BOT
