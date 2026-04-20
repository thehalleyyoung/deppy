"""
synhopy.ghost — Ghost/erased computation support.

Provides ghost variables and computations for specification-only values.
"""
from __future__ import annotations
from typing import TypeVar, Generic

T = TypeVar("T")


class Ghost(Generic[T]):
    """A ghost (erased) value — exists only in specifications, not at runtime."""
    def __init__(self, value: T):
        self._value = value
    def reveal(self) -> T:
        return self._value
    def __repr__(self):
        return f"Ghost({self._value!r})"


def ghost_var(name: str, typ=None, initial=None):
    """Declare a ghost variable for use in specifications."""
    return Ghost(initial)


def ghost_update(ghost, new_value):
    """Update a ghost variable (specification only)."""
    return Ghost(new_value)

# Aliases used in book examples
ghost_set = ghost_update


def ghost_pts_to(ghost, value):
    """Ghost points-to: specification-level assertion that ghost holds value."""
    return Ghost(value)
