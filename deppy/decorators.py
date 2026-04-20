"""
deppy.decorators — Decorator inspection utilities.

For ``from deppy.decorators import unwrap_decorator_stack``.
"""
from __future__ import annotations
import functools
import inspect


def unwrap_decorator_stack(fn):
    """Unwrap a stack of decorators, returning the original function."""
    while hasattr(fn, '__wrapped__'):
        fn = fn.__wrapped__
    return fn


def decorator_chain(fn):
    """Return the chain of decorators applied to fn (outermost first)."""
    chain = []
    current = fn
    while hasattr(current, '__wrapped__'):
        chain.append(current)
        current = current.__wrapped__
    chain.append(current)  # original function
    return chain
