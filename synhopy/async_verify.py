"""
synhopy.async_verify — Async/await verification constructs.

Provides async-aware pre/postconditions and coroutine verification for
``from synhopy.async_verify import async_requires, async_ensures``.
"""
from __future__ import annotations
from typing import Any, Callable, TypeVar
import functools

T = TypeVar("T")


class Async:
    """Type wrapper indicating an async computation."""
    def __init__(self, result_type=None):
        self.result_type = result_type


def async_requires(pred):
    """Precondition for async functions."""
    def decorator(fn):
        fn._synhopy_async_requires = pred
        @functools.wraps(fn)
        async def wrapper(*args, **kwargs):
            return await fn(*args, **kwargs)
        wrapper._synhopy_async_requires = pred
        wrapper.__wrapped__ = fn
        return wrapper
    return decorator


def async_ensures(pred):
    """Postcondition for async functions."""
    def decorator(fn):
        fn._synhopy_async_ensures = pred
        @functools.wraps(fn)
        async def wrapper(*args, **kwargs):
            return await fn(*args, **kwargs)
        wrapper._synhopy_async_ensures = pred
        wrapper.__wrapped__ = fn
        return wrapper
    return decorator


def async_yields(pred):
    """Yield spec for async generators."""
    def decorator(fn):
        fn._synhopy_async_yields = pred
        return fn
    return decorator


def async_invariant(inv):
    """Loop invariant for async loops."""
    def decorator(fn):
        fn._synhopy_async_invariant = inv
        return fn
    return decorator
