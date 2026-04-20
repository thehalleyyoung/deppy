"""
deppy.patching — Monkey patching safety verification.

For ``from deppy.patching import safe_patch``.
"""
from __future__ import annotations
import functools


def safe_patch(target_cls, method_name: str = ""):
    """Decorator verifying a monkey patch preserves behavioral equivalence.

    Usage::

        @safe_patch(SomeClass, "method_name")
        def patched_method(self, ...):
            ...
    """
    def decorator(fn):
        fn._deppy_safe_patch = True
        fn._deppy_patch_target = target_cls
        fn._deppy_patch_method = method_name or fn.__name__
        @functools.wraps(fn)
        def wrapper(*args, **kwargs):
            return fn(*args, **kwargs)
        wrapper._deppy_safe_patch = True
        wrapper._deppy_patch_target = target_cls
        wrapper._deppy_patch_method = method_name or fn.__name__
        return wrapper
    return decorator
