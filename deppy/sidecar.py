"""
deppy.sidecar — thin re-export shim.

This module re-exports ``SidecarModule`` / ``ExternalSpec`` from
``deppy.proofs.sidecar`` and decorators like ``guarantee`` / ``verify``
from ``deppy.proofs.sugar``.  It also exports its own ``about`` and
``assume`` helpers — **note that**:

* ``about("module.path")`` attaches the string to ``fn._deppy_about``
  but the rest of the pipeline does not read that attribute; the
  decorator is effectively documentation.
* ``assume(statement)`` returns an ``Assume`` kernel term which CAN
  be cited in a proof — that part is real — but nothing here
  type-checks ``statement`` against the code the assumption targets.

For the real sidecar API, import from ``deppy.proofs.sidecar``.
"""
from __future__ import annotations

from deppy.proofs.sidecar import (       # noqa: F401
    SidecarModule, ExternalSpec,
)
from deppy.proofs.sugar import (         # noqa: F401
    guarantee, verify, by_z3, by_axiom,
    formal_check, formal_eq,
)
from deppy.core.kernel import Assume     # noqa: F401


def about(module_path: str):
    """Decorator marking a function/class as a sidecar spec for module_path."""
    def decorator(fn):
        fn._deppy_about = module_path
        return fn
    return decorator


def assume(statement: str, *, name: str = "", domain: str = ""):
    """Declare an assumed property of an external library."""
    return Assume(statement)


def prove(statement: str, *, by=None, name: str = ""):
    """Declare a property to be proved about an external library."""
    return statement


def law(name_or_fn=None, statement: str = "", *, domain: str = ""):
    """Declare a mathematical law as an axiom for sidecar proofs.

    Can be used as:
      - Bare decorator: @law on a method
      - With args: law("name", "statement")
    """
    # @law used as bare decorator
    if callable(name_or_fn):
        fn = name_or_fn
        fn._deppy_law = True
        fn._deppy_law_name = getattr(fn, '__name__', 'unnamed')
        return fn

    # law("name", "statement") — returns an Assume
    if isinstance(name_or_fn, str) and statement:
        return Assume(f"{name_or_fn}: {statement}")

    # @law("name") used as decorator factory
    if isinstance(name_or_fn, str):
        def decorator(fn):
            fn._deppy_law = True
            fn._deppy_law_name = name_or_fn
            return fn
        return decorator

    # law() with no args — decorator factory
    def decorator(fn):
        fn._deppy_law = True
        fn._deppy_law_name = getattr(fn, '__name__', 'unnamed')
        return fn
    return decorator


def proof_for(target: str):
    """Decorator marking a function as providing a proof for target."""
    def decorator(fn):
        fn._deppy_proof_for = target
        return fn
    return decorator


def z3_config(**kwargs):
    """Configure Z3 settings for a sidecar proof.  Works as a decorator."""
    def decorator(fn):
        fn._deppy_z3_config = kwargs
        return fn
    return decorator


def z3_hint(**kwargs):
    """Provide hints to the Z3 solver.  Works as a decorator."""
    def decorator(fn):
        fn._deppy_z3_hint = kwargs
        return fn
    return decorator


def loop_invariant(**kwargs):
    """Declare a loop invariant for sidecar proofs.  Works as a decorator."""
    def decorator(fn):
        fn._deppy_loop_invariant = kwargs
        return fn
    return decorator


def assert_lemma(statement: str, *, by=None):
    """Assert a lemma within a sidecar proof."""
    return statement


def numpy_spec(module_name: str = "numpy"):
    """Load pre-built NumPy sidecar specifications."""
    return {"module": module_name, "specs": "numpy_builtin"}
