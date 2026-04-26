"""
deppy.hott — Homotopy Type Theory constructs for Deppy.

Re-exports HoTT primitives so that ``from deppy.hott import DuckPath``
works as shown in the Deppy tutorial book.
"""
from __future__ import annotations

from deppy.core.kernel import (          # noqa: F401
    DuckPath, ConditionalDuckPath, FiberedLookup,
    TransportProof, PathComp, Ap, FunExt,
    CechGlue, Univalence, Fiber, Patch, Refl, Sym, Trans, Cong,
)
from deppy.core.types import PathType    # noqa: F401

from deppy.proofs.sugar import (         # noqa: F401
    path, path_chain, funext, transport_proof, transport_from,
    path_equivalent, by_transport, by_cech_proof, by_fiber_proof,
)

# Convenience re-exports
transport = transport_proof

# Add class methods to kernel types for book API compatibility
def _duck_path_auto_construct(cls, source_cls, target_cls, protocol=None):
    """Automatically construct a DuckPath by introspecting methods."""
    import inspect
    methods = []
    if protocol:
        for name in dir(protocol):
            if not name.startswith('_') or name in ('__iter__', '__next__', '__len__',
                '__getitem__', '__setitem__', '__contains__', '__enter__', '__exit__',
                '__call__', '__eq__', '__hash__', '__repr__', '__str__'):
                if hasattr(source_cls, name) and hasattr(target_cls, name):
                    methods.append(name)
    else:
        for name in dir(target_cls):
            if not name.startswith('_') and hasattr(source_cls, name):
                methods.append(name)
    evidence = {m: MethodPath(source_cls, target_cls, m) for m in methods}
    return DuckPath(
        f"auto:{source_cls.__name__}~{target_cls.__name__}",
        evidence=evidence
    )
DuckPath.auto_construct = classmethod(_duck_path_auto_construct)

class MethodPath:
    """Evidence that a method on one class behaves like a method on another."""
    def __init__(self, source_cls, target_cls, method_name: str, evidence=None):
        self.source_cls = source_cls
        self.target_cls = target_cls
        self.method_name = method_name
        self.evidence = evidence

    def details(self) -> str:
        """Human-readable description of this method path."""
        return (
            f"MethodPath({self.source_cls}.{self.method_name} "
            f"→ {self.target_cls}.{self.method_name}): "
            f"evidence={self.evidence}"
        )

class SignatureCheck:
    """Evidence that a class has a method with the expected signature."""
    def __init__(self, cls, method_name: str, expected_sig=None):
        self.cls = cls
        self.method_name = method_name
        self.expected_sig = expected_sig

class Fibration:
    """A fibration p: E → B with fiber F."""
    def __init__(self, total_space, base_space, projection=None, fiber=None):
        self.total_space = total_space
        self.base_space = base_space
        self.projection = projection
        self.fiber = fiber

    @classmethod
    def from_metaclass(cls, metaclass):
        """Construct a Fibration from a metaclass.

        Mirrors :meth:`deppy.core.kernel.Fiber.from_metaclass`: the
        metaclass forms the *base space* and the breadth-first
        ``__subclasses__()`` closure forms the *total space*.

        Validation:

        * ``metaclass`` must itself be a Python class
          (``isinstance(metaclass, type)``) — otherwise a
          :class:`TypeError` is raised so the caller cannot pass a
          random instance and quietly get an empty fibration.

        The constructed object exposes the enumerated subclass list
        on ``self.subclasses`` for downstream consumers.
        """
        if not isinstance(metaclass, type):
            raise TypeError(
                f"Fibration.from_metaclass: expected a class (typically a "
                f"metaclass), got {type(metaclass).__name__}"
            )

        seen: set = set()
        subclasses: list = []
        queue = [metaclass]
        while queue:
            cls_ = queue.pop(0)
            if cls_ in seen:
                continue
            seen.add(cls_)
            try:
                children = cls_.__subclasses__()
            except TypeError:
                children = []
            for child in children:
                if child not in seen:
                    subclasses.append(child)
                    queue.append(child)

        fib = cls(
            total_space=tuple(subclasses) or (metaclass,),
            base_space=metaclass,
            projection=lambda x: type(x),
        )
        fib.subclasses = list(subclasses)
        return fib

class FiberCheck:
    """Evidence that a value lies in a specific fiber."""
    def __init__(self, fibration, base_point, value, evidence=None):
        self.fibration = fibration
        self.base_point = base_point
        self.value = value
        self.evidence = evidence

class Equiv:
    """Evidence that two types are equivalent (A ≃ B)."""
    def __init__(self, forward, backward, section=None, retraction=None):
        self.forward = forward
        self.backward = backward
        self.section = section
        self.retraction = retraction

def path_compose(*paths):
    """Compose multiple paths: p1 · p2 · ... · pn."""
    result = paths[0] if paths else None
    for p in paths[1:]:
        result = PathComp(result, p)
    return result


# ── Additional types referenced in the book ──

class Universe:
    """The type universe U_i at level i."""
    def __init__(self, level: int = 0):
        self.level = level
    def __repr__(self):
        return f"U_{self.level}"

class Level:
    """Universe level."""
    def __init__(self, n: int = 0):
        self.n = n

class Dec:
    """Decidable proposition: either a proof or a refutation."""
    def __init__(self, prop, evidence=None, is_yes: bool = True):
        self.prop = prop
        self.evidence = evidence
        self.is_yes = is_yes

class Narrowing:
    """Type narrowing evidence: a value is known to inhabit a subtype."""
    def __init__(self, value, narrow_type, evidence=None):
        self.value = value
        self.narrow_type = narrow_type
        self.evidence = evidence

NarrowingProof = Narrowing  # alias

class PathPreserving:
    """Evidence that a function preserves paths (is functorial)."""
    def __init__(self, fn, evidence=None):
        self.fn = fn
        self.evidence = evidence

class PathEquiv(Equiv):
    """Path equivalence: evidence that two types are path-equivalent."""
    pass

class TotalSpace:
    """Total space of a fibration: Σ(b:B). F(b)."""
    def __init__(self, base, fiber_fn):
        self.base = base
        self.fiber_fn = fiber_fn

class Section:
    """A section of a fibration: s: B → E such that p ∘ s = id."""
    def __init__(self, fibration, section_fn):
        self.fibration = fibration
        self.section_fn = section_fn
