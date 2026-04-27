"""Async / await for PSDL — event-indexed paths.

A coroutine is an *event-indexed path*: between an enter point and
each ``await`` point lies a path in the world category, then between
the await point and its resumption lies a path indexed by the event
that woke the coroutine.

Cubical interpretation::

    Async(ε, A) ≅ ∫_{ε : Event} (Path Pre(ε) Post(ε) → A)

i.e. an async value of type ``A`` is a function from events ``ε`` to
*completions*: a path from the pre-await world to the post-await
world plus the resulting ``A`` value.

  * ``await x`` is :class:`EffectWitness` with effect
    ``"await:E"`` (``E`` is the awaitable's identifier).
  * Resumption after the event arrives is :class:`TransportProof`
    along the event-arrival path: the motive is the post-await
    state of the coroutine.
  * ``async def`` is a coalgebra: each await suspends and resumes,
    composing into a chain of paths.
  * The event loop's choice of which coroutine to schedule next is
    a :class:`Fiber` over the set of pending awaitables — different
    fibres represent different scheduling decisions.

Soundness gain: claims about an async function's value are claims
about the *exit fibre* of its scheduling — at least one fibre must
satisfy the property, but the user cannot assume which one fires.
``await`` outside an ``async def`` is a syntax error in Python; PSDL
flags the same as a soundness violation.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional


@dataclass
class AwaitPoint:
    """One await suspension in a coroutine's lifecycle."""
    index: int
    awaitable_repr: str
    line_no: int = 0
    world_epoch: int = 0
    # Whether this await is currently pending (not yet resumed).
    pending: bool = True


@dataclass
class Coroutine:
    """A coroutine's lifecycle as a sequence of await points.

    Mirrors :class:`Generator` but the suspension condition is an
    *event* (an awaitable), not a yield destination.  The ``Async``
    monad's ``then`` is path composition; the ``Future`` algebra's
    completion is :class:`TransportProof` along the event path.
    """
    name: str
    awaits: list[AwaitPoint] = field(default_factory=list)
    completed: bool = False
    cell_id: Optional[int] = None

    def add_await(
        self, awaitable_repr: str, *, line: int, world_epoch: int,
    ) -> AwaitPoint:
        idx = len(self.awaits)
        ap = AwaitPoint(
            index=idx,
            awaitable_repr=awaitable_repr,
            line_no=line,
            world_epoch=world_epoch,
        )
        self.awaits.append(ap)
        return ap

    def resume(self, index: int) -> Optional[AwaitPoint]:
        if 0 <= index < len(self.awaits):
            self.awaits[index].pending = False
            return self.awaits[index]
        return None


@dataclass
class CoroutineRegistry:
    """Tracks every async coroutine in a PSDL block."""
    coroutines: dict[str, Coroutine] = field(default_factory=dict)
    aliases: dict[str, str] = field(default_factory=dict)

    def resolve(self, name: str) -> str:
        seen: set[str] = set()
        cur = name
        while cur in self.aliases and cur not in seen:
            seen.add(cur)
            cur = self.aliases[cur]
        return cur

    def get(self, name: str) -> Optional[Coroutine]:
        return self.coroutines.get(self.resolve(name))

    def declare(self, name: str, *, line: int = 0) -> Coroutine:
        canonical = self.resolve(name)
        if canonical in self.coroutines:
            return self.coroutines[canonical]
        c = Coroutine(name=canonical)
        self.coroutines[canonical] = c
        return c

    def alias(self, dst: str, src: str) -> None:
        self.aliases[dst] = self.resolve(src)

    def add_await_to(
        self,
        name: str,
        awaitable_repr: str,
        *,
        line: int,
        world_epoch: int,
    ) -> AwaitPoint:
        c = self.get(name)
        if c is None:
            c = self.declare(name, line=line)
        return c.add_await(
            awaitable_repr, line=line, world_epoch=world_epoch,
        )


# ───────────────────────────────────────────────────────────────────
#  PSDL primitives — emit kernel terms for await/resume
# ───────────────────────────────────────────────────────────────────

def emit_await_witness(
    awaitable_repr: str, index: int, *, world_epoch: int,
):
    """Build an :class:`EffectWitness` recording one ``await`` step.

    The effect tag encodes the awaitable's identity AND the world
    epoch at the await point — so two awaits on the same awaitable
    at different epochs are distinct kernel artefacts.
    """
    from deppy.core.kernel import EffectWitness, Refl
    from deppy.core.types import Var
    return EffectWitness(
        effect=f"await:{awaitable_repr[:40]}@epoch{world_epoch}",
        proof=Refl(Var(f"_await_{index}")),
    )


def emit_resume_witness(c: Coroutine, index: int, *, line: int):
    """Build a :class:`TransportProof` for the event-arrival path:
    the motive is "post-await world", the path is the event's
    fulfilment, the base is the suspended state at the await."""
    from deppy.core.kernel import TransportProof, AxiomInvocation, Refl
    from deppy.core.types import Var
    if not (0 <= index < len(c.awaits)):
        from deppy.core.kernel import Structural
        return Structural(
            f"coroutine {c.name}: resume out-of-range (line {line})"
        )
    ap = c.awaits[index]
    return TransportProof(
        type_family=Var(f"_post_await_{c.name}_{index}"),
        path_proof=AxiomInvocation(
            name=f"event_{ap.awaitable_repr[:40]}_arrived",
            module="async",
        ),
        base_proof=Refl(Var(f"_pre_await_{c.name}_{index}")),
    )


__all__ = [
    "AwaitPoint",
    "Coroutine",
    "CoroutineRegistry",
    "emit_await_witness",
    "emit_resume_witness",
]
