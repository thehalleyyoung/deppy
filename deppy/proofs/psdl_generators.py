"""Generator semantics for PSDL — yield/pause/resume as a coalgebra.

A generator is the coalgebra of the comonad ``◇(A × _)``:

    G(A) ≅ ◇ (A × G(A))

i.e. a generator over ``A`` is *either* exhausted, *or* it produces
one ``A`` and a continuation generator.  ``yield x`` is the
destructor that extracts ``(x, k)``.

In cubical terms:

  * Each ``yield x`` is an :class:`EffectWitness` in the ``◇``
    modality with effect ``"yield:N"`` (``N`` is the yield index).
  * The path from one yield to the next is a kernel-level
    :class:`PathComp`.
  * ``next(g)`` is the comonad's *counit* ``extract``: it pulls the
    head out of the ◇.
  * ``g.send(v)`` resumes with input — this is *transport* along
    the path indexed by the input value.
  * ``g.close()`` is path inversion (``Sym``) on the suspended path.

Soundness gain: a proof claim about *all* values produced by a
generator must be expressed as a ``ListInduction`` over the chain
of yields, *not* over the iterable's surface elements.  Re-iterating
an exhausted generator is forbidden by the path's already-traversed
status — the kernel sees no fresh path to extract from.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional


@dataclass
class YieldPoint:
    """One yield in a generator's lifecycle."""
    index: int  # 0-based position in the yield sequence
    value_repr: str  # textual representation of the yielded value
    line_no: int = 0
    # The state of the world AT this yield (epoch from psdl_heap).
    world_epoch: int = 0
    # Whether the generator is suspended *here* (paused, awaiting
    # ``next`` / ``send``).  After ``next``, this becomes False and
    # the next YieldPoint is the new suspension point.
    suspended: bool = True


@dataclass
class Generator:
    """A generator's lifecycle as a sequence of yield points.

    The generator is in one of three states:

      * **Fresh**: created via ``def gen(): yield ...`` but not yet
        iterated.  The first ``next(g)`` runs to the first yield.
      * **Suspended**: paused at a yield point, awaiting a
        ``next``/``send``.
      * **Exhausted**: ran past the final yield and returned (or
        raised :class:`StopIteration`).  Re-iterating gives nothing.

    Each transition is a path:

      Fresh ─[run-to-first-yield]→ Suspended(0)
      Suspended(N) ─[next/send]─→ Suspended(N+1) | Exhausted

    Composition of these paths yields the *whole* generator's path,
    which is the kernel-level :class:`PathComp` chain of
    ``EffectWitness("yield:N", ...)`` terms.
    """
    name: str
    yields: list[YieldPoint] = field(default_factory=list)
    exhausted: bool = False
    # Cell-level identity in the heap (so a generator can be
    # aliased like any other cell — but re-iterating an alias
    # exhausts the same one-shot underlying state).
    cell_id: Optional[int] = None

    @property
    def current_index(self) -> int:
        """Index of the currently-suspended yield (-1 if fresh)."""
        for y in self.yields:
            if y.suspended:
                return y.index
        return -1

    def advance(self) -> Optional[YieldPoint]:
        """Resume past the current suspension point.  Returns the
        new yield point (or None if exhausted)."""
        cur = self.current_index
        if cur < 0:
            # Fresh: become suspended at index 0 if any yields.
            if self.yields:
                self.yields[0].suspended = True
                return self.yields[0]
            self.exhausted = True
            return None
        # Move suspension to next index.
        self.yields[cur].suspended = False
        next_idx = cur + 1
        if next_idx < len(self.yields):
            self.yields[next_idx].suspended = True
            return self.yields[next_idx]
        self.exhausted = True
        return None

    def add_yield(self, value_repr: str, *, line: int, world_epoch: int) -> YieldPoint:
        idx = len(self.yields)
        yp = YieldPoint(
            index=idx,
            value_repr=value_repr,
            line_no=line,
            world_epoch=world_epoch,
            suspended=False,  # not yet at this yield
        )
        self.yields.append(yp)
        return yp


@dataclass
class GeneratorRegistry:
    """Tracks every generator referenced in a PSDL block.

    Indexed by name so the compiler can look up and update the
    generator's state when ``next(g)`` / ``g.send(v)`` / ``g.close()``
    is called.  When a generator is aliased, both names share the
    same registry entry — ``advance()`` through one exhausts the
    other (matching Python runtime).
    """
    generators: dict[str, Generator] = field(default_factory=dict)
    # name → name resolution (alias map at the registry level).
    aliases: dict[str, str] = field(default_factory=dict)

    def resolve(self, name: str) -> str:
        """Follow alias links to the canonical generator name."""
        seen: set[str] = set()
        cur = name
        while cur in self.aliases and cur not in seen:
            seen.add(cur)
            cur = self.aliases[cur]
        return cur

    def get(self, name: str) -> Optional[Generator]:
        return self.generators.get(self.resolve(name))

    def declare(self, name: str, *, line: int = 0) -> Generator:
        """Declare a fresh generator under ``name``."""
        canonical = self.resolve(name)
        if canonical in self.generators:
            return self.generators[canonical]
        g = Generator(name=canonical)
        self.generators[canonical] = g
        return g

    def alias(self, dst: str, src: str) -> None:
        """Make ``dst`` reference the same generator as ``src``."""
        canonical = self.resolve(src)
        self.aliases[dst] = canonical

    def add_yield_to(
        self, name: str, value_repr: str, *, line: int, world_epoch: int,
    ) -> YieldPoint:
        g = self.get(name)
        if g is None:
            g = self.declare(name, line=line)
        return g.add_yield(value_repr, line=line, world_epoch=world_epoch)

    def advance(self, name: str) -> Optional[YieldPoint]:
        g = self.get(name)
        if g is None:
            return None
        return g.advance()


# ───────────────────────────────────────────────────────────────────
#  PSDL primitives: callable from PSDL source via the compiler hook
# ───────────────────────────────────────────────────────────────────

def emit_yield_witness(value_repr: str, index: int, *, world_epoch: int):
    """Build an ``EffectWitness`` recording one ``yield`` step.

    Returns a kernel ProofTerm.  Callers chain these via ``PathComp``
    to obtain the whole generator's world-path.
    """
    from deppy.core.kernel import EffectWitness, Refl
    from deppy.core.types import Var
    return EffectWitness(
        effect=f"yield:{index}@epoch{world_epoch}",
        proof=Refl(Var(f"_yield_{index}_{value_repr[:24]}")),
    )


def emit_advance_witness(g: Generator, *, line: int):
    """Build a kernel artefact for ``next(g)`` / ``g.send(v)``.

    Returns a ``Cut`` whose lemma is the current yield point and
    whose body is the resumption.
    """
    from deppy.core.kernel import Cut, Refl, EffectWitness
    from deppy.core.types import Var, PyObjType
    cur = g.current_index
    if cur < 0 and g.yields:
        cur = 0
    if cur < 0 or g.exhausted:
        # Fresh-and-empty or exhausted: produce a Structural marker
        # so the kernel sees "no yield available".
        from deppy.core.kernel import Structural
        return Structural(f"generator {g.name}: exhausted (line {line})")
    yp = g.yields[cur]
    return Cut(
        hyp_name=f"_yield_{g.name}_{cur}",
        hyp_type=PyObjType(),
        lemma_proof=EffectWitness(
            effect=f"yield:{cur}@epoch{yp.world_epoch}",
            proof=Refl(Var(yp.value_repr[:24] or "_y")),
        ),
        body_proof=Refl(Var(f"_resume_{g.name}_{cur}")),
    )


__all__ = [
    "YieldPoint",
    "Generator",
    "GeneratorRegistry",
    "emit_yield_witness",
    "emit_advance_witness",
]
