"""Cubical heap / effect model for PSDL.

A *heap world* is treated as a point in a universe of worlds.  Each
mutation produces a **path** between two worlds; pure expressions are
**reflexivity** on the world.  Aliasing is a **DuckPath** at the cell
level: two names referring to the same cell are read-equivalent under
the path-of-the-current-world.  Reading through an alias after a
mutation requires a **transport** along the mutation path; absent the
transport, the proof inhabits the wrong world and the kernel rejects.

This module uses the kernel primitives that already exist in
:mod:`deppy.core.kernel`:

  * ``EffectWitness(effect="mutate:NAME@epoch_N", ...)`` — a mutation
    is an effect in the ◇ modality, indexed by the mutated name and
    the new world epoch.
  * ``DuckPath(type_a, type_b, method_proofs=[("read", Refl(...))])``
    — aliasing as a path equivalence at the read interface.
  * ``TransportProof(motive, mutation_path, base_proof)`` — moving a
    proof past a mutation: the motive is the invariant being
    transported; the path is the mutation; the base is the
    pre-mutation proof.
  * ``Cut`` to chain world-changing steps so trust composes.

We don't introduce new kernel terms — we *use* the cubical vocabulary
already present.  The heap itself is a piece of *meta-data* threaded
through the PSDL compiler; it parameterises which kernel terms get
constructed.

Mathematical sketch
-------------------

Worlds form a directed graph: each node is an epoch, each edge is a
mutation path.  An alias group is a fibre over a cell.  Reading a
name in world W produces a proof of the form
``Reads(name, W) : V``; the same name in world W' produces
``Reads(name, W') : V``.  These types are **identified** if W ≃ W'
(no mutation happened to the cell between W and W').  The
identification is established via ``Refl`` if W = W' literally, or
``TransportProof`` along the mutation path.

The cocycle condition (associativity of mutation paths) is automatic
because the kernel's ``PathComp`` is associative.

Cubical-effect modality
-----------------------

Pure expressions are ``□`` (Box): no world change.  Effectful
expressions are ``◇`` (Diamond): they live in the exception/mutation
fibre.  PSDL's ``raise`` was already modelled as ``EffectWitness(
"exception:E", ...)``; mutations are now modelled as ``EffectWitness(
"mutate:X@N", ...)`` with the same modality structure.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterator

# These methods are conventionally mutating in CPython.  Calling any
# of them on a list/dict/set/object updates the heap in place.
MUTATING_METHODS: frozenset[str] = frozenset({
    # list
    "append", "extend", "pop", "remove", "clear", "insert",
    "sort", "reverse",
    # dict
    "update", "popitem", "setdefault", "pop", "clear",
    # set
    "add", "discard", "remove", "pop", "clear", "update",
    "intersection_update", "difference_update",
    "symmetric_difference_update",
    # generic / convention
    "__setattr__", "__delattr__", "__setitem__", "__delitem__",
})


@dataclass
class CellInvariant:
    """A proof-relevant fact about a heap cell, established at a
    specific world epoch.

    The kernel's ``TransportProof`` is needed to use the invariant in
    a later epoch — *only when the cell was mutated in between*.
    """
    # The Python expression / claim that's held to be true.
    predicate: str
    # The world epoch at which this invariant was established.
    established_at_epoch: int
    # The line number where the invariant was registered.
    source_line: int = 0


@dataclass
class HeapCell:
    """An object in the heap.  Each cell has a stable identity (its
    ``id``) and a set of invariants that hold in some prefix of the
    epoch sequence.
    """
    id: int
    type_tag: str = "object"
    invariants: list[CellInvariant] = field(default_factory=list)
    # Epochs at which this cell was mutated.  Useful for diagnostic
    # messages and for the kernel's transport requirement.
    mutated_at: list[int] = field(default_factory=list)


@dataclass
class World:
    """A snapshot of the runtime heap at a specific epoch.

    Invariants form a *fibre* over each cell: facts you can rely on
    when reading from any name pointing at that cell.  The world's
    epoch increments on every mutation; reading at an old epoch
    requires transport.
    """
    epoch: int = 0
    # Each Python name maps to the cell ID it currently references.
    name_to_cell: dict[str, int] = field(default_factory=dict)
    # The cells themselves.  Keyed by ID so multiple names can
    # share a cell (aliasing).
    cells: dict[int, HeapCell] = field(default_factory=dict)
    # Monotonic counter for fresh cell IDs.
    _next_id: int = 0

    def alloc(self, type_tag: str = "object") -> int:
        """Allocate a new cell and return its ID."""
        cid = self._next_id
        self._next_id += 1
        self.cells[cid] = HeapCell(id=cid, type_tag=type_tag)
        return cid

    def bind(self, name: str, cell_id: int) -> None:
        """Bind ``name`` to point at the given cell."""
        self.name_to_cell[name] = cell_id

    def alias(self, dst: str, src: str) -> bool:
        """Make ``dst`` point at the same cell as ``src``.  Returns
        True when an alias was actually established (i.e. ``src`` is
        bound)."""
        cid = self.name_to_cell.get(src)
        if cid is None:
            return False
        self.name_to_cell[dst] = cid
        return True

    def cell_of(self, name: str) -> HeapCell | None:
        cid = self.name_to_cell.get(name)
        if cid is None:
            return None
        return self.cells.get(cid)

    def aliases_of(self, name: str) -> set[str]:
        """All names currently pointing at the same cell as ``name``
        (including ``name`` itself)."""
        cid = self.name_to_cell.get(name)
        if cid is None:
            return {name}
        return {n for n, c in self.name_to_cell.items() if c == cid}

    def mutate(self, name: str, *, line: int = 0) -> set[str]:
        """Record a mutation through ``name``.  Bumps the epoch,
        records the mutation on the cell, and returns the set of
        affected (aliased) names so the caller can invalidate proofs.
        """
        cid = self.name_to_cell.get(name)
        if cid is None:
            # Mutating an unknown name — allocate a fresh cell so
            # the rest of the analysis sees something.
            cid = self.alloc()
            self.name_to_cell[name] = cid
        self.epoch += 1
        cell = self.cells[cid]
        cell.mutated_at.append(self.epoch)
        affected = {n for n, c in self.name_to_cell.items() if c == cid}
        # Drop invariants — they were proven at the old epoch.
        cell.invariants = [
            inv for inv in cell.invariants
            if inv.established_at_epoch >= self.epoch
        ]
        return affected

    def add_invariant(
        self, name: str, predicate: str, *, line: int = 0,
    ) -> None:
        """Register an invariant on the cell currently bound to
        ``name``."""
        cell = self.cell_of(name)
        if cell is None:
            cid = self.alloc()
            self.name_to_cell[name] = cid
            cell = self.cells[cid]
        cell.invariants.append(CellInvariant(
            predicate=predicate,
            established_at_epoch=self.epoch,
            source_line=line,
        ))

    def invariants_at(self, name: str, *, epoch: int) -> list[CellInvariant]:
        """Invariants on ``name``'s cell that are still valid at the
        given epoch (i.e. no mutation happened to the cell since the
        invariant was registered).
        """
        cell = self.cell_of(name)
        if cell is None:
            return []
        # Mutations strictly after the invariant's epoch break it.
        out: list[CellInvariant] = []
        for inv in cell.invariants:
            if inv.established_at_epoch <= epoch:
                # Was the cell mutated between inv.established_at_epoch
                # and epoch (exclusive)?  If yes, the invariant is
                # broken and would need transport.
                broken = any(
                    inv.established_at_epoch < m <= epoch
                    for m in cell.mutated_at
                )
                if not broken:
                    out.append(inv)
        return out

    def transport_required(
        self, name: str, *, from_epoch: int, to_epoch: int,
    ) -> tuple[bool, list[int]]:
        """Does using a proof established at ``from_epoch`` require
        transport at ``to_epoch``?  Returns ``(needed, mutations)``
        where ``mutations`` is the list of intervening mutation
        epochs that the transport would have to bridge.
        """
        cell = self.cell_of(name)
        if cell is None:
            return False, []
        bridging = [
            m for m in cell.mutated_at
            if from_epoch < m <= to_epoch
        ]
        return (bool(bridging), bridging)

    def snapshot(self) -> "World":
        """Return a shallow copy useful for emitting kernel terms."""
        return World(
            epoch=self.epoch,
            name_to_cell=dict(self.name_to_cell),
            cells={
                cid: HeapCell(
                    id=cell.id,
                    type_tag=cell.type_tag,
                    invariants=list(cell.invariants),
                    mutated_at=list(cell.mutated_at),
                )
                for cid, cell in self.cells.items()
            },
            _next_id=self._next_id,
        )


@dataclass
class Effect:
    """An effect at a program point — used for sequencing.

    Effects compose left-to-right and form a path in the world
    category.  Pure expressions emit no Effect.
    """
    line_no: int
    kind: str  # "mutate" / "raise" / "call" / "io"
    locator: str  # name affected / func called / exc type
    epoch: int  # the world epoch this effect produced


@dataclass
class EffectSequence:
    """Ordered sequence of effects within a proof block.

    The sequence is the *world path* from the block's enter epoch
    to its exit epoch.  Each Effect contributes one edge.
    Composition is automatic via the kernel's ``PathComp``.
    """
    effects: list[Effect] = field(default_factory=list)

    def append(self, e: Effect) -> None:
        self.effects.append(e)

    def __iter__(self) -> Iterator[Effect]:
        return iter(self.effects)

    def __len__(self) -> int:
        return len(self.effects)


def looks_mutating(method_name: str) -> bool:
    """Heuristic: does this method name belong to the conventional
    set of CPython mutators?  Used by the PSDL compiler to decide
    whether a method call bumps the world epoch."""
    return method_name in MUTATING_METHODS


__all__ = [
    "MUTATING_METHODS",
    "CellInvariant",
    "HeapCell",
    "World",
    "Effect",
    "EffectSequence",
    "looks_mutating",
]
