"""Single-file deppy/PSDL proof exercise: properties of a binary min-heap.

The previous BST exercise (``examples/bst_proof.py``) tested a
pointer-based recursive ADT.  This one tests an *array-based*
mutable structure with explicit loop invariants — a different cross-
section of deppy's surface.

What we attempt:

  1. Specify the heap invariant: ``∀ i. data[i] ≤ data[2i+1]`` and
     ``data[i] ≤ data[2i+2]`` whenever the children are in range.
  2. Prove ``push`` preserves the heap invariant (sift-up loop).
  3. Prove ``pop`` returns the minimum and preserves the heap
     invariant (sift-down loop).
  4. Prove ``push`` followed by ``pop`` is the identity on a single
     element: a *real* round-trip property.

Run via::

    python -m deppy check examples/heap_proof.py --verbose

Pain points expected (different from the BST set):

  * Loop invariants on ``while`` loops — different from structural
    induction.
  * Array index bounds — Z3 can model ``list[int]`` but reasoning
    about ``data[parent(i)] ≤ data[i]`` for symbolic ``i`` is hard.
  * Mutation — ``self._data.append(...)`` and ``self._data[i], self._data[j] = ...``.
  * Termination measure — sift_up's ``i`` decreases monotonically;
    sift_down's ``i`` strictly grows.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from deppy.proofs.sidecar_decorators import (
    foundation, axiom, verify, spec, psdl_proof, code_type,
)
from deppy import requires, ensures, guarantee, pure, invariant


# ═══════════════════════════════════════════════════════════════════
#  §1  Foundations — the heap invariant
# ═══════════════════════════════════════════════════════════════════
#
# We write the heap-shape invariant as a foundation citation.  Z3
# can encode ``∀ i. 0 ≤ i < n → data[2i+1 < n] data[i] ≤ data[2i+1]``
# directly using the typed encoder + axiom propagation (item 9 of
# the punch-list).

@foundation
def Heap_invariant():
    """is_heap(d) := ∀ i. 0 ≤ i ∧ 2i+1 < len(d) → d[i] ≤ d[2i+1]
                       ∀ i. 0 ≤ i ∧ 2i+2 < len(d) → d[i] ≤ d[2i+2]"""


@foundation
def Heap_root_is_min():
    """is_heap(d) ∧ len(d) > 0 → d[0] = min(d)"""


@foundation
def Heap_sift_up_terminates():
    """sift_up(d, i) terminates because i strictly decreases."""


@foundation
def Heap_sift_down_terminates():
    """sift_down(d, i) terminates because the chosen child index
       strictly exceeds i, growing toward len(d)."""


@foundation
def Heap_push_preserves_invariant():
    """is_heap(d) ⇒ is_heap(push(d, x))"""


@foundation
def Heap_pop_preserves_invariant():
    """is_heap(d) ∧ len(d) > 0 ⇒ is_heap(pop(d))"""


@foundation
def Heap_push_pop_singleton():
    """For an empty heap, push(x) then pop returns x."""


@foundation
def Int_min_geq_first():
    """min(a, b) ≤ a"""


@foundation
def Int_min_geq_second():
    """min(a, b) ≤ b"""


# ── Code-type declarations ──────────────────────────────────────────

code_type("is_heap", "list[int] → bool")(None)
code_type("size", "list[int] → int")(None)


# ═══════════════════════════════════════════════════════════════════
#  §2  Helper predicates — the heap shape
# ═══════════════════════════════════════════════════════════════════

@pure
def _parent(i: int) -> int:
    """Index of the parent of position i (i > 0)."""
    return (i - 1) // 2


@pure
def _left_child(i: int) -> int:
    """Index of the left child of position i."""
    return 2 * i + 1


@pure
def _right_child(i: int) -> int:
    """Index of the right child of position i."""
    return 2 * i + 2


@pure
def is_heap(data: list[int]) -> bool:
    """Heap invariant: every parent ≤ its children.

    Pain point #1 (heap-shape): this is a quantified predicate over
    a list, with arithmetic (2i+1, 2i+2) inside.  The Z3 typed
    encoder can express the ∀, but the *symbolic* index pattern
    (relating data[i] to data[2i+1]) requires the encoder to keep
    array-of-int relationships across the multiplication, which is
    an SMT corner.
    """
    n = len(data)
    for i in range(n):
        left = 2 * i + 1
        right = 2 * i + 2
        if left < n and data[i] > data[left]:
            return False
        if right < n and data[i] > data[right]:
            return False
    return True


# ═══════════════════════════════════════════════════════════════════
#  §3  The MinHeap class — array-based min-heap
# ═══════════════════════════════════════════════════════════════════

@spec(
    guarantees=[
        "is_heap(self._data)",
    ],
    invariants=[
        # Class invariant — declared on the spec, but checked at
        # method exits via deppy's invariant machinery.
        "is_heap(self._data)",
    ],
)
@dataclass
class MinHeap:
    """Array-based min-heap.

    The data is stored in a single list with the standard array-heap
    convention: parent of index i is (i-1)//2; children of i are 2i+1
    and 2i+2.

    Pain point #2 (mutable dataclass): @dataclass with a default-factory
    list field works at the Python level, but deppy's @spec-on-class
    machinery doesn't currently inspect ``__init__`` to verify the
    invariant on the empty heap.  We rely on the user starting from
    an empty (or already-valid) heap.
    """
    _data: list[int] = field(default_factory=list)

    # ── Length & peek ──────────────────────────────────────────────

    @ensures(lambda self, result: result == len(self._data))
    def __len__(self) -> int:
        return len(self._data)

    @requires(lambda self: len(self._data) > 0)
    @ensures(lambda self, result: result == self._data[0])
    @ensures(lambda self, result: all(result <= x for x in self._data))
    def peek(self) -> int:
        """Min element (the root) without removing it.

        Pain point #3 (∀ over self field): the second @ensures says
        the result is a lower bound on every element.  This needs
        ``is_heap`` to imply ``data[0] ≤ data[i]`` for all i, which
        is *itself* a non-trivial corollary (Heap_root_is_min).
        """
        return self._data[0]

    # ── Push ────────────────────────────────────────────────────────

    @requires(lambda self, x: is_heap(self._data))
    @ensures(lambda self, x, result: is_heap(self._data))
    @ensures(lambda self, x, result: len(self._data) ==
                                        len(self._data) + 1 - 1)  # tautology — see pain point
    def push(self, x: int) -> None:
        """Insert x and restore the heap property.

        Pain point #4 (post-conditions on mutating methods): the
        @ensures sees ``self._data`` *after* the method runs.  But
        the requires sees it *before*.  There's no way to refer to
        "old self._data" in the @ensures — Python lambdas can't
        capture pre-state easily.  Workaround: write a tautological
        post-condition or duplicate state at method start.
        """
        self._data.append(x)
        self._sift_up(len(self._data) - 1)

    @verify(
        property="is_heap(self._data) ⇒ is_heap(push(self, x))",
        via="foundation Heap_push_preserves_invariant",
        binders={"self": "MinHeap", "x": "int"},
    )
    @psdl_proof("""
# Pain point #5 (loop invariant for sift-up):
# After ``self._data.append(x)``, _data has length n+1 with x at
# the end.  sift_up walks up by parent indices, swapping while
# the parent is greater.  The loop invariant: every position
# *not on the path from end to current* still satisfies the heap
# property, AND the path is "almost" valid — only the relation
# between current and its parent could be violated.
#
# Stating this requires a sub-predicate.  PSDL has no syntax
# for "let invariant := ... ; while loop holds invariant".
# We invoke the foundation as an axiom.
apply(Heap_push_preserves_invariant)
assert is_heap(self._data), "by foundation Heap_push_preserves_invariant"
""")
    def push_preserves_heap(self):
        """Verify block — push preserves the heap invariant."""

    @requires(lambda self, i: 0 <= i < len(self._data))
    @ensures(lambda self, i, result: is_heap(self._data))
    def _sift_up(self, i: int) -> None:
        """Restore heap by swapping i upward toward its parent.

        Pain point #6 (loop bounds change inside the loop): ``i``
        is reassigned inside the while-body.  deppy's exception-
        source analyzer needs to know that after ``i = parent``,
        the value ``i`` is in [0, len(_data)).  Type-narrowing
        catches None checks (P3 fix), but doesn't track integer
        bounds — those would need a numerical-range analyzer.
        """
        while i > 0:
            parent = _parent(i)
            if self._data[parent] <= self._data[i]:
                break
            self._data[parent], self._data[i] = (
                self._data[i], self._data[parent],
            )
            i = parent

    # ── Pop ─────────────────────────────────────────────────────────

    @requires(lambda self: len(self._data) > 0)
    @requires(lambda self: is_heap(self._data))
    @ensures(lambda self, result: is_heap(self._data))
    @ensures(lambda self, result: True)  # would say "result == old_min"
    def pop(self) -> int:
        """Remove and return the min element.

        Pain point #7 (referring to "old min" in @ensures): we
        want to say ``result == old(self._data[0])`` where ``old``
        captures the pre-state.  Python lambdas don't have a way
        to express this without caller-side rewriting.
        """
        if len(self._data) == 1:
            return self._data.pop()
        result = self._data[0]
        self._data[0] = self._data.pop()
        self._sift_down(0)
        return result

    @verify(
        property="is_heap(self._data) ∧ len(self._data) > 0 ⇒ is_heap(pop(self))",
        via="foundation Heap_pop_preserves_invariant",
        binders={"self": "MinHeap"},
    )
    @psdl_proof("""
# Same pattern as push_preserves_heap — appeal to the foundation.
apply(Heap_pop_preserves_invariant)
assert is_heap(self._data), "by foundation Heap_pop_preserves_invariant"
""")
    def pop_preserves_heap(self):
        """Verify block — pop preserves the heap invariant."""

    @requires(lambda self, i: 0 <= i < len(self._data))
    @ensures(lambda self, i, result: is_heap(self._data))
    def _sift_down(self, i: int) -> None:
        """Restore heap by swapping i downward toward smaller child.

        Pain point #8 (chooses min of two children): the inner
        ``if/else`` selects between left and right based on which
        is smaller.  Z3 can encode ``min(a, b)``, but the proof
        that "after swap, heap property holds at i and at the
        child we swapped with" requires step-by-step Hoare-style
        reasoning.
        """
        n = len(self._data)
        while True:
            left = _left_child(i)
            right = _right_child(i)
            smallest = i
            if left < n and self._data[left] < self._data[smallest]:
                smallest = left
            if right < n and self._data[right] < self._data[smallest]:
                smallest = right
            if smallest == i:
                break
            self._data[i], self._data[smallest] = (
                self._data[smallest], self._data[i],
            )
            i = smallest


# ═══════════════════════════════════════════════════════════════════
#  §4  Round-trip property — push then pop for empty heap
# ═══════════════════════════════════════════════════════════════════

@guarantee("push then pop on an empty heap returns the pushed element")
@ensures(lambda x, result: result == x)
def push_pop_singleton(x: int) -> int:
    """Round-trip: empty heap, push x, immediately pop, get x.

    Pain point #9 (no module-level state in proofs): we have to
    create a fresh heap inside the function, which means the
    function isn't pure (it has a heap-allocation effect).  The
    @pure decorator wouldn't apply.  But the *result* is purely
    determined by ``x``, so the @ensures is logically valid.
    """
    h = MinHeap()
    h.push(x)
    return h.pop()


@verify(
    property="push_pop_singleton(x) == x",
    via="foundation Heap_push_pop_singleton",
    binders={"x": "int"},
)
@psdl_proof("""
# This *should* discharge by simple unfolding: push(empty, x) yields
# a 1-element heap [x]; pop on a 1-element heap returns the only
# element.  No arithmetic, no loop invariant.
#
# But PSDL has no inlining tactic — we'd have to manually unfold
# both push and pop.  Pain point #10 (no automatic unfold for
# pure-shape methods).
apply(Heap_push_pop_singleton)
assert push_pop_singleton(x) == x, "by foundation Heap_push_pop_singleton"
""")
def push_pop_returns_pushed():
    """Verify block — the round-trip property."""


# ═══════════════════════════════════════════════════════════════════
#  §5  Sanity check — actually use the heap
# ═══════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    h = MinHeap()
    inputs = [5, 3, 8, 1, 4, 7, 9, 2, 6]
    for x in inputs:
        h.push(x)
    assert is_heap(h._data), f"invariant violated: {h._data}"
    assert len(h) == len(inputs)

    out = []
    while len(h) > 0:
        out.append(h.pop())
    assert out == sorted(inputs), f"not sorted: {out}"
    assert push_pop_singleton(42) == 42
    print("Min-heap sanity check passed.")
