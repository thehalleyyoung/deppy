"""Single-file deppy/PSDL proof exercise: properties of a binary search tree.

This file *exercises* the deppy/PSDL system as a normal user would.  We
specify a BST data type, an insert/find/contains/size operation set,
and progressively richer properties — then ask deppy to verify them.

The goal is not to prove everything; it's to surface *pain points* in
real usage of deppy/PSDL today.  Each section below has a brief note
about what we expect deppy to do well and what we expect it to
struggle with.

Run via::

    python -m deppy check examples/bst_proof.py --verbose

We avoid the ``.deppy`` sidecar workflow — every annotation lives
inline alongside the code it describes.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from deppy.proofs.sidecar_decorators import (
    foundation, axiom, verify, spec, psdl_proof, code_type,
)
from deppy import requires, ensures, guarantee, pure


# ═══════════════════════════════════════════════════════════════════
#  §1  The BST data type
# ═══════════════════════════════════════════════════════════════════
#
# We use Optional[BST] for nullable subtrees.  A leaf is just a node
# with both children None.  This is the standard recursive shape;
# deppy's ``register_recursive_class`` (item 9) should let Z3 reason
# about it structurally.

@dataclass(frozen=True)
class BST:
    """Binary search tree over integers.  Frozen so equality is by
    structure (every node is immutable; insert returns a fresh tree).
    """
    value: int
    left: Optional["BST"] = None
    right: Optional["BST"] = None


# ═══════════════════════════════════════════════════════════════════
#  §2  Foundations — the BST invariant + helper predicates
# ═══════════════════════════════════════════════════════════════════
#
# We write the invariants as ordinary Python functions.  The hope is
# that deppy treats them as predicates and lets us *cite* them in
# @requires / @ensures clauses.  This is where we expect the first
# pain point: recursive predicates over user-defined recursive types.

@foundation
def Bst_invariant_definition():
    """is_bst(t) := t is None ∨ (left_bound(t.left, t.value)
                                 ∧ right_bound(t.right, t.value)
                                 ∧ is_bst(t.left) ∧ is_bst(t.right))"""


@foundation
def Bst_left_bound():
    """left_bound(t, v) := t is None ∨ (max_value(t) < v)"""


@foundation
def Bst_right_bound():
    """right_bound(t, v) := t is None ∨ (min_value(t) > v)"""


@foundation
def Bst_insert_preserves_invariant():
    """is_bst(t) ⇒ is_bst(insert(t, v))"""


@foundation
def Bst_find_correct():
    """find(t, v) is True iff v ∈ values(t)"""


@foundation
def Bst_size_monotone():
    """size(insert(t, v)) ∈ {size(t), size(t) + 1}"""


@foundation
def Int_lt_trans():
    """a < b ∧ b < c ⇒ a < c"""


@foundation
def Int_lt_irreflexive():
    """¬(a < a)"""


# ── Code-type declarations for symbols deppy may not infer ──────────

code_type("is_bst", "BST → Bool")(None)
code_type("contains", "BST → Int → Bool")(None)
code_type("size", "BST → Int")(None)
code_type("min_value", "BST → Int")(None)
code_type("max_value", "BST → Int")(None)


# ═══════════════════════════════════════════════════════════════════
#  §3  Helper predicates — pure Python implementations
# ═══════════════════════════════════════════════════════════════════
#
# Each is a recursive function on Optional[BST].  We mark them as
# ``@pure`` so deppy knows they're side-effect free, and we attach
# minimal contracts.

@pure
def is_bst(t: Optional[BST]) -> bool:
    """Recursive BST invariant: every node's value strictly bounds
    every left descendant from above and every right descendant from
    below.

    Pain point #1: this is a recursive predicate over a recursive
    type.  deppy's `is_arithmetic_spec` heuristic in
    `lean/compiler.py:_pick_tactic_for_spec` doesn't recognise
    "is_bst".  Z3's typed encoder (item 9) needs the recursive class
    registered before it can reason about field accesses.
    """
    if t is None:
        return True
    if t.left is not None and not _all_less(t.left, t.value):
        return False
    if t.right is not None and not _all_greater(t.right, t.value):
        return False
    return is_bst(t.left) and is_bst(t.right)


@pure
def _all_less(t: Optional[BST], v: int) -> bool:
    """Every value in subtree ``t`` is strictly less than ``v``."""
    if t is None:
        return True
    if t.value >= v:
        return False
    return _all_less(t.left, v) and _all_less(t.right, v)


@pure
def _all_greater(t: Optional[BST], v: int) -> bool:
    """Every value in subtree ``t`` is strictly greater than ``v``."""
    if t is None:
        return True
    if t.value <= v:
        return False
    return _all_greater(t.left, v) and _all_greater(t.right, v)


@pure
def size(t: Optional[BST]) -> int:
    """Number of nodes."""
    if t is None:
        return 0
    return 1 + size(t.left) + size(t.right)


# ═══════════════════════════════════════════════════════════════════
#  §4  insert — the headline proof obligation
# ═══════════════════════════════════════════════════════════════════
#
# We attempt to prove three things about insert:
#
#   1. @ensures: insert preserves is_bst.
#   2. @ensures: contains(insert(t, v), v) is True.
#   3. @ensures: size(insert(t, v)) ≤ size(t) + 1.
#
# We try the *simplest* form first — a plain @guarantee — then
# escalate to @verify with a @psdl_proof.

@guarantee("insert(t, v) is a BST when t is")
@requires(lambda t, v: is_bst(t))
@ensures(lambda t, v, result: is_bst(result))
@ensures(lambda t, v, result: contains(result, v))
@ensures(lambda t, v, result: size(result) <= size(t) + 1)
def insert(t: Optional[BST], v: int) -> BST:
    """Insert v into BST t.  Returns the modified tree.

    Pain point #2: the @ensures lambdas reference ``is_bst`` and
    ``contains`` — user-defined recursive predicates.  deppy's
    refinement compiler (item 5) can translate the surface syntax
    to Lean ∀/∃ but it can't *discharge* the obligations because
    the inductive structure of ``insert``-on-BST isn't in the
    tactic library (item 6).  We expect deppy to emit ``sorry``
    here and rely on the @psdl_proof block below to manually
    structure the induction.
    """
    if t is None:
        return BST(value=v)
    if v < t.value:
        return BST(value=t.value, left=insert(t.left, v), right=t.right)
    if v > t.value:
        return BST(value=t.value, left=t.left, right=insert(t.right, v))
    return t  # v already present — tree unchanged


@axiom(
    target="examples.bst_proof.insert",
    statement="is_bst(t) → is_bst(insert(t, v))",
    module="examples",
)
def insert_preserves_bst_axiom():
    """The deppy-axiom restating the invariant."""


@verify(
    property="is_bst(t) → is_bst(insert(t, v))",
    via="foundation Bst_insert_preserves_invariant",
    binders={"t": "Optional[BST]", "v": "int"},
)
@psdl_proof("""
# Pain point #3: PSDL syntax for structural induction over a recursive
# user type.  We want to say "induct on t, showing the property holds
# for None, and assuming it holds for t.left and t.right, conclude it
# holds for the constructor case."  The ``induction_on_list`` tactic
# from item 6 doesn't apply (BST isn't a list); a tree-induction
# tactic doesn't exist.  We fall back to manual case analysis.
if t is None:
    # Base: insert(None, v) = BST(v).  is_bst(BST(v)) reduces to
    # _all_less(None, v) ∧ _all_greater(None, v) ∧ is_bst(None) ∧ is_bst(None).
    # All four are trivially True.
    apply(Bst_invariant_definition)
    assert is_bst(BST(value=v)), "qed"
else:
    # Inductive step.
    case v < t.value:
        # insert(t, v) = BST(t.value, insert(t.left, v), t.right).
        # By IH on t.left, is_bst(insert(t.left, v)).
        # By premise, is_bst(t.right) and (the bound) _all_greater(t.right, t.value).
        # We additionally need _all_less(insert(t.left, v), t.value)
        # — the inserted v is < t.value (by case), and the IH on
        # _all_less(t.left, v) preserves the bound.  Pain point #4:
        # *this* sub-obligation about bound preservation isn't a
        # foundation we cite — we'd have to introduce another lemma.
        apply(Bst_invariant_definition)
        assert _all_less(insert(t.left, v), t.value), "z3"
        assert is_bst(insert(t.left, v)), "by foundation Bst_insert_preserves_invariant"
        # symmetric reasoning for the right side
    case v > t.value:
        apply(Bst_invariant_definition)
        assert _all_greater(insert(t.right, v), t.value), "z3"
        assert is_bst(insert(t.right, v)), "by foundation Bst_insert_preserves_invariant"
    case v == t.value:
        # insert(t, v) = t, the invariant is preserved trivially.
        assert insert(t, v) == t, "rfl"
""")
def insert_preserves_bst():
    """Verify block — the proof obligation insert_preserves_bst."""


# ═══════════════════════════════════════════════════════════════════
#  §5  contains — find a value in the tree
# ═══════════════════════════════════════════════════════════════════

@guarantee("contains(t, v) iff v is in the tree's value set")
@requires(lambda t, v: is_bst(t))
@ensures(lambda t, v, result: result == _value_in_tree(t, v))
def contains(t: Optional[BST], v: int) -> bool:
    """Find v in BST t."""
    if t is None:
        return False
    if v == t.value:
        return True
    if v < t.value:
        return contains(t.left, v)
    return contains(t.right, v)


@pure
def _value_in_tree(t: Optional[BST], v: int) -> bool:
    """Naive recursive membership: traverses the entire tree."""
    if t is None:
        return False
    if t.value == v:
        return True
    return _value_in_tree(t.left, v) or _value_in_tree(t.right, v)


@verify(
    property="is_bst(t) → contains(t, v) == _value_in_tree(t, v)",
    via="foundation Bst_find_correct",
    binders={"t": "Optional[BST]", "v": "int"},
)
@psdl_proof("""
# Pain point #5: this property is true *only because* of the BST
# invariant — `contains` walks one branch but `_value_in_tree` checks
# both.  Their agreement requires inducting on t and using the
# is_bst hypothesis to argue that v can't be in the subtree we
# skipped.  PSDL has no built-in `inversion` tactic for is_bst — we
# can apply the foundation, but the structural induction step isn't
# automated.
if t is None:
    assert contains(None, v) == False, "rfl"
    assert _value_in_tree(None, v) == False, "rfl"
else:
    case v == t.value:
        assert contains(t, v) == True, "qed"
        assert _value_in_tree(t, v) == True, "qed"
    case v < t.value:
        # By BST invariant, v ∉ t.right, so _value_in_tree(t.right, v) == False.
        # Therefore _value_in_tree(t, v) == _value_in_tree(t.left, v).
        assert _all_greater(t.right, t.value), "by foundation Bst_invariant_definition"
        assert v < t.value, "qed"
        # Pain point #6: chaining ``_all_greater(t.right, t.value)``
        # and ``v < t.value`` to conclude ``v ∉ t.right``.  This is
        # transitivity of <, which Bst_left_bound captures, but
        # PSDL has no automated chaining of foundation lemmas — we
        # must spell each step.
        assert not _value_in_tree(t.right, v), "by foundation Bst_left_bound"
        # Now contains(t, v) == contains(t.left, v) and
        # _value_in_tree(t, v) == _value_in_tree(t.left, v), so the
        # IH closes.
        apply(Bst_find_correct)
    case v > t.value:
        # symmetric
        assert _all_less(t.left, t.value), "by foundation Bst_invariant_definition"
        assert v > t.value, "qed"
        assert not _value_in_tree(t.left, v), "by foundation Bst_right_bound"
        apply(Bst_find_correct)
""")
def contains_correct():
    """Verify block — `contains` agrees with naive membership."""


# ═══════════════════════════════════════════════════════════════════
#  §6  Round-trip — insert then find
# ═══════════════════════════════════════════════════════════════════
#
# The cleanest round-trip property: contains(insert(t, v), v) is True.

@guarantee("contains(insert(t, v), v) is True")
@requires(lambda t, v: is_bst(t))
def insert_then_contains(t: Optional[BST], v: int) -> bool:
    """Helper to expose the round-trip as a verifiable function."""
    return contains(insert(t, v), v)


@verify(
    property="is_bst(t) → contains(insert(t, v), v) == True",
    via="foundation Bst_find_correct",
    binders={"t": "Optional[BST]", "v": "int"},
)
@psdl_proof("""
# Pain point #7: this property *should* be discharged via a chain
# of three foundations:
#   (a) insert preserves is_bst,
#   (b) v ∈ values(insert(t, v))   — by definition of insert,
#   (c) contains agrees with _value_in_tree.
# But chaining (a) → (b) → (c) is a manual `apply ; apply ; apply`
# sequence.  We don't have a `chain_lemmas` tactic.  Each step is
# its own assert.
apply(Bst_insert_preserves_invariant)
assert is_bst(insert(t, v)), "qed"
assert _value_in_tree(insert(t, v), v) == True, "by foundation Bst_invariant_definition"
assert contains(insert(t, v), v) == _value_in_tree(insert(t, v), v), "by foundation Bst_find_correct"
assert contains(insert(t, v), v) == True, "qed"
""")
def insert_then_contains_returns_true():
    """The headline round-trip theorem."""


# ═══════════════════════════════════════════════════════════════════
#  §7  Size invariants
# ═══════════════════════════════════════════════════════════════════

@guarantee("size(insert(t, v)) is size(t) or size(t)+1")
@requires(lambda t, v: is_bst(t))
@ensures(lambda t, v, result: size(result) == size(t)
                          or size(result) == size(t) + 1)
def insert_with_size_bound(t: Optional[BST], v: int) -> BST:
    """Same as insert; size grows by 0 (already-present) or 1."""
    return insert(t, v)


@verify(
    property=("size(insert(t, v)) == size(t) "
              "or size(insert(t, v)) == size(t) + 1"),
    via="foundation Bst_size_monotone",
    binders={"t": "Optional[BST]", "v": "int"},
)
@psdl_proof("""
# Pain point #8: arithmetic-on-recursive-function is hard to discharge.
# size(insert(t, v)) unfolds via the same case split as insert; each
# branch produces a structural equality (or +1).  The Z3 typed encoder
# can handle ``size(t) == k`` for concrete k, but for symbolic
# "size(t) is whatever it is", we'd need omega+unfold combined.
if t is None:
    assert size(insert(None, v)) == 1, "rfl"
    assert size(None) == 0, "rfl"
    assert size(BST(v)) == 1, "by foundation Bst_invariant_definition"
else:
    case v == t.value:
        assert insert(t, v) == t, "rfl"
        assert size(insert(t, v)) == size(t), "qed"
    case v < t.value:
        # size(insert) = 1 + size(insert(t.left, v)) + size(t.right).
        # By IH, size(insert(t.left, v)) is size(t.left) or +1.
        # So total is size(t) or size(t) + 1.
        apply(Bst_size_monotone)
        assert (size(insert(t.left, v)) == size(t.left)
                or size(insert(t.left, v)) == size(t.left) + 1), "qed"
    case v > t.value:
        apply(Bst_size_monotone)
        assert (size(insert(t.right, v)) == size(t.right)
                or size(insert(t.right, v)) == size(t.right) + 1), "qed"
""")
def insert_size_bounded():
    """Verify block — insert grows size by at most 1."""


# ═══════════════════════════════════════════════════════════════════
#  §8  Z3 encoder registration — make trees known to Z3
# ═══════════════════════════════════════════════════════════════════
#
# Pain point #9: this registration is a side-effect that must run
# *before* deppy invokes Z3.  We do it at import time; deppy's check
# command imports the module first, so this works — but it's
# fragile.  A registration syntax like @recursive_z3 on the BST
# class would be more discoverable.

try:
    from deppy.core.z3_encoder import register_recursive_class
    register_recursive_class(BST)
except Exception:
    # Z3 not installed, or the registration API moved — graceful
    # degradation.
    pass


# ═══════════════════════════════════════════════════════════════════
#  §9  Sanity check — actually run the operations
# ═══════════════════════════════════════════════════════════════════
#
# This isn't part of the formal proof; it's a runtime check that
# our definitions agree with our intent.

if __name__ == "__main__":
    # Build a small BST: 5, 3, 8, 1, 4, 7, 9.
    t: Optional[BST] = None
    for v in [5, 3, 8, 1, 4, 7, 9]:
        t = insert(t, v)
    assert is_bst(t)
    assert size(t) == 7
    for v in [5, 3, 8, 1, 4, 7, 9]:
        assert contains(t, v)
    for v in [0, 2, 6, 10, 100]:
        assert not contains(t, v)
    # Round-trip.
    t2 = insert(t, 6)
    assert is_bst(t2)
    assert contains(t2, 6)
    assert size(t2) == 8
    # Already-present.
    t3 = insert(t, 5)
    assert is_bst(t3)
    assert size(t3) == 7
    print("BST sanity check passed.")
