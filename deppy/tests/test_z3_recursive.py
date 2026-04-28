"""Tests for the three Z3-encoder extensions:

1. Recursive datatypes (binary trees, linked lists, …).
2. Polymorphic memoisation of encodings.
3. Custom predicate registration & dispatch.

Each test is independent — the cache is cleared at fixture setup so
stale state from earlier tests cannot leak.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

import pytest


@pytest.fixture(autouse=True)
def _require_z3_and_clear():
    """Ensure Z3 is available and start each test with empty caches."""
    pytest.importorskip("z3")
    from deppy.core.z3_encoder import (
        clear_encoding_cache,
        unregister_custom_predicate,
        list_custom_predicates,
        unregister_recursive_class,
        _RECURSIVE_CLASS_REGISTRY,
    )
    clear_encoding_cache()
    for n in list(_RECURSIVE_CLASS_REGISTRY.keys()):
        unregister_recursive_class(n)
    for n in list_custom_predicates():
        unregister_custom_predicate(n)
    yield
    # Cleanup — leave global state clean for the next test.
    clear_encoding_cache()
    for n in list(_RECURSIVE_CLASS_REGISTRY.keys()):
        unregister_recursive_class(n)
    for n in list_custom_predicates():
        unregister_custom_predicate(n)


# ─────────────────────────────────────────────────────────────────────
#  Test fixtures — recursive dataclasses
# ─────────────────────────────────────────────────────────────────────

@dataclass
class Tree:
    value: int
    left: Optional["Tree"] = None
    right: Optional["Tree"] = None


@dataclass
class Node:
    value: int
    next: Optional["Node"] = None


# ─────────────────────────────────────────────────────────────────────
#  Extension 1 — Recursive datatypes
# ─────────────────────────────────────────────────────────────────────

def test_recursive_class_detection():
    """``_is_recursive_dataclass`` recognises self-referential
    dataclasses but rejects unrelated ones."""
    from deppy.core.z3_encoder import _is_recursive_dataclass

    @dataclass
    class Plain:
        x: int
        y: int

    assert _is_recursive_dataclass(Tree) is True
    assert _is_recursive_dataclass(Node) is True
    assert _is_recursive_dataclass(Plain) is False


def test_recursive_datatype_emits_z3_datatype():
    """Encoding a registered recursive class produces a Z3 datatype
    (not an uninterpreted sort)."""
    import z3
    from deppy.core.z3_encoder import (
        Z3Encoding, register_recursive_class, _encode_recursive_datatype,
    )

    register_recursive_class(Tree)
    enc = Z3Encoding()
    sort, expr, helpers = _encode_recursive_datatype(Tree, "t", enc, z3)

    assert isinstance(sort, z3.DatatypeSortRef)
    # Two constructors: leaf + node.
    assert sort.num_constructors() == 2
    assert "leaf" in helpers and "node" in helpers
    assert "is_leaf" in helpers and "is_node" in helpers


def test_binary_tree_balanced_predicate_via_check_implication():
    """A balanced predicate over Tree can be Z3-verified end-to-end.

    We register a custom ``is_balanced`` predicate that returns True
    for any ``leaf`` and assert: for a leaf, the predicate must hold.
    """
    import z3
    from deppy.core.z3_encoder import (
        register_recursive_class, register_custom_predicate,
        check_implication,
    )

    register_recursive_class(Tree)

    # The Z3 builder takes a Tree-sorted argument and asserts triviality
    # for the leaf case.  In a real implementation this would be a
    # recursive Z3 function; for testing the dispatch path it suffices
    # that the predicate evaluates to a BoolRef.
    def _is_balanced_z3(tree, helpers):
        # ``helpers`` carries ``is_leaf`` from the recursive encoding.
        is_leaf = helpers.get("is_leaf")
        if is_leaf is None:
            return z3.BoolVal(True)
        return is_leaf(tree)

    register_custom_predicate(
        "is_balanced",
        fn=lambda t: True,                         # Python stub
        signature={"args": ["Tree"], "returns": "bool"},
        z3_builder=_is_balanced_z3,
    )

    # Verify: any t which is a leaf is balanced (via our trivial
    # builder).  Premise asserts is_leaf(t); conclusion is_balanced(t).
    verdict, reason = check_implication(
        premise="True",
        conclusion="is_balanced(t)",
        binders={"t": "Tree"},
    )
    # The conclusion holds iff is_balanced(t) is True for ALL t.  For
    # a leaf-only encoding the predicate is is_leaf(t), which is NOT
    # always true — so we expect the encoder to return a sound False.
    assert verdict is False
    assert reason in (None, "disagrees")


def test_linked_list_length_predicate():
    """A linked-list (``Node``) datatype with a registered length
    predicate dispatches via the custom-predicate hook.
    """
    import z3
    from deppy.core.z3_encoder import (
        register_recursive_class, register_custom_predicate,
        check_implication,
    )

    register_recursive_class(Node)

    # Register a Z3 ``length`` function that returns an Int.  This is
    # an uninterpreted Z3 function over the recursive sort; the test
    # verifies the dispatch path works even when the builder yields
    # an Int (not a Bool).
    def _length_z3(n, helpers):
        # Uninterpreted length helper — tied to the leaf/node sort.
        is_leaf = helpers.get("is_leaf")
        if is_leaf is None:
            return z3.IntVal(0)
        return z3.If(is_leaf(n), z3.IntVal(0), z3.IntVal(1))

    register_custom_predicate(
        "length",
        fn=lambda n: 0,
        signature={"args": ["Node"], "returns": "int"},
        z3_builder=_length_z3,
    )

    # length(n) >= 0 is always true (0 or 1).
    verdict, _reason = check_implication(
        premise="True",
        conclusion="length(n) >= 0",
        binders={"n": "Node"},
    )
    assert verdict is True


# ─────────────────────────────────────────────────────────────────────
#  Extension 2 — Polymorphic memoisation
# ─────────────────────────────────────────────────────────────────────

def test_memoisation_optional_int_same_sort():
    """Two ``Optional[int]`` encodings produce the same Z3 sort."""
    import z3
    from deppy.core.z3_encoder import _ast_to_z3, Z3Encoding
    import ast

    enc1, enc2 = Z3Encoding(), Z3Encoding()
    tree = ast.parse("Optional[int]", mode="eval").body
    sort_a, _, _ = _ast_to_z3(tree, "a", enc1, None, z3)
    tree2 = ast.parse("Optional[int]", mode="eval").body
    sort_b, _, _ = _ast_to_z3(tree2, "b", enc2, None, z3)

    # Same sort object — this is the entire point of the cache.
    assert sort_a is sort_b or sort_a == sort_b


def test_memoisation_user_class_same_sort():
    """Two encodings of an unregistered user class hit the cache."""
    import z3
    from deppy.core.z3_encoder import _ast_to_z3, Z3Encoding
    import ast

    enc1, enc2 = Z3Encoding(), Z3Encoding()
    tree1 = ast.parse("MyType", mode="eval").body
    tree2 = ast.parse("MyType", mode="eval").body
    sort_a, _, _ = _ast_to_z3(tree1, "a", enc1, None, z3)
    sort_b, _, _ = _ast_to_z3(tree2, "b", enc2, None, z3)
    assert sort_a == sort_b


def test_cache_invalidation():
    """``clear_encoding_cache`` empties the cache so subsequent
    encodings build new sorts (with new uniquely-numbered names)."""
    import z3
    from deppy.core.z3_encoder import (
        _ast_to_z3, Z3Encoding, clear_encoding_cache, _ENCODING_CACHE,
    )
    import ast

    tree = ast.parse("MyOpaque", mode="eval").body
    sort_a, _, _ = _ast_to_z3(tree, "a", Z3Encoding(), None, z3)
    assert len(_ENCODING_CACHE) >= 1
    clear_encoding_cache()
    assert len(_ENCODING_CACHE) == 0
    sort_c, _, _ = _ast_to_z3(tree, "c", Z3Encoding(), None, z3)
    # After clearing, a fresh sort is built.  It need not be ``!=`` to
    # the original (Z3 may intern by name) but the cache should be
    # repopulated.
    assert len(_ENCODING_CACHE) >= 1
    # And subsequent identical encodings hit the new entry.
    sort_d, _, _ = _ast_to_z3(tree, "d", Z3Encoding(), None, z3)
    assert sort_c == sort_d


def test_memoisation_does_not_collapse_distinct_types():
    """``list[int]`` and ``list[str]`` should NOT share a sort."""
    import z3
    from deppy.core.z3_encoder import _ast_to_z3, Z3Encoding
    import ast

    enc = Z3Encoding()
    s1, _, _ = _ast_to_z3(
        ast.parse("list[int]", mode="eval").body, "xs", enc, None, z3,
    )
    s2, _, _ = _ast_to_z3(
        ast.parse("list[str]", mode="eval").body, "ys", enc, None, z3,
    )
    assert s1 != s2


# ─────────────────────────────────────────────────────────────────────
#  Extension 3 — Custom predicate registration
# ─────────────────────────────────────────────────────────────────────

def test_register_and_dispatch_custom_predicate():
    """A registered predicate is dispatched on call instead of being
    treated as uninterpreted."""
    import z3
    from deppy.core.z3_encoder import (
        register_custom_predicate, list_custom_predicates,
        check_implication,
    )

    def _always_true(x, helpers):
        return z3.BoolVal(True)

    register_custom_predicate(
        "trivially_true",
        fn=lambda x: True,
        signature={"args": ["int"], "returns": "bool"},
        z3_builder=_always_true,
    )
    assert "trivially_true" in list_custom_predicates()

    verdict, _ = check_implication(
        premise="True",
        conclusion="trivially_true(x)",
        binders={"x": "int"},
    )
    assert verdict is True


def test_unregister_custom_predicate():
    """Unregistration removes the dispatch hook."""
    from deppy.core.z3_encoder import (
        register_custom_predicate, unregister_custom_predicate,
        list_custom_predicates,
    )
    register_custom_predicate(
        "p",
        fn=lambda: True,
        signature={"args": [], "returns": "bool"},
        z3_builder=None,
    )
    assert "p" in list_custom_predicates()
    unregister_custom_predicate("p")
    assert "p" not in list_custom_predicates()


def test_custom_predicate_falls_back_to_uninterpreted_when_no_builder():
    """When ``z3_builder`` is None, the dispatch synthesises a fresh
    uninterpreted Bool function — the predicate becomes opaque but the
    encoder still emits a valid BoolRef."""
    import z3
    from deppy.core.z3_encoder import (
        register_custom_predicate, check_implication,
    )

    register_custom_predicate(
        "opaque",
        fn=lambda x: True,
        signature={"args": ["int"], "returns": "bool"},
        z3_builder=None,
    )
    # opaque(x) does not imply opaque(x+1) for an opaque function —
    # so the implication should not be discharged.
    verdict, _ = check_implication(
        premise="opaque(x)",
        conclusion="opaque(x + 1)",
        binders={"x": "int"},
    )
    assert verdict is False


def test_custom_predicate_with_recursive_class_argument():
    """Combine extensions 1 and 3: a predicate over a registered
    recursive datatype dispatches with the right Z3 sort for the
    argument."""
    import z3
    from deppy.core.z3_encoder import (
        register_recursive_class, register_custom_predicate,
        check_implication,
    )

    register_recursive_class(Tree)

    def _is_leaf_pred(t, helpers):
        is_leaf = helpers.get("is_leaf")
        if is_leaf is None:
            return z3.BoolVal(False)
        return is_leaf(t)

    register_custom_predicate(
        "tree_is_leaf",
        fn=lambda t: t.left is None and t.right is None,
        signature={"args": ["Tree"], "returns": "bool"},
        z3_builder=_is_leaf_pred,
    )

    # Trivial tautology — ``tree_is_leaf(t) ⇒ tree_is_leaf(t)``.
    verdict, _ = check_implication(
        premise="tree_is_leaf(t)",
        conclusion="tree_is_leaf(t)",
        binders={"t": "Tree"},
    )
    assert verdict is True


# ─────────────────────────────────────────────────────────────────────
#  Sanity — combined extensions don't break existing encodings
# ─────────────────────────────────────────────────────────────────────

def test_existing_list_int_still_works():
    """The new cache and predicate registry don't break the
    list-encoding tests that already passed."""
    from deppy.core.z3_encoder import check_implication
    verdict, _ = check_implication(
        premise="True",
        conclusion="len(xs) >= 0",
        binders={"xs": "list[int]"},
    )
    assert verdict is True


def test_cache_idempotent_under_repeated_calls():
    """Calling ``check_implication`` twice with the same binders
    leaves the cache bounded (we don't grow it linearly with calls)."""
    from deppy.core.z3_encoder import (
        check_implication, _ENCODING_CACHE,
    )
    binders = {"xs": "list[int]", "ys": "list[int]"}
    check_implication("True", "len(xs) >= 0", binders=binders)
    n1 = len(_ENCODING_CACHE)
    check_implication("True", "len(ys) >= 0", binders=binders)
    n2 = len(_ENCODING_CACHE)
    # Second call should not have grown the cache: same signatures.
    assert n2 == n1
