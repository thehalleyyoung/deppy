"""Tests for the extended Z3 encoding of lists, dicts, sets, and refinement
predicates.  These are the cases that previously needed manual PSDL
(``_z3_check_implication`` rejected them with ``unsupported-constructs``)
or that the typed encoder couldn't dispatch.

Each test demonstrates one previously-failing pattern that now
auto-discharges through ``deppy.core.z3_encoder.check_implication``.
"""
from __future__ import annotations

import pytest


@pytest.fixture(autouse=True)
def _require_z3():
    z3 = pytest.importorskip("z3")
    return z3


def _ok(premise: str, conclusion: str, binders: dict[str, str]) -> bool:
    """Run the typed Z3 encoder and return True iff it proved P ⇒ Q."""
    from deppy.core.z3_encoder import check_implication
    verdict, _reason = check_implication(premise, conclusion, binders=binders)
    return verdict


# ── 1. Length non-negativity is now an asserted axiom ────────────────

def test_list_length_is_nonneg_without_explicit_premise():
    """The encoder now asserts ``len(xs) >= 0`` automatically; previously
    a user had to add it as an explicit precondition."""
    assert _ok(
        premise="True",
        conclusion="len(xs) >= 0",
        binders={"xs": "list[int]"},
    )


def test_dict_length_is_nonneg():
    assert _ok(
        premise="True",
        conclusion="len(d) >= 0",
        binders={"d": "dict[str, int]"},
    )


# ── 2. Real ``x in xs`` membership for typed lists ───────────────────

def test_list_membership_implies_existence():
    """``x in xs ⇒ ∃i. 0 ≤ i < len(xs) ∧ xs[i] = x`` — the encoder now
    builds this Exists directly (was returning ``None`` before)."""
    assert _ok(
        premise="x == xs[0] and len(xs) > 0",
        conclusion="x in xs",
        binders={"xs": "list[int]", "x": "int"},
    )


def test_list_membership_index_correctness():
    """``xs[i] == y ∧ 0 ≤ i < len(xs) ⇒ y in xs``."""
    assert _ok(
        premise="0 <= i and i < len(xs) and y == xs[i]",
        conclusion="y in xs",
        binders={"xs": "list[int]", "i": "int", "y": "int"},
    )


# ── 3. Set membership uses Z3 native IsMember ───────────────────────

def test_set_add_then_member():
    """``s ∪ {x}`` contains x — Z3 set theory."""
    assert _ok(
        premise="True",
        conclusion="x in s.add(x)",
        binders={"s": "set[int]", "x": "int"},
    )


def test_set_member_after_discard_other():
    """Discarding a different element preserves membership."""
    assert _ok(
        premise="x in s and x != y",
        conclusion="x in s.discard(y)",
        binders={"s": "set[int]", "x": "int", "y": "int"},
    )


# ── 4. Literal-list membership ──────────────────────────────────────

def test_literal_list_membership():
    assert _ok(
        premise="x == 2",
        conclusion="x in [1, 2, 3]",
        binders={"x": "int"},
    )


def test_literal_list_non_membership():
    assert _ok(
        premise="x == 5",
        conclusion="x not in [1, 2, 3]",
        binders={"x": "int"},
    )


# ── 5. List append semantics ────────────────────────────────────────

def test_append_increases_membership():
    """After ``xs.append(y)``, the list contains y at the old length."""
    assert _ok(
        premise="True",
        conclusion="xs.append(y)[len(xs)] == y",
        binders={"xs": "list[int]", "y": "int"},
    )


# ── 6. Universal quantifier over range + list ───────────────────────

def test_all_over_range_implies_lower_bound():
    """``∀ i ∈ [0, n). xs[i] >= 0  ⇒  xs[k] >= 0`` for any k in range."""
    assert _ok(
        premise="all(xs[i] >= 0 for i in range(n)) and 0 <= k and k < n",
        conclusion="xs[k] >= 0",
        binders={"xs": "list[int]", "n": "int", "k": "int"},
    )


def test_all_over_list_implies_pointwise():
    """``∀ x ∈ xs. P(x)  ⇒  xs is empty ∨ P(xs[0])``."""
    assert _ok(
        premise="all(x >= 0 for x in xs) and len(xs) > 0",
        conclusion="xs[0] >= 0",
        binders={"xs": "list[int]"},
    )


def test_any_over_range():
    """``i = 5 ∧ 0 ≤ i < 10 ∧ predicate@i  ⇒  any(...) holds``."""
    assert _ok(
        premise="True",
        conclusion="any(j == 5 for j in range(10))",
        binders={},
    )


# ── 7. Dict get + contains ──────────────────────────────────────────

def test_dict_get_with_default():
    """``d.get(k, default) = if (k in d) then d[k] else default``.
    When the key is known to be present, ``get`` returns the stored value."""
    assert _ok(
        premise="k in d",
        conclusion="d.get(k, 0) == d[k]",
        binders={"d": "dict[str, int]", "k": "str"},
    )


def test_dict_get_default_when_missing():
    assert _ok(
        premise="k not in d",
        conclusion="d.get(k, 42) == 42",
        binders={"d": "dict[str, int]", "k": "str"},
    )


# ── 8. Refinement-style: filter + length monotone ──────────────────

def test_min_max_arithmetic():
    """min/max should reduce to If(<,>) directly without uninterpreted func."""
    assert _ok(
        premise="True",
        conclusion="min(a, b) <= max(a, b)",
        binders={"a": "int", "b": "int"},
    )


def test_abs_is_nonneg():
    assert _ok(
        premise="True",
        conclusion="abs(x) >= 0",
        binders={"x": "int"},
    )


# ── 9. String operations ────────────────────────────────────────────

def test_string_startswith_implies_prefix_length():
    """If s starts with p, then len(s) >= len(p)."""
    assert _ok(
        premise="s.startswith(p)",
        conclusion="len(s) >= len(p)",
        binders={"s": "str", "p": "str"},
    )


# ── 10. The kernel's no-binder fallback now goes through typed path ─

def test_kernel_no_binder_routes_to_typed_encoder():
    """A formula with ``len(xs)`` and no annotations was previously
    rejected with ``unsupported-constructs``.  The kernel now infers
    a list hint and dispatches via the typed encoder."""
    from deppy.core.kernel import ProofKernel
    k = ProofKernel()
    verdict, reason = k._z3_check_implication(
        premise="True",
        conclusion="len(xs) >= 0",
    )
    assert verdict, f"expected proof, got reason={reason!r}"
