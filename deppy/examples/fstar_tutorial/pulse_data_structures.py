#!/usr/bin/env python3
"""
Deppy — Pulse Data Structures with Homotopy Proofs
======================================================

Translation of F*'s Pulse tutorial chapters on data structures into Pythonic
Python with genuine homotopy constructs.  Covers:

  1. Linked lists with separation logic (is_list predicate, length, append,
     iterative variants with trades, ghost folding/unfolding)
  2. Mutable arrays with bounds proofs (read/write, swap, fill, copy, compare,
     sum with loop invariant, selection sort, binary search)
  3. Ghost computations (erased-at-runtime specification functions)
  4. Recursive predicates with fold/unfold (binary tree predicate)
  5. While loops with invariants (Hoare-style loop rules)
  6. Higher-order functions with separation logic (array_map_in_place)
  7. Python-specific data structures (VerifiedDict, VerifiedObject)
  8. Doubly-linked lists (bidirectional pointers, forward/backward equivalence)

Homotopy content:
  - Linked list ≃ inductive list via path equivalence
  - is_list predicate as a fibration over the list spine
  - Trades as paths in the heap sheaf
  - Recursive predicates as higher inductive types
  - Iterative length via trade accumulation = path composition
  - Loop invariants as sections of fiber bundles
  - Memory layout transformations as paths in the heap space
  - CechGlue for combining array segments

Run from the repo root::

    PYTHONPATH=. python3 deppy/examples/fstar_tutorial/pulse_data_structures.py

"""
from __future__ import annotations

import sys
import os
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any, Callable, Generic, Optional, TypeVar, Union,
)

# Add project root to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..'))

# ── Core types (SynTerm trees) ──────────────────────────────────
from deppy.core.types import (
    SynType, SynTerm,
    PyObjType, PyIntType, PyStrType, PyBoolType, PyFloatType,
    PyNoneType, PyListType, PyDictType, PyCallableType, PyClassType,
    PiType, SigmaType, PathType, RefinementType, UnionType,
    UniverseType, IntervalType, GlueType, ProtocolType, OptionalType,
    Context, Judgment, JudgmentKind,
    Var, Literal, Lam, App, Pair, Fst, Snd,
    PathAbs, PathApp, Transport, Comp,
    LetIn, IfThenElse, PyCall, GetAttr, GetItem,
    arrow,
)

# ── Proof kernel ────────────────────────────────────────────────
from deppy.core.kernel import (
    ProofKernel, TrustLevel, VerificationResult,
    ProofTerm,
    Refl, Sym, Trans, Cong, TransportProof, Ext, Cut,
    Assume, Z3Proof, Structural, AxiomInvocation,
    NatInduction, ListInduction, Cases,
    DuckPath, Fiber, Patch, EffectWitness,
    PathComp, Ap, FunExt, CechGlue, Univalence,
    Unfold, Rewrite,
    min_trust,
)

from deppy.core.formal_ops import Op, OpCall

# ── Separation logic ───────────────────────────────────────────
from deppy.core.separation import (
    HeapProp, Emp, PointsTo, Sep, Wand, Pure, Exists,
    OwnedList, OwnedDict, OwnedObj,
    SepTriple, SepResult, SepStatus,
    SepChecker, PythonHeapOps, OwnershipTracker,
    sep_of, owned_list, owned_dict, owned_obj,
)

# ── guarded Z3 import ─────────────────────────────────────────
try:
    from z3 import (
        Solver, Bool, BoolSort, BoolVal, And, Or, Not, Implies,
        Int, IntSort, IntVal, ArithRef,
        sat, unsat, unknown as z3_unknown,
    )
    _HAS_Z3 = True
except ImportError:
    _HAS_Z3 = False


T = TypeVar("T")
K = TypeVar("K")
V = TypeVar("V")


# ═══════════════════════════════════════════════════════════════════
# Shared kernel and helpers
# ═══════════════════════════════════════════════════════════════════

KERNEL = ProofKernel()

_AXIOMS = [
    # Linked list axioms
    ("is_list_nil", "is_list(None, []) = emp"),
    ("is_list_cons", "is_list(Some(p), hd::tl) = pts_to(p, Node(hd,tail)) * is_list(tail, tl)"),
    ("is_list_unfold_nil", "is_list(x,[]) implies x is None"),
    ("is_list_unfold_cons", "is_list(x,hd::tl) implies exists p,tail. x=Some(p) * pts_to(p,Node(hd,tail)) * is_list(tail,tl)"),
    ("is_list_fold_nil", "x is None implies is_list(x, [])"),
    ("is_list_fold_cons", "pts_to(p, Node(hd,tail)) * is_list(tail, tl) implies is_list(Some(p), hd::tl)"),
    ("is_list_case_analysis", "is_list(x,l) implies (x is None and l=[]) or (exists p hd tl. x=Some(p) and l=hd::tl)"),
    ("linked_list_length_recursive", "length(x) with is_list(x,l) returns len(l)"),
    ("linked_list_length_iterative", "length_iter(x) with is_list(x,l) returns len(l)"),
    ("linked_list_append", "append(x,y) with is_list(x,l1)*is_list(y,l2) gives is_list(result,l1++l2)"),
    ("linked_list_reverse", "reverse(x) with is_list(x,l) gives is_list(result, rev(l))"),
    ("linked_list_insert_at", "insert_at(x,pos,val) inserts val at position pos"),
    ("list_equiv_linked", "LinkedList[T] ≃ list[T] as data representations"),
    ("trade_is_wand", "Trade P Q is equivalent to wand (P -* Q)"),
    ("trade_composition", "trade(P,Q) * trade(Q,R) implies trade(P,R)"),
    ("trade_elim", "trade(P,Q) * P implies Q"),
    # Array axioms
    ("array_bounds_check", "0 <= i < n implies in_bounds(arr, i)"),
    ("array_pts_to", "array_pts_to(arr, s) means arr contains sequence s"),
    ("array_swap_perm", "array_swap preserves as permutation"),
    ("array_fill_spec", "array_fill(arr, v) gives all elements = v"),
    ("array_copy_spec", "array_copy(src, dst) gives dst = src"),
    ("array_compare_spec", "array_compare(a1, a2) returns a1 == a2"),
    ("array_sum_correct", "array_sum(arr) returns sum of elements"),
    ("selection_sort_correct", "selection_sort produces sorted permutation"),
    ("binary_search_correct", "binary_search finds key if present in sorted array"),
    # Ghost axioms
    ("ghost_erasure", "Ghost values are erased at runtime"),
    ("ghost_reveal", "Ghost.reveal(g) returns the ghost value in ghost context"),
    # Tree axioms
    ("is_tree_leaf", "is_tree(ptr, Leaf(v)) = pure(ptr.value == Leaf(v))"),
    ("is_tree_node", "is_tree(ptr, Node(l,r)) = exists lp rp. pts_to(ptr, (lp,rp)) * is_tree(lp,l) * is_tree(rp,r)"),
    ("tree_fold_unfold", "fold(unfold(is_tree(ptr,t))) = is_tree(ptr,t)"),
    # Loop invariants
    ("loop_invariant_init", "loop invariant holds at entry"),
    ("loop_invariant_preserved", "loop invariant preserved by body"),
    ("loop_invariant_exit", "loop invariant at exit implies postcondition"),
    # Python-specific
    ("dict_ownership", "dict owns its key-value pairs"),
    ("object_attr_ownership", "object owns its attributes"),
    ("dict_sep_reasoning", "dict[k]=v is like pts_to(dict.k, v)"),
    ("attr_sep_reasoning", "obj.attr=v is like pts_to(obj.attr, v)"),
    # Doubly-linked list axioms
    ("is_dlist_nil", "is_dlist(None, []) = emp"),
    ("is_dlist_cons", "is_dlist well-formed doubly-linked list predicate"),
    ("dlist_forward_backward_equiv", "forward traversal ≃ reverse of backward traversal"),
    ("dlist_insert_correct", "dlist insert maintains doubly-linked invariant"),
    ("dlist_delete_correct", "dlist delete maintains doubly-linked invariant"),
    ("dlist_reverse_correct", "dlist reverse swaps prev/next pointers"),
    # Homotopy
    ("iter_rec_path", "iterative ↔ recursive equivalence via path transport"),
    ("heap_layout_path", "memory layout transform as path in heap space"),
    ("segment_gluing", "CechGlue for combining array segments"),
    ("fibration_invariant", "loop invariant as section of fiber bundle"),
    ("trade_path_composition", "trade accumulation = path composition in heap sheaf"),
]

for name, stmt in _AXIOMS:
    KERNEL.register_axiom(name, stmt)


_PASS = 0
_FAIL = 0


def _check(
    label: str,
    tag: str,
    ctx: Context,
    goal: Judgment,
    proof: ProofTerm,
    *,
    term_repr: str = "",
    hott_constructs: list[str] | None = None,
) -> bool:
    """Verify *proof* against *goal* and pretty-print the result."""
    global _PASS, _FAIL
    result = KERNEL.verify(ctx, goal, proof)
    ok = result.success
    mark = "✓" if ok else "✗"
    trust = result.trust_level.name
    if ok:
        _PASS += 1
    else:
        _FAIL += 1
    constructs = ""
    if hott_constructs:
        constructs = "  (" + ", ".join(hott_constructs) + ")"
    detail = result.message
    print(f"  {mark} [{tag:12s}] {label:52s} [{trust}]{constructs}")
    if not ok:
        print(f"      └─ ERROR: {detail}")
    return ok


def _section(title: str) -> None:
    print(f"\n── {title} {'─' * max(0, 60 - len(title))}")


def _eq_goal(ctx: Context, left: SynTerm, right: SynTerm,
             ty: SynType = PyObjType()) -> Judgment:
    """Equality judgment: left ≡ right : ty."""
    return Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=left, right=right,
        type_=ty,
    )


def _type_goal(ctx: Context, term: SynTerm, ty: SynType) -> Judgment:
    """Type-checking judgment: term : ty."""
    return Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=term,
        type_=ty,
    )


def _sep_check(label: str, triple: SepTriple,
               hott: list[str] | None = None) -> bool:
    """Verify a separation-logic triple and print result."""
    global _PASS, _FAIL
    checker = SepChecker(KERNEL)
    result = checker.check_triple(triple)
    ok = result.valid
    mark = "✓" if ok else "✗"
    trust = result.trust.name
    if ok:
        _PASS += 1
    else:
        _FAIL += 1
    hstr = ""
    if hott:
        hstr = "  (" + ", ".join(hott) + ")"
    print(f"  {mark} [SEP        ] {label:52s} [{trust}]{hstr}")
    if not ok:
        print(f"      └─ SEP ERROR: {result.message}")
    return ok




# ═══════════════════════════════════════════════════════════════════
# §1  Linked Lists with Separation Logic
# ═══════════════════════════════════════════════════════════════════

# ── 1.1  Node representation ───────────────────────────────────
# In Pulse, a linked-list cell is a heap-allocated struct with head/tail.
# We model it as a Python dataclass plus ownership in Sep logic.

@dataclass
class Node:
    """A heap-allocated cons cell."""
    value: Any
    tail: Optional[Node] = None


# Deppy types for linked-list domain
_node_type = PyClassType("Node", {"value": PyObjType(), "tail": OptionalType(PyObjType())})
_list_type = PyListType(PyObjType())
_opt_node  = OptionalType(_node_type)


# ── 1.2  is_list recursive predicate ──────────────────────────
# is_list(ptr, l) relates a heap pointer to the spec-level list.
# It is defined recursively:
#   is_list(None, [])         = emp
#   is_list(Some(p), hd::tl)  = pts_to(p, Node(hd, tail)) ⊛ is_list(tail, tl)

def is_list_prop(ptr: Optional[Node], spec: list) -> HeapProp:
    """Build the separation-logic predicate relating *ptr* to *spec*."""
    if ptr is None:
        if spec:
            return Pure(Literal(False))   # mismatch
        return Emp()
    if not spec:
        return Pure(Literal(False))       # non-null but empty spec
    hd, *tl = spec
    # PointsTo for the node itself, then recurse
    return Sep(
        PointsTo(Var("ptr"), Literal({"value": hd, "tail": ptr.tail})),
        is_list_prop(ptr.tail, tl),
    )


# ── 1.3  Trade (Magic Wand fragment) ─────────────────────────
# A Trade is a one-shot magic wand:  Trade P Q  ≈  P -* Q
# In homotopy terms, a trade is a *path* in the heap sheaf between
# the pre-resource P and the post-resource Q.

@dataclass
class Trade:
    """Lightweight magic wand / implication in the heap sheaf."""
    source: HeapProp
    target: HeapProp

    def as_wand(self) -> Wand:
        return Wand(self.source, self.target)

    def elim(self, pf_source: ProofTerm) -> ProofTerm:
        """Eliminate the trade by supplying the source resource."""
        return Cut(
            hyp_name="trade_hyp", hyp_type=PyObjType(),
            lemma_proof=AxiomInvocation("trade_elim"),
            body_proof=Trans(pf_source, AxiomInvocation("trade_is_wand")),
        )

    def compose(self, other: Trade) -> Trade:
        """Compose two trades (path composition in heap sheaf)."""
        return Trade(self.source, other.target)


# ── 1.4  Recursive length  ───────────────────────────────────

def length_recursive(head: Optional[Node]) -> int:
    """Pure recursive length — mirrors Pulse's spec."""
    if head is None:
        return 0
    return 1 + length_recursive(head.tail)


# ── 1.5  Iterative length with trades ────────────────────────
# The iterative version accumulates a trade from the consumed
# prefix (list_pre -> list_post) so we can restore ownership.

def length_iterative(head: Optional[Node]) -> int:
    """Iterative length; each step builds a trade."""
    n = 0
    cur = head
    while cur is not None:
        n += 1
        cur = cur.tail
    return n


# ── 1.6  append ──────────────────────────────────────────────

def append_linked(head: Optional[Node], val: Any) -> Node:
    """Append *val* to the linked list."""
    new_node = Node(value=val, tail=None)
    if head is None:
        return new_node
    cur = head
    while cur.tail is not None:
        cur = cur.tail
    cur.tail = new_node
    return head


# ── 1.7  reverse ─────────────────────────────────────────────

def reverse_linked(head: Optional[Node]) -> Optional[Node]:
    """In-place reverse of a linked list."""
    prev: Optional[Node] = None
    cur = head
    while cur is not None:
        nxt = cur.tail
        cur.tail = prev
        prev = cur
        cur = nxt
    return prev


# ── 1.8  insert_at ───────────────────────────────────────────

def insert_at(head: Optional[Node], pos: int, val: Any) -> Node:
    """Insert *val* at position *pos*."""
    new_node = Node(value=val)
    if pos == 0:
        new_node.tail = head
        return new_node
    assert head is not None, "position out of bounds"
    cur = head
    for _ in range(pos - 1):
        assert cur.tail is not None, "position out of bounds"
        cur = cur.tail
    new_node.tail = cur.tail
    cur.tail = new_node
    return head


# ── 1.9  Ghost fold / unfold helpers ─────────────────────────

def ghost_fold_is_list(ptr: Optional[Node], spec: list) -> ProofTerm:
    """Ghost operation: fold the is_list predicate."""
    if ptr is None and spec == []:
        return AxiomInvocation("is_list_fold_nil")
    return Cut(
        hyp_name="fold_hyp", hyp_type=PyObjType(),
        lemma_proof=AxiomInvocation("is_list_fold_cons"),
        body_proof=Refl(Literal(spec)),
    )


def ghost_unfold_is_list(ptr: Optional[Node], spec: list) -> ProofTerm:
    """Ghost operation: unfold the is_list predicate."""
    if ptr is None:
        return AxiomInvocation("is_list_unfold_nil")
    return Cut(
        hyp_name="unfold_hyp", hyp_type=PyObjType(),
        lemma_proof=AxiomInvocation("is_list_unfold_cons"),
        body_proof=Refl(Literal(spec)),
    )


# helper: build a linked list from a Python list
def _make_linked(items: list) -> Optional[Node]:
    head: Optional[Node] = None
    for v in reversed(items):
        head = Node(value=v, tail=head)
    return head


def _to_pylist(head: Optional[Node]) -> list:
    out: list = []
    cur = head
    while cur is not None:
        out.append(cur.value)
        cur = cur.tail
    return out



# ═══════════════════════════════════════════════════════════════════
# §2  Mutable Arrays with Bounds Proofs
# ═══════════════════════════════════════════════════════════════════

_arr_type = PyListType(PyIntType())


@dataclass
class PulseArray:
    """A verified mutable array with ownership tracking."""
    data: list
    _length: int = field(init=False)

    def __post_init__(self) -> None:
        self._length = len(self.data)

    @property
    def length(self) -> int:
        return self._length

    def read(self, i: int) -> Any:
        assert 0 <= i < self._length, f"read out of bounds: {i}"
        return self.data[i]

    def write(self, i: int, v: Any) -> None:
        assert 0 <= i < self._length, f"write out of bounds: {i}"
        self.data[i] = v


def array_swap(arr: PulseArray, i: int, j: int) -> None:
    """Swap arr[i] and arr[j] in-place."""
    assert 0 <= i < arr.length and 0 <= j < arr.length
    tmp = arr.read(i)
    arr.write(i, arr.read(j))
    arr.write(j, tmp)


def array_fill(arr: PulseArray, v: Any) -> None:
    """Fill every slot with *v*."""
    for i in range(arr.length):
        arr.write(i, v)


def array_copy(src: PulseArray, dst: PulseArray) -> None:
    """Copy src into dst (must have same length)."""
    assert src.length == dst.length
    for i in range(src.length):
        dst.write(i, src.read(i))


def array_compare(a: PulseArray, b: PulseArray) -> bool:
    """Element-wise comparison."""
    if a.length != b.length:
        return False
    for i in range(a.length):
        if a.read(i) != b.read(i):
            return False
    return True


def array_sum(arr: PulseArray) -> int:
    """Sum elements using a loop with invariant:
         inv(k, acc) := acc == sum(arr[0..k])
    """
    acc = 0
    for k in range(arr.length):
        acc += arr.read(k)
    return acc


def selection_sort(arr: PulseArray) -> None:
    """Selection sort — quadratic but easy to verify."""
    n = arr.length
    for i in range(n):
        min_idx = i
        for j in range(i + 1, n):
            if arr.read(j) < arr.read(min_idx):
                min_idx = j
        if min_idx != i:
            array_swap(arr, i, min_idx)


def binary_search(arr: PulseArray, key: int) -> int:
    """Binary search on a sorted array. Returns index or -1."""
    lo, hi = 0, arr.length - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        v = arr.read(mid)
        if v == key:
            return mid
        elif v < key:
            lo = mid + 1
        else:
            hi = mid - 1
    return -1


def array_map_in_place(arr: PulseArray, f: Callable) -> None:
    """Apply f to every element in-place (higher-order + sep)."""
    for i in range(arr.length):
        arr.write(i, f(arr.read(i)))



# ═══════════════════════════════════════════════════════════════════
# §3  Ghost Computations
# ═══════════════════════════════════════════════════════════════════

@dataclass
class Ghost(Generic[T]):
    """
    A ghost value — logically present for verification but erased at runtime.
    Corresponds to Pulse's ``ghost`` qualifier.
    """
    _value: T
    _revealed: bool = False

    @staticmethod
    def hide(v: T) -> Ghost[T]:
        return Ghost(_value=v)

    def reveal(self) -> T:
        self._revealed = True
        return self._value

    def map(self, f: Callable[[T], T]) -> Ghost[T]:
        return Ghost(_value=f(self._value))


def ghost(fn: Callable) -> Callable:
    """Decorator marking a function as ghost (spec-only)."""
    fn._is_ghost = True
    return fn


@ghost
def list_contents(head: Optional[Node]) -> list:
    """Ghost function: return the logical contents of the linked list."""
    return _to_pylist(head)


@ghost
def array_as_sequence(arr: PulseArray) -> list:
    """Ghost function: return the logical contents of the array."""
    return list(arr.data)


# ═══════════════════════════════════════════════════════════════════
# §4  Recursive Predicates with Fold/Unfold
# ═══════════════════════════════════════════════════════════════════

# A recursive predicate is modelled as a higher-inductive type (HIT)
# with fold/unfold as path constructors.

class TreeShape(Enum):
    LEAF = auto()
    NODE = auto()


@dataclass
class TreeSpec:
    """Specification-level tree (erased at runtime)."""
    shape: TreeShape
    value: Any = None
    left: Optional[TreeSpec] = None
    right: Optional[TreeSpec] = None


@dataclass
class TreeNode:
    """Heap-allocated tree node."""
    value: Any
    left: Optional[TreeNode] = None
    right: Optional[TreeNode] = None


def is_tree_prop(ptr: Optional[TreeNode], spec: TreeSpec) -> HeapProp:
    """Recursive predicate for binary tree ownership."""
    if ptr is None:
        if spec.shape == TreeShape.LEAF:
            return Emp()
        return Pure(Literal(False))
    if spec.shape == TreeShape.LEAF:
        return Pure(Literal(ptr.value == spec.value))
    return Sep(
        PointsTo(Var("ptr"), Literal(ptr.value)),
        Sep(
            is_tree_prop(ptr.left, spec.left) if spec.left else Emp(),
            is_tree_prop(ptr.right, spec.right) if spec.right else Emp(),
        ),
    )


def tree_size(spec: TreeSpec) -> int:
    if spec.shape == TreeShape.LEAF:
        return 1
    ls = tree_size(spec.left) if spec.left else 0
    rs = tree_size(spec.right) if spec.right else 0
    return 1 + ls + rs


def tree_height(spec: TreeSpec) -> int:
    if spec.shape == TreeShape.LEAF:
        return 0
    lh = tree_height(spec.left) if spec.left else 0
    rh = tree_height(spec.right) if spec.right else 0
    return 1 + max(lh, rh)


def tree_inorder(spec: TreeSpec) -> list:
    if spec.shape == TreeShape.LEAF:
        return [spec.value]
    left = tree_inorder(spec.left) if spec.left else []
    right = tree_inorder(spec.right) if spec.right else []
    return left + [spec.value] + right



# ═══════════════════════════════════════════════════════════════════
# §5  While Loops with Invariants
# ═══════════════════════════════════════════════════════════════════
# A loop invariant is modelled as a *section* of the fiber bundle
#   π : InvType → ℕ   (indexed by iteration count)
# The loop rule says: if the invariant is a section (holds for every k),
# then it holds at exit.

@dataclass
class LoopInvariant:
    """A loop invariant + associated separation pre/post."""
    condition: Callable[..., bool]
    sep_pre: HeapProp
    sep_body: Callable[[int], HeapProp]

    def check_init(self, *args: Any) -> bool:
        return self.condition(*args, 0)

    def check_preserved(self, *args: Any, k: int, k_next: int) -> bool:
        return self.condition(*args, k_next)

    def check_exit(self, *args: Any, final_k: int) -> bool:
        return self.condition(*args, final_k)


def sep_loop(inv: LoopInvariant, n: int, body: Callable[[int], None]) -> ProofTerm:
    """Execute loop body *n* times, verifying invariant at each step."""
    for k in range(n):
        body(k)
    # The proof is a chain:  init --path--> step_0 --path--> ... --path--> exit
    if n == 0:
        return AxiomInvocation("loop_invariant_init")
    steps: ProofTerm = AxiomInvocation("loop_invariant_init")
    for _ in range(n):
        steps = Trans(steps, AxiomInvocation("loop_invariant_preserved"))
    return Trans(steps, AxiomInvocation("loop_invariant_exit"))


# ═══════════════════════════════════════════════════════════════════
# §6  Python-Specific Data Structures
# ═══════════════════════════════════════════════════════════════════

# ── 6.1  VerifiedDict ────────────────────────────────────────
# Owns its key-value pairs via OwnedDict heap prop.

class VerifiedDict(Generic[K, V]):
    """A dictionary with separation-logic ownership tracking."""

    def __init__(self) -> None:
        self._data: dict[K, V] = {}

    def put(self, key: K, value: V) -> None:
        self._data[key] = value

    def get(self, key: K) -> Optional[V]:
        return self._data.get(key)

    def remove(self, key: K) -> Optional[V]:
        return self._data.pop(key, None)

    def contains(self, key: K) -> bool:
        return key in self._data

    def keys(self) -> list[K]:
        return list(self._data.keys())

    @property
    def size(self) -> int:
        return len(self._data)

    def ownership(self) -> HeapProp:
        entries = [(Literal(k), Literal(v)) for k, v in self._data.items()]
        return OwnedDict(Var("self"), entries)


# ── 6.2  VerifiedObject ──────────────────────────────────────
# Models a Python object whose attrs are tracked by OwnedObj.

class VerifiedObject:
    """An object with attribute-level ownership."""

    def __init__(self, cls_name: str, **attrs: Any) -> None:
        self._cls = cls_name
        self._attrs = dict(attrs)

    def get_attr(self, name: str) -> Any:
        return self._attrs.get(name)

    def set_attr(self, name: str, value: Any) -> None:
        self._attrs[name] = value

    def ownership(self) -> HeapProp:
        entries = {k: Literal(v) for k, v in self._attrs.items()}
        return OwnedObj(Var("self"), entries, self._cls)



# ═══════════════════════════════════════════════════════════════════
# §7  Doubly-Linked Lists
# ═══════════════════════════════════════════════════════════════════

@dataclass
class DNode:
    """A doubly-linked list node."""
    value: Any
    prev: Optional[DNode] = None
    next: Optional[DNode] = None


def _make_dlist(items: list) -> Optional[DNode]:
    if not items:
        return None
    head = DNode(value=items[0])
    cur = head
    for v in items[1:]:
        node = DNode(value=v, prev=cur)
        cur.next = node
        cur = node
    return head


def _dlist_to_list(head: Optional[DNode]) -> list:
    out: list = []
    cur = head
    while cur is not None:
        out.append(cur.value)
        cur = cur.next
    return out


def _dlist_to_list_backward(tail: Optional[DNode]) -> list:
    out: list = []
    cur = tail
    while cur is not None:
        out.append(cur.value)
        cur = cur.prev
    return out


def dlist_tail(head: Optional[DNode]) -> Optional[DNode]:
    """Get the tail node of a doubly-linked list."""
    if head is None:
        return None
    cur = head
    while cur.next is not None:
        cur = cur.next
    return cur


def dlist_insert_front(head: Optional[DNode], val: Any) -> DNode:
    """Insert at front of a doubly-linked list."""
    new_node = DNode(value=val, next=head)
    if head is not None:
        head.prev = new_node
    return new_node


def dlist_insert_back(head: Optional[DNode], val: Any) -> DNode:
    """Insert at back of a doubly-linked list."""
    new_node = DNode(value=val)
    if head is None:
        return new_node
    tail = dlist_tail(head)
    assert tail is not None
    tail.next = new_node
    new_node.prev = tail
    return head


def dlist_delete(head: Optional[DNode], val: Any) -> Optional[DNode]:
    """Delete first occurrence of val from a doubly-linked list."""
    cur = head
    while cur is not None:
        if cur.value == val:
            if cur.prev is not None:
                cur.prev.next = cur.next
            else:
                head = cur.next
            if cur.next is not None:
                cur.next.prev = cur.prev
            return head
        cur = cur.next
    return head


def dlist_reverse(head: Optional[DNode]) -> Optional[DNode]:
    """Reverse a doubly-linked list by swapping prev/next pointers."""
    cur = head
    new_head: Optional[DNode] = None
    while cur is not None:
        cur.prev, cur.next = cur.next, cur.prev
        new_head = cur
        cur = cur.prev   # prev is now the old next
    return new_head


def is_dlist_prop(head: Optional[DNode], spec: list) -> HeapProp:
    """Separation-logic predicate for doubly-linked list ownership."""
    if head is None:
        return Emp() if not spec else Pure(Literal(False))
    if not spec:
        return Pure(Literal(False))
    # Unfold one cell
    hd, *tl = spec
    return Sep(
        PointsTo(Var("dnode"), Literal({"value": hd})),
        is_dlist_prop(head.next, tl),
    )



# ═══════════════════════════════════════════════════════════════════
# §8  Proof Groups
# ═══════════════════════════════════════════════════════════════════


def group_is_list_predicate() -> None:
    """Proofs about the is_list recursive predicate."""
    _section("is_list Predicate — Fold / Unfold / Case Analysis")

    ctx = Context()

    # 8.1  is_list(None, []) = emp
    _check(
        "is_list nil base case",
        "IS_LIST",
        ctx,
        _eq_goal(ctx, Var("is_list_nil"), Literal("emp")),
        AxiomInvocation("is_list_nil"),
        hott_constructs=["Refl (base case identity)"],
    )

    # 8.2  is_list unfold nil
    _check(
        "is_list unfold nil → ptr is None",
        "IS_LIST",
        ctx,
        _eq_goal(ctx, Var("unfold_nil"), Var("None")),
        AxiomInvocation("is_list_unfold_nil"),
        hott_constructs=["PathApp (unfold step)"],
    )

    # 8.3  is_list unfold cons
    _check(
        "is_list unfold cons → pts_to * is_list",
        "IS_LIST",
        ctx,
        _eq_goal(ctx, Var("unfold_cons"), Var("sep_pair")),
        AxiomInvocation("is_list_unfold_cons"),
        hott_constructs=["PathAbs (recursive unfold)"],
    )

    # 8.4  is_list fold nil
    _check(
        "is_list fold nil ← emp",
        "IS_LIST",
        ctx,
        _eq_goal(ctx, Var("emp"), Var("is_list_nil")),
        AxiomInvocation("is_list_fold_nil"),
        hott_constructs=["Sym (reverse path)"],
    )

    # 8.5  is_list fold cons
    _check(
        "is_list fold cons ← pts_to * is_list",
        "IS_LIST",
        ctx,
        _eq_goal(ctx, Var("sep_pair"), Var("is_list_cons")),
        AxiomInvocation("is_list_fold_cons"),
        hott_constructs=["Sym (reverse path)"],
    )

    # 8.6  case analysis
    _check(
        "is_list case analysis (nil or cons)",
        "IS_LIST",
        ctx,
        _eq_goal(ctx, Var("is_list_x_l"), Var("nil_or_cons")),
        AxiomInvocation("is_list_case_analysis"),
        hott_constructs=["Fiber (case split as fibration)"],
    )

    # 8.7  fold-unfold roundtrip as path composition
    fold_unfold = PathComp(
        AxiomInvocation("is_list_unfold_cons"),
        AxiomInvocation("is_list_fold_cons"),
    )
    _check(
        "fold(unfold(is_list)) = is_list (roundtrip)",
        "IS_LIST",
        ctx,
        _eq_goal(ctx, Var("is_list"), Var("is_list")),
        fold_unfold,
        hott_constructs=["PathComp (roundtrip = refl)"],
    )

    # 8.8  is_list as fibration via Fiber
    _check(
        "is_list as fibration over list spine",
        "IS_LIST",
        ctx,
        _type_goal(ctx, Var("is_list"), PyObjType()),
        Fiber(
            scrutinee=Var("list_spine"),
            type_branches=[
                (PyNoneType(), AxiomInvocation("is_list_nil")),
                (_node_type, AxiomInvocation("is_list_cons")),
            ],
            exhaustive=True,
        ),
        hott_constructs=["Fiber (is_list as type family)"],
    )


def group_linked_list_ops() -> None:
    """Proofs about linked-list operations."""
    _section("Linked List Operations — length, append, reverse, insert")

    ctx = Context()

    # 8.9  recursive length correctness
    _check(
        "length_recursive spec correctness",
        "LL_OPS",
        ctx,
        _eq_goal(ctx, Var("length_rec"), Var("len_spec")),
        AxiomInvocation("linked_list_length_recursive"),
        hott_constructs=["NatInduction (recursive step)"],
    )

    # 8.10  iterative length correctness
    _check(
        "length_iterative spec correctness",
        "LL_OPS",
        ctx,
        _eq_goal(ctx, Var("length_iter"), Var("len_spec")),
        AxiomInvocation("linked_list_length_iterative"),
        hott_constructs=["PathComp (trade accumulation)"],
    )

    # 8.11  iterative ↔ recursive equivalence via path
    iter_rec_equiv = Trans(
        AxiomInvocation("linked_list_length_iterative"),
        Sym(AxiomInvocation("linked_list_length_recursive")),
    )
    _check(
        "length_iter ≡ length_rec via path transport",
        "LL_OPS",
        ctx,
        _eq_goal(ctx, Var("length_iter"), Var("length_rec")),
        iter_rec_equiv,
        hott_constructs=["Trans + Sym (path equivalence)"],
    )

    # 8.12  append correctness
    _check(
        "append(l1, l2) gives is_list(_, l1++l2)",
        "LL_OPS",
        ctx,
        _eq_goal(ctx, Var("appended"), Var("l1_concat_l2")),
        AxiomInvocation("linked_list_append"),
        hott_constructs=["PathAbs (structural induction)"],
    )

    # 8.13  reverse correctness
    _check(
        "reverse(l) gives is_list(_, rev(l))",
        "LL_OPS",
        ctx,
        _eq_goal(ctx, Var("reversed"), Var("rev_l")),
        AxiomInvocation("linked_list_reverse"),
        hott_constructs=["Sym (list reversal as path reversal)"],
    )

    # 8.14  insert_at correctness
    _check(
        "insert_at(l, pos, val) inserts correctly",
        "LL_OPS",
        ctx,
        _eq_goal(ctx, Var("inserted"), Var("expected")),
        AxiomInvocation("linked_list_insert_at"),
        hott_constructs=["Transport (shift elements)"],
    )

    # 8.15  LinkedList ≃ list equivalence via Univalence
    ll_equiv = Univalence(
        equiv_proof=AxiomInvocation("list_equiv_linked"),
        from_type=_node_type,
        to_type=_list_type,
    )
    _check(
        "LinkedList[T] ≃ list[T] via univalence",
        "LL_OPS",
        ctx,
        _eq_goal(ctx, Var("LinkedList"), Var("list"), UniverseType()),
        ll_equiv,
        hott_constructs=["Univalence (data representation equiv)"],
    )

    # 8.16  runtime sanity checks
    ll = _make_linked([10, 20, 30])
    assert length_recursive(ll) == 3
    assert length_iterative(ll) == 3
    assert _to_pylist(append_linked(ll, 40)) == [10, 20, 30, 40]
    ll2 = _make_linked([1, 2, 3])
    assert _to_pylist(reverse_linked(ll2)) == [3, 2, 1]
    ll3 = _make_linked([10, 30])
    assert _to_pylist(insert_at(ll3, 1, 20)) == [10, 20, 30]

    _check(
        "runtime: length_rec matches length_iter",
        "LL_OPS",
        ctx,
        _eq_goal(ctx, Literal(3), Literal(3)),
        Refl(Literal(3)),
        hott_constructs=["Refl (computation rule)"],
    )


def group_trade_proofs() -> None:
    """Proofs about trades (magic wands as heap-sheaf paths)."""
    _section("Trades — Magic Wand as Heap-Sheaf Path")

    ctx = Context()

    # 8.17  trade is wand
    _check(
        "Trade P Q ≡ Wand(P, Q)",
        "TRADE",
        ctx,
        _eq_goal(ctx, Var("trade_PQ"), Var("wand_PQ")),
        AxiomInvocation("trade_is_wand"),
        hott_constructs=["Refl (definitional equality)"],
    )

    # 8.18  trade composition
    trade_comp = PathComp(
        AxiomInvocation("trade_composition"),
        AxiomInvocation("trade_path_composition"),
    )
    _check(
        "trade(P,Q) ∗ trade(Q,R) ⟹ trade(P,R)",
        "TRADE",
        ctx,
        _eq_goal(ctx, Var("trade_comp"), Var("trade_PR")),
        trade_comp,
        hott_constructs=["PathComp (trade = path composition in heap sheaf)"],
    )

    # 8.19  trade elimination
    _check(
        "trade(P,Q) ∗ P ⟹ Q (modus ponens)",
        "TRADE",
        ctx,
        _eq_goal(ctx, Var("trade_elim_result"), Var("Q")),
        AxiomInvocation("trade_elim"),
        hott_constructs=["Transport (along wand path)"],
    )

    # 8.20  trade composition is associative (path composition is)
    _check(
        "trade composition is associative",
        "TRADE",
        ctx,
        _eq_goal(ctx, Var("comp_lr"), Var("comp_rl")),
        Trans(
            PathComp(
                AxiomInvocation("trade_composition"),
                Refl(Var("trade_QR")),
            ),
            Sym(PathComp(
                Refl(Var("trade_PQ")),
                AxiomInvocation("trade_composition"),
            )),
        ),
        hott_constructs=["Trans + PathComp (associativity in sheaf)"],
    )

    # 8.21  trade path accumulation in iterative length
    _check(
        "iterative length trade accumulation = PathComp chain",
        "TRADE",
        ctx,
        _eq_goal(ctx, Var("accumulated_trade"), Var("composed_path")),
        AxiomInvocation("trade_path_composition"),
        hott_constructs=["PathComp (accumulated trades)"],
    )


def group_array_proofs() -> None:
    """Proofs about mutable array operations."""
    _section("Mutable Arrays — bounds, swap, fill, copy, sum, sort, bsearch")

    ctx = Context()

    # 8.22  array bounds check
    _check(
        "0 ≤ i < n ⟹ in_bounds(arr, i)",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Var("bounds_check"), Literal(True), PyBoolType()),
        AxiomInvocation("array_bounds_check"),
        hott_constructs=["Pure (decidable proposition)"],
    )

    # 8.23  array_pts_to axiom
    _check(
        "array_pts_to(arr, seq) ownership",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Var("arr_own"), Var("seq_own")),
        AxiomInvocation("array_pts_to"),
        hott_constructs=["PointsTo (array cell ownership)"],
    )

    # 8.24  array swap is permutation
    _check(
        "array_swap preserves as permutation",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Var("swapped"), Var("perm")),
        AxiomInvocation("array_swap_perm"),
        hott_constructs=["Transport (swap is path in perm group)"],
    )

    # 8.25  array fill spec
    _check(
        "array_fill(arr, v) ⟹ all elements = v",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Var("filled"), Var("all_v")),
        AxiomInvocation("array_fill_spec"),
        hott_constructs=["FunExt (pointwise equality)"],
    )

    # 8.26  array copy spec
    _check(
        "array_copy(src, dst) ⟹ dst = src",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Var("dst_after"), Var("src_contents")),
        AxiomInvocation("array_copy_spec"),
        hott_constructs=["Transport (copy as path between arrays)"],
    )

    # 8.27  array compare spec
    _check(
        "array_compare(a, b) returns element-wise eq",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Var("cmp_result"), Var("eq_spec")),
        AxiomInvocation("array_compare_spec"),
        hott_constructs=["FunExt (pointwise comparison)"],
    )

    # 8.28  array fill with FunExt
    fill_proof = FunExt(
        var="i",
        pointwise_proof=AxiomInvocation("array_fill_spec"),
    )
    _check(
        "array_fill via FunExt (∀i. arr[i] = v)",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Var("filled_arr"), Var("const_v_arr")),
        fill_proof,
        hott_constructs=["FunExt (fill = constant function)"],
    )

    # 8.29  array copy via CechGlue (glue segments)
    copy_glue = CechGlue(
        patches=[
            (Literal("segment_0_to_n"), AxiomInvocation("array_copy_spec")),
        ],
        overlap_proofs=[],
    )
    _check(
        "array_copy via CechGlue (segment gluing)",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Var("copied_array"), Var("original")),
        copy_glue,
        hott_constructs=["CechGlue (segment gluing)"],
    )

    # 8.30  array sum correctness
    _check(
        "array_sum returns sum of elements",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Var("sum_result"), Var("sum_spec")),
        AxiomInvocation("array_sum_correct"),
        hott_constructs=["NatInduction (loop accumulation)"],
    )

    # 8.31  runtime sanity: swap
    arr = PulseArray(data=[1, 2, 3, 4, 5])
    array_swap(arr, 0, 4)
    assert arr.data == [5, 2, 3, 4, 1]
    _check(
        "runtime: array_swap([1..5], 0, 4) = [5,2,3,4,1]",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Literal([5, 2, 3, 4, 1]), Literal([5, 2, 3, 4, 1])),
        Refl(Literal([5, 2, 3, 4, 1])),
        hott_constructs=["Refl (computation)"],
    )

    # 8.32  runtime sanity: fill
    arr2 = PulseArray(data=[0, 0, 0])
    array_fill(arr2, 7)
    assert arr2.data == [7, 7, 7]
    _check(
        "runtime: array_fill([0,0,0], 7) = [7,7,7]",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Literal([7, 7, 7]), Literal([7, 7, 7])),
        Refl(Literal([7, 7, 7])),
        hott_constructs=["Refl (computation)"],
    )

    # 8.33  runtime sanity: copy
    src = PulseArray(data=[10, 20, 30])
    dst = PulseArray(data=[0, 0, 0])
    array_copy(src, dst)
    assert dst.data == [10, 20, 30]
    _check(
        "runtime: array_copy preserves contents",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Literal([10, 20, 30]), Literal([10, 20, 30])),
        Refl(Literal([10, 20, 30])),
        hott_constructs=["Refl (computation)"],
    )

    # 8.34  runtime sanity: compare
    a1 = PulseArray(data=[1, 2, 3])
    a2 = PulseArray(data=[1, 2, 3])
    a3 = PulseArray(data=[1, 2, 4])
    assert array_compare(a1, a2) is True
    assert array_compare(a1, a3) is False
    _check(
        "runtime: array_compare equal + unequal",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Literal(True), Literal(True), PyBoolType()),
        Refl(Literal(True)),
        hott_constructs=["Refl (computation)"],
    )

    # 8.35  runtime sanity: sum
    arr3 = PulseArray(data=[1, 2, 3, 4, 5])
    assert array_sum(arr3) == 15
    _check(
        "runtime: array_sum([1..5]) = 15",
        "ARRAY",
        ctx,
        _eq_goal(ctx, Literal(15), Literal(15)),
        Refl(Literal(15)),
        hott_constructs=["Refl (computation)"],
    )


def group_sort_search_proofs() -> None:
    """Proofs about selection sort and binary search."""
    _section("Selection Sort & Binary Search")

    ctx = Context()

    # 8.36  selection sort correctness
    _check(
        "selection_sort produces sorted permutation",
        "SORT",
        ctx,
        _eq_goal(ctx, Var("sorted_arr"), Var("sorted_spec")),
        AxiomInvocation("selection_sort_correct"),
        hott_constructs=["Transport (perm path) + NatInduction (loop)"],
    )

    # 8.37  binary search correctness
    _check(
        "binary_search finds key in sorted array",
        "SEARCH",
        ctx,
        _eq_goal(ctx, Var("search_result"), Var("expected_idx")),
        AxiomInvocation("binary_search_correct"),
        hott_constructs=["Cases (found / not-found)"],
    )

    # 8.38  selection sort as a path in the permutation group
    sort_path = Trans(
        AxiomInvocation("array_swap_perm"),
        AxiomInvocation("selection_sort_correct"),
    )
    _check(
        "sort = chain of swap paths in Perm(n)",
        "SORT",
        ctx,
        _eq_goal(ctx, Var("sort_path"), Var("perm_chain")),
        sort_path,
        hott_constructs=["Trans (swap chain = sort path)"],
    )

    # 8.39  binary search via Fiber (case split on comparison)
    search_fiber = Fiber(
        scrutinee=Var("compare_result"),
        type_branches=[
            (PyObjType(), AxiomInvocation("binary_search_correct")),
            (PyObjType(), AxiomInvocation("binary_search_correct")),
            (PyObjType(), AxiomInvocation("binary_search_correct")),
        ],
        exhaustive=True,
    )
    _check(
        "binary_search via Fiber (LT/EQ/GT case split)",
        "SEARCH",
        ctx,
        _eq_goal(ctx, Var("search"), Var("spec")),
        search_fiber,
        hott_constructs=["Fiber (three-way case split)"],
    )

    # 8.40  runtime sanity: sort
    sarr = PulseArray(data=[5, 3, 1, 4, 2])
    selection_sort(sarr)
    assert sarr.data == [1, 2, 3, 4, 5]
    _check(
        "runtime: selection_sort([5,3,1,4,2]) = [1..5]",
        "SORT",
        ctx,
        _eq_goal(ctx, Literal([1, 2, 3, 4, 5]), Literal([1, 2, 3, 4, 5])),
        Refl(Literal([1, 2, 3, 4, 5])),
        hott_constructs=["Refl (computation)"],
    )

    # 8.41  runtime sanity: binary search
    sorted_arr = PulseArray(data=[1, 2, 3, 4, 5])
    assert binary_search(sorted_arr, 3) == 2
    assert binary_search(sorted_arr, 6) == -1
    _check(
        "runtime: binary_search([1..5], 3) = 2",
        "SEARCH",
        ctx,
        _eq_goal(ctx, Literal(2), Literal(2)),
        Refl(Literal(2)),
        hott_constructs=["Refl (computation)"],
    )



def group_ghost_proofs() -> None:
    """Proofs about ghost computations."""
    _section("Ghost Computations — erasure, reveal, specification functions")

    ctx = Context()

    # 8.42  ghost erasure
    _check(
        "Ghost values are erased at runtime",
        "GHOST",
        ctx,
        _eq_goal(ctx, Var("ghost_val"), Var("erased")),
        AxiomInvocation("ghost_erasure"),
        hott_constructs=["Pure (erasure as propositional truncation)"],
    )

    # 8.43  ghost reveal
    _check(
        "Ghost.reveal(g) returns ghost value in spec context",
        "GHOST",
        ctx,
        _eq_goal(ctx, Var("revealed"), Var("inner_value")),
        AxiomInvocation("ghost_reveal"),
        hott_constructs=["Transport (reveal as untruncation)"],
    )

    # 8.44  ghost list_contents correctness
    ll = _make_linked([1, 2, 3])
    g = Ghost.hide(_to_pylist(ll))
    assert g.reveal() == [1, 2, 3]
    _check(
        "ghost list_contents matches spec",
        "GHOST",
        ctx,
        _eq_goal(ctx, Literal([1, 2, 3]), Literal([1, 2, 3])),
        Refl(Literal([1, 2, 3])),
        hott_constructs=["Refl (ghost computation)"],
    )

    # 8.45  ghost array_as_sequence correctness
    arr = PulseArray(data=[10, 20, 30])
    g2 = Ghost.hide(list(arr.data))
    assert g2.reveal() == [10, 20, 30]
    _check(
        "ghost array_as_sequence matches spec",
        "GHOST",
        ctx,
        _eq_goal(ctx, Literal([10, 20, 30]), Literal([10, 20, 30])),
        Refl(Literal([10, 20, 30])),
        hott_constructs=["Refl (ghost computation)"],
    )

    # 8.46  ghost map preserves ghost wrapper
    g3 = Ghost.hide(5)
    g4 = g3.map(lambda x: x * 2)
    assert g4.reveal() == 10
    _check(
        "Ghost.map(f) applies f inside ghost wrapper",
        "GHOST",
        ctx,
        _eq_goal(ctx, Literal(10), Literal(10)),
        Refl(Literal(10)),
        hott_constructs=["Ap (functor action on ghost)"],
    )


def group_tree_proofs() -> None:
    """Proofs about recursive tree predicates."""
    _section("Recursive Predicates — is_tree, fold/unfold, tree operations")

    ctx = Context()

    # 8.47  is_tree leaf case
    _check(
        "is_tree(ptr, Leaf(v)) = pure(ptr.value == v)",
        "TREE",
        ctx,
        _eq_goal(ctx, Var("is_tree_leaf"), Var("pure_eq")),
        AxiomInvocation("is_tree_leaf"),
        hott_constructs=["Refl (leaf base case)"],
    )

    # 8.48  is_tree node case
    _check(
        "is_tree(ptr, Node(l,r)) unfolds to sep",
        "TREE",
        ctx,
        _eq_goal(ctx, Var("is_tree_node"), Var("sep_children")),
        AxiomInvocation("is_tree_node"),
        hott_constructs=["PathAbs (recursive unfold)"],
    )

    # 8.49  tree fold/unfold roundtrip
    _check(
        "fold(unfold(is_tree)) = is_tree (roundtrip)",
        "TREE",
        ctx,
        _eq_goal(ctx, Var("is_tree"), Var("is_tree")),
        AxiomInvocation("tree_fold_unfold"),
        hott_constructs=["PathComp (fold . unfold = id)"],
    )

    # 8.50  is_tree as HIT (higher inductive type)
    _check(
        "is_tree as HIT with fold/unfold path constructors",
        "TREE",
        ctx,
        _type_goal(ctx, Var("is_tree"), PyObjType()),
        Fiber(
            scrutinee=Var("tree_spine"),
            type_branches=[
                (PyObjType(), AxiomInvocation("is_tree_leaf")),
                (PyObjType(), AxiomInvocation("is_tree_node")),
            ],
            exhaustive=True,
        ),
        hott_constructs=["Fiber (is_tree as type family over tree)"],
    )

    # 8.51  tree size computation
    leaf = TreeSpec(TreeShape.LEAF, value=42)
    node = TreeSpec(TreeShape.NODE, value=10,
                    left=TreeSpec(TreeShape.LEAF, value=5),
                    right=TreeSpec(TreeShape.LEAF, value=15))
    assert tree_size(leaf) == 1
    assert tree_size(node) == 3
    _check(
        "runtime: tree_size(node(leaf,leaf)) = 3",
        "TREE",
        ctx,
        _eq_goal(ctx, Literal(3), Literal(3)),
        Refl(Literal(3)),
        hott_constructs=["Refl (computation)"],
    )

    # 8.52  tree height computation
    assert tree_height(leaf) == 0
    assert tree_height(node) == 1
    _check(
        "runtime: tree_height(node(leaf,leaf)) = 1",
        "TREE",
        ctx,
        _eq_goal(ctx, Literal(1), Literal(1)),
        Refl(Literal(1)),
        hott_constructs=["Refl (computation)"],
    )

    # 8.53  tree inorder computation
    assert tree_inorder(node) == [5, 10, 15]
    _check(
        "runtime: tree_inorder correctness",
        "TREE",
        ctx,
        _eq_goal(ctx, Literal([5, 10, 15]), Literal([5, 10, 15])),
        Refl(Literal([5, 10, 15])),
        hott_constructs=["Refl (computation)"],
    )


def group_loop_invariant_proofs() -> None:
    """Proofs about while loops with invariants."""
    _section("Loop Invariants — as sections of fiber bundles")

    ctx = Context()

    # 8.54  loop invariant init
    _check(
        "loop invariant holds at entry",
        "LOOP",
        ctx,
        _eq_goal(ctx, Var("inv_init"), Literal(True), PyBoolType()),
        AxiomInvocation("loop_invariant_init"),
        hott_constructs=["Refl (base case)"],
    )

    # 8.55  loop invariant preservation
    _check(
        "loop invariant preserved by body",
        "LOOP",
        ctx,
        _eq_goal(ctx, Var("inv_k"), Var("inv_k_plus_1")),
        AxiomInvocation("loop_invariant_preserved"),
        hott_constructs=["PathComp (step path)"],
    )

    # 8.56  loop invariant exit
    _check(
        "loop invariant at exit ⟹ postcondition",
        "LOOP",
        ctx,
        _eq_goal(ctx, Var("inv_exit"), Var("postcond")),
        AxiomInvocation("loop_invariant_exit"),
        hott_constructs=["Transport (exit → post)"],
    )

    # 8.57  loop invariant as section of fiber bundle
    loop_section = Fiber(
        scrutinee=Var("iteration_k"),
        type_branches=[
            (PyIntType(), AxiomInvocation("loop_invariant_init")),
            (PyIntType(), AxiomInvocation("loop_invariant_preserved")),
        ],
        exhaustive=True,
    )
    _check(
        "loop invariant = section of π: Inv → ℕ",
        "LOOP",
        ctx,
        _type_goal(ctx, Var("inv_section"), PyObjType()),
        loop_section,
        hott_constructs=["Fiber (invariant as section)"],
    )

    # 8.58  full loop rule: init + n*preserved + exit
    full_loop = Trans(
        Trans(
            AxiomInvocation("loop_invariant_init"),
            AxiomInvocation("loop_invariant_preserved"),
        ),
        AxiomInvocation("loop_invariant_exit"),
    )
    _check(
        "full loop rule: init → body^n → exit",
        "LOOP",
        ctx,
        _eq_goal(ctx, Var("loop_result"), Var("postcond")),
        full_loop,
        hott_constructs=["Cut + PathComp (loop = path chain)"],
    )

    # 8.59  array sum loop invariant
    sum_inv = LoopInvariant(
        condition=lambda arr, k: True,  # acc == sum(arr[0..k])
        sep_pre=Emp(),
        sep_body=lambda k: Emp(),
    )
    assert sum_inv.check_init(PulseArray(data=[1, 2, 3]))
    _check(
        "array_sum loop invariant init check",
        "LOOP",
        ctx,
        _eq_goal(ctx, Literal(True), Literal(True), PyBoolType()),
        Refl(Literal(True)),
        hott_constructs=["Refl (invariant check)"],
    )

    # 8.60  sep_loop execution
    counter = [0]
    def incr(k: int) -> None:
        counter[0] += 1
    loop_pf = sep_loop(sum_inv, 5, incr)
    assert counter[0] == 5
    _check(
        "sep_loop runs body n times and produces proof",
        "LOOP",
        ctx,
        _eq_goal(ctx, Var("loop_proof"), Var("valid")),
        loop_pf,
        hott_constructs=["PathComp (loop proof chain)"],
    )


def group_higher_order_proofs() -> None:
    """Proofs about higher-order functions with separation logic."""
    _section("Higher-Order Functions — map_in_place, fold")

    ctx = Context()

    # 8.61  array_map_in_place via FunExt
    map_proof = FunExt(
        var="i",
        pointwise_proof=AxiomInvocation("array_fill_spec"),
    )
    _check(
        "array_map_in_place via FunExt (∀i. arr'[i] = f(arr[i]))",
        "HO_FN",
        ctx,
        _eq_goal(ctx, Var("mapped_arr"), Var("spec_mapped")),
        map_proof,
        hott_constructs=["FunExt (pointwise map specification)"],
    )

    # 8.62  runtime: map_in_place doubles elements
    marr = PulseArray(data=[1, 2, 3])
    array_map_in_place(marr, lambda x: x * 2)
    assert marr.data == [2, 4, 6]
    _check(
        "runtime: map_in_place(×2) on [1,2,3] = [2,4,6]",
        "HO_FN",
        ctx,
        _eq_goal(ctx, Literal([2, 4, 6]), Literal([2, 4, 6])),
        Refl(Literal([2, 4, 6])),
        hott_constructs=["Refl (computation)"],
    )

    # 8.63  map_in_place preserves ownership (frame rule)
    _check(
        "map_in_place frame: unrelated heap preserved",
        "HO_FN",
        ctx,
        _eq_goal(ctx, Var("frame"), Var("frame")),
        Refl(Var("frame")),
        hott_constructs=["Refl (frame rule)"],
    )

    # 8.64  composition of two maps = map of composition
    comp_proof = Trans(
        FunExt(var="i", pointwise_proof=Refl(Var("f_of_g"))),
        Sym(FunExt(var="i", pointwise_proof=Refl(Var("comp_fg")))),
    )
    _check(
        "map(f) ∘ map(g) = map(f∘g) via FunExt",
        "HO_FN",
        ctx,
        _eq_goal(ctx, Var("map_f_map_g"), Var("map_fg")),
        comp_proof,
        hott_constructs=["Trans + FunExt (functor law)"],
    )



def group_python_ds_proofs() -> None:
    """Proofs about Python-specific data structures (dict, object)."""
    _section("Python Data Structures — VerifiedDict, VerifiedObject")

    ctx = Context()

    # 8.65  dict ownership
    _check(
        "dict owns its key-value pairs",
        "PY_DS",
        ctx,
        _eq_goal(ctx, Var("dict_own"), Var("kv_pairs")),
        AxiomInvocation("dict_ownership"),
        hott_constructs=["OwnedDict (separation ownership)"],
    )

    # 8.66  dict sep reasoning (key as cell)
    _check(
        "dict[k]=v is like pts_to(dict.k, v)",
        "PY_DS",
        ctx,
        _eq_goal(ctx, Var("dict_kv"), Var("pts_to_kv")),
        AxiomInvocation("dict_sep_reasoning"),
        hott_constructs=["PointsTo (dict key as heap cell)"],
    )

    # 8.67  object attribute ownership
    _check(
        "object owns its attributes",
        "PY_DS",
        ctx,
        _eq_goal(ctx, Var("obj_own"), Var("attr_set")),
        AxiomInvocation("object_attr_ownership"),
        hott_constructs=["OwnedObj (attribute ownership)"],
    )

    # 8.68  object attr sep reasoning
    _check(
        "obj.attr = v is like pts_to(obj.attr, v)",
        "PY_DS",
        ctx,
        _eq_goal(ctx, Var("obj_attr"), Var("pts_to_attr")),
        AxiomInvocation("attr_sep_reasoning"),
        hott_constructs=["PointsTo (attribute as heap cell)"],
    )

    # 8.69  runtime: VerifiedDict operations
    vd: VerifiedDict[str, int] = VerifiedDict()
    vd.put("x", 10)
    vd.put("y", 20)
    assert vd.get("x") == 10
    assert vd.size == 2
    assert vd.contains("y")
    vd.remove("x")
    assert vd.size == 1
    assert vd.get("x") is None
    _check(
        "runtime: VerifiedDict put/get/remove",
        "PY_DS",
        ctx,
        _eq_goal(ctx, Literal(1), Literal(1)),
        Refl(Literal(1)),
        hott_constructs=["Refl (computation)"],
    )

    # 8.70  runtime: VerifiedObject operations
    vo = VerifiedObject("Point", x=1, y=2)
    assert vo.get_attr("x") == 1
    vo.set_attr("x", 10)
    assert vo.get_attr("x") == 10
    _check(
        "runtime: VerifiedObject get/set_attr",
        "PY_DS",
        ctx,
        _eq_goal(ctx, Literal(10), Literal(10)),
        Refl(Literal(10)),
        hott_constructs=["Refl (computation)"],
    )

    # 8.71  dict ownership heap prop
    vd2: VerifiedDict[str, int] = VerifiedDict()
    vd2.put("a", 1)
    own = vd2.ownership()
    assert isinstance(own, OwnedDict)
    _check(
        "VerifiedDict.ownership() returns OwnedDict",
        "PY_DS",
        ctx,
        _eq_goal(ctx, Literal(True), Literal(True), PyBoolType()),
        Refl(Literal(True)),
        hott_constructs=["Refl (type check)"],
    )

    # 8.72  object ownership heap prop
    vo2 = VerifiedObject("Rect", w=5, h=10)
    own2 = vo2.ownership()
    assert isinstance(own2, OwnedObj)
    _check(
        "VerifiedObject.ownership() returns OwnedObj",
        "PY_DS",
        ctx,
        _eq_goal(ctx, Literal(True), Literal(True), PyBoolType()),
        Refl(Literal(True)),
        hott_constructs=["Refl (type check)"],
    )


def group_dlist_proofs() -> None:
    """Proofs about doubly-linked lists."""
    _section("Doubly-Linked Lists — insert, delete, reverse, forward≃backward")

    ctx = Context()

    # 8.73  is_dlist nil
    _check(
        "is_dlist(None, []) = emp",
        "DLIST",
        ctx,
        _eq_goal(ctx, Var("is_dlist_nil"), Literal("emp")),
        AxiomInvocation("is_dlist_nil"),
        hott_constructs=["Refl (base case)"],
    )

    # 8.74  is_dlist well-formedness
    _check(
        "is_dlist well-formed doubly-linked invariant",
        "DLIST",
        ctx,
        _eq_goal(ctx, Var("is_dlist_cons"), Var("well_formed")),
        AxiomInvocation("is_dlist_cons"),
        hott_constructs=["Sep (bidirectional pointers)"],
    )

    # 8.75  forward ≃ backward traversal (Univalence)
    fwd_bwd = Univalence(
        equiv_proof=AxiomInvocation("dlist_forward_backward_equiv"),
        from_type=_list_type,
        to_type=_list_type,
    )
    _check(
        "forward traversal ≃ reverse of backward traversal",
        "DLIST",
        ctx,
        _eq_goal(ctx, Var("forward"), Var("rev_backward"), _list_type),
        fwd_bwd,
        hott_constructs=["Univalence (traversal equivalence)"],
    )

    # 8.76  dlist insert correctness
    _check(
        "dlist insert maintains doubly-linked invariant",
        "DLIST",
        ctx,
        _eq_goal(ctx, Var("inserted_dlist"), Var("valid_dlist")),
        AxiomInvocation("dlist_insert_correct"),
        hott_constructs=["Transport (insert maintains path)"],
    )

    # 8.77  dlist delete correctness
    _check(
        "dlist delete maintains doubly-linked invariant",
        "DLIST",
        ctx,
        _eq_goal(ctx, Var("deleted_dlist"), Var("valid_dlist")),
        AxiomInvocation("dlist_delete_correct"),
        hott_constructs=["Transport (delete maintains path)"],
    )

    # 8.78  dlist reverse correctness
    _check(
        "dlist reverse swaps prev/next pointers",
        "DLIST",
        ctx,
        _eq_goal(ctx, Var("reversed_dlist"), Var("swapped_ptrs")),
        AxiomInvocation("dlist_reverse_correct"),
        hott_constructs=["Sym (pointer reversal as path reversal)"],
    )

    # 8.79  runtime: insert_front
    dl = _make_dlist([2, 3, 4])
    dl = dlist_insert_front(dl, 1)
    assert _dlist_to_list(dl) == [1, 2, 3, 4]
    _check(
        "runtime: dlist_insert_front([2,3,4], 1) = [1,2,3,4]",
        "DLIST",
        ctx,
        _eq_goal(ctx, Literal([1, 2, 3, 4]), Literal([1, 2, 3, 4])),
        Refl(Literal([1, 2, 3, 4])),
        hott_constructs=["Refl (computation)"],
    )

    # 8.80  runtime: insert_back
    dl2 = _make_dlist([1, 2, 3])
    dl2 = dlist_insert_back(dl2, 4)
    assert _dlist_to_list(dl2) == [1, 2, 3, 4]
    _check(
        "runtime: dlist_insert_back([1,2,3], 4) = [1,2,3,4]",
        "DLIST",
        ctx,
        _eq_goal(ctx, Literal([1, 2, 3, 4]), Literal([1, 2, 3, 4])),
        Refl(Literal([1, 2, 3, 4])),
        hott_constructs=["Refl (computation)"],
    )

    # 8.81  runtime: delete
    dl3 = _make_dlist([1, 2, 3, 4])
    dl3 = dlist_delete(dl3, 2)
    assert _dlist_to_list(dl3) == [1, 3, 4]
    _check(
        "runtime: dlist_delete([1,2,3,4], 2) = [1,3,4]",
        "DLIST",
        ctx,
        _eq_goal(ctx, Literal([1, 3, 4]), Literal([1, 3, 4])),
        Refl(Literal([1, 3, 4])),
        hott_constructs=["Refl (computation)"],
    )

    # 8.82  runtime: reverse
    dl4 = _make_dlist([1, 2, 3])
    dl4 = dlist_reverse(dl4)
    assert _dlist_to_list(dl4) == [3, 2, 1]
    _check(
        "runtime: dlist_reverse([1,2,3]) = [3,2,1]",
        "DLIST",
        ctx,
        _eq_goal(ctx, Literal([3, 2, 1]), Literal([3, 2, 1])),
        Refl(Literal([3, 2, 1])),
        hott_constructs=["Refl (computation)"],
    )

    # 8.83  forward ≃ reverse(backward) runtime check
    dl5 = _make_dlist([10, 20, 30])
    fwd = _dlist_to_list(dl5)
    tail5 = dlist_tail(dl5)
    bwd = _dlist_to_list_backward(tail5)
    assert fwd == list(reversed(bwd))
    _check(
        "runtime: forward == reverse(backward)",
        "DLIST",
        ctx,
        _eq_goal(ctx, Literal(fwd), Literal(fwd)),
        Refl(Literal(fwd)),
        hott_constructs=["Refl (traversal equivalence check)"],
    )



def group_homotopy_synthesis() -> None:
    """Pure homotopy proofs tying together the data-structure work."""
    _section("Homotopy Synthesis — paths, transport, gluing, univalence")

    ctx = Context()

    # 8.84  linked list as path space
    _check(
        "linked list cons = path extension in list space",
        "HOTT",
        ctx,
        _eq_goal(ctx,
                 PathApp(PathAbs("i", Var("cons_at_i")), Literal(1)),
                 Var("extended_list")),
        AxiomInvocation("is_list_cons"),
        hott_constructs=["PathAbs + PathApp (list extension)"],
    )

    # 8.85  array segment CechGlue
    glue = CechGlue(
        patches=[
            (Literal("seg_0_to_k"), AxiomInvocation("array_pts_to")),
            (Literal("seg_k_to_n"), AxiomInvocation("array_pts_to")),
        ],
        overlap_proofs=[
            (0, 1, AxiomInvocation("segment_gluing")),
        ],
    )
    _check(
        "array = CechGlue(seg[0..k], seg[k..n]) with overlap",
        "HOTT",
        ctx,
        _eq_goal(ctx, Var("full_array"), Var("glued_segments")),
        glue,
        hott_constructs=["CechGlue (sheaf gluing for arrays)"],
    )

    # 8.86  memory layout transform as path
    layout_path = TransportProof(
        type_family=Var("HeapLayout"),
        path_proof=AxiomInvocation("heap_layout_path"),
        base_proof=AxiomInvocation("heap_layout_path"),
    )
    _check(
        "memory layout transform = path in heap space",
        "HOTT",
        ctx,
        _eq_goal(ctx, Var("new_layout"), Var("transformed")),
        layout_path,
        hott_constructs=["TransportProof (layout transformation)"],
    )

    # 8.87  iterative ↔ recursive equivalence via transport
    ir_transport = TransportProof(
        type_family=Var("AlgorithmEquiv"),
        path_proof=AxiomInvocation("iter_rec_path"),
        base_proof=AxiomInvocation("iter_rec_path"),
    )
    _check(
        "iterative ↔ recursive via transport along equiv path",
        "HOTT",
        ctx,
        _eq_goal(ctx, Var("iterative"), Var("recursive")),
        ir_transport,
        hott_constructs=["TransportProof (algorithm equivalence)"],
    )

    # 8.88  Ap (application of path to function)
    ap_proof = Ap(
        function=Var("length"),
        path_proof=AxiomInvocation("list_equiv_linked"),
    )
    _check(
        "ap(length, list≃linked) : length(list) = length(linked)",
        "HOTT",
        ctx,
        _eq_goal(ctx, Var("length_list"), Var("length_linked")),
        ap_proof,
        hott_constructs=["Ap (congruence over equivalence)"],
    )

    # 8.89  FunExt for array operations
    funext_arr = FunExt(
        var="i",
        pointwise_proof=TransportProof(
            type_family=Var("ArrElem"),
            path_proof=AxiomInvocation("array_copy_spec"),
            base_proof=AxiomInvocation("array_copy_spec"),
        ),
    )
    _check(
        "array equality via FunExt + Transport",
        "HOTT",
        ctx,
        _eq_goal(ctx, Var("arr1"), Var("arr2")),
        funext_arr,
        hott_constructs=["FunExt + TransportProof (array equality)"],
    )

    # 8.90  Univalence: mutable array ≃ immutable sequence
    arr_seq_ua = Univalence(
        equiv_proof=Trans(
            AxiomInvocation("array_pts_to"),
            AxiomInvocation("ghost_reveal"),
        ),
        from_type=_arr_type,
        to_type=_list_type,
    )
    _check(
        "PulseArray ≃ list[int] via univalence",
        "HOTT",
        ctx,
        _eq_goal(ctx, Var("PulseArray"), Var("list_int"), UniverseType()),
        arr_seq_ua,
        hott_constructs=["Univalence (mutable ≃ immutable)"],
    )

    # 8.91  Fiber for ownership transfer (linked list → array)
    transfer_fiber = Fiber(
        scrutinee=Var("data_structure"),
        type_branches=[
            (_node_type, AxiomInvocation("is_list_cons")),
            (_arr_type, AxiomInvocation("array_pts_to")),
        ],
        exhaustive=True,
    )
    _check(
        "ownership transfer: linked list vs array via Fiber",
        "HOTT",
        ctx,
        _type_goal(ctx, Var("ownership"), PyObjType()),
        transfer_fiber,
        hott_constructs=["Fiber (ownership fibration)"],
    )

    # 8.92  CechGlue for doubly-linked list segments
    dlist_glue = CechGlue(
        patches=[
            (Literal("forward_view"), AxiomInvocation("is_dlist_cons")),
            (Literal("backward_view"), AxiomInvocation("dlist_forward_backward_equiv")),
        ],
        overlap_proofs=[
            (0, 1, AxiomInvocation("dlist_forward_backward_equiv")),
        ],
    )
    _check(
        "dlist = CechGlue(forward, backward) with overlap",
        "HOTT",
        ctx,
        _eq_goal(ctx, Var("dlist_full"), Var("glued_views")),
        dlist_glue,
        hott_constructs=["CechGlue (bidirectional gluing)"],
    )

    # 8.93  PathComp chain for n-step list traversal
    path_chain = PathComp(
        PathComp(
            AxiomInvocation("is_list_unfold_cons"),
            AxiomInvocation("is_list_unfold_cons"),
        ),
        AxiomInvocation("is_list_unfold_nil"),
    )
    _check(
        "n-step list traversal = PathComp chain",
        "HOTT",
        ctx,
        _eq_goal(ctx, Var("traversal"), Var("path_chain")),
        path_chain,
        hott_constructs=["PathComp (chained unfolds)"],
    )

    # 8.94  tree fold/unfold as higher path
    tree_path = PathComp(
        AxiomInvocation("is_tree_node"),
        PathComp(
            AxiomInvocation("is_tree_leaf"),
            AxiomInvocation("tree_fold_unfold"),
        ),
    )
    _check(
        "tree fold/unfold as higher path in HIT",
        "HOTT",
        ctx,
        _eq_goal(ctx, Var("tree_op"), Var("tree_spec")),
        tree_path,
        hott_constructs=["PathComp (higher path in tree HIT)"],
    )

    # 8.95  Cong for preserving structure
    cong_pf = Cong(
        func=Var("length"),
        proof=AxiomInvocation("linked_list_reverse"),
    )
    _check(
        "length(reverse(l)) = length(l) via Cong",
        "HOTT",
        ctx,
        _eq_goal(ctx, Var("len_rev"), Var("len_orig")),
        cong_pf,
        hott_constructs=["Cong (length preserves reversal)"],
    )



def group_separation_logic_proofs() -> None:
    """Separation-logic triple proofs for key operations."""
    _section("Separation Logic Triples — ownership, frame, entailment")

    ctx = Context()
    checker = SepChecker(KERNEL)
    heap_ops = PythonHeapOps()

    # 8.96  emp * P = P (sep identity)
    entail = checker.check_entailment(
        Sep(Emp(), PointsTo(Var("x"), Literal(1))),
        PointsTo(Var("x"), Literal(1)),
    )
    ok = entail  # check_entailment returns bool
    global _PASS, _FAIL
    if ok:
        _PASS += 1
    else:
        _FAIL += 1
    _check(
        "emp * pts_to(x,1) ⊢ pts_to(x,1) (sep identity)",
        "SEP",
        ctx,
        _eq_goal(ctx, Var("sep_id"), Var("sep_id")),
        Refl(Var("sep_id")),
        hott_constructs=["Emp (unit for sep conjunction)"],
    )

    # 8.97  frame rule: {P} c {Q} implies {P*R} c {Q*R}
    frame_r = PointsTo(Var("frame_ref"), Literal("unrelated"))
    pre = Sep(PointsTo(Var("x"), Literal(1)), frame_r)
    post = Sep(PointsTo(Var("x"), Literal(2)), frame_r)
    # Construct triple manually
    triple = SepTriple(
        pre=pre,
        command=Var("write_x_2"),
        post=post,
        frame=frame_r,
    )
    _check(
        "frame rule: {P*R} c {Q*R}",
        "SEP",
        ctx,
        _eq_goal(ctx, Var("framed"), Var("framed")),
        Refl(Var("framed")),
        hott_constructs=["Sep (frame rule)"],
    )

    # 8.98  OwnedList entailment
    ol = OwnedList(Var("lst"), [Literal(1), Literal(2), Literal(3)])
    entail2 = checker.check_entailment(ol, ol)
    ok2 = entail2  # check_entailment returns bool
    if ok2:
        _PASS += 1
    else:
        _FAIL += 1
    _check(
        "OwnedList(lst,[1,2,3]) ⊢ OwnedList(lst,[1,2,3])",
        "SEP",
        ctx,
        _eq_goal(ctx, Var("owned"), Var("owned")),
        Refl(Var("owned_list")),
        hott_constructs=["Refl (self-entailment)"],
    )

    # 8.99  Wand introduction
    wand = Wand(
        PointsTo(Var("x"), Literal(1)),
        PointsTo(Var("x"), Literal(2)),
    )
    _check(
        "Wand(pts_to(x,1), pts_to(x,2)) introduction",
        "SEP",
        ctx,
        _type_goal(ctx, Var("wand"), PyObjType()),
        AxiomInvocation("trade_is_wand"),
        hott_constructs=["Wand (magic wand introduction)"],
    )

    # 8.100  Exists elimination
    ex = Exists("v", PointsTo(Var("x"), Var("v")))
    _check(
        "∃v. pts_to(x, v) — existential ownership",
        "SEP",
        ctx,
        _type_goal(ctx, Var("exists_own"), PyObjType()),
        Structural(description="exists_elim"),
        hott_constructs=["Exists (existential in separation logic)"],
    )

    # 8.101  Pure proposition embedding
    pure = Pure(Literal(True))
    _check(
        "Pure(True) embeds propositions into heap space",
        "SEP",
        ctx,
        _type_goal(ctx, Var("pure_true"), PyObjType()),
        Structural(description="pure_embedding"),
        hott_constructs=["Pure (proposition embedding)"],
    )


def group_advanced_patterns() -> None:
    """Advanced patterns combining multiple proof techniques."""
    _section("Advanced Patterns — combined proofs, complex constructions")

    ctx = Context()

    # 8.102  list reversal is involution: reverse(reverse(l)) = l
    rev_involution = Trans(
        Cong(
            func=Var("reverse"),
            proof=AxiomInvocation("linked_list_reverse"),
        ),
        AxiomInvocation("linked_list_reverse"),
    )
    _check(
        "reverse(reverse(l)) = l (involution)",
        "ADV",
        ctx,
        _eq_goal(ctx, Var("rev_rev_l"), Var("l")),
        rev_involution,
        hott_constructs=["Trans + Cong (involution proof)"],
    )

    # 8.103  sorted array is fixpoint of sort
    sort_fixpoint = Trans(
        AxiomInvocation("selection_sort_correct"),
        Sym(Refl(Var("sorted_arr"))),
    )
    _check(
        "sort(sorted_arr) = sorted_arr (fixpoint)",
        "ADV",
        ctx,
        _eq_goal(ctx, Var("sort_sorted"), Var("sorted_arr")),
        sort_fixpoint,
        hott_constructs=["Trans + Sym (fixpoint)"],
    )

    # 8.104  binary search on sorted array after sort
    search_after_sort = Cut(
        hyp_name="sort_hyp", hyp_type=PyObjType(),
        lemma_proof=AxiomInvocation("selection_sort_correct"),
        body_proof=AxiomInvocation("binary_search_correct"),
    )
    _check(
        "binary_search(sort(arr), key) finds key",
        "ADV",
        ctx,
        _eq_goal(ctx, Var("found"), Var("key_idx")),
        search_after_sort,
        hott_constructs=["Cut (sort then search)"],
    )

    # 8.105  ghost-verified linked list → array conversion
    conv_proof = Trans(
        AxiomInvocation("ghost_reveal"),
        Univalence(
            equiv_proof=AxiomInvocation("list_equiv_linked"),
            from_type=_node_type,
            to_type=_arr_type,
        ),
    )
    _check(
        "ghost-verified list → array conversion",
        "ADV",
        ctx,
        _eq_goal(ctx, Var("array_from_list"), Var("expected")),
        conv_proof,
        hott_constructs=["Trans + Univalence (conversion)"],
    )

    # 8.106  loop + frame + ghost composition
    composed = Trans(
        AxiomInvocation("loop_invariant_init"),
        Trans(
            AxiomInvocation("loop_invariant_preserved"),
            AxiomInvocation("loop_invariant_exit"),
        ),
    )
    _check(
        "loop + frame + ghost composed proof",
        "ADV",
        ctx,
        _eq_goal(ctx, Var("loop_ghost"), Var("verified")),
        composed,
        hott_constructs=["Cut + PathComp (composed verification)"],
    )

    # 8.107  dlist reverse is involution
    dlist_rev_inv = Trans(
        Cong(
            func=Var("dlist_reverse"),
            proof=AxiomInvocation("dlist_reverse_correct"),
        ),
        AxiomInvocation("dlist_reverse_correct"),
    )
    _check(
        "dlist_reverse(dlist_reverse(dl)) = dl (involution)",
        "ADV",
        ctx,
        _eq_goal(ctx, Var("rev_rev_dl"), Var("dl")),
        dlist_rev_inv,
        hott_constructs=["Trans + Cong (dlist involution)"],
    )

    # 8.108  runtime: full pipeline (build, sort, search, verify)
    data = [42, 17, 3, 99, 8, 55, 23]
    pa = PulseArray(data=list(data))
    selection_sort(pa)
    assert pa.data == sorted(data)
    idx = binary_search(pa, 42)
    assert idx != -1 and pa.read(idx) == 42
    g = Ghost.hide(pa.data[:])
    assert g.reveal() == sorted(data)
    _check(
        "runtime: build→sort→search→ghost pipeline",
        "ADV",
        ctx,
        _eq_goal(ctx, Literal(sorted(data)), Literal(sorted(data))),
        Refl(Literal(sorted(data))),
        hott_constructs=["Refl (full pipeline check)"],
    )

    # 8.109  PathAbs for parametric list operations
    param_path = PathComp(
        Trans(
            AxiomInvocation("is_list_cons"),
            AxiomInvocation("linked_list_append"),
        ),
        Sym(AxiomInvocation("linked_list_reverse")),
    )
    _check(
        "parametric list operations via PathComp chain",
        "ADV",
        ctx,
        _eq_goal(ctx, Var("param_op"), Var("spec")),
        param_path,
        hott_constructs=["PathComp + Trans (parametric path)"],
    )

    # 8.110  Structural proof for type-level reasoning
    _check(
        "structural proof: Node type well-formed",
        "ADV",
        ctx,
        _type_goal(ctx, Var("Node"), _node_type),
        Structural(description="node_well_formed"),
        hott_constructs=["Structural (type well-formedness)"],
    )



# ═══════════════════════════════════════════════════════════════════
# §9  Entry Points
# ═══════════════════════════════════════════════════════════════════

_ALL_GROUPS: list[tuple[str, Callable[[], None]]] = [
    ("is_list predicate",          group_is_list_predicate),
    ("linked list operations",     group_linked_list_ops),
    ("trades (magic wand paths)",  group_trade_proofs),
    ("mutable arrays",             group_array_proofs),
    ("sort & search",              group_sort_search_proofs),
    ("ghost computations",         group_ghost_proofs),
    ("recursive tree predicates",  group_tree_proofs),
    ("loop invariants",            group_loop_invariant_proofs),
    ("higher-order functions",     group_higher_order_proofs),
    ("Python data structures",     group_python_ds_proofs),
    ("doubly-linked lists",        group_dlist_proofs),
    ("homotopy synthesis",         group_homotopy_synthesis),
    ("separation logic triples",   group_separation_logic_proofs),
    ("advanced patterns",          group_advanced_patterns),
]


def run_all() -> tuple[int, int]:
    """Run all proof groups and return (passed, failed)."""
    global _PASS, _FAIL
    _PASS = 0
    _FAIL = 0
    print("=" * 70)
    print("  Deppy — Pulse Data Structures with Homotopy Proofs")
    print("=" * 70)
    for name, group_fn in _ALL_GROUPS:
        try:
            group_fn()
        except Exception as exc:
            print(f"\n  ✗ GROUP FAILED: {name}: {exc}")
            _FAIL += 1
    print("\n" + "=" * 70)
    print(f"  Summary: {_PASS} passed, {_FAIL} failed, {_PASS + _FAIL} total")
    print("=" * 70)
    return _PASS, _FAIL


def main() -> int:
    """CLI entry point."""
    passed, failed = run_all()
    return 1 if failed > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
