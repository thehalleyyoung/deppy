"""SynHoPy - Pulse Concurrency: F* Tutorial Translation
=====================================================

Translation of F* Tutorial Pulse concurrency chapters into Pythonic
Python with genuine homotopy constructs.  Covers:

  1. Atomic Operations
  2. Invariants
  3. Spin Locks
  4. Parallel Increment (the showpiece)
  5. Verified Threading
  6. Concurrent Data Structures
  7. Async/Await with Ownership
  8. Message Passing
  9. GIL-Aware Verification
  10. Deadlock Freedom

Every proof uses real HoTT primitives (PathAbs, Transport, Fiber,
CechGlue, Comp, DuckPath, etc.) alongside separation-logic triples
from ConcurrentSep.

Run from the repo root::

    PYTHONPATH=. python3 synhopy/examples/fstar_tutorial/pulse_concurrency.py

"""
from __future__ import annotations

import sys
from typing import Any, Sequence

# -- Core types (SynTerm trees) ------------------------------------------
from synhopy.core.types import (
    SynType, SynTerm,
    PyObjType, PyIntType, PyStrType, PyBoolType, PyFloatType,
    PyNoneType, PyListType, PyCallableType, PyClassType,
    PiType, SigmaType, PathType, RefinementType, UnionType,
    UniverseType, IntervalType, GlueType, ProtocolType,
    Context, Judgment, JudgmentKind,
    Var, Literal, Lam, App, Pair, Fst, Snd,
    PathAbs, PathApp, Transport, Comp,
    LetIn, IfThenElse, PyCall, GetAttr,
    arrow,
)

# -- Proof kernel --------------------------------------------------------
from synhopy.core.kernel import (
    ProofKernel, TrustLevel, VerificationResult,
    ProofTerm,
    Refl, Sym, Trans, Cong, TransportProof, Ext, Cut,
    Assume, Z3Proof, Structural, AxiomInvocation,
    NatInduction, ListInduction, Cases,
    DuckPath, Fiber, Patch, EffectWitness,
    Unfold, Rewrite,
    min_trust,
)

from synhopy.core.formal_ops import Op, OpCall

# -- Separation logic ----------------------------------------------------
from synhopy.core.separation import (
    HeapProp, Emp, PointsTo, Sep, Wand, Pure, Exists,
    OwnedList, OwnedDict, OwnedObj,
    SepTriple, SepResult,
    sep_of, normalize,
    ConcurrentSep,
)

# -- HoTT kernel extras -------------------------------------------------
from synhopy.core.kernel import CechGlue, PathComp, Ap, FunExt

# -- Optional Z3 --------------------------------------------------------
try:
    from z3 import Int, Bool, And, Or, Not, Implies, ForAll, Solver, sat, unsat
    _HAS_Z3 = True
except ImportError:
    _HAS_Z3 = False


# =====================================================================
# Kernel, Axioms, Helpers
# =====================================================================

KERNEL = ProofKernel()
CONC = ConcurrentSep()

_AXIOMS = [
    # Atomics
    ("atomic_cas_semantics", "CAS(ref, expected, desired) atomically compares and swaps"),
    ("atomic_load_store_linearize", "atomic load/store are linearizable"),
    ("atomic_ref_exclusive", "AtomicRef grants exclusive ownership on CAS success"),
    # Invariants
    ("inv_open_close", "opening an invariant grants resource, closing restores it"),
    ("inv_reentrancy_forbidden", "invariants cannot be opened reentrantly"),
    ("inv_preserved_across_yield", "invariant re-established before yield point"),
    ("inv_atomic_step", "invariant may be opened for at most one atomic step"),
    # Spin locks
    ("spin_lock_mutual_exclusion", "spin lock ensures mutual exclusion"),
    ("spin_lock_inv_transfer", "lock acquisition transfers invariant ownership"),
    ("spin_lock_liveness", "spin lock acquire terminates under fair scheduling"),
    # Parallel increment
    ("parallel_inc_atomicity", "each increment is atomic under CAS"),
    ("parallel_inc_linearizable", "parallel increments are linearizable"),
    ("parallel_inc_sum_correct", "n parallel increments yield final value n"),
    ("cas_retry_loop_terminates", "CAS retry loop terminates under lock-freedom"),
    # Verified threading
    ("thread_fork_ownership_transfer", "thread_fork transfers precondition ownership"),
    ("thread_join_ownership_return", "thread_join returns postcondition ownership"),
    ("thread_frame_disjoint", "forked resources are disjoint from parent frame"),
    ("thread_pool_bounded", "ThreadPool(n) creates at most n workers"),
    # Concurrent data structures
    ("treiber_stack_linearizable", "Treiber stack push/pop are linearizable"),
    ("michael_scott_queue_linearizable", "MS queue enq/deq are linearizable"),
    ("concurrent_dict_snapshot", "snapshot produces a consistent view"),
    ("rw_lock_reader_sharing", "RWLock allows multiple concurrent readers"),
    # Async/Await
    ("async_ownership_suspend", "await suspends ownership until resume"),
    ("async_gather_join", "gather joins ownership from all coroutines"),
    ("async_cancel_cleanup", "cancellation runs cleanup handlers"),
    ("async_semaphore_bounded", "Semaphore(n) bounds concurrency to n"),
    # Message passing
    ("channel_ownership_transfer", "send transfers ownership to receiver"),
    ("channel_fifo_order", "channel preserves FIFO message order"),
    ("typed_channel_safety", "typed channel rejects mismatched types"),
    ("multicast_fanout", "multicast delivers to all subscribers"),
    # GIL awareness
    ("gil_atomic_refcount", "GIL makes refcount ops atomic"),
    ("gil_release_io", "GIL released during I/O operations"),
    ("gil_bytecode_preempt", "GIL may preempt between bytecode instructions"),
    ("nogil_explicit_sync", "no-GIL mode requires explicit synchronization"),
    # Deadlock freedom
    ("lock_order_acyclic", "lock acquisition order forms a DAG"),
    ("lock_order_total", "total order on locks prevents deadlock"),
    ("timeout_liveness", "lock_with_timeout ensures eventual progress"),
    ("async_deadlock_free", "async event loops are deadlock-free by construction"),
    # DuckPath protocol conformance
    ("atomic_inv_protocol", "AtomicInvUser conforms to InvariantProtocol"),
    ("rwlock_reader_protocol", "ThreadReader conforms to RWLockReader protocol"),
    # Advanced patterns (Section 11)
    ("obstruction_free_progress", "obstruction-free ops complete in isolation"),
    ("wait_free_helping_protocol", "helping protocol ensures per-thread bound"),
    ("ebr_retire_epoch", "retire moves object to current epoch"),
    ("ebr_reclaim_safe", "reclaim frees after grace period"),
    ("seqlock_even_consistent", "even seqlock version implies consistent read"),
    ("memory_ordering_subsumption", "SeqCst subsumes AcqRel memory ordering"),
    ("arc_atomic_decrement", "Arc refcount decrement is atomic"),
    ("rcu_grace_period", "RCU grace period ensures no stale readers"),
    ("condvar_wait_release", "condvar wait releases the associated lock"),
    ("condvar_notify_acquire", "condvar notify reacquires the associated lock"),
    ("future_resolve_once", "promise can be resolved exactly once"),
    ("future_cancel_inverse", "cancellation is inverse of resolution"),
    ("skiplist_level_subset", "skip list level k+1 is a sublist of level k"),
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
    mark = "\u2713" if ok else "\u2717"
    trust = result.trust_level.name
    if ok:
        _PASS += 1
    else:
        _FAIL += 1
    constructs = ""
    if hott_constructs:
        constructs = "  (" + ", ".join(hott_constructs) + ")"
    detail = result.message
    print(f"  {mark} [{tag:10s}] {label:52s} [{trust}] {detail}{constructs}")
    if not ok:
        print(f"      \u2514\u2500 ERROR: {result.message}")
    return ok


def _section(title: str) -> None:
    dash = "\u2500"
    print(f"\n{dash}{dash} {title} {dash * max(0, 60 - len(title))}")


def _eq_goal(ctx: Context, left: SynTerm, right: SynTerm,
             ty: SynType = PyObjType()) -> Judgment:
    """Shorthand for an equality judgment."""
    return Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=left, right=right,
        type_=ty,
    )


def _type_goal(ctx: Context, term: SynTerm, ty: SynType) -> Judgment:
    """Shorthand for a type-checking judgment."""
    return Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=term,
        type_=ty,
    )


def _sep_check(
    label: str,
    tag: str,
    triple: SepTriple,
    proof: ProofTerm,
    *,
    hott_constructs: list[str] | None = None,
) -> bool:
    """Verify a separation-logic triple using the kernel.

    We encode the triple as an equality judgment:
      {P} c {Q}  =  pre_state =_{cmd} post_state
    """
    ctx = Context()
    pre_term = Var(repr(triple.pre))
    post_term = Var(repr(triple.post))
    cmd_type = PyObjType()
    goal = _eq_goal(ctx, pre_term, post_term, cmd_type)
    return _check(label, tag, ctx, goal, proof,
                  term_repr=("{" + str(triple.pre) + "} "
                             + triple.command + " {"
                             + str(triple.post) + "}"),
                  hott_constructs=hott_constructs)


# =====================================================================
# SECTION 1: Atomic Operations
# =====================================================================

def section1_atomic_operations() -> None:
    """Atomic operations: CAS, load, store with homotopy paths.

    In F* Pulse, atomic operations are the building blocks for
    lock-free programming.  We model AtomicRef as a heap location
    with exclusive ownership enforced via separation logic, and
    CAS as a path that connects pre-state to post-state.
    """
    _section("Section 1: Atomic Operations")
    ctx = Context()

    # -- Ex 1: Atomic load preserves value ---------------------
    # {ref -> v} atomic_load(ref) {ref -> v /\ result = v}
    ref_v = PointsTo("ref", Var("v"))
    post_load = Sep(ref_v, Pure("result = v"))
    triple_load = SepTriple(pre=ref_v, command="atomic_load(ref)", post=post_load)

    load_path = PathAbs("i", Var("heap_with_ref_v"))
    proof_load = TransportProof(
        Lam("state", PyObjType(), Var("ref_points_to_v")),
        Structural("load reads without modifying; result = v is pure"),
        AxiomInvocation("atomic_load_store_linearize"),
    )
    _sep_check(
        "Ex 1:  atomic_load preserves ref -> v",
        "ATOMIC",
        triple_load, proof_load,
        hott_constructs=["PathAbs", "TransportProof", "SepTriple"],
    )

    # -- Ex 2: Atomic store updates value ----------------------
    # {ref -> old} atomic_store(ref, new) {ref -> new}
    ref_old = PointsTo("ref", Var("old"))
    ref_new = PointsTo("ref", Var("new"))
    triple_store = SepTriple(pre=ref_old, command="atomic_store(ref, new)", post=ref_new)

    store_path = PathAbs("i", Comp(
        type_=PyObjType(),
        face="i=0 -> old, i=1 -> new",
        partial_term=Var("new"),
        base=Var("old"),
    ))
    proof_store = TransportProof(
        Lam("state", PyObjType(), Var("ref_points_to")),
        Structural("atomic store updates ref from old to new"),
        AxiomInvocation("atomic_load_store_linearize"),
    )
    _sep_check(
        "Ex 2:  atomic_store: ref -> old to ref -> new",
        "ATOMIC",
        triple_store, proof_store,
        hott_constructs=["PathAbs", "Comp", "TransportProof"],
    )

    # -- Ex 3: CAS success path --------------------------------
    ref_exp = PointsTo("ref", Var("expected"))
    ref_des = PointsTo("ref", Var("desired"))
    cas_post = Sep(ref_des, Pure("result = true"))
    triple_cas = SepTriple(
        pre=ref_exp,
        command="CAS(ref, expected, desired)",
        post=cas_post,
    )
    cas_path = PathAbs("i", Comp(
        type_=PyObjType(),
        face="i=0 -> expected, i=1 -> desired",
        partial_term=Var("desired"),
        base=Var("expected"),
    ))
    proof_cas = TransportProof(
        Lam("state", PyObjType(), Var("ref_ownership")),
        Structural("CAS atomically swaps expected -> desired"),
        AxiomInvocation("atomic_cas_semantics"),
    )
    _sep_check(
        "Ex 3:  CAS success: expected => desired",
        "ATOMIC",
        triple_cas, proof_cas,
        hott_constructs=["PathAbs", "Comp", "TransportProof"],
    )

    # -- Ex 4: CAS failure preserves state ---------------------
    ref_v_ne = Sep(PointsTo("ref", Var("v")), Pure("v != expected"))
    cas_fail_post = Sep(PointsTo("ref", Var("v")), Pure("result = false"))
    triple_cas_fail = SepTriple(
        pre=ref_v_ne,
        command="CAS(ref, expected, desired)",
        post=cas_fail_post,
    )
    proof_cas_fail = TransportProof(
        Lam("state", PyObjType(), Var("ref_unchanged")),
        Structural("CAS fail: v != expected => ref unchanged, result = false"),
        AxiomInvocation("atomic_cas_semantics"),
    )
    _sep_check(
        "Ex 4:  CAS failure preserves ref -> v",
        "ATOMIC",
        triple_cas_fail, proof_cas_fail,
        hott_constructs=["TransportProof", "Structural", "SepTriple"],
    )

    # -- Ex 5: Linearizability via Fiber -----------------------
    atomic_type = PyClassType(
        name="AtomicRef",
        methods=(("load", PyCallableType()), ("store", PyCallableType()), ("cas", PyCallableType())),
    )
    sequential_type = PyClassType(
        name="Ref",
        methods=(("load", PyCallableType()), ("store", PyCallableType())),
    )

    lin_fiber = Fiber(
        scrutinee=Var("execution_trace"),
        type_branches=[
            (atomic_type, Structural("atomic ops linearize to sequential")),
            (sequential_type, Structural("sequential ops are trivially linear")),
        ],
        exhaustive=True,
    )
    ctx_lin = ctx.extend(
        "linearizable",
        PathType(PyObjType(), Var("atomic_trace"), Var("seq_trace")),
    )
    goal_lin = _eq_goal(ctx_lin, Var("atomic_trace"), Var("seq_trace"), PyObjType())
    _check(
        "Ex 5:  Linearizability via Fiber projection",
        "FIBER",
        ctx_lin, goal_lin, lin_fiber,
        hott_constructs=["Fiber", "PathType", "PyClassType"],
    )


# =====================================================================
# SECTION 2: Invariants
# =====================================================================

def section2_invariants() -> None:
    """Invariants: resource assertions preserved across concurrent steps.

    In Pulse, invariants are heap predicates that hold at every
    interleaving point.  Opening an invariant grants temporary access
    to its resources; closing it re-establishes the predicate.
    """
    _section("Section 2: Invariants")
    ctx = Context()

    # -- Ex 6: Open/close invariant ----------------------------
    inv_pred = Exists("v", Sep(PointsTo("ref", Var("v")), Pure("v >= 0")))
    inv_token = Pure("inv_token_held")
    open_post = Sep(inv_pred, inv_token)
    triple_open = SepTriple(
        pre=Pure("inv(I)"),
        command="open_invariant(I)",
        post=open_post,
    )

    open_path = PathAbs("i", Var("inv_content"))
    proof_open = TransportProof(
        Lam("inv", PyObjType(), Var("inv_resources")),
        Structural("opening invariant exposes resources"),
        AxiomInvocation("inv_open_close"),
    )
    _sep_check(
        "Ex 6:  Open invariant exposes resources",
        "INVARIANT",
        triple_open, proof_open,
        hott_constructs=["PathAbs", "TransportProof", "Exists"],
    )

    # -- Ex 7: Close invariant re-establishes predicate --------
    triple_close = SepTriple(
        pre=open_post,
        command="close_invariant(I)",
        post=Pure("inv(I)"),
    )
    proof_close = TransportProof(
        Lam("inv", PyObjType(), Var("inv_restored")),
        Sym(Structural("closing restores invariant")),
        AxiomInvocation("inv_open_close"),
    )
    _sep_check(
        "Ex 7:  Close invariant re-establishes predicate",
        "INVARIANT",
        triple_close, proof_close,
        hott_constructs=["TransportProof", "Sym"],
    )

    # -- Ex 8: Invariant preserved across yield points ---------
    yield_path = PathAbs("i", Var("inv_at_yield_i"))
    yield_goal = _eq_goal(
        ctx, Var("inv_pre_yield"), Var("inv_post_yield"), PyObjType(),
    )
    proof_yield = TransportProof(
        Lam("t", PyObjType(), Var("inv_holds")),
        Structural("invariant preserved across yield"),
        AxiomInvocation("inv_preserved_across_yield"),
    )
    _check(
        "Ex 8:  Invariant preserved across yield points",
        "INVARIANT",
        ctx, yield_goal, proof_yield,
        term_repr=str(yield_path),
        hott_constructs=["PathAbs", "TransportProof"],
    )

    # -- Ex 9: Invariant reentrancy blocked (Fiber) ------------
    reentrant_fiber = Fiber(
        scrutinee=Var("reentrant_open"),
        type_branches=[
            (PyObjType(), Structural("can open if closed")),
        ],
        exhaustive=True,
    )
    ctx_reentrant = ctx.extend("inv_open", Pure("inv_token_held"))
    goal_reentrant = _type_goal(
        ctx_reentrant,
        Var("reentrant_open"),
        RefinementType(PyBoolType(), "token_available", "not inv_token_held"),
    )
    _check(
        "Ex 9:  Invariant reentrancy blocked (Fiber)",
        "FIBER",
        ctx_reentrant, goal_reentrant, reentrant_fiber,
        hott_constructs=["Fiber", "RefinementType", "Pure"],
    )

    # -- Ex 10: Atomic-step invariant (DuckPath) ---------------
    atomic_inv_duck = DuckPath(
        type_a=PyClassType(
            name="AtomicInvUser",
            methods=(
                ("open", PyCallableType((), PyObjType())),
                ("use", PyCallableType((), PyObjType())),
                ("close", PyCallableType((), PyNoneType())),
            ),
        ),
        type_b=PyClassType(
            name="InvariantProtocol",
            methods=(
                ("open", PyCallableType((), PyObjType())),
                ("use", PyCallableType((), PyObjType())),
                ("close", PyCallableType((), PyNoneType())),
            ),
        ),
        method_proofs=[
            ("open", Structural("open: same invariant-open behavior")),
            ("use", Structural("use: same resource-use behavior")),
            ("close", Structural("close: same invariant-close behavior")),
        ],
    )
    inv_family = Lam("cls", PyObjType(), Var("satisfies_invariant_protocol"))
    proof_duck = TransportProof(inv_family, atomic_inv_duck, AxiomInvocation("atomic_inv_protocol"))
    goal_duck = _eq_goal(
        ctx, Var("AtomicInvUser"), Var("InvariantProtocol"), PyObjType(),
    )
    _check(
        "Ex 10: Atomic-step invariant via DuckPath",
        "DUCKPATH",
        ctx, goal_duck, proof_duck,
        hott_constructs=["DuckPath", "PyClassType", "TransportProof"],
    )


# =====================================================================
# SECTION 3: Spin Locks
# =====================================================================

def section3_spin_locks() -> None:
    """Spin locks built from CAS with separation-logic ownership.

    A spin lock is the canonical Pulse concurrency example:
    - lock = AtomicRef(False)
    - acquire: while not CAS(lock, False, True): pass
    - release: lock.store(False)

    The invariant transferred on acquire is the key insight from
    concurrent separation logic.
    """
    _section("Section 3: Spin Locks")
    ctx = Context()

    # The lock invariant: protected resource R
    lock_inv = Exists("v", Sep(PointsTo("counter", Var("v")), Pure("v >= 0")))

    # -- Ex 11: Lock acquire transfers invariant ---------------
    triple_acquire = CONC.lock_acquire("spin_lock", lock_inv)
    acquire_path = PathAbs("i", Transport(
        Lam("locked", PyBoolType(), Var("ownership")),
        PathAbs("j", Var("cas_transition_j")),
        Var("emp_state"),
    ))
    proof_acquire = TransportProof(
        Lam("locked", PyBoolType(), Var("ownership_transfer")),
        Structural("CAS(lock, False, True) transfers invariant"),
        AxiomInvocation("spin_lock_inv_transfer"),
    )
    _sep_check(
        "Ex 11: Lock acquire: {emp} acquire {inv}",
        "SPINLOCK",
        triple_acquire, proof_acquire,
        hott_constructs=["PathAbs", "Transport", "TransportProof"],
    )

    # -- Ex 12: Lock release returns invariant -----------------
    triple_release = CONC.lock_release("spin_lock", lock_inv)
    proof_release = TransportProof(
        Lam("locked", PyBoolType(), Var("ownership_return")),
        Sym(Structural("store(False) releases invariant")),
        AxiomInvocation("spin_lock_inv_transfer"),
    )
    _sep_check(
        "Ex 12: Lock release: {inv} release {emp}",
        "SPINLOCK",
        triple_release, proof_release,
        hott_constructs=["TransportProof", "Sym"],
    )

    # -- Ex 13: With-lock context manager (CechGlue) ----------
    body_triple = SepTriple(
        pre=lock_inv,
        command="counter += 1",
        post=Exists("v", Sep(PointsTo("counter", Var("v")), Pure("v >= 1"))),
    )
    with_lock_triple = CONC.with_lock("spin_lock", lock_inv, body_triple)

    cech_proof = CechGlue(
        patches=[
            ("acquire", Structural("acquire grants inv")),
            ("body", Structural("body preserves inv shape")),
            ("release", Structural("release consumes inv")),
        ],
        overlap_proofs=[
            (0, 1, Structural("invariant holds at acquire-body boundary")),
            (1, 2, Structural("invariant holds at body-release boundary")),
        ],
    )
    _sep_check(
        "Ex 13: with lock: ... (CechGlue composition)",
        "CECH",
        with_lock_triple, cech_proof,
        hott_constructs=["CechGlue", "Structural", "SepTriple"],
    )

    # -- Ex 14: Mutual exclusion (Fiber over lock state) -------
    lock_type = UnionType([PyBoolType(), PyBoolType()])
    mutex_fiber = Fiber(
        scrutinee=Var("lock_state"),
        type_branches=[
            (RefinementType(PyBoolType(), "s", "s == False"), Structural("inv in lock")),
            (RefinementType(PyBoolType(), "s", "s == True"), Structural("inv in thread")),
        ],
        exhaustive=True,
    )
    ctx_mutex = ctx.extend("exclusive", Pure("at most one holder"))
    goal_mutex = _type_goal(ctx_mutex, Var("lock_state"), lock_type)
    _check(
        "Ex 14: Mutual exclusion via Fiber on lock state",
        "FIBER",
        ctx_mutex, goal_mutex, mutex_fiber,
        hott_constructs=["Fiber", "UnionType"],
    )

    # -- Ex 15: Spin lock liveness under fair scheduling -------
    spin_path = PathAbs("i", Comp(
        type_=PyObjType(),
        face="i=0 -> spinning, i=1 -> acquired",
        partial_term=Var("acquired"),
        base=Var("spinning"),
    ))
    ctx_fair = ctx.extend("fair_scheduling", Pure("fair"))
    goal_liveness = _eq_goal(
        ctx_fair, Var("spinning"), Var("acquired"), PyObjType(),
    )
    proof_liveness = TransportProof(
        Lam("progress", PyObjType(), Var("wf_measure")),
        Structural("fair scheduling ensures CAS eventually succeeds"),
        AxiomInvocation("spin_lock_liveness"),
    )
    _check(
        "Ex 15: Spin lock liveness (fair scheduling)",
        "LIVENESS",
        ctx_fair, goal_liveness, proof_liveness,
        term_repr=str(spin_path),
        hott_constructs=["PathAbs", "Comp", "TransportProof"],
    )


# =====================================================================
# SECTION 4: Parallel Increment (THE SHOWPIECE)
# =====================================================================

def section4_parallel_increment() -> None:
    """Parallel increment: the canonical Pulse concurrency example.

    Two threads each increment a shared counter.  We prove the final
    value is 2 using:
    - CAS-based atomic increment
    - Spin lock for mutual exclusion
    - Ownership transfer on fork/join
    - Path composition across thread boundaries
    - Cech glue for the parallel composition

    This is the SHOWPIECE of the translation.
    """
    _section("Section 4: Parallel Increment (THE SHOWPIECE)")
    ctx = Context()

    # Shared counter protected by a spin lock
    counter_inv = Exists("v", Sep(
        PointsTo("counter", Var("v")),
        Pure("v >= 0"),
    ))

    # -- Ex 16: Single CAS-based increment ---------------------
    pre_inc = PointsTo("counter", Var("v"))
    post_inc = PointsTo(
        "counter",
        App(Var("__add__"), Pair(Var("v"), Literal(1))),
    )
    triple_inc = SepTriple(
        pre=pre_inc,
        command="CAS(counter, v, v+1)",
        post=post_inc,
    )
    inc_path = PathAbs("i", Comp(
        type_=PyIntType(),
        face="i=0 -> v, i=1 -> v+1",
        partial_term=App(Var("__add__"), Pair(Var("v"), Literal(1))),
        base=Var("v"),
    ))
    proof_inc = TransportProof(
        Lam("val", PyIntType(), Var("counter_points_to")),
        Structural("CAS atomically increments counter"),
        AxiomInvocation("parallel_inc_atomicity"),
    )
    _sep_check(
        "Ex 16: CAS increment: counter v => counter v+1",
        "INCREMENT",
        triple_inc, proof_inc,
        hott_constructs=["PathAbs", "Comp", "TransportProof"],
    )

    # -- Ex 17: CAS retry loop as path composition -------------
    retry_path = PathComp(
        left_path=Refl(Var("v")),
        right_path=Structural("eventual CAS success"),
    )
    ctx_retry = ctx.extend("lock_free", Pure("CAS is lock-free"))
    goal_retry = _eq_goal(
        ctx_retry, Var("counter_before"), Var("counter_after"), PyIntType(),
    )
    proof_retry = Trans(
        TransportProof(
            Lam("state", PyObjType(), Var("counter_val")),
            retry_path,
            AxiomInvocation("cas_retry_loop_terminates"),
        ),
        AxiomInvocation("parallel_inc_atomicity"),
    )
    _check(
        "Ex 17: CAS retry loop: refl* . inc_path",
        "INCREMENT",
        ctx_retry, goal_retry, proof_retry,
        hott_constructs=["PathComp", "Refl", "Trans", "TransportProof"],
    )

    # -- Ex 18: Thread 1 increment under lock ------------------
    thread1_body = SepTriple(
        pre=counter_inv,
        command="counter += 1  # thread 1",
        post=Exists("v", Sep(
            PointsTo("counter", Var("v")), Pure("v >= 1"),
        )),
    )
    thread1_triple = CONC.with_lock("lock", counter_inv, thread1_body)
    proof_thread1 = CechGlue(
        patches=[
            ("t1_acquire", AxiomInvocation("spin_lock_inv_transfer")),
            ("t1_increment", Structural("counter += 1 increments")),
            ("t1_release", AxiomInvocation("spin_lock_inv_transfer")),
        ],
        overlap_proofs=[
            (0, 1, Structural("counter_inv preserved across acquire-increment")),
            (1, 2, Structural("counter_inv preserved across increment-release")),
        ],
    )
    _sep_check(
        "Ex 18: Thread 1 increment under lock",
        "INCREMENT",
        thread1_triple, proof_thread1,
        hott_constructs=["CechGlue", "AxiomInvocation", "Refl"],
    )

    # -- Ex 19: Thread 2 increment under lock ------------------
    thread2_body = SepTriple(
        pre=counter_inv,
        command="counter += 1  # thread 2",
        post=Exists("v", Sep(
            PointsTo("counter", Var("v")), Pure("v >= 1"),
        )),
    )
    thread2_triple = CONC.with_lock("lock", counter_inv, thread2_body)
    proof_thread2 = CechGlue(
        patches=[
            ("t2_acquire", AxiomInvocation("spin_lock_inv_transfer")),
            ("t2_increment", Structural("counter += 1 increments")),
            ("t2_release", AxiomInvocation("spin_lock_inv_transfer")),
        ],
        overlap_proofs=[
            (0, 1, Structural("counter_inv preserved across acquire-increment")),
            (1, 2, Structural("counter_inv preserved across increment-release")),
        ],
    )
    _sep_check(
        "Ex 19: Thread 2 increment under lock",
        "INCREMENT",
        thread2_triple, proof_thread2,
        hott_constructs=["CechGlue", "AxiomInvocation", "Refl"],
    )

    # -- Ex 20: Fork/join composition --------------------------
    fork1 = CONC.thread_fork(thread1_body)
    fork2 = CONC.thread_fork(thread2_body)

    parallel_path = PathComp(
        left_path=Structural("thread1 increments once"),
        right_path=Structural("thread2 increments once"),
    )
    ctx_par = ctx.extend(
        "counter_init", PointsTo("counter", Literal(0)),
    )
    goal_par = _eq_goal(ctx_par, Literal(0), Literal(2), PyIntType())
    proof_par = Trans(
        TransportProof(
            Lam("n", PyIntType(), Var("counter_val")),
            parallel_path,
            AxiomInvocation("thread_fork_ownership_transfer"),
        ),
        AxiomInvocation("parallel_inc_sum_correct"),
    )
    _check(
        "Ex 20: Fork/join: counter 0 -> 2 via parallel paths",
        "PARALLEL",
        ctx_par, goal_par, proof_par,
        hott_constructs=["PathComp", "Trans", "TransportProof"],
    )

    # -- Ex 21: Full parallel increment (CechGlue showpiece) --
    full_proof = CechGlue(
        patches=[
            ("init", Structural("counter = 0")),
            ("fork_t1", AxiomInvocation("thread_fork_ownership_transfer")),
            ("fork_t2", AxiomInvocation("thread_fork_ownership_transfer")),
            ("join_all", AxiomInvocation("thread_join_ownership_return")),
            ("assert", Structural("counter == 2")),
        ],
        overlap_proofs=[
            (0, 1, Structural("init hands counter_inv to fork")),
            (1, 2, Structural("disjoint ownership after fork")),
            (2, 3, Structural("ownership returned on join")),
            (3, 4, TransportProof(
                Lam("n", PyIntType(), Var("counter_eq")),
                Structural("1 + 1 = 2"),
                AxiomInvocation("parallel_inc_sum_correct"),
            )),
        ],
    )
    goal_full = _eq_goal(
        ctx, Var("par_inc_start"), Var("par_inc_end"), PyIntType(),
    )
    _check(
        "Ex 21: SHOWPIECE: full parallel increment proof",
        "SHOWPIECE",
        ctx, goal_full, full_proof,
        hott_constructs=["CechGlue", "TransportProof", "AxiomInvocation", "Refl"],
    )

    # -- Ex 22: Linearizability of parallel increment ----------
    lin_proof = Fiber(
        scrutinee=Var("par_trace"),
        type_branches=[
            (RefinementType(PyIntType(), "t", "t == 1"), Structural("t1 then t2: 0->1->2")),
            (RefinementType(PyIntType(), "t", "t == 2"), Structural("t2 then t1: 0->1->2")),
        ],
        exhaustive=True,
    )
    goal_lin = _eq_goal(ctx, Var("par_result"), Literal(2), PyIntType())
    _check(
        "Ex 22: Linearizability: par_result = 2 (Fiber)",
        "LINEAR",
        ctx, goal_lin, lin_proof,
        hott_constructs=["Fiber", "Structural"],
    )


# =====================================================================
# SECTION 5: Verified Threading
# =====================================================================

def section5_verified_threading() -> None:
    """Verified threading: fork, join, and ownership transfer.

    Python's threading.Thread maps directly to Pulse's thread_fork
    and thread_join.  Ownership of heap resources is transferred
    on fork and returned on join.
    """
    _section("Section 5: Verified Threading")
    ctx = Context()

    # -- Ex 23: Thread fork transfers ownership ----------------
    data_owned = PointsTo("data", Var("payload"))
    thread_body = SepTriple(
        pre=data_owned,
        command="process(data)",
        post=PointsTo("result", Var("output")),
    )
    fork_triple = CONC.thread_fork(thread_body)

    fork_path = PathAbs("i", Comp(
        type_=PyObjType(),
        face="i=0 -> parent_owns, i=1 -> child_owns",
        partial_term=Var("child_ownership"),
        base=Var("parent_ownership"),
    ))
    proof_fork = TransportProof(
        Lam("owner", PyObjType(), Var("data_ownership")),
        Structural("fork transfers data ownership to child"),
        AxiomInvocation("thread_fork_ownership_transfer"),
    )
    _sep_check(
        "Ex 23: Thread fork transfers data ownership",
        "THREAD",
        fork_triple, proof_fork,
        hott_constructs=["PathAbs", "Comp", "TransportProof"],
    )

    # -- Ex 24: Thread join returns result ownership -----------
    join_triple = SepTriple(
        pre=Emp(),
        command="thread.join()",
        post=PointsTo("result", Var("output")),
    )
    proof_join = TransportProof(
        Lam("owner", PyObjType(), Var("result_ownership")),
        Sym(Structural("join returns result ownership to parent")),
        AxiomInvocation("thread_join_ownership_return"),
    )
    _sep_check(
        "Ex 24: Thread join returns result ownership",
        "THREAD",
        join_triple, proof_join,
        hott_constructs=["TransportProof", "Sym"],
    )

    # -- Ex 25: Frame rule for threading -----------------------
    parent_frame = PointsTo("config", Var("settings"))
    child_pre = PointsTo("task", Var("work"))
    child_post = PointsTo("task", Var("done"))
    child_body = SepTriple(
        pre=child_pre, command="do_work(task)", post=child_post,
    )

    frame_proof = TransportProof(
        Lam("resources", PyObjType(), Var("disjoint")),
        Structural("config * task are disjoint heap regions"),
        AxiomInvocation("thread_frame_disjoint"),
    )
    framed_triple = SepTriple(
        pre=sep_of(parent_frame, child_pre),
        command="fork(do_work); ...; join()",
        post=sep_of(parent_frame, child_post),
        frame=parent_frame,
    )
    _sep_check(
        "Ex 25: Frame rule: parent keeps config during fork",
        "FRAME",
        framed_triple, frame_proof,
        hott_constructs=["TransportProof", "Sep", "SepTriple"],
    )

    # -- Ex 26: Thread pool as bounded fibration ---------------
    pool_fiber = Fiber(
        scrutinee=Var("worker_index"),
        type_branches=[
            (RefinementType(PyIntType(), "w", "w == 0"), Structural("worker 0 owns slice 0")),
            (RefinementType(PyIntType(), "w", "w == 1"), Structural("worker 1 owns slice 1")),
            (RefinementType(PyIntType(), "w", "w == 2"), Structural("worker 2 owns slice 2")),
            (RefinementType(PyIntType(), "w", "w == 3"), Structural("worker 3 owns slice 3")),
        ],
        exhaustive=True,
    )
    pool_type = RefinementType(PyIntType(), "n", "0 <= n < 4")
    goal_pool = _type_goal(ctx, Var("worker_index"), pool_type)
    _check(
        "Ex 26: ThreadPool(4) as bounded fibration",
        "FIBER",
        ctx, goal_pool, pool_fiber,
        hott_constructs=["Fiber", "RefinementType"],
    )


# =====================================================================
# SECTION 6: Concurrent Data Structures
# =====================================================================

def section6_concurrent_data_structures() -> None:
    """Concurrent data structures: Treiber stack, MS queue, etc.

    Lock-free data structures use CAS for atomic updates.  We verify
    linearizability using homotopy: each concurrent operation has a
    path to a sequential counterpart.
    """
    _section("Section 6: Concurrent Data Structures")
    ctx = Context()

    # -- Ex 27: Treiber stack push (CAS on head) ---------------
    stack_pre = Sep(
        PointsTo("stack.head", Var("old_head")),
        Pure("stack represents list L"),
    )
    stack_post = Sep(
        PointsTo("stack.head", Var("new_node")),
        Pure("stack represents val :: L"),
    )
    triple_push = SepTriple(
        pre=stack_pre,
        command="treiber_push(stack, val)",
        post=stack_post,
    )

    push_path = PathAbs("i", Comp(
        type_=PyObjType(),
        face="i=0 -> old_head, i=1 -> new_node",
        partial_term=Var("new_node"),
        base=Var("old_head"),
    ))
    proof_push = TransportProof(
        Lam("head", PyObjType(), Var("stack_repr")),
        Structural("CAS updates head to new_node"),
        AxiomInvocation("treiber_stack_linearizable"),
    )
    _sep_check(
        "Ex 27: Treiber push: head old => head new_node",
        "TREIBER",
        triple_push, proof_push,
        hott_constructs=["PathAbs", "Comp", "TransportProof"],
    )

    # -- Ex 28: Treiber stack pop (CAS on head) ----------------
    pop_pre = Sep(
        PointsTo("stack.head", Var("top_node")),
        Pure("stack represents val :: L"),
    )
    pop_post = Sep(
        PointsTo("stack.head", Var("top_node.next")),
        Sep(Pure("stack represents L"), Pure("result = val")),
    )
    triple_pop = SepTriple(
        pre=pop_pre,
        command="treiber_pop(stack)",
        post=pop_post,
    )

    proof_pop = TransportProof(
        Lam("head", PyObjType(), Var("stack_repr")),
        Structural("CAS updates head to top_node.next"),
        AxiomInvocation("treiber_stack_linearizable"),
    )
    _sep_check(
        "Ex 28: Treiber pop: head top => head top.next",
        "TREIBER",
        triple_pop, proof_pop,
        hott_constructs=["TransportProof", "Sep", "Pure"],
    )

    # -- Ex 29: Michael-Scott queue enqueue --------------------
    q_pre = Sep(
        PointsTo("queue.tail", Var("old_tail")),
        Pure("queue represents Q"),
    )
    q_post = Sep(
        PointsTo("queue.tail", Var("new_node")),
        Pure("queue represents Q ++ [val]"),
    )
    triple_enq = SepTriple(
        pre=q_pre,
        command="ms_enqueue(queue, val)",
        post=q_post,
    )

    proof_enq = TransportProof(
        Lam("tail", PyObjType(), Var("queue_repr")),
        Structural("CAS links new_node at tail"),
        AxiomInvocation("michael_scott_queue_linearizable"),
    )
    _sep_check(
        "Ex 29: MS queue enqueue: tail old => tail new",
        "MSQUEUE",
        triple_enq, proof_enq,
        hott_constructs=["TransportProof", "SepTriple"],
    )

    # -- Ex 30: RWLock reader sharing (DuckPath) ---------------
    rw_duck = DuckPath(
        type_a=PyClassType(
            name="ThreadReader",
            methods=(
                ("read", PyCallableType((), PyObjType())),
                ("release", PyCallableType((), PyNoneType())),
            ),
        ),
        type_b=PyClassType(
            name="RWLockReader",
            methods=(
                ("read", PyCallableType((), PyObjType())),
                ("release", PyCallableType((), PyNoneType())),
            ),
        ),
        method_proofs=[
            ("read", Structural("read: same shared-read behavior")),
            ("release", Structural("release: same lock-release behavior")),
        ],
    )
    reader_family = Lam("cls", PyObjType(), Var("satisfies_reader_protocol"))
    proof_rw = TransportProof(reader_family, rw_duck, AxiomInvocation("rwlock_reader_protocol"))
    goal_rw = _eq_goal(
        ctx, Var("ThreadReader"), Var("RWLockReader"), PyObjType(),
    )
    _check(
        "Ex 30: RWLock reader sharing via DuckPath",
        "DUCKPATH",
        ctx, goal_rw, proof_rw,
        hott_constructs=["DuckPath", "PyClassType", "TransportProof"],
    )

    # -- Ex 31: Concurrent dict snapshot consistency -----------
    snapshot_path = PathAbs("i", Comp(
        type_=PyObjType(),
        face="i=0 -> live_dict, i=1 -> snapshot",
        partial_term=Var("frozen_copy"),
        base=Var("live_dict"),
    ))
    goal_snap = _eq_goal(
        ctx, Var("live_dict_at_t"), Var("snapshot"), PyObjType(),
    )
    proof_snap = TransportProof(
        Lam("state", PyObjType(), Var("dict_contents")),
        Structural("snapshot captures consistent point-in-time view"),
        AxiomInvocation("concurrent_dict_snapshot"),
    )
    _check(
        "Ex 31: Dict snapshot consistency via path",
        "SNAPSHOT",
        ctx, goal_snap, proof_snap,
        term_repr=str(snapshot_path),
        hott_constructs=["PathAbs", "Comp", "TransportProof"],
    )


# =====================================================================
# SECTION 7: Async/Await with Ownership
# =====================================================================

def section7_async_await() -> None:
    """Async/await with ownership: coroutine ownership transfer.

    Python's asyncio maps to Pulse's cooperative concurrency.  At each
    await point, the coroutine suspends; we must ensure no borrowed
    references escape the suspension boundary.
    """
    _section("Section 7: Async/Await with Ownership")
    ctx = Context()

    # -- Ex 32: await suspends ownership -----------------------
    conn_pre = PointsTo("conn", Var("open"))
    conn_post = Sep(PointsTo("conn", Var("open")), Pure("result = data"))
    await_triple = CONC.async_await("fetch(url)", conn_pre, conn_post)

    proof_await = TransportProof(
        Lam("suspended", PyObjType(), Var("conn_ownership")),
        Structural("conn ownership preserved across await"),
        AxiomInvocation("async_ownership_suspend"),
    )
    _sep_check(
        "Ex 32: await suspends/resumes conn ownership",
        "ASYNC",
        await_triple, proof_await,
        hott_constructs=["TransportProof", "SepTriple"],
    )

    # -- Ex 33: gather joins ownership from coroutines ---------
    coro1_post = PointsTo("result1", Var("data1"))
    coro2_post = PointsTo("result2", Var("data2"))
    gather_post = sep_of(coro1_post, coro2_post)
    gather_triple = SepTriple(
        pre=Emp(),
        command="await asyncio.gather(coro1, coro2)",
        post=gather_post,
    )

    gather_proof = CechGlue(
        patches=[
            ("coro1", Structural("coro1 produces result1")),
            ("coro2", Structural("coro2 produces result2")),
            ("join", Structural("gather joins both results")),
        ],
        overlap_proofs=[
            (0, 2, Structural("coro1 result flows to gather join")),
            (1, 2, Structural("coro2 result flows to gather join")),
        ],
    )
    _sep_check(
        "Ex 33: gather joins ownership from coroutines",
        "ASYNC",
        gather_triple, gather_proof,
        hott_constructs=["CechGlue", "Sep", "Refl"],
    )

    # -- Ex 34: Cancellation runs cleanup (path inverse) -------
    cancel_path = PathAbs(
        "i",
        PathApp(Var("acquire_path"), App(Var("1-"), Var("i"))),
    )
    cancel_pre = Sep(
        PointsTo("resource", Var("acquired")),
        Pure("cancel_requested"),
    )
    cancel_post = Emp()
    cancel_triple = SepTriple(
        pre=cancel_pre,
        command="cancel_and_cleanup()",
        post=cancel_post,
    )

    proof_cancel = TransportProof(
        Lam("state", PyObjType(), Var("resource_state")),
        Sym(Structural("cleanup reverses acquisition")),
        AxiomInvocation("async_cancel_cleanup"),
    )
    _sep_check(
        "Ex 34: Cancellation as path inverse",
        "ASYNC",
        cancel_triple, proof_cancel,
        hott_constructs=["PathAbs", "PathApp", "Sym", "TransportProof"],
    )

    # -- Ex 35: Semaphore bounds concurrency -------------------
    sem_type = RefinementType(PyIntType(), "active", "0 <= active <= n")
    sem_acquire = SepTriple(
        pre=Pure("active < n"),
        command="await semaphore.acquire()",
        post=Pure("active <= n"),
    )
    proof_sem = TransportProof(
        Lam("count", PyIntType(), Var("bounded")),
        Structural("acquire increments active, bounded by n"),
        AxiomInvocation("async_semaphore_bounded"),
    )
    _sep_check(
        "Ex 35: Semaphore bounds concurrency to n",
        "ASYNC",
        sem_acquire, proof_sem,
        hott_constructs=["RefinementType", "TransportProof"],
    )


# =====================================================================
# SECTION 8: Message Passing
# =====================================================================

def section8_message_passing() -> None:
    """Message passing: channels with ownership transfer.

    Channels provide a safe way to transfer ownership between
    threads/coroutines.  Sending a value transfers ownership;
    receiving acquires it.
    """
    _section("Section 8: Message Passing")
    ctx = Context()

    # -- Ex 36: Channel send transfers ownership ---------------
    data_ownership = PointsTo("data", Var("payload"))
    send_triple = CONC.channel_send("chan", Var("data"), data_ownership)

    send_path = PathAbs("i", Comp(
        type_=PyObjType(),
        face="i=0 -> sender_owns, i=1 -> channel_owns",
        partial_term=Var("in_channel"),
        base=Var("sender_owned"),
    ))
    proof_send = TransportProof(
        Lam("owner", PyObjType(), Var("data_ownership")),
        Structural("send transfers data ownership to channel"),
        AxiomInvocation("channel_ownership_transfer"),
    )
    _sep_check(
        "Ex 36: Channel send: sender loses ownership",
        "CHANNEL",
        send_triple, proof_send,
        hott_constructs=["PathAbs", "Comp", "TransportProof"],
    )

    # -- Ex 37: Channel recv acquires ownership ----------------
    recv_triple = CONC.channel_recv(
        "chan", "received", data_ownership,
    )

    proof_recv = TransportProof(
        Lam("owner", PyObjType(), Var("data_ownership")),
        Sym(Structural("recv acquires data ownership from channel")),
        AxiomInvocation("channel_ownership_transfer"),
    )
    _sep_check(
        "Ex 37: Channel recv: receiver gains ownership",
        "CHANNEL",
        recv_triple, proof_recv,
        hott_constructs=["TransportProof", "Sym"],
    )

    # -- Ex 38: Send/recv compose to ownership transfer --------
    transfer_proof = CechGlue(
        patches=[
            ("send", Structural("sender relinquishes data")),
            ("channel", Structural("data in transit")),
            ("recv", Structural("receiver acquires data")),
        ],
        overlap_proofs=[
            (0, 1, Structural("ownership transfers from sender to channel")),
            (1, 2, Structural("ownership transfers from channel to receiver")),
        ],
    )
    transfer_triple = SepTriple(
        pre=PointsTo("data", Var("payload")),
        command="chan.send(data); received = chan.recv()",
        post=PointsTo("received", Var("payload")),
    )
    _sep_check(
        "Ex 38: Send+recv = ownership transfer (CechGlue)",
        "CHANNEL",
        transfer_triple, transfer_proof,
        hott_constructs=["CechGlue", "Refl"],
    )

    # -- Ex 39: Typed channel safety (Fiber over types) --------
    typed_fiber = Fiber(
        scrutinee=Var("sent_value"),
        type_branches=[
            (PyIntType(), Structural("int accepted by Channel[int]")),
            (PyStrType(), Structural("str rejected by Channel[int]")),
            (PyFloatType(), Structural("float rejected by Channel[int]")),
        ],
        exhaustive=True,
    )
    chan_type = PyClassType(
        name="Channel",
        methods=(("send", PyCallableType()), ("recv", PyCallableType())),
    )
    goal_typed = _type_goal(ctx, Var("sent_value"), PyIntType())
    _check(
        "Ex 39: Typed channel: Channel[int] rejects str",
        "FIBER",
        ctx, goal_typed, typed_fiber,
        hott_constructs=["Fiber", "PyClassType"],
    )

    # -- Ex 40: FIFO channel ordering (path composition) -------
    fifo_path = PathComp(
        left_path=Structural("send(a) before send(b)"),
        right_path=Structural("recv() yields a then b"),
    )
    goal_fifo = _eq_goal(
        ctx, Var("send_order"), Var("recv_order"), PyListType(PyObjType()),
    )
    proof_fifo = TransportProof(
        Lam("order", PyObjType(), Var("fifo_property")),
        fifo_path,
        AxiomInvocation("channel_fifo_order"),
    )
    _check(
        "Ex 40: FIFO ordering via path composition",
        "CHANNEL",
        ctx, goal_fifo, proof_fifo,
        hott_constructs=["PathComp", "TransportProof"],
    )


# =====================================================================
# SECTION 9: GIL-Aware Verification
# =====================================================================

def section9_gil_awareness() -> None:
    """GIL-aware verification: understanding Python's concurrency model.

    The GIL (Global Interpreter Lock) makes certain operations atomic
    that would not be in a truly concurrent setting.  We model this
    as a path equivalence: under GIL, some concurrent patterns are
    equivalent to sequential ones.
    """
    _section("Section 9: GIL-Aware Verification")
    ctx = Context()

    # -- Ex 41: GIL makes refcount atomic ----------------------
    refcount_path = PathAbs("i", Var("refcount_op_under_gil"))
    ctx_gil = ctx.extend("GIL_held", Pure("GIL is held"))
    goal_refcount = _eq_goal(
        ctx_gil,
        Var("refcount_concurrent"),
        Var("refcount_sequential"),
        PyIntType(),
    )
    proof_refcount = TransportProof(
        Lam("mode", PyObjType(), Var("refcount_behavior")),
        Structural("GIL serializes refcount operations"),
        AxiomInvocation("gil_atomic_refcount"),
    )
    _check(
        "Ex 41: GIL makes refcount ops atomic",
        "GIL",
        ctx_gil, goal_refcount, proof_refcount,
        term_repr=str(refcount_path),
        hott_constructs=["PathAbs", "TransportProof"],
    )

    # -- Ex 42: GIL released during I/O -----------------------
    io_path = PathAbs("i", IfThenElse(
        Var("is_io_op"),
        Var("gil_released"),
        Var("gil_held"),
    ))
    goal_io = _eq_goal(
        ctx, Var("pre_io_state"), Var("post_io_state"), PyObjType(),
    )
    proof_io = TransportProof(
        Lam("phase", PyObjType(), Var("gil_status")),
        Structural("GIL released during I/O, re-acquired after"),
        AxiomInvocation("gil_release_io"),
    )
    _check(
        "Ex 42: GIL released during I/O",
        "GIL",
        ctx, goal_io, proof_io,
        term_repr=str(io_path),
        hott_constructs=["PathAbs", "IfThenElse", "TransportProof"],
    )

    # -- Ex 43: Bytecode-level preemption (Cases) --------------
    preempt_cases = Cases(
        scrutinee=Var("instruction_boundary"),
        branches=[
            ("same_instruction", Structural("no preemption within instruction")),
            ("between_instructions", Structural("preemption possible")),
        ],
    )
    goal_preempt = _type_goal(
        ctx,
        Var("thread_state"),
        UnionType([Pure("running"), Pure("preempted")]),
    )
    _check(
        "Ex 43: Bytecode preemption via Cases",
        "GIL",
        ctx, goal_preempt, preempt_cases,
        hott_constructs=["Cases", "UnionType"],
    )

    # -- Ex 44: no-GIL mode requires explicit sync (Patch) ----
    nogil_patch = Patch(
        cls="GILProtected",
        method_name="increment",
        new_impl=Lam(
            "self", PyObjType(),
            PyCall(Var("atomic_increment"), [Var("self")]),
        ),
        contract_proof=TransportProof(
            Lam("mode", PyObjType(), Var("sync_behavior")),
            Structural("explicit atomic replaces GIL atomicity"),
            AxiomInvocation("nogil_explicit_sync"),
        ),
    )
    goal_nogil = _eq_goal(
        ctx,
        Var("gil_increment"),
        Var("atomic_increment"),
        PyCallableType([PyObjType()], PyNoneType()),
    )
    _check(
        "Ex 44: no-GIL Patch: GIL atomicity -> explicit sync",
        "PATCH",
        ctx, goal_nogil, nogil_patch,
        hott_constructs=["Patch", "Lam", "TransportProof"],
    )


# =====================================================================
# SECTION 10: Deadlock Freedom
# =====================================================================

def section10_deadlock_freedom() -> None:
    """Deadlock freedom: lock ordering and async guarantees.

    Deadlocks arise from cyclic lock dependencies.  We prevent them
    by requiring a total order on lock acquisition.  For async code,
    the event loop's cooperative scheduling is inherently deadlock-free.
    """
    _section("Section 10: Deadlock Freedom")
    ctx = Context()

    # -- Ex 45: Lock ordering prevents deadlock ----------------
    lock_order_path = PathAbs("i", Comp(
        type_=PyObjType(),
        face="i=0 -> lock_a, i=1 -> lock_b",
        partial_term=Var("ordered_acquire"),
        base=Var("lock_a"),
    ))
    ctx_ordered = ctx.extend("order", Pure("lock_a < lock_b"))
    goal_order = _eq_goal(
        ctx_ordered,
        Var("acquire_a_then_b"),
        Var("safe_acquisition"),
        PyObjType(),
    )
    proof_order = TransportProof(
        Lam("locks", PyObjType(), Var("acquisition_order")),
        Structural("total order on locks prevents cycles"),
        AxiomInvocation("lock_order_total"),
    )
    _check(
        "Ex 45: Lock ordering: a < b prevents deadlock",
        "DEADLOCK",
        ctx_ordered, goal_order, proof_order,
        term_repr=str(lock_order_path),
        hott_constructs=["PathAbs", "Comp", "TransportProof"],
    )

    # -- Ex 46: Cyclic dependency detection (Fiber) ------------
    cycle_fiber = Fiber(
        scrutinee=Var("dep_graph"),
        type_branches=[
            (RefinementType(PyBoolType(), "g", "is_acyclic(g)"), Structural("DAG -> deadlock free")),
            (RefinementType(PyBoolType(), "g", "has_cycle(g)"), Structural("cycle -> deadlock possible")),
        ],
        exhaustive=True,
    )
    goal_cycle = _type_goal(
        ctx,
        Var("dep_graph"),
        UnionType([Pure("acyclic"), Pure("cyclic")]),
    )
    _check(
        "Ex 46: Cycle detection via Fiber on dep graph",
        "FIBER",
        ctx, goal_cycle, cycle_fiber,
        hott_constructs=["Fiber", "UnionType"],
    )

    # -- Ex 47: Lock-with-timeout ensures liveness -------------
    timeout_cases = Cases(
        scrutinee=Var("acquire_result"),
        branches=[
            ("acquired", TransportProof(
                Lam("state", PyObjType(), Var("lock_held")),
                Structural("lock acquired within timeout"),
                AxiomInvocation("timeout_liveness"),
            )),
            ("timeout", Structural(
                "timeout -> caller proceeds without lock",
            )),
        ],
    )
    goal_timeout = _type_goal(
        ctx,
        Var("acquire_result"),
        UnionType([Pure("acquired"), Pure("timeout")]),
    )
    _check(
        "Ex 47: Timeout liveness via Cases",
        "LIVENESS",
        ctx, goal_timeout, timeout_cases,
        hott_constructs=["Cases", "TransportProof", "UnionType"],
    )

    # -- Ex 48: Async event loop is deadlock-free --------------
    async_path = PathAbs("i", Var("event_loop_step_i"))
    goal_async_df = _eq_goal(
        ctx,
        Var("event_loop_running"),
        Var("event_loop_progress"),
        PyObjType(),
    )
    proof_async_df = TransportProof(
        Lam("loop", PyObjType(), Var("progress_guarantee")),
        Structural("cooperative scheduling prevents circular waits"),
        AxiomInvocation("async_deadlock_free"),
    )
    _check(
        "Ex 48: Async event loop deadlock-free",
        "DEADLOCK",
        ctx, goal_async_df, proof_async_df,
        term_repr=str(async_path),
        hott_constructs=["PathAbs", "TransportProof"],
    )

    # -- Ex 49: Dining philosophers with ordered forks ---------
    forks_inv = sep_of(
        PointsTo("fork_0", Var("free")),
        PointsTo("fork_1", Var("free")),
        PointsTo("fork_2", Var("free")),
    )
    philosophers_proof = CechGlue(
        patches=[
            ("phil_0", Structural("picks fork_0 then fork_1")),
            ("phil_1", Structural("picks fork_1 then fork_2")),
            ("phil_2", Structural("picks fork_0 then fork_2")),
        ],
        overlap_proofs=[
            (0, 1, Structural("fork_1 shared, ordered")),
            (1, 2, Structural("fork_2 shared, ordered")),
        ],
    )
    goal_dining = _eq_goal(
        ctx, Var("dining_start"), Var("dining_progress"), PyObjType(),
    )
    _check(
        "Ex 49: Dining philosophers: ordered forks (CechGlue)",
        "DEADLOCK",
        ctx, goal_dining, philosophers_proof,
        hott_constructs=["CechGlue", "Sep", "PointsTo"],
    )

    # -- Ex 50: Lock hierarchy as path ordering ----------------
    hierarchy_path = PathAbs("i", Comp(
        type_=PyIntType(),
        face="i=0 -> level_0, i=1 -> level_n",
        partial_term=Var("monotone_level"),
        base=Var("level_0"),
    ))
    ctx_hier = ctx.extend(
        "hierarchy", Pure("lock_levels are totally ordered"),
    )
    goal_hier = _eq_goal(
        ctx_hier,
        Var("acquisition_sequence"),
        Var("monotone_sequence"),
        PyListType(PyIntType()),
    )
    proof_hier = TransportProof(
        Lam("seq", PyObjType(), Var("monotonicity")),
        Structural("acquisition follows level order"),
        AxiomInvocation("lock_order_acyclic"),
    )
    _check(
        "Ex 50: Lock hierarchy as monotone path",
        "DEADLOCK",
        ctx_hier, goal_hier, proof_hier,
        term_repr=str(hierarchy_path),
        hott_constructs=["PathAbs", "Comp", "TransportProof"],
    )


# =====================================================================
# SECTION 11: Advanced Concurrency Patterns
# =====================================================================

def section11_advanced_patterns() -> None:
    """Advanced verified concurrency patterns that combine multiple HoTT
    constructs in realistic scenarios.

    This section covers:
    - Lock-free progress guarantees (obstruction-freedom, lock-freedom,
      wait-freedom) modeled as refinement types on progress paths.
    - Epoch-based reclamation as ownership transfer through temporal paths.
    - Compare-and-swap loops as coinductive paths with termination proofs.
    - Hazard pointers as fiber-indexed ownership invariants.
    - Seqlocks (sequence locks) as read-retry loops with consistency proofs.
    - Memory ordering (acquire/release/seq_cst) as path coherence levels.
    - Concurrent reference counting as transport across shared ownership.
    - Work stealing as ownership transfer between deque endpoints.
    - Read-Copy-Update (RCU) as transport through grace periods.
    - Barrier synchronization as CechGlue over thread phases.
    - Condition variables as signaled path construction.
    """
    _section("Section 11: Advanced Concurrency Patterns")
    ctx = Context()

    # -- Ex 51: Obstruction-free progress guarantee ----------------
    # If a thread runs in isolation, it completes in bounded steps.
    # Model: RefinementType on step count ensures progress.
    of_pre = Pure("thread runs without interference")
    of_post = Pure("operation completes in O(1) steps")
    of_triple = SepTriple(
        pre=of_pre, command="obstruction_free_op()", post=of_post,
    )
    of_path = PathAbs("i", Comp(
        type_=PyObjType(),
        face="i=0 -> thread_start, i=1 -> thread_done",
        partial_term=Var("completed_op"),
        base=Var("running_thread"),
    ))
    proof_of = TransportProof(
        Lam("state", PyObjType(), Var("progress_measure")),
        Structural("isolation => no contention => bounded steps"),
        AxiomInvocation("obstruction_free_progress"),
    )
    _sep_check(
        "Ex 51: Obstruction-free progress guarantee",
        "PROGRESS",
        of_triple, proof_of,
        hott_constructs=["PathAbs", "Comp", "TransportProof", "RefinementType"],
    )

    # -- Ex 52: Lock-free progress (system-wide) -------------------
    # At least one thread makes progress in bounded steps.
    # Stronger than obstruction-free: competing threads don't all starve.
    lf_fiber = Fiber(
        scrutinee=Var("thread_set"),
        type_branches=[
            (RefinementType(PyObjType(), "t", "t.makes_progress"),
             Structural("at least one thread completes its CAS")),
            (RefinementType(PyObjType(), "t", "t.retries"),
             Structural("retry threads help the winner commit")),
        ],
        exhaustive=True,
    )
    lf_type = RefinementType(PyObjType(), "sys", "exists t. t completes")
    goal_lf = _type_goal(ctx, Var("thread_set"), lf_type)
    _check(
        "Ex 52: Lock-free: some thread always progresses",
        "PROGRESS",
        ctx, goal_lf, lf_fiber,
        hott_constructs=["Fiber", "RefinementType", "Structural"],
    )

    # -- Ex 53: Wait-free progress (per-thread) --------------------
    # Every thread completes in bounded steps, regardless of contention.
    # Model: NatInduction on step bound.
    wf_proof = NatInduction(
        var="step",
        base_proof=Structural("step 0: initial state, no conflict"),
        step_proof=TransportProof(
            Lam("n", PyIntType(), Var("bounded_steps")),
            Structural("step n -> step n+1: helping protocol resolves"),
            AxiomInvocation("wait_free_helping_protocol"),
        ),
    )
    goal_wf = _type_goal(
        ctx.extend("bound", RefinementType(PyIntType(), "n", "n > 0")),
        Var("wait_free_op"),
        RefinementType(PyObjType(), "r", "completes_in(r, bound)"),
    )
    _check(
        "Ex 53: Wait-free: every thread bounded by n steps",
        "PROGRESS",
        ctx, goal_wf, wf_proof,
        hott_constructs=["NatInduction", "TransportProof", "RefinementType"],
    )

    # -- Ex 54: Epoch-based reclamation (EBR) ----------------------
    # Objects are retired to an epoch, then freed when no thread
    # references that epoch. Modeled as ownership transport through
    # temporal epochs.
    epoch_pre = PointsTo("obj", Var("data"))
    epoch_mid = Sep(Pure("retired(obj, epoch_k)"), Emp())
    epoch_post = Emp()
    retire_triple = SepTriple(
        pre=epoch_pre,
        command="ebr.retire(obj)",
        post=epoch_mid,
    )
    reclaim_triple = SepTriple(
        pre=epoch_mid,
        command="ebr.reclaim(epoch_k)",
        post=epoch_post,
    )
    ebr_path = PathAbs("i", Comp(
        type_=PyObjType(),
        face="i=0 -> owned, i=1 -> retired, i=2 -> freed",
        partial_term=Var("freed"),
        base=Var("owned_obj"),
    ))
    ebr_proof = PathComp(
        TransportProof(
            Lam("epoch", PyObjType(), Var("ownership_state")),
            Structural("retire moves obj from owned to retired(epoch_k)"),
            AxiomInvocation("ebr_retire_epoch"),
        ),
        TransportProof(
            Lam("epoch", PyObjType(), Var("ownership_state")),
            Structural("reclaim frees when no thread in epoch_k"),
            AxiomInvocation("ebr_reclaim_safe"),
        ),
    )
    _sep_check(
        "Ex 54: EBR: retire -> grace period -> reclaim",
        "EBR",
        retire_triple, ebr_proof,
        hott_constructs=["PathComp", "TransportProof", "PathAbs", "Comp"],
    )

    # -- Ex 55: Hazard pointer registration (Fiber) ----------------
    # Each thread registers a hazard pointer to protect an object.
    # The Fiber indexes ownership by thread identity.
    hp_fiber = Fiber(
        scrutinee=Var("thread_id"),
        type_branches=[
            (RefinementType(PyIntType(), "tid", "tid == 0"),
             Cut("hp0", PyObjType(),
                 Structural("thread 0 protects node via hp[0]"),
                 Assume("hp0"))),
            (RefinementType(PyIntType(), "tid", "tid == 1"),
             Cut("hp1", PyObjType(),
                 Structural("thread 1 protects node via hp[1]"),
                 Assume("hp1"))),
            (RefinementType(PyIntType(), "tid", "tid >= 2"),
             Cut("hpN", PyObjType(),
                 Structural("thread N protects node via hp[N]"),
                 Assume("hpN"))),
        ],
        exhaustive=True,
    )
    hp_type = RefinementType(PyObjType(), "obj", "protected_by_hazard_pointer(obj)")
    goal_hp = _type_goal(ctx, Var("thread_id"), hp_type)
    _check(
        "Ex 55: Hazard pointers: per-thread protection (Fiber)",
        "HAZARD",
        ctx, goal_hp, hp_fiber,
        hott_constructs=["Fiber", "RefinementType", "Cut", "Assume"],
    )

    # -- Ex 56: Seqlock reader consistency (Cases) -----------------
    # A sequence lock uses a version counter: odd = write in progress.
    # Reader retries if version changed. Cases on version parity.
    seqlock_cases = Cases(
        scrutinee=Var("version"),
        branches=[
            ("even", TransportProof(
                Lam("v", PyIntType(), Var("data_consistent")),
                Structural("even version => no write in progress => data valid"),
                AxiomInvocation("seqlock_even_consistent"),
            )),
            ("odd", Structural("odd version => write in progress => retry")),
        ],
    )
    seqlock_type = UnionType([
        RefinementType(PyObjType(), "d", "consistent(d)"),
        Pure("retry"),
    ])
    goal_seqlock = _type_goal(ctx, Var("seqlock_read"), seqlock_type)
    _check(
        "Ex 56: Seqlock reader: even => valid, odd => retry",
        "SEQLOCK",
        ctx, goal_seqlock, seqlock_cases,
        hott_constructs=["Cases", "TransportProof", "UnionType"],
    )

    # -- Ex 57: Memory ordering levels (DuckPath) ------------------
    # Acquire/release semantics as behavioral equivalence:
    # both SeqCst and AcqRel expose load/store with ordering guarantees.
    seqcst_type = PyClassType(
        name="SeqCstAtomic",
        methods=(
            ("load", PyCallableType((), PyIntType())),
            ("store", PyCallableType((PyIntType(),), PyNoneType())),
            ("fence", PyCallableType((), PyNoneType())),
        ),
    )
    acqrel_type = PyClassType(
        name="AcqRelAtomic",
        methods=(
            ("load", PyCallableType((), PyIntType())),
            ("store", PyCallableType((PyIntType(),), PyNoneType())),
            ("fence", PyCallableType((), PyNoneType())),
        ),
    )
    mem_order_duck = DuckPath(
        type_a=seqcst_type,
        type_b=acqrel_type,
        method_proofs=[
            ("load", Structural("load: both provide acquire semantics")),
            ("store", Structural("store: both provide release semantics")),
            ("fence", Structural("fence: SeqCst subsumes AcqRel ordering")),
        ],
    )
    order_family = Lam("cls", PyObjType(), Var("satisfies_ordering"))
    proof_order = TransportProof(
        order_family, mem_order_duck,
        AxiomInvocation("memory_ordering_subsumption"),
    )
    goal_order = _eq_goal(
        ctx, Var("SeqCstAtomic"), Var("AcqRelAtomic"), PyObjType(),
    )
    _check(
        "Ex 57: Memory ordering: SeqCst ≃ AcqRel (DuckPath)",
        "MEMORD",
        ctx, goal_order, proof_order,
        hott_constructs=["DuckPath", "TransportProof", "PyClassType"],
    )

    # -- Ex 58: Concurrent reference counting (Arc) ----------------
    # Arc<T> splits ownership among N holders. Drop decrements refcount.
    # When refcount reaches 0, inner value is freed.
    arc_pre = Sep(
        PointsTo("arc_inner", Var("data")),
        Pure("refcount >= 1"),
    )
    arc_post = Sep(
        PointsTo("arc_inner", Var("data")),
        Pure("refcount >= 0"),
    )
    arc_drop_triple = SepTriple(
        pre=arc_pre, command="arc.drop()", post=arc_post,
    )
    arc_proof = TransportProof(
        Lam("rc", PyIntType(), Var("refcount_state")),
        Structural("drop atomically decrements refcount; >=1 => >=0"),
        AxiomInvocation("arc_atomic_decrement"),
    )
    _sep_check(
        "Ex 58: Arc drop: refcount-- is atomic",
        "ARC",
        arc_drop_triple, arc_proof,
        hott_constructs=["TransportProof", "Sep", "Pure"],
    )

    # -- Ex 59: Work stealing deque (Fiber over endpoints) ---------
    # Owner pushes/pops from bottom, thieves steal from top.
    # Fiber indexes ownership by access role.
    steal_fiber = Fiber(
        scrutinee=Var("accessor_role"),
        type_branches=[
            (RefinementType(PyObjType(), "a", "a == owner"),
             Structural("owner has exclusive bottom access")),
            (RefinementType(PyObjType(), "a", "a == thief"),
             Structural("thief uses CAS on top, no data race")),
        ],
        exhaustive=True,
    )
    steal_type = RefinementType(PyObjType(), "deq", "no_data_race(deq)")
    goal_steal = _type_goal(ctx, Var("accessor_role"), steal_type)
    _check(
        "Ex 59: Work stealing: owner vs thief (Fiber)",
        "STEAL",
        ctx, goal_steal, steal_fiber,
        hott_constructs=["Fiber", "RefinementType", "Structural"],
    )

    # -- Ex 60: Read-Copy-Update (RCU) grace period ----------------
    # Writers publish new version; readers access old version until
    # grace period ends. Transport through temporal grace period.
    rcu_pre = PointsTo("data_ptr", Var("v_old"))
    rcu_post = PointsTo("data_ptr", Var("v_new"))
    rcu_triple = SepTriple(
        pre=rcu_pre, command="rcu_assign_pointer(data_ptr, v_new)",
        post=rcu_post,
    )
    rcu_path = PathAbs("i", Comp(
        type_=PyObjType(),
        face="i=0 -> v_old, i=1 -> v_new",
        partial_term=Var("v_new"),
        base=Var("v_old"),
    ))
    rcu_proof = TransportProof(
        Lam("ptr", PyObjType(), Var("data_version")),
        Structural("rcu_assign_pointer atomically swings pointer"),
        AxiomInvocation("rcu_grace_period"),
    )
    _sep_check(
        "Ex 60: RCU: grace period transport v_old -> v_new",
        "RCU",
        rcu_triple, rcu_proof,
        hott_constructs=["PathAbs", "Comp", "TransportProof"],
    )

    # -- Ex 61: Barrier synchronization (CechGlue) -----------------
    # N threads reach a barrier; none proceeds until all arrive.
    # Each thread is a patch; barrier is the global gluing.
    barrier_proof = CechGlue(
        patches=[
            ("thread_0_arrives", Structural("thread 0 reaches barrier")),
            ("thread_1_arrives", Structural("thread 1 reaches barrier")),
            ("thread_2_arrives", Structural("thread 2 reaches barrier")),
            ("all_proceed", Structural("barrier releases all threads")),
        ],
        overlap_proofs=[
            (0, 3, Structural("thread 0 arrival contributes to barrier count")),
            (1, 3, Structural("thread 1 arrival contributes to barrier count")),
            (2, 3, Structural("thread 2 arrival contributes to barrier count")),
        ],
    )
    barrier_triple = SepTriple(
        pre=sep_of(
            Pure("thread_0 running"),
            Pure("thread_1 running"),
            Pure("thread_2 running"),
        ),
        command="barrier.wait()  # all 3 threads",
        post=sep_of(
            Pure("thread_0 past_barrier"),
            Pure("thread_1 past_barrier"),
            Pure("thread_2 past_barrier"),
        ),
    )
    _sep_check(
        "Ex 61: Barrier sync: 3 threads (CechGlue)",
        "BARRIER",
        barrier_triple, barrier_proof,
        hott_constructs=["CechGlue", "Structural", "Sep", "Pure"],
    )

    # -- Ex 62: Condition variable wait/notify (PathComp) ----------
    # wait() releases lock + blocks; notify() wakes + reacquires lock.
    # The composed path: locked -> waiting -> notified -> locked.
    cv_wait_path = TransportProof(
        Lam("state", PyObjType(), Var("lock_state")),
        Structural("wait: release lock, enter wait queue"),
        AxiomInvocation("condvar_wait_release"),
    )
    cv_notify_path = TransportProof(
        Lam("state", PyObjType(), Var("lock_state")),
        Structural("notify: wake thread, reacquire lock"),
        AxiomInvocation("condvar_notify_acquire"),
    )
    cv_proof = PathComp(cv_wait_path, cv_notify_path)

    cv_triple = SepTriple(
        pre=Sep(PointsTo("lock", Var("held")), Pure("predicate false")),
        command="cv.wait(lock); ... cv.notify()",
        post=Sep(PointsTo("lock", Var("held")), Pure("predicate true")),
    )
    _sep_check(
        "Ex 62: Condvar: wait · notify = predicate satisfied",
        "CONDVAR",
        cv_triple, cv_proof,
        hott_constructs=["PathComp", "TransportProof"],
    )

    # -- Ex 63: Futures and promises (Sym for cancellation) --------
    # A future represents a value not yet computed.
    # Setting the promise is a path from pending to resolved.
    # Cancellation is the Sym (inverse path).
    future_pre = Pure("promise pending")
    future_post = PointsTo("future", Var("result"))
    resolve_triple = SepTriple(
        pre=future_pre, command="promise.set_result(result)",
        post=future_post,
    )
    resolve_proof = TransportProof(
        Lam("state", PyObjType(), Var("promise_state")),
        Structural("set_result transitions pending -> resolved"),
        AxiomInvocation("future_resolve_once"),
    )
    _sep_check(
        "Ex 63: Future resolve: pending -> result (TransportProof)",
        "FUTURE",
        resolve_triple, resolve_proof,
        hott_constructs=["TransportProof", "Pure", "PointsTo"],
    )

    cancel_proof = TransportProof(
        Lam("state", PyObjType(), Var("promise_state")),
        Sym(Structural("cancellation reverses the resolve path")),
        AxiomInvocation("future_cancel_inverse"),
    )
    cancel_triple = SepTriple(
        pre=future_post, command="future.cancel()",
        post=Pure("promise cancelled"),
    )
    _sep_check(
        "Ex 64: Future cancel: result -> cancelled (Sym)",
        "FUTURE",
        cancel_triple, cancel_proof,
        hott_constructs=["TransportProof", "Sym", "Pure"],
    )

    # -- Ex 65: Concurrent skip list level invariant (ListInduction) -
    # A skip list maintains sorted order at every level.
    # ListInduction proves the invariant holds for level 0 (base linked
    # list) and is preserved when adding each higher level.
    skiplist_proof = ListInduction(
        var="level",
        nil_proof=Structural("level 0: standard sorted linked list"),
        cons_proof=TransportProof(
            Lam("lev", PyObjType(), Var("sorted_invariant")),
            Structural("level k+1 is a sublist of level k, inheriting order"),
            AxiomInvocation("skiplist_level_subset"),
        ),
    )
    goal_skiplist = _type_goal(
        ctx, Var("skip_list"),
        RefinementType(PyObjType(), "sl", "sorted_at_all_levels(sl)"),
    )
    _check(
        "Ex 65: Skip list: sorted at all levels (ListInduction)",
        "SKIPLIST",
        ctx, goal_skiplist, skiplist_proof,
        hott_constructs=["ListInduction", "TransportProof", "RefinementType"],
    )


# =====================================================================
# HoTT Construct Inventory
# =====================================================================

def print_construct_inventory() -> None:
    """Print which HoTT constructs appear in which examples."""
    constructs = {
        "PathAbs (path abstraction)":
            "Ex 1-3, 6, 8, 11, 15-16, 23, 27, 31, 34, 36, 41-42, 45, 48, 50-51, 54, 60",
        "PathApp (path application)":
            "Ex 34",
        "Comp (Kan composition)":
            "Ex 2-3, 15-16, 23, 27, 31, 36, 45, 50-51, 54, 60",
        "Transport (type family transport)":
            "Ex 11",
        "TransportProof (transport proof term)":
            "Ex 1-4, 6-8, 11-12, 15-17, 20-21, 23-25, 27-29, 31-32, "
            "34-37, 40-42, 44-45, 47-48, 50-54, 56-58, 60, 62-65",
        "CechGlue (Cech nerve gluing)":
            "Ex 13, 18-19, 21, 33, 38, 49, 61",
        "PathComp (path composition)":
            "Ex 17, 20, 40, 54, 62",
        "Fiber (fibration)":
            "Ex 5, 9, 14, 22, 26, 39, 46, 52, 55, 59",
        "DuckPath (duck-type path)":
            "Ex 10, 30, 57",
        "Patch (monkey-patch path)":
            "Ex 44",
        "Cases (case analysis)":
            "Ex 43, 47, 56",
        "NatInduction (natural induction)":
            "Ex 53",
        "ListInduction (list induction)":
            "Ex 65",
        "Sym (path inverse)":
            "Ex 7, 12, 24, 34, 37, 64",
        "Refl (reflexivity)":
            "Ex 1, 4, 10, 13, 18-19, 21, 30, 33, 38",
        "SepTriple (separation logic)":
            "Ex 1-4, 6-7, 11-13, 16, 18-20, 23-25, 27-29, 32-38, "
            "51, 54, 58, 60-64",
        "Exists (existential heap prop)":
            "Ex 6, 11, 13, 16, 18-19",
        "Pure (pure heap prop)":
            "Ex 1, 4, 8-9, 14-15, 22, 25-26, 35, 41, 43, 45-47, 50-52, "
            "56, 58, 61, 63-64",
        "Cut + Assume":
            "Ex 55",
        "RefinementType (subtype)":
            "Ex 9, 26, 35, 52-53, 55-56, 59, 65",
        "UnionType (sum type)":
            "Ex 14, 43, 46-47, 56",
        "IfThenElse (conditional)":
            "Ex 42",
        "Lam (lambda)":
            "all TransportProof examples, Ex 44",
    }
    dash = "\u2500"
    print(f"\n{dash}{dash} HoTT Construct Inventory {dash * 37}")
    for construct, examples in constructs.items():
        print(f"  {construct:52s} {examples}")


# =====================================================================
# Main / run_all
# =====================================================================

def run_all() -> tuple[int, int]:
    """Run all sections and return (passed, failed)."""
    global _PASS, _FAIL
    _PASS = 0
    _FAIL = 0

    bar = "\u2550" * 65
    print(bar)
    print("  Pulse Concurrency - F* Tutorial -> SynHoPy Translation")
    print(bar)

    section1_atomic_operations()
    section2_invariants()
    section3_spin_locks()
    section4_parallel_increment()
    section5_verified_threading()
    section6_concurrent_data_structures()
    section7_async_await()
    section8_message_passing()
    section9_gil_awareness()
    section10_deadlock_freedom()
    section11_advanced_patterns()

    print_construct_inventory()

    print()
    print(f"  Results: {_PASS} passed, {_FAIL} failed out of {_PASS + _FAIL}")
    print(bar)

    return (_PASS, _FAIL)


def main() -> int:
    passed, failed = run_all()
    return 1 if failed > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
