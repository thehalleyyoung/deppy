"""P29 Axiom: Async Pattern Equivalences.

Establishes equivalences between different asyncio/async-await
patterns that produce the same concurrent or sequential behaviour.

Mathematical basis: Async computations form a monad (the IO monad
in the async runtime).  Concurrent composition via gather is the
monoidal product; sequential await is Kleisli composition:
    asyncio.gather(f(), g()) ≅ (await f(), await g())   (when independent)
    async for x in ait     ≅ while True: x = await ait.__anext__()
    async with cm as v     ≅ v = await cm.__aenter__(); ... await cm.__aexit__()
    asyncio.create_task(c) ≅ await c                    (when immediately awaited)

Key rewrites:
  • asyncio.gather(*coros) ↔ sequential await (for independent coros)
  • async for ↔ manual __aiter__/__anext__
  • async with ↔ manual __aenter__/__aexit__
  • create_task + immediate await ↔ direct await
  • asyncio.Queue put/get ↔ manual async queue
  • asyncio.wait ↔ asyncio.as_completed
  • async generator expr ↔ sync generator expr (for non-async bodies)
  • asyncio.run ↔ event_loop.run_until_complete

(§P29, Python-specific axioms)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

from ..denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── Axiom metadata ──────────────────────────────────────────

AXIOM_NAME = "P29_async"
AXIOM_CATEGORY = "python_idiom"

COMPOSES_WITH = ["P17_context", "P23_iteration"]
REQUIRES: List[str] = []

SOUNDNESS_PROOF = r"""
Theorem (P29 Async Pattern Equivalences).

1. asyncio.gather(c1, c2, ...) ≡ (await c1, await c2, ...)
   When coroutines are independent (no shared mutable state),
   concurrent gather and sequential await produce identical results.
   (Modulo scheduling non-determinism which does not affect values.)

2. async for x in ait ≡ while True: try: x = await ait.__anext__()
                         except StopAsyncIteration: break
   The async for protocol desugars to __aiter__/__anext__ calls.

3. async with cm as v ≡ v = await cm.__aenter__(); try: ...
                         finally: await cm.__aexit__(...)
   The async with protocol desugars to __aenter__/__aexit__ calls.

4. t = create_task(c); r = await t ≡ r = await c
   When a task is created and immediately awaited with no intervening
   work, it is equivalent to directly awaiting the coroutine.

5. asyncio.Queue.put(x) + Queue.get() ≡ manual async queue
   asyncio.Queue is a channel; manual implementations with
   conditions/events provide the same FIFO semantics.

6. asyncio.wait(fs) ≡ asyncio.as_completed(fs) (for result collection)
   Both iterate over futures; as_completed yields in completion order.

7. asyncio.run(main()) ≡ loop.run_until_complete(main())
   asyncio.run creates a new event loop and runs until complete.

8. async genexpr ≡ sync genexpr (when body is synchronous)
   If the generator body involves no awaits, async iteration is
   equivalent to synchronous iteration.
"""

EXAMPLES = [
    ("asyncio_gather($c1, $c2)", "sequential_await($c1, $c2)", "P29_gather_to_sequential"),
    ("async_for($ait, $body)", "manual_aiter($ait, $body)", "P29_async_for_to_manual"),
    ("async_with($cm, $body)", "manual_aenter_aexit($cm, $body)", "P29_async_with_to_manual"),
    ("create_task($c)", "direct_await($c)", "P29_task_to_await"),
    ("asyncio_run($main)", "event_loop_run($main)", "P29_run_to_loop"),
]

_ASYNC_OPS = frozenset({
    'asyncio_gather', 'sequential_await', 'async_for', 'manual_aiter',
    'async_with', 'manual_aenter_aexit', 'create_task', 'direct_await',
    'async_queue_put_get', 'manual_async_queue',
    'asyncio_wait', 'asyncio_as_completed',
    'async_genexpr', 'sync_genexpr',
    'asyncio_run', 'event_loop_run',
})


# ═══════════════════════════════════════════════════════════
# Main axiom: apply
# ═══════════════════════════════════════════════════════════

def apply(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    """P29: Async pattern equivalence rewrites."""
    results: List[Tuple[OTerm, str]] = []

    # ── asyncio.gather(*coros) ↔ sequential_await ──
    if isinstance(term, OOp) and term.name == 'asyncio_gather' and len(term.args) >= 1:
        results.append((
            OOp('sequential_await', term.args),
            'P29_gather_to_sequential',
        ))

    if isinstance(term, OOp) and term.name == 'sequential_await' and len(term.args) >= 1:
        results.append((
            OOp('asyncio_gather', term.args),
            'P29_sequential_to_gather',
        ))

    # ── async for ↔ manual __aiter__/__anext__ ──
    if isinstance(term, OOp) and term.name == 'async_for' and len(term.args) >= 2:
        results.append((
            OOp('manual_aiter', term.args),
            'P29_async_for_to_manual',
        ))

    if isinstance(term, OOp) and term.name == 'manual_aiter' and len(term.args) >= 2:
        results.append((
            OOp('async_for', term.args),
            'P29_manual_aiter_to_async_for',
        ))

    # ── async with ↔ manual __aenter__/__aexit__ ──
    if isinstance(term, OOp) and term.name == 'async_with' and len(term.args) >= 2:
        results.append((
            OOp('manual_aenter_aexit', term.args),
            'P29_async_with_to_manual',
        ))

    if isinstance(term, OOp) and term.name == 'manual_aenter_aexit' and len(term.args) >= 2:
        results.append((
            OOp('async_with', term.args),
            'P29_manual_to_async_with',
        ))

    # ── create_task + await ↔ direct_await ──
    if isinstance(term, OOp) and term.name == 'create_task' and len(term.args) >= 1:
        results.append((
            OOp('direct_await', term.args),
            'P29_create_task_to_direct_await',
        ))

    if isinstance(term, OOp) and term.name == 'direct_await' and len(term.args) >= 1:
        results.append((
            OOp('create_task', term.args),
            'P29_direct_await_to_create_task',
        ))

    # ── asyncio.Queue put/get ↔ manual_async_queue ──
    if isinstance(term, OOp) and term.name == 'async_queue_put_get' and len(term.args) >= 1:
        results.append((
            OOp('manual_async_queue', term.args),
            'P29_queue_to_manual',
        ))

    if isinstance(term, OOp) and term.name == 'manual_async_queue' and len(term.args) >= 1:
        results.append((
            OOp('async_queue_put_get', term.args),
            'P29_manual_to_queue',
        ))

    # ── asyncio.wait ↔ asyncio.as_completed ──
    if isinstance(term, OOp) and term.name == 'asyncio_wait' and len(term.args) >= 1:
        results.append((
            OOp('asyncio_as_completed', term.args),
            'P29_wait_to_as_completed',
        ))

    if isinstance(term, OOp) and term.name == 'asyncio_as_completed' and len(term.args) >= 1:
        results.append((
            OOp('asyncio_wait', term.args),
            'P29_as_completed_to_wait',
        ))

    # ── async genexpr ↔ sync genexpr (sync body) ──
    if isinstance(term, OOp) and term.name == 'async_genexpr' and len(term.args) >= 1:
        results.append((
            OOp('sync_genexpr', term.args),
            'P29_async_genexpr_to_sync',
        ))

    if isinstance(term, OOp) and term.name == 'sync_genexpr' and len(term.args) >= 1:
        results.append((
            OOp('async_genexpr', term.args),
            'P29_sync_genexpr_to_async',
        ))

    # ── asyncio.run ↔ event_loop.run_until_complete ──
    if isinstance(term, OOp) and term.name == 'asyncio_run' and len(term.args) >= 1:
        results.append((
            OOp('event_loop_run', term.args),
            'P29_asyncio_run_to_event_loop',
        ))

    if isinstance(term, OOp) and term.name == 'event_loop_run' and len(term.args) >= 1:
        results.append((
            OOp('asyncio_run', term.args),
            'P29_event_loop_to_asyncio_run',
        ))

    # ── gather of single coroutine → direct await ──
    if isinstance(term, OOp) and term.name == 'asyncio_gather' and len(term.args) == 1:
        results.append((
            OOp('direct_await', term.args),
            'P29_gather_single_to_await',
        ))

    # ── nested gather flattening ──
    if isinstance(term, OOp) and term.name == 'asyncio_gather':
        inner_args: list[OTerm] = []
        has_nested = False
        for arg in term.args:
            if isinstance(arg, OOp) and arg.name == 'asyncio_gather':
                inner_args.extend(arg.args)
                has_nested = True
            else:
                inner_args.append(arg)
        if has_nested:
            results.append((
                OOp('asyncio_gather', tuple(inner_args)),
                'P29_flatten_gather',
            ))

    return results


# ═══════════════════════════════════════════════════════════
# Inverse, recognition, scoring
# ═══════════════════════════════════════════════════════════

def apply_inverse(term: OTerm, ctx: Any = None) -> List[Tuple[OTerm, str]]:
    results = apply(term, ctx)
    inv = {l for _, l in results if '_to_gather' in l or '_to_async_for' in l
           or '_to_async_with' in l or '_to_create_task' in l
           or '_to_queue' in l or '_to_wait' in l
           or '_to_async' in l or '_to_asyncio_run' in l}
    return [(t, l) for t, l in results if l in inv]


def recognizes(term: OTerm) -> bool:
    if isinstance(term, OOp) and term.name in _ASYNC_OPS:
        return True
    return False


def relevance_score(source: OTerm, target: OTerm) -> float:
    sc, tc = source.canon(), target.canon()
    for kw in ('asyncio', 'async_', 'await', 'gather', 'create_task',
               'aiter', 'aenter', 'event_loop'):
        if kw in sc and kw in tc:
            return 0.85
    async_kws = ('asyncio', 'async', 'await', 'gather', 'sequential_await',
                 'create_task', 'aiter', 'aenter', 'event_loop', 'queue')
    if (any(k in sc for k in async_kws) and any(k in tc for k in async_kws)):
        return 0.8
    if any(k in sc for k in async_kws) or any(k in tc for k in async_kws):
        return 0.3
    return 0.05


# ═══════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════

if __name__ == '__main__':
    _pass = 0
    _fail = 0

    def _assert(cond: bool, msg: str) -> None:
        global _pass, _fail
        if cond:
            _pass += 1
        else:
            _fail += 1
            print(f"  FAIL: {msg}")

    # 1. gather → sequential
    t = OOp('asyncio_gather', (OVar('c1'), OVar('c2')))
    r = apply(t)
    _assert(any(a == 'P29_gather_to_sequential' for _, a in r), "gather → sequential")

    # 2. sequential → gather
    t2 = OOp('sequential_await', (OVar('c1'), OVar('c2')))
    r2 = apply(t2)
    _assert(any(a == 'P29_sequential_to_gather' for _, a in r2), "sequential → gather")

    # 3. async_for → manual_aiter
    t3 = OOp('async_for', (OVar('ait'), OVar('body')))
    r3 = apply(t3)
    _assert(any(a == 'P29_async_for_to_manual' for _, a in r3), "async_for → manual")

    # 4. manual_aiter → async_for
    t4 = OOp('manual_aiter', (OVar('ait'), OVar('body')))
    r4 = apply(t4)
    _assert(any(a == 'P29_manual_aiter_to_async_for' for _, a in r4), "manual → async_for")

    # 5. async_with → manual
    t5 = OOp('async_with', (OVar('cm'), OVar('body')))
    r5 = apply(t5)
    _assert(any(a == 'P29_async_with_to_manual' for _, a in r5), "async_with → manual")

    # 6. manual → async_with
    t6 = OOp('manual_aenter_aexit', (OVar('cm'), OVar('body')))
    r6 = apply(t6)
    _assert(any(a == 'P29_manual_to_async_with' for _, a in r6), "manual → async_with")

    # 7. create_task → direct_await
    t7 = OOp('create_task', (OVar('c'),))
    r7 = apply(t7)
    _assert(any(a == 'P29_create_task_to_direct_await' for _, a in r7), "task → await")

    # 8. direct_await → create_task
    t8 = OOp('direct_await', (OVar('c'),))
    r8 = apply(t8)
    _assert(any(a == 'P29_direct_await_to_create_task' for _, a in r8), "await → task")

    # 9. queue → manual
    t9 = OOp('async_queue_put_get', (OVar('q'),))
    r9 = apply(t9)
    _assert(any(a == 'P29_queue_to_manual' for _, a in r9), "queue → manual")

    # 10. manual → queue
    t10 = OOp('manual_async_queue', (OVar('q'),))
    r10 = apply(t10)
    _assert(any(a == 'P29_manual_to_queue' for _, a in r10), "manual → queue")

    # 11. wait → as_completed
    t11 = OOp('asyncio_wait', (OVar('fs'),))
    r11 = apply(t11)
    _assert(any(a == 'P29_wait_to_as_completed' for _, a in r11), "wait → as_completed")

    # 12. as_completed → wait
    t12 = OOp('asyncio_as_completed', (OVar('fs'),))
    r12 = apply(t12)
    _assert(any(a == 'P29_as_completed_to_wait' for _, a in r12), "as_completed → wait")

    # 13. async genexpr → sync genexpr
    t13 = OOp('async_genexpr', (OVar('body'), OVar('col')))
    r13 = apply(t13)
    _assert(any(a == 'P29_async_genexpr_to_sync' for _, a in r13), "async gen → sync")

    # 14. asyncio.run → event_loop
    t14 = OOp('asyncio_run', (OVar('main'),))
    r14 = apply(t14)
    _assert(any(a == 'P29_asyncio_run_to_event_loop' for _, a in r14), "run → loop")

    # 15. event_loop → asyncio.run
    t15 = OOp('event_loop_run', (OVar('main'),))
    r15 = apply(t15)
    _assert(any(a == 'P29_event_loop_to_asyncio_run' for _, a in r15), "loop → run")

    # 16. gather single → direct await
    t16 = OOp('asyncio_gather', (OVar('c'),))
    r16 = apply(t16)
    _assert(any(a == 'P29_gather_single_to_await' for _, a in r16), "gather(1) → await")

    # 17. nested gather flattening
    inner = OOp('asyncio_gather', (OVar('c2'), OVar('c3')))
    t17 = OOp('asyncio_gather', (OVar('c1'), inner))
    r17 = apply(t17)
    _assert(any(a == 'P29_flatten_gather' for _, a in r17), "flatten nested gather")

    # 18. recognizes
    _assert(recognizes(t), "recognizes asyncio_gather")
    _assert(recognizes(OOp('create_task', (OVar('c'),))), "recognizes create_task")
    _assert(not recognizes(OLit(42)), "!recognizes literal")

    # 19. relevance: async ↔ async high
    _assert(relevance_score(t, t2) > 0.5, "async relevance high")

    # 20. relevance: unrelated low
    _assert(relevance_score(OLit(1), OLit(2)) < 0.2, "unrelated relevance low")

    print(f"P29 async: {_pass} passed, {_fail} failed")
