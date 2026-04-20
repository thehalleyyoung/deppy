"""
Parallel Verification Scheduler

Implements the "Parallel Verification" section from the monograph.
Functions in different connected components of the call graph can be
verified in parallel.  Within a component, callees are verified before
callers (topological order).

Architecture
------------
  VerificationGraph   – dependency graph where edges mean "f calls g"
  ParallelScheduler   – schedule verification tasks across a thread pool
  SCCHandler          – handle strongly connected components (mutual recursion)
  SchedulingReport    – summary of the computed schedule

The key insight: a module's function‐call graph decomposes into
connected components.  Within each component the topological layers
(verification rounds) expose independent functions that can be checked
concurrently.  Mutually recursive groups (SCCs) are collapsed into
single nodes and verified via a fixed‐point iteration.
"""
from __future__ import annotations

import ast
import threading
import time
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, Future, as_completed
from dataclasses import dataclass, field
from typing import Any, Callable

from synhopy.core.kernel import TrustLevel, VerificationResult


# ═══════════════════════════════════════════════════════════════════
# 1.  Verification Dependency Graph
# ═══════════════════════════════════════════════════════════════════


class VerificationGraph:
    """Dependency graph where edges represent "f calls g".

    Functions in distinct connected components are trivially parallelizable.
    Within a component, topological order determines the schedule.
    """

    def __init__(self) -> None:
        self._nodes: set[str] = set()
        self._edges: dict[str, set[str]] = {}  # caller -> {callees}

    # -- mutation --------------------------------------------------------

    def add_function(self, name: str) -> None:
        """Register a function in the graph."""
        self._nodes.add(name)
        self._edges.setdefault(name, set())

    def add_call(self, caller: str, callee: str) -> None:
        """Record that *caller* invokes *callee*."""
        self.add_function(caller)
        self.add_function(callee)
        self._edges[caller].add(callee)

    # -- AST construction ------------------------------------------------

    def build_from_module(self, module_ast: ast.Module) -> None:
        """Build graph from a module AST by analyzing function calls.

        Only considers top‐level ``def`` and calls to other top‐level
        functions defined in the same module (i.e. intra‐module calls).
        """
        # Collect top-level function names.
        func_names: set[str] = set()
        for node in ast.iter_child_nodes(module_ast):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                func_names.add(node.name)

        for node in ast.iter_child_nodes(module_ast):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                self.add_function(node.name)
                for child in ast.walk(node):
                    if isinstance(child, ast.Call):
                        callee_name = _extract_call_name(child)
                        if callee_name and callee_name in func_names:
                            self.add_call(node.name, callee_name)

    # -- queries ---------------------------------------------------------

    @property
    def nodes(self) -> frozenset[str]:
        return frozenset(self._nodes)

    def callees(self, name: str) -> frozenset[str]:
        """Return functions that *name* directly calls."""
        return frozenset(self._edges.get(name, set()))

    def callers(self, name: str) -> frozenset[str]:
        """Return functions that directly call *name*."""
        return frozenset(
            n for n, cs in self._edges.items() if name in cs
        )

    def _undirected_adj(self) -> dict[str, set[str]]:
        """Build an undirected adjacency list for component analysis."""
        adj: dict[str, set[str]] = {n: set() for n in self._nodes}
        for caller, callees in self._edges.items():
            for callee in callees:
                adj[caller].add(callee)
                adj[callee].add(caller)
        return adj

    def connected_components(self) -> list[set[str]]:
        """Find connected components (independent verification groups).

        Uses BFS on the undirected view of the graph.
        """
        adj = self._undirected_adj()
        visited: set[str] = set()
        components: list[set[str]] = []

        for start in sorted(self._nodes):
            if start in visited:
                continue
            component: set[str] = set()
            queue: deque[str] = deque([start])
            while queue:
                node = queue.popleft()
                if node in visited:
                    continue
                visited.add(node)
                component.add(node)
                for neighbour in adj.get(node, set()):
                    if neighbour not in visited:
                        queue.append(neighbour)
            components.append(component)

        return components

    def topological_order(self, component: set[str] | None = None) -> list[str]:
        """Topological sort within a *component* (Kahn's algorithm).

        Returns callees before callers so that leaf functions come first.
        Raises ``ValueError`` if the sub‐graph has a cycle — use
        :class:`SCCHandler` to collapse cycles first.
        """
        nodes = component if component is not None else self._nodes

        # Build in-degree restricted to *nodes*.  "in" here means
        # "is called by" — we want callees first, so an edge caller→callee
        # means callee has in‑degree 0 relative to *being needed first*.
        # We reverse the direction: edge callee←caller, counting how many
        # callers still need a callee.
        #
        # Actually we want callees before callers.  So in the dependency
        # sense: caller depends on callee.  Kahn's on "depends on":
        #   in_degree[caller] = number of callees in component
        in_deg: dict[str, int] = {n: 0 for n in nodes}
        for n in nodes:
            for callee in self._edges.get(n, set()):
                if callee in nodes:
                    in_deg[n] += 1  # n depends on callee

        queue: deque[str] = deque(
            sorted(n for n in nodes if in_deg[n] == 0)
        )
        order: list[str] = []

        while queue:
            node = queue.popleft()
            order.append(node)
            # node is resolved — decrease in_deg for its callers
            for caller in sorted(nodes):
                if node in self._edges.get(caller, set()):
                    if caller in nodes:
                        in_deg[caller] -= 1
                        if in_deg[caller] == 0:
                            queue.append(caller)

        if len(order) != len(nodes):
            raise ValueError(
                "Cycle detected; use SCCHandler to collapse mutual recursion"
            )
        return order

    def verification_rounds(self) -> list[list[str]]:
        """Compute verification rounds across the *entire* graph.

        Round 0: leaf functions (no outgoing calls within the graph).
        Round k+1: functions whose callees are all in rounds 0..k.

        Each round is a list of functions that can be verified in parallel.
        """
        assigned: dict[str, int] = {}
        rounds: list[list[str]] = []

        # Iteratively peel off nodes whose dependencies are all assigned.
        remaining = set(self._nodes)
        while remaining:
            current_round: list[str] = []
            for n in sorted(remaining):
                deps = self._edges.get(n, set()) & self._nodes
                if all(d in assigned for d in deps):
                    current_round.append(n)
            if not current_round:
                # Remaining nodes form cycles — treat each SCC as one round.
                handler = SCCHandler()
                sccs = handler.find_sccs(self)
                # Only keep SCCs that intersect remaining
                for scc in sccs:
                    scc_remaining = [n for n in scc if n in remaining]
                    if scc_remaining:
                        for n in scc_remaining:
                            assigned[n] = len(rounds)
                        rounds.append(scc_remaining)
                        for n in scc_remaining:
                            remaining.discard(n)
                if not remaining:
                    break
                continue
            for n in current_round:
                assigned[n] = len(rounds)
                remaining.discard(n)
            rounds.append(current_round)

        return rounds

    def max_parallelism(self) -> int:
        """Maximum number of functions that can be verified in parallel.

        This equals the size of the largest verification round.
        """
        rounds = self.verification_rounds()
        if not rounds:
            return 0
        return max(len(r) for r in rounds)


# ═══════════════════════════════════════════════════════════════════
# 2.  Parallel Scheduler
# ═══════════════════════════════════════════════════════════════════


class ParallelScheduler:
    """Schedule verification tasks across a thread pool.

    Uses the verification graph to determine which functions
    can be verified concurrently.
    """

    def __init__(self, max_workers: int = 4) -> None:
        self._max_workers = max_workers

    def schedule(
        self,
        graph: VerificationGraph,
        verify_fn: Callable[[str], VerificationResult],
    ) -> dict[str, VerificationResult]:
        """Verify all functions respecting dependencies.

        Uses :class:`concurrent.futures.ThreadPoolExecutor` to parallelize
        within each round.  Rounds are executed sequentially so that all
        callees are verified before their callers.
        """
        rounds = graph.verification_rounds()
        results: dict[str, VerificationResult] = {}

        with ThreadPoolExecutor(max_workers=self._max_workers) as pool:
            for rnd in rounds:
                futures: dict[Future[VerificationResult], str] = {}
                for fn_name in rnd:
                    fut = pool.submit(verify_fn, fn_name)
                    futures[fut] = fn_name

                for fut in as_completed(futures):
                    fn_name = futures[fut]
                    try:
                        results[fn_name] = fut.result()
                    except Exception as exc:
                        results[fn_name] = VerificationResult.fail(
                            f"Exception during verification of {fn_name}: {exc}",
                            code="E_PARALLEL",
                        )

        return results

    def estimate_speedup(self, graph: VerificationGraph) -> float:
        """Estimate the speedup from parallelization.

        ``sequential_time / parallel_time ≈ total_functions / num_rounds``

        Assumes each function takes the same time to verify (uniform cost
        model).  Real speedup depends on per‐function cost variance.
        """
        rounds = graph.verification_rounds()
        total = sum(len(r) for r in rounds)
        num_rounds = len(rounds)
        if num_rounds == 0:
            return 1.0
        return total / num_rounds

    def report(self, graph: VerificationGraph) -> SchedulingReport:
        """Build a :class:`SchedulingReport` from the graph."""
        handler = SCCHandler()
        sccs = handler.find_sccs(graph)
        non_trivial_sccs = [s for s in sccs if len(s) > 1]
        rounds = graph.verification_rounds()

        return SchedulingReport(
            total_functions=len(graph.nodes),
            num_components=len(graph.connected_components()),
            num_rounds=len(rounds),
            max_parallelism=graph.max_parallelism(),
            estimated_speedup=self.estimate_speedup(graph),
            sccs=len(non_trivial_sccs),
        )


# ═══════════════════════════════════════════════════════════════════
# 3.  SCC Handling for Mutual Recursion
# ═══════════════════════════════════════════════════════════════════


class SCCHandler:
    """Handle strongly connected components (mutual recursion).

    Functions in an SCC must be verified together using
    a fixed‐point computation.
    """

    def find_sccs(self, graph: VerificationGraph) -> list[list[str]]:
        """Tarjan's algorithm for finding SCCs.

        Returns SCCs in reverse topological order (callees before callers).
        """
        index_counter = [0]
        stack: list[str] = []
        on_stack: set[str] = set()
        indices: dict[str, int] = {}
        lowlinks: dict[str, int] = {}
        result: list[list[str]] = []

        def strongconnect(v: str) -> None:
            indices[v] = index_counter[0]
            lowlinks[v] = index_counter[0]
            index_counter[0] += 1
            stack.append(v)
            on_stack.add(v)

            for w in sorted(graph.callees(v)):
                if w not in indices:
                    strongconnect(w)
                    lowlinks[v] = min(lowlinks[v], lowlinks[w])
                elif w in on_stack:
                    lowlinks[v] = min(lowlinks[v], indices[w])

            # Root of an SCC
            if lowlinks[v] == indices[v]:
                scc: list[str] = []
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    scc.append(w)
                    if w == v:
                        break
                result.append(scc)

        for v in sorted(graph.nodes):
            if v not in indices:
                strongconnect(v)

        return result

    def verify_scc(
        self,
        scc: list[str],
        verify_fn: Callable[[str], VerificationResult],
        max_iterations: int = 5,
    ) -> dict[str, VerificationResult]:
        """Verify a mutually recursive group.

        Strategy: assume all specs, verify each function, iterate until
        a fixed point is reached or *max_iterations* is exceeded.

        Fixed point = all results remain unchanged between iterations.
        """
        results: dict[str, VerificationResult] = {}
        for _ in range(max_iterations):
            new_results: dict[str, VerificationResult] = {}
            for fn_name in scc:
                new_results[fn_name] = verify_fn(fn_name)

            if _results_unchanged(results, new_results):
                return new_results
            results = new_results

        # Mark as fixed-point-not-reached but return best effort
        for fn_name in results:
            if results[fn_name].success:
                results[fn_name] = VerificationResult(
                    success=True,
                    trust_level=TrustLevel.UNTRUSTED,
                    message=(
                        f"Verified but fixed point not reached "
                        f"after {max_iterations} iterations"
                    ),
                )
        return results

    def condense(self, graph: VerificationGraph) -> tuple[
        VerificationGraph, dict[str, list[str]]
    ]:
        """Condense SCCs into single nodes, returning the DAG and a map.

        Returns
        -------
        condensed : VerificationGraph
            A DAG where each SCC is replaced by a single representative
            node (the lexicographically first member).
        scc_map : dict[str, list[str]]
            Maps each representative node to the full SCC member list.
        """
        sccs = self.find_sccs(graph)
        node_to_rep: dict[str, str] = {}
        scc_map: dict[str, list[str]] = {}

        for scc in sccs:
            rep = min(scc)
            scc_map[rep] = sorted(scc)
            for member in scc:
                node_to_rep[member] = rep

        condensed = VerificationGraph()
        for rep in scc_map:
            condensed.add_function(rep)

        for caller in graph.nodes:
            for callee in graph.callees(caller):
                rep_caller = node_to_rep[caller]
                rep_callee = node_to_rep[callee]
                if rep_caller != rep_callee:
                    condensed.add_call(rep_caller, rep_callee)

        return condensed, scc_map


# ═══════════════════════════════════════════════════════════════════
# 4.  Scheduling Report
# ═══════════════════════════════════════════════════════════════════


@dataclass
class SchedulingReport:
    """Summary of the parallel verification schedule."""

    total_functions: int = 0
    num_components: int = 0
    num_rounds: int = 0
    max_parallelism: int = 0
    estimated_speedup: float = 1.0
    sccs: int = 0  # number of mutually recursive groups

    def summary(self) -> str:
        lines = [
            "╔══════════════════════════════════════════╗",
            "║      Parallel Verification Schedule      ║",
            "╠══════════════════════════════════════════╣",
            f"║  Total functions      : {self.total_functions:<16} ║",
            f"║  Connected components : {self.num_components:<16} ║",
            f"║  Verification rounds  : {self.num_rounds:<16} ║",
            f"║  Max parallelism      : {self.max_parallelism:<16} ║",
            f"║  Estimated speedup    : {self.estimated_speedup:<16.2f} ║",
            f"║  Mutual recursion SCCs: {self.sccs:<16} ║",
            "╚══════════════════════════════════════════╝",
        ]
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════════════


def _extract_call_name(node: ast.Call) -> str | None:
    """Extract the callee name from a simple ``f()`` or ``self.f()`` call."""
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        return node.func.attr
    return None


def _results_unchanged(
    old: dict[str, VerificationResult],
    new: dict[str, VerificationResult],
) -> bool:
    """Check whether two result dicts have the same success/message."""
    if old.keys() != new.keys():
        return False
    return all(
        old[k].success == new[k].success and old[k].message == new[k].message
        for k in old
    )


# ═══════════════════════════════════════════════════════════════════
# 5.  Self-tests
# ═══════════════════════════════════════════════════════════════════


def _self_test() -> None:
    """Smoke‐tests exercised via ``python -m synhopy.pipeline.parallel``."""
    import textwrap

    print("── VerificationGraph basic operations ──")
    g = VerificationGraph()
    g.add_function("a")
    g.add_function("b")
    g.add_function("c")
    g.add_call("a", "b")
    g.add_call("a", "c")
    assert g.nodes == frozenset({"a", "b", "c"})
    assert g.callees("a") == frozenset({"b", "c"})
    assert g.callers("b") == frozenset({"a"})
    print("  nodes / callees / callers ... OK")

    # -- connected components --
    g2 = VerificationGraph()
    for name in ("f", "g", "h", "x", "y"):
        g2.add_function(name)
    g2.add_call("f", "g")
    g2.add_call("g", "h")
    g2.add_call("x", "y")
    comps = g2.connected_components()
    assert len(comps) == 2, f"Expected 2 components, got {len(comps)}"
    comp_sets = [frozenset(c) for c in comps]
    assert frozenset({"f", "g", "h"}) in comp_sets
    assert frozenset({"x", "y"}) in comp_sets
    print("  connected_components ... OK")

    # -- topological order --
    topo = g2.topological_order({"f", "g", "h"})
    assert topo.index("h") < topo.index("g") < topo.index("f"), (
        f"Bad topo order: {topo}"
    )
    print("  topological_order ... OK")

    # -- verification rounds --
    rounds = g2.verification_rounds()
    # Round 0 should contain leaf functions h, y
    assert "h" in rounds[0] or "y" in rounds[0], f"Unexpected round 0: {rounds[0]}"
    print(f"  verification_rounds ({len(rounds)} rounds) ... OK")

    # -- max parallelism --
    mp = g2.max_parallelism()
    assert mp >= 2, f"Expected max_parallelism >= 2, got {mp}"
    print(f"  max_parallelism = {mp} ... OK")

    # -- build from AST --
    src = textwrap.dedent("""\
        def helper():
            pass

        def worker():
            helper()

        def main():
            worker()

        def standalone():
            pass
    """)
    tree = ast.parse(src)
    g3 = VerificationGraph()
    g3.build_from_module(tree)
    assert g3.callees("worker") == frozenset({"helper"})
    assert g3.callees("main") == frozenset({"worker"})
    assert g3.callees("standalone") == frozenset()
    comps3 = g3.connected_components()
    assert len(comps3) == 2, f"Expected 2 components, got {len(comps3)}"
    print("  build_from_module ... OK")

    # -- SCC detection --
    print("\n── SCCHandler ──")
    g4 = VerificationGraph()
    g4.add_call("a", "b")
    g4.add_call("b", "a")  # mutual recursion
    g4.add_call("a", "c")
    handler = SCCHandler()
    sccs = handler.find_sccs(g4)
    scc_sets = [frozenset(s) for s in sccs]
    assert frozenset({"a", "b"}) in scc_sets, f"Expected SCC {{a,b}}, got {scc_sets}"
    print("  find_sccs (mutual recursion) ... OK")

    # -- SCC condensation --
    condensed, scc_map = handler.condense(g4)
    assert len(scc_map) == 2  # {a,b} condensed + {c}
    print(f"  condense ({len(scc_map)} nodes in DAG) ... OK")

    # -- SCC verification --
    call_count: dict[str, int] = defaultdict(int)

    def _mock_verify(name: str) -> VerificationResult:
        call_count[name] += 1
        return VerificationResult.ok(TrustLevel.KERNEL, f"verified {name}")

    scc_results = handler.verify_scc(["a", "b"], _mock_verify)
    assert all(r.success for r in scc_results.values())
    print("  verify_scc (fixed point) ... OK")

    # -- Parallel scheduler --
    print("\n── ParallelScheduler ──")
    lock = threading.Lock()
    verified_order: list[str] = []

    def _threaded_verify(name: str) -> VerificationResult:
        with lock:
            verified_order.append(name)
        return VerificationResult.ok(TrustLevel.KERNEL, f"ok:{name}")

    sched = ParallelScheduler(max_workers=2)
    results = sched.schedule(g2, _threaded_verify)
    assert len(results) == 5
    assert all(r.success for r in results.values())
    print(f"  schedule ({len(results)} results) ... OK")

    speedup = sched.estimate_speedup(g2)
    assert speedup >= 1.0, f"Expected speedup >= 1.0, got {speedup}"
    print(f"  estimate_speedup = {speedup:.2f} ... OK")

    # -- Scheduling report --
    print("\n── SchedulingReport ──")
    report = sched.report(g2)
    assert report.total_functions == 5
    assert report.num_components == 2
    print(report.summary())

    # -- verification rounds with cycles --
    print("\n── Cycles in verification_rounds ──")
    g5 = VerificationGraph()
    g5.add_call("p", "q")
    g5.add_call("q", "p")  # cycle
    g5.add_call("p", "r")
    rounds5 = g5.verification_rounds()
    all_in_rounds = set()
    for r in rounds5:
        all_in_rounds.update(r)
    assert all_in_rounds == {"p", "q", "r"}, (
        f"All nodes should appear in rounds: {all_in_rounds}"
    )
    print(f"  verification_rounds with cycle ({len(rounds5)} rounds) ... OK")

    # -- exception handling in scheduler --
    print("\n── Exception handling ──")

    def _failing_verify(name: str) -> VerificationResult:
        if name == "g":
            raise RuntimeError("simulated failure")
        return VerificationResult.ok(TrustLevel.KERNEL, f"ok:{name}")

    results_fail = sched.schedule(g2, _failing_verify)
    assert not results_fail["g"].success
    assert "simulated failure" in results_fail["g"].message
    print("  exception handling ... OK")

    # -- empty graph --
    print("\n── Edge cases ──")
    g_empty = VerificationGraph()
    assert g_empty.connected_components() == []
    assert g_empty.verification_rounds() == []
    assert g_empty.max_parallelism() == 0
    results_empty = sched.schedule(g_empty, _mock_verify)
    assert results_empty == {}
    print("  empty graph ... OK")

    # -- single node --
    g_single = VerificationGraph()
    g_single.add_function("solo")
    assert len(g_single.connected_components()) == 1
    assert g_single.verification_rounds() == [["solo"]]
    assert g_single.max_parallelism() == 1
    print("  single node ... OK")

    # -- diamond dependency: a→b, a→c, b→d, c→d --
    g_diamond = VerificationGraph()
    g_diamond.add_call("a", "b")
    g_diamond.add_call("a", "c")
    g_diamond.add_call("b", "d")
    g_diamond.add_call("c", "d")
    rounds_d = g_diamond.verification_rounds()
    # d must be in round 0, b and c in round 1, a in round 2
    assert rounds_d[0] == ["d"]
    assert set(rounds_d[1]) == {"b", "c"}
    assert rounds_d[2] == ["a"]
    print("  diamond dependency ... OK")

    print("\n✅ All self‐tests passed.")


if __name__ == "__main__":
    _self_test()
