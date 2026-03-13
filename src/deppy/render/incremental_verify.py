"""Incremental re-verification via Mayer-Vietoris locality.

When code changes, don't re-verify everything.  The Mayer-Vietoris
sequence tells us exactly which cohomology classes are affected by
a local change.  Only re-check the sites whose cover overlaps the
changed region.

Given:
  - A previous SpecVerificationResult (with cover and VC results)
  - A set of changed lines

Compute:
  - Which cover sites overlap the changed lines
  - Which VCs need re-checking (via MV decomposition)
  - Which VCs are definitely unchanged (MV locality guarantee)

This provides:
  "Edit line 42 → Re-checking 3/20 VCs (sites 5, 8, 12 overlap
   the edit). 17 VCs unchanged by Mayer-Vietoris locality."

Usage:
    from deppy.render.incremental_verify import plan_incremental_reverify
    plan = plan_incremental_reverify(old_result, changed_lines={42, 43})
    print(plan.summary())
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Optional, Set, Tuple


@dataclass
class IncrementalVerifyPlan:
    """Plan for incremental re-verification."""
    changed_lines: FrozenSet[int]
    total_vcs: int = 0
    recheck_vcs: List[int] = field(default_factory=list)
    unchanged_vcs: List[int] = field(default_factory=list)
    recheck_conjuncts: Set[int] = field(default_factory=set)
    mv_components_affected: int = 0
    mv_components_total: int = 0
    explanation: str = ""

    @property
    def savings(self) -> float:
        """Fraction of VCs we can skip."""
        if self.total_vcs == 0:
            return 0.0
        return len(self.unchanged_vcs) / self.total_vcs

    def summary(self) -> str:
        lines = [
            f"Incremental re-verification plan:",
            f"  Changed lines: {sorted(self.changed_lines)}",
            f"  Total VCs: {self.total_vcs}",
            f"  Must re-check: {len(self.recheck_vcs)} VCs "
            f"(sites: {self.recheck_vcs[:10]}{'...' if len(self.recheck_vcs) > 10 else ''})",
            f"  Unchanged (MV locality): {len(self.unchanged_vcs)} VCs",
            f"  Savings: {self.savings:.0%} of VCs skipped",
            f"  MV components affected: "
            f"{self.mv_components_affected}/{self.mv_components_total}",
        ]
        if self.recheck_conjuncts:
            lines.append(
                f"  Conjuncts to re-check: {sorted(self.recheck_conjuncts)}")
        return "\n".join(lines)


def plan_incremental_reverify(
    previous_result,  # SpecVerificationResult
    changed_lines: Set[int],
) -> IncrementalVerifyPlan:
    """Plan which VCs need re-checking after code changes.

    Uses the Mayer-Vietoris decomposition from the previous
    verification to determine which connected components of the
    spec cover are affected by the changes.
    """
    cover = previous_result.cover
    vc_results = previous_result.vc_results
    spec_decomp = previous_result.spec_decomposition
    impl = previous_result.impl_analysis

    if cover is None or not vc_results:
        return IncrementalVerifyPlan(
            changed_lines=frozenset(changed_lines),
            total_vcs=len(vc_results) if vc_results else 0,
            recheck_vcs=list(range(len(vc_results) if vc_results else 0)),
            explanation="No cover available; must re-check all")

    n_sites = len(cover.sites)
    changed = frozenset(changed_lines)

    # Phase 1: Find which cover sites overlap changed lines
    affected_sites: Set[int] = set()
    for i, site in enumerate(cover.sites):
        # Each site covers a range of lines (path × conjunct)
        path_idx = site.path_idx
        if impl and path_idx < len(impl.paths):
            path = impl.paths[path_idx]
            path_lines: Set[int] = set()
            if hasattr(path, 'line_range'):
                lr = path.line_range
                if isinstance(lr, (tuple, list)) and len(lr) == 2:
                    path_lines = set(range(lr[0], lr[1] + 1))
                else:
                    path_lines = set(lr)
            # Also check the path's condition lines
            for cond in (path.conditions if hasattr(path, 'conditions') else []):
                if hasattr(cond, 'lineno'):
                    path_lines.add(cond.lineno)

            if path_lines & changed:
                affected_sites.add(i)
            elif not path_lines:
                # Conservative: if we can't determine the line range, re-check
                affected_sites.add(i)
        else:
            affected_sites.add(i)

    # Phase 2: Expand affected set via MV connectivity
    # If site i is affected and shares an overlap with site j,
    # then j may also need re-checking (the MV connecting
    # homomorphism couples them).
    if hasattr(cover, 'overlap_graph'):
        expanded = set(affected_sites)
        frontier = list(affected_sites)
        while frontier:
            site = frontier.pop()
            neighbors = cover.overlap_graph.get(site, set())
            for nb in neighbors:
                if nb not in expanded:
                    expanded.add(nb)
                    frontier.append(nb)
        affected_sites = expanded

    # Phase 3: Determine which conjuncts are affected
    affected_conjuncts: Set[int] = set()
    for i in affected_sites:
        if i < n_sites:
            affected_conjuncts.add(cover.sites[i].conjunct_idx)

    # Phase 4: Build re-check and unchanged lists
    recheck: List[int] = sorted(affected_sites)
    unchanged: List[int] = sorted(set(range(n_sites)) - affected_sites)

    # Phase 5: Count MV components
    # Build adjacency from overlap graph
    if hasattr(cover, 'overlap_graph'):
        visited: Set[int] = set()
        total_components = 0
        affected_components = 0
        for start in range(n_sites):
            if start in visited:
                continue
            component: Set[int] = set()
            queue = [start]
            visited.add(start)
            while queue:
                node = queue.pop(0)
                component.add(node)
                for nb in cover.overlap_graph.get(node, set()):
                    if nb not in visited:
                        visited.add(nb)
                        queue.append(nb)
            total_components += 1
            if component & affected_sites:
                affected_components += 1
    else:
        total_components = n_sites
        affected_components = len(affected_sites)

    return IncrementalVerifyPlan(
        changed_lines=changed,
        total_vcs=n_sites,
        recheck_vcs=recheck,
        unchanged_vcs=unchanged,
        recheck_conjuncts=affected_conjuncts,
        mv_components_affected=affected_components,
        mv_components_total=total_components,
    )
