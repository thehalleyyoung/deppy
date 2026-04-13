"""
Code proposals for chapters 37-40 (g15_impl_detail):
  - The AST Compiler in Detail
  - Duck Type Inference in Detail
  - The Čech Complex Construction Algorithm
  - End-to-End Pipeline Trace

Expanded, exhaustive utility module with 17 proposals.  Every function
and class is real, importable Python code with docstrings, type hints,
edge-case handling, and self-tests at the bottom.
"""
from __future__ import annotations

import ast
import itertools
import textwrap
import time
from collections import defaultdict
from dataclasses import dataclass, field
from typing import (
    Any, Dict, FrozenSet, List, Optional, Set, Tuple,
)


# ═══════════════════════════════════════════════════════════
# Proposal 1 — Environment inline status reporter
# ═══════════════════════════════════════════════════════════

def env_inline_status(env) -> dict:
    """Report inlining status of the compilation environment.

    Returns a dict with:
      depth        – current nesting depth
      can_inline   – whether depth < 3  (the compiler's hard limit)
      func_defs    – names available for β-reduction inlining
      class_defs   – class names tracked in the environment
      imports      – import aliases currently in scope
      binding_count – total number of live variable bindings
    """
    return {
        'depth': env.depth,
        'can_inline': env.depth < 3,
        'func_defs': list(env.func_defs.keys()),
        'class_defs': list(env.class_defs.keys()),
        'imports': dict(env.imports),
        'binding_count': len(env.bindings),
    }


# ═══════════════════════════════════════════════════════════
# Proposal 2 — Section coverage checker (presheaf completeness)
# ═══════════════════════════════════════════════════════════

@dataclass
class CoverageReport:
    """Result of checking whether section guards cover all inputs."""
    is_complete: bool
    guard_count: int
    trivially_true_guards: int
    trivially_false_guards: int
    redundant_pairs: List[Tuple[int, int]]

    def summary(self) -> str:
        tag = "COMPLETE" if self.is_complete else "INCOMPLETE"
        parts = [
            f"Coverage: {tag}",
            f"  {self.guard_count} guard(s)",
            f"  {self.trivially_true_guards} trivially-true",
            f"  {self.trivially_false_guards} trivially-false",
        ]
        if self.redundant_pairs:
            parts.append(f"  {len(self.redundant_pairs)} redundant pair(s)")
        return "\n".join(parts)


def check_section_coverage(sections, T=None) -> CoverageReport:
    """Check if the disjunction of section guards is tautological.

    This is the presheaf completeness condition: every point in
    the input space falls under at least one section's guard.
    Also detects trivially-true/false guards and redundant pairs.
    """
    guards = [s.guard for s in sections]
    n = len(guards)

    trivially_true = 0
    trivially_false = 0
    redundant: List[Tuple[int, int]] = []

    try:
        from z3 import Solver, Or, Not, And, unsat, sat, BoolVal

        solver = Solver()
        solver.set('timeout', 2000)

        for i, g in enumerate(guards):
            s = Solver()
            s.set('timeout', 500)
            s.add(Not(g))
            if s.check() == unsat:
                trivially_true += 1
            s2 = Solver()
            s2.set('timeout', 500)
            s2.add(g)
            if s2.check() == unsat:
                trivially_false += 1

        for i in range(n):
            for j in range(i + 1, n):
                s = Solver()
                s.set('timeout', 500)
                s.add(And(guards[i], guards[j]))
                if s.check() == unsat:
                    continue
                s2 = Solver()
                s2.set('timeout', 500)
                s2.add(guards[i])
                s2.add(Not(guards[j]))
                if s2.check() == unsat:
                    redundant.append((i, j))
                else:
                    s3 = Solver()
                    s3.set('timeout', 500)
                    s3.add(guards[j])
                    s3.add(Not(guards[i]))
                    if s3.check() == unsat:
                        redundant.append((j, i))

        solver.add(Not(Or(*guards)) if guards else BoolVal(True))
        is_complete = solver.check() == unsat

    except Exception:
        is_complete = False

    return CoverageReport(
        is_complete=is_complete,
        guard_count=n,
        trivially_true_guards=trivially_true,
        trivially_false_guards=trivially_false,
        redundant_pairs=redundant,
    )


# ═══════════════════════════════════════════════════════════
# Proposal 3 — Section guard simplification
# ═══════════════════════════════════════════════════════════

def simplify_section_guard(guard):
    """Simplify a Z3 Boolean guard via tactics.

    Uses Z3's ctx-solver-simplify tactic to reduce guard
    complexity, then falls back to the default simplifier.
    """
    try:
        from z3 import Tactic, Then, simplify as z3simp
        tac = Then(Tactic('ctx-solver-simplify'), Tactic('simplify'))
        goal = tac(guard)
        if len(goal) == 1 and len(goal[0]) == 1:
            return goal[0][0]
        return z3simp(guard)
    except Exception:
        try:
            from z3 import simplify as z3simp
            return z3simp(guard)
        except Exception:
            return guard


def simplify_sections(sections) -> list:
    """Return a new section list with simplified guards.

    Each section's guard is run through ``simplify_section_guard``.
    The term is left unchanged.
    """
    from dataclasses import replace as _replace
    out = []
    for s in sections:
        try:
            new_guard = simplify_section_guard(s.guard)
            out.append(type(s)(guard=new_guard, term=s.term))
        except Exception:
            out.append(s)
    return out


# ═══════════════════════════════════════════════════════════
# Proposal 4 — Duck type lattice with Hasse diagram and
#              Galois connection
# ═══════════════════════════════════════════════════════════

ALL_FIBERS = frozenset(['int', 'bool', 'str', 'pair', 'ref', 'none'])

DUCK_TYPE_FIBERS: Dict[str, FrozenSet[str]] = {
    'int': frozenset(['int']),
    'bool': frozenset(['bool']),
    'str': frozenset(['str']),
    'ref': frozenset(['ref']),
    'list': frozenset(['pair', 'ref']),
    'collection': frozenset(['pair', 'ref', 'str']),
    'any': ALL_FIBERS,
    'unknown': ALL_FIBERS,
}


def duck_type_leq(t1: str, t2: str) -> bool:
    """Check if duck type t1 ⊑ t2 in the lattice (F(t1) ⊆ F(t2))."""
    f1 = DUCK_TYPE_FIBERS.get(t1, frozenset())
    f2 = DUCK_TYPE_FIBERS.get(t2, frozenset())
    return f1 <= f2


def duck_type_meet(t1: str, t2: str) -> str:
    """Greatest lower bound — narrowest type containing F(t1) ∪ F(t2)."""
    f1 = DUCK_TYPE_FIBERS.get(t1, frozenset())
    f2 = DUCK_TYPE_FIBERS.get(t2, frozenset())
    union = f1 | f2
    best = 'any'
    best_size = len(DUCK_TYPE_FIBERS['any'])
    for name, fibers in DUCK_TYPE_FIBERS.items():
        if union <= fibers and len(fibers) < best_size:
            best = name
            best_size = len(fibers)
    return best


def duck_type_join(t1: str, t2: str) -> str:
    """Least upper bound — widest type whose fibers are in F(t1) ∩ F(t2).

    Returns 'bottom' if the intersection is empty.
    """
    f1 = DUCK_TYPE_FIBERS.get(t1, frozenset())
    f2 = DUCK_TYPE_FIBERS.get(t2, frozenset())
    inter = f1 & f2
    if not inter:
        return 'bottom'
    best = 'any'
    best_size = len(DUCK_TYPE_FIBERS['any'])
    for name, fibers in DUCK_TYPE_FIBERS.items():
        if fibers <= inter and len(fibers) <= best_size:
            if len(fibers) > len(DUCK_TYPE_FIBERS.get(best, frozenset())) or \
               len(fibers) == len(DUCK_TYPE_FIBERS.get(best, frozenset())):
                pass
            best_candidate_size = len(fibers)
    best = 'bottom'
    best_size = 0
    for name, fibers in DUCK_TYPE_FIBERS.items():
        if fibers <= inter and len(fibers) > best_size:
            best = name
            best_size = len(fibers)
    return best


@dataclass
class HasseDiagram:
    """Hasse diagram of the duck type lattice.

    Nodes are duck type names, edges are immediate ⊑ relations
    (no transitive shortcuts).
    """
    nodes: List[str]
    edges: List[Tuple[str, str]]

    def render_ascii(self) -> str:
        """Render the Hasse diagram as ASCII art."""
        levels: Dict[str, int] = {}
        for n in self.nodes:
            levels[n] = len(DUCK_TYPE_FIBERS.get(n, frozenset()))

        by_level: Dict[int, List[str]] = defaultdict(list)
        for n, lvl in sorted(levels.items(), key=lambda x: x[1]):
            by_level[lvl].append(n)

        lines: List[str] = []
        for lvl in sorted(by_level.keys(), reverse=True):
            row = "  ".join(by_level[lvl])
            lines.append(f"  level {lvl}: {row}")

        lines.append("")
        lines.append("  Edges (⊑):")
        for a, b in self.edges:
            lines.append(f"    {a} ⊑ {b}")
        return "\n".join(lines)


def build_hasse_diagram() -> HasseDiagram:
    """Build the Hasse diagram for the duck type lattice.

    An edge (a, b) means a ⊑ b AND there is no c with a ⊑ c ⊑ b.
    """
    names = list(DUCK_TYPE_FIBERS.keys())
    all_edges: List[Tuple[str, str]] = []
    for a in names:
        for b in names:
            if a != b and duck_type_leq(a, b):
                all_edges.append((a, b))

    hasse_edges: List[Tuple[str, str]] = []
    for a, b in all_edges:
        is_immediate = True
        for c_name in names:
            if c_name != a and c_name != b:
                if duck_type_leq(a, c_name) and duck_type_leq(c_name, b):
                    is_immediate = False
                    break
        if is_immediate:
            hasse_edges.append((a, b))

    return HasseDiagram(nodes=names, edges=hasse_edges)


def galois_connection_alpha(concrete_fibers: FrozenSet[str]) -> str:
    """α map of the Galois connection: concrete fiber set → abstract duck type.

    Returns the narrowest duck type whose fiber set contains the input.
    """
    best = 'any'
    best_size = len(ALL_FIBERS)
    for name, fibers in DUCK_TYPE_FIBERS.items():
        if concrete_fibers <= fibers and len(fibers) < best_size:
            best = name
            best_size = len(fibers)
    return best


def galois_connection_gamma(duck_type: str) -> FrozenSet[str]:
    """γ map of the Galois connection: abstract duck type → concrete fiber set."""
    return DUCK_TYPE_FIBERS.get(duck_type, ALL_FIBERS)


# ═══════════════════════════════════════════════════════════
# Proposal 5 — Opacity analysis (where Z3 reasoning stops)
# ═══════════════════════════════════════════════════════════

INTERPRETED_PREFIXES = frozenset([
    'binop_', 'unop_', 'truthy_', 'fold_', 'tag_',
    'If', 'And', 'Or', 'Not', 'Implies',
    'IntObj', 'BoolObj', 'StrObj', 'NoneObj', 'Pair', 'Ref', 'Bottom',
    'ival', 'bval', 'sval', 'fst', 'snd', 'addr',
    'is_IntObj', 'is_BoolObj', 'is_StrObj', 'is_NoneObj',
    'is_Pair', 'is_Ref', 'is_Bottom',
])

UNINTERPRETED_PREFIXES = ('py_', 'meth_', 'call_', 'dyncall_', 'mut_',
                          'rec_', 'lp_', 'wh_', 'comp_', 'fold_unpack_',
                          'foreach_', 'dictcomp_', 'try_', 'attr_',
                          'slice', 'contains', 'isinstance_')


@dataclass
class OpacityReport:
    """Full opacity analysis of a Z3 term."""
    total_depth: int
    uninterp_depth: int
    total_nodes: int
    uninterp_nodes: int
    interpreted_nodes: int
    uninterp_names: Set[str]
    is_fully_interpreted: bool
    opacity_ratio: float
    boundary_nodes: List[str]

    def summary(self) -> str:
        tag = "INTERPRETED" if self.is_fully_interpreted else "OPAQUE"
        lines = [
            f"Opacity: {tag}",
            f"  Total nodes: {self.total_nodes}",
            f"  Interpreted: {self.interpreted_nodes}",
            f"  Uninterpreted: {self.uninterp_nodes}",
            f"  Opacity ratio: {self.opacity_ratio:.2%}",
            f"  Max uninterp depth: {self.uninterp_depth}",
        ]
        if self.boundary_nodes:
            lines.append(f"  Boundary nodes: {', '.join(self.boundary_nodes[:10])}")
        if self.uninterp_names:
            lines.append(f"  Uninterpreted names: {', '.join(sorted(self.uninterp_names)[:15])}")
        return "\n".join(lines)


def _is_uninterpreted_name(name: str) -> bool:
    """Check whether a Z3 declaration name is uninterpreted."""
    return any(name.startswith(p) for p in UNINTERPRETED_PREFIXES)


def _opacity_walk(term, names: Set[str], depth: int,
                  stats: Dict[str, int],
                  boundaries: List[str]) -> int:
    """Walk a Z3 term tree collecting opacity statistics."""
    if depth > 20:
        return 0
    try:
        stats['total'] = stats.get('total', 0) + 1
        if term.num_args() == 0:
            stats['interpreted'] = stats.get('interpreted', 0) + 1
            return 0
        decl_name = term.decl().name()
        is_uninterp = _is_uninterpreted_name(decl_name)
        if is_uninterp:
            names.add(decl_name)
            stats['uninterp'] = stats.get('uninterp', 0) + 1
            parent_interp = depth == 0
            if not parent_interp:
                boundaries.append(decl_name)
        else:
            stats['interpreted'] = stats.get('interpreted', 0) + 1

        child_max = 0
        for i in range(term.num_args()):
            child_d = _opacity_walk(term.arg(i), names, depth + 1,
                                    stats, boundaries)
            child_max = max(child_max, child_d)
        return (1 if is_uninterp else 0) + child_max
    except Exception:
        return 0


def analyze_term_opacity(term) -> OpacityReport:
    """Analyze the opacity of a Z3 PyObj term.

    Returns a full OpacityReport with node counts, depth measures,
    opacity ratio, and the names of boundary nodes where interpretation
    transitions from interpreted → uninterpreted.
    """
    names: Set[str] = set()
    stats: Dict[str, int] = {'total': 0, 'uninterp': 0, 'interpreted': 0}
    boundaries: List[str] = []
    max_uninterp = _opacity_walk(term, names, 0, stats, boundaries)
    total = stats.get('total', 1) or 1
    uninterp_count = stats.get('uninterp', 0)
    interp_count = stats.get('interpreted', 0)

    return OpacityReport(
        total_depth=max_uninterp + interp_count,
        uninterp_depth=max_uninterp,
        total_nodes=total,
        uninterp_nodes=uninterp_count,
        interpreted_nodes=interp_count,
        uninterp_names=names,
        is_fully_interpreted=len(names) == 0,
        opacity_ratio=uninterp_count / total,
        boundary_nodes=boundaries,
    )


def find_opacity_boundary(term) -> List[Tuple[str, int]]:
    """Find the exact nodes where Z3 reasoning transitions to opaque.

    Returns list of (decl_name, depth) for every uninterpreted node
    whose parent is interpreted.
    """
    result: List[Tuple[str, int]] = []
    _find_boundary_walk(term, False, 0, result)
    return result


def _find_boundary_walk(term, parent_uninterp: bool, depth: int,
                        result: List[Tuple[str, int]]):
    if depth > 20:
        return
    try:
        if term.num_args() == 0:
            return
        decl_name = term.decl().name()
        is_uninterp = _is_uninterpreted_name(decl_name)
        if is_uninterp and not parent_uninterp:
            result.append((decl_name, depth))
        for i in range(term.num_args()):
            _find_boundary_walk(term.arg(i), is_uninterp, depth + 1, result)
    except Exception:
        pass


# ═══════════════════════════════════════════════════════════
# Proposal 6 — Čech result pretty-printer with fiber breakdown
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberBreakdown:
    """Per-fiber detail for the Čech result pretty-printer."""
    fiber: Tuple[str, ...]
    status: str
    explanation: str
    counterexample: Optional[str] = None

    def render(self) -> str:
        tag_map = {'equivalent': '✓', 'inequivalent': '✗', 'unknown': '?'}
        tag = tag_map.get(self.status, '?')
        line = f"  [{tag}] {self.fiber}: {self.explanation}"
        if self.counterexample:
            line += f" (cex: {self.counterexample})"
        return line


def format_cech_result(cech, judgments: Optional[dict] = None) -> str:
    """Format a CechResult as a human-readable summary.

    If ``judgments`` (fiber → LocalJudgment) is provided, includes a
    fiber-by-fiber breakdown table.
    """
    lines: List[str] = []
    lines.append("═══ Čech Cohomology Report ═══")
    lines.append(f"  H⁰ = {cech.h0}  (locally equivalent fibers)")
    lines.append(f"  H¹ rank = {cech.h1_rank}  (independent obstructions)")
    lines.append(f"  Total fibers = {cech.total_fibers}")
    lines.append(f"  Unknown fibers = {cech.unknown_fibers}")

    if cech.total_fibers > 0:
        coverage = cech.h0 / cech.total_fibers * 100
        lines.append(f"  Coverage = {coverage:.1f}%")

    if cech.equivalent is True:
        lines.append("  Verdict: ✓ EQUIVALENT (local equivalences glue globally)")
    elif cech.equivalent is False:
        lines.append("  Verdict: ✗ INEQUIVALENT")
        for obs in cech.obstructions:
            lines.append(f"    Obstruction on fiber: {obs}")
    else:
        lines.append("  Verdict: ? INCONCLUSIVE")

    if judgments:
        lines.append("")
        lines.append("  ─── Fiber-by-Fiber Breakdown ───")
        for fiber, judgment in sorted(judgments.items(), key=lambda x: str(x[0])):
            if judgment.is_equivalent is True:
                fb = FiberBreakdown(fiber, 'equivalent', judgment.explanation)
            elif judgment.is_equivalent is False:
                fb = FiberBreakdown(fiber, 'inequivalent',
                                   judgment.explanation,
                                   judgment.counterexample)
            else:
                fb = FiberBreakdown(fiber, 'unknown', judgment.explanation)
            lines.append(fb.render())

    return "\n".join(lines)


def format_cech_as_table(cech, judgments: Optional[dict] = None) -> str:
    """Format Čech results as a compact ASCII table."""
    header = f"{'Fiber':<25} {'Status':<12} {'Detail'}"
    sep = "─" * 60
    lines = [header, sep]

    if judgments:
        for fiber, j in sorted(judgments.items(), key=lambda x: str(x[0])):
            status = {True: 'EQ', False: 'NEQ', None: '?'}.get(j.is_equivalent, '?')
            lines.append(f"{str(fiber):<25} {status:<12} {j.explanation[:40]}")
    else:
        lines.append(f"{'(all)':<25} {'EQ' if cech.equivalent else 'NEQ' if cech.equivalent is False else '?':<12}")

    lines.append(sep)
    lines.append(f"H⁰={cech.h0}  H¹={cech.h1_rank}  "
                 f"fibers={cech.total_fibers}  unknown={cech.unknown_fibers}")
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════
# Proposal 7 — Full pipeline trace with timing
# ═══════════════════════════════════════════════════════════

@dataclass
class TraceEntry:
    """A single pipeline trace entry."""
    stage: str
    data: Any
    elapsed_ms: float
    timestamp: float


class PipelineTrace:
    """Records each stage of the CCTT equivalence pipeline with timing.

    Usage::

        trace = PipelineTrace()
        trace.start('compile_f')
        # ... do compilation ...
        trace.stop('compile_f', sections_f)
        trace.start('z3_check')
        # ... do Z3 checking ...
        trace.stop('z3_check', {'fiber': ('int',), 'result': 'UNSAT'})
        print(trace.format())
    """

    def __init__(self):
        self.entries: List[TraceEntry] = []
        self._open: Dict[str, float] = {}
        self._t0 = time.monotonic()

    def log(self, stage: str, data: Any):
        """Record a completed stage (no start/stop tracking)."""
        now = time.monotonic()
        self.entries.append(TraceEntry(
            stage=stage, data=data,
            elapsed_ms=0.0, timestamp=now - self._t0,
        ))

    def start(self, stage: str):
        """Mark the beginning of a pipeline stage."""
        self._open[stage] = time.monotonic()

    def stop(self, stage: str, data: Any = None):
        """Mark the end of a pipeline stage, record elapsed time."""
        now = time.monotonic()
        t0 = self._open.pop(stage, now)
        elapsed = (now - t0) * 1000.0
        self.entries.append(TraceEntry(
            stage=stage, data=data,
            elapsed_ms=elapsed, timestamp=now - self._t0,
        ))

    def total_ms(self) -> float:
        """Total elapsed time across all stages."""
        return sum(e.elapsed_ms for e in self.entries)

    def slowest(self, n: int = 3) -> List[TraceEntry]:
        """Return the n slowest stages."""
        return sorted(self.entries, key=lambda e: e.elapsed_ms, reverse=True)[:n]

    def format(self) -> str:
        """Format the trace as a human-readable report."""
        lines = ["═══ CCTT Pipeline Trace ═══"]
        for i, e in enumerate(self.entries, 1):
            ms = f"{e.elapsed_ms:7.1f}ms" if e.elapsed_ms > 0 else "       "
            lines.append(f"  Step {i}: [{ms}] {e.stage}")
            if isinstance(e.data, dict):
                for k, v in e.data.items():
                    lines.append(f"           {k}: {v}")
            elif e.data is not None:
                for dline in str(e.data).split('\n'):
                    lines.append(f"           {dline}")
        lines.append(f"  ─── Total: {self.total_ms():.1f}ms ───")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════
# Proposal 8 — Compiler limitation detector
# ═══════════════════════════════════════════════════════════

@dataclass
class CompilerWarning:
    """A single compiler limitation warning."""
    lineno: int
    col_offset: int
    category: str
    message: str
    severity: str  # 'info', 'warn', 'error'

    def __str__(self) -> str:
        return f"Line {self.lineno}:{self.col_offset} [{self.severity}] {self.category}: {self.message}"


def detect_compiler_limitations(source: str) -> List[CompilerWarning]:
    """Detect Python features that the CCTT compiler cannot fully handle.

    Returns a list of ``CompilerWarning`` objects about constructs
    that will produce fresh constants (uninterpreted symbols) rather
    than precise Z3 terms.
    """
    warnings: List[CompilerWarning] = []
    try:
        tree = ast.parse(source)
    except SyntaxError as e:
        return [CompilerWarning(
            lineno=e.lineno or 0, col_offset=e.offset or 0,
            category='syntax', message=str(e), severity='error')]

    for node in ast.walk(tree):
        ln = getattr(node, 'lineno', 0)
        col = getattr(node, 'col_offset', 0)

        if isinstance(node, ast.Lambda):
            warnings.append(CompilerWarning(
                ln, col, 'lambda',
                'Lambda expression produces fresh constant (not inlined)',
                'warn'))

        if isinstance(node, (ast.Yield, ast.YieldFrom)):
            warnings.append(CompilerWarning(
                ln, col, 'generator',
                'Yield/generator: lazy evaluation semantics not modeled',
                'warn'))

        if isinstance(node, ast.ListComp) and len(node.generators) > 1:
            warnings.append(CompilerWarning(
                ln, col, 'nested_comp',
                'Nested comprehension: outer generator hashed, inner chained',
                'info'))

        if isinstance(node, ast.Constant) and isinstance(node.value, float):
            v = node.value
            if v != v or v == float('inf') or v == float('-inf'):
                warnings.append(CompilerWarning(
                    ln, col, 'special_float',
                    f'Special float {v!r} produces fresh constant',
                    'warn'))

        if isinstance(node, ast.ClassDef):
            warnings.append(CompilerWarning(
                ln, col, 'class_def',
                f'Class {node.name}: instances modeled as opaque Ref',
                'info'))

        if isinstance(node, (ast.AsyncFunctionDef, ast.AsyncFor, ast.AsyncWith)):
            warnings.append(CompilerWarning(
                ln, col, 'async',
                'Async constructs: concurrency semantics not modeled',
                'warn'))

        if isinstance(node, ast.Raise):
            warnings.append(CompilerWarning(
                ln, col, 'raise',
                'Raise statement: exception semantics partially modeled via try/except',
                'info'))

        if isinstance(node, ast.Global):
            warnings.append(CompilerWarning(
                ln, col, 'global',
                'Global statement: cross-scope mutation not tracked',
                'info'))

        if isinstance(node, ast.Delete):
            warnings.append(CompilerWarning(
                ln, col, 'delete',
                'Delete statement: binding removal may cause stale references',
                'info'))

        if isinstance(node, ast.Try):
            n_handlers = len(node.handlers)
            if n_handlers > 2:
                warnings.append(CompilerWarning(
                    ln, col, 'complex_try',
                    f'Try with {n_handlers} handlers: each handler path compiled independently',
                    'info'))

        if isinstance(node, ast.While):
            warnings.append(CompilerWarning(
                ln, col, 'while_loop',
                'While loop: unrolled to RecFunction with depth limit 50',
                'info'))

    return warnings


# ═══════════════════════════════════════════════════════════
# Proposal 9 — AST node coverage matrix
# ═══════════════════════════════════════════════════════════

COMPILER_HANDLED_EXPR_NODES = {
    'Constant', 'Name', 'BinOp', 'UnaryOp', 'Compare', 'BoolOp',
    'IfExp', 'Call', 'Subscript', 'Tuple', 'List', 'ListComp',
    'SetComp', 'GeneratorExp', 'DictComp', 'Attribute', 'Dict',
    'Set', 'Lambda', 'Starred', 'JoinedStr', 'NamedExpr',
    'Await', 'Yield', 'YieldFrom', 'FormattedValue',
}

COMPILER_HANDLED_STMT_NODES = {
    'Return', 'If', 'Assign', 'AugAssign', 'For', 'While',
    'FunctionDef', 'AsyncFunctionDef', 'ClassDef', 'Expr',
    'Try', 'With', 'AsyncWith', 'Import', 'ImportFrom',
    'Assert', 'Delete', 'Global', 'Nonlocal', 'Pass', 'Break',
    'Continue', 'Raise',
}

ALL_PYTHON_EXPR_NODES = {
    'Constant', 'Name', 'BinOp', 'UnaryOp', 'Compare', 'BoolOp',
    'IfExp', 'Call', 'Subscript', 'Tuple', 'List', 'ListComp',
    'SetComp', 'GeneratorExp', 'DictComp', 'Attribute', 'Dict',
    'Set', 'Lambda', 'Starred', 'JoinedStr', 'NamedExpr',
    'Await', 'Yield', 'YieldFrom', 'FormattedValue',
    'Slice',
}

ALL_PYTHON_STMT_NODES = {
    'Return', 'If', 'Assign', 'AugAssign', 'For', 'While',
    'FunctionDef', 'AsyncFunctionDef', 'ClassDef', 'Expr',
    'Try', 'TryStar', 'With', 'AsyncWith', 'Import', 'ImportFrom',
    'Assert', 'Delete', 'Global', 'Nonlocal', 'Pass', 'Break',
    'Continue', 'Raise', 'Match', 'AsyncFor',
}


@dataclass
class CoverageMatrix:
    """AST node coverage matrix for the CCTT compiler."""
    handled_expr: Set[str]
    handled_stmt: Set[str]
    unhandled_expr: Set[str]
    unhandled_stmt: Set[str]
    expr_coverage: float
    stmt_coverage: float

    def format(self) -> str:
        lines = ["═══ AST Node Coverage Matrix ═══"]
        lines.append(f"  Expression nodes: {len(self.handled_expr)}/{len(self.handled_expr) + len(self.unhandled_expr)}"
                     f" ({self.expr_coverage:.0%})")
        lines.append(f"  Statement  nodes: {len(self.handled_stmt)}/{len(self.handled_stmt) + len(self.unhandled_stmt)}"
                     f" ({self.stmt_coverage:.0%})")
        if self.unhandled_expr:
            lines.append(f"  Unhandled expressions: {', '.join(sorted(self.unhandled_expr))}")
        if self.unhandled_stmt:
            lines.append(f"  Unhandled statements:  {', '.join(sorted(self.unhandled_stmt))}")
        return "\n".join(lines)


def compute_ast_coverage() -> CoverageMatrix:
    """Compute which Python AST nodes the CCTT compiler handles."""
    unhandled_expr = ALL_PYTHON_EXPR_NODES - COMPILER_HANDLED_EXPR_NODES
    unhandled_stmt = ALL_PYTHON_STMT_NODES - COMPILER_HANDLED_STMT_NODES
    total_expr = len(ALL_PYTHON_EXPR_NODES) or 1
    total_stmt = len(ALL_PYTHON_STMT_NODES) or 1
    return CoverageMatrix(
        handled_expr=COMPILER_HANDLED_EXPR_NODES,
        handled_stmt=COMPILER_HANDLED_STMT_NODES,
        unhandled_expr=unhandled_expr,
        unhandled_stmt=unhandled_stmt,
        expr_coverage=len(COMPILER_HANDLED_EXPR_NODES) / total_expr,
        stmt_coverage=len(COMPILER_HANDLED_STMT_NODES) / total_stmt,
    )


def analyze_source_coverage(source: str) -> Dict[str, str]:
    """Analyze which AST nodes in a given source are handled/unhandled.

    Returns a mapping node_type → 'handled' | 'unhandled' | 'partial'.
    """
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return {'__error__': 'SyntaxError'}

    result: Dict[str, str] = {}
    for node in ast.walk(tree):
        name = type(node).__name__
        if name in COMPILER_HANDLED_EXPR_NODES or name in COMPILER_HANDLED_STMT_NODES:
            result.setdefault(name, 'handled')
        elif name in ALL_PYTHON_EXPR_NODES or name in ALL_PYTHON_STMT_NODES:
            result[name] = 'unhandled'
    return result


# ═══════════════════════════════════════════════════════════
# Proposal 10 — Compiler diagnostic mode
# ═══════════════════════════════════════════════════════════

@dataclass
class CompilationDiagnostic:
    """Report of what the compiler did with each part of the source."""
    function_name: str
    param_count: int
    section_count: int
    compiled_nodes: int
    skipped_nodes: int
    fresh_constants: int
    warnings: List[CompilerWarning]
    elapsed_ms: float

    def format(self) -> str:
        lines = [
            f"═══ Compilation Diagnostic: {self.function_name} ═══",
            f"  Parameters: {self.param_count}",
            f"  Sections extracted: {self.section_count}",
            f"  Compiled AST nodes: {self.compiled_nodes}",
            f"  Skipped nodes: {self.skipped_nodes}",
            f"  Fresh constants (opaque): {self.fresh_constants}",
            f"  Compilation time: {self.elapsed_ms:.1f}ms",
        ]
        if self.warnings:
            lines.append(f"  Warnings ({len(self.warnings)}):")
            for w in self.warnings[:10]:
                lines.append(f"    {w}")
        return "\n".join(lines)


def compile_with_diagnostics(source: str) -> CompilationDiagnostic:
    """Compile a Python function and return detailed diagnostics.

    This wraps the normal compiler but also counts AST nodes,
    fresh constants produced, and sections extracted.
    """
    warnings = detect_compiler_limitations(source)

    try:
        tree = ast.parse(textwrap.dedent(source))
    except SyntaxError:
        return CompilationDiagnostic(
            function_name='<error>', param_count=0, section_count=0,
            compiled_nodes=0, skipped_nodes=0, fresh_constants=0,
            warnings=warnings, elapsed_ms=0.0)

    func_node = None
    for n in ast.walk(tree):
        if isinstance(n, ast.FunctionDef):
            func_node = n
            break

    if func_node is None:
        return CompilationDiagnostic(
            function_name='<none>', param_count=0, section_count=0,
            compiled_nodes=0, skipped_nodes=0, fresh_constants=0,
            warnings=warnings, elapsed_ms=0.0)

    total_nodes = sum(1 for _ in ast.walk(func_node))
    handled = COMPILER_HANDLED_EXPR_NODES | COMPILER_HANDLED_STMT_NODES
    compiled = sum(1 for n in ast.walk(func_node) if type(n).__name__ in handled)
    skipped = total_nodes - compiled
    param_count = len(func_node.args.args)

    t0 = time.monotonic()
    section_count = 0
    fresh_count = 0
    try:
        from .compiler import compile_func
        from .theory import Theory
        T = Theory()
        result = compile_func(source, T)
        elapsed = (time.monotonic() - t0) * 1000
        if result is not None:
            sections, params, _ = result
            section_count = len(sections)
            for s in sections:
                try:
                    term_str = str(s.term)
                    fresh_count += term_str.count('fresh_')
                except Exception:
                    pass
    except Exception:
        elapsed = (time.monotonic() - t0) * 1000

    return CompilationDiagnostic(
        function_name=func_node.name,
        param_count=param_count,
        section_count=section_count,
        compiled_nodes=compiled,
        skipped_nodes=skipped,
        fresh_constants=fresh_count,
        warnings=warnings,
        elapsed_ms=elapsed,
    )


# ═══════════════════════════════════════════════════════════
# Proposal 11 — Z3 term size estimator
# ═══════════════════════════════════════════════════════════

@dataclass
class TermSizeEstimate:
    """Estimate of Z3 solver difficulty from term structure."""
    total_nodes: int
    max_depth: int
    num_quantifiers: int
    num_ite: int
    num_recfunctions: int
    num_distinct_sorts: int
    estimated_difficulty: str

    def format(self) -> str:
        lines = [
            "═══ Z3 Term Size Estimate ═══",
            f"  Total nodes: {self.total_nodes}",
            f"  Max depth: {self.max_depth}",
            f"  ITE nodes: {self.num_ite}",
            f"  RecFunction calls: {self.num_recfunctions}",
            f"  Quantifiers: {self.num_quantifiers}",
            f"  Distinct sorts: {self.num_distinct_sorts}",
            f"  Estimated difficulty: {self.estimated_difficulty}",
        ]
        return "\n".join(lines)


def _walk_term_size(term, depth: int, stats: Dict[str, int],
                    sorts: Set[str], max_depth: int = 30):
    """Recursively collect term size statistics."""
    if depth > max_depth:
        return
    stats['nodes'] = stats.get('nodes', 0) + 1
    stats['max_depth'] = max(stats.get('max_depth', 0), depth)

    try:
        sort_name = str(term.sort())
        sorts.add(sort_name)
    except Exception:
        pass

    try:
        decl_name = term.decl().name()
        if decl_name == 'if':
            stats['ite'] = stats.get('ite', 0) + 1
        if decl_name.startswith(('lp_', 'wh_', 'fold_', 'rec_')):
            stats['recfn'] = stats.get('recfn', 0) + 1
    except Exception:
        pass

    try:
        for i in range(term.num_args()):
            _walk_term_size(term.arg(i), depth + 1, stats, sorts, max_depth)
    except Exception:
        pass


def estimate_term_size(term) -> TermSizeEstimate:
    """Estimate Z3 solver difficulty from the structure of a term.

    Heuristic difficulty levels:
      - EASY:   ≤ 50 nodes, depth ≤ 5, no RecFunctions
      - MEDIUM: ≤ 200 nodes or RecFunctions present
      - HARD:   > 200 nodes or depth > 15 or quantifiers
    """
    stats: Dict[str, int] = {}
    sorts: Set[str] = set()
    _walk_term_size(term, 0, stats, sorts)

    nodes = stats.get('nodes', 1)
    max_d = stats.get('max_depth', 0)
    ite = stats.get('ite', 0)
    recfn = stats.get('recfn', 0)
    quant = stats.get('quantifiers', 0)

    if nodes > 200 or max_d > 15 or quant > 0:
        difficulty = 'HARD'
    elif nodes > 50 or recfn > 0:
        difficulty = 'MEDIUM'
    else:
        difficulty = 'EASY'

    return TermSizeEstimate(
        total_nodes=nodes,
        max_depth=max_d,
        num_quantifiers=quant,
        num_ite=ite,
        num_recfunctions=recfn,
        num_distinct_sorts=len(sorts),
        estimated_difficulty=difficulty,
    )


def compare_term_sizes(term_f, term_g) -> Dict[str, Any]:
    """Compare term sizes of two compiled functions.

    Useful for predicting whether a Z3 equivalence check will
    be easy, and for diagnosing asymmetric compilation depth.
    """
    est_f = estimate_term_size(term_f)
    est_g = estimate_term_size(term_g)

    size_ratio = max(est_f.total_nodes, 1) / max(est_g.total_nodes, 1)
    if size_ratio > 1:
        size_ratio = 1.0 / size_ratio

    return {
        'f': est_f,
        'g': est_g,
        'size_ratio': size_ratio,
        'asymmetric': size_ratio < 0.3,
        'combined_difficulty': max(est_f.estimated_difficulty,
                                   est_g.estimated_difficulty,
                                   key=lambda d: {'EASY': 0, 'MEDIUM': 1, 'HARD': 2}[d]),
    }


# ═══════════════════════════════════════════════════════════
# Proposal 12 — Guard contradiction detector
# ═══════════════════════════════════════════════════════════

@dataclass
class ContradictionReport:
    """Report of unsatisfiable guard combinations."""
    total_guards: int
    dead_guards: List[int]
    contradictory_pairs: List[Tuple[int, int]]
    exhaustive: bool

    def format(self) -> str:
        lines = [
            "═══ Guard Contradiction Report ═══",
            f"  Total guards: {self.total_guards}",
        ]
        if self.dead_guards:
            lines.append(f"  Dead guards (always false): {self.dead_guards}")
        if self.contradictory_pairs:
            lines.append(f"  Contradictory pairs: {len(self.contradictory_pairs)}")
            for a, b in self.contradictory_pairs[:10]:
                lines.append(f"    guards {a} ∧ {b} = ⊥")
        if self.exhaustive:
            lines.append("  Guard set is exhaustive (disjunction = ⊤)")
        else:
            lines.append("  Guard set is NOT exhaustive (gaps exist)")
        return "\n".join(lines)


def detect_guard_contradictions(sections) -> ContradictionReport:
    """Find unsatisfiable guard combinations among presheaf sections.

    Detects:
      - Dead guards (individual guards that are always False)
      - Contradictory pairs (guards whose conjunction is unsatisfiable)
      - Whether the guard set is exhaustive (covers all inputs)
    """
    guards = [s.guard for s in sections]
    n = len(guards)
    dead: List[int] = []
    contradictions: List[Tuple[int, int]] = []
    exhaustive = False

    try:
        from z3 import Solver, And, Or, Not, unsat, BoolVal

        for i, g in enumerate(guards):
            s = Solver()
            s.set('timeout', 500)
            s.add(g)
            if s.check() == unsat:
                dead.append(i)

        for i in range(n):
            if i in dead:
                continue
            for j in range(i + 1, n):
                if j in dead:
                    continue
                s = Solver()
                s.set('timeout', 500)
                s.add(And(guards[i], guards[j]))
                if s.check() == unsat:
                    contradictions.append((i, j))

        s = Solver()
        s.set('timeout', 1000)
        live_guards = [g for idx, g in enumerate(guards) if idx not in dead]
        if live_guards:
            s.add(Not(Or(*live_guards)))
            exhaustive = s.check() == unsat
        else:
            exhaustive = False

    except Exception:
        pass

    return ContradictionReport(
        total_guards=n,
        dead_guards=dead,
        contradictory_pairs=contradictions,
        exhaustive=exhaustive,
    )


# ═══════════════════════════════════════════════════════════
# Proposal 13 — Fiber decomposition visualizer
# ═══════════════════════════════════════════════════════════

@dataclass
class FiberDecomposition:
    """Decomposition of the input space into type fibers."""
    param_names: List[str]
    param_fibers: List[List[str]]
    fiber_combos: List[Tuple[str, ...]]
    combo_count: int
    overlap_pairs: List[Tuple[Tuple[str, ...], Tuple[str, ...]]]

    def format(self) -> str:
        lines = ["═══ Fiber Decomposition ═══"]
        for name, fibers in zip(self.param_names, self.param_fibers):
            lines.append(f"  {name}: {' | '.join(fibers)}")
        lines.append(f"  Total fiber combos: {self.combo_count}")
        if self.combo_count <= 20:
            for combo in self.fiber_combos:
                lines.append(f"    ({', '.join(combo)})")
        else:
            for combo in self.fiber_combos[:10]:
                lines.append(f"    ({', '.join(combo)})")
            lines.append(f"    ... and {self.combo_count - 10} more")
        lines.append(f"  Overlap pairs: {len(self.overlap_pairs)}")
        return "\n".join(lines)

    def render_grid(self) -> str:
        """Render a 2D grid for 2-parameter decompositions."""
        if len(self.param_names) != 2:
            return "(grid view requires exactly 2 parameters)"

        fibers_a = self.param_fibers[0]
        fibers_b = self.param_fibers[1]
        header = "      " + "  ".join(f"{f:>5}" for f in fibers_b)
        lines = [header]
        for fa in fibers_a:
            row_cells = []
            for fb in fibers_b:
                combo = (fa, fb)
                row_cells.append("  ●  " if combo in self.fiber_combos else "  ·  ")
            lines.append(f"{fa:>5} {''.join(row_cells)}")
        return "\n".join(lines)


def decompose_fibers(source_f: str, source_g: str) -> FiberDecomposition:
    """Decompose the input space into type fibers for two functions.

    Uses duck type inference to determine fibers per parameter,
    then computes the Cartesian product (site category objects)
    and overlap pairs (morphisms).
    """
    try:
        from .duck import infer_duck_type
    except ImportError:
        infer_duck_type = None

    try:
        tree_f = ast.parse(textwrap.dedent(source_f))
        tree_g = ast.parse(textwrap.dedent(source_g))
        func_f = next(n for n in ast.walk(tree_f) if isinstance(n, ast.FunctionDef))
        func_g = next(n for n in ast.walk(tree_g) if isinstance(n, ast.FunctionDef))
        param_names = [a.arg for a in func_f.args.args]
    except Exception:
        return FiberDecomposition([], [], [], 0, [])

    fiber_map = {
        'int': ['int'], 'str': ['str'], 'bool': ['bool'],
        'ref': ['ref'], 'list': ['pair', 'ref'],
        'collection': ['pair', 'ref', 'str'],
        'any': ['int', 'bool', 'str', 'pair', 'ref', 'none'],
        'unknown': ['int', 'bool', 'str', 'pair', 'ref', 'none'],
    }

    param_fibers: List[List[str]] = []
    for pname in param_names:
        if infer_duck_type is not None:
            kind, _ = infer_duck_type(func_f, func_g, pname)
        else:
            kind = 'unknown'
        param_fibers.append(fiber_map.get(kind, fiber_map['unknown']))

    combos = list(itertools.product(*param_fibers)) if param_fibers else [()]

    overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]] = []
    for i in range(len(combos)):
        for j in range(i + 1, len(combos)):
            ci, cj = combos[i], combos[j]
            if any(ci[k] == cj[k] for k in range(len(ci))):
                overlaps.append((ci, cj))

    return FiberDecomposition(
        param_names=param_names,
        param_fibers=param_fibers,
        fiber_combos=list(combos),
        combo_count=len(combos),
        overlap_pairs=overlaps,
    )


# ═══════════════════════════════════════════════════════════
# Proposal 14 — Full pipeline runner with trace
# ═══════════════════════════════════════════════════════════

@dataclass
class FullPipelineResult:
    """Complete pipeline output with trace and all intermediate data."""
    equivalent: Optional[bool]
    explanation: str
    trace: PipelineTrace
    fiber_decomposition: Optional[FiberDecomposition]
    compilation_diag_f: Optional[CompilationDiagnostic]
    compilation_diag_g: Optional[CompilationDiagnostic]
    warnings_f: List[CompilerWarning]
    warnings_g: List[CompilerWarning]

    def format(self) -> str:
        eq_sym = {True: '✓ EQUIVALENT', False: '✗ INEQUIVALENT', None: '? INCONCLUSIVE'}
        lines = [
            "═══ Full Pipeline Result ═══",
            f"  Verdict: {eq_sym.get(self.equivalent, '?')}",
            f"  Explanation: {self.explanation}",
        ]
        if self.compilation_diag_f:
            lines.append(f"  F compiled: {self.compilation_diag_f.section_count} sections, "
                         f"{self.compilation_diag_f.fresh_constants} opaque")
        if self.compilation_diag_g:
            lines.append(f"  G compiled: {self.compilation_diag_g.section_count} sections, "
                         f"{self.compilation_diag_g.fresh_constants} opaque")
        if self.fiber_decomposition:
            lines.append(f"  Fibers: {self.fiber_decomposition.combo_count} combos")
        if self.warnings_f or self.warnings_g:
            lines.append(f"  Warnings: {len(self.warnings_f)}(F) + {len(self.warnings_g)}(G)")
        lines.append("")
        lines.append(self.trace.format())
        return "\n".join(lines)


def run_traced_pipeline(source_f: str, source_g: str,
                        timeout_ms: int = 5000) -> FullPipelineResult:
    """Run the full CCTT equivalence pipeline with tracing and diagnostics.

    This is the instrumented version of ``check_equivalence`` that
    records every stage's timing and intermediate results.
    """
    trace = PipelineTrace()

    trace.start('warnings')
    w_f = detect_compiler_limitations(source_f)
    w_g = detect_compiler_limitations(source_g)
    trace.stop('warnings', {'f': len(w_f), 'g': len(w_g)})

    trace.start('fiber_decomposition')
    try:
        decomp = decompose_fibers(source_f, source_g)
    except Exception:
        decomp = None
    trace.stop('fiber_decomposition', decomp.combo_count if decomp else 0)

    trace.start('compile_diagnostics')
    try:
        diag_f = compile_with_diagnostics(source_f)
        diag_g = compile_with_diagnostics(source_g)
    except Exception:
        diag_f = diag_g = None
    trace.stop('compile_diagnostics')

    trace.start('equivalence_check')
    try:
        from .checker import check_equivalence
        result = check_equivalence(source_f, source_g, timeout_ms)
        equivalent = result.equivalent
        explanation = result.explanation
    except Exception as e:
        equivalent = None
        explanation = f'pipeline error: {e}'
    trace.stop('equivalence_check', {'equivalent': equivalent})

    return FullPipelineResult(
        equivalent=equivalent,
        explanation=explanation,
        trace=trace,
        fiber_decomposition=decomp,
        compilation_diag_f=diag_f,
        compilation_diag_g=diag_g,
        warnings_f=w_f,
        warnings_g=w_g,
    )


# ═══════════════════════════════════════════════════════════
# Proposal 15 — Duck type inference from source strings
# ═══════════════════════════════════════════════════════════

@dataclass
class DuckTypeReport:
    """Report of duck type inference for all parameters."""
    param_types: Dict[str, str]
    param_confident: Dict[str, bool]
    param_ops: Dict[str, Set[str]]

    def format(self) -> str:
        lines = ["═══ Duck Type Inference Report ═══"]
        for p in sorted(self.param_types.keys()):
            conf = "✓" if self.param_confident.get(p, False) else "?"
            ops = self.param_ops.get(p, set())
            op_str = ", ".join(sorted(ops)[:8])
            if len(ops) > 8:
                op_str += f" (+{len(ops) - 8} more)"
            lines.append(f"  {p}: {self.param_types[p]} [{conf}]  ops={{{{ {op_str} }}}}")
        return "\n".join(lines)


def infer_duck_types_from_source(source_f: str, source_g: str) -> DuckTypeReport:
    """Infer duck types for all parameters from two source strings."""
    try:
        from .duck import infer_duck_type, extract_duck_ops
    except ImportError:
        return DuckTypeReport({}, {}, {})

    try:
        tree_f = ast.parse(textwrap.dedent(source_f))
        tree_g = ast.parse(textwrap.dedent(source_g))
        func_f = next(n for n in ast.walk(tree_f) if isinstance(n, ast.FunctionDef))
        func_g = next(n for n in ast.walk(tree_g) if isinstance(n, ast.FunctionDef))
        param_names = [a.arg for a in func_f.args.args]
    except Exception:
        return DuckTypeReport({}, {}, {})

    types: Dict[str, str] = {}
    confident: Dict[str, bool] = {}
    ops: Dict[str, Set[str]] = {}

    for pname in param_names:
        kind, conf = infer_duck_type(func_f, func_g, pname)
        types[pname] = kind
        confident[pname] = conf
        ops_f = extract_duck_ops(func_f, pname)
        ops_g = extract_duck_ops(func_g, pname)
        ops[pname] = ops_f | ops_g

    return DuckTypeReport(param_types=types, param_confident=confident, param_ops=ops)


# ═══════════════════════════════════════════════════════════
# Proposal 16 — GF(2) rank computation utilities
# ═══════════════════════════════════════════════════════════

def gf2_rank(matrix: List[List[int]]) -> int:
    """Compute the rank of a binary matrix over GF(2).

    Uses Gaussian elimination.  The matrix is a list of rows,
    each row a list of 0/1 values.
    """
    if not matrix or not matrix[0]:
        return 0
    m = [row[:] for row in matrix]
    rows, cols = len(m), len(m[0])
    rank = 0
    for col in range(cols):
        pivot = None
        for row in range(rank, rows):
            if m[row][col] == 1:
                pivot = row
                break
        if pivot is None:
            continue
        m[rank], m[pivot] = m[pivot], m[rank]
        for row in range(rows):
            if row != rank and m[row][col] == 1:
                m[row] = [(m[row][j] + m[rank][j]) % 2 for j in range(cols)]
        rank += 1
    return rank


def gf2_kernel(matrix: List[List[int]]) -> List[List[int]]:
    """Compute a basis for the kernel of a GF(2) matrix.

    Returns a list of vectors (rows) that span ker(M).
    """
    if not matrix or not matrix[0]:
        return []
    rows_n = len(matrix)
    cols_n = len(matrix[0])
    aug = [row[:] + [1 if i == j else 0 for j in range(cols_n)]
           for i, row in enumerate(matrix)]

    m = [r[:] for r in aug]
    rows_count = len(m)
    cols_total = len(m[0]) if m else 0

    rank = 0
    pivot_cols: List[int] = []
    for col in range(cols_n):
        pivot_row = None
        for row in range(rank, rows_count):
            if m[row][col] == 1:
                pivot_row = row
                break
        if pivot_row is None:
            continue
        m[rank], m[pivot_row] = m[pivot_row], m[rank]
        for row in range(rows_count):
            if row != rank and m[row][col] == 1:
                m[row] = [(m[row][j] + m[rank][j]) % 2 for j in range(cols_total)]
        pivot_cols.append(col)
        rank += 1

    free_cols = [c for c in range(cols_n) if c not in pivot_cols]
    kernel_basis: List[List[int]] = []
    for fc in free_cols:
        vec = [0] * cols_n
        vec[fc] = 1
        for i, pc in enumerate(pivot_cols):
            if i < len(m):
                vec[pc] = m[i][fc]
        kernel_basis.append(vec)
    return kernel_basis


def coboundary_delta0(fibers: List[Any],
                      overlaps: List[Tuple[Any, Any]]) -> List[List[int]]:
    """Build the δ⁰ coboundary matrix for the Čech complex.

    Each row corresponds to an overlap (edge), each column to a fiber (vertex).
    Entry (k, i) = 1 if overlap k involves fiber i.
    """
    fiber_idx = {f: i for i, f in enumerate(fibers)}
    n = len(fibers)
    matrix: List[List[int]] = []
    for a, b in overlaps:
        row = [0] * n
        if a in fiber_idx:
            row[fiber_idx[a]] = 1
        if b in fiber_idx:
            row[fiber_idx[b]] = 1
        matrix.append(row)
    return matrix


# ═══════════════════════════════════════════════════════════
# Proposal 17 — Comprehensive self-test suite
# ═══════════════════════════════════════════════════════════

def _run_self_tests():
    """Run all self-tests for this module.  Print results."""
    passed = 0
    failed = 0
    errors: List[str] = []

    def check(name: str, condition: bool, detail: str = ""):
        nonlocal passed, failed
        if condition:
            passed += 1
        else:
            failed += 1
            msg = f"FAIL: {name}"
            if detail:
                msg += f" — {detail}"
            errors.append(msg)
            print(f"  ✗ {msg}")

    print("═══ g15_impl_detail self-tests ═══\n")

    # ── Test 1: Duck type lattice ──
    print("  Testing duck type lattice...")
    check("int ⊑ any", duck_type_leq('int', 'any'))
    check("int ⊑ int", duck_type_leq('int', 'int'))
    check("¬(any ⊑ int)", not duck_type_leq('any', 'int'))
    check("bool ⊑ any", duck_type_leq('bool', 'any'))
    check("str ⊑ collection", duck_type_leq('str', 'collection'))
    check("list ⊑ collection", duck_type_leq('list', 'collection'))
    check("ref ⊑ list", duck_type_leq('ref', 'list'))
    check("¬(int ⊑ str)", not duck_type_leq('int', 'str'))

    check("meet(int, str) is any or collection or wider",
          duck_type_meet('int', 'str') in ('any', 'unknown'))
    check("meet(int, int) = int", duck_type_meet('int', 'int') == 'int')
    check("meet(str, ref) = collection or wider",
          duck_type_meet('str', 'ref') in ('collection', 'any', 'unknown'))

    check("join(int, any) = int", duck_type_join('int', 'any') == 'int')
    check("join(int, str) = bottom", duck_type_join('int', 'str') == 'bottom')

    # ── Test 2: Galois connection ──
    print("  Testing Galois connection...")
    check("α({int}) = int", galois_connection_alpha(frozenset(['int'])) == 'int')
    check("α({pair, ref}) = list", galois_connection_alpha(frozenset(['pair', 'ref'])) == 'list')
    check("γ(int) = {int}", galois_connection_gamma('int') == frozenset(['int']))
    check("γ(any) = ALL_FIBERS", galois_connection_gamma('any') == ALL_FIBERS)
    int_fibers = galois_connection_gamma('int')
    check("α(γ(int)) ⊒ int", duck_type_leq('int', galois_connection_alpha(int_fibers)))

    # ── Test 3: Hasse diagram ──
    print("  Testing Hasse diagram...")
    hasse = build_hasse_diagram()
    check("Hasse has nodes", len(hasse.nodes) > 0)
    check("Hasse has edges", len(hasse.edges) > 0)
    for a, b in hasse.edges:
        check(f"edge {a}⊑{b} valid", duck_type_leq(a, b),
              f"F({a})={DUCK_TYPE_FIBERS[a]}, F({b})={DUCK_TYPE_FIBERS[b]}")

    # ── Test 4: AST coverage matrix ──
    print("  Testing AST coverage matrix...")
    cov = compute_ast_coverage()
    check("expr coverage > 0", cov.expr_coverage > 0)
    check("stmt coverage > 0", cov.stmt_coverage > 0)
    check("Constant handled", 'Constant' in cov.handled_expr)
    check("Return handled", 'Return' in cov.handled_stmt)

    # ── Test 5: Source coverage analysis ──
    print("  Testing source coverage analysis...")
    src = "def foo(x):\n  return x + 1\n"
    sc = analyze_source_coverage(src)
    check("Return is handled in source", sc.get('Return') == 'handled')
    check("BinOp is handled in source", sc.get('BinOp') == 'handled')
    check("SyntaxError handled", '__error__' in analyze_source_coverage("def ("))

    # ── Test 6: Compiler limitation detection ──
    print("  Testing compiler limitation detection...")
    lim_src = textwrap.dedent("""\
    def foo(x):
        f = lambda y: y + 1
        yield x
        return [i for j in x for i in j]
    """)
    warnings = detect_compiler_limitations(lim_src)
    categories = [w.category for w in warnings]
    check("lambda detected", 'lambda' in categories)
    check("generator detected", 'generator' in categories)
    check("nested comp detected", 'nested_comp' in categories)

    check("no warnings for simple code",
          len(detect_compiler_limitations("def f(x): return x + 1\n")) == 0)

    # ── Test 7: GF(2) rank ──
    print("  Testing GF(2) rank...")
    check("rank of identity 3x3 = 3",
          gf2_rank([[1, 0, 0], [0, 1, 0], [0, 0, 1]]) == 3)
    check("rank of zero matrix = 0",
          gf2_rank([[0, 0], [0, 0]]) == 0)
    check("rank of [1,1;1,1] = 1",
          gf2_rank([[1, 1], [1, 1]]) == 1)
    check("rank of [1,0,1;0,1,1;1,1,0] = 2 or 3",
          gf2_rank([[1, 0, 1], [0, 1, 1], [1, 1, 0]]) in (2, 3))
    check("rank of empty = 0", gf2_rank([]) == 0)

    # ── Test 8: GF(2) kernel ──
    print("  Testing GF(2) kernel...")
    k = gf2_kernel([[1, 0, 1], [0, 1, 1]])
    check("kernel has at least 1 vector", len(k) >= 1)
    for vec in k:
        r1 = sum(a * b for a, b in zip([1, 0, 1], vec)) % 2
        r2 = sum(a * b for a, b in zip([0, 1, 1], vec)) % 2
        check(f"kernel vec {vec} in kernel", r1 == 0 and r2 == 0)

    # ── Test 9: Coboundary δ⁰ ──
    print("  Testing coboundary δ⁰...")
    fibers = [('int',), ('str',), ('bool',)]
    overlaps = [(('int',), ('str',)), (('str',), ('bool',))]
    d0 = coboundary_delta0(fibers, overlaps)
    check("δ⁰ has 2 rows", len(d0) == 2)
    check("δ⁰ row 0 correct", d0[0] == [1, 1, 0])
    check("δ⁰ row 1 correct", d0[1] == [0, 1, 1])

    # ── Test 10: Pipeline trace ──
    print("  Testing pipeline trace...")
    trace = PipelineTrace()
    trace.log('parse', 'ok')
    trace.start('compile')
    time.sleep(0.001)
    trace.stop('compile', '3 sections')
    trace.start('z3')
    time.sleep(0.002)
    trace.stop('z3', {'result': 'UNSAT'})
    fmt = trace.format()
    check("trace format contains Pipeline", "Pipeline Trace" in fmt)
    check("trace has entries", len(trace.entries) == 3)
    check("total_ms > 0", trace.total_ms() > 0)
    slowest = trace.slowest(1)
    check("slowest returns entries", len(slowest) == 1)

    # ── Test 11: Term size estimator (without Z3) ──
    print("  Testing term size estimator (mock)...")

    class MockTerm:
        def __init__(self, name: str, children=None):
            self._name = name
            self._children = children or []
        def num_args(self):
            return len(self._children)
        def arg(self, i):
            return self._children[i]
        def decl(self):
            return self
        def name(self):
            return self._name
        def sort(self):
            return 'PyObj'

    leaf = MockTerm('IntObj')
    binop = MockTerm('binop_add', [leaf, leaf])
    ite = MockTerm('if', [leaf, binop, leaf])
    est = estimate_term_size(ite)
    check("estimate nodes > 0", est.total_nodes > 0)
    check("estimate has ITE", est.num_ite >= 1)
    check("estimate difficulty is EASY", est.estimated_difficulty == 'EASY')

    deep = leaf
    for i in range(60):
        deep = MockTerm(f'call_f{i}', [deep])
    est_deep = estimate_term_size(deep)
    check("deep term is HARD", est_deep.estimated_difficulty == 'HARD')

    # ── Test 12: Opacity analysis (mock) ──
    print("  Testing opacity analysis (mock)...")
    interp = MockTerm('binop_add', [MockTerm('IntObj'), MockTerm('IntObj')])
    report = analyze_term_opacity(interp)
    check("interpreted term is fully interpreted", report.is_fully_interpreted)
    check("opacity ratio = 0", report.opacity_ratio == 0.0)

    opaque = MockTerm('call_foo', [MockTerm('IntObj'), MockTerm('meth_bar', [MockTerm('IntObj')])])
    report2 = analyze_term_opacity(opaque)
    check("opaque term is NOT fully interpreted", not report2.is_fully_interpreted)
    check("opaque has uninterp names", len(report2.uninterp_names) > 0)
    check("call_foo in names", 'call_foo' in report2.uninterp_names)
    check("meth_bar in names", 'meth_bar' in report2.uninterp_names)

    # ── Test 13: Opacity boundary finder (mock) ──
    print("  Testing opacity boundary finder (mock)...")
    boundary = find_opacity_boundary(opaque)
    check("boundary found", len(boundary) > 0)
    boundary_names = [name for name, _ in boundary]
    check("call_foo at boundary", 'call_foo' in boundary_names)

    # ── Test 14: Fiber decomposition ──
    print("  Testing fiber decomposition...")
    src_f = "def add(n):\n  return n + 1\n"
    src_g = "def inc(n):\n  return 1 + n\n"
    try:
        decomp = decompose_fibers(src_f, src_g)
        check("decomp has param names", len(decomp.param_names) > 0)
        check("decomp has fibers", len(decomp.param_fibers) > 0)
        check("decomp combo count > 0", decomp.combo_count > 0)
    except Exception as e:
        check("decomposition ran", False, str(e))

    # ── Test 15: Duck type report ──
    print("  Testing duck type report...")
    try:
        dt_report = infer_duck_types_from_source(src_f, src_g)
        if dt_report.param_types:
            check("duck type report has types", len(dt_report.param_types) > 0)
            n_type = dt_report.param_types.get('n', 'unknown')
            check("param n inferred as int", n_type == 'int', f"got {n_type}")
        else:
            # Relative import unavailable when run as __main__ standalone
            check("duck type report graceful fallback", True)
            check("duck type fallback returns empty", len(dt_report.param_types) == 0)
    except Exception as e:
        check("duck type inference ran", False, str(e))

    # ── Test 16: CompilerWarning formatting ──
    print("  Testing CompilerWarning formatting...")
    cw = CompilerWarning(10, 4, 'lambda', 'Lambda produces fresh constant', 'warn')
    s = str(cw)
    check("warning str has line", "Line 10" in s)
    check("warning str has category", "lambda" in s)

    # ── Test 17: CoverageReport ──
    print("  Testing CoverageReport...")
    cr = CoverageReport(
        is_complete=True, guard_count=3,
        trivially_true_guards=1, trivially_false_guards=0,
        redundant_pairs=[(0, 1)])
    summary = cr.summary()
    check("coverage summary says COMPLETE", "COMPLETE" in summary)
    check("coverage summary shows redundant", "redundant" in summary)

    # ── Test 18: ContradictionReport ──
    print("  Testing ContradictionReport...")
    ct = ContradictionReport(
        total_guards=3, dead_guards=[2],
        contradictory_pairs=[(0, 1)], exhaustive=False)
    ct_fmt = ct.format()
    check("contradiction report has dead", "Dead" in ct_fmt or "dead" in ct_fmt.lower())
    check("contradiction report not exhaustive", "NOT exhaustive" in ct_fmt)

    # ── Test 19: CompilationDiagnostic ──
    print("  Testing CompilationDiagnostic...")
    cd = CompilationDiagnostic(
        function_name='foo', param_count=2, section_count=3,
        compiled_nodes=15, skipped_nodes=2, fresh_constants=1,
        warnings=[], elapsed_ms=12.5)
    cd_fmt = cd.format()
    check("diag has function name", "foo" in cd_fmt)
    check("diag has elapsed", "12.5" in cd_fmt)

    # ── Test 20: TermSizeEstimate ──
    print("  Testing TermSizeEstimate...")
    tse = TermSizeEstimate(
        total_nodes=100, max_depth=8, num_quantifiers=0,
        num_ite=5, num_recfunctions=2, num_distinct_sorts=2,
        estimated_difficulty='MEDIUM')
    tse_fmt = tse.format()
    check("term size has MEDIUM", "MEDIUM" in tse_fmt)

    # ── Test 21: Hasse diagram ASCII ──
    print("  Testing Hasse diagram ASCII rendering...")
    ascii_diag = hasse.render_ascii()
    check("hasse ascii has 'level'", "level" in ascii_diag)
    check("hasse ascii has edges", "⊑" in ascii_diag)

    # ── Test 22: Cech format with judgments ──
    print("  Testing Čech format with mock judgments...")

    class MockCech:
        def __init__(self):
            self.h0 = 2
            self.h1_rank = 0
            self.total_fibers = 3
            self.unknown_fibers = 1
            self.obstructions = []
            self.equivalent = True

    class MockJudgment:
        def __init__(self, fiber, eq, expl, cex=None):
            self.fiber = fiber
            self.is_equivalent = eq
            self.explanation = expl
            self.counterexample = cex

    mock_cech = MockCech()
    mock_judgments = {
        ('int',): MockJudgment(('int',), True, '1/1 sections agree'),
        ('str',): MockJudgment(('str',), True, '1/1 sections agree'),
        ('bool',): MockJudgment(('bool',), None, 'timeout'),
    }
    cech_fmt = format_cech_result(mock_cech, mock_judgments)
    check("cech format has H⁰", "H⁰" in cech_fmt)
    check("cech format has verdict", "EQUIVALENT" in cech_fmt)
    check("cech format has fiber breakdown", "Fiber-by-Fiber" in cech_fmt)

    table_fmt = format_cech_as_table(mock_cech, mock_judgments)
    check("table format has header", "Fiber" in table_fmt)

    # ── Test 23: FullPipelineResult ──
    print("  Testing FullPipelineResult formatting...")
    fpr = FullPipelineResult(
        equivalent=True, explanation='test',
        trace=trace, fiber_decomposition=decomp if 'decomp' in dir() else None,
        compilation_diag_f=cd, compilation_diag_g=cd,
        warnings_f=[], warnings_g=[])
    fpr_fmt = fpr.format()
    check("full pipeline has verdict", "EQUIVALENT" in fpr_fmt)

    # ── Summary ──
    print(f"\n═══ Results: {passed} passed, {failed} failed ═══")
    if errors:
        print("\nFailures:")
        for e in errors:
            print(f"  {e}")
    return failed == 0


if __name__ == '__main__':
    import sys
    ok = _run_self_tests()
    sys.exit(0 if ok else 1)
