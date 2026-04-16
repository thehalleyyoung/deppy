"""Implementation details and diagnostics for the CCTT pipeline.

Proposals wired from g15_impl_detail:
  1  — Environment inline status reporter
  2  — Section coverage checker (presheaf completeness)
  3  — Section guard simplification
  5  — Opacity analysis (where Z3 reasoning stops)
  6  — Čech result pretty-printer with fiber breakdown
  7  — Full pipeline trace with timing
  10 — Compiler diagnostic mode
  11 — Z3 term size estimator
  12 — Guard contradiction detector
  13 — Fiber decomposition visualizer
  15 — Duck type inference from source strings
  16 — GF(2) rank computation utilities
"""
from __future__ import annotations

import ast
import itertools
import textwrap
import time
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple


# ═══════════════════════════════════════════════════════════
# Proposal 1 — Environment inline status reporter
# ═══════════════════════════════════════════════════════════

def env_inline_status(env) -> dict:
    """Report inlining status of the compilation environment."""
    return {
        'depth': env.depth,
        'can_inline': env.depth < 3,
        'func_defs': list(env.func_defs.keys()),
        'class_defs': list(env.class_defs.keys()),
        'imports': dict(env.imports),
        'binding_count': len(env.bindings),
    }


# ═══════════════════════════════════════════════════════════
# Proposal 2 — Section coverage checker
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
    """Check if the disjunction of section guards is tautological."""
    guards = [s.guard for s in sections]
    n = len(guards)

    trivially_true = 0
    trivially_false = 0
    redundant: List[Tuple[int, int]] = []

    try:
        from z3 import Solver, Or, Not, And, unsat, BoolVal

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
    """Simplify a Z3 Boolean guard via tactics."""
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
    """Return a new section list with simplified guards."""
    out = []
    for s in sections:
        try:
            new_guard = simplify_section_guard(s.guard)
            out.append(type(s)(guard=new_guard, term=s.term))
        except Exception:
            out.append(s)
    return out


# ═══════════════════════════════════════════════════════════
# Proposal 5 — Opacity analysis
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
    return any(name.startswith(p) for p in UNINTERPRETED_PREFIXES)


def _opacity_walk(term, names: Set[str], depth: int,
                  stats: Dict[str, int],
                  boundaries: List[str]) -> int:
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
            if depth > 0:
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
    """Analyze the opacity of a Z3 PyObj term."""
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
    """Find nodes where Z3 reasoning transitions to opaque."""
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
# Proposal 6 — Čech result pretty-printer
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
    """Format a CechResult as a human-readable summary."""
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
    """Records each stage of the CCTT equivalence pipeline with timing."""

    def __init__(self):
        self.entries: List[TraceEntry] = []
        self._open: Dict[str, float] = {}
        self._t0 = time.monotonic()

    def log(self, stage: str, data: Any):
        now = time.monotonic()
        self.entries.append(TraceEntry(
            stage=stage, data=data,
            elapsed_ms=0.0, timestamp=now - self._t0,
        ))

    def start(self, stage: str):
        self._open[stage] = time.monotonic()

    def stop(self, stage: str, data: Any = None):
        now = time.monotonic()
        t0 = self._open.pop(stage, now)
        elapsed = (now - t0) * 1000.0
        self.entries.append(TraceEntry(
            stage=stage, data=data,
            elapsed_ms=elapsed, timestamp=now - self._t0,
        ))

    def total_ms(self) -> float:
        return sum(e.elapsed_ms for e in self.entries)

    def slowest(self, n: int = 3) -> List[TraceEntry]:
        return sorted(self.entries, key=lambda e: e.elapsed_ms, reverse=True)[:n]

    def format(self) -> str:
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
    warnings: list
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
    """Compile a Python function and return detailed diagnostics."""
    from .normalizer import (
        detect_compiler_limitations, COMPILER_HANDLED_EXPR_NODES,
        COMPILER_HANDLED_STMT_NODES,
    )
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
    """Estimate Z3 solver difficulty from term structure.

    EASY: ≤50 nodes, depth ≤5, no RecFunctions.
    MEDIUM: ≤200 nodes or RecFunctions present.
    HARD: >200 nodes or depth >15 or quantifiers.
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
    """Compare term sizes of two compiled functions."""
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
    """Find unsatisfiable guard combinations among presheaf sections."""
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
    """Decompose the input space into type fibers for two functions."""
    from .duck import infer_duck_type

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
        kind, _ = infer_duck_type(func_f, func_g, pname)
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
            lines.append(f"  {p}: {self.param_types[p]} [{conf}]  ops={{ {op_str} }}")
        return "\n".join(lines)


def infer_duck_types_from_source(source_f: str, source_g: str) -> DuckTypeReport:
    """Infer duck types for all parameters from two source strings."""
    from .duck import infer_duck_type, extract_duck_ops

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
    """Compute the rank of a binary matrix over GF(2)."""
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
    """Compute a basis for the kernel of a GF(2) matrix."""
    if not matrix or not matrix[0]:
        return []
    rows_n = len(matrix)
    cols_n = len(matrix[0])
    m = [row[:] + [1 if i == j else 0 for j in range(cols_n)]
         for i, row in enumerate(matrix)]
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
    """Build the δ⁰ coboundary matrix for the Čech complex."""
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
