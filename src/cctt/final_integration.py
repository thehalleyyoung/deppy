"""Capstone integration of g17_final proposals into the CCTT pipeline.

Wires together:
  1. InstrumentedChecker — wraps check_equivalence with profiling,
     graceful-degradation tracking, and resource budgeting.
  2. OOP-aware equivalence — C3 MRO, class compilation, virtual dispatch.
  3. Difficulty-guided timeout — predict_difficulty adjusts per-pair budget.
  4. Regression-aware harness — RegressionTracker over batch runs.
  5. Parallel fiber dispatch — parallel checking with early cancellation.

All capstone code lives here; existing cctt modules are read-only.
"""
from __future__ import annotations

import ast
import contextlib
import json
import statistics
import textwrap
import threading
import time
from collections import defaultdict
from concurrent.futures import Future, ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from enum import Enum, auto
from pathlib import Path
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    Iterator,
    List,
    Optional,
    Set,
    Tuple,
    Union,
)

# ── CCTT imports (read-only) ────────────────────────────────────
from .checker import Result, check_equivalence
from .denotation import (
    OCase,
    ODict,
    OFix,
    OFold,
    OLam,
    OLit,
    OOp,
    OSeq,
    OTerm,
    OUnknown,
    OVar,
    compile_to_oterm,
)

try:
    from .cohomology import CechResult, LocalJudgment, compute_cech_h1
except Exception:  # pragma: no cover
    pass

try:
    from z3 import Context, Solver, set_param

    _HAS_Z3 = True
except ImportError:
    _HAS_Z3 = False


# ═══════════════════════════════════════════════════════════════════
# §1  OTerm Structural Utilities
# ═══════════════════════════════════════════════════════════════════


def oterm_depth(term: OTerm) -> int:
    """Maximum nesting depth of an OTerm tree."""
    if isinstance(term, (OVar, OLit, OUnknown)):
        return 0
    if isinstance(term, OOp):
        return 1 + max((oterm_depth(a) for a in term.args), default=0)
    if isinstance(term, OFold):
        return 1 + max(oterm_depth(term.init), oterm_depth(term.collection))
    if isinstance(term, OCase):
        return 1 + max(oterm_depth(term.test),
                       oterm_depth(term.true_branch),
                       oterm_depth(term.false_branch))
    if isinstance(term, OFix):
        return 1 + oterm_depth(term.body)
    if isinstance(term, OSeq):
        return 1 + max((oterm_depth(e) for e in term.elements), default=0)
    if isinstance(term, ODict):
        if not term.pairs:
            return 1
        return 1 + max(max(oterm_depth(k), oterm_depth(v))
                       for k, v in term.pairs)
    if isinstance(term, OLam):
        return 1 + oterm_depth(term.body)
    return 0


def oterm_size(term: OTerm) -> int:
    """Total number of nodes in an OTerm tree."""
    if isinstance(term, (OVar, OLit, OUnknown)):
        return 1
    if isinstance(term, OOp):
        return 1 + sum(oterm_size(a) for a in term.args)
    if isinstance(term, OFold):
        return 1 + oterm_size(term.init) + oterm_size(term.collection)
    if isinstance(term, OCase):
        return 1 + oterm_size(term.test) + oterm_size(term.true_branch) + oterm_size(term.false_branch)
    if isinstance(term, OFix):
        return 1 + oterm_size(term.body)
    if isinstance(term, OSeq):
        return 1 + sum(oterm_size(e) for e in term.elements)
    if isinstance(term, ODict):
        return 1 + sum(oterm_size(k) + oterm_size(v) for k, v in term.pairs)
    if isinstance(term, OLam):
        return 1 + oterm_size(term.body)
    return 1


def oterm_has_fix(term: OTerm) -> bool:
    """Return True if *term* contains an OFix (recursion) node."""
    if isinstance(term, OFix):
        return True
    if isinstance(term, OOp):
        return any(oterm_has_fix(a) for a in term.args)
    if isinstance(term, OFold):
        return oterm_has_fix(term.init) or oterm_has_fix(term.collection)
    if isinstance(term, OCase):
        return (oterm_has_fix(term.test) or oterm_has_fix(term.true_branch)
                or oterm_has_fix(term.false_branch))
    if isinstance(term, OSeq):
        return any(oterm_has_fix(e) for e in term.elements)
    if isinstance(term, ODict):
        return any(oterm_has_fix(k) or oterm_has_fix(v) for k, v in term.pairs)
    if isinstance(term, OLam):
        return oterm_has_fix(term.body)
    return False


def oterm_collect_ops(term: OTerm) -> set[str]:
    """Collect all operation names referenced in *term*."""
    ops: set[str] = set()
    if isinstance(term, OOp):
        ops.add(term.name)
        for a in term.args:
            ops |= oterm_collect_ops(a)
    elif isinstance(term, OFold):
        ops.add(term.op_name)
        ops |= oterm_collect_ops(term.init)
        ops |= oterm_collect_ops(term.collection)
    elif isinstance(term, OCase):
        ops |= oterm_collect_ops(term.test)
        ops |= oterm_collect_ops(term.true_branch)
        ops |= oterm_collect_ops(term.false_branch)
    elif isinstance(term, OFix):
        ops |= oterm_collect_ops(term.body)
    elif isinstance(term, OSeq):
        for e in term.elements:
            ops |= oterm_collect_ops(e)
    elif isinstance(term, ODict):
        for k, v in term.pairs:
            ops |= oterm_collect_ops(k)
            ops |= oterm_collect_ops(v)
    elif isinstance(term, OLam):
        ops |= oterm_collect_ops(term.body)
    return ops


def _count_nodes(term: OTerm, node_type: type) -> int:
    """Count occurrences of *node_type* in *term*."""
    count = 1 if isinstance(term, node_type) else 0
    if isinstance(term, OOp):
        count += sum(_count_nodes(a, node_type) for a in term.args)
    elif isinstance(term, OFold):
        count += _count_nodes(term.init, node_type) + _count_nodes(term.collection, node_type)
    elif isinstance(term, OCase):
        count += (_count_nodes(term.test, node_type)
                  + _count_nodes(term.true_branch, node_type)
                  + _count_nodes(term.false_branch, node_type))
    elif isinstance(term, OFix):
        count += _count_nodes(term.body, node_type)
    elif isinstance(term, OSeq):
        count += sum(_count_nodes(e, node_type) for e in term.elements)
    elif isinstance(term, ODict):
        for k, v in term.pairs:
            count += _count_nodes(k, node_type) + _count_nodes(v, node_type)
    elif isinstance(term, OLam):
        count += _count_nodes(term.body, node_type)
    return count


def _subst_oterm(term: OTerm, mapping: dict[str, str]) -> OTerm:
    """Substitute variable names in an OTerm tree."""
    if isinstance(term, OVar):
        return OVar(mapping.get(term.name, term.name))
    if isinstance(term, OLit):
        return term
    if isinstance(term, OOp):
        return OOp(term.name, tuple(_subst_oterm(a, mapping) for a in term.args))
    if isinstance(term, OFold):
        return OFold(term.op_name, _subst_oterm(term.init, mapping),
                     _subst_oterm(term.collection, mapping))
    if isinstance(term, OCase):
        return OCase(_subst_oterm(term.test, mapping),
                     _subst_oterm(term.true_branch, mapping),
                     _subst_oterm(term.false_branch, mapping))
    if isinstance(term, OFix):
        return OFix(term.name, _subst_oterm(term.body, mapping))
    if isinstance(term, OSeq):
        return OSeq(tuple(_subst_oterm(e, mapping) for e in term.elements))
    if isinstance(term, ODict):
        return ODict(tuple((_subst_oterm(k, mapping), _subst_oterm(v, mapping))
                           for k, v in term.pairs))
    if isinstance(term, OLam):
        inner = {k: v for k, v in mapping.items() if k not in term.params}
        return OLam(term.params, _subst_oterm(term.body, inner))
    return term


# ═══════════════════════════════════════════════════════════════════
# §2  OOP — C3 MRO, Class Compilation, Virtual Dispatch
# ═══════════════════════════════════════════════════════════════════


@dataclass
class ClassInfo:
    """Compiled representation of a Python class in the OTerm framework."""
    name: str
    bases: list[str]
    attrs: list[str]
    methods: dict[str, ast.FunctionDef]
    mro: list[str] = field(default_factory=list)


def _merge_c3(sequences: list[list[str]]) -> list[str]:
    """Core C3 merge algorithm for MRO linearisation."""
    result: list[str] = []
    while True:
        live = [s for s in sequences if s]
        if not live:
            return result
        for seq in live:
            candidate = seq[0]
            if all(candidate not in s[1:] for s in live):
                result.append(candidate)
                for s in live:
                    if s[0] == candidate:
                        s.pop(0)
                break
        else:
            remaining = [s[0] for s in live]
            raise TypeError(
                f"Cannot create a consistent MRO: conflicting classes {remaining}"
            )


def compute_c3_mro(cls_name: str, class_map: dict[str, ClassInfo]) -> list[str]:
    """Compute C3 linearisation (Python MRO) for *cls_name*."""
    if cls_name not in class_map:
        return [cls_name]
    info = class_map[cls_name]
    if not info.bases:
        return [cls_name]
    base_mros = [compute_c3_mro(b, class_map) for b in info.bases]
    base_mros.append(list(info.bases))
    return [cls_name] + _merge_c3(base_mros)


def compute_all_mros(class_map: dict[str, ClassInfo]) -> dict[str, list[str]]:
    """Compute and cache MROs for every class in *class_map*."""
    result: dict[str, list[str]] = {}
    for name in class_map:
        mro = compute_c3_mro(name, class_map)
        class_map[name].mro = mro
        result[name] = mro
    return result


def resolve_method(cls_name: str, method_name: str,
                   class_map: dict[str, ClassInfo]) -> str | None:
    """Resolve a method using the MRO path."""
    mro = compute_c3_mro(cls_name, class_map)
    for ancestor in mro:
        if ancestor in class_map and method_name in class_map[ancestor].methods:
            return ancestor
    return None


def resolve_all_methods(cls_name: str,
                        class_map: dict[str, ClassInfo]) -> dict[str, str]:
    """Return {method_name → provider_class} for all visible methods."""
    mro = compute_c3_mro(cls_name, class_map)
    seen: dict[str, str] = {}
    for ancestor in mro:
        if ancestor not in class_map:
            continue
        for mname in class_map[ancestor].methods:
            if mname not in seen:
                seen[mname] = ancestor
    return seen


def _compile_expr(node: ast.expr, params: list[str]) -> OTerm:
    """Compile a single expression AST node to an OTerm."""
    if isinstance(node, ast.Name):
        return OVar(node.id)
    if isinstance(node, ast.Constant):
        return OLit(node.value)
    if isinstance(node, ast.BinOp):
        left = _compile_expr(node.left, params)
        right = _compile_expr(node.right, params)
        op_name = type(node.op).__name__.lower()
        return OOp(op_name, (left, right))
    if isinstance(node, ast.Call):
        func_term = _compile_expr(node.func, params)
        arg_terms = tuple(_compile_expr(a, params) for a in node.args)
        if isinstance(func_term, OVar):
            return OOp(func_term.name, arg_terms)
        return OOp("call", (func_term,) + arg_terms)
    if isinstance(node, ast.IfExp):
        return OCase(_compile_expr(node.test, params),
                     _compile_expr(node.body, params),
                     _compile_expr(node.orelse, params))
    if isinstance(node, ast.Compare) and node.comparators:
        left = _compile_expr(node.left, params)
        right = _compile_expr(node.comparators[0], params)
        op_name = type(node.ops[0]).__name__.lower()
        return OOp(op_name, (left, right))
    return OUnknown(f"expr_{type(node).__name__}")


def _compile_func_body(stmts: list[ast.stmt],
                       params: list[str]) -> OTerm:
    """Compile a list of statements to an OTerm."""
    if not stmts:
        return OLit(None)
    stmt = stmts[0]
    rest = stmts[1:]
    if isinstance(stmt, ast.Return):
        if stmt.value is None:
            return OLit(None)
        return _compile_expr(stmt.value, params)
    if isinstance(stmt, ast.If):
        test = _compile_expr(stmt.test, params)
        true_br = _compile_func_body(stmt.body, params)
        false_br = _compile_func_body(stmt.orelse, params) if stmt.orelse else OLit(None)
        return OCase(test, true_br, false_br)
    if isinstance(stmt, ast.For):
        iter_expr = _compile_expr(stmt.iter, params)
        body_term = _compile_func_body(stmt.body, params)
        return OFold("for", body_term, iter_expr)
    if rest:
        return _compile_func_body(rest, params)
    return OUnknown(f"stmt_{type(stmt).__name__}")


def _method_ast_to_olam(func_def: ast.FunctionDef) -> OLam:
    """Compile a method AST to an OLam, stripping ``self``."""
    params = [a.arg for a in func_def.args.args if a.arg != "self"]
    body = _compile_func_body(func_def.body, params)
    return OLam(tuple(params), body)


def compile_class_to_oterm(cls_info: ClassInfo,
                           class_map: dict[str, ClassInfo]) -> dict[str, OLam]:
    """Compile all methods of *cls_info* to OLam terms, respecting MRO."""
    method_providers = resolve_all_methods(cls_info.name, class_map)
    compiled: dict[str, OLam] = {}
    for method_name, provider_cls in method_providers.items():
        func_def = class_map[provider_cls].methods[method_name]
        compiled[method_name] = _method_ast_to_olam(func_def)
    return compiled


def compile_class_dispatch_oterm(cls_info: ClassInfo,
                                 method_name: str,
                                 class_map: dict[str, ClassInfo]) -> OTerm:
    """Build an OCase chain for dispatching *method_name* across MRO."""
    mro = compute_c3_mro(cls_info.name, class_map)
    providers: list[tuple[str, OLam]] = []
    for ancestor in mro:
        if ancestor in class_map and method_name in class_map[ancestor].methods:
            olam = _method_ast_to_olam(class_map[ancestor].methods[method_name])
            providers.append((ancestor, olam))
    if not providers:
        return OUnknown(f"no_method_{method_name}")
    if len(providers) == 1:
        return providers[0][1]
    result: OTerm = providers[-1][1]
    for cls_name, olam in reversed(providers[:-1]):
        test = OOp("class_eq", (OVar("self"), OLit(cls_name)))
        result = OCase(test, olam, result)
    return result


def parse_classes_from_source(source: str) -> dict[str, ClassInfo]:
    """Parse Python source and extract ClassInfo for each class definition."""
    tree = ast.parse(textwrap.dedent(source))
    class_map: dict[str, ClassInfo] = {}
    for node in ast.walk(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        bases = []
        for b in node.bases:
            if isinstance(b, ast.Name):
                bases.append(b.id)
            elif isinstance(b, ast.Attribute):
                bases.append(ast.dump(b))
        attrs: list[str] = []
        methods: dict[str, ast.FunctionDef] = {}
        for item in node.body:
            if isinstance(item, ast.FunctionDef):
                methods[item.name] = item
            elif isinstance(item, ast.Assign):
                for target in item.targets:
                    if isinstance(target, ast.Name):
                        attrs.append(target.id)
            elif isinstance(item, ast.AnnAssign) and isinstance(item.target, ast.Name):
                attrs.append(item.target.id)
        class_map[node.name] = ClassInfo(
            name=node.name, bases=bases, attrs=attrs, methods=methods
        )
    return class_map


def check_class_method_equivalence(
    source_a: str, source_b: str,
    class_name: str, method_name: str,
    timeout_ms: int = 5000,
) -> Result:
    """Check equivalence of a method across two class hierarchies.

    Compiles both class hierarchies, resolves the method via MRO,
    and compares the resulting OLam terms.  Falls back to
    check_equivalence on the extracted method source.
    """
    classes_a = parse_classes_from_source(source_a)
    classes_b = parse_classes_from_source(source_b)

    if class_name not in classes_a or class_name not in classes_b:
        return Result(None, f"class {class_name} not found in both sources")

    methods_a = compile_class_to_oterm(classes_a[class_name], classes_a)
    methods_b = compile_class_to_oterm(classes_b[class_name], classes_b)

    if method_name not in methods_a or method_name not in methods_b:
        return Result(None, f"method {method_name} not found in both classes")

    olam_a = methods_a[method_name]
    olam_b = methods_b[method_name]

    if olam_a.canon() == olam_b.canon():
        return Result(True, f"OLam canonical match for {class_name}.{method_name}",
                      h0=1, confidence=0.95)

    # Fall back to the full checker on extracted method source
    provider_a = resolve_method(class_name, method_name, classes_a)
    provider_b = resolve_method(class_name, method_name, classes_b)
    if provider_a and provider_b:
        src_a = ast.unparse(classes_a[provider_a].methods[method_name])
        src_b = ast.unparse(classes_b[provider_b].methods[method_name])
        # Wrap as standalone functions
        func_a = f"def {method_name}_a({', '.join(a.arg for a in classes_a[provider_a].methods[method_name].args.args if a.arg != 'self')}):\n"
        func_a += textwrap.indent(src_a, "    ")
        func_b = f"def {method_name}_b({', '.join(a.arg for a in classes_b[provider_b].methods[method_name].args.args if a.arg != 'self')}):\n"
        func_b += textwrap.indent(src_b, "    ")
        return check_equivalence(func_a, func_b, timeout_ms)

    return Result(None, "could not extract method source for full check")


# ═══════════════════════════════════════════════════════════════════
# §3  Graceful Degradation & Pipeline Profiling
# ═══════════════════════════════════════════════════════════════════


class DegradationLevel(Enum):
    DECIDED = auto()
    UNKNOWN = auto()
    INCONCLUSIVE = auto()


class StageStatus(Enum):
    PENDING = "pending"
    RUNNING = "running"
    SUCCEEDED = "succeeded"
    FAILED = "failed"
    TIMED_OUT = "timed_out"
    SKIPPED = "skipped"


@dataclass
class StageRecord:
    """Record for a single pipeline stage execution."""
    name: str
    status: StageStatus = StageStatus.PENDING
    start_time: float = 0.0
    end_time: float = 0.0
    error_message: str | None = None
    result: Any = None

    @property
    def elapsed_ms(self) -> float:
        if self.start_time == 0.0:
            return 0.0
        end = self.end_time if self.end_time > 0 else time.monotonic()
        return (end - self.start_time) * 1000


class DegradationStateMachine:
    """Track pipeline stages through a state machine for graceful degradation."""

    STAGE_ORDER: list[str] = [
        "parse", "compile", "denotational", "z3_structural",
        "fingerprint", "duck_type", "fiber_check", "cohomology",
    ]

    def __init__(self) -> None:
        self._stages: dict[str, StageRecord] = {}
        for name in self.STAGE_ORDER:
            self._stages[name] = StageRecord(name=name)

    def begin(self, stage_name: str) -> None:
        if stage_name not in self._stages:
            self._stages[stage_name] = StageRecord(name=stage_name)
        rec = self._stages[stage_name]
        rec.status = StageStatus.RUNNING
        rec.start_time = time.monotonic()

    def succeed(self, stage_name: str, result: Any = None) -> None:
        rec = self._stages[stage_name]
        rec.status = StageStatus.SUCCEEDED
        rec.end_time = time.monotonic()
        rec.result = result

    def fail(self, stage_name: str, error: str) -> None:
        rec = self._stages[stage_name]
        rec.status = StageStatus.FAILED
        rec.end_time = time.monotonic()
        rec.error_message = error

    def timeout(self, stage_name: str) -> None:
        rec = self._stages[stage_name]
        rec.status = StageStatus.TIMED_OUT
        rec.end_time = time.monotonic()

    def skip(self, stage_name: str, reason: str = "") -> None:
        rec = self._stages[stage_name]
        rec.status = StageStatus.SKIPPED
        rec.error_message = reason

    def stage(self, stage_name: str) -> StageRecord:
        return self._stages[stage_name]

    @property
    def overall_level(self) -> DegradationLevel:
        if any(r.status == StageStatus.SUCCEEDED for r in self._stages.values()):
            return DegradationLevel.DECIDED
        if any(r.status == StageStatus.TIMED_OUT for r in self._stages.values()):
            return DegradationLevel.UNKNOWN
        return DegradationLevel.INCONCLUSIVE

    @property
    def succeeded_stages(self) -> list[str]:
        return [n for n, r in self._stages.items()
                if r.status == StageStatus.SUCCEEDED]

    @property
    def failed_stages(self) -> list[str]:
        return [n for n, r in self._stages.items()
                if r.status == StageStatus.FAILED]

    @property
    def timed_out_stages(self) -> list[str]:
        return [n for n, r in self._stages.items()
                if r.status == StageStatus.TIMED_OUT]

    def timing_report(self) -> dict[str, float]:
        return {
            name: rec.elapsed_ms
            for name, rec in self._stages.items()
            if rec.status not in (StageStatus.PENDING, StageStatus.SKIPPED)
        }

    def total_elapsed_ms(self) -> float:
        return sum(self.timing_report().values())


@dataclass
class ProfileEntry:
    """Timing data for a single profiler entry."""
    stage: str
    start: float
    end: float
    label: str = ""

    @property
    def elapsed_ms(self) -> float:
        return (self.end - self.start) * 1000


class PipelineProfiler:
    """Profile pipeline stages with timing breakdown."""

    def __init__(self) -> None:
        self._entries: list[ProfileEntry] = []
        self._active: dict[str, float] = {}
        self._global_start: float = time.monotonic()

    @contextlib.contextmanager
    def stage(self, name: str, label: str = "") -> Iterator[None]:
        t0 = time.monotonic()
        self._active[name] = t0
        try:
            yield
        finally:
            t1 = time.monotonic()
            self._entries.append(ProfileEntry(name, t0, t1, label))
            self._active.pop(name, None)

    def record(self, name: str, elapsed_ms: float, label: str = "") -> None:
        now = time.monotonic()
        self._entries.append(ProfileEntry(
            name, now - elapsed_ms / 1000, now, label
        ))

    @property
    def total_ms(self) -> float:
        return (time.monotonic() - self._global_start) * 1000

    def breakdown(self) -> dict[str, float]:
        agg: dict[str, float] = defaultdict(float)
        for e in self._entries:
            agg[e.stage] += e.elapsed_ms
        return dict(agg)

    def hotspot(self) -> str | None:
        bd = self.breakdown()
        return max(bd, key=bd.get) if bd else None

    def report(self) -> str:
        bd = self.breakdown()
        total = self.total_ms
        lines = [f"Pipeline profile: {total:.1f} ms total"]
        for stage_name, ms in sorted(bd.items(), key=lambda kv: -kv[1]):
            pct = (ms / total * 100) if total > 0 else 0
            bar = "#" * int(pct / 2)
            lines.append(f"  {stage_name:20s} {ms:8.1f} ms ({pct:5.1f}%) {bar}")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# §4  Resource Budget Management
# ═══════════════════════════════════════════════════════════════════


@dataclass
class FiberBudget:
    """Timeout budget that redistributes slack from fast fibers."""
    total_ms: float
    remaining_ms: float = 0.0
    fibers_remaining: int = 0
    _allocations: list[tuple[str, int]] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.remaining_ms = self.total_ms

    def allocate(self, n_fibers: int) -> None:
        self.fibers_remaining = n_fibers

    def next_timeout(self, fiber_name: str = "") -> int:
        if self.fibers_remaining <= 0:
            return 0
        per_fiber = self.remaining_ms / self.fibers_remaining
        timeout = max(100, int(per_fiber))
        self._allocations.append((fiber_name, timeout))
        return timeout

    def record(self, elapsed_ms: float) -> None:
        self.remaining_ms -= elapsed_ms
        self.fibers_remaining -= 1
        self.remaining_ms = max(0, self.remaining_ms)

    @property
    def utilisation(self) -> float:
        used = self.total_ms - self.remaining_ms
        return used / self.total_ms if self.total_ms > 0 else 0.0


@dataclass
class StageBudget:
    """Budget allocation for a single pipeline stage."""
    name: str
    time_ms: float
    memory_mb: int
    priority: float = 1.0


class ResourceBudgetManager:
    """Allocate time and memory budgets across pipeline stages."""

    def __init__(self, total_time_ms: float = 10000,
                 total_memory_mb: int = 768) -> None:
        self._total_time_ms = total_time_ms
        self._total_memory_mb = total_memory_mb
        self._stages: dict[str, StageBudget] = {}
        self._spent: dict[str, float] = {}

    def add_stage(self, name: str, priority: float = 1.0,
                  memory_mb: int | None = None) -> None:
        mem = memory_mb if memory_mb is not None else self._total_memory_mb
        self._stages[name] = StageBudget(
            name=name, time_ms=0.0, memory_mb=mem, priority=priority
        )

    def compute_allocations(self) -> dict[str, StageBudget]:
        total_prio = sum(s.priority for s in self._stages.values()
                         if s.name not in self._spent)
        if total_prio == 0:
            return dict(self._stages)
        remaining_time = self._total_time_ms - sum(self._spent.values())
        remaining_time = max(0, remaining_time)
        for stage in self._stages.values():
            if stage.name in self._spent:
                continue
            stage.time_ms = (stage.priority / total_prio) * remaining_time
        return dict(self._stages)

    def record_stage(self, name: str, elapsed_ms: float) -> None:
        self._spent[name] = elapsed_ms

    def budget_for(self, name: str) -> StageBudget:
        self.compute_allocations()
        return self._stages[name]

    @property
    def remaining_time_ms(self) -> float:
        return max(0, self._total_time_ms - sum(self._spent.values()))

    def summary(self) -> dict[str, Any]:
        self.compute_allocations()
        return {
            "total_time_ms": self._total_time_ms,
            "total_memory_mb": self._total_memory_mb,
            "remaining_time_ms": round(self.remaining_time_ms, 2),
            "stages": {
                name: {
                    "allocated_ms": round(s.time_ms, 2),
                    "spent_ms": round(self._spent.get(name, 0), 2),
                    "memory_mb": s.memory_mb,
                    "priority": s.priority,
                }
                for name, s in self._stages.items()
            },
        }


# ═══════════════════════════════════════════════════════════════════
# §5  Difficulty Prediction
# ═══════════════════════════════════════════════════════════════════


class DifficultyTier(Enum):
    TRIVIAL = "trivial"
    MEDIUM = "medium"
    HARD = "hard"


class ResolutionStage(Enum):
    COMPILE = "compile"
    FIBER = "fiber"
    COHOMOLOGY = "cohomology"
    AXIOM = "axiom"
    RECFUNCTION = "recfunction"


@dataclass
class DifficultyEstimate:
    """Predicted difficulty of a benchmark pair from OTerm structure."""
    pair_name: str
    predicted_tier: DifficultyTier
    predicted_stage: ResolutionStage
    score: float
    features: dict[str, float]


def _compute_structural_features(term: OTerm) -> dict[str, float]:
    return {
        "depth": float(oterm_depth(term)),
        "size": float(oterm_size(term)),
        "has_fix": 1.0 if oterm_has_fix(term) else 0.0,
        "num_ops": float(len(oterm_collect_ops(term))),
        "has_fold": 1.0 if isinstance(term, OFold) else 0.0,
        "num_cases": float(_count_nodes(term, OCase)),
    }


def predict_difficulty(term_a: OTerm, term_b: OTerm,
                       pair_name: str = "") -> DifficultyEstimate:
    """Predict difficulty tier and expected resolution stage."""
    fa = _compute_structural_features(term_a)
    fb = _compute_structural_features(term_b)

    combined: dict[str, float] = {}
    for key in fa:
        combined[f"a_{key}"] = fa[key]
        combined[f"b_{key}"] = fb[key]
    combined["depth_diff"] = abs(fa["depth"] - fb["depth"])
    combined["size_ratio"] = max(fa["size"], 1.0) / max(fb["size"], 1.0)
    combined["op_overlap"] = float(len(
        oterm_collect_ops(term_a) & oterm_collect_ops(term_b)
    ))

    score = (
        combined["a_has_fix"] * 30
        + combined["b_has_fix"] * 30
        + combined["depth_diff"] * 5
        + (1.0 if combined["size_ratio"] > 2.0 else 0.0) * 10
        + combined["a_num_cases"] * 3
        + combined["b_num_cases"] * 3
        + (combined["a_size"] + combined["b_size"]) * 0.5
    )

    if combined["a_has_fix"] or combined["b_has_fix"]:
        tier = DifficultyTier.HARD
        stage = ResolutionStage.RECFUNCTION
    elif score > 30:
        tier = DifficultyTier.MEDIUM
        stage = ResolutionStage.COHOMOLOGY
    elif combined["depth_diff"] > 3 or combined["size_ratio"] > 2.5:
        tier = DifficultyTier.MEDIUM
        stage = ResolutionStage.FIBER
    else:
        tier = DifficultyTier.TRIVIAL
        stage = ResolutionStage.COMPILE

    return DifficultyEstimate(
        pair_name=pair_name, predicted_tier=tier,
        predicted_stage=stage, score=score, features=combined,
    )


def difficulty_adjusted_timeout(base_ms: int, estimate: DifficultyEstimate) -> int:
    """Adjust timeout based on predicted difficulty."""
    multipliers = {
        DifficultyTier.TRIVIAL: 0.5,
        DifficultyTier.MEDIUM: 1.0,
        DifficultyTier.HARD: 2.0,
    }
    return max(500, int(base_ms * multipliers[estimate.predicted_tier]))


# ═══════════════════════════════════════════════════════════════════
# §6  Regression Tracker
# ═══════════════════════════════════════════════════════════════════


@dataclass
class BenchmarkRun:
    """A single run of a benchmark pair."""
    pair_id: str
    timestamp: float
    expected: bool
    got: bool | None
    time_ms: float
    explanation: str = ""
    commit_sha: str = ""

    @property
    def correct(self) -> bool:
        return self.got == self.expected

    def to_dict(self) -> dict[str, Any]:
        return {
            "pair_id": self.pair_id, "timestamp": self.timestamp,
            "expected": self.expected, "got": self.got,
            "time_ms": round(self.time_ms, 2), "correct": self.correct,
            "explanation": self.explanation, "commit_sha": self.commit_sha,
        }

    @staticmethod
    def from_dict(d: dict[str, Any]) -> BenchmarkRun:
        return BenchmarkRun(
            pair_id=d["pair_id"], timestamp=d["timestamp"],
            expected=d["expected"], got=d.get("got"),
            time_ms=d.get("time_ms", 0.0),
            explanation=d.get("explanation", ""),
            commit_sha=d.get("commit_sha", ""),
        )


class RegressionTracker:
    """Store benchmark results and detect regressions."""

    def __init__(self, history_path: str | Path | None = None) -> None:
        self._history: list[BenchmarkRun] = []
        self._history_path = Path(history_path) if history_path else None
        if self._history_path and self._history_path.exists():
            self._load()

    def _load(self) -> None:
        if self._history_path is None:
            return
        with open(self._history_path, "r") as f:
            data = json.load(f)
        self._history = [BenchmarkRun.from_dict(d) for d in data]

    def _save(self) -> None:
        if self._history_path is None:
            return
        with open(self._history_path, "w") as f:
            json.dump([r.to_dict() for r in self._history], f, indent=2)

    def record(self, run: BenchmarkRun) -> None:
        self._history.append(run)

    def record_batch(self, runs: list[BenchmarkRun]) -> None:
        self._history.extend(runs)
        self._save()

    def latest_runs(self, pair_id: str | None = None) -> list[BenchmarkRun]:
        latest: dict[str, BenchmarkRun] = {}
        for run in self._history:
            if pair_id is not None and run.pair_id != pair_id:
                continue
            if (run.pair_id not in latest
                    or run.timestamp > latest[run.pair_id].timestamp):
                latest[run.pair_id] = run
        return list(latest.values())

    def previous_runs(self, pair_id: str | None = None) -> list[BenchmarkRun]:
        by_pair: dict[str, list[BenchmarkRun]] = defaultdict(list)
        for run in self._history:
            if pair_id is not None and run.pair_id != pair_id:
                continue
            by_pair[run.pair_id].append(run)
        prev: list[BenchmarkRun] = []
        for runs in by_pair.values():
            runs_sorted = sorted(runs, key=lambda r: r.timestamp, reverse=True)
            if len(runs_sorted) >= 2:
                prev.append(runs_sorted[1])
        return prev

    def detect_regressions(self) -> list[tuple[BenchmarkRun, BenchmarkRun]]:
        prev_map: dict[str, BenchmarkRun] = {
            r.pair_id: r for r in self.previous_runs()
        }
        regressions: list[tuple[BenchmarkRun, BenchmarkRun]] = []
        for current in self.latest_runs():
            prev = prev_map.get(current.pair_id)
            if prev is not None and prev.correct and not current.correct:
                regressions.append((prev, current))
        return regressions

    def detect_improvements(self) -> list[tuple[BenchmarkRun, BenchmarkRun]]:
        prev_map: dict[str, BenchmarkRun] = {
            r.pair_id: r for r in self.previous_runs()
        }
        improvements: list[tuple[BenchmarkRun, BenchmarkRun]] = []
        for current in self.latest_runs():
            prev = prev_map.get(current.pair_id)
            if prev is not None and not prev.correct and current.correct:
                improvements.append((prev, current))
        return improvements

    def timing_stats(self, pair_id: str) -> dict[str, float]:
        times = [r.time_ms for r in self._history if r.pair_id == pair_id]
        if not times:
            return {"count": 0, "mean": 0, "median": 0, "stdev": 0, "min": 0, "max": 0}
        return {
            "count": len(times),
            "mean": statistics.mean(times),
            "median": statistics.median(times),
            "stdev": statistics.stdev(times) if len(times) > 1 else 0.0,
            "min": min(times),
            "max": max(times),
        }

    def summary(self) -> dict[str, Any]:
        latest = self.latest_runs()
        correct = sum(1 for r in latest if r.correct)
        total = len(latest)
        regressions = self.detect_regressions()
        improvements = self.detect_improvements()
        return {
            "total_pairs_tracked": total,
            "current_accuracy": round(correct / total, 4) if total else 0.0,
            "regressions": len(regressions),
            "improvements": len(improvements),
            "total_runs_recorded": len(self._history),
            "regression_pairs": [r[1].pair_id for r in regressions],
            "improvement_pairs": [r[1].pair_id for r in improvements],
        }


# ═══════════════════════════════════════════════════════════════════
# §7  Parallel Fiber Checker
# ═══════════════════════════════════════════════════════════════════


@dataclass
class FiberResult:
    """Result of checking a single fiber."""
    fiber_name: str
    equivalent: bool | None
    level: DegradationLevel
    time_ms: float = 0.0
    error: str | None = None


@dataclass
class PipelineResult:
    """Aggregated result with graceful degradation."""
    fiber_results: list[FiberResult] = field(default_factory=list)
    total_time_ms: float = 0.0

    @property
    def decided_count(self) -> int:
        return sum(1 for r in self.fiber_results
                   if r.level == DegradationLevel.DECIDED)

    @property
    def confidence(self) -> float:
        decided = [r for r in self.fiber_results
                   if r.level == DegradationLevel.DECIDED]
        if not decided:
            return 0.0
        equiv = sum(1 for r in decided if r.equivalent)
        return equiv / len(decided)

    @property
    def verdict(self) -> str:
        if any(r.equivalent is False and r.level == DegradationLevel.DECIDED
               for r in self.fiber_results):
            return "INEQUIVALENT"
        if all(r.equivalent is True for r in self.fiber_results):
            return "EQUIVALENT"
        unknown_count = sum(1 for r in self.fiber_results
                            if r.level != DegradationLevel.DECIDED)
        total = len(self.fiber_results)
        return f"PARTIAL ({total - unknown_count}/{total} fibers decided)"


@dataclass
class ParallelCheckConfig:
    max_workers: int = 4
    per_fiber_timeout_ms: int = 5000
    total_timeout_ms: int = 30000
    escalation_factor: int = 3


def check_fibers_parallel(
    fiber_checks: list[tuple[str, Callable[..., bool | None]]],
    config: ParallelCheckConfig | None = None,
) -> PipelineResult:
    """Run fiber checks in parallel with early cancellation on NEQ."""
    if config is None:
        config = ParallelCheckConfig()

    result = PipelineResult()
    deadline = time.monotonic() + config.total_timeout_ms / 1000.0
    cancel_event = threading.Event()

    def _run_one(fiber_name: str,
                 check_fn: Callable[..., bool | None]) -> FiberResult:
        if cancel_event.is_set():
            return FiberResult(fiber_name, None, DegradationLevel.UNKNOWN, 0.0)
        t0 = time.monotonic()
        remaining = max(100, int((deadline - t0) * 1000))
        timeout = min(config.per_fiber_timeout_ms, remaining)
        try:
            res = check_fn(timeout_ms=timeout)
        except Exception as e:
            elapsed = (time.monotonic() - t0) * 1000
            return FiberResult(fiber_name, None, DegradationLevel.INCONCLUSIVE,
                               elapsed, error=str(e)[:80])

        if res is None and not cancel_event.is_set():
            escalated = min(
                timeout * config.escalation_factor,
                max(100, int((deadline - time.monotonic()) * 1000)),
            )
            try:
                res = check_fn(timeout_ms=escalated)
            except Exception:
                pass

        elapsed = (time.monotonic() - t0) * 1000
        if res is None:
            return FiberResult(fiber_name, None, DegradationLevel.UNKNOWN, elapsed)
        if res is False:
            cancel_event.set()
        return FiberResult(fiber_name, res, DegradationLevel.DECIDED, elapsed)

    t_start = time.monotonic()
    with ThreadPoolExecutor(max_workers=config.max_workers) as pool:
        futures: dict[Future[FiberResult], str] = {}
        for fiber_name, check_fn in fiber_checks:
            fut = pool.submit(_run_one, fiber_name, check_fn)
            futures[fut] = fiber_name
        for fut in as_completed(futures):
            fr = fut.result()
            result.fiber_results.append(fr)

    result.total_time_ms = (time.monotonic() - t_start) * 1000
    return result


# ═══════════════════════════════════════════════════════════════════
# §8  Z3 Context Manager
# ═══════════════════════════════════════════════════════════════════


class Z3ContextManager:
    """Context manager for Z3 with auto-cleanup on exit."""

    def __init__(self, timeout_ms: int = 5000, memory_mb: int = 512) -> None:
        self._timeout_ms = timeout_ms
        self._memory_mb = memory_mb
        self._ctx: Any = None
        self._solver: Any = None
        self._entered = False

    def __enter__(self) -> Z3ContextManager:
        if not _HAS_Z3:
            raise RuntimeError("Z3 is not available")
        self._ctx = Context()
        set_param("timeout", self._timeout_ms)
        set_param("memory_max_size", self._memory_mb)
        self._entered = True
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> bool:
        self._cleanup()
        return exc_type is MemoryError

    def _cleanup(self) -> None:
        import gc
        self._solver = None
        self._ctx = None
        self._entered = False
        gc.collect()

    @property
    def ctx(self) -> Any:
        if not self._entered:
            raise RuntimeError("Z3ContextManager not entered")
        return self._ctx

    def solver(self) -> Any:
        if self._solver is None:
            self._solver = Solver(ctx=self._ctx)
            self._solver.set("timeout", self._timeout_ms)
        return self._solver

    def fresh_solver(self) -> Any:
        self._solver = Solver(ctx=self._ctx)
        self._solver.set("timeout", self._timeout_ms)
        return self._solver


# ═══════════════════════════════════════════════════════════════════
# §9  Instrumented Checker — capstone integration
# ═══════════════════════════════════════════════════════════════════


@dataclass
class InstrumentedResult:
    """check_equivalence result enriched with profiling and degradation."""
    result: Result
    profiler: PipelineProfiler
    degradation: DegradationStateMachine
    budget_summary: dict[str, Any]
    difficulty: DifficultyEstimate | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "equivalent": self.result.equivalent,
            "explanation": self.result.explanation,
            "confidence": self.result.confidence,
            "timing": self.profiler.breakdown(),
            "hotspot": self.profiler.hotspot(),
            "total_ms": round(self.profiler.total_ms, 2),
            "degradation_level": self.degradation.overall_level.name,
            "succeeded_stages": self.degradation.succeeded_stages,
            "failed_stages": self.degradation.failed_stages,
            "budget": self.budget_summary,
            "difficulty": (
                {
                    "tier": self.difficulty.predicted_tier.value,
                    "stage": self.difficulty.predicted_stage.value,
                    "score": round(self.difficulty.score, 2),
                }
                if self.difficulty else None
            ),
        }


def instrumented_check(
    source_f: str,
    source_g: str,
    timeout_ms: int = 5000,
    profile: bool = True,
) -> InstrumentedResult:
    """Run check_equivalence wrapped with profiling, budget, and degradation.

    This is the capstone: it ties the existing CCTT checker to the new
    g17_final infrastructure.
    """
    profiler = PipelineProfiler()
    sm = DegradationStateMachine()
    budget = ResourceBudgetManager(total_time_ms=float(timeout_ms))
    budget.add_stage("denotational", priority=3.0)
    budget.add_stage("z3_check", priority=5.0)
    budget.add_stage("testing", priority=2.0)
    budget.compute_allocations()

    # Difficulty prediction via OTerm compilation (optional)
    difficulty: DifficultyEstimate | None = None
    adjusted_timeout = timeout_ms
    with profiler.stage("difficulty_prediction"):
        sm.begin("compile")
        try:
            ot_f = compile_to_oterm(source_f)
            ot_g = compile_to_oterm(source_g)
            if ot_f is not None and ot_g is not None:
                term_f, _ = ot_f
                term_g, _ = ot_g
                difficulty = predict_difficulty(term_f, term_g, "inline")
                adjusted_timeout = difficulty_adjusted_timeout(timeout_ms, difficulty)
            sm.succeed("compile")
        except Exception as e:
            sm.fail("compile", str(e))

    # Run the actual checker
    with profiler.stage("check_equivalence"):
        sm.begin("fiber_check")
        try:
            result = check_equivalence(source_f, source_g, adjusted_timeout)
            if result.equivalent is not None:
                sm.succeed("fiber_check", result=result.equivalent)
            else:
                sm.timeout("fiber_check")
        except Exception as e:
            sm.fail("fiber_check", str(e))
            result = Result(None, f"instrumented error: {e}")

    budget.record_stage("z3_check", profiler.breakdown().get("check_equivalence", 0))

    return InstrumentedResult(
        result=result,
        profiler=profiler,
        degradation=sm,
        budget_summary=budget.summary(),
        difficulty=difficulty,
    )


def batch_check_with_regression(
    pairs: list[tuple[str, str, str, bool]],
    tracker: RegressionTracker | None = None,
    timeout_ms: int = 5000,
    commit_sha: str = "",
) -> tuple[list[InstrumentedResult], dict[str, Any]]:
    """Run instrumented checks on a batch of pairs and track regressions.

    Each pair is (pair_id, source_f, source_g, expected_equivalent).
    Returns (results, regression_summary).
    """
    if tracker is None:
        tracker = RegressionTracker()

    results: list[InstrumentedResult] = []
    runs: list[BenchmarkRun] = []

    for pair_id, source_f, source_g, expected in pairs:
        t0 = time.monotonic()
        ir = instrumented_check(source_f, source_g, timeout_ms)
        elapsed = (time.monotonic() - t0) * 1000
        results.append(ir)

        run = BenchmarkRun(
            pair_id=pair_id,
            timestamp=time.time(),
            expected=expected,
            got=ir.result.equivalent,
            time_ms=elapsed,
            explanation=ir.result.explanation,
            commit_sha=commit_sha,
        )
        tracker.record(run)
        runs.append(run)

    reg_summary = tracker.summary()
    return results, reg_summary


# ═══════════════════════════════════════════════════════════════════
# §10  Fiber Pruning / Ranking
# ═══════════════════════════════════════════════════════════════════


def prune_fibers(
    fibers: list[tuple[str, float]],
    epsilon: float = 0.01,
) -> list[str]:
    """Prune fibers whose confidence is below *epsilon*."""
    return [name for name, conf in fibers if conf >= epsilon]


def rank_fibers(
    fibers: list[tuple[str, float]],
) -> list[str]:
    """Rank fibers by confidence descending."""
    return [name for name, _ in sorted(fibers, key=lambda x: -x[1])]


# ═══════════════════════════════════════════════════════════════════
# §11  Benchmark Classification Catalog
# ═══════════════════════════════════════════════════════════════════


@dataclass
class PairClassification:
    pair_id: str
    description: str
    is_equivalent: bool
    stage: ResolutionStage
    tier: DifficultyTier


EQ_CLASSIFICATIONS: list[PairClassification] = [
    PairClassification("EQ-01", "Flatten nested: recursive gen vs iterative stack",
                       True, ResolutionStage.RECFUNCTION, DifficultyTier.HARD),
    PairClassification("EQ-07", "Convex hull: gift-wrap vs Graham scan",
                       True, ResolutionStage.RECFUNCTION, DifficultyTier.HARD),
    PairClassification("EQ-23", "Bracket matching: stack vs counter",
                       True, ResolutionStage.FIBER, DifficultyTier.TRIVIAL),
    PairClassification("EQ-29", "Graph inversion: comprehension vs defaultdict",
                       True, ResolutionStage.FIBER, DifficultyTier.TRIVIAL),
]

NEQ_CLASSIFICATIONS: list[PairClassification] = [
    PairClassification("NEQ-01", "Floor div vs truncation on negative",
                       False, ResolutionStage.COMPILE, DifficultyTier.TRIVIAL),
    PairClassification("NEQ-09", "NaN propagation in max()",
                       False, ResolutionStage.FIBER, DifficultyTier.MEDIUM),
    PairClassification("NEQ-22", "+= vs + on list aliases",
                       False, ResolutionStage.AXIOM, DifficultyTier.HARD),
]


def classify_benchmark_suite(
    pair_classifications: list[PairClassification],
) -> dict[str, dict[str, int]]:
    """Produce summary statistics of the benchmark by tier and stage."""
    stats: dict[str, dict[str, int]] = {
        "by_tier": {},
        "by_stage": {},
        "by_equivalence": {"equivalent": 0, "non_equivalent": 0},
    }
    for pc in pair_classifications:
        tier = pc.tier.value
        stage_val = pc.stage.value
        stats["by_tier"][tier] = stats["by_tier"].get(tier, 0) + 1
        stats["by_stage"][stage_val] = stats["by_stage"].get(stage_val, 0) + 1
        if pc.is_equivalent:
            stats["by_equivalence"]["equivalent"] += 1
        else:
            stats["by_equivalence"]["non_equivalent"] += 1
    return stats


# ═══════════════════════════════════════════════════════════════════
# Self-Tests
# ═══════════════════════════════════════════════════════════════════


def _run_self_tests() -> bool:
    """Run all self-tests, return True if all pass."""
    import sys

    counts = {"passed": 0, "failed": 0}

    def _assert(cond: bool, msg: str) -> None:
        if cond:
            counts["passed"] += 1
            print(f"  ✓ {msg}")
        else:
            counts["failed"] += 1
            print(f"  ✗ FAIL: {msg}")

    # ── C3 MRO ──────────────────────────────────────────────
    print("\n=== C3 MRO Tests ===")
    cmap: dict[str, ClassInfo] = {
        "A": ClassInfo("A", [], [], {}),
        "B": ClassInfo("B", ["A"], [], {}),
        "C": ClassInfo("C", ["A"], [], {}),
        "D": ClassInfo("D", ["B", "C"], [], {}),
    }
    mro_d = compute_c3_mro("D", cmap)
    _assert(mro_d == ["D", "B", "C", "A"], f"Diamond MRO: {mro_d}")

    mro_b = compute_c3_mro("B", cmap)
    _assert(mro_b == ["B", "A"], f"Single inheritance MRO: {mro_b}")

    mro_unknown = compute_c3_mro("Z", cmap)
    _assert(mro_unknown == ["Z"], f"Unknown class MRO: {mro_unknown}")

    all_mros = compute_all_mros(cmap)
    _assert(len(all_mros) == 4, f"compute_all_mros: {len(all_mros)} entries")

    # ── Method Resolution ────────────────────────────────────
    print("\n=== Method Resolution Tests ===")
    func_a = ast.parse("def foo(self): pass").body[0]
    func_c = ast.parse("def bar(self): pass").body[0]
    func_b = ast.parse("def foo(self): pass").body[0]

    mr_map: dict[str, ClassInfo] = {
        "Base": ClassInfo("Base", [], [], {"foo": func_a}),
        "Child": ClassInfo("Child", ["Base"], [], {"bar": func_c}),
        "Override": ClassInfo("Override", ["Base"], [], {"foo": func_b, "bar": func_c}),
    }

    res = resolve_method("Child", "foo", mr_map)
    _assert(res == "Base", f"Inherited resolves to Base: {res}")

    res2 = resolve_method("Override", "foo", mr_map)
    _assert(res2 == "Override", f"Overridden resolves to Override: {res2}")

    res3 = resolve_method("Child", "missing", mr_map)
    _assert(res3 is None, f"Missing method returns None: {res3}")

    all_m = resolve_all_methods("Child", mr_map)
    _assert(set(all_m.keys()) == {"foo", "bar"}, f"All methods: {all_m}")

    # ── Class Compilation ─────────────────────────────────────
    print("\n=== Class Compilation Tests ===")
    src = textwrap.dedent("""\
    class Animal:
        kind = "animal"
        def speak(self):
            return "..."

    class Dog(Animal):
        def speak(self):
            return "woof"

    class Cat(Animal):
        def speak(self):
            return "meow"
    """)
    parsed = parse_classes_from_source(src)
    _assert(len(parsed) == 3, f"Parsed 3 classes: {list(parsed.keys())}")
    _assert("Dog" in parsed, "Dog class found")

    dog_methods = compile_class_to_oterm(parsed["Dog"], parsed)
    _assert("speak" in dog_methods, f"Dog has speak: {list(dog_methods.keys())}")
    _assert(isinstance(dog_methods["speak"], OLam), "speak is OLam")

    dispatch_term = compile_class_dispatch_oterm(parsed["Dog"], "speak", parsed)
    _assert(isinstance(dispatch_term, (OLam, OCase)),
            f"Dispatch term type: {type(dispatch_term).__name__}")

    # ── OTerm Utilities ──────────────────────────────────────
    print("\n=== OTerm Utility Tests ===")
    t1 = OOp("add", (OVar("x"), OLit(1)))
    t2 = OFix("fib", OCase(
        OOp("lt", (OVar("n"), OLit(2))),
        OVar("n"),
        OOp("add", (
            OOp("fib", (OOp("sub", (OVar("n"), OLit(1))),)),
            OOp("fib", (OOp("sub", (OVar("n"), OLit(2))),)),
        )),
    ))

    _assert(oterm_depth(t1) == 1, f"Simple depth: {oterm_depth(t1)}")
    _assert(oterm_size(t1) == 3, f"Simple size: {oterm_size(t1)}")
    _assert(not oterm_has_fix(t1), "Simple term has no fix")
    _assert(oterm_has_fix(t2), "Fib term has fix")
    _assert("add" in oterm_collect_ops(t1), "Collects 'add' op")
    _assert(len(oterm_collect_ops(t2)) >= 3, f"Fib ops: {oterm_collect_ops(t2)}")

    subst_t = _subst_oterm(t1, {"x": "y"})
    _assert(isinstance(subst_t, OOp), "Subst preserves OOp")
    _assert(subst_t.canon() == "add($y,1)", f"Subst result: {subst_t.canon()}")

    # ── Degradation State Machine ─────────────────────────────
    print("\n=== Degradation State Machine Tests ===")
    sm = DegradationStateMachine()
    sm.begin("parse")
    sm.succeed("parse", result="ok")
    sm.begin("compile")
    sm.fail("compile", "syntax error")
    sm.begin("fiber_check")
    sm.timeout("fiber_check")
    sm.skip("cohomology", "prerequisite failed")

    _assert(sm.stage("parse").status == StageStatus.SUCCEEDED, "Parse succeeded")
    _assert(sm.stage("compile").status == StageStatus.FAILED, "Compile failed")
    _assert(sm.stage("fiber_check").status == StageStatus.TIMED_OUT, "Fiber timed out")
    _assert(sm.stage("cohomology").status == StageStatus.SKIPPED, "Cohomology skipped")
    _assert(sm.overall_level == DegradationLevel.DECIDED, "Overall = DECIDED")
    _assert("parse" in sm.succeeded_stages, "Parse in succeeded list")
    _assert("compile" in sm.failed_stages, "Compile in failed list")
    _assert("fiber_check" in sm.timed_out_stages, "Fiber in timed_out list")
    timing = sm.timing_report()
    _assert("parse" in timing, f"Timing has parse: {list(timing.keys())}")

    # ── FiberBudget ──────────────────────────────────────────
    print("\n=== Budget Tests ===")
    fb = FiberBudget(total_ms=10000)
    fb.allocate(4)
    t1_budget = fb.next_timeout("fiber_int")
    _assert(t1_budget == 2500, f"First budget: {t1_budget}")
    fb.record(500)
    t2_budget = fb.next_timeout("fiber_str")
    _assert(t2_budget >= 3000, f"Redistributed budget: {t2_budget}")
    _assert(fb.utilisation > 0, f"Utilisation: {fb.utilisation}")

    # ── Resource Budget Manager ──────────────────────────────
    print("\n=== Resource Budget Manager Tests ===")
    rbm = ResourceBudgetManager(total_time_ms=10000, total_memory_mb=768)
    rbm.add_stage("compile", priority=2.0)
    rbm.add_stage("z3_check", priority=5.0)
    rbm.add_stage("cohomology", priority=3.0)
    allocs = rbm.compute_allocations()
    _assert(allocs["z3_check"].time_ms > allocs["compile"].time_ms,
            "Z3 gets more time than compile")
    total_alloc = sum(s.time_ms for s in allocs.values())
    _assert(abs(total_alloc - 10000) < 1, f"Budget sums to total: {total_alloc}")

    # ── Pipeline Profiler ────────────────────────────────────
    print("\n=== Profiler Tests ===")
    profiler = PipelineProfiler()
    with profiler.stage("compile"):
        time.sleep(0.01)
    with profiler.stage("z3_check"):
        time.sleep(0.02)
    profiler.record("cohomology", 5.0)
    bd = profiler.breakdown()
    _assert("compile" in bd, "Breakdown has compile")
    _assert("z3_check" in bd, "Breakdown has z3_check")
    _assert(bd["z3_check"] > bd["compile"], "Z3 took longer than compile")
    _assert(profiler.hotspot() == "z3_check", f"Hotspot: {profiler.hotspot()}")
    report_str = profiler.report()
    _assert("Pipeline profile" in report_str, "Report has header")

    # ── Difficulty Predictor ─────────────────────────────────
    print("\n=== Difficulty Predictor Tests ===")
    simple_a = OOp("add", (OVar("x"), OLit(1)))
    simple_b = OOp("add", (OVar("x"), OLit(1)))
    est_trivial = predict_difficulty(simple_a, simple_b, "trivial_pair")
    _assert(est_trivial.predicted_tier == DifficultyTier.TRIVIAL,
            f"Trivial prediction: {est_trivial.predicted_tier}")

    complex_a = OFix("f", OCase(OVar("n"), OVar("n"),
                                OOp("f", (OOp("sub", (OVar("n"), OLit(1))),))))
    complex_b = OFold("add", OLit(0), OVar("xs"))
    est_hard = predict_difficulty(complex_a, complex_b, "hard_pair")
    _assert(est_hard.predicted_tier == DifficultyTier.HARD,
            f"Hard prediction: {est_hard.predicted_tier}")
    _assert(est_hard.predicted_stage == ResolutionStage.RECFUNCTION,
            f"Hard stage: {est_hard.predicted_stage}")
    _assert(est_hard.score > est_trivial.score,
            f"Hard score ({est_hard.score:.1f}) > trivial ({est_trivial.score:.1f})")

    # Difficulty-adjusted timeout
    adj = difficulty_adjusted_timeout(5000, est_hard)
    _assert(adj == 10000, f"Hard pair gets 2x: {adj}")
    adj_trivial = difficulty_adjusted_timeout(5000, est_trivial)
    _assert(adj_trivial == 2500, f"Trivial pair gets 0.5x: {adj_trivial}")

    # ── Regression Tracker ───────────────────────────────────
    print("\n=== Regression Tracker Tests ===")
    tracker = RegressionTracker()
    now = time.time()
    tracker.record(BenchmarkRun("EQ-01", now - 100, True, True, 500.0, "ok", "abc123"))
    tracker.record(BenchmarkRun("EQ-02", now - 100, True, True, 300.0, "ok", "abc123"))
    tracker.record(BenchmarkRun("EQ-01", now, True, False, 600.0, "regression", "def456"))
    tracker.record(BenchmarkRun("EQ-02", now, True, True, 250.0, "ok", "def456"))

    latest = tracker.latest_runs()
    _assert(len(latest) == 2, f"Latest runs: {len(latest)}")

    regressions = tracker.detect_regressions()
    _assert(len(regressions) == 1, f"Regressions: {len(regressions)}")
    _assert(regressions[0][1].pair_id == "EQ-01", "EQ-01 regressed")

    improvements = tracker.detect_improvements()
    _assert(len(improvements) == 0, "No improvements")

    ts = tracker.timing_stats("EQ-01")
    _assert(ts["count"] == 2, f"Timing count: {ts['count']}")
    _assert(ts["mean"] == 550.0, f"Timing mean: {ts['mean']}")

    t_summary = tracker.summary()
    _assert(t_summary["regressions"] == 1, f"Summary regressions: {t_summary['regressions']}")
    _assert(t_summary["current_accuracy"] == 0.5,
            f"Summary accuracy: {t_summary['current_accuracy']}")

    # ── Parallel Checker ─────────────────────────────────────
    print("\n=== Parallel Checker Tests ===")
    cfg = ParallelCheckConfig(max_workers=2, per_fiber_timeout_ms=1000)
    dummy_checks: list[tuple[str, Callable[..., bool | None]]] = [
        ("fiber_a", lambda timeout_ms=1000: True),
        ("fiber_b", lambda timeout_ms=1000: True),
        ("fiber_c", lambda timeout_ms=1000: False),
    ]
    par_result = check_fibers_parallel(dummy_checks, cfg)
    _assert(len(par_result.fiber_results) == 3,
            f"Parallel results: {len(par_result.fiber_results)}")
    _assert(par_result.total_time_ms > 0, f"Parallel time: {par_result.total_time_ms:.1f}")
    has_false = any(r.equivalent is False for r in par_result.fiber_results)
    _assert(has_false, "Parallel found counterexample")

    # ── Fiber Pruning / Ranking ──────────────────────────────
    print("\n=== Fiber Pruning Tests ===")
    fibers_in = [("int", 0.9), ("str", 0.005), ("bool", 0.5), ("ref", 0.001)]
    pruned = prune_fibers(fibers_in, epsilon=0.01)
    _assert(pruned == ["int", "bool"], f"Pruned: {pruned}")
    ranked = rank_fibers(fibers_in)
    _assert(ranked[0] == "int", f"Highest first: {ranked}")

    # ── Classification ───────────────────────────────────────
    print("\n=== Classification Tests ===")
    all_class = EQ_CLASSIFICATIONS + NEQ_CLASSIFICATIONS
    stats = classify_benchmark_suite(all_class)
    _assert("by_tier" in stats, "Stats has by_tier")
    _assert("by_stage" in stats, "Stats has by_stage")
    _assert(stats["by_equivalence"]["equivalent"] == len(EQ_CLASSIFICATIONS),
            f"EQ count: {stats['by_equivalence']['equivalent']}")
    _assert(stats["by_equivalence"]["non_equivalent"] == len(NEQ_CLASSIFICATIONS),
            f"NEQ count: {stats['by_equivalence']['non_equivalent']}")

    # ── Z3 Context Manager ───────────────────────────────────
    print("\n=== Z3 Context Manager Tests ===")
    if _HAS_Z3:
        with Z3ContextManager(timeout_ms=2000, memory_mb=256) as z3cm:
            s = z3cm.solver()
            _assert(s is not None, "Solver created")
            s2 = z3cm.fresh_solver()
            _assert(s2 is not None, "Fresh solver created")
            _assert(s2 is not s, "Fresh solver is different")
        _assert(True, "Z3ContextManager exited cleanly")
    else:
        _assert(True, "Z3 not available — skipping")

    # ── Instrumented Check ────────────────────────────────────
    print("\n=== Instrumented Checker Tests ===")
    ir = instrumented_check(
        "def f(x): return x + 1",
        "def g(x): return x + 1",
        timeout_ms=3000,
    )
    _assert(ir.result.equivalent is True, f"Instrumented EQ: {ir.result.equivalent}")
    _assert(ir.profiler.total_ms > 0, f"Profiler tracked time: {ir.profiler.total_ms:.1f}")
    _assert(len(ir.degradation.succeeded_stages) > 0, "Some stages succeeded")
    ir_dict = ir.to_dict()
    _assert("equivalent" in ir_dict, "to_dict has equivalent")
    _assert("timing" in ir_dict, "to_dict has timing")
    _assert("difficulty" in ir_dict, "to_dict has difficulty")

    # ── Summary ──────────────────────────────────────────────
    print(f"\n{'='*60}")
    print(f"Results: {counts['passed']} passed, {counts['failed']} failed")
    if counts["failed"]:
        print("SOME TESTS FAILED")
        return False
    else:
        print("ALL TESTS PASSED")
        return True


if __name__ == "__main__":
    import sys
    ok = _run_self_tests()
    sys.exit(0 if ok else 1)
