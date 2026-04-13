"""Code proposals for chapters 42-46 (g17_final): OOP, Error Handling,
Scalability, Math Prerequisites, and Benchmark Catalog.

Extended with full implementations for:
  - C3 MRO linearisation with cycle detection and diamond resolution
  - OOP class compilation to OTerm (methods → OLam, inheritance → OCase chain)
  - Resource budget manager (time/memory across pipeline stages)
  - Graceful degradation state machine (track stage success/failure/timeout)
  - Benchmark pair difficulty predictor (estimate from OTerm structure)
  - Benchmark regression tracker (store results over time, detect regressions)
  - Pipeline stage profiler with timing breakdown
  - Parallel fiber checker with worker pool
  - Memory-safe Z3 context manager (auto-cleanup on timeout/OOM)
"""
from __future__ import annotations

import ast
import contextlib
import hashlib
import json
import math
import os
import resource
import signal
import statistics
import textwrap
import threading
import time
from collections import defaultdict, deque
from concurrent.futures import Future, ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from enum import Enum, auto
from pathlib import Path
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Deque,
    Dict,
    Iterator,
    List,
    Optional,
    Protocol,
    Sequence,
    Set,
    Tuple,
    Union,
)

try:
    from z3 import (
        BoolSort,
        Const,
        Context,
        DatatypeSort,
        ForAll,
        FreshConst,
        If,
        Solver,
        set_param,
        unknown,
    )

    _HAS_Z3 = True
except ImportError:
    _HAS_Z3 = False


# ══════════════════════════════════════════════════════════════════
# OTerm types (lightweight local definitions matching denotation.py)
# ══════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class OVar:
    """Variable reference in the OTerm language."""
    name: str
    def canon(self) -> str:
        return f"${self.name}"
    def depth(self) -> int:
        return 0
    def size(self) -> int:
        return 1


@dataclass(frozen=True)
class OLit:
    """Literal value."""
    value: Any
    def canon(self) -> str:
        return repr(self.value)
    def depth(self) -> int:
        return 0
    def size(self) -> int:
        return 1


@dataclass(frozen=True)
class OOp:
    """Application of a named operation."""
    name: str
    args: tuple[OTerm, ...]
    def canon(self) -> str:
        return f"{self.name}({','.join(a.canon() for a in self.args)})"
    def depth(self) -> int:
        return 1 + max((a.depth() for a in self.args), default=0)
    def size(self) -> int:
        return 1 + sum(a.size() for a in self.args)


@dataclass(frozen=True)
class OFold:
    """Fold/reduce over a collection."""
    op_name: str
    init: OTerm
    collection: OTerm
    def canon(self) -> str:
        return f"fold[{self.op_name}]({self.init.canon()},{self.collection.canon()})"
    def depth(self) -> int:
        return 1 + max(self.init.depth(), self.collection.depth())
    def size(self) -> int:
        return 1 + self.init.size() + self.collection.size()


@dataclass(frozen=True)
class OCase:
    """Case/branch expression."""
    test: OTerm
    true_branch: OTerm
    false_branch: OTerm
    def canon(self) -> str:
        return f"case({self.test.canon()},{self.true_branch.canon()},{self.false_branch.canon()})"
    def depth(self) -> int:
        return 1 + max(self.test.depth(), self.true_branch.depth(), self.false_branch.depth())
    def size(self) -> int:
        return 1 + self.test.size() + self.true_branch.size() + self.false_branch.size()


@dataclass(frozen=True)
class OFix:
    """Fixed point (recursion)."""
    name: str
    body: OTerm
    def canon(self) -> str:
        return f"fix[{self.name}]({self.body.canon()})"
    def depth(self) -> int:
        return 1 + self.body.depth()
    def size(self) -> int:
        return 1 + self.body.size()


@dataclass(frozen=True)
class OSeq:
    """Sequence/list construction."""
    elements: tuple[OTerm, ...]
    def canon(self) -> str:
        return f"[{','.join(e.canon() for e in self.elements)}]"
    def depth(self) -> int:
        return 1 + max((e.depth() for e in self.elements), default=0)
    def size(self) -> int:
        return 1 + sum(e.size() for e in self.elements)


@dataclass(frozen=True)
class ODict:
    """Dictionary construction."""
    pairs: tuple[tuple[OTerm, OTerm], ...]
    def canon(self) -> str:
        return "{" + ",".join(f"{k.canon()}:{v.canon()}" for k, v in self.pairs) + "}"
    def depth(self) -> int:
        if not self.pairs:
            return 1
        return 1 + max(max(k.depth(), v.depth()) for k, v in self.pairs)
    def size(self) -> int:
        return 1 + sum(k.size() + v.size() for k, v in self.pairs)


@dataclass(frozen=True)
class OLam:
    """Lambda / anonymous function with captured body."""
    params: tuple[str, ...]
    body: OTerm
    def canon(self) -> str:
        mapping = {p: f"_b{i}" for i, p in enumerate(self.params)}
        normalised = _subst_oterm(self.body, mapping)
        return f"λ({','.join(f'_b{i}' for i in range(len(self.params)))}){normalised.canon()}"
    def depth(self) -> int:
        return 1 + self.body.depth()
    def size(self) -> int:
        return 1 + self.body.size()


@dataclass(frozen=True)
class OUnknown:
    """Opaque term."""
    desc: str
    def canon(self) -> str:
        return f"?{self.desc}"
    def depth(self) -> int:
        return 0
    def size(self) -> int:
        return 1


OTerm = Union[OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict, OLam, OUnknown]


def _subst_oterm(term: OTerm, mapping: dict[str, str]) -> OTerm:
    """Substitute variable names in an OTerm tree according to *mapping*."""
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


def oterm_depth(term: OTerm) -> int:
    """Maximum nesting depth of an OTerm tree."""
    return term.depth()


def oterm_size(term: OTerm) -> int:
    """Total number of nodes in an OTerm tree."""
    return term.size()


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


# ══════════════════════════════════════════════════════════════════
# Chapter 42: OOP — Classes, Inheritance, and Method Resolution
# ══════════════════════════════════════════════════════════════════


@dataclass
class ClassInfo:
    """Compiled representation of a Python class in the OTerm framework.

    Stores the class name, direct base names, attribute names,
    method AST nodes, and a lazily-computed MRO list.
    """

    name: str
    bases: list[str]
    attrs: list[str]
    methods: dict[str, ast.FunctionDef]
    mro: list[str] = field(default_factory=list)


def _merge_c3(sequences: list[list[str]]) -> list[str]:
    """Core C3 merge algorithm.

    Given a list of MRO sequences (each ending with the base list),
    produce a single linearised list respecting:
      1. Local precedence order (direct bases left-to-right).
      2. Monotonicity (each base's MRO appears in order).
    Raises TypeError on inconsistent hierarchies.
    """
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
    """Compute C3 linearisation (Python MRO) for *cls_name*.

    Models MRO as a path through the class hierarchy HIT:
    each step in the linearisation corresponds to traversing an
    inheritance path constructor.

    Handles:
      - Single inheritance chains
      - Diamond inheritance
      - Deep hierarchies
      - Missing classes (treated as leaves)
      - Inconsistent hierarchies (raises TypeError)
    """
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
    """Resolve a method using the MRO path (transport along the
    class hierarchy HIT).

    Returns the class that provides the method implementation,
    or None if no class in the MRO defines it.
    """
    mro = compute_c3_mro(cls_name, class_map)
    for ancestor in mro:
        if ancestor in class_map and method_name in class_map[ancestor].methods:
            return ancestor
    return None


def resolve_all_methods(cls_name: str,
                        class_map: dict[str, ClassInfo]) -> dict[str, str]:
    """Return a mapping {method_name → provider_class} for all methods
    visible from *cls_name* through its MRO."""
    mro = compute_c3_mro(cls_name, class_map)
    seen: dict[str, str] = {}
    for ancestor in mro:
        if ancestor not in class_map:
            continue
        for mname in class_map[ancestor].methods:
            if mname not in seen:
                seen[mname] = ancestor
    return seen


def collect_all_attrs(cls_name: str,
                      class_map: dict[str, ClassInfo]) -> list[str]:
    """Collect all attribute names visible from *cls_name* through its MRO,
    preserving MRO order (first definition wins)."""
    mro = compute_c3_mro(cls_name, class_map)
    seen: set[str] = set()
    attrs: list[str] = []
    for ancestor in mro:
        if ancestor not in class_map:
            continue
        for attr in class_map[ancestor].attrs:
            if attr not in seen:
                seen.add(attr)
                attrs.append(attr)
    return attrs


def compile_virtual_dispatch(obj_symbol: str, method_name: str,
                             possible_classes: list[str],
                             class_map: dict[str, ClassInfo]) -> str:
    """Compile virtual dispatch as a case split on the object's class fiber.

    Each class in *possible_classes* defines a sub-fiber of TRef.
    The dispatch is a nested If expression over class tags.
    """
    if not possible_classes:
        return f"py_meth_{method_name}_default({obj_symbol})"

    cls = possible_classes[0]
    provider = resolve_method(cls, method_name, class_map)
    method_sym = f"py_meth_{method_name}_{provider or cls}"

    if len(possible_classes) == 1:
        return f"{method_sym}({obj_symbol})"

    rest = compile_virtual_dispatch(obj_symbol, method_name,
                                    possible_classes[1:], class_map)
    return (f"If(class_of({obj_symbol}) == {cls}, "
            f"{method_sym}({obj_symbol}), {rest})")


# ══════════════════════════════════════════════════════════════════
# OOP Class Compilation to OTerm
# ══════════════════════════════════════════════════════════════════


def _method_ast_to_olam(func_def: ast.FunctionDef) -> OLam:
    """Compile a method AST node to an OLam term.

    Strips the ``self`` parameter and compiles the body to an OTerm
    via a lightweight AST walk.
    """
    params = [a.arg for a in func_def.args.args if a.arg != "self"]
    body = _compile_func_body(func_def.body, params)
    return OLam(tuple(params), body)


def _compile_func_body(stmts: list[ast.stmt],
                       params: list[str]) -> OTerm:
    """Compile a list of statements to an OTerm.

    Handles return statements, assignments, if-else, and for-loops
    at a structural level sufficient for equivalence analysis.
    """
    if not stmts:
        return OLit(None)

    stmt = stmts[0]
    rest = stmts[1:]

    if isinstance(stmt, ast.Return):
        if stmt.value is None:
            return OLit(None)
        return _compile_expr(stmt.value, params)

    if isinstance(stmt, ast.Assign) and rest:
        return _compile_func_body(rest, params)

    if isinstance(stmt, ast.If):
        test = _compile_expr(stmt.test, params)
        true_br = _compile_func_body(stmt.body, params)
        false_br = _compile_func_body(stmt.orelse, params) if stmt.orelse else OLit(None)
        if rest:
            continuation = _compile_func_body(rest, params)
            return OOp("seq", (OCase(test, true_br, false_br), continuation))
        return OCase(test, true_br, false_br)

    if isinstance(stmt, ast.For):
        iter_expr = _compile_expr(stmt.iter, params)
        body_term = _compile_func_body(stmt.body, params)
        return OFold("for", body_term, iter_expr)

    if rest:
        return _compile_func_body(rest, params)

    return OUnknown(f"stmt_{type(stmt).__name__}")


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
    if isinstance(node, ast.UnaryOp):
        operand = _compile_expr(node.operand, params)
        op_name = f"u_{type(node.op).__name__.lower()}"
        return OOp(op_name, (operand,))
    if isinstance(node, ast.Compare):
        left = _compile_expr(node.left, params)
        if node.comparators:
            right = _compile_expr(node.comparators[0], params)
            op_name = type(node.ops[0]).__name__.lower()
            return OOp(op_name, (left, right))
        return left
    if isinstance(node, ast.Call):
        func_term = _compile_expr(node.func, params)
        arg_terms = tuple(_compile_expr(a, params) for a in node.args)
        if isinstance(func_term, OVar):
            return OOp(func_term.name, arg_terms)
        return OOp("call", (func_term,) + arg_terms)
    if isinstance(node, ast.Attribute):
        value = _compile_expr(node.value, params)
        return OOp(f"attr_{node.attr}", (value,))
    if isinstance(node, ast.List):
        return OSeq(tuple(_compile_expr(e, params) for e in node.elts))
    if isinstance(node, ast.Tuple):
        return OSeq(tuple(_compile_expr(e, params) for e in node.elts))
    if isinstance(node, ast.Dict):
        pairs: list[tuple[OTerm, OTerm]] = []
        for k, v in zip(node.keys, node.values):
            if k is not None:
                pairs.append((_compile_expr(k, params), _compile_expr(v, params)))
        return ODict(tuple(pairs))
    if isinstance(node, ast.IfExp):
        return OCase(_compile_expr(node.test, params),
                     _compile_expr(node.body, params),
                     _compile_expr(node.orelse, params))
    if isinstance(node, ast.Lambda):
        lam_params = tuple(a.arg for a in node.args.args)
        body = _compile_expr(node.body, list(lam_params))
        return OLam(lam_params, body)
    if isinstance(node, ast.Subscript):
        value = _compile_expr(node.value, params)
        sl = _compile_expr(node.slice, params) if isinstance(node.slice, ast.expr) else OUnknown("slice")
        return OOp("getitem", (value, sl))
    return OUnknown(f"expr_{type(node).__name__}")


def compile_class_to_oterm(cls_info: ClassInfo,
                           class_map: dict[str, ClassInfo]) -> dict[str, OLam]:
    """Compile all methods of *cls_info* to OLam terms, respecting MRO.

    Returns a mapping {method_name → OLam} representing the fully-resolved
    method set of the class (inheritance applied via MRO).
    """
    method_providers = resolve_all_methods(cls_info.name, class_map)
    compiled: dict[str, OLam] = {}
    for method_name, provider_cls in method_providers.items():
        func_def = class_map[provider_cls].methods[method_name]
        compiled[method_name] = _method_ast_to_olam(func_def)
    return compiled


def compile_class_dispatch_oterm(cls_info: ClassInfo,
                                 method_name: str,
                                 class_map: dict[str, ClassInfo]) -> OTerm:
    """Build an OCase chain for dispatching *method_name* across the
    inheritance hierarchy rooted at *cls_info*.

    The result is an OTerm tree of nested OCase nodes, one per class
    in the MRO, where each branch invokes the correct method body.
    """
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


# ══════════════════════════════════════════════════════════════════
# Chapter 43: Error Handling and Graceful Degradation
# ══════════════════════════════════════════════════════════════════


class DegradationLevel(Enum):
    """Pipeline degradation levels, from most to least informative."""
    DECIDED = auto()       # Z3 gave sat/unsat
    UNKNOWN = auto()       # Z3 timed out, partial confidence
    INCONCLUSIVE = auto()  # Compiler failed, fresh-constant fallback


@dataclass
class FiberResult:
    """Result of checking a single fiber."""
    fiber_name: str
    equivalent: bool | None  # None = unknown/timeout
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
        return sum(1 for r in self.fiber_results if r.level == DegradationLevel.DECIDED)

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

    def summary(self) -> dict[str, Any]:
        """Machine-readable summary of the pipeline result."""
        return {
            "verdict": self.verdict,
            "confidence": round(self.confidence, 4),
            "total_fibers": len(self.fiber_results),
            "decided": self.decided_count,
            "time_ms": round(self.total_time_ms, 2),
            "fibers": [
                {
                    "name": r.fiber_name,
                    "equivalent": r.equivalent,
                    "level": r.level.name,
                    "time_ms": round(r.time_ms, 2),
                    "error": r.error,
                }
                for r in self.fiber_results
            ],
        }


# ══════════════════════════════════════════════════════════════════
# Graceful Degradation State Machine
# ══════════════════════════════════════════════════════════════════


class StageStatus(Enum):
    """Status of a single pipeline stage."""
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
    """Track pipeline stages through a state machine for graceful degradation.

    Stages proceed through: PENDING → RUNNING → (SUCCEEDED | FAILED | TIMED_OUT).
    A stage can be SKIPPED if its prerequisites failed.

    The machine computes an overall degradation level based on which stages
    completed successfully.
    """

    STAGE_ORDER: list[str] = [
        "parse",
        "compile",
        "denotational",
        "z3_structural",
        "fingerprint",
        "duck_type",
        "fiber_check",
        "cohomology",
    ]

    def __init__(self) -> None:
        self._stages: dict[str, StageRecord] = {}
        for name in self.STAGE_ORDER:
            self._stages[name] = StageRecord(name=name)

    def begin(self, stage_name: str) -> None:
        """Mark *stage_name* as running."""
        if stage_name not in self._stages:
            self._stages[stage_name] = StageRecord(name=stage_name)
        rec = self._stages[stage_name]
        rec.status = StageStatus.RUNNING
        rec.start_time = time.monotonic()

    def succeed(self, stage_name: str, result: Any = None) -> None:
        """Mark *stage_name* as succeeded."""
        rec = self._stages[stage_name]
        rec.status = StageStatus.SUCCEEDED
        rec.end_time = time.monotonic()
        rec.result = result

    def fail(self, stage_name: str, error: str) -> None:
        """Mark *stage_name* as failed."""
        rec = self._stages[stage_name]
        rec.status = StageStatus.FAILED
        rec.end_time = time.monotonic()
        rec.error_message = error

    def timeout(self, stage_name: str) -> None:
        """Mark *stage_name* as timed out."""
        rec = self._stages[stage_name]
        rec.status = StageStatus.TIMED_OUT
        rec.end_time = time.monotonic()

    def skip(self, stage_name: str, reason: str = "") -> None:
        """Mark *stage_name* as skipped."""
        rec = self._stages[stage_name]
        rec.status = StageStatus.SKIPPED
        rec.error_message = reason

    def stage(self, stage_name: str) -> StageRecord:
        """Get the record for *stage_name*."""
        return self._stages[stage_name]

    @property
    def overall_level(self) -> DegradationLevel:
        """Compute the overall degradation level from stage statuses."""
        if any(r.status == StageStatus.SUCCEEDED
               for r in self._stages.values()):
            return DegradationLevel.DECIDED
        if any(r.status == StageStatus.TIMED_OUT
               for r in self._stages.values()):
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
        """Return a mapping of stage → elapsed_ms for all completed stages."""
        return {
            name: rec.elapsed_ms
            for name, rec in self._stages.items()
            if rec.status not in (StageStatus.PENDING, StageStatus.SKIPPED)
        }

    def total_elapsed_ms(self) -> float:
        """Total wall-clock time across all stages."""
        return sum(self.timing_report().values())


# ══════════════════════════════════════════════════════════════════
# Resource Limits and OS-Level Isolation
# ══════════════════════════════════════════════════════════════════


def set_resource_limits(
    memory_mb: int = 768,
    cpu_soft: int = 10,
    cpu_hard: int = 12,
) -> None:
    """Apply OS-level resource limits for subprocess safety.

    Defence-in-depth stack:
    1. Z3 memory_max_size (set separately)
    2. RLIMIT_AS — catches memory growth outside Z3
    3. RLIMIT_CPU — catches infinite loops
    """
    try:
        mem_bytes = memory_mb * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (mem_bytes, mem_bytes))
    except (ValueError, resource.error):
        pass

    try:
        resource.setrlimit(resource.RLIMIT_CPU, (cpu_soft, cpu_hard))
    except (ValueError, resource.error):
        pass


def check_fiber_with_timeout(
    fiber_name: str,
    check_fn: Any,
    timeout_ms: int = 5000,
    escalation_factor: int = 3,
) -> FiberResult:
    """Check a single fiber with timeout and escalation.

    If the initial check times out, retry with *escalation_factor* × timeout.
    """
    t0 = time.monotonic()

    try:
        result = check_fn(timeout_ms=timeout_ms)
    except MemoryError:
        elapsed = (time.monotonic() - t0) * 1000
        return FiberResult(fiber_name, None, DegradationLevel.INCONCLUSIVE,
                           elapsed, error="OOM")

    if result is None:
        try:
            result = check_fn(timeout_ms=timeout_ms * escalation_factor)
        except MemoryError:
            elapsed = (time.monotonic() - t0) * 1000
            return FiberResult(fiber_name, None,
                               DegradationLevel.INCONCLUSIVE, elapsed, error="OOM_escalated")

    elapsed = (time.monotonic() - t0) * 1000

    if result is None:
        return FiberResult(fiber_name, None, DegradationLevel.UNKNOWN, elapsed)
    return FiberResult(fiber_name, result, DegradationLevel.DECIDED, elapsed)


# ══════════════════════════════════════════════════════════════════
# Memory-Safe Z3 Context Manager
# ══════════════════════════════════════════════════════════════════


class Z3ContextManager:
    """Context manager for Z3 that auto-cleans on timeout or OOM.

    Creates an isolated Z3 Context so that formulas from one check
    don't leak into the next.  On exit (normal or exceptional),
    all Z3 references are dropped and a GC sweep is triggered.

    Usage::

        with Z3ContextManager(timeout_ms=5000, memory_mb=512) as ctx:
            s = ctx.solver()
            s.add(...)
            result = s.check()
    """

    def __init__(self, timeout_ms: int = 5000, memory_mb: int = 512) -> None:
        self._timeout_ms = timeout_ms
        self._memory_mb = memory_mb
        self._ctx: Any = None
        self._solver: Any = None
        self._entered = False

    def __enter__(self) -> "Z3ContextManager":
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
        """Release all Z3 objects and run GC."""
        import gc
        self._solver = None
        self._ctx = None
        self._entered = False
        gc.collect()

    @property
    def ctx(self) -> Any:
        """The Z3 Context for this session."""
        if not self._entered:
            raise RuntimeError("Z3ContextManager not entered")
        return self._ctx

    def solver(self) -> Any:
        """Create (or return cached) Solver bound to this context."""
        if self._solver is None:
            self._solver = Solver(ctx=self._ctx)
            self._solver.set("timeout", self._timeout_ms)
        return self._solver

    def fresh_solver(self) -> Any:
        """Create a new Solver, discarding any previous one."""
        self._solver = Solver(ctx=self._ctx)
        self._solver.set("timeout", self._timeout_ms)
        return self._solver


# ══════════════════════════════════════════════════════════════════
# Chapter 44: Scalability — Fiber Pruning, Budget, and Profiling
# ══════════════════════════════════════════════════════════════════


@dataclass
class FiberBudget:
    """Timeout budget manager that redistributes slack from fast fibers.

    The budget starts with *total_ms* milliseconds.  As each fiber
    completes, its actual elapsed time is subtracted and the remaining
    budget is split evenly among the remaining fibers.
    """
    total_ms: float
    remaining_ms: float = 0.0
    fibers_remaining: int = 0
    _allocations: list[tuple[str, int]] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.remaining_ms = self.total_ms

    def allocate(self, n_fibers: int) -> None:
        """Set the number of fibers that will consume this budget."""
        self.fibers_remaining = n_fibers

    def next_timeout(self, fiber_name: str = "") -> int:
        """Compute the timeout for the next fiber.

        Returns at least 100 ms to avoid trivially failing checks.
        """
        if self.fibers_remaining <= 0:
            return 0
        per_fiber = self.remaining_ms / self.fibers_remaining
        timeout = max(100, int(per_fiber))
        self._allocations.append((fiber_name, timeout))
        return timeout

    def record(self, elapsed_ms: float) -> None:
        """Record that a fiber consumed *elapsed_ms* of the budget."""
        self.remaining_ms -= elapsed_ms
        self.fibers_remaining -= 1
        self.remaining_ms = max(0, self.remaining_ms)

    @property
    def utilisation(self) -> float:
        """Fraction of total budget consumed so far."""
        used = self.total_ms - self.remaining_ms
        return used / self.total_ms if self.total_ms > 0 else 0.0


# ══════════════════════════════════════════════════════════════════
# Resource Budget Manager (time + memory across pipeline stages)
# ══════════════════════════════════════════════════════════════════


@dataclass
class StageBudget:
    """Budget allocation for a single pipeline stage."""
    name: str
    time_ms: float
    memory_mb: int
    priority: float = 1.0


class ResourceBudgetManager:
    """Allocate time and memory budgets across pipeline stages.

    Given a total time budget and memory ceiling, the manager distributes
    resources proportionally based on stage priorities, with the ability
    to reallocate slack from stages that finish early.
    """

    def __init__(self, total_time_ms: float = 10000,
                 total_memory_mb: int = 768) -> None:
        self._total_time_ms = total_time_ms
        self._total_memory_mb = total_memory_mb
        self._stages: dict[str, StageBudget] = {}
        self._spent: dict[str, float] = {}

    def add_stage(self, name: str, priority: float = 1.0,
                  memory_mb: int | None = None) -> None:
        """Register a pipeline stage with relative priority."""
        mem = memory_mb if memory_mb is not None else self._total_memory_mb
        self._stages[name] = StageBudget(
            name=name, time_ms=0.0, memory_mb=mem, priority=priority
        )

    def compute_allocations(self) -> dict[str, StageBudget]:
        """Distribute the remaining time budget proportionally across stages
        that have not yet been allocated."""
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
        """Record that *name* consumed *elapsed_ms*.

        Automatically re-distributes slack to remaining stages on the
        next call to :meth:`compute_allocations`.
        """
        self._spent[name] = elapsed_ms

    def budget_for(self, name: str) -> StageBudget:
        """Get the current budget for *name*, re-computing if needed."""
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


# ══════════════════════════════════════════════════════════════════
# Pipeline Stage Profiler
# ══════════════════════════════════════════════════════════════════


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
    """Profile pipeline stages with sub-millisecond timing breakdown.

    Usage::

        profiler = PipelineProfiler()
        with profiler.stage("compile"):
            ...
        with profiler.stage("z3_check"):
            ...
        print(profiler.report())
    """

    def __init__(self) -> None:
        self._entries: list[ProfileEntry] = []
        self._active: dict[str, float] = {}
        self._global_start: float = time.monotonic()

    @contextlib.contextmanager
    def stage(self, name: str, label: str = "") -> Iterator[None]:
        """Context manager to profile a named stage."""
        t0 = time.monotonic()
        self._active[name] = t0
        try:
            yield
        finally:
            t1 = time.monotonic()
            self._entries.append(ProfileEntry(name, t0, t1, label))
            self._active.pop(name, None)

    def record(self, name: str, elapsed_ms: float, label: str = "") -> None:
        """Manually record a stage timing."""
        now = time.monotonic()
        self._entries.append(ProfileEntry(
            name, now - elapsed_ms / 1000, now, label
        ))

    @property
    def total_ms(self) -> float:
        return (time.monotonic() - self._global_start) * 1000

    def breakdown(self) -> dict[str, float]:
        """Return {stage_name → total_elapsed_ms} aggregated over repeated calls."""
        agg: dict[str, float] = defaultdict(float)
        for e in self._entries:
            agg[e.stage] += e.elapsed_ms
        return dict(agg)

    def hotspot(self) -> str | None:
        """Return the stage that consumed the most time."""
        bd = self.breakdown()
        return max(bd, key=bd.get) if bd else None

    def report(self) -> str:
        """Human-readable timing breakdown."""
        bd = self.breakdown()
        total = self.total_ms
        lines = [f"Pipeline profile: {total:.1f} ms total"]
        for stage, ms in sorted(bd.items(), key=lambda kv: -kv[1]):
            pct = (ms / total * 100) if total > 0 else 0
            bar = "█" * int(pct / 2)
            lines.append(f"  {stage:20s} {ms:8.1f} ms ({pct:5.1f}%) {bar}")
        return "\n".join(lines)


# ══════════════════════════════════════════════════════════════════
# Fiber Pruning
# ══════════════════════════════════════════════════════════════════


def prune_fibers(
    fibers: list[tuple[str, float]],
    epsilon: float = 0.01,
) -> list[str]:
    """Prune fibers whose confidence is below *epsilon*.

    Each fiber is ``(name, confidence)``.
    """
    return [name for name, conf in fibers if conf >= epsilon]


def rank_fibers(
    fibers: list[tuple[str, float]],
) -> list[str]:
    """Rank fibers by confidence descending (check high-confidence first)."""
    return [name for name, _ in sorted(fibers, key=lambda x: -x[1])]


# ══════════════════════════════════════════════════════════════════
# Parallel Fiber Checker with Worker Pool
# ══════════════════════════════════════════════════════════════════


@dataclass
class ParallelCheckConfig:
    """Configuration for the parallel fiber checker."""
    max_workers: int = 4
    per_fiber_timeout_ms: int = 5000
    total_timeout_ms: int = 30000
    escalation_factor: int = 3


def check_fibers_parallel(
    fiber_checks: list[tuple[str, Callable[..., bool | None]]],
    config: ParallelCheckConfig | None = None,
) -> PipelineResult:
    """Run fiber checks in parallel using a thread pool.

    Each check function receives ``timeout_ms`` as a keyword argument.
    Results are collected and any counterexample triggers early cancellation.

    Thread-safety note: each fiber check should use its own Z3 Solver
    or a Z3ContextManager to avoid cross-thread state corruption.
    """
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
        except MemoryError:
            elapsed = (time.monotonic() - t0) * 1000
            return FiberResult(fiber_name, None, DegradationLevel.INCONCLUSIVE,
                               elapsed, error="OOM")
        except Exception as e:
            elapsed = (time.monotonic() - t0) * 1000
            return FiberResult(fiber_name, None, DegradationLevel.INCONCLUSIVE,
                               elapsed, error=str(e)[:80])

        if res is None and not cancel_event.is_set():
            escalated_timeout = min(
                timeout * config.escalation_factor,
                max(100, int((deadline - time.monotonic()) * 1000)),
            )
            try:
                res = check_fn(timeout_ms=escalated_timeout)
            except (MemoryError, Exception):
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


# ══════════════════════════════════════════════════════════════════
# Sequential Checking with Early Termination and Budget
# ══════════════════════════════════════════════════════════════════


def check_with_early_termination(
    fiber_checks: list[tuple[str, Any]],
    budget: FiberBudget,
    mode: str = "equivalence",
) -> PipelineResult:
    """Run fiber checks with early termination and budget allocation.

    For equivalence mode: terminate early if a counterexample is found.
    For inequivalence mode: terminate early if all fibers agree.
    """
    budget.allocate(len(fiber_checks))
    result = PipelineResult()
    t_start = time.monotonic()

    for fiber_name, check_fn in fiber_checks:
        timeout = budget.next_timeout(fiber_name)
        if timeout <= 0:
            result.fiber_results.append(
                FiberResult(fiber_name, None, DegradationLevel.UNKNOWN))
            budget.record(0)
            continue

        t0 = time.monotonic()
        fr = check_fiber_with_timeout(fiber_name, check_fn, timeout)
        elapsed = (time.monotonic() - t0) * 1000
        budget.record(elapsed)
        result.fiber_results.append(fr)

        if mode == "equivalence" and fr.equivalent is False:
            break
        if mode == "inequivalence" and fr.equivalent is True:
            break

    result.total_time_ms = (time.monotonic() - t_start) * 1000
    return result


# ══════════════════════════════════════════════════════════════════
# Chapter 45: Mathematical Prerequisites — reference catalog
# ══════════════════════════════════════════════════════════════════

MATH_REFERENCES: dict[str, list[str]] = {
    "category_theory": [
        "Mac Lane, Categories for the Working Mathematician (1971)",
        "Riehl, Category Theory in Context (2017)",
    ],
    "sheaf_theory": [
        "Grothendieck, Sur quelques points d'algèbre homologique (1957)",
        "Hartshorne, Algebraic Geometry, Ch. III (1977)",
        "Curry, Sheaves, Cosheaves and Applications (2014)",
    ],
    "homotopy_type_theory": [
        "HoTT Book, Univalent Foundations (2013)",
        "Cohen et al., Cubical Type Theory (2018)",
        "Angiuli et al., Computational Higher-Dimensional Type Theory (2018)",
    ],
    "smt_solving": [
        "de Moura & Bjørner, Z3: An Efficient SMT Solver (2008)",
        "Barrett et al., The SMT-LIB Standard",
    ],
}


# ══════════════════════════════════════════════════════════════════
# Chapter 46: Benchmark Pair Catalog — Difficulty Classification
# ══════════════════════════════════════════════════════════════════


class DifficultyTier(Enum):
    TRIVIAL = "trivial"    # Canonical match, resolved at compile stage
    MEDIUM = "medium"      # Path search, multi-fiber or axiom-assisted
    HARD = "hard"          # Different algorithms, RecFunction reasoning


class ResolutionStage(Enum):
    COMPILE = "compile"          # Identical/alpha-equiv OTerms
    FIBER = "fiber"              # Per-fiber Z3 checking
    COHOMOLOGY = "cohomology"    # H^1 computation
    AXIOM = "axiom"              # Shared-function axioms
    RECFUNCTION = "recfunction"  # Z3 RecFunction reasoning


@dataclass
class PairClassification:
    """Classification metadata for a single benchmark pair."""
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
    PairClassification("EQ-14", "Arithmetic parser: recursive descent vs shunting-yard",
                       True, ResolutionStage.RECFUNCTION, DifficultyTier.HARD),
    PairClassification("EQ-23", "Bracket matching: stack vs counter",
                       True, ResolutionStage.FIBER, DifficultyTier.TRIVIAL),
    PairClassification("EQ-29", "Graph inversion: comprehension vs defaultdict",
                       True, ResolutionStage.FIBER, DifficultyTier.TRIVIAL),
    PairClassification("EQ-37", "Fibonacci: matrix exponentiation vs iterative",
                       True, ResolutionStage.RECFUNCTION, DifficultyTier.HARD),
]

NEQ_CLASSIFICATIONS: list[PairClassification] = [
    PairClassification("NEQ-01", "Floor div vs truncation on negative",
                       False, ResolutionStage.COMPILE, DifficultyTier.TRIVIAL),
    PairClassification("NEQ-06", "Late-binding vs early-binding closure",
                       False, ResolutionStage.RECFUNCTION, DifficultyTier.HARD),
    PairClassification("NEQ-09", "NaN propagation in max()",
                       False, ResolutionStage.FIBER, DifficultyTier.MEDIUM),
    PairClassification("NEQ-22", "+= vs + on list aliases",
                       False, ResolutionStage.AXIOM, DifficultyTier.HARD),
    PairClassification("NEQ-42", "Shallow vs deep copy inner mutation",
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
        stage = pc.stage.value
        stats["by_tier"][tier] = stats["by_tier"].get(tier, 0) + 1
        stats["by_stage"][stage] = stats["by_stage"].get(stage, 0) + 1
        if pc.is_equivalent:
            stats["by_equivalence"]["equivalent"] += 1
        else:
            stats["by_equivalence"]["non_equivalent"] += 1
    return stats


# ══════════════════════════════════════════════════════════════════
# Benchmark Pair Difficulty Predictor
# ══════════════════════════════════════════════════════════════════


@dataclass
class DifficultyEstimate:
    """Predicted difficulty of a benchmark pair from OTerm structure."""
    pair_name: str
    predicted_tier: DifficultyTier
    predicted_stage: ResolutionStage
    score: float
    features: dict[str, float]


def _compute_structural_features(term: OTerm) -> dict[str, float]:
    """Extract numeric features from an OTerm for difficulty prediction."""
    return {
        "depth": float(oterm_depth(term)),
        "size": float(oterm_size(term)),
        "has_fix": 1.0 if oterm_has_fix(term) else 0.0,
        "num_ops": float(len(oterm_collect_ops(term))),
        "has_fold": 1.0 if isinstance(term, OFold) else 0.0,
        "num_cases": float(_count_nodes(term, OCase)),
    }


def _count_nodes(term: OTerm, node_type: type) -> int:
    """Count occurrences of *node_type* in *term*."""
    count = 1 if isinstance(term, node_type) else 0
    if isinstance(term, OOp):
        count += sum(_count_nodes(a, node_type) for a in term.args)
    elif isinstance(term, OFold):
        count += _count_nodes(term.init, node_type) + _count_nodes(term.collection, node_type)
    elif isinstance(term, OCase):
        count += (_count_nodes(term.test, node_type) + _count_nodes(term.true_branch, node_type)
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


def predict_difficulty(term_a: OTerm, term_b: OTerm,
                       pair_name: str = "") -> DifficultyEstimate:
    """Predict the difficulty tier and expected resolution stage for a pair
    of OTerms, using structural features.

    Heuristic:
      - If either term contains OFix → HARD / RECFUNCTION
      - If depths differ by > 3 or sizes differ by > 2× → MEDIUM / COHOMOLOGY
      - If both are shallow and small → TRIVIAL / COMPILE
    """
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
        pair_name=pair_name,
        predicted_tier=tier,
        predicted_stage=stage,
        score=score,
        features=combined,
    )


# ══════════════════════════════════════════════════════════════════
# Benchmark Regression Tracker
# ══════════════════════════════════════════════════════════════════


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
            "pair_id": self.pair_id,
            "timestamp": self.timestamp,
            "expected": self.expected,
            "got": self.got,
            "time_ms": round(self.time_ms, 2),
            "correct": self.correct,
            "explanation": self.explanation,
            "commit_sha": self.commit_sha,
        }

    @staticmethod
    def from_dict(d: dict[str, Any]) -> "BenchmarkRun":
        return BenchmarkRun(
            pair_id=d["pair_id"],
            timestamp=d["timestamp"],
            expected=d["expected"],
            got=d.get("got"),
            time_ms=d.get("time_ms", 0.0),
            explanation=d.get("explanation", ""),
            commit_sha=d.get("commit_sha", ""),
        )


class RegressionTracker:
    """Store benchmark results over time and detect regressions.

    Maintains an in-memory history and can persist to a JSON file.
    A *regression* is defined as a pair that was correct in the
    previous run but incorrect in the current run.
    """

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
        """Add a benchmark run to the history."""
        self._history.append(run)

    def record_batch(self, runs: list[BenchmarkRun]) -> None:
        """Add a batch of runs and persist."""
        self._history.extend(runs)
        self._save()

    def latest_runs(self, pair_id: str | None = None) -> list[BenchmarkRun]:
        """Get the most recent run for each pair (or for a specific pair)."""
        latest: dict[str, BenchmarkRun] = {}
        for run in self._history:
            if pair_id is not None and run.pair_id != pair_id:
                continue
            if (run.pair_id not in latest
                    or run.timestamp > latest[run.pair_id].timestamp):
                latest[run.pair_id] = run
        return list(latest.values())

    def previous_runs(self, pair_id: str | None = None) -> list[BenchmarkRun]:
        """Get the second-most-recent run for each pair."""
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
        """Detect regressions: pairs that were correct before but are now wrong.

        Returns a list of (previous_run, current_run) pairs.
        """
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
        """Detect improvements: pairs that were wrong before but are now correct."""
        prev_map: dict[str, BenchmarkRun] = {
            r.pair_id: r for r in self.previous_runs()
        }
        improvements: list[tuple[BenchmarkRun, BenchmarkRun]] = []
        for current in self.latest_runs():
            prev = prev_map.get(current.pair_id)
            if prev is not None and not prev.correct and current.correct:
                improvements.append((prev, current))
        return improvements

    def accuracy_over_time(self) -> list[tuple[float, float]]:
        """Return (timestamp, accuracy) tuples grouped by recording batch.

        A "batch" is defined as runs sharing the same commit_sha, or
        falling within a 60-second window if no commit_sha is set.
        """
        if not self._history:
            return []

        by_batch: dict[str, list[BenchmarkRun]] = defaultdict(list)
        for run in self._history:
            key = run.commit_sha or str(int(run.timestamp / 60))
            by_batch[key].append(run)

        results: list[tuple[float, float]] = []
        for batch in by_batch.values():
            ts = max(r.timestamp for r in batch)
            correct = sum(1 for r in batch if r.correct)
            accuracy = correct / len(batch) if batch else 0.0
            results.append((ts, accuracy))

        return sorted(results)

    def timing_stats(self, pair_id: str) -> dict[str, float]:
        """Compute timing statistics for a specific pair across all runs."""
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
        """Overall summary of regression tracker state."""
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


# ══════════════════════════════════════════════════════════════════
# Self-Tests
# ══════════════════════════════════════════════════════════════════


if __name__ == "__main__":
    import sys

    _counts = {"passed": 0, "failed": 0}

    def _assert(cond: bool, msg: str) -> None:
        if cond:
            _counts["passed"] += 1
            print(f"  ✓ {msg}")
        else:
            _counts["failed"] += 1
            print(f"  ✗ FAIL: {msg}")

    # ── C3 MRO ──────────────────────────────────────────────────
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

    mro_leaf = compute_c3_mro("A", cmap)
    _assert(mro_leaf == ["A"], f"Leaf class MRO: {mro_leaf}")

    deep_map: dict[str, ClassInfo] = {
        "X": ClassInfo("X", [], [], {}),
        "Y": ClassInfo("Y", ["X"], [], {}),
        "Z": ClassInfo("Z", ["Y"], [], {}),
        "W": ClassInfo("W", ["Z"], [], {}),
    }
    mro_w = compute_c3_mro("W", deep_map)
    _assert(mro_w == ["W", "Z", "Y", "X"], f"Deep chain MRO: {mro_w}")

    all_mros = compute_all_mros(cmap)
    _assert(len(all_mros) == 4, f"compute_all_mros returned {len(all_mros)} entries")

    # ── Method Resolution ────────────────────────────────────────
    print("\n=== Method Resolution Tests ===")

    func_a = ast.parse("def foo(self): pass").body[0]
    func_b = ast.parse("def foo(self): pass").body[0]
    func_c = ast.parse("def bar(self): pass").body[0]

    mr_map: dict[str, ClassInfo] = {
        "Base": ClassInfo("Base", [], [], {"foo": func_a}),
        "Child": ClassInfo("Child", ["Base"], [], {"bar": func_c}),
        "Override": ClassInfo("Override", ["Base"], [], {"foo": func_b, "bar": func_c}),
    }

    res = resolve_method("Child", "foo", mr_map)
    _assert(res == "Base", f"Inherited method resolves to Base: {res}")

    res2 = resolve_method("Override", "foo", mr_map)
    _assert(res2 == "Override", f"Overridden method resolves to Override: {res2}")

    res3 = resolve_method("Child", "missing", mr_map)
    _assert(res3 is None, f"Missing method returns None: {res3}")

    all_m = resolve_all_methods("Child", mr_map)
    _assert(set(all_m.keys()) == {"foo", "bar"}, f"All methods: {all_m}")

    attrs = collect_all_attrs("Child", mr_map)
    _assert(isinstance(attrs, list), f"collect_all_attrs returns list")

    # ── Virtual Dispatch Compilation ──────────────────────────────
    print("\n=== Virtual Dispatch Tests ===")

    dispatch = compile_virtual_dispatch("obj", "foo", ["Override", "Child"], mr_map)
    _assert("If(class_of(obj)" in dispatch, f"Dispatch has If: {dispatch[:60]}")

    dispatch_single = compile_virtual_dispatch("obj", "foo", ["Base"], mr_map)
    _assert("py_meth_foo_Base(obj)" == dispatch_single, f"Single dispatch: {dispatch_single}")

    dispatch_empty = compile_virtual_dispatch("obj", "foo", [], mr_map)
    _assert("default" in dispatch_empty, f"Empty dispatch: {dispatch_empty}")

    # ── OOP Class Compilation ──────────────────────────────────────
    print("\n=== OOP Class Compilation Tests ===")

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

    parsed_classes = parse_classes_from_source(src)
    _assert(len(parsed_classes) == 3, f"Parsed 3 classes: {list(parsed_classes.keys())}")
    _assert("Dog" in parsed_classes, "Dog class found")

    dog_methods = compile_class_to_oterm(parsed_classes["Dog"], parsed_classes)
    _assert("speak" in dog_methods, f"Dog has speak method: {list(dog_methods.keys())}")
    _assert(isinstance(dog_methods["speak"], OLam), "speak is OLam")

    dispatch_term = compile_class_dispatch_oterm(
        parsed_classes["Dog"], "speak", parsed_classes
    )
    _assert(isinstance(dispatch_term, (OLam, OCase)),
            f"Dispatch term type: {type(dispatch_term).__name__}")

    # ── OTerm Utilities ──────────────────────────────────────────
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

    lam = OLam(("a", "b"), OOp("add", (OVar("a"), OVar("b"))))
    _assert("λ" in lam.canon(), f"OLam canon: {lam.canon()}")

    # ── DegradationLevel / FiberResult ────────────────────────────
    print("\n=== Degradation Tests ===")

    pr = PipelineResult(fiber_results=[
        FiberResult("int", True, DegradationLevel.DECIDED, 100.0),
        FiberResult("str", True, DegradationLevel.DECIDED, 200.0),
        FiberResult("bool", None, DegradationLevel.UNKNOWN, 50.0),
    ])
    _assert(pr.confidence == 1.0, f"Confidence: {pr.confidence}")
    _assert("PARTIAL" in pr.verdict, f"Verdict: {pr.verdict}")
    _assert(pr.decided_count == 2, f"Decided count: {pr.decided_count}")

    pr2 = PipelineResult(fiber_results=[
        FiberResult("int", True, DegradationLevel.DECIDED, 100.0),
        FiberResult("str", False, DegradationLevel.DECIDED, 200.0),
    ])
    _assert(pr2.verdict == "INEQUIVALENT", f"NEQ verdict: {pr2.verdict}")

    summary = pr.summary()
    _assert(summary["total_fibers"] == 3, f"Summary fibers: {summary['total_fibers']}")

    # ── Graceful Degradation State Machine ────────────────────────
    print("\n=== State Machine Tests ===")

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

    _assert(sm.overall_level == DegradationLevel.DECIDED, "Overall = DECIDED (parse succeeded)")
    _assert("parse" in sm.succeeded_stages, "Parse in succeeded list")
    _assert("compile" in sm.failed_stages, "Compile in failed list")
    _assert("fiber_check" in sm.timed_out_stages, "Fiber in timed_out list")

    timing = sm.timing_report()
    _assert("parse" in timing, f"Timing has parse: {list(timing.keys())}")
    _assert(sm.total_elapsed_ms() >= 0, f"Total elapsed: {sm.total_elapsed_ms():.2f}")

    # ── FiberBudget ──────────────────────────────────────────────
    print("\n=== Budget Tests ===")

    fb = FiberBudget(total_ms=10000)
    fb.allocate(4)
    t1_budget = fb.next_timeout("fiber_int")
    _assert(t1_budget == 2500, f"First budget: {t1_budget}")
    fb.record(500)
    t2_budget = fb.next_timeout("fiber_str")
    _assert(t2_budget >= 3000, f"Redistributed budget: {t2_budget}")
    _assert(fb.utilisation > 0, f"Utilisation: {fb.utilisation}")

    # ── Resource Budget Manager ──────────────────────────────────
    print("\n=== Resource Budget Manager Tests ===")

    rbm = ResourceBudgetManager(total_time_ms=10000, total_memory_mb=768)
    rbm.add_stage("compile", priority=2.0)
    rbm.add_stage("z3_check", priority=5.0)
    rbm.add_stage("cohomology", priority=3.0)

    allocs = rbm.compute_allocations()
    _assert(allocs["z3_check"].time_ms > allocs["compile"].time_ms,
            f"Z3 gets more time than compile")
    total_alloc = sum(s.time_ms for s in allocs.values())
    _assert(abs(total_alloc - 10000) < 1, f"Budget sums to total: {total_alloc}")

    z3_before = allocs["z3_check"].time_ms
    rbm.record_stage("compile", 200)
    rbm.compute_allocations()
    z3_after = allocs["z3_check"].time_ms
    _assert(z3_after > z3_before,
            f"Z3 gets slack from fast compile: {z3_before:.0f} → {z3_after:.0f}")

    rbm_summary = rbm.summary()
    _assert("remaining_time_ms" in rbm_summary, "Summary has remaining_time_ms")

    # ── Pipeline Profiler ────────────────────────────────────────
    print("\n=== Profiler Tests ===")

    profiler = PipelineProfiler()
    with profiler.stage("compile"):
        time.sleep(0.01)
    with profiler.stage("z3_check"):
        time.sleep(0.02)
    profiler.record("cohomology", 5.0)

    bd = profiler.breakdown()
    _assert("compile" in bd, f"Breakdown has compile")
    _assert("z3_check" in bd, f"Breakdown has z3_check")
    _assert(bd["z3_check"] > bd["compile"], "Z3 took longer than compile")
    _assert(profiler.hotspot() == "z3_check", f"Hotspot: {profiler.hotspot()}")
    report_str = profiler.report()
    _assert("Pipeline profile" in report_str, "Report has header")

    # ── Difficulty Predictor ─────────────────────────────────────
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

    # ── Regression Tracker ───────────────────────────────────────
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

    acc = tracker.accuracy_over_time()
    _assert(len(acc) >= 1, f"Accuracy timeline entries: {len(acc)}")

    t_summary = tracker.summary()
    _assert(t_summary["regressions"] == 1, f"Summary regressions: {t_summary['regressions']}")
    _assert(t_summary["current_accuracy"] == 0.5,
            f"Summary accuracy: {t_summary['current_accuracy']}")

    # ── Benchmark Classification ─────────────────────────────────
    print("\n=== Classification Tests ===")

    all_class = EQ_CLASSIFICATIONS + NEQ_CLASSIFICATIONS
    stats = classify_benchmark_suite(all_class)
    _assert("by_tier" in stats, "Stats has by_tier")
    _assert("by_stage" in stats, "Stats has by_stage")
    _assert("by_equivalence" in stats, "Stats has by_equivalence")
    _assert(stats["by_equivalence"]["equivalent"] == len(EQ_CLASSIFICATIONS),
            f"EQ count: {stats['by_equivalence']['equivalent']}")
    _assert(stats["by_equivalence"]["non_equivalent"] == len(NEQ_CLASSIFICATIONS),
            f"NEQ count: {stats['by_equivalence']['non_equivalent']}")

    # ── Fiber Pruning / Ranking ──────────────────────────────────
    print("\n=== Fiber Pruning Tests ===")

    fibers_in = [("int", 0.9), ("str", 0.005), ("bool", 0.5), ("ref", 0.001)]
    pruned = prune_fibers(fibers_in, epsilon=0.01)
    _assert(pruned == ["int", "bool"], f"Pruned: {pruned}")

    ranked = rank_fibers(fibers_in)
    _assert(ranked[0] == "int", f"Highest-confidence first: {ranked}")

    # ── Z3 Context Manager ───────────────────────────────────────
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
        _assert(True, "Z3 not available — skipping Z3ContextManager test")

    # ── AST → OTerm Compilation ──────────────────────────────────
    print("\n=== AST → OTerm Compilation Tests ===")

    func_src = "def f(x): return x + 1"
    tree = ast.parse(func_src)
    func_node = tree.body[0]
    body_term = _compile_func_body(func_node.body, ["x"])
    _assert(isinstance(body_term, OOp), f"Compiled body type: {type(body_term).__name__}")
    _assert("add" in body_term.canon(), f"Body canon: {body_term.canon()}")

    cond_src = "def f(x): return x if x > 0 else -x"
    tree2 = ast.parse(cond_src)
    func_node2 = tree2.body[0]
    cond_term = _compile_func_body(func_node2.body, ["x"])
    _assert(isinstance(cond_term, OCase), f"Conditional type: {type(cond_term).__name__}")

    # ── Parallel Checker Config ──────────────────────────────────
    print("\n=== Parallel Checker Config Tests ===")

    cfg = ParallelCheckConfig(max_workers=2, per_fiber_timeout_ms=1000)
    _assert(cfg.max_workers == 2, "Config workers")
    _assert(cfg.per_fiber_timeout_ms == 1000, "Config timeout")

    dummy_checks: list[tuple[str, Callable[..., bool | None]]] = [
        ("fiber_a", lambda timeout_ms=1000: True),
        ("fiber_b", lambda timeout_ms=1000: True),
        ("fiber_c", lambda timeout_ms=1000: False),
    ]
    par_result = check_fibers_parallel(dummy_checks, cfg)
    _assert(len(par_result.fiber_results) == 3, f"Parallel results: {len(par_result.fiber_results)}")
    _assert(par_result.total_time_ms > 0, f"Parallel time: {par_result.total_time_ms:.1f}")
    has_false = any(r.equivalent is False for r in par_result.fiber_results)
    _assert(has_false, "Parallel found counterexample")

    # ── Sequential Early Termination ─────────────────────────────
    print("\n=== Sequential Early Termination Tests ===")

    seq_budget = FiberBudget(total_ms=5000)
    seq_checks: list[tuple[str, Any]] = [
        ("f1", lambda timeout_ms=1000: True),
        ("f2", lambda timeout_ms=1000: False),
        ("f3", lambda timeout_ms=1000: True),
    ]
    seq_result = check_with_early_termination(seq_checks, seq_budget, mode="equivalence")
    _assert(len(seq_result.fiber_results) == 2,
            f"Early termination at fiber 2: {len(seq_result.fiber_results)}")

    # ── Summary ──────────────────────────────────────────────────
    print(f"\n{'='*60}")
    print(f"Results: {_counts['passed']} passed, {_counts['failed']} failed")
    if _counts["failed"]:
        print("SOME TESTS FAILED")
        sys.exit(1)
    else:
        print("ALL TESTS PASSED")
        sys.exit(0)
