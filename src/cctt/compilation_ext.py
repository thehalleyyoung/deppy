"""§2-ext: Compilation Extensions — proposals from g13_compilation wired into CCTT.

Provides additional AST→Z3 helpers that extend compiler.py:
  1. Compilation coverage analyzer (which Python AST nodes are/aren't handled)
  2. Section complexity metrics (guard/term depth, variable counts)
  3. Recursion scheme classification for choosing Z3 encoding strategy
  4. Extended fold recognition for builtins (prod, bitwise, set ops)
  5. Lambda body compilation (defunctionalization)
  6. AnnAssign / Match / TryStar statement handlers
  7. Assert-as-guard section extraction
"""
from __future__ import annotations

import ast
import textwrap
from collections import Counter
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple

from .theory import Theory, _z3, _HAS_Z3
from .compiler import (
    Env, Section, compile_expr, compile_func, extract_sections,
    exec_stmts, exec_one, _ensure_z3, _assign_target, _skip_doc,
    _stable_hash, _find_modified, _has_ret, compile_call,
    SHARED_BUILTINS, SHARED_MODULE_FUNCS,
    ADD, SUB, MUL, FLOORDIV, MOD, POW,
    BITOR, BITAND, BITXOR,
    IADD, IMUL, NEG, ABS_, NOT, BOOL_, INT_, LEN_,
    GETITEM, EQ, NE, LT, LE, GT, GE,
)


# ═══════════════════════════════════════════════════════════
# §1  Compilation Coverage Analyzer
#     (ported from g13_compilation §10, adapted for Z3 compiler)
# ═══════════════════════════════════════════════════════════

_ALL_EXPR_NODES: FrozenSet[str] = frozenset({
    'Constant', 'Name', 'BinOp', 'UnaryOp', 'Compare', 'BoolOp',
    'IfExp', 'Call', 'Subscript', 'Tuple', 'List', 'ListComp',
    'SetComp', 'GeneratorExp', 'DictComp', 'Dict', 'Set',
    'Attribute', 'NamedExpr', 'Lambda', 'Starred', 'JoinedStr',
    'FormattedValue', 'Slice', 'Await', 'Yield', 'YieldFrom',
})

_ALL_STMT_NODES: FrozenSet[str] = frozenset({
    'Return', 'Assign', 'AugAssign', 'AnnAssign', 'If', 'For',
    'While', 'Try', 'TryStar', 'With', 'Raise', 'Assert',
    'Import', 'ImportFrom', 'FunctionDef', 'AsyncFunctionDef',
    'ClassDef', 'Expr', 'Pass', 'Break', 'Continue', 'Delete',
    'Global', 'Nonlocal', 'Match',
})

# What compiler.py actually handles (in compile_expr / exec_one)
_HANDLED_EXPR_NODES: FrozenSet[str] = frozenset({
    'Constant', 'Name', 'BinOp', 'UnaryOp', 'Compare', 'BoolOp',
    'IfExp', 'Call', 'Subscript', 'Tuple', 'List', 'ListComp',
    'SetComp', 'GeneratorExp', 'DictComp', 'Dict', 'Set',
    'Attribute', 'NamedExpr', 'Lambda', 'Starred', 'JoinedStr',
    'FormattedValue', 'Await', 'Yield', 'YieldFrom',
})

# Extended set: includes nodes this module adds handlers for
_HANDLED_STMT_NODES: FrozenSet[str] = frozenset({
    'Return', 'Assign', 'AugAssign', 'AnnAssign', 'If', 'For',
    'While', 'Try', 'With', 'AsyncWith', 'Raise', 'Assert',
    'Import', 'ImportFrom', 'FunctionDef', 'AsyncFunctionDef',
    'ClassDef', 'Expr', 'Pass', 'Break', 'Continue', 'Delete',
    'Global', 'Nonlocal', 'Match',
})


@dataclass
class CoverageReport:
    """Report of which Python AST node types are/aren't handled by compilation."""
    handled_expr: FrozenSet[str]
    unhandled_expr: FrozenSet[str]
    handled_stmt: FrozenSet[str]
    unhandled_stmt: FrozenSet[str]
    source_expr_counts: Dict[str, int]
    source_stmt_counts: Dict[str, int]
    coverage_pct: float

    def summary(self) -> str:
        lines = [f"Compilation coverage: {self.coverage_pct:.1f}%"]
        if self.unhandled_expr:
            lines.append(f"  Unhandled expr nodes: {sorted(self.unhandled_expr)}")
        if self.unhandled_stmt:
            lines.append(f"  Unhandled stmt nodes: {sorted(self.unhandled_stmt)}")
        used_unhandled_expr = {n for n in self.unhandled_expr
                               if self.source_expr_counts.get(n, 0) > 0}
        used_unhandled_stmt = {n for n in self.unhandled_stmt
                               if self.source_stmt_counts.get(n, 0) > 0}
        if used_unhandled_expr:
            lines.append(f"  ⚠ Used but unhandled expr: {sorted(used_unhandled_expr)}")
        if used_unhandled_stmt:
            lines.append(f"  ⚠ Used but unhandled stmt: {sorted(used_unhandled_stmt)}")
        return '\n'.join(lines)


def analyze_coverage(source: str) -> CoverageReport:
    """Analyze which AST node types in the given source are handled by the Z3 compiler.

    Parses the source, walks the AST, and compares against the set of
    node types that compiler.py + compilation_ext.py handle.
    """
    try:
        tree = ast.parse(textwrap.dedent(source))
    except SyntaxError:
        return CoverageReport(
            handled_expr=_HANDLED_EXPR_NODES,
            unhandled_expr=_ALL_EXPR_NODES - _HANDLED_EXPR_NODES,
            handled_stmt=_HANDLED_STMT_NODES,
            unhandled_stmt=_ALL_STMT_NODES - _HANDLED_STMT_NODES,
            source_expr_counts={},
            source_stmt_counts={},
            coverage_pct=0.0,
        )

    expr_counts: Counter = Counter()
    stmt_counts: Counter = Counter()
    for node in ast.walk(tree):
        name = type(node).__name__
        if isinstance(node, ast.expr):
            expr_counts[name] += 1
        elif isinstance(node, ast.stmt):
            stmt_counts[name] += 1

    used_nodes = set(expr_counts.keys()) | set(stmt_counts.keys())
    handled_used = used_nodes & (_HANDLED_EXPR_NODES | _HANDLED_STMT_NODES)
    total_used = len(used_nodes)
    coverage_pct = (len(handled_used) / max(total_used, 1)) * 100.0

    return CoverageReport(
        handled_expr=_HANDLED_EXPR_NODES,
        unhandled_expr=_ALL_EXPR_NODES - _HANDLED_EXPR_NODES,
        handled_stmt=_HANDLED_STMT_NODES,
        unhandled_stmt=_ALL_STMT_NODES - _HANDLED_STMT_NODES,
        source_expr_counts=dict(expr_counts),
        source_stmt_counts=dict(stmt_counts),
        coverage_pct=coverage_pct,
    )


# ═══════════════════════════════════════════════════════════
# §2  Section Complexity Metrics
#     (ported from g13_compilation §1, adapted for Z3 sections)
# ═══════════════════════════════════════════════════════════

@dataclass(frozen=True)
class SectionMetrics:
    """Complexity metrics for a compiled presheaf section."""
    num_sections: int
    max_guard_depth: int
    max_term_depth: int
    total_z3_nodes: int
    distinct_symbols: int
    has_recursion: bool
    has_ite: bool

    @property
    def complexity_score(self) -> float:
        score = float(self.total_z3_nodes)
        score += self.max_guard_depth * 2.0
        score += self.max_term_depth * 2.0
        if self.has_recursion:
            score *= 1.5
        return score


def _z3_depth(expr) -> int:
    """Compute depth of a Z3 expression tree."""
    if not _HAS_Z3:
        return 0
    try:
        if not hasattr(expr, 'num_args') or expr.num_args() == 0:
            return 0
        return 1 + max(_z3_depth(expr.arg(i)) for i in range(expr.num_args()))
    except Exception:
        return 0


def _z3_size(expr) -> int:
    """Count total nodes in a Z3 expression tree."""
    if not _HAS_Z3:
        return 1
    try:
        if not hasattr(expr, 'num_args') or expr.num_args() == 0:
            return 1
        return 1 + sum(_z3_size(expr.arg(i)) for i in range(expr.num_args()))
    except Exception:
        return 1


def _z3_symbols(expr) -> Set[str]:
    """Collect distinct symbol names from a Z3 expression."""
    syms: Set[str] = set()
    if not _HAS_Z3:
        return syms
    try:
        if hasattr(expr, 'decl'):
            syms.add(expr.decl().name())
        if hasattr(expr, 'num_args'):
            for i in range(expr.num_args()):
                syms |= _z3_symbols(expr.arg(i))
    except Exception:
        pass
    return syms


def compute_section_metrics(sections: List[Section]) -> SectionMetrics:
    """Compute complexity metrics for a list of presheaf sections."""
    if not sections:
        return SectionMetrics(0, 0, 0, 0, 0, False, False)

    max_gdepth = 0
    max_tdepth = 0
    total_nodes = 0
    all_syms: Set[str] = set()
    has_rec = False
    has_ite = False

    for sec in sections:
        gd = _z3_depth(sec.guard)
        td = _z3_depth(sec.term)
        max_gdepth = max(max_gdepth, gd)
        max_tdepth = max(max_tdepth, td)
        total_nodes += _z3_size(sec.guard) + _z3_size(sec.term)
        all_syms |= _z3_symbols(sec.guard) | _z3_symbols(sec.term)
        # Check for recursive function symbols
        syms = _z3_symbols(sec.term)
        if any(s.startswith('rec_') for s in syms):
            has_rec = True
        if any(s == 'if' or s == 'If' for s in syms):
            has_ite = True

    return SectionMetrics(
        num_sections=len(sections),
        max_guard_depth=max_gdepth,
        max_term_depth=max_tdepth,
        total_z3_nodes=total_nodes,
        distinct_symbols=len(all_syms),
        has_recursion=has_rec,
        has_ite=has_ite,
    )


# ═══════════════════════════════════════════════════════════
# §3  Recursion Scheme Classification
#     (ported from g13_compilation §4, adapted for AST-level analysis)
# ═══════════════════════════════════════════════════════════

class RecursionScheme(Enum):
    """Classification of recursion patterns in Python functions."""
    PRIMITIVE = auto()          # f(n) depends only on f(n-1)
    COURSE_OF_VALUES = auto()   # f(n) depends on f(n-1), ..., f(n-k)
    TAIL = auto()               # recursive call is in tail position
    TREE = auto()               # multiple recursive calls at different subproblems
    MUTUAL = auto()             # calls another function that calls back
    NON_RECURSIVE = auto()      # no self-reference
    ACCUMULATOR = auto()        # tail call with accumulator argument
    UNKNOWN = auto()


@dataclass
class RecursionInfo:
    """Analysis of a Python function's recursion structure."""
    scheme: RecursionScheme
    depth: Optional[int]
    call_count: int
    is_tail: bool
    offsets: Set[int]
    has_accumulator: bool


def classify_recursion_ast(func_node: ast.FunctionDef) -> RecursionInfo:
    """Classify the recursion scheme of a Python function from its AST.

    Walks the AST to find self-recursive calls, determines tail position,
    counts call sites, and extracts recursion offsets.
    """
    fname = func_node.name
    calls = _collect_recursive_calls_ast(func_node.body, fname)
    call_count = len(calls)

    if call_count == 0:
        return RecursionInfo(
            scheme=RecursionScheme.NON_RECURSIVE,
            depth=None, call_count=0, is_tail=False,
            offsets=set(), has_accumulator=False,
        )

    offsets = set()
    for call in calls:
        off = _extract_offset_ast(call, func_node.args.args)
        if off is not None:
            offsets.add(off)

    is_tail = _is_tail_position_ast(func_node.body, fname)
    has_acc = _has_accumulator_ast(calls, func_node.args.args)

    if is_tail and has_acc:
        return RecursionInfo(
            scheme=RecursionScheme.ACCUMULATOR,
            depth=1, call_count=call_count, is_tail=True,
            offsets=offsets, has_accumulator=True,
        )

    if is_tail:
        return RecursionInfo(
            scheme=RecursionScheme.TAIL,
            depth=1, call_count=call_count, is_tail=True,
            offsets=offsets, has_accumulator=False,
        )

    if call_count >= 2 and len(offsets) <= 1:
        return RecursionInfo(
            scheme=RecursionScheme.TREE,
            depth=None, call_count=call_count, is_tail=False,
            offsets=offsets, has_accumulator=False,
        )

    if offsets and offsets == set(range(1, max(offsets) + 1)):
        k = max(offsets)
        scheme = RecursionScheme.PRIMITIVE if k == 1 else RecursionScheme.COURSE_OF_VALUES
        return RecursionInfo(
            scheme=scheme,
            depth=k, call_count=call_count, is_tail=False,
            offsets=offsets, has_accumulator=False,
        )

    return RecursionInfo(
        scheme=RecursionScheme.UNKNOWN,
        depth=None, call_count=call_count, is_tail=is_tail,
        offsets=offsets, has_accumulator=has_acc,
    )


def _collect_recursive_calls_ast(stmts, fname: str) -> List[ast.Call]:
    """Collect all self-recursive Call nodes from a statement list."""
    calls: List[ast.Call] = []
    for node in ast.walk(ast.Module(body=stmts if isinstance(stmts, list) else [stmts],
                                     type_ignores=[])):
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == fname):
            calls.append(node)
    return calls


def _extract_offset_ast(call: ast.Call, params: list) -> Optional[int]:
    """Extract the recursion offset from f(n - k) calls."""
    if not call.args:
        return None
    arg = call.args[0]
    if (isinstance(arg, ast.BinOp) and isinstance(arg.op, ast.Sub)
            and isinstance(arg.left, ast.Name) and isinstance(arg.right, ast.Constant)
            and isinstance(arg.right.value, int)):
        return arg.right.value
    return None


def _is_tail_position_ast(body, fname: str) -> bool:
    """Check if all recursive calls are in tail position."""
    for stmt in reversed(body):
        if isinstance(stmt, ast.Return) and stmt.value is not None:
            return _is_tail_call(stmt.value, fname)
        if isinstance(stmt, ast.If):
            t = _is_tail_position_ast(stmt.body, fname)
            f = _is_tail_position_ast(stmt.orelse, fname) if stmt.orelse else True
            return t and f
    return False


def _is_tail_call(expr, fname: str) -> bool:
    """Check if an expression is a direct recursive call (tail position)."""
    if isinstance(expr, ast.Call) and isinstance(expr.func, ast.Name):
        return expr.func.id == fname
    if isinstance(expr, ast.IfExp):
        return _is_tail_call(expr.body, fname) or _is_tail_call(expr.orelse, fname)
    return False


def _has_accumulator_ast(calls: List[ast.Call], params: list) -> bool:
    """Detect accumulator-passing style in recursive calls."""
    param_names = {a.arg for a in params}
    for call in calls:
        for arg in call.args:
            if isinstance(arg, ast.BinOp):
                if (isinstance(arg.left, ast.Name) and arg.left.id in param_names
                        and isinstance(arg.op, (ast.Add, ast.Mult, ast.Sub))):
                    return True
                if (isinstance(arg.right, ast.Name) and arg.right.id in param_names
                        and isinstance(arg.op, (ast.Add, ast.Mult, ast.Sub))):
                    return True
    return False


# ═══════════════════════════════════════════════════════════
# §4  Extended Fold Recognition for Builtins
#     (ported from g13_compilation §11, adapted for Z3 terms)
# ═══════════════════════════════════════════════════════════

# Maps builtin reducer names → (Z3 op constant, identity element maker)
_EXTENDED_FOLD_OPS: Dict[str, Tuple[int, Callable]] = {}


def _init_fold_ops():
    """Initialize extended fold op table (deferred to avoid import-time Z3)."""
    global _EXTENDED_FOLD_OPS
    if _EXTENDED_FOLD_OPS:
        return
    _EXTENDED_FOLD_OPS.update({
        'prod': (MUL, lambda T: T.mkint(1)),
        'math.prod': (MUL, lambda T: T.mkint(1)),
        'sum': (ADD, lambda T: T.mkint(0)),
        'any': (BITOR, lambda T: T.mkbool(False)),
        'all': (BITAND, lambda T: T.mkbool(True)),
    })


def try_fold_builtin(name: str, args: List[Any], T: 'Theory') -> Optional[Any]:
    """Try to compile a builtin reducer call as a Z3 fold term.

    Recognizes prod(xs), math.prod(xs), any(xs), all(xs) and compiles
    them as fold terms using Theory.fold(), paralleling how sum() already
    works in compiler.py for range-based folds.
    """
    _init_fold_ops()
    if name not in _EXTENDED_FOLD_OPS or len(args) != 1:
        return None
    op, mk_init = _EXTENDED_FOLD_OPS[name]
    fn = T.shared_fn(f'fold_{name}', 2)
    return fn(mk_init(T), args[0])


# ═══════════════════════════════════════════════════════════
# §5  Lambda Body Compilation (Defunctionalization)
#     (inspired by g13_compilation §6/§7)
# ═══════════════════════════════════════════════════════════

def compile_lambda_body(node: ast.Lambda, env: Env) -> Any:
    """Compile a lambda expression by building a Z3 function from its body.

    Instead of returning a fresh opaque symbol, this compiles the lambda
    body in a sub-environment where the parameters are fresh Z3 constants,
    then wraps the result as a shared function application.

    This enables equivalence checking between lambdas with identical semantics.
    """
    T = env.T
    params = [a.arg for a in node.args.args]
    if not params:
        # Nullary lambda: just compile the body
        return compile_expr(node.body, env)

    # Create sub-env with fresh param symbols
    sub = env.copy()
    sub.depth += 1
    param_syms = []
    for p in params:
        sym = T.fresh(f'lam_{p}')
        sub.put(p, sym)
        param_syms.append(sym)

    body_val = compile_expr(node.body, sub)

    # Create a canonical function symbol from the lambda's AST structure
    body_hash = _stable_hash(ast.dump(node.body))
    fn = T.shared_fn(f'lambda_{body_hash}', len(params))
    return fn(*param_syms)


# ═══════════════════════════════════════════════════════════
# §6  AnnAssign / Match / TryStar Statement Handlers
#     (fills gaps identified by g13_compilation §10)
# ═══════════════════════════════════════════════════════════

def exec_ann_assign(stmt: ast.AnnAssign, env: Env) -> None:
    """Handle annotated assignment: `x: int = 5`.

    Compiles the value (if present) and binds it in the environment,
    treating it identically to a plain assignment.
    """
    if stmt.value is not None:
        val = compile_expr(stmt.value, env)
        val = _ensure_z3(val, env.T)
        if isinstance(stmt.target, ast.Name):
            env.put(stmt.target.id, val)
        else:
            _assign_target(stmt.target, val, env)


def exec_match_stmt(stmt, env: Env) -> None:
    """Handle match/case (structural pattern matching, Python 3.10+).

    Compiles the subject, then for each case arm compiles the body
    under a guard derived from the pattern. Uses fresh symbols for
    pattern-bound variables.
    """
    T = env.T
    if not hasattr(ast, 'Match'):
        return
    subject = compile_expr(stmt.subject, env)
    for case in stmt.cases:
        ce = env.copy()
        _bind_match_pattern(case.pattern, subject, ce)
        exec_stmts(case.body, ce)
        # Merge back modified vars
        for k, v in ce.bindings.items():
            if v is not env.get(k):
                env.put(k, v)


def _bind_match_pattern(pattern, subject, env: Env) -> None:
    """Bind names from a match pattern into the environment."""
    T = env.T
    if not hasattr(ast, 'MatchAs'):
        return

    if isinstance(pattern, ast.MatchAs):
        if pattern.name:
            env.put(pattern.name, subject)
    elif isinstance(pattern, ast.MatchValue):
        pass  # No bindings
    elif isinstance(pattern, ast.MatchSequence):
        for i, p in enumerate(pattern.patterns):
            elem = T.binop(GETITEM, subject, T.mkint(i))
            _bind_match_pattern(p, elem, env)
    elif isinstance(pattern, ast.MatchMapping):
        for key, p in zip(pattern.keys, pattern.patterns):
            k = compile_expr(key, env)
            v = T.binop(GETITEM, subject, k)
            _bind_match_pattern(p, v, env)
    elif isinstance(pattern, ast.MatchStar):
        if pattern.name:
            env.put(pattern.name, T.fresh(f'star_{pattern.name}'))
    elif isinstance(pattern, ast.MatchOr):
        if pattern.patterns:
            _bind_match_pattern(pattern.patterns[0], subject, env)


def extract_match_sections(stmt, env: Env, guard: Any) -> List[Section]:
    """Extract presheaf sections from match/case for section-mode compilation."""
    T = env.T
    if not hasattr(ast, 'Match'):
        return []
    sections: List[Section] = []
    subject = compile_expr(stmt.subject, env)

    for ci, case in enumerate(stmt.cases):
        ce = env.copy()
        _bind_match_pattern(case.pattern, subject, ce)
        # Each case arm gets a fresh guard based on pattern index
        T._uid += 1
        case_guard_fn = _z3.Function(f'match_case_{ci}_{T._uid}', T.S, _z3.BoolSort())
        case_guard = _z3.And(guard, case_guard_fn(subject))

        if case.guard is not None:
            extra = T.truthy(compile_expr(case.guard, ce))
            case_guard = _z3.And(case_guard, extra)

        case_secs = extract_sections(case.body, ce, case_guard)
        sections.extend(case_secs)

    return sections


def exec_assert_as_guard(stmt: ast.Assert, env: Env) -> Any:
    """Compile an assert statement's test as a Z3 guard condition.

    Returns a Z3 boolean that can be conjuncted with section guards
    to narrow the verified space.
    """
    T = env.T
    return T.truthy(compile_expr(stmt.test, env))


# ═══════════════════════════════════════════════════════════
# §7  Enhanced exec_one with Extended Statement Coverage
# ═══════════════════════════════════════════════════════════

def exec_one_ext(stmt, env: Env) -> None:
    """Extended statement executor that handles AnnAssign, Match, TryStar.

    Falls through to compiler.exec_one for all standard statements.
    Call this instead of exec_one when you need extended coverage.
    """
    if isinstance(stmt, ast.AnnAssign):
        exec_ann_assign(stmt, env)
        return

    if hasattr(ast, 'Match') and isinstance(stmt, ast.Match):
        exec_match_stmt(stmt, env)
        return

    # TryStar (Python 3.11+): handle like regular Try
    if hasattr(ast, 'TryStar') and isinstance(stmt, ast.TryStar):
        exec_stmts(stmt.body, env)
        for handler in getattr(stmt, 'handlers', []):
            he = env.copy()
            if handler.name:
                he.put(handler.name, env.T.fresh(f'exc_{handler.name}'))
            exec_stmts(handler.body, he)
        if hasattr(stmt, 'orelse') and stmt.orelse:
            exec_stmts(stmt.orelse, env)
        if hasattr(stmt, 'finalbody') and stmt.finalbody:
            exec_stmts(stmt.finalbody, env)
        return

    exec_one(stmt, env)


def extract_sections_ext(stmts: list, env: Env,
                         guard: Any = None) -> List[Section]:
    """Extended section extraction with Match/AnnAssign/Assert support.

    Wraps compiler.extract_sections but intercepts Match and AnnAssign
    statements, and converts Assert into guard constraints.
    """
    T = env.T
    if guard is None:
        guard = _z3.BoolVal(True)
    stmts = _skip_doc(stmts)
    sections: List[Section] = []

    for i, stmt in enumerate(stmts):
        if isinstance(stmt, ast.Return):
            val = compile_expr(stmt.value, env) if stmt.value else T.mknone()
            sections.append(Section(guard=guard, term=val))
            return sections

        if isinstance(stmt, ast.AnnAssign):
            exec_ann_assign(stmt, env)
            continue

        if isinstance(stmt, ast.Assert):
            assertion_guard = exec_assert_as_guard(stmt, env)
            guard = _z3.And(guard, assertion_guard)
            continue

        if hasattr(ast, 'Match') and isinstance(stmt, ast.Match):
            msecs = extract_match_sections(stmt, env, guard)
            if msecs:
                sections.extend(msecs)
                return sections
            exec_match_stmt(stmt, env)
            continue

        if isinstance(stmt, ast.If):
            cond = T.truthy(compile_expr(stmt.test, env))
            tg = _z3.And(guard, cond)
            fg = _z3.And(guard, _z3.Not(cond))
            tr = _has_ret(stmt.body)
            fr = _has_ret(stmt.orelse) if stmt.orelse else False
            if tr:
                sections.extend(extract_sections_ext(stmt.body, env.copy(), tg))
            if fr and stmt.orelse:
                sections.extend(extract_sections_ext(stmt.orelse, env.copy(), fg))
            if tr and fr:
                return sections
            if tr:
                re = env.copy()
                if stmt.orelse:
                    for s in stmt.orelse:
                        exec_one_ext(s, re)
                sections.extend(extract_sections_ext(stmts[i+1:], re, fg))
                return sections
            if fr:
                re = env.copy()
                for s in stmt.body:
                    exec_one_ext(s, re)
                sections.extend(extract_sections_ext(stmts[i+1:], re, tg))
                return sections
            te, fe = env.copy(), env.copy()
            for s in stmt.body:
                exec_one_ext(s, te)
            if stmt.orelse:
                for s in stmt.orelse:
                    exec_one_ext(s, fe)
            from .compiler import _merge_envs
            _merge_envs(env, te, fe, cond)
            continue

        exec_one_ext(stmt, env)

    return sections


# ═══════════════════════════════════════════════════════════
# §8  Batch Compilation Utilities
# ═══════════════════════════════════════════════════════════

@dataclass
class CompilationResult:
    """Result of compiling a Python function source to Z3 sections."""
    source: str
    sections: Optional[List[Section]]
    params: Optional[List[Any]]
    func_name: str
    recursion_info: Optional[RecursionInfo]
    metrics: Optional[SectionMetrics]
    coverage: CoverageReport
    error: Optional[str]


def compile_func_ext(source: str, T: Theory) -> CompilationResult:
    """Extended compile_func that also computes recursion info and metrics.

    Wraps compiler.compile_func and enriches the result with:
    - Recursion scheme classification
    - Section complexity metrics
    - Coverage analysis
    """
    coverage = analyze_coverage(source)

    try:
        result = compile_func(source, T)
    except Exception as e:
        return CompilationResult(
            source=source, sections=None, params=None,
            func_name='', recursion_info=None, metrics=None,
            coverage=coverage, error=str(e),
        )

    if result is None:
        return CompilationResult(
            source=source, sections=None, params=None,
            func_name='', recursion_info=None, metrics=None,
            coverage=coverage, error='compile_func returned None',
        )

    secs, params, func_node = result
    rec_info = classify_recursion_ast(func_node)
    metrics = compute_section_metrics(secs)

    return CompilationResult(
        source=source, sections=secs, params=params,
        func_name=func_node.name, recursion_info=rec_info,
        metrics=metrics, coverage=coverage, error=None,
    )


def batch_compile(sources: List[str], T: Theory) -> List[CompilationResult]:
    """Compile multiple Python function sources and return enriched results."""
    return [compile_func_ext(src, T) for src in sources]
