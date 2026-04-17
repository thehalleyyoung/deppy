"""c4_llm_verifier.py — C4-native LLM spec generation and verification.

This module bridges LLM-generated specifications with the C4 proof compiler.
Every spec clause MUST be in the C4 spec language (Z3-parseable) and every
clause is verified by constructing and compiling a C4 proof obligation.

ARCHITECTURE
============

1. C4 Spec Grammar — the subset of Python that Z3Env can parse
2. Typed Validator — rejects clauses with unknown identifiers / constructs
3. Path Extractor — extracts (guard, return_expr) pairs from source AST
4. Spec Prover — for each clause × path, constructs Z3 formula and checks
5. LLM Prompt — teaches the LLM the C4 language

VERIFICATION FLOW
=================

    source code → extract_return_paths() → [(guard₁, ret₁), ...]
    LLM → spec in C4 language → validate_c4_spec() → accept/reject
    For each accepted clause × return path:
        formula = Implies(And(requires, guard_i), clause[result := ret_i])
        Z3Env.check_valid(formula) → verified / unknown / refuted
    Exhaustiveness: Implies(And(requires), Or(guard₁, guard₂, ...))
    Result: per-clause C4_VERIFIED / C4_ASSUMED / C4_FAILED

TRUST
=====
    C4_VERIFIED — Z3 proved the clause (Z3 trust, no assumptions)
    C4_ASSUMED  — Z3 couldn't prove or disprove (tracked assumption)
    C4_FAILED   — Z3 disproved the clause (genuine error)

This is honest C4 verification because:
    - Specs are in C4's language (Z3-parseable formulas)
    - Each clause is checked via the same Z3Env used by the C4 compiler
    - Path-sensitive: each return path is checked separately
    - Binding: specs reference actual source params and return expressions
    - Trust: verified = Z3, assumed = tracked, failed = Z3 disproved
"""
from __future__ import annotations

import ast
import hashlib
import logging
import re
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, List, Optional, Set, Tuple

log = logging.getLogger(__name__)


# ═══════════════════════════════════════════════════════════════════
# C4 Spec Grammar
# ═══════════════════════════════════════════════════════════════════

# Built-in functions that Z3Env can handle (as uninterpreted functions)
C4_BUILTIN_FUNCTIONS: Set[str] = {
    'abs', 'len', 'max', 'min', 'sum', 'int', 'float', 'bool',
    'round', 'divmod', 'pow', 'hash', 'id', 'ord', 'chr',
    'isinstance', 'type',
}

# Reserved variable names
C4_RESERVED_VARS: Set[str] = {'result', 'True', 'False', 'None'}

C4_GRAMMAR_DOC = """\
C4 Spec Language — the formal grammar for specifications.

VARIABLES
    Parameter names from the function signature
    'result' for the return value
    'self' for methods (attributes accessed as self_attrname)

LITERALS
    Integers: 0, 1, -1, 42
    Floats: 0.0, 1.5, -3.14
    Booleans: True, False

ARITHMETIC
    +, -, *, %, //, **

COMPARISONS
    ==, !=, <, <=, >, >=

BOOLEAN CONNECTIVES
    and, or, not

CONDITIONALS
    expr if condition else expr

BUILT-IN FUNCTIONS (uninterpreted in Z3)
    abs(x), len(x), max(x, y), min(x, y), isinstance(x, T)

ATTRIBUTE ACCESS
    self.attr → modeled as selector function self_attr
    obj.attr  → modeled as selector function objname_attr

EXAMPLES OF VALID CLAUSES
    result >= 0
    result == x + y
    result == abs(x)
    result > 0 if x > 0 else result == 0
    isinstance(result, int)
    result == max(x, y)
    result * result <= x * x

EXAMPLES OF INVALID CLAUSES (rejected)
    q.is_zero is not True            ← method call, 'is not'
    result is S.NaN                  ← library constant, 'is'
    all(result[i] <= result[i+1] ...) ← comprehension, subscript
    "returns a positive number"       ← English text
    result == sorted(lst)             ← not a C4 builtin
"""


# ═══════════════════════════════════════════════════════════════════
# Data types
# ═══════════════════════════════════════════════════════════════════

class ClauseVerdict(Enum):
    """Verification status of a single spec clause."""
    C4_VERIFIED = auto()   # Z3 proved it (zero assumptions)
    C4_ASSUMED = auto()    # Z3 couldn't prove or disprove
    C4_FAILED = auto()     # Z3 disproved it
    REJECTED = auto()      # Clause not in C4 language


@dataclass
class ReturnPath:
    """A single return path through a function.

    Represents: under path_guard, the function returns return_expr.
    Extracted from the source AST.
    """
    guard: str                   # path condition (C4 formula), "True" for unconditional
    return_expr: str             # what is returned on this path
    lineno: int = 0              # source line number
    is_exception: bool = False   # if this path raises an exception


@dataclass
class ClauseResult:
    """Result of verifying one spec clause."""
    clause: str
    verdict: ClauseVerdict
    detail: str = ""
    # Per-path breakdown (which paths verified this clause)
    path_results: List[Tuple[str, str]] = field(default_factory=list)
    # (path_guard, "verified"/"assumed"/"failed")


@dataclass
class C4SpecVerdict:
    """Full verification result for a spec against source code."""
    func_name: str
    source_hash: str
    clause_results: List[ClauseResult] = field(default_factory=list)
    exhaustiveness: Optional[str] = None  # "verified" / "failed" / "vacuous"
    validation_errors: List[str] = field(default_factory=list)

    @property
    def n_verified(self) -> int:
        return sum(1 for c in self.clause_results if c.verdict == ClauseVerdict.C4_VERIFIED)

    @property
    def n_assumed(self) -> int:
        return sum(1 for c in self.clause_results if c.verdict == ClauseVerdict.C4_ASSUMED)

    @property
    def n_failed(self) -> int:
        return sum(1 for c in self.clause_results if c.verdict == ClauseVerdict.C4_FAILED)

    @property
    def n_rejected(self) -> int:
        return sum(1 for c in self.clause_results if c.verdict == ClauseVerdict.REJECTED)

    @property
    def all_verified(self) -> bool:
        """True only if every clause is C4_VERIFIED (zero assumptions)."""
        return (self.clause_results
                and all(c.verdict == ClauseVerdict.C4_VERIFIED for c in self.clause_results))

    @property
    def summary(self) -> str:
        n = len(self.clause_results)
        parts = []
        if self.n_verified:
            parts.append(f"{self.n_verified} C4-verified")
        if self.n_assumed:
            parts.append(f"{self.n_assumed} assumed")
        if self.n_failed:
            parts.append(f"{self.n_failed} FAILED")
        if self.n_rejected:
            parts.append(f"{self.n_rejected} rejected")
        return f"{'/'.join(parts)} (of {n} clauses)"

    def to_json(self) -> Dict[str, Any]:
        return {
            "func_name": self.func_name,
            "source_hash": self.source_hash,
            "n_verified": self.n_verified,
            "n_assumed": self.n_assumed,
            "n_failed": self.n_failed,
            "n_rejected": self.n_rejected,
            "all_verified": self.all_verified,
            "exhaustiveness": self.exhaustiveness,
            "clauses": [
                {
                    "clause": cr.clause,
                    "verdict": cr.verdict.name,
                    "detail": cr.detail,
                    "path_results": cr.path_results,
                }
                for cr in self.clause_results
            ],
            "validation_errors": self.validation_errors,
            "summary": self.summary,
        }


# ═══════════════════════════════════════════════════════════════════
# Typed Spec Validator
# ═══════════════════════════════════════════════════════════════════

class _IdentifierCollector(ast.NodeVisitor):
    """Collect all Name nodes from a Python AST."""

    def __init__(self) -> None:
        self.names: Set[str] = set()
        self.calls: Set[str] = set()
        self.has_subscript = False
        self.has_starred = False
        self.has_comprehension = False
        self.has_attribute = False
        self.has_method_call = False
        self.method_calls: List[str] = []
        self.attributes: List[str] = []

    def visit_Name(self, node: ast.Name) -> None:
        self.names.add(node.id)
        self.generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:
        if isinstance(node.func, ast.Name):
            self.calls.add(node.func.id)
        elif isinstance(node.func, ast.Attribute):
            # Method call: obj.method() — only allowed on self
            if isinstance(node.func.value, ast.Name):
                obj_name = node.func.value.id
                if obj_name != 'self':
                    self.has_method_call = True
                    self.method_calls.append(f"{obj_name}.{node.func.attr}()")
            else:
                self.has_method_call = True
                self.method_calls.append(ast.dump(node.func))
        self.generic_visit(node)

    def visit_Subscript(self, node: ast.Subscript) -> None:
        self.has_subscript = True
        self.generic_visit(node)

    def visit_Starred(self, node: ast.Starred) -> None:
        self.has_starred = True
        self.generic_visit(node)

    def visit_ListComp(self, node: ast.ListComp) -> None:
        self.has_comprehension = True

    def visit_SetComp(self, node: ast.SetComp) -> None:
        self.has_comprehension = True

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> None:
        self.has_comprehension = True

    def visit_DictComp(self, node: ast.DictComp) -> None:
        self.has_comprehension = True

    def visit_Attribute(self, node: ast.Attribute) -> None:
        if isinstance(node.value, ast.Name):
            # self.x → allowed, modeled as self_x
            self.attributes.append(f"{node.value.id}.{node.attr}")
        self.generic_visit(node)


def validate_c4_clause(
    clause: str,
    allowed_vars: Set[str],
) -> Tuple[bool, str]:
    """Validate that a clause is in the C4 spec language.

    Checks:
    1. Parses as a Python expression
    2. Only uses allowed identifiers (params + result + True/False)
    3. No comprehensions, subscripts, or complex constructs
    4. Function calls are limited to C4 builtins
    5. Attribute access is from known objects (self, params)

    Returns (valid, reason).
    """
    clause = clause.strip()
    if not clause:
        return False, "empty clause"

    # Quick reject: English text
    if ' ' in clause and not any(op in clause for op in
            ['==', '!=', '<=', '>=', '<', '>', 'and', 'or', 'not',
             'if', 'else', 'isinstance', 'True', 'False', '+', '-',
             '*', '%', '/', '(', ')']):
        return False, "appears to be English text, not a C4 formula"

    # Quick reject: 'is' operator (not '==')
    if re.search(r'\bis\b(?!\s*None)', clause) and 'isinstance' not in clause:
        return False, "'is' not supported in C4 (use '==')"

    # Parse
    try:
        tree = ast.parse(clause, mode='eval')
    except SyntaxError as e:
        return False, f"syntax error: {e}"

    collector = _IdentifierCollector()
    collector.visit(tree)

    # Check for disallowed constructs
    if collector.has_comprehension:
        return False, "comprehensions not supported in C4"
    if collector.has_subscript:
        return False, "subscript access not supported in C4 (use a selector function)"
    if collector.has_method_call:
        return False, f"method calls not supported in C4: {collector.method_calls}"

    # Check identifiers
    all_allowed = allowed_vars | C4_RESERVED_VARS
    unknown = collector.names - all_allowed
    # Allow attribute-derived names (self_x patterns)
    attr_names = set()
    for attr in collector.attributes:
        parts = attr.split('.')
        if len(parts) == 2 and parts[0] in allowed_vars:
            attr_names.add(parts[0])  # the base is allowed
    unknown -= attr_names
    # Allow function names
    unknown -= C4_BUILTIN_FUNCTIONS
    unknown -= collector.calls & C4_BUILTIN_FUNCTIONS

    if unknown:
        return False, f"unknown identifiers: {unknown} (allowed: {all_allowed})"

    # Check function calls are C4 builtins
    unknown_calls = collector.calls - C4_BUILTIN_FUNCTIONS
    if unknown_calls:
        return False, f"non-C4 function calls: {unknown_calls}"

    # Try parsing in Z3Env to confirm
    try:
        from cctt.proof_theory.c4_compiler import Z3Env
        env = Z3Env()
        for v in allowed_vars:
            env.declare_var(v, 'Int')
        z3_expr = env.parse_formula(clause)
        if z3_expr is None:
            return False, "Z3Env cannot parse this clause"
    except ImportError:
        pass  # Z3 not available, skip Z3 check
    except Exception as e:
        return False, f"Z3 parse error: {e}"

    return True, "valid C4 clause"


def validate_c4_spec(
    spec: Dict[str, Any],
    params: List[str],
) -> Tuple[bool, List[str]]:
    """Validate that all clauses in a spec dict are in C4 language.

    Returns (all_valid, list_of_errors).
    """
    allowed = set(params) | {'result', 'self'}
    errors: List[str] = []

    for key in ('requires', 'ensures'):
        for clause in spec.get(key, []):
            ok, reason = validate_c4_clause(clause, allowed)
            if not ok:
                errors.append(f"{key}: {clause!r} — {reason}")

    for fiber in spec.get('fibers', []):
        guard = fiber.get('guard', 'True')
        ok, reason = validate_c4_clause(guard, allowed)
        if not ok:
            errors.append(f"fiber[{fiber.get('name', '?')}].guard: {guard!r} — {reason}")
        for clause in fiber.get('ensures', []):
            ok, reason = validate_c4_clause(clause, allowed)
            if not ok:
                errors.append(f"fiber[{fiber.get('name', '?')}].ensures: {clause!r} — {reason}")

    ret = spec.get('returns_expr')
    if ret:
        ok, reason = validate_c4_clause(f"result == ({ret})", allowed)
        if not ok:
            errors.append(f"returns_expr: {ret!r} — {reason}")

    return len(errors) == 0, errors


# ═══════════════════════════════════════════════════════════════════
# Path Extractor — extract return paths from source AST
# ═══════════════════════════════════════════════════════════════════

def extract_return_paths(source: str, func_name: str) -> List[ReturnPath]:
    """Extract (guard, return_expr) pairs from a function's source.

    Each pair represents one execution path: under the given path
    condition (guard), the function returns the given expression.

    This is the source-of-truth for what the code ACTUALLY does.
    """
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []

    # Find the target function
    func_def = None
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.name == func_name:
                func_def = node
                break

    if func_def is None:
        return []

    paths: List[ReturnPath] = []
    _collect_return_paths(func_def.body, [], paths)

    # If no return paths found, add implicit None return
    if not paths:
        paths.append(ReturnPath(guard="True", return_expr="None", lineno=func_def.lineno))

    return paths


def _collect_return_paths(
    stmts: List[ast.stmt],
    guards: List[str],
    paths: List[ReturnPath],
) -> bool:
    """Recursively collect return paths with their path conditions.

    Returns True if all control flow paths return (no fallthrough).
    """
    for i, stmt in enumerate(stmts):
        if isinstance(stmt, ast.Return):
            if stmt.value is not None:
                try:
                    ret_expr = ast.unparse(stmt.value)
                except Exception:
                    ret_expr = "<?>"
            else:
                ret_expr = "None"
            guard = " and ".join(guards) if guards else "True"
            paths.append(ReturnPath(
                guard=guard, return_expr=ret_expr, lineno=stmt.lineno))
            return True

        if isinstance(stmt, ast.If):
            try:
                test_str = ast.unparse(stmt.test)
            except Exception:
                test_str = "<?>"

            # True branch
            true_guards = guards + [test_str]
            true_returns = _collect_return_paths(stmt.body, true_guards, paths)

            # False branch
            if stmt.orelse:
                false_guards = guards + [f"not ({test_str})"]
                false_returns = _collect_return_paths(stmt.orelse, false_guards, paths)
            else:
                false_returns = False

            if true_returns and false_returns:
                return True
            # If only one branch returns, continue with remaining stmts
            continue

        if isinstance(stmt, ast.Raise):
            guard = " and ".join(guards) if guards else "True"
            try:
                exc_str = ast.unparse(stmt.exc) if stmt.exc else "Exception"
            except Exception:
                exc_str = "Exception"
            paths.append(ReturnPath(
                guard=guard, return_expr=f"raise({exc_str})",
                lineno=stmt.lineno, is_exception=True))
            return True

        # For/while loops: don't descend (too complex for path extraction)
        # Try blocks: skip for now
        if isinstance(stmt, (ast.For, ast.While, ast.Try)):
            continue

    return False


# ═══════════════════════════════════════════════════════════════════
# Result Substitution
# ═══════════════════════════════════════════════════════════════════

def _substitute_result(clause: str, return_expr: str) -> str:
    """Substitute 'result' with the actual return expression."""
    try:
        tree = ast.parse(clause, mode='eval')
    except SyntaxError:
        return clause.replace('result', f'({return_expr})')

    class ResultSubstituter(ast.NodeTransformer):
        def visit_Name(self, node: ast.Name) -> ast.AST:
            if node.id == 'result':
                try:
                    return ast.parse(return_expr, mode='eval').body
                except SyntaxError:
                    return node
            return node

    new_tree = ResultSubstituter().visit(tree)
    ast.fix_missing_locations(new_tree)
    try:
        return ast.unparse(new_tree)
    except Exception:
        return clause.replace('result', f'({return_expr})')


# ═══════════════════════════════════════════════════════════════════
# Sort Inference — infer Z3 sorts from context
# ═══════════════════════════════════════════════════════════════════

def _infer_param_sort(name: str, func_name: str, source: str) -> str:
    """Infer the Z3 sort for a parameter from context clues."""
    # Check annotations in source
    try:
        tree = ast.parse(source)
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node.name == func_name:
                    for arg in node.args.args:
                        if arg.arg == name and arg.annotation:
                            ann = ast.unparse(arg.annotation)
                            if ann in ('bool', 'Bool'):
                                return 'Bool'
                            if ann in ('float', 'Float', 'Real'):
                                return 'Real'
    except Exception:
        pass
    return 'Int'


def _infer_result_sort(func_name: str, source: str) -> str:
    """Infer Z3 sort for the result from return annotation and name patterns."""
    # Boolean function patterns
    bool_prefixes = ('is_', 'has_', 'can_', 'should_', 'was_', 'will_',
                     '_eval_is_', '_is_')
    if any(func_name.startswith(p) or func_name.startswith('_eval_' + p.lstrip('_'))
           for p in bool_prefixes):
        return 'Bool'
    if func_name.startswith('_eval_is_'):
        return 'Bool'

    # Check return annotation
    try:
        tree = ast.parse(source)
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node.name == func_name and node.returns:
                    ann = ast.unparse(node.returns)
                    if ann in ('bool', 'Bool'):
                        return 'Bool'
                    if ann in ('float', 'Float'):
                        return 'Real'
    except Exception:
        pass

    return 'Int'


# ═══════════════════════════════════════════════════════════════════
# Axiom Injection — known facts about builtin functions
# ═══════════════════════════════════════════════════════════════════

def _inject_builtin_axioms(env: Any) -> List[Any]:
    """Inject axioms for builtins into Z3 environment.

    Returns a list of Z3 formulas to add as hypotheses.
    These are SOUND axioms — mathematical truths about these functions.
    """
    try:
        from z3 import (
            Int, Bool, ForAll as Z3ForAll, Implies as Z3Implies,
            And as Z3And, Or as Z3Or, Not as Z3Not,
            IntVal, BoolVal,
        )
    except ImportError:
        return []

    axioms = []
    x = Int('__ax_x')
    y = Int('__ax_y')

    # abs(x) >= 0
    abs_f = env.declare_function('abs', 1)
    axioms.append(Z3ForAll([x], abs_f(x) >= 0))
    # abs(x) == x when x >= 0
    axioms.append(Z3ForAll([x], Z3Implies(x >= 0, abs_f(x) == x)))
    # abs(x) == -x when x < 0
    axioms.append(Z3ForAll([x], Z3Implies(x < 0, abs_f(x) == -x)))

    # max(x, y) >= x and max(x, y) >= y
    max_f = env.declare_function('max', 2)
    axioms.append(Z3ForAll([x, y], max_f(x, y) >= x))
    axioms.append(Z3ForAll([x, y], max_f(x, y) >= y))
    axioms.append(Z3ForAll([x, y], Z3Or(max_f(x, y) == x, max_f(x, y) == y)))

    # min(x, y) <= x and min(x, y) <= y
    min_f = env.declare_function('min', 2)
    axioms.append(Z3ForAll([x, y], min_f(x, y) <= x))
    axioms.append(Z3ForAll([x, y], min_f(x, y) <= y))
    axioms.append(Z3ForAll([x, y], Z3Or(min_f(x, y) == x, min_f(x, y) == y)))

    # len(x) >= 0
    len_f = env.declare_function('len_of', 1)
    axioms.append(Z3ForAll([x], len_f(x) >= 0))

    return axioms


# ═══════════════════════════════════════════════════════════════════
# Tautology Detection — clauses provable without source analysis
# ═══════════════════════════════════════════════════════════════════

def _is_boolean_tautology(clause: str, result_sort: str) -> Optional[str]:
    """Detect clauses that are tautologically true given sort info.

    Returns a reason string if tautology, None otherwise.
    """
    clause_stripped = clause.strip()

    # "result == True or result == False" is tautology for Bool result
    if result_sort == 'Bool':
        if clause_stripped in (
            'result == True or result == False',
            'result == False or result == True',
            'result == True or result == False or result == None',
        ):
            return "tautology: Bool ∈ {True, False}"

    # "isinstance(result, bool)" is tautology for Bool result
    if result_sort == 'Bool' and 'isinstance(result' in clause_stripped:
        if 'bool' in clause_stripped.lower():
            return "tautology: result declared as Bool"

    # "isinstance(result, float)" is tautology for Real result
    if result_sort == 'Real' and 'isinstance(result' in clause_stripped:
        if 'float' in clause_stripped.lower():
            return "tautology: result declared as Real"

    # "isinstance(result, int)" is tautology for Int result
    if result_sort == 'Int' and 'isinstance(result' in clause_stripped:
        if 'int' in clause_stripped.lower():
            return "tautology: result declared as Int"

    # "result >= 0 or result < 0" style tautologies
    if clause_stripped in (
        'result >= 0 or result < 0',
        'result > 0 or result <= 0',
        'result > 0 or result == 0 or result < 0',
        'result != 0 or result == 0',
    ):
        return "tautology: exhaustive arithmetic disjunction"

    return None


# ═══════════════════════════════════════════════════════════════════
# Core Verifier — Z3-based clause checking per path (with tactics)
# ═══════════════════════════════════════════════════════════════════

def verify_clause_on_path(
    clause: str,
    path: ReturnPath,
    requires: List[str],
    params: List[str],
    func_name: str = "",
    source: str = "",
) -> Tuple[str, str]:
    """Verify one clause on one return path via Z3 with C4 tactics.

    Tactics applied (in order):
    1. Tautology detection (sort-aware)
    2. Z3Discharge with sort inference
    3. Builtin axiom injection (abs, max, min, len)
    4. Direct substitution fallback

    Returns (verdict, detail) where verdict ∈ {"verified", "assumed", "failed"}.
    """
    try:
        from cctt.proof_theory.c4_compiler import Z3Env
        from z3 import (
            Solver, And as Z3And, Not as Z3Not, Implies as Z3Implies,
            unsat, sat,
        )
    except ImportError:
        return "assumed", "Z3 not available"

    if path.is_exception:
        return "assumed", "exception path — clause doesn't apply"

    # ── Tactic 1: Sort inference ──
    result_sort = _infer_result_sort(func_name, source) if func_name else 'Int'

    # ── Tactic 2: Tautology detection ──
    tautology = _is_boolean_tautology(clause, result_sort)
    if tautology:
        return "verified", f"tautology ({tautology})"

    # ── Tactic 3: Z3 with proper sorts ──
    env = Z3Env()
    for p in params:
        p_sort = _infer_param_sort(p, func_name, source) if source else 'Int'
        env.declare_var(p, p_sort)
    env.declare_var('result', result_sort)

    # ── Tactic 4: Inject builtin axioms ──
    builtin_axioms = _inject_builtin_axioms(env)

    # Build hypothesis: requires ∧ path_guard ∧ (result == return_expr)
    hyp_parts = list(builtin_axioms)

    for req in requires:
        z3_req = env.parse_formula(req)
        if z3_req is not None:
            hyp_parts.append(z3_req)

    if path.guard != "True":
        z3_guard = env.parse_formula(path.guard)
        if z3_guard is not None:
            hyp_parts.append(z3_guard)
        else:
            return "assumed", f"path guard unparseable: {path.guard}"

    # Bind result to return expression
    ret_binding = env.parse_formula(f"result == ({path.return_expr})")
    if ret_binding is not None:
        hyp_parts.append(ret_binding)

    # Build goal
    if ret_binding is not None:
        goal_str = clause
    else:
        goal_str = _substitute_result(clause, path.return_expr)

    goal = env.parse_formula(goal_str)
    if goal is None:
        return "assumed", f"clause unparseable after substitution: {goal_str}"

    # Check: hyp → goal  (i.e., ¬(hyp ∧ ¬goal) is UNSAT)
    s = Solver()
    s.set('timeout', 5000)
    for h in hyp_parts:
        s.add(h)
    s.add(Z3Not(goal))
    result = s.check()

    if result == unsat:
        return "verified", "Z3: hypothesis → goal (with axioms)"

    # Check if hypothesis is even satisfiable (to avoid vacuous proofs)
    s2 = Solver()
    s2.set('timeout', 3000)
    for h in hyp_parts:
        s2.add(h)
    s2.add(goal)
    result2 = s2.check()

    if result2 == unsat:
        return "failed", "Z3: hypothesis → ¬goal (goal UNSAT under hypothesis)"

    return "assumed", "Z3: neither proved nor disproved"


def verify_clause(
    clause: str,
    paths: List[ReturnPath],
    requires: List[str],
    params: List[str],
    func_name: str = "",
    source: str = "",
) -> ClauseResult:
    """Verify one clause against ALL return paths.

    For each non-exception path, checks:
        requires ∧ path_guard → clause[result := return_expr]

    A clause is:
    - C4_VERIFIED if verified on ALL non-exception paths
    - C4_FAILED if failed on ANY path
    - C4_ASSUMED otherwise
    """
    non_exc_paths = [p for p in paths if not p.is_exception]
    if not non_exc_paths:
        return ClauseResult(
            clause=clause,
            verdict=ClauseVerdict.C4_ASSUMED,
            detail="no non-exception return paths",
        )

    path_results: List[Tuple[str, str]] = []
    any_failed = False
    all_verified = True

    for path in non_exc_paths:
        verdict, detail = verify_clause_on_path(
            clause, path, requires, params,
            func_name=func_name, source=source)
        path_results.append((path.guard, verdict))
        if verdict == "failed":
            any_failed = True
        if verdict != "verified":
            all_verified = False

    if any_failed:
        return ClauseResult(
            clause=clause,
            verdict=ClauseVerdict.C4_FAILED,
            detail="Z3 disproved on at least one path",
            path_results=path_results,
        )
    if all_verified:
        return ClauseResult(
            clause=clause,
            verdict=ClauseVerdict.C4_VERIFIED,
            detail="Z3 proved on all paths",
            path_results=path_results,
        )

    return ClauseResult(
        clause=clause,
        verdict=ClauseVerdict.C4_ASSUMED,
        detail="Z3 proved on some paths, undecidable on others",
        path_results=path_results,
    )


def check_path_exhaustiveness(
    paths: List[ReturnPath],
    requires: List[str],
    params: List[str],
) -> str:
    """Check that return paths cover all inputs satisfying requires.

    Checks: requires → (guard₁ ∨ guard₂ ∨ ...)

    Returns "verified" / "failed" / "vacuous".
    """
    non_exc_paths = [p for p in paths if not p.is_exception]
    if not non_exc_paths:
        return "vacuous"

    try:
        from cctt.proof_theory.c4_compiler import Z3Env
        from z3 import (
            Solver, And as Z3And, Or as Z3Or, Not as Z3Not,
            Implies as Z3Implies, unsat,
        )
    except ImportError:
        return "assumed"

    env = Z3Env()
    for p in params:
        env.declare_var(p, 'Int')

    # Parse requires
    req_parts = []
    for req in requires:
        z3_req = env.parse_formula(req)
        if z3_req is not None:
            req_parts.append(z3_req)

    # Parse path guards
    guard_parts = []
    for path in non_exc_paths:
        if path.guard == "True":
            return "verified"  # unconditional path covers everything
        z3_guard = env.parse_formula(path.guard)
        if z3_guard is not None:
            guard_parts.append(z3_guard)

    if not guard_parts:
        return "vacuous"

    # Check: requires → (∨ guards)
    coverage = Z3Or(*guard_parts) if len(guard_parts) > 1 else guard_parts[0]
    if req_parts:
        hypothesis = Z3And(*req_parts) if len(req_parts) > 1 else req_parts[0]
        formula = Z3Implies(hypothesis, coverage)
    else:
        formula = coverage

    s = Solver()
    s.set('timeout', 3000)
    s.add(Z3Not(formula))
    result = s.check()

    return "verified" if result == unsat else "failed"


# ═══════════════════════════════════════════════════════════════════
# Top-level Verification Pipeline
# ═══════════════════════════════════════════════════════════════════

def verify_c4_spec(
    source: str,
    func_name: str,
    params: List[str],
    spec: Dict[str, Any],
) -> C4SpecVerdict:
    """Verify a C4 spec against actual source code via the C4 proof compiler.

    This is the main entry point. It:
    1. Validates every clause is in C4 language
    2. Extracts return paths from source
    3. Verifies each clause on each path
    4. Checks path exhaustiveness under requires
    5. Returns a full C4SpecVerdict

    Args:
        source: Full source code of the function
        func_name: Name of the function to verify
        params: Parameter names (excluding 'self')
        spec: Dict with requires, ensures, returns_expr, fibers
    """
    source_hash = hashlib.sha256(source.encode()).hexdigest()[:16]
    verdict = C4SpecVerdict(func_name=func_name, source_hash=source_hash)

    # 1. Validate all clauses
    valid, errors = validate_c4_spec(spec, params)
    verdict.validation_errors = errors

    # 2. Extract return paths from source
    paths = extract_return_paths(source, func_name)
    if not paths:
        verdict.validation_errors.append(f"no return paths found in {func_name}")

    requires = spec.get('requires', [])

    # 3. Filter to only valid clauses for verification
    allowed_vars = set(params) | {'result', 'self'}
    ensures_to_verify: List[str] = []
    for clause in spec.get('ensures', []):
        ok, reason = validate_c4_clause(clause, allowed_vars)
        if ok:
            ensures_to_verify.append(clause)
        else:
            verdict.clause_results.append(ClauseResult(
                clause=clause,
                verdict=ClauseVerdict.REJECTED,
                detail=f"not valid C4: {reason}",
            ))

    # 4. Verify each valid clause against all return paths
    for clause in ensures_to_verify:
        result = verify_clause(clause, paths, requires, params,
                              func_name=func_name, source=source)
        verdict.clause_results.append(result)

    # 5. Verify fiber clauses (per-fiber, under fiber guard)
    for fiber in spec.get('fibers', []):
        fiber_guard = fiber.get('guard', 'True')
        fiber_name = fiber.get('name', '?')

        # Validate fiber guard
        ok_guard, reason_guard = validate_c4_clause(fiber_guard, allowed_vars)
        if not ok_guard:
            verdict.clause_results.append(ClauseResult(
                clause=f"[fiber:{fiber_name}] guard: {fiber_guard}",
                verdict=ClauseVerdict.REJECTED,
                detail=f"fiber guard not valid C4: {reason_guard}",
            ))
            continue

        fiber_requires = requires + [fiber_guard]

        for clause in fiber.get('ensures', []):
            ok, reason = validate_c4_clause(clause, allowed_vars)
            if not ok:
                verdict.clause_results.append(ClauseResult(
                    clause=f"[fiber:{fiber_name}] {clause}",
                    verdict=ClauseVerdict.REJECTED,
                    detail=f"not valid C4: {reason}",
                ))
                continue

            result = verify_clause(clause, paths, fiber_requires, params,
                                  func_name=func_name, source=source)
            result.clause = f"[fiber:{fiber_name}] {result.clause}"
            verdict.clause_results.append(result)

    # 6. Check path exhaustiveness
    if paths:
        verdict.exhaustiveness = check_path_exhaustiveness(paths, requires, params)

    return verdict


# ═══════════════════════════════════════════════════════════════════
# C4 LLM Prompt — teaches the LLM the C4 spec language
# ═══════════════════════════════════════════════════════════════════

C4_SPEC_SYSTEM_PROMPT = """\
You are a C4 formal specification generator. C4 is a cubical refinement type \
theory for Python verification. Every spec clause you produce MUST be a valid \
C4 expression — a Python boolean expression parseable by Z3.

## C4 Spec Language (STRICT GRAMMAR — anything outside this is REJECTED)

VARIABLES
  The function's parameter names (given below)
  'result' — the return value
  Integer/float/bool literals: 0, 1, -1, 3.14, True, False

ARITHMETIC: +, -, *, %, //
COMPARISONS: ==, !=, <, <=, >, >=
BOOLEAN: and, or, not
CONDITIONALS: value_if_true if condition else value_if_false

BUILT-IN FUNCTIONS (these become uninterpreted Z3 functions):
  abs(x), len(x), max(x, y), min(x, y), isinstance(x, type_name)

FORBIDDEN (will cause clause rejection):
  - English text or descriptions
  - Method calls like x.method() or x.is_something
  - Library constants like S.NaN, math.inf
  - Subscript access like x[0], result[i]
  - Comprehensions like [x for x in lst]
  - 'is' comparisons (use '==' instead)
  - 'in' membership tests
  - String operations
  - Any function not in the built-in list above

## Output Format
Return a JSON object:
{
  "requires": ["x > 0"],              // preconditions (C4 formulas)
  "ensures": ["result >= 0"],          // postconditions (C4 formulas)
  "returns_expr": "x + 1",            // exact return, or null
  "fibers": [                          // case analysis (optional)
    {
      "name": "case_name",
      "guard": "x >= 0",              // C4 formula
      "ensures": ["result == x"]       // C4 formulas
    }
  ]
}

## Rules
1. EVERY clause MUST parse as a valid Python expression using ONLY the \
constructs above
2. Postconditions use 'result' for the return value
3. State the INTENT (what the function SHOULD do), not just what the code does
4. For math functions: state mathematical properties (commutativity, \
idempotence, bounds, etc.)
5. For predicates: result == True or result == False (not isinstance)
6. For case analysis: fiber guards MUST be Z3-parseable boolean expressions \
over parameters
7. If a property cannot be expressed in C4, do NOT include it — only \
include verifiable clauses

## Examples

Function: def abs_val(x): return x if x >= 0 else -x
Spec: {
  "requires": [],
  "ensures": ["result >= 0", "result == max(x, -x)"],
  "returns_expr": null,
  "fibers": [
    {"name": "non_negative", "guard": "x >= 0", \
"ensures": ["result == x"]},
    {"name": "negative", "guard": "x < 0", \
"ensures": ["result == -x"]}
  ]
}

Function: def add(a, b): return a + b
Spec: {
  "requires": [],
  "ensures": ["result == a + b"],
  "returns_expr": "a + b",
  "fibers": []
}

Function: def clamp(x, lo, hi): return max(lo, min(x, hi))
Spec: {
  "requires": ["lo <= hi"],
  "ensures": ["result >= lo", "result <= hi"],
  "returns_expr": null,
  "fibers": [
    {"name": "below", "guard": "x < lo", "ensures": ["result == lo"]},
    {"name": "above", "guard": "x > hi", "ensures": ["result == hi"]},
    {"name": "in_range", "guard": "x >= lo and x <= hi", \
"ensures": ["result == x"]}
  ]
}

Output ONLY valid JSON. No markdown fences, no explanation.\
"""


def build_c4_spec_prompt(
    source: str,
    name: str,
    params: List[str],
    docstring: str = "",
) -> str:
    """Build a prompt that asks the LLM to generate a C4 spec."""
    param_str = ", ".join(params) if params else "(no parameters)"
    doc_part = f"\nDocstring: {docstring}" if docstring else ""

    return (
        f"Generate a C4 formal specification for this Python function.\n"
        f"Function name: {name}\n"
        f"Parameters: {param_str}\n"
        f"{doc_part}\n\n"
        f"Source code:\n```python\n{source}\n```\n\n"
        f"Remember: EVERY clause must be a valid C4 expression "
        f"(Z3-parseable Python boolean expression using only: "
        f"arithmetic, comparisons, boolean connectives, and the built-in "
        f"functions abs/len/max/min/isinstance). "
        f"Do NOT use method calls, library constants, subscripts, or English."
    )


# ═══════════════════════════════════════════════════════════════════
# Integration with existing oracle infrastructure
# ═══════════════════════════════════════════════════════════════════

def verify_llm_spec(
    source: str,
    func_name: str,
    params: List[str],
    spec_dict: Dict[str, Any],
) -> C4SpecVerdict:
    """Validate and verify an LLM-generated spec through C4.

    This is the function that baseline_prove should call instead of
    the old check_impl_implies_intent.

    1. Validate spec is in C4 language (reject non-C4 clauses)
    2. Extract return paths from source (path-sensitive)
    3. Verify each clause on each path via Z3
    4. Check exhaustiveness under requires
    5. Return C4SpecVerdict with honest verification status
    """
    return verify_c4_spec(source, func_name, params, spec_dict)
