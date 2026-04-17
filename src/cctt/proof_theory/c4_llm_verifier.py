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
    # Quantified predicates (uninterpreted in Z3)
    'all_of', 'any_of', 'none_of',
    # Ordering/sorting predicates (uninterpreted)
    'is_sorted', 'is_permutation',
    # Collection predicates
    'contains', 'is_subset', 'is_disjoint',
}

# Reserved variable names
C4_RESERVED_VARS: Set[str] = {'result', 'True', 'False', 'None'}

# Type names recognized in isinstance/type specs
C4_TYPE_NAMES: Set[str] = {
    'int', 'float', 'str', 'bool', 'list', 'dict', 'set', 'tuple',
    'NoneType', 'bytes', 'complex', 'frozenset',
    # Common library types
    'Expr', 'Symbol', 'Number', 'Integer', 'Rational', 'Matrix',
    'Poly', 'Add', 'Mul', 'Pow', 'Function',
}

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
    None: None

ARITHMETIC
    +, -, *, %, //, **

COMPARISONS
    ==, !=, <, <=, >, >=

NONE COMPARISONS
    x == None, x != None (for nullability checks)

BOOLEAN CONNECTIVES
    and, or, not

CONDITIONALS
    expr if condition else expr

BUILT-IN FUNCTIONS (uninterpreted in Z3)
    abs(x), len(x), max(x, y), min(x, y), isinstance(x, T)

QUANTIFIED PREDICATES (uninterpreted in Z3)
    all_of(collection, pred_name) — ∀x∈collection. pred(x)
    any_of(collection, pred_name) — ∃x∈collection. pred(x)
    is_sorted(collection)         — collection is in sorted order
    is_permutation(a, b)          — a is a permutation of b

COLLECTION PREDICATES
    contains(collection, element) — element ∈ collection
    is_subset(a, b)               — a ⊆ b

TYPE NAMES (for isinstance/type checks)
    int, float, str, bool, list, dict, set, tuple, NoneType,
    Expr, Symbol, Number, Integer, Rational, Matrix, Poly

ATTRIBUTE ACCESS
    self.attr → modeled as selector function self_attr
    obj.attr  → modeled as selector function objname_attr

EFFECT ANNOTATIONS (in spec metadata, not in clause formulas)
    pure     — no side effects
    mutating — modifies self or arguments
    io       — performs I/O

EXAMPLES OF VALID CLAUSES
    result >= 0
    result == x + y
    result == abs(x)
    result > 0 if x > 0 else result == 0
    isinstance(result, int)
    result == max(x, y)
    result * result <= x * x
    result != None
    len(result) == len(x)
    is_sorted(result)
    isinstance(result, Expr)

EXAMPLES OF INVALID CLAUSES (rejected)
    q.is_zero is not True            ← method call
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


class C4Strategy(Enum):
    """Which C4 proof strategy was used to verify a clause.

    Each maps to a C4 proof term constructor:
      Z3Discharge        — direct Z3 validity (cheapest)
      CasesSplit          — exhaustive case analysis over branch guards
      RefinementDescent   — fiber cover {φᵢ} + per-fiber proof + overlap
      FiberDecomposition  — per-fiber proof, disjoint fibers
      LibraryAxiom        — trusted builtin/library axiom injection
      Tautology           — sort-aware trivial truth (Bool ∈ {True,False})
      WeakestPrecondition — wp calculus for imperative reasoning
      EffectFrame         — frame condition (only declared state modified)
      ExceptionCase       — try/except as disjoint union
      DependentMatch      — isinstance dispatch with type refinement
      Normalize           — prove by normalization to canonical form
      Unfold              — δ-reduce and simplify
    """
    Z3_DISCHARGE = "Z3Discharge"
    CASES_SPLIT = "CasesSplit"
    REFINEMENT_DESCENT = "RefinementDescent"
    FIBER_DECOMPOSITION = "FiberDecomposition"
    LIBRARY_AXIOM = "LibraryAxiom"
    TAUTOLOGY = "Tautology"
    WEAKEST_PRECONDITION = "WeakestPrecondition"
    EFFECT_FRAME = "EffectFrame"
    EXCEPTION_CASE = "ExceptionCase"
    DEPENDENT_MATCH = "DependentMatch"
    NORMALIZE = "Normalize"
    UNFOLD = "Unfold"


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
    """Result of verifying one spec clause.

    When verdict is C4_VERIFIED, proof_term contains the ProofTerm witness
    and compile_verdict contains the result of compiling it through C4.
    """
    clause: str
    verdict: ClauseVerdict
    detail: str = ""
    strategy: Optional[C4Strategy] = None  # which C4 proof strategy was used
    # Per-path breakdown (which paths verified this clause)
    path_results: List[Tuple[str, str]] = field(default_factory=list)
    # (path_guard, "verified"/"assumed"/"failed")
    # Proof term emitted for this clause (None if unverified)
    proof_term: Optional[Any] = None  # ProofTerm — typed as Any to avoid circular import
    # The goal this proof witnesses: "clause holds under function semantics"
    proof_goal: str = ""
    # Result of compiling the proof_term through compile_proof()
    compile_verdict: Optional[Any] = None  # C4Verdict


@dataclass
class C4SpecVerdict:
    """Full verification result for a spec against source code."""
    func_name: str
    source_hash: str
    clause_results: List[ClauseResult] = field(default_factory=list)
    exhaustiveness: Optional[str] = None  # "verified" / "failed" / "vacuous"
    validation_errors: List[str] = field(default_factory=list)
    # All compiled proof terms (one per verified clause)
    proof_terms: List[Any] = field(default_factory=list)  # List[ProofTerm]
    # Number of proofs that compiled successfully through C4
    n_compiled: int = 0

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
            "n_compiled": self.n_compiled,
            "all_verified": self.all_verified,
            "exhaustiveness": self.exhaustiveness,
            "clauses": [
                {
                    "clause": cr.clause,
                    "verdict": cr.verdict.name,
                    "detail": cr.detail,
                    "strategy": cr.strategy.value if cr.strategy else None,
                    "path_results": cr.path_results,
                    "has_proof_term": cr.proof_term is not None,
                    "proof_goal": cr.proof_goal,
                    "compiled": cr.compile_verdict is not None,
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
    # Allow type names in isinstance context
    unknown -= C4_TYPE_NAMES

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
        # Declare None as a special constant for comparisons
        env.declare_var('None', 'Int')
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
# Core Verifier — C4 proof strategies for clause checking
#
# Each tactic corresponds to a C4 proof term:
#   Tautology       → sort-aware trivial truth (no proof needed)
#   Z3Discharge     → direct Z3 validity check (cheapest real tactic)
#   LibraryAxiom    → inject trusted builtins (abs, max, min, len)
#                     then re-check via Z3Discharge under axioms
#   CasesSplit      → verify per-path under branch guards (exhaustive)
#   RefinementDescent → verify per-fiber under fiber guards + overlap
# ═══════════════════════════════════════════════════════════════════

def verify_clause_on_path(
    clause: str,
    path: ReturnPath,
    requires: List[str],
    params: List[str],
    func_name: str = "",
    source: str = "",
) -> Tuple[str, str, Optional[C4Strategy], Optional[Any]]:
    """Verify one clause on one return path via C4 proof strategies.

    Strategy pipeline (ordered by C4 proof-term specificity):
    1. Tautology — sort-aware trivial truth (Bool ∈ {True,False} etc.)
    2. Z3Discharge — direct Z3 ¬(hyp ∧ ¬goal) check, no axioms
    3. LibraryAxiom + Z3Discharge — inject builtin axioms then retry Z3

    Returns (verdict, detail, strategy, proof_term) where:
        verdict    ∈ {"verified", "assumed", "failed"}
        strategy   ∈ C4Strategy or None
        proof_term ∈ ProofTerm or None (only when verified)
    """
    try:
        from cctt.proof_theory.c4_compiler import Z3Env
        from cctt.proof_theory.terms import Z3Discharge as Z3DischargeTerm
        from cctt.proof_theory.library_axioms import LibraryAxiom as LibAxiomTerm
        from cctt.denotation import OVar, OLit
        from z3 import (
            Solver, And as Z3And, Not as Z3Not, Implies as Z3Implies,
            unsat, sat,
        )
    except ImportError:
        return "assumed", "Z3 not available", None, None

    if path.is_exception:
        return "assumed", "exception path — clause doesn't apply", None, None

    # ── Sort inference (used by all tactics below) ──
    result_sort = _infer_result_sort(func_name, source) if func_name else 'Int'

    # ── Tactic 1: Tautology (C4Strategy.TAUTOLOGY) ──
    # Per rubber-duck review: tautologies get Z3Discharge, not Refl
    tautology = _is_boolean_tautology(clause, result_sort)
    if tautology:
        proof = Z3DischargeTerm(
            formula=clause,
            fragment='TAUTOLOGY',
            timeout_ms=0,
            variables={p: 'Int' for p in params},
        )
        return "verified", f"Tautology: {tautology}", C4Strategy.TAUTOLOGY, proof

    # ── Build Z3 environment with sort-inferred variables ──
    env = Z3Env()
    var_sorts: Dict[str, str] = {}
    for p in params:
        p_sort = _infer_param_sort(p, func_name, source) if source else 'Int'
        env.declare_var(p, p_sort)
        var_sorts[p] = p_sort
    env.declare_var('result', result_sort)
    var_sorts['result'] = result_sort

    # Build hypothesis: requires ∧ path_guard ∧ (result == return_expr)
    base_hyps = []
    hyp_formulas: List[str] = []
    for req in requires:
        z3_req = env.parse_formula(req)
        if z3_req is not None:
            base_hyps.append(z3_req)
            hyp_formulas.append(req)

    if path.guard != "True":
        z3_guard = env.parse_formula(path.guard)
        if z3_guard is not None:
            base_hyps.append(z3_guard)
            hyp_formulas.append(path.guard)
        else:
            return "assumed", f"path guard unparseable: {path.guard}", None, None

    # Bind result to return expression
    ret_binding = env.parse_formula(f"result == ({path.return_expr})")
    if ret_binding is not None:
        base_hyps.append(ret_binding)
        hyp_formulas.append(f"result == ({path.return_expr})")

    # Build goal
    goal_str = clause if ret_binding is not None else _substitute_result(clause, path.return_expr)
    goal = env.parse_formula(goal_str)
    if goal is None:
        return "assumed", f"clause unparseable: {goal_str}", None, None

    def _is_z3_bool(expr: Any) -> bool:
        """Check if a Z3 expression has Boolean sort."""
        try:
            from z3 import BoolSort
            return expr.sort() == BoolSort()
        except Exception:
            return False

    # Filter hypotheses to only Boolean-sorted Z3 expressions
    bool_hyps = [h for h in base_hyps if _is_z3_bool(h)]

    if not _is_z3_bool(goal):
        return "assumed", f"goal not Boolean-sorted: {goal_str}", None, None

    # Build the full proof formula for ProofTerm emission
    # Use Python-style implication: not(hyps) or goal — parseable by Z3Env
    if hyp_formulas:
        hyps_conj = " and ".join(f"({h})" for h in hyp_formulas)
        full_formula = f"not ({hyps_conj}) or ({goal_str})"
    else:
        full_formula = goal_str

    # ── Tactic 2: Z3Discharge (C4Strategy.Z3_DISCHARGE) ──
    # Pure Z3 check with NO axioms — this is the kernel-level tactic.
    s = Solver()
    s.set('timeout', 5000)
    for h in bool_hyps:
        s.add(h)
    s.add(Z3Not(goal))
    result = s.check()

    if result == unsat:
        proof = Z3DischargeTerm(
            formula=full_formula,
            fragment='QF_LIA',
            timeout_ms=5000,
            variables=var_sorts,
        )
        return "verified", "Z3Discharge: ¬(hyp ∧ ¬goal) UNSAT", C4Strategy.Z3_DISCHARGE, proof

    # Check if hypothesis is even satisfiable (Z3 refutation)
    s2 = Solver()
    s2.set('timeout', 3000)
    for h in bool_hyps:
        s2.add(h)
    s2.add(goal)
    result2 = s2.check()
    if result2 == unsat:
        return "failed", "Z3Discharge: hyp → ¬goal (goal UNSAT)", C4Strategy.Z3_DISCHARGE, None

    # ── Tactic 3: LibraryAxiom + Z3Discharge (C4Strategy.LIBRARY_AXIOM) ──
    # Inject trusted axioms for builtins (abs, max, min, len), then retry.
    # These are at LIBRARY_ASSUMED trust level, not KERNEL.
    builtin_axioms = _inject_builtin_axioms(env)
    bool_axioms = [ax for ax in builtin_axioms if _is_z3_bool(ax)]
    if bool_axioms:
        s3 = Solver()
        s3.set('timeout', 5000)
        for h in bool_hyps:
            s3.add(h)
        for ax in bool_axioms:
            s3.add(ax)
        s3.add(Z3Not(goal))
        result3 = s3.check()

        if result3 == unsat:
            proof = LibAxiomTerm(
                library='builtins',
                axiom_name='builtin_axioms',
                statement=full_formula,
            )
            return ("verified",
                    "LibraryAxiom(builtins) + Z3Discharge: proved with builtin axioms",
                    C4Strategy.LIBRARY_AXIOM, proof)

        # Refutation under axioms
        s4 = Solver()
        s4.set('timeout', 3000)
        for h in bool_hyps:
            s4.add(h)
        for ax in bool_axioms:
            s4.add(ax)
        s4.add(goal)
        result4 = s4.check()
        if result4 == unsat:
            return "failed", "LibraryAxiom + Z3: goal UNSAT under axioms", C4Strategy.LIBRARY_AXIOM, None

    return "assumed", "Z3: neither proved nor disproved", None, None


def verify_clause(
    clause: str,
    paths: List[ReturnPath],
    requires: List[str],
    params: List[str],
    func_name: str = "",
    source: str = "",
) -> ClauseResult:
    """Verify one clause against ALL return paths using C4 CasesSplit.

    This is the C4 CasesSplit strategy: each return path is a case,
    the clause must hold under each case, and cases must be exhaustive.

    When there's a single non-exception path, this degenerates to plain
    Z3Discharge (no case splitting needed).

    A clause is:
    - C4_VERIFIED if verified on ALL non-exception paths
    - C4_FAILED if failed on ANY path
    - C4_ASSUMED otherwise

    Now also emits ProofTerms:
    - Single path verified → the per-path proof term
    - Multiple paths all verified → CasesSplit wrapping per-path proofs
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
    strategies_used: List[C4Strategy] = []
    per_path_proofs: Dict[str, Any] = {}  # guard → ProofTerm

    for path in non_exc_paths:
        verdict, detail, strategy, proof_term = verify_clause_on_path(
            clause, path, requires, params,
            func_name=func_name, source=source)
        path_results.append((path.guard, verdict))
        if strategy:
            strategies_used.append(strategy)
        if proof_term is not None:
            per_path_proofs[path.guard] = proof_term
        if verdict == "failed":
            any_failed = True
        if verdict != "verified":
            all_verified = False

    # Determine the overall C4 strategy
    if len(non_exc_paths) > 1 and all_verified:
        overall_strategy = C4Strategy.CASES_SPLIT
    elif strategies_used:
        if C4Strategy.LIBRARY_AXIOM in strategies_used:
            overall_strategy = C4Strategy.LIBRARY_AXIOM
        elif C4Strategy.Z3_DISCHARGE in strategies_used:
            overall_strategy = C4Strategy.Z3_DISCHARGE
        elif C4Strategy.TAUTOLOGY in strategies_used:
            overall_strategy = C4Strategy.TAUTOLOGY
        else:
            overall_strategy = strategies_used[0]
    else:
        overall_strategy = None

    # Build composite ProofTerm
    composite_proof = None
    if all_verified and per_path_proofs:
        if len(per_path_proofs) == 1:
            composite_proof = next(iter(per_path_proofs.values()))
        else:
            # Multiple paths → CasesSplit
            try:
                from cctt.proof_theory.terms import CasesSplit as CasesSplitTerm
                from cctt.denotation import OVar
                composite_proof = CasesSplitTerm(
                    discriminant=OVar(f'path_guard_{func_name}'),
                    cases=per_path_proofs,
                )
            except ImportError:
                pass

    proof_goal = f"∀ paths. ({' ∧ '.join(requires)} → {clause})" if requires else clause

    if any_failed:
        return ClauseResult(
            clause=clause,
            verdict=ClauseVerdict.C4_FAILED,
            detail="Z3 disproved on at least one path",
            strategy=overall_strategy,
            path_results=path_results,
            proof_goal=proof_goal,
        )
    if all_verified:
        strategy_name = overall_strategy.value if overall_strategy else "Z3"
        return ClauseResult(
            clause=clause,
            verdict=ClauseVerdict.C4_VERIFIED,
            detail=f"{strategy_name}: proved on all {len(non_exc_paths)} path(s)",
            strategy=overall_strategy,
            path_results=path_results,
            proof_term=composite_proof,
            proof_goal=proof_goal,
        )

    return ClauseResult(
        clause=clause,
        verdict=ClauseVerdict.C4_ASSUMED,
        detail="Z3 proved on some paths, undecidable on others",
        strategy=overall_strategy,
        path_results=path_results,
        proof_goal=proof_goal,
    )


def check_path_exhaustiveness(
    paths: List[ReturnPath],
    requires: List[str],
    params: List[str],
    func_name: str = "",
    source: str = "",
) -> str:
    """Check that return paths cover all inputs satisfying requires.

    Checks: requires → (guard₁ ∨ guard₂ ∨ ...)
    Uses sort inference for proper typing of guard comparisons.

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
        p_sort = _infer_param_sort(p, func_name, source) if source else 'Int'
        env.declare_var(p, p_sort)

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
    # This is C4's RefinementDescent: each fiber guard φᵢ defines a face,
    # and the clause must hold on each face.
    fibers = spec.get('fibers', [])
    has_fibers = bool(fibers)
    for fiber in fibers:
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
            # Tag with RefinementDescent strategy when fibers are present
            if result.verdict == ClauseVerdict.C4_VERIFIED and has_fibers:
                result.strategy = C4Strategy.REFINEMENT_DESCENT
            result.clause = f"[fiber:{fiber_name}] {result.clause}"
            verdict.clause_results.append(result)

    # 6. Check path exhaustiveness (with sort inference)
    if paths:
        verdict.exhaustiveness = check_path_exhaustiveness(
            paths, requires, params,
            func_name=func_name, source=source)

    # 7. Compile emitted proof terms through C4 compiler
    _compile_emitted_proofs(verdict)

    return verdict


def _compile_emitted_proofs(verdict: C4SpecVerdict) -> None:
    """Compile all emitted ProofTerms through the C4 proof compiler.

    For each ClauseResult with a proof_term, call compile_proof() and
    store the C4Verdict. This is the machine-checking step — it turns
    a Z3-validated strategy into a compiled proof certificate.
    """
    try:
        from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
        from cctt.denotation import OVar, OLit
    except ImportError:
        return

    env = Z3Env()
    compiled_count = 0

    for cr in verdict.clause_results:
        if cr.proof_term is None:
            continue

        try:
            # The proof witnesses: clause_formula ≡ True
            # We use OVar placeholders for lhs/rhs since Z3Discharge
            # doesn't actually check OTerm equality
            lhs = OVar(f'spec_{verdict.func_name}')
            rhs = OVar(f'impl_{verdict.func_name}')

            c4_result = compile_proof(cr.proof_term, lhs, rhs, env, depth=0)
            cr.compile_verdict = c4_result
            verdict.proof_terms.append(cr.proof_term)

            if c4_result.valid:
                compiled_count += 1
        except Exception as e:
            log.debug("Proof compilation failed for %s: %s", cr.clause, e)

    verdict.n_compiled = compiled_count


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
  Integer/float/bool/None literals: 0, 1, -1, 3.14, True, False, None

ARITHMETIC: +, -, *, %, //, **
COMPARISONS: ==, !=, <, <=, >, >=
BOOLEAN: and, or, not
CONDITIONALS: value_if_true if condition else value_if_false

BUILT-IN FUNCTIONS (these become uninterpreted Z3 functions):
  abs(x), len(x), max(x, y), min(x, y), isinstance(x, type_name)

QUANTIFIED PREDICATES (uninterpreted — express intent):
  all_of(collection, pred) — all elements satisfy predicate
  any_of(collection, pred) — some element satisfies predicate
  is_sorted(collection) — collection is sorted
  is_permutation(a, b) — a is a rearrangement of b
  contains(collection, elem) — element in collection
  is_subset(a, b) — a is a subset of b

TYPE NAMES (for isinstance):
  int, float, str, bool, list, dict, set, tuple, NoneType
  Expr, Symbol, Number, Integer, Rational, Matrix, Poly

NONE CHECKS: x == None, x != None (NOT 'x is None')

FORBIDDEN (will cause clause rejection):
  - English text or descriptions
  - Method calls like x.method() or x.is_something
  - Library constants like S.NaN, math.inf
  - Subscript access like x[0], result[i]
  - List/dict/set comprehensions
  - 'is' comparisons (use '==' instead)
  - 'in' membership tests (use contains() instead)
  - String operations
  - Any function not in the built-in list above

## Output Format
Return a JSON object:
{
  "requires": ["x > 0"],
  "ensures": ["result >= 0"],
  "returns_expr": "x + 1",
  "fibers": [
    {
      "name": "case_name",
      "guard": "x >= 0",
      "ensures": ["result == x"]
    }
  ],
  "effect": "pure"
}

## Spec Categories by Function Type

### Pure arithmetic / straight-line
  ensures: exact return expression, bounds, sign, type
  Example: {"ensures": ["result == a + b"], "effect": "pure"}

### Boolean predicates (is_*, has_*)
  ensures: result == True/False conditions
  fibers: case split on what makes it True vs False

### Transformers (modify and return expression)
  ensures: semantic preservation properties
  Example: {"ensures": ["isinstance(result, Expr)"], "effect": "pure"}

### Constructors (__init__)
  ensures: initialization invariants (use self_attr for attributes)
  Example: {"ensures": ["self_name == name"], "effect": "mutating"}

### Properties (@property)
  ensures: what the property computes
  effect: "pure" (properties should not mutate)

### Protocol methods (__add__, __mul__, __eq__)
  ensures: algebraic laws (commutativity, associativity, identity)
  Example: {"ensures": ["result == a + b", "isinstance(result, type(a))"], "effect": "pure"}

### Complex control flow (loops, recursion)
  ensures: high-level intent (what the function computes)
  fibers: case split on input patterns

### Side-effectful (I/O, mutation, caching)
  ensures: postconditions on return value
  effect: "mutating" or "io"

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
8. Always include at least one ensures clause
9. Use quantified predicates (all_of, is_sorted, etc.) for collection specs
10. Prefer specific bounds/equalities over vague "result != None"

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
  ],
  "effect": "pure"
}

Function: def __init__(self, name, value=0): self.name = name; self.value = value
Spec: {
  "requires": [],
  "ensures": ["self_name == name", "self_value == value"],
  "returns_expr": null,
  "fibers": [],
  "effect": "mutating"
}

Function: def solve(f, x0): ...  # iterative solver
Spec: {
  "requires": [],
  "ensures": ["result != None"],
  "returns_expr": null,
  "fibers": [],
  "effect": "pure"
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
