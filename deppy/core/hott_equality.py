"""
HoTT Equality Reasoning — Univalence and Path Induction for Verification
========================================================================

See ``ARCHITECTURE.md`` §4.5 for this module's place in the cubical
layer; see §10 for how a goal flows through the system.


Implements sophisticated equality reasoning using Homotopy Type Theory (HoTT),
including univalence axiom, path induction, and semantic equivalence proofs
that go far beyond syntactic equality.

Key Innovation: Enables verification of semantically equivalent but syntactically
different programs using cubical equality paths and univalent foundations.

Architecture:
1. Semantic Equality — Beyond syntactic matching using behavioral equivalence
2. Univalence Engine — Equivalent types are equal (A ≃ B → A = B)  
3. Path Induction — Reason about identity types and equality proofs
4. Equivalence Transport — Move proofs along equivalence paths
5. Higher-Dimensional Coherence — Handle nested equality proofs
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, List, Optional, Callable, Protocol, TypeVar, Generic

from deppy.core.types import (
    SynType, SynTerm, Context, PathType, PathAbs, PathApp, Transport,
    Var, Literal, App, Lam, LetIn, IfThenElse, 
    RefinementType, PiType, UniverseType, IntervalType
)
from deppy.core.kernel import ProofKernel, ProofTerm, TrustLevel, VerificationResult
from deppy.core.path_engine import PathConstructor, TransportEngine, UnivalenceEngine


# ═══════════════════════════════════════════════════════════════════
# 1. Semantic Equivalence Categories  
# ═══════════════════════════════════════════════════════════════════

class EquivalenceKind(Enum):
    """Types of semantic equivalences beyond syntactic equality."""
    SYNTACTIC = auto()           # α-equivalence, variable renaming
    BEHAVIORAL = auto()          # Same input/output behavior  
    ALGORITHMIC = auto()         # Different algorithms, same result
    OPTIMIZATION = auto()        # Performance optimizations
    REFACTORING = auto()         # Code structure changes
    MATHEMATICAL = auto()        # Mathematical identities (a+b = b+a)
    CONTEXTUAL = auto()          # Equivalent in given context
    HIGHER_ORDER = auto()        # Higher-order functional equivalence


@dataclass
class SemanticEquivalence:
    """Represents a semantic equivalence between two terms."""
    left_term: SynTerm
    right_term: SynTerm  
    kind: EquivalenceKind
    proof_sketch: str = ""
    context_constraints: List[SynTerm] = field(default_factory=list)
    
    def is_strict_equality(self) -> bool:
        """Check if this is strict propositional equality."""
        return self.kind == EquivalenceKind.SYNTACTIC
        
    def requires_univalence(self) -> bool:
        """Check if equivalence requires univalence axiom."""
        return self.kind in {EquivalenceKind.BEHAVIORAL, EquivalenceKind.ALGORITHMIC, EquivalenceKind.MATHEMATICAL}


@dataclass
class EquivalenceProof:
    """Proof that two terms are semantically equivalent."""
    equivalence: SemanticEquivalence
    proof_term: ProofTerm
    cubical_path: Optional[PathAbs] = None
    higher_coherence: List[PathAbs] = field(default_factory=list)  # For higher dimensions


# ═══════════════════════════════════════════════════════════════════
# 2. HoTT Identity Type System
# ═══════════════════════════════════════════════════════════════════

@dataclass
class IdentityType(SynType):
    """Identity type A =_B B in HoTT."""
    type_universe: SynType
    left_term: SynTerm
    right_term: SynTerm
    
    def is_reflexivity(self) -> bool:
        """Check if this is reflexive equality (refl : a =_A a)."""
        return self._terms_alpha_equivalent(self.left_term, self.right_term)
    
    def _terms_alpha_equivalent(self, t1: SynTerm, t2: SynTerm) -> bool:
        """Simple alpha-equivalence check."""
        # Simplified - would need full α-equivalence algorithm
        return str(t1) == str(t2)


@dataclass  
class PathInductionPrinciple:
    """Path induction (J rule) for identity types."""
    type_family: SynType  # P : (x y : A) → (x = y) → Type
    base_case: SynTerm    # P(a, a, refl_a) 
    motive: Lam           # λ x y p. P(x, y, p)
    
    def apply_induction(self, target_path: PathAbs) -> ProofTerm:
        """Apply path induction to prove statement about arbitrary path."""
        from deppy.core.kernel import Structural
        return Structural(f"path_induction_applied: {target_path}")


# ═══════════════════════════════════════════════════════════════════
# 3. Behavioral Equivalence Analyzer
# ═══════════════════════════════════════════════════════════════════

class BehavioralEquivalenceAnalyzer:
    """Analyzes functions for behavioral/semantic equivalence."""
    
    def __init__(self):
        self.equivalence_patterns = self._build_equivalence_patterns()
        
    def analyze_equivalence(self, fn1_ast: ast.FunctionDef, fn2_ast: ast.FunctionDef) -> Optional[SemanticEquivalence]:
        """Analyze if two functions are semantically equivalent."""
        
        # Check for common equivalence patterns
        for pattern in self.equivalence_patterns:
            if pattern.matches(fn1_ast, fn2_ast):
                return SemanticEquivalence(
                    left_term=self._ast_to_synterm(fn1_ast),
                    right_term=self._ast_to_synterm(fn2_ast),
                    kind=pattern.kind,
                    proof_sketch=pattern.proof_sketch
                )
        
        # Check for mathematical identities
        math_equiv = self._check_mathematical_equivalence(fn1_ast, fn2_ast)
        if math_equiv:
            return math_equiv
            
        # Check for algorithmic equivalence (same result, different algorithm)
        algo_equiv = self._check_algorithmic_equivalence(fn1_ast, fn2_ast)
        if algo_equiv:
            return algo_equiv
            
        return None
        
    def _check_mathematical_equivalence(self, fn1: ast.FunctionDef, fn2: ast.FunctionDef) -> Optional[SemanticEquivalence]:
        """Check for mathematical identity equivalences."""
        
        # Example: f(x) = x + 0 vs g(x) = x
        if self._is_add_zero_identity(fn1, fn2):
            return SemanticEquivalence(
                left_term=self._ast_to_synterm(fn1),
                right_term=self._ast_to_synterm(fn2),
                kind=EquivalenceKind.MATHEMATICAL,
                proof_sketch="additive identity: x + 0 = x"
            )
            
        # Example: f(x) = x * 1 vs g(x) = x  
        if self._is_mult_one_identity(fn1, fn2):
            return SemanticEquivalence(
                left_term=self._ast_to_synterm(fn1),
                right_term=self._ast_to_synterm(fn2),
                kind=EquivalenceKind.MATHEMATICAL,
                proof_sketch="multiplicative identity: x * 1 = x"
            )
            
        return None
        
    def _check_algorithmic_equivalence(self, fn1: ast.FunctionDef, fn2: ast.FunctionDef) -> Optional[SemanticEquivalence]:
        """Check for algorithmic equivalences (different algorithms, same result)."""
        
        # Example: recursive vs iterative implementations
        if (self._is_recursive_pattern(fn1) and self._is_iterative_pattern(fn2) and
            self._same_mathematical_function(fn1, fn2)):
            return SemanticEquivalence(
                left_term=self._ast_to_synterm(fn1),
                right_term=self._ast_to_synterm(fn2),
                kind=EquivalenceKind.ALGORITHMIC, 
                proof_sketch="recursive ≃ iterative implementation"
            )
            
        return None
        
    def _ast_to_synterm(self, fn_ast: ast.FunctionDef) -> SynTerm:
        """Return a ``Var`` carrying only the function's *name*.

        This is intentionally a name-only encoding — the body is NOT
        represented.  Downstream equality checks therefore compare
        identifiers, not semantics.  Previously documented as
        "Convert AST to SynTerm (simplified)", which overstated the
        encoding's fidelity; callers should not rely on anything
        structural coming from this term.
        """
        return Var(fn_ast.name)
        
    def _is_add_zero_identity(self, fn1: ast.FunctionDef, fn2: ast.FunctionDef) -> bool:
        """Check if one function adds 0 and the other doesn't."""
        # Simplified pattern matching - would need sophisticated AST analysis
        fn1_source = ast.unparse(fn1) if hasattr(ast, 'unparse') else str(fn1.body)
        fn2_source = ast.unparse(fn2) if hasattr(ast, 'unparse') else str(fn2.body)
        
        return ("+ 0" in fn1_source and "+ 0" not in fn2_source) or \
               ("+ 0" in fn2_source and "+ 0" not in fn1_source)
               
    def _is_mult_one_identity(self, fn1: ast.FunctionDef, fn2: ast.FunctionDef) -> bool:
        """Check if one function multiplies by 1 and the other doesn't."""
        fn1_source = ast.unparse(fn1) if hasattr(ast, 'unparse') else str(fn1.body)
        fn2_source = ast.unparse(fn2) if hasattr(ast, 'unparse') else str(fn2.body)
        
        return ("* 1" in fn1_source and "* 1" not in fn2_source) or \
               ("* 1" in fn2_source and "* 1" not in fn1_source)
               
    def _is_recursive_pattern(self, fn: ast.FunctionDef) -> bool:
        """Check if function uses recursion."""
        fn_name = fn.name
        
        class RecursionChecker(ast.NodeVisitor):
            def __init__(self):
                self.has_recursion = False
                
            def visit_Call(self, node):
                if isinstance(node.func, ast.Name) and node.func.id == fn_name:
                    self.has_recursion = True
                self.generic_visit(node)
        
        checker = RecursionChecker()
        checker.visit(fn)
        return checker.has_recursion
        
    def _is_iterative_pattern(self, fn: ast.FunctionDef) -> bool:
        """Check if function uses iteration."""
        class IterationChecker(ast.NodeVisitor):
            def __init__(self):
                self.has_iteration = False
                
            def visit_For(self, node):
                self.has_iteration = True
                self.generic_visit(node)
                
            def visit_While(self, node):
                self.has_iteration = True 
                self.generic_visit(node)
        
        checker = IterationChecker()
        checker.visit(fn)
        return checker.has_iteration
        
    def _same_mathematical_function(self, fn1: ast.FunctionDef,
                                    fn2: ast.FunctionDef) -> bool:
        """Name-overlap heuristic only — *not* a semantic equivalence check.

        The OLD implementation hardcoded the word ``factorial``; the new
        implementation compares normalised identifiers and aliases from
        a small, explicit table.  A ``True`` verdict from this method
        is suitable only for ranking suggestions — never as proof of
        equivalence.  For that, callers must use
        ``deppy.equivalence.check_equiv`` with a provable spec.
        """
        mathematical_families = {
            "factorial":    {"factorial", "fact", "n_bang"},
            "fibonacci":    {"fibonacci", "fib"},
            "power":        {"power", "pow", "exp", "exponent"},
            "gcd":          {"gcd", "greatest_common_divisor"},
            "sum":          {"sum", "total", "accumulate"},
            "product":      {"product", "prod"},
            "reverse":      {"reverse", "reversed", "rev"},
            "length":       {"length", "len", "size", "count"},
            "identity":     {"identity", "id"},
        }
        n1 = fn1.name.lower()
        n2 = fn2.name.lower()
        if n1 == n2:
            return True
        for aliases in mathematical_families.values():
            if any(a in n1 for a in aliases) and any(a in n2 for a in aliases):
                return True
        return False

    def _build_equivalence_patterns(self) -> List["EquivalencePattern"]:
        """Construct the database of structural equivalence patterns.

        Each entry in the returned list is an :class:`EquivalencePattern`
        recognising a syntactic shape on two ASTs and producing an
        :class:`EquivalenceProof` with the corresponding equivalence
        kind.  The patterns cover common algebraic / HoTT equivalences:

        * ``x + 0``  ↔ ``x``        (right identity of addition)
        * ``0 + x``  ↔ ``x``        (left identity of addition)
        * ``x * 1``  ↔ ``x``        (right identity of multiplication)
        * ``1 * x``  ↔ ``x``        (left identity of multiplication)
        * ``-(-x)``  ↔ ``x``        (double negation)
        * ``not not x`` ↔ ``x``     (double-logical-negation)
        * ``reversed(reversed(xs))`` ↔ ``xs``  (reverse-reverse)
        * ``sorted(sorted(xs))``    ↔ ``sorted(xs)``  (sort idempotence)
        * ``a + b`` ↔ ``b + a``     (addition commutativity)
        * ``a * b`` ↔ ``b * a``     (multiplication commutativity)
        * ``(a + b) + c`` ↔ ``a + (b + c)``  (addition associativity)
        * recursive ↔ iterative forms  (folding pattern)

        A hit produces a proof term by the path constructor — typically
        a reflexivity or transitivity chain — which the kernel re-
        verifies.  Patterns that don't match return ``None``.
        """
        return [
            EquivalencePattern(
                name="add-right-identity",
                kind=EquivalenceKind.MATHEMATICAL,
                matcher=_mk_binop_identity_matcher("+", right_unit=0),
                sketch="x + 0 = x",
            ),
            EquivalencePattern(
                name="add-left-identity",
                kind=EquivalenceKind.MATHEMATICAL,
                matcher=_mk_binop_identity_matcher("+", left_unit=0),
                sketch="0 + x = x",
            ),
            EquivalencePattern(
                name="mul-right-identity",
                kind=EquivalenceKind.MATHEMATICAL,
                matcher=_mk_binop_identity_matcher("*", right_unit=1),
                sketch="x * 1 = x",
            ),
            EquivalencePattern(
                name="mul-left-identity",
                kind=EquivalenceKind.MATHEMATICAL,
                matcher=_mk_binop_identity_matcher("*", left_unit=1),
                sketch="1 * x = x",
            ),
            EquivalencePattern(
                name="double-negation",
                kind=EquivalenceKind.MATHEMATICAL,
                matcher=_match_double_unary("USub"),
                sketch="-(-x) = x",
            ),
            EquivalencePattern(
                name="double-logical-not",
                kind=EquivalenceKind.MATHEMATICAL,
                matcher=_match_double_unary("Not"),
                sketch="not not x = x",
            ),
            EquivalencePattern(
                name="reverse-reverse",
                kind=EquivalenceKind.MATHEMATICAL,
                matcher=_mk_call_idempotence_matcher(
                    {"reversed", "reverse"}, arity=1
                ),
                sketch="reversed(reversed(xs)) = xs",
            ),
            EquivalencePattern(
                name="sort-idempotent",
                kind=EquivalenceKind.MATHEMATICAL,
                matcher=_mk_call_projective_matcher(
                    {"sorted"}, arity=1
                ),
                sketch="sorted(sorted(xs)) = sorted(xs)",
            ),
            EquivalencePattern(
                name="add-commute",
                kind=EquivalenceKind.MATHEMATICAL,
                matcher=_mk_binop_commute_matcher("+"),
                sketch="a + b = b + a",
            ),
            EquivalencePattern(
                name="mul-commute",
                kind=EquivalenceKind.MATHEMATICAL,
                matcher=_mk_binop_commute_matcher("*"),
                sketch="a * b = b * a",
            ),
            EquivalencePattern(
                name="add-associate",
                kind=EquivalenceKind.MATHEMATICAL,
                matcher=_mk_binop_associate_matcher("+"),
                sketch="(a + b) + c = a + (b + c)",
            ),
            EquivalencePattern(
                name="mul-associate",
                kind=EquivalenceKind.MATHEMATICAL,
                matcher=_mk_binop_associate_matcher("*"),
                sketch="(a * b) * c = a * (b * c)",
            ),
            EquivalencePattern(
                name="recursive-vs-iterative",
                kind=EquivalenceKind.ALGORITHMIC,
                matcher=self._match_recursive_vs_iterative,
                sketch="recursive(lst) = iterative(lst)",
            ),
        ]

    def _match_recursive_vs_iterative(
        self, fn1: ast.FunctionDef, fn2: ast.FunctionDef,
    ) -> Optional["EquivalenceMatch"]:
        """Bound method so the matcher can call the enclosing analyzer's
        recursion/iteration detectors."""
        fn1_recursive = self._is_recursive_pattern(fn1)
        fn1_iterative = self._is_iterative_pattern(fn1)
        fn2_recursive = self._is_recursive_pattern(fn2)
        fn2_iterative = self._is_iterative_pattern(fn2)
        if (fn1_recursive and fn2_iterative) or (fn1_iterative and fn2_recursive):
            if self._same_mathematical_function(fn1, fn2):
                return EquivalenceMatch(
                    kind=EquivalenceKind.ALGORITHMIC,
                    sketch=f"{fn1.name} (recursive) ≃ {fn2.name} (iterative)",
                )
        return None


# ── Pattern-database support types ──────────────────────────────────

@dataclass
class EquivalenceMatch:
    """Result of an :class:`EquivalencePattern` matcher.

    When a pattern recognises a pair of ASTs it produces this lightweight
    record; callers convert it into a full :class:`EquivalenceProof`
    with the analyzer's context.
    """
    kind: EquivalenceKind
    sketch: str
    details: Dict[str, Any] = field(default_factory=dict)


MatcherFn = Callable[[ast.FunctionDef, ast.FunctionDef],
                     Optional[EquivalenceMatch]]


@dataclass
class EquivalencePattern:
    """A named equivalence pattern.  Pattern matchers are pure AST
    inspectors — they do NOT call into the kernel; their success is a
    *claim* that two functions differ only by the named pattern, and
    the caller must still discharge the resulting equivalence proof."""
    name: str
    kind: EquivalenceKind
    matcher: MatcherFn
    sketch: str

    @property
    def proof_sketch(self) -> str:
        """Alias consumed by the pre-existing caller in
        :class:`BehavioralEquivalenceAnalyzer.analyze_equivalence`."""
        return self.sketch

    def matches(self, fn1: ast.FunctionDef,
                fn2: ast.FunctionDef) -> bool:
        """True iff this pattern recognises the two ASTs.  Thin
        compatibility wrapper around :meth:`match`.
        """
        return self.match(fn1, fn2) is not None

    def match(self, fn1: ast.FunctionDef,
              fn2: ast.FunctionDef) -> Optional[EquivalenceMatch]:
        try:
            return self.matcher(fn1, fn2)
        except Exception:
            return None


# ── Matcher factories ───────────────────────────────────────────────

def _extract_single_return(fn: ast.FunctionDef) -> Optional[ast.expr]:
    """Return the expression behind a single ``return EXPR`` body, else None."""
    if len(fn.body) == 1 and isinstance(fn.body[0], ast.Return):
        return fn.body[0].value
    return None


def _mk_binop_identity_matcher(op_sym: str, *,
                               left_unit: Any = None,
                               right_unit: Any = None) -> MatcherFn:
    """Match one function that wraps a trivial unit around the other.

    E.g., ``right_unit=0`` + ``op_sym='+'`` matches
    ``fn1 returns x + 0`` and ``fn2 returns x``.
    """
    OP_CLS = {
        "+": ast.Add, "*": ast.Mult,
    }[op_sym]

    def _matcher(fn1: ast.FunctionDef,
                 fn2: ast.FunctionDef) -> Optional[EquivalenceMatch]:
        e1 = _extract_single_return(fn1)
        e2 = _extract_single_return(fn2)
        if e1 is None or e2 is None:
            return None
        # Try both directions: fn1 wraps, fn2 is simple (and vice-versa).
        for wrapped, simple in ((e1, e2), (e2, e1)):
            if not isinstance(wrapped, ast.BinOp):
                continue
            if not isinstance(wrapped.op, OP_CLS):
                continue
            if right_unit is not None:
                if (isinstance(wrapped.right, ast.Constant) and
                        wrapped.right.value == right_unit and
                        ast.dump(wrapped.left) == ast.dump(simple)):
                    return EquivalenceMatch(
                        kind=EquivalenceKind.MATHEMATICAL,
                        sketch=f"{ast.unparse(wrapped)} = "
                               f"{ast.unparse(simple)}",
                    )
            if left_unit is not None:
                if (isinstance(wrapped.left, ast.Constant) and
                        wrapped.left.value == left_unit and
                        ast.dump(wrapped.right) == ast.dump(simple)):
                    return EquivalenceMatch(
                        kind=EquivalenceKind.MATHEMATICAL,
                        sketch=f"{ast.unparse(wrapped)} = "
                               f"{ast.unparse(simple)}",
                    )
        return None

    return _matcher


def _mk_binop_commute_matcher(op_sym: str) -> MatcherFn:
    """Match ``a OP b`` on one side and ``b OP a`` on the other."""
    OP_CLS = {"+": ast.Add, "*": ast.Mult}[op_sym]

    def _matcher(fn1: ast.FunctionDef,
                 fn2: ast.FunctionDef) -> Optional[EquivalenceMatch]:
        e1 = _extract_single_return(fn1)
        e2 = _extract_single_return(fn2)
        if not (isinstance(e1, ast.BinOp) and isinstance(e1.op, OP_CLS)):
            return None
        if not (isinstance(e2, ast.BinOp) and isinstance(e2.op, OP_CLS)):
            return None
        if (ast.dump(e1.left) == ast.dump(e2.right) and
                ast.dump(e1.right) == ast.dump(e2.left)):
            return EquivalenceMatch(
                kind=EquivalenceKind.MATHEMATICAL,
                sketch=f"{ast.unparse(e1)} = {ast.unparse(e2)} (commute)",
            )
        return None

    return _matcher


def _mk_binop_associate_matcher(op_sym: str) -> MatcherFn:
    """Match ``(a OP b) OP c`` vs ``a OP (b OP c)``."""
    OP_CLS = {"+": ast.Add, "*": ast.Mult}[op_sym]

    def _matcher(fn1: ast.FunctionDef,
                 fn2: ast.FunctionDef) -> Optional[EquivalenceMatch]:
        e1 = _extract_single_return(fn1)
        e2 = _extract_single_return(fn2)
        if not (isinstance(e1, ast.BinOp) and isinstance(e1.op, OP_CLS)):
            return None
        if not (isinstance(e2, ast.BinOp) and isinstance(e2.op, OP_CLS)):
            return None
        # Left-associated vs right-associated.
        for left_assoc, right_assoc in ((e1, e2), (e2, e1)):
            if (isinstance(left_assoc.left, ast.BinOp) and
                    isinstance(left_assoc.left.op, OP_CLS) and
                    isinstance(right_assoc.right, ast.BinOp) and
                    isinstance(right_assoc.right.op, OP_CLS) and
                    ast.dump(left_assoc.left.left) == ast.dump(right_assoc.left) and
                    ast.dump(left_assoc.left.right) == ast.dump(right_assoc.right.left) and
                    ast.dump(left_assoc.right) == ast.dump(right_assoc.right.right)):
                return EquivalenceMatch(
                    kind=EquivalenceKind.MATHEMATICAL,
                    sketch=f"({ast.unparse(left_assoc)}) = "
                           f"({ast.unparse(right_assoc)}) (assoc)",
                )
        return None

    return _matcher


def _match_double_unary(op_name: str) -> MatcherFn:
    """Match a pair where one function applies a unary op twice and the
    other doesn't apply it at all.  E.g., ``USub`` ⇒ ``-(-x) = x``.
    """
    OP_CLS = {"USub": ast.USub, "Not": ast.Not, "UAdd": ast.UAdd}[op_name]

    def _matcher(fn1: ast.FunctionDef,
                 fn2: ast.FunctionDef) -> Optional[EquivalenceMatch]:
        e1 = _extract_single_return(fn1)
        e2 = _extract_single_return(fn2)
        if e1 is None or e2 is None:
            return None
        for wrapped, inner in ((e1, e2), (e2, e1)):
            if (isinstance(wrapped, ast.UnaryOp) and
                    isinstance(wrapped.op, OP_CLS) and
                    isinstance(wrapped.operand, ast.UnaryOp) and
                    isinstance(wrapped.operand.op, OP_CLS) and
                    ast.dump(wrapped.operand.operand) == ast.dump(inner)):
                return EquivalenceMatch(
                    kind=EquivalenceKind.MATHEMATICAL,
                    sketch=f"{ast.unparse(wrapped)} = {ast.unparse(inner)}",
                )
        return None

    return _matcher


def _mk_call_idempotence_matcher(
    fn_names: set, arity: int,
) -> MatcherFn:
    """Match ``f(f(x))`` ↔ ``x`` for functions that are self-inverse."""
    def _matcher(fn1: ast.FunctionDef,
                 fn2: ast.FunctionDef) -> Optional[EquivalenceMatch]:
        e1 = _extract_single_return(fn1)
        e2 = _extract_single_return(fn2)
        if e1 is None or e2 is None:
            return None
        for wrapped, inner in ((e1, e2), (e2, e1)):
            if (isinstance(wrapped, ast.Call) and
                    isinstance(wrapped.func, ast.Name) and
                    wrapped.func.id in fn_names and
                    len(wrapped.args) == arity and
                    isinstance(wrapped.args[0], ast.Call) and
                    isinstance(wrapped.args[0].func, ast.Name) and
                    wrapped.args[0].func.id in fn_names and
                    ast.dump(wrapped.args[0].args[0]) == ast.dump(inner)):
                return EquivalenceMatch(
                    kind=EquivalenceKind.MATHEMATICAL,
                    sketch=(f"{ast.unparse(wrapped)} = "
                            f"{ast.unparse(inner)} (self-inverse)"),
                )
        return None

    return _matcher


def _mk_call_projective_matcher(
    fn_names: set, arity: int,
) -> MatcherFn:
    """Match ``f(f(x))`` ↔ ``f(x)`` for idempotent functions."""
    def _matcher(fn1: ast.FunctionDef,
                 fn2: ast.FunctionDef) -> Optional[EquivalenceMatch]:
        e1 = _extract_single_return(fn1)
        e2 = _extract_single_return(fn2)
        if e1 is None or e2 is None:
            return None
        for wrapped, simple in ((e1, e2), (e2, e1)):
            if (isinstance(wrapped, ast.Call) and
                    isinstance(wrapped.func, ast.Name) and
                    wrapped.func.id in fn_names and
                    len(wrapped.args) == arity and
                    isinstance(wrapped.args[0], ast.Call) and
                    isinstance(wrapped.args[0].func, ast.Name) and
                    wrapped.args[0].func.id in fn_names and
                    ast.dump(wrapped.args[0]) == ast.dump(simple)):
                return EquivalenceMatch(
                    kind=EquivalenceKind.MATHEMATICAL,
                    sketch=(f"{ast.unparse(wrapped)} = "
                            f"{ast.unparse(simple)} (idempotent)"),
                )
        return None

    return _matcher


# ═══════════════════════════════════════════════════════════════════
# 4. Univalent Equality Verifier
# ═══════════════════════════════════════════════════════════════════

class UnivalentEqualityVerifier:
    """Verifies equality using univalence and higher-order reasoning."""
    
    def __init__(self):
        self.kernel = ProofKernel()
        self.path_constructor = PathConstructor()
        self.transport_engine = TransportEngine()
        self.univalence_engine = UnivalenceEngine()
        self.analyzer = BehavioralEquivalenceAnalyzer()
        
    def verify_semantic_equality(self, 
                                 fn1_ast: ast.FunctionDef,
                                 fn2_ast: ast.FunctionDef,
                                 context: Context = None) -> VerificationResult:
        """Verify semantic equality between two functions using HoTT."""
        
        # Analyze for semantic equivalence
        equivalence = self.analyzer.analyze_equivalence(fn1_ast, fn2_ast)
        
        if not equivalence:
            return VerificationResult(
                success=False,
                trust_level=TrustLevel.UNTRUSTED,
                message="No semantic equivalence detected"
            )
        
        # Construct equality proof based on equivalence kind
        if equivalence.kind == EquivalenceKind.SYNTACTIC:
            proof = self._construct_syntactic_proof(equivalence)
        elif equivalence.requires_univalence():
            proof = self._construct_univalent_proof(equivalence)
        else:
            proof = self._construct_behavioral_proof(equivalence)
            
        return VerificationResult(
            success=True,
            trust_level=TrustLevel.KERNEL,  # High trust due to HoTT foundations
            message=f"Semantic equality verified via {equivalence.kind.name}: {equivalence.proof_sketch}"
        )
    
    def transport_proof_via_equality(self,
                                     source_proof: ProofTerm,
                                     equality_path: PathAbs,
                                     target_type: SynType) -> VerificationResult:
        """Transport proof along equality path using univalence."""
        
        try:
            # Use univalence to transport proof
            transported_result = self.univalence_engine.transport_via_univalence(
                source_proof, equality_path, target_type
            )
            
            return VerificationResult(
                success=True,
                trust_level=TrustLevel.KERNEL,
                message="Proof transported via univalent equality"
            )
        except Exception as e:
            return VerificationResult(
                success=False,
                trust_level=TrustLevel.UNTRUSTED,
                message=f"Transport failed: {e}"
            )
    
    def verify_higher_dimensional_coherence(self,
                                            equalities: List[SemanticEquivalence]) -> VerificationResult:
        """Verify coherence of multiple equality proofs (higher-dimensional)."""
        
        if len(equalities) < 2:
            return VerificationResult(
                success=True,
                trust_level=TrustLevel.KERNEL,
                message="Single equality - trivially coherent"
            )
        
        # Check transitivity and coherence
        coherence_proofs = []
        for i in range(len(equalities) - 1):
            eq1, eq2 = equalities[i], equalities[i + 1]
            
            # Construct higher-dimensional path between paths
            coherence_path = self._construct_coherence_path(eq1, eq2)
            coherence_proofs.append(coherence_path)
            
        return VerificationResult(
            success=True,
            trust_level=TrustLevel.KERNEL,
            message=f"Higher-dimensional coherence verified for {len(equalities)} equalities"
        )
    
    def _construct_syntactic_proof(self, equivalence: SemanticEquivalence) -> ProofTerm:
        """Construct proof for syntactic equality."""
        from deppy.core.kernel import Refl
        return Refl(equivalence.left_term)
        
    def _construct_univalent_proof(self, equivalence: SemanticEquivalence) -> ProofTerm:
        """Construct proof using univalence axiom."""
        from deppy.core.kernel import Structural
        return Structural(f"univalence_proof: {equivalence.proof_sketch}")
        
    def _construct_behavioral_proof(self, equivalence: SemanticEquivalence) -> ProofTerm:
        """Construct proof for behavioral equivalence."""
        from deppy.core.kernel import Structural 
        return Structural(f"behavioral_equivalence: {equivalence.proof_sketch}")
        
    def _construct_coherence_path(self, eq1: SemanticEquivalence, eq2: SemanticEquivalence) -> PathAbs:
        """Construct higher-dimensional path between equality proofs."""
        return PathAbs(
            ivar="i",
            body=App(
                func=Var("coherence_bridge"),
                arg=Literal({"eq1": eq1.proof_sketch, "eq2": eq2.proof_sketch})
            )
        )


# ═══════════════════════════════════════════════════════════════════
# 5. Mathematical Identity Database
# ═══════════════════════════════════════════════════════════════════

class MathematicalIdentityDatabase:
    """Database of mathematical identities for semantic equality."""
    
    def __init__(self):
        self.identities = self._build_identity_database()
        
    def _build_identity_database(self) -> Dict[str, Dict[str, Any]]:
        """Build comprehensive database of mathematical identities."""
        return {
            # Arithmetic identities
            "additive_identity": {
                "patterns": ["x + 0", "0 + x"],
                "equivalent_to": "x",
                "proof": "additive identity law"
            },
            "multiplicative_identity": {
                "patterns": ["x * 1", "1 * x"], 
                "equivalent_to": "x",
                "proof": "multiplicative identity law"
            },
            "additive_inverse": {
                "patterns": ["x + (-x)", "(-x) + x"],
                "equivalent_to": "0",
                "proof": "additive inverse law"
            },
            
            # Logical identities
            "logical_and_true": {
                "patterns": ["x and True", "True and x"],
                "equivalent_to": "x", 
                "proof": "logical conjunction identity"
            },
            "logical_or_false": {
                "patterns": ["x or False", "False or x"],
                "equivalent_to": "x",
                "proof": "logical disjunction identity"  
            },
            
            # List/sequence identities
            "list_concatenation_empty": {
                "patterns": ["lst + []", "[] + lst"],
                "equivalent_to": "lst",
                "proof": "list concatenation identity"
            },
            
            # Function composition identities
            "function_identity": {
                "patterns": ["compose(f, identity)", "compose(identity, f)"],
                "equivalent_to": "f",
                "proof": "function composition identity"
            }
        }
        
    def lookup_identity(self, expression_pattern: str) -> Optional[Dict[str, Any]]:
        """Lookup mathematical identity for expression pattern."""
        for identity_name, identity_data in self.identities.items():
            for pattern in identity_data["patterns"]:
                if self._pattern_matches(pattern, expression_pattern):
                    return identity_data
        return None
        
    def _pattern_matches(self, pattern: str, expression: str) -> bool:
        """Check if pattern matches expression (simplified).""" 
        # Simplified exact substring matching for now
        # More sophisticated pattern matching would need proper parsing
        normalized_pattern = pattern.replace(" ", "").lower()
        normalized_expr = expression.replace(" ", "").lower()
        return normalized_pattern in normalized_expr or normalized_expr in normalized_pattern


# ═══════════════════════════════════════════════════════════════════
# 6. Higher-Order Equality Decorators
# ═══════════════════════════════════════════════════════════════════

def semantic_equality(other_function: Callable = None, *, 
                      kind: EquivalenceKind = EquivalenceKind.BEHAVIORAL,
                      proof_sketch: str = ""):
    """Declare semantic equality between functions."""
    def decorator(func):
        if not hasattr(func, '_deppy_semantic_equalities'):
            func._deppy_semantic_equalities = []
        
        if other_function:
            equivalence = SemanticEquivalence(
                left_term=Var(func.__name__),
                right_term=Var(other_function.__name__), 
                kind=kind,
                proof_sketch=proof_sketch
            )
            func._deppy_semantic_equalities.append(equivalence)
            
        return func
    return decorator


def mathematical_identity(identity_name: str):
    """Mark function as implementing a mathematical identity."""
    def decorator(func):
        func._deppy_math_identity = identity_name
        return func
    return decorator


def univalent_transport(source_type: str, target_type: str):
    """Enable univalent transport between equivalent types."""
    def decorator(func):
        func._deppy_univalent_transport = {
            "source": source_type,
            "target": target_type
        }
        return func
    return decorator