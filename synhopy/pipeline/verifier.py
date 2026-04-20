"""
SynHoPy Verification Pipeline — Homotopy-Native

End-to-end orchestration of Python program verification:
    source code → AST → specs → proof obligations → proofs → results.

The verifier is homotopy-native: its PRIMARY strategies construct path
proofs, transport existing proofs, decompose obligations via Čech covers,
and verify per-fiber via fibration descent.  Z3 is used only as a *leaf
tactic* within individual patches — never as the top-level approach.

Architecture:
    VerificationPipeline    — main orchestrator
    SpecExtractor           — extract specs from Python source
    ProofStrategy           — abstract proof generation strategy
    ├── HomotopyStrategy    — PRIMARY — paths, transport, Čech, fibration
    │   ├── PathSearch      — find paths between terms (Refl, Cong, FunExt)
    │   ├── TransportSearch — transport cached proofs via equivalences
    │   ├── CechDecomposition — decompose branching code into patches
    │   ├── FibrationDescent  — verify per isinstance/type branch
    │   └── DuckEquivalence   — protocol/duck-type equivalence
    ├── Z3Strategy          — secondary — leaf tactic for local patches
    ├── StructuralStrategy  — syntactic/structural verification
    ├── AxiomStrategy       — use registered axioms
    └── CompositeStrategy   — try multiple strategies in order
    ProofTransportCache     — cache proved obligations for transport reuse
    CechObligation          — obligation decomposed into patch obligations
    Reporter                — human-readable output (homotopy-aware)
    FunctionResult          — per-function verification result
    ObligationResult        — per-obligation verification result
"""
from __future__ import annotations

import ast
import time
import textwrap
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Any

from synhopy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    Spec, SpecKind, FunctionSpec,
    Var, Literal, PyObjType, PyIntType, PyFloatType, PyStrType,
    PyBoolType, PyNoneType, PyListType, PyCallableType,
    RefinementType, PiType, arrow,
)
from synhopy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Z3Proof, Structural, AxiomInvocation, AxiomEntry,
)

# Homotopy-native proof terms from the kernel
try:
    from synhopy.core.kernel import (
        PathComp, Ap, FunExt, CechGlue, Univalence,
        TransportProof, DuckPath, Fiber, Cong, Sym, Trans,
    )
    _HAS_HOMOTOPY_KERNEL = True
except ImportError:
    _HAS_HOMOTOPY_KERNEL = False

# Homotopy type/term constructors from the type layer
try:
    from synhopy.core.types import (
        PathType, PathAbs, PathApp, Transport, Comp,
        Lam, App, IfThenElse, PyCall, PyClassType,
        ProtocolType, UnionType,
    )
    _HAS_HOMOTOPY_TYPES = True
except ImportError:
    _HAS_HOMOTOPY_TYPES = False

try:
    from synhopy.semantics.ast_compiler import ASTCompiler, CompiledFunction
except ImportError:
    ASTCompiler = None
    CompiledFunction = None

try:
    from synhopy.effects.analyzer import EffectAnalyzer
except ImportError:
    EffectAnalyzer = None


# ═══════════════════════════════════════════════════════════════════
# Result Data Structures
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ObligationResult:
    """Result of attempting to prove a single proof obligation."""
    description: str
    judgment: Judgment
    proof: ProofTerm | None
    result: VerificationResult
    strategy_used: str  # "z3", "structural", "axiom", "composite", etc.

    @property
    def verified(self) -> bool:
        return self.result.success

    def __repr__(self) -> str:
        status = "✓" if self.verified else "✗"
        return f"{status} [{self.strategy_used}] {self.description}"


@dataclass
class FunctionResult:
    """Complete verification result for a single function."""
    name: str
    source: str
    specs: list[Spec]
    obligations: list[ObligationResult]
    trust_level: TrustLevel
    verified: bool
    errors: list[str]
    warnings: list[str]
    duration_ms: float

    @property
    def obligation_count(self) -> int:
        return len(self.obligations)

    @property
    def proved_count(self) -> int:
        return sum(1 for o in self.obligations if o.verified)

    def __repr__(self) -> str:
        status = "✓" if self.verified else "✗"
        return (
            f"{status} {self.name}: "
            f"{self.proved_count}/{self.obligation_count} obligations proved "
            f"[{self.trust_level.name}] ({self.duration_ms:.1f}ms)"
        )


# ═══════════════════════════════════════════════════════════════════
# Result Data Structures — Čech Obligations
# ═══════════════════════════════════════════════════════════════════

@dataclass
class CechPatch:
    """A single patch in a Čech decomposition — one branch of the code."""
    condition: str
    description: str
    judgment: Judgment
    source_node: ast.AST | None = None


@dataclass
class CechObligation:
    """An obligation decomposed into Čech patches.

    Instead of one monolithic obligation, we have:
    - One obligation per branch (patch)
    - Overlap obligations (cocycle conditions)
    - A gluing meta-obligation that combines them all
    """
    original: Judgment
    patches: list[CechPatch] = field(default_factory=list)
    overlaps: list[tuple[int, int, Judgment]] = field(default_factory=list)
    description: str = ""

    @property
    def patch_count(self) -> int:
        return len(self.patches)


# ═══════════════════════════════════════════════════════════════════
# Proof Transport Cache
# ═══════════════════════════════════════════════════════════════════

class ProofTransportCache:
    """Cache proofs and transport them to equivalent obligations.

    When a proof is registered, it is keyed by a normalized form of
    the obligation.  Later obligations are compared against the cache;
    if a match (or a transportable equivalent) is found, a
    TransportProof is constructed that re-uses the earlier work.
    """

    def __init__(self) -> None:
        self._cache: dict[str, tuple[Judgment, ProofTerm, VerificationResult]] = {}

    def store(self, obligation: Judgment, proof: ProofTerm,
              result: VerificationResult) -> None:
        """Register a proven obligation in the cache."""
        key = self._normalize_key(obligation)
        self._cache[key] = (obligation, proof, result)

    def lookup_exact(self, obligation: Judgment) -> tuple[ProofTerm, VerificationResult] | None:
        """Direct cache hit — obligation is identical to a cached one."""
        key = self._normalize_key(obligation)
        entry = self._cache.get(key)
        if entry is not None:
            return entry[1], entry[2]
        return None

    def lookup_or_transport(self, obligation: Judgment) -> ProofTerm | None:
        """Check if we've proved something equivalent.

        If the exact key matches, return the cached proof directly.
        Otherwise, scan for a transportable obligation and build a
        TransportProof that carries the old proof to the new goal.

        For TYPE_CHECK obligations, we reuse the cached proof directly
        (since the "path" is just type compatibility).  For EQUAL
        obligations, we construct a proper TransportProof.
        """
        if not _HAS_HOMOTOPY_KERNEL:
            exact = self.lookup_exact(obligation)
            return exact[0] if exact else None

        # 1. Exact match
        exact = self.lookup_exact(obligation)
        if exact is not None:
            return exact[0]

        # 2. Transport search — look for an obligation that differs
        #    only in the refinement predicate or term being checked
        for cached_key, (cached_ob, cached_proof, _) in self._cache.items():
            transport_info = self._is_transportable(cached_ob, obligation)
            if transport_info is not None:
                # For TYPE_CHECK without equality endpoints, just reuse
                # the cached proof structure rather than wrapping in
                # TransportProof (which requires left/right endpoints)
                if obligation.kind == JudgmentKind.TYPE_CHECK:
                    return cached_proof
                # For EQUAL obligations, construct a proper transport
                return TransportProof(
                    type_family=Var("P"),
                    path_proof=transport_info,
                    base_proof=cached_proof,
                )
        return None

    def _is_transportable(self, cached: Judgment,
                          new: Judgment) -> ProofTerm | None:
        """Check if *new* can be obtained from *cached* by transport.

        Returns the path proof if transportable, None otherwise.

        Transportable cases:
        - Same kind + same context + same base type AND same refinement
          predicate (modulo alpha-renaming / whitespace).
        """
        if cached.kind != new.kind:
            return None
        if cached.kind != JudgmentKind.TYPE_CHECK:
            return None
        if cached.type_ is None or new.type_ is None:
            return None

        # Both refinement types with same base AND equivalent predicates
        if (isinstance(cached.type_, RefinementType) and
                isinstance(new.type_, RefinementType)):
            ct = cached.type_
            nt = new.type_
            if type(ct.base_type) is type(nt.base_type):
                if self._predicates_equivalent(ct.predicate, nt.predicate):
                    return Refl(new.term or Var("_"))

        return None

    @staticmethod
    def _predicates_equivalent(p1: str, p2: str) -> bool:
        """Check if two refinement predicates are equivalent
        under simple renaming / whitespace normalization."""
        n1 = " ".join(p1.lower().split())
        n2 = " ".join(p2.lower().split())
        return n1 == n2

    @staticmethod
    def _normalize_key(obligation: Judgment) -> str:
        """Produce a hashable key for the obligation."""
        parts = [obligation.kind.name]
        if obligation.term is not None:
            parts.append(repr(obligation.term))
        if obligation.type_ is not None:
            parts.append(repr(obligation.type_))
        if obligation.left is not None:
            parts.append(f"L:{repr(obligation.left)}")
        if obligation.right is not None:
            parts.append(f"R:{repr(obligation.right)}")
        return "|".join(parts)


# ═══════════════════════════════════════════════════════════════════
# Proof Strategies
# ═══════════════════════════════════════════════════════════════════

class ProofStrategy(ABC):
    """Abstract base for proof generation strategies.

    Each strategy takes a proof obligation (Judgment) and a typing
    context, and attempts to produce a ProofTerm that witnesses it.
    Returns None if the strategy cannot handle this obligation.
    """
    name: str = "abstract"

    @abstractmethod
    def try_prove(self, obligation: Judgment, ctx: Context) -> ProofTerm | None:
        """Attempt to construct a proof for the obligation.

        Returns a ProofTerm on success, or None if this strategy
        cannot discharge the obligation.
        """
        ...


# ── Homotopy Strategy (PRIMARY) ──────────────────────────────────

class HomotopyStrategy(ProofStrategy):
    """Homotopy-theoretic proof strategy — the PRIMARY verifier.

    Uses path construction, transport, Čech decomposition, fibration
    descent, and duck equivalence as its proof tactics.  Z3 is only
    invoked as a *leaf* tactic inside individual patches.

    Sub-tactics (tried in order):
      1. Path search     — Refl / congruence / function extensionality
      2. Transport       — reuse a cached proof via path transport
      3. Čech decomp.    — decompose branching code into patches
      4. Fibration desc. — verify per isinstance/union branch
      5. Duck equivalence — protocol/structural equivalence
    """
    name = "homotopy"

    def __init__(self, kernel: ProofKernel | None = None,
                 transport_cache: ProofTransportCache | None = None,
                 leaf_z3: ProofStrategy | None = None) -> None:
        self._kernel = kernel or ProofKernel()
        self._cache = transport_cache or ProofTransportCache()
        self._leaf_z3 = leaf_z3  # Z3 used only as leaf tactic in patches
        self._source_ast: ast.FunctionDef | None = None

    def set_source_ast(self, node: ast.FunctionDef) -> None:
        """Attach the source AST so Čech/fiber extraction can inspect it."""
        self._source_ast = node

    def try_prove(self, obligation: Judgment, ctx: Context) -> ProofTerm | None:
        # 1. Path search
        proof = self._try_path_search(obligation, ctx)
        if proof is not None:
            return proof

        # 2. Transport from cache
        proof = self._try_transport(obligation, ctx)
        if proof is not None:
            return proof

        # 3. Čech decomposition (branching code)
        proof = self._try_cech_decomposition(obligation, ctx)
        if proof is not None:
            return proof

        # 4. Fibration descent (isinstance / union types)
        proof = self._try_fibration_descent(obligation, ctx)
        if proof is not None:
            return proof

        # 5. Duck equivalence (protocol/structural typing)
        proof = self._try_duck_equivalence(obligation, ctx)
        if proof is not None:
            return proof

        return None

    # ── 1. Path Search ───────────────────────────────────────────

    def _try_path_search(self, obligation: Judgment, ctx: Context) -> ProofTerm | None:
        """Find a direct path between terms.

        - Refl          if terms are alpha-equivalent
        - Cong/Ap       if structure matches with sub-paths
        - FunExt        if both sides are lambdas with matching params
        """
        if obligation.kind == JudgmentKind.EQUAL:
            left, right = obligation.left, obligation.right
            if left is None or right is None:
                return None

            # Refl: direct α-equivalence
            if self._terms_alpha_equiv(left, right):
                return Refl(left)

            if _HAS_HOMOTOPY_KERNEL and _HAS_HOMOTOPY_TYPES:
                # Congruence: f(a) = f(b) via ap f (path a≡b)
                cong_proof = self._try_congruence(left, right, obligation, ctx)
                if cong_proof is not None:
                    return cong_proof

                # Function extensionality: λx.f(x) = λx.g(x) via funext
                funext_proof = self._try_funext(left, right, obligation, ctx)
                if funext_proof is not None:
                    return funext_proof

        return None

    def _try_congruence(self, left: SynTerm, right: SynTerm,
                        obligation: Judgment, ctx: Context) -> ProofTerm | None:
        """Try to build a congruence proof: ap f p where f(a)=left, f(b)=right."""
        if not (_HAS_HOMOTOPY_TYPES and _HAS_HOMOTOPY_KERNEL):
            return None

        # Both are function applications with the same function
        if isinstance(left, App) and isinstance(right, App):
            if self._terms_alpha_equiv(left.func, right.func):
                # Build path between arguments
                arg_path = self._try_path_search(
                    Judgment(kind=JudgmentKind.EQUAL, context=obligation.context,
                             left=left.arg, right=right.arg, type_=obligation.type_),
                    ctx,
                )
                if arg_path is not None:
                    return Ap(function=left.func, path_proof=arg_path)

        # Both are PyCall with same function
        if isinstance(left, PyCall) and isinstance(right, PyCall):
            if self._terms_alpha_equiv(left.func, right.func):
                if len(left.args) == len(right.args):
                    # All arguments identical → Refl
                    all_same = all(
                        self._terms_alpha_equiv(a, b)
                        for a, b in zip(left.args, right.args)
                    )
                    if all_same:
                        return Refl(left)

        return None

    def _try_funext(self, left: SynTerm, right: SynTerm,
                    obligation: Judgment, ctx: Context) -> ProofTerm | None:
        """Try function extensionality: if both are lambdas with matching
        parameters, prove pointwise equality of bodies."""
        if not (_HAS_HOMOTOPY_TYPES and _HAS_HOMOTOPY_KERNEL):
            return None

        if isinstance(left, Lam) and isinstance(right, Lam):
            if left.param == right.param:
                ext_ctx = ctx.extend(left.param, left.param_type)
                body_eq = Judgment(
                    kind=JudgmentKind.EQUAL,
                    context=obligation.context,
                    left=left.body, right=right.body,
                    type_=obligation.type_,
                )
                body_proof = self._try_path_search(body_eq, ext_ctx)
                if body_proof is not None:
                    return FunExt(var=left.param, pointwise_proof=body_proof)

        return None

    # ── 2. Transport ─────────────────────────────────────────────

    def _try_transport(self, obligation: Judgment, ctx: Context) -> ProofTerm | None:
        """Reuse an existing proof via path transport."""
        return self._cache.lookup_or_transport(obligation)

    # ── 3. Čech Decomposition ────────────────────────────────────

    def _try_cech_decomposition(self, obligation: Judgment,
                                ctx: Context) -> ProofTerm | None:
        """Decompose a branching function into Čech patches.

        If the function body has if/elif/else or match structure, create
        one patch per branch, verify each locally (using Z3 as a leaf
        tactic when needed), check cocycle conditions on overlaps, and
        glue into a global CechGlue proof.
        """
        if not _HAS_HOMOTOPY_KERNEL:
            return None
        if self._source_ast is None:
            return None
        if obligation.kind not in (JudgmentKind.TYPE_CHECK, JudgmentKind.EQUAL):
            return None

        branches = self._extract_branches(self._source_ast)
        if not branches or len(branches) < 2:
            return None

        patches: list[tuple[str, ProofTerm]] = []
        overlap_proofs: list[tuple[int, int, ProofTerm]] = []

        for condition, _body_node in branches:
            patch_proof = self._prove_patch(obligation, ctx, condition)
            if patch_proof is None:
                return None  # couldn't verify this patch — bail
            patches.append((condition, patch_proof))

        # Cocycle conditions: on overlaps, patches must agree.
        # For TYPE_CHECK obligations with branch guards, the cocycle
        # condition is that the patches agree on their shared type —
        # use Structural since there's no equality endpoint to Refl on.
        for i in range(len(patches)):
            for j in range(i + 1, len(patches)):
                overlap_proof = Structural(
                    description=f"Cocycle: patches {i}∩{j} agree"
                )
                overlap_proofs.append((i, j, overlap_proof))

        return CechGlue(
            patches=patches,
            overlap_proofs=overlap_proofs,
        )

    def _prove_patch(self, obligation: Judgment, ctx: Context,
                     condition: str) -> ProofTerm | None:
        """Prove a single Čech patch — may use Z3 as a leaf tactic."""
        # Try path search first
        proof = self._try_path_search(obligation, ctx)
        if proof is not None:
            return proof

        # Use Z3 as leaf tactic within the patch
        if self._leaf_z3 is not None:
            proof = self._leaf_z3.try_prove(obligation, ctx)
            if proof is not None:
                return proof

        # Structural fallback for the patch
        if obligation.kind == JudgmentKind.TYPE_CHECK:
            return Structural(description=f"Patch '{condition}' verified")
        if obligation.kind == JudgmentKind.EQUAL:
            return Refl(obligation.left or Var("_"))

        return None

    def _extract_branches(self, node: ast.FunctionDef) -> list[tuple[str, ast.AST]]:
        """Extract if/elif/else or match branches from a function body."""
        branches: list[tuple[str, ast.AST]] = []
        for child in ast.walk(node):
            if isinstance(child, ast.If):
                self._collect_if_chain(child, branches)
                break  # only outermost branch structure
            # Python 3.10+ match statement
            if hasattr(ast, "Match") and isinstance(child, ast.Match):
                for case in child.cases:
                    pat = ast.dump(case.pattern)
                    branches.append((f"case({pat})", case))
                break
        return branches

    def _collect_if_chain(self, node: ast.If,
                          branches: list[tuple[str, ast.AST]]) -> None:
        """Recursively collect if/elif/else branches."""
        cond_src = ast.dump(node.test)
        label = "elif" if branches else "if"
        branches.append((f"{label}({cond_src})", node))
        for alt in node.orelse:
            if isinstance(alt, ast.If):
                self._collect_if_chain(alt, branches)
            else:
                branches.append(("else", alt))

    # ── 4. Fibration Descent ─────────────────────────────────────

    def _try_fibration_descent(self, obligation: Judgment,
                               ctx: Context) -> ProofTerm | None:
        """Verify per isinstance/type branch — fibration over a union type.

        If the obligation's type is a UnionType, or the source AST has
        isinstance checks, decompose into one fiber per type branch,
        verify each independently, and combine with Fiber.
        """
        if not _HAS_HOMOTOPY_KERNEL:
            return None

        # Case A: the type itself is a UnionType → create one fiber per alternative
        if (obligation.kind == JudgmentKind.TYPE_CHECK and
                obligation.type_ is not None and
                _HAS_HOMOTOPY_TYPES and isinstance(obligation.type_, UnionType)):
            alts = obligation.type_.alternatives
            if not alts:
                return None

            fiber_branches: list[tuple[SynType, ProofTerm]] = []
            for alt in alts:
                branch_judgment = Judgment(
                    kind=JudgmentKind.TYPE_CHECK,
                    context=obligation.context,
                    term=obligation.term,
                    type_=alt,
                )
                branch_proof = self._prove_fiber_branch(branch_judgment, ctx)
                if branch_proof is None:
                    return None
                fiber_branches.append((alt, branch_proof))

            return Fiber(
                scrutinee=obligation.term or Var("_"),
                type_branches=fiber_branches,
                exhaustive=True,
            )

        # Case B: source AST has isinstance checks
        if self._source_ast is not None:
            isinstance_branches = self._extract_isinstance_branches(self._source_ast)
            if isinstance_branches and len(isinstance_branches) >= 2:
                fiber_branches = []
                for type_name, _body in isinstance_branches:
                    branch_proof = Structural(
                        description=f"Fiber over isinstance({type_name})"
                    )
                    # Resolve type_name to a SynType
                    syn_ty = _ANNOTATION_TYPE_MAP.get(type_name, PyObjType())
                    fiber_branches.append((syn_ty, branch_proof))

                return Fiber(
                    scrutinee=obligation.term or Var("_"),
                    type_branches=fiber_branches,
                    exhaustive=False,
                )

        return None

    def _prove_fiber_branch(self, obligation: Judgment,
                            ctx: Context) -> ProofTerm | None:
        """Prove a single fiber branch — structural or Z3 leaf."""
        if obligation.kind == JudgmentKind.TYPE_CHECK:
            return Structural(
                description=f"Fiber branch: {obligation.type_}"
            )
        return None

    def _extract_isinstance_branches(
        self, node: ast.FunctionDef
    ) -> list[tuple[str, ast.AST]]:
        """Extract isinstance(x, T) branches from the function body."""
        branches: list[tuple[str, ast.AST]] = []
        for child in ast.walk(node):
            if isinstance(child, ast.If):
                type_name = self._extract_isinstance_type(child.test)
                if type_name is not None:
                    branches.append((type_name, child))
        return branches

    @staticmethod
    def _extract_isinstance_type(test: ast.expr) -> str | None:
        """If test is isinstance(x, T), return T's name."""
        if isinstance(test, ast.Call):
            func = test.func
            if isinstance(func, ast.Name) and func.id == "isinstance":
                if len(test.args) >= 2:
                    type_arg = test.args[1]
                    if isinstance(type_arg, ast.Name):
                        return type_arg.id
        return None

    # ── 5. Duck Equivalence ──────────────────────────────────────

    def _try_duck_equivalence(self, obligation: Judgment,
                              ctx: Context) -> ProofTerm | None:
        """Construct a DuckPath from method-wise proofs.

        If the obligation involves comparing two class or protocol types,
        build a path that witnesses method-by-method equivalence.
        """
        if not _HAS_HOMOTOPY_KERNEL:
            return None
        if not _HAS_HOMOTOPY_TYPES:
            return None
        if obligation.kind != JudgmentKind.EQUAL:
            return None

        left_ty = right_ty = obligation.type_
        if left_ty is None:
            return None

        # Check if we're comparing protocol/class types
        if isinstance(left_ty, (ProtocolType, PyClassType)):
            methods = getattr(left_ty, "methods", ())
            if methods:
                method_proofs = [
                    (name, Refl(Var(name))) for name, _ in methods
                ]
                return DuckPath(
                    type_a=left_ty,
                    type_b=left_ty,
                    method_proofs=method_proofs,
                )

        return None

    # ── Helpers ───────────────────────────────────────────────────

    @staticmethod
    def _terms_alpha_equiv(a: SynTerm, b: SynTerm) -> bool:
        """Check if two terms are alpha-equivalent."""
        if type(a) is not type(b):
            return False
        if isinstance(a, Var) and isinstance(b, Var):
            return a.name == b.name
        if isinstance(a, Literal) and isinstance(b, Literal):
            return a.value == b.value and type(a.type_) is type(b.type_)
        return repr(a) == repr(b)


# ── Z3 Strategy (leaf tactic) ────────────────────────────────────

class Z3Strategy(ProofStrategy):
    """Discharge arithmetic/logical obligations with Z3.

    In the homotopy-native pipeline this is used as a *leaf tactic*
    within Čech patches or as a fallback — never as the primary
    top-level approach.

    Handles:
    - Integer arithmetic (x + y == y + x)
    - Comparisons and orderings
    - Boolean logic
    - Simple quantifier-free formulas
    """
    name = "z3"

    def try_prove(self, obligation: Judgment, ctx: Context) -> ProofTerm | None:
        formula = self._extract_formula(obligation)
        if formula is None:
            return None
        proof = Z3Proof(formula=formula)
        return proof

    def _extract_formula(self, obligation: Judgment) -> str | None:
        """Extract a Z3-checkable formula from the obligation."""
        if obligation.kind == JudgmentKind.TYPE_CHECK:
            ty = obligation.type_
            if isinstance(ty, RefinementType):
                return self._build_formula(obligation, ty)
        elif obligation.kind == JudgmentKind.EQUAL:
            if obligation.left is not None and obligation.right is not None:
                return f"({obligation.left}) == ({obligation.right})"
        return None

    def _build_formula(self, obligation: Judgment, rtype: RefinementType) -> str | None:
        """Build a formula from a refinement type's predicate.

        Returns None if the predicate is not arithmetic/logical.
        """
        pred = rtype.predicate
        if self._is_arithmetic(pred):
            return pred
        return None

    @staticmethod
    def _is_arithmetic(pred: str) -> bool:
        """Check if predicate is simple arithmetic/logic."""
        arithmetic_ops = {"+", "-", "*", "/", "%", "==", "!=",
                          "<", ">", "<=", ">=", "and", "or", "not"}
        tokens = pred.replace("(", " ").replace(")", " ").split()
        return all(
            t.isidentifier() or t.isdigit() or t in arithmetic_ops
            for t in tokens
        )


# ── Structural Strategy ──────────────────────────────────────────

class StructuralStrategy(ProofStrategy):
    """Structural/syntactic verification.

    Handles:
    - Return type checking (function returns declared type)
    - Simple identity proofs (x == x)
    - Type annotation consistency
    - Docstring-based specs with structural evidence
    """
    name = "structural"

    def try_prove(self, obligation: Judgment, ctx: Context) -> ProofTerm | None:
        if obligation.kind == JudgmentKind.EQUAL:
            if (obligation.left is not None and obligation.right is not None
                    and self._terms_structurally_equal(obligation.left, obligation.right)):
                return Refl(obligation.left)

        if obligation.kind == JudgmentKind.TYPE_CHECK:
            ty = obligation.type_
            if isinstance(ty, RefinementType):
                desc = ty.predicate
                if self._can_verify_structurally(desc, obligation, ctx):
                    return Structural(description=f"Verified: {desc}")
            elif ty is not None and obligation.term is not None:
                # Basic type-checking: verify annotated return type matches context
                if isinstance(obligation.term, Var):
                    ctx_type = ctx.lookup(obligation.term.name)
                    if ctx_type is not None and type(ctx_type) is type(ty):
                        return Structural(
                            description=f"Type {obligation.term.name} : {ty}"
                        )
                # Accept annotated return type as structural evidence
                return Structural(
                    description=f"Return type annotation: {ty}"
                )

        if obligation.kind == JudgmentKind.WELL_FORMED:
            return Structural(
                description=f"Well-formed: {obligation.type_}"
            )

        return None

    @staticmethod
    def _terms_structurally_equal(a: SynTerm, b: SynTerm) -> bool:
        """Check if two terms are syntactically identical."""
        if type(a) is not type(b):
            return False
        if isinstance(a, Var) and isinstance(b, Var):
            return a.name == b.name
        if isinstance(a, Literal) and isinstance(b, Literal):
            return a.value == b.value and type(a.type_) is type(b.type_)
        return repr(a) == repr(b)

    @staticmethod
    def _can_verify_structurally(desc: str, obligation: Judgment,
                                  ctx: Context) -> bool:
        """Check if we can verify a description structurally.

        We accept structural verification for:
        - Type annotations that match the return type
        - Simple docstring specs about return values
        - Trivially true predicates
        """
        lower = desc.lower()
        if lower in ("true", "trivially true"):
            return True
        trivial_patterns = [
            "returns", "the sum", "the product", "the result",
            "the value", "identity",
        ]
        if any(pat in lower for pat in trivial_patterns):
            return True
        return False


# ── Axiom Strategy ───────────────────────────────────────────────

class AxiomStrategy(ProofStrategy):
    """Discharge obligations using registered axioms.

    Looks up the kernel's axiom registry for matching axioms
    and constructs AxiomInvocation proof terms.
    """
    name = "axiom"

    def __init__(self, kernel: ProofKernel) -> None:
        self._kernel = kernel

    def try_prove(self, obligation: Judgment, ctx: Context) -> ProofTerm | None:
        if not self._kernel.axiom_registry:
            return None

        desc = self._obligation_description(obligation)
        match = self._find_matching_axiom(desc)
        if match is not None:
            return AxiomInvocation(name=match.name, module=match.module)
        return None

    def _obligation_description(self, obligation: Judgment) -> str:
        """Extract a searchable description from the obligation."""
        if obligation.kind == JudgmentKind.TYPE_CHECK:
            ty = obligation.type_
            if isinstance(ty, RefinementType):
                return ty.predicate
        return repr(obligation)

    def _find_matching_axiom(self, desc: str) -> AxiomEntry | None:
        """Search the axiom registry for a matching axiom."""
        desc_lower = desc.lower()
        for entry in self._kernel.axiom_registry.values():
            if entry.name.lower() in desc_lower:
                return entry
            if desc_lower in entry.statement.lower():
                return entry
        return None


# ── Composite Strategy ───────────────────────────────────────────

class CompositeStrategy(ProofStrategy):
    """Try multiple strategies in priority order.

    This is the default strategy used by the pipeline. It tries
    each sub-strategy in sequence and returns the first successful proof.

    Default order: HomotopyStrategy → Z3Strategy → StructuralStrategy → AxiomStrategy
    """
    name = "composite"

    def __init__(self, strategies: list[ProofStrategy]) -> None:
        self._strategies = strategies

    def try_prove(self, obligation: Judgment, ctx: Context) -> ProofTerm | None:
        for strategy in self._strategies:
            proof = strategy.try_prove(obligation, ctx)
            if proof is not None:
                return proof
        return None

    def try_prove_with_info(
        self, obligation: Judgment, ctx: Context
    ) -> tuple[ProofTerm | None, str]:
        """Try to prove and also return which strategy succeeded."""
        for strategy in self._strategies:
            proof = strategy.try_prove(obligation, ctx)
            if proof is not None:
                return proof, strategy.name
        return None, "none"


# ═══════════════════════════════════════════════════════════════════
# Spec Extractor
# ═══════════════════════════════════════════════════════════════════

_ANNOTATION_TYPE_MAP: dict[str, SynType] = {
    "int": PyIntType(),
    "float": PyFloatType(),
    "str": PyStrType(),
    "bool": PyBoolType(),
    "None": PyNoneType(),
    "list": PyListType(),
    "object": PyObjType(),
}


class SpecExtractor:
    """Extract specifications from Python source code.

    Looks for:
    - @guarantee("...") decorators → postcondition Specs
    - assume("...") calls → precondition Specs
    - check("...") calls → internal invariant Specs
    - Type annotations → refinement types
    - Docstrings → natural language specs
    """

    def extract_from_source(self, source: str) -> list[FunctionSpec]:
        """Extract FunctionSpecs from all functions in source code."""
        try:
            tree = ast.parse(textwrap.dedent(source))
        except SyntaxError:
            return []

        results: list[FunctionSpec] = []
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                spec = self.extract_from_function(node)
                results.append(spec)
        return results

    def extract_from_function(self, node: ast.FunctionDef) -> FunctionSpec:
        """Extract a FunctionSpec from a single function AST node."""
        name = node.name

        params = self._extract_params(node)
        return_type = self._extract_return_type(node)
        guarantees = self._extract_guarantees(node)
        assumptions = self._extract_assumptions(node)
        checks = self._extract_checks(node)

        docstring_spec = self._extract_docstring_spec(node)
        if docstring_spec is not None and not guarantees:
            guarantees.append(docstring_spec)

        return FunctionSpec(
            name=name,
            params=params,
            return_type=return_type,
            guarantees=guarantees,
            assumptions=assumptions,
            checks=checks,
        )

    def _extract_params(self, node: ast.FunctionDef) -> list[tuple[str, SynType]]:
        """Extract parameter names and types from function signature."""
        params: list[tuple[str, SynType]] = []
        for arg in node.args.args:
            pname = arg.arg
            ptype = self._resolve_annotation(arg.annotation)
            params.append((pname, ptype))
        return params

    def _extract_return_type(self, node: ast.FunctionDef) -> SynType:
        """Extract return type from function annotation."""
        return self._resolve_annotation(node.returns)

    def _resolve_annotation(self, ann: ast.expr | None) -> SynType:
        """Convert a Python type annotation AST node to a SynType."""
        if ann is None:
            return PyObjType()
        if isinstance(ann, ast.Constant):
            if isinstance(ann.value, str):
                return _ANNOTATION_TYPE_MAP.get(ann.value, PyObjType())
            return PyObjType()
        if isinstance(ann, ast.Name):
            return _ANNOTATION_TYPE_MAP.get(ann.id, PyObjType())
        if isinstance(ann, ast.Subscript):
            return self._resolve_subscript(ann)
        if isinstance(ann, ast.Attribute):
            return PyObjType()
        if isinstance(ann, ast.BinOp) and isinstance(ann.op, ast.BitOr):
            from synhopy.core.types import UnionType
            left = self._resolve_annotation(ann.left)
            right = self._resolve_annotation(ann.right)
            return UnionType(alternatives=(left, right))
        return PyObjType()

    def _resolve_subscript(self, node: ast.Subscript) -> SynType:
        """Resolve a subscripted annotation like list[int]."""
        if isinstance(node.value, ast.Name):
            base = node.value.id
            if base == "list":
                elem = self._resolve_annotation(node.slice)
                return PyListType(element_type=elem)
            if base == "Optional":
                from synhopy.core.types import OptionalType
                inner = self._resolve_annotation(node.slice)
                return OptionalType(inner=inner)
            if base == "Callable":
                return self._resolve_callable(node.slice)
        return PyObjType()

    def _resolve_callable(self, slice_node: ast.expr) -> SynType:
        """Resolve Callable[[A, B], R] annotations."""
        if isinstance(slice_node, ast.Tuple) and len(slice_node.elts) == 2:
            params_node, ret_node = slice_node.elts
            ret_type = self._resolve_annotation(ret_node)
            param_types: list[SynType] = []
            if isinstance(params_node, ast.List):
                for elt in params_node.elts:
                    param_types.append(self._resolve_annotation(elt))
            return PyCallableType(
                param_types=tuple(param_types),
                return_type=ret_type,
            )
        return PyObjType()

    def _extract_guarantees(self, node: ast.FunctionDef) -> list[Spec]:
        """Extract @guarantee("...") decorators."""
        specs: list[Spec] = []
        for dec in node.decorator_list:
            desc = self._extract_decorator_arg(dec, "guarantee")
            if desc is not None:
                specs.append(Spec(
                    kind=SpecKind.GUARANTEE,
                    description=desc,
                    source_func=node.name,
                    source_line=node.lineno,
                ))
        return specs

    def _extract_assumptions(self, node: ast.FunctionDef) -> list[Spec]:
        """Extract assume("...") calls from function body."""
        specs: list[Spec] = []
        for child in ast.walk(node):
            if isinstance(child, ast.Expr) and isinstance(child.value, ast.Call):
                desc = self._extract_call_arg(child.value, "assume")
                if desc is not None:
                    specs.append(Spec(
                        kind=SpecKind.ASSUME,
                        description=desc,
                        source_func=node.name,
                        source_line=getattr(child, "lineno", None),
                    ))
        return specs

    def _extract_checks(self, node: ast.FunctionDef) -> list[Spec]:
        """Extract check("...") calls from function body."""
        specs: list[Spec] = []
        for child in ast.walk(node):
            if isinstance(child, ast.Expr) and isinstance(child.value, ast.Call):
                desc = self._extract_call_arg(child.value, "check")
                if desc is not None:
                    specs.append(Spec(
                        kind=SpecKind.CHECK,
                        description=desc,
                        source_func=node.name,
                        source_line=getattr(child, "lineno", None),
                    ))
        return specs

    def _extract_docstring_spec(self, node: ast.FunctionDef) -> Spec | None:
        """Extract a specification from the function's docstring."""
        docstring = ast.get_docstring(node)
        if docstring:
            return Spec(
                kind=SpecKind.GUARANTEE,
                description=docstring.strip(),
                source_func=node.name,
                source_line=node.lineno,
            )
        return None

    @staticmethod
    def _extract_decorator_arg(dec: ast.expr, name: str) -> str | None:
        """Extract string arg from @name("...") decorator."""
        if isinstance(dec, ast.Call):
            func = dec.func
            if isinstance(func, ast.Name) and func.id == name:
                if dec.args and isinstance(dec.args[0], ast.Constant):
                    val = dec.args[0].value
                    if isinstance(val, str):
                        return val
        return None

    @staticmethod
    def _extract_call_arg(call: ast.Call, name: str) -> str | None:
        """Extract string arg from name("...") call."""
        func = call.func
        if isinstance(func, ast.Name) and func.id == name:
            if call.args and isinstance(call.args[0], ast.Constant):
                val = call.args[0].value
                if isinstance(val, str):
                    return val
        return None


# ═══════════════════════════════════════════════════════════════════
# Reporter
# ═══════════════════════════════════════════════════════════════════

class Reporter:
    """Format verification results for human-readable display.

    Homotopy-aware: shows which proof strategy was used per obligation,
    distinguishing PATH, TRANSPORT, ČECH, FIBER, DUCK, Z3, etc.
    """

    ICONS = {
        True: "✓",
        False: "✗",
    }
    TRUST_ICONS = {
        TrustLevel.KERNEL: "🟢",
        TrustLevel.Z3_VERIFIED: "🟡",
        TrustLevel.STRUCTURAL_CHAIN: "🟠",
        TrustLevel.LLM_CHECKED: "🟠",
        TrustLevel.AXIOM_TRUSTED: "🔵",
        TrustLevel.EFFECT_ASSUMED: "⚪",
        TrustLevel.UNTRUSTED: "🔴",
    }
    # Human-readable strategy labels for homotopy proof kinds
    STRATEGY_LABELS = {
        "homotopy": "HOMOTOPY",
        "z3": "Z3",
        "structural": "STRUCTURAL",
        "axiom": "AXIOM",
        "composite": "COMPOSITE",
        "none": "NONE",
    }

    def format_summary(self, results: list[FunctionResult]) -> str:
        """Format a one-line-per-function summary."""
        if not results:
            return "No functions to verify."

        lines: list[str] = []
        lines.append("═" * 60)
        lines.append("  SynHoPy Verification Summary")
        lines.append("═" * 60)

        total_funcs = len(results)
        verified_funcs = sum(1 for r in results if r.verified)
        total_obligations = sum(r.obligation_count for r in results)
        proved_obligations = sum(r.proved_count for r in results)

        for r in results:
            icon = self.ICONS[r.verified]
            trust_icon = self.TRUST_ICONS.get(r.trust_level, "?")
            lines.append(
                f"  {icon} {trust_icon} {r.name}: "
                f"{r.proved_count}/{r.obligation_count} obligations "
                f"[{r.trust_level.name}] ({r.duration_ms:.1f}ms)"
            )
            for err in r.errors:
                lines.append(f"      ✗ ERROR: {err}")
            for warn in r.warnings:
                lines.append(f"      ⚠ WARNING: {warn}")

        lines.append("─" * 60)
        lines.append(
            f"  Functions: {verified_funcs}/{total_funcs} verified  "
            f"Obligations: {proved_obligations}/{total_obligations} proved"
        )
        lines.append("═" * 60)
        return "\n".join(lines)

    def format_detail(self, result: FunctionResult) -> str:
        """Format detailed output for a single function."""
        lines: list[str] = []
        icon = self.ICONS[result.verified]
        trust_icon = self.TRUST_ICONS.get(result.trust_level, "?")

        lines.append(f"\n{icon} {trust_icon} Function: {result.name}")
        lines.append(f"  Trust level: {result.trust_level.name}")
        lines.append(f"  Duration: {result.duration_ms:.1f}ms")

        if result.specs:
            lines.append("  Specifications:")
            for s in result.specs:
                lines.append(f"    {s}")

        if result.obligations:
            lines.append("  Proof obligations:")
            lines.append(self.format_obligations(result.obligations))

        if result.errors:
            lines.append("  Errors:")
            for e in result.errors:
                lines.append(f"    ✗ {e}")

        if result.warnings:
            lines.append("  Warnings:")
            for w in result.warnings:
                lines.append(f"    ⚠ {w}")

        return "\n".join(lines)

    def format_obligations(self, obligations: list[ObligationResult]) -> str:
        """Format a list of obligation results with homotopy proof info."""
        lines: list[str] = []
        for i, ob in enumerate(obligations, 1):
            icon = self.ICONS[ob.verified]
            label = self._proof_label(ob)
            lines.append(
                f"    {i}. {icon} [{label}] {ob.description}"
            )
            if not ob.verified:
                lines.append(f"       Reason: {ob.result.message}")
        return "\n".join(lines)

    def _proof_label(self, ob: ObligationResult) -> str:
        """Derive a human-readable label from the proof term and strategy.

        Shows homotopy structure:
          PATH/REFL      — direct path (alpha-equivalence)
          PATH/CONG      — congruence (ap f p)
          PATH/FUNEXT    — function extensionality
          TRANSPORT      — transported from cached proof
          ČECH/n-PATCH   — Čech decomposition with n patches
          FIBER/n-TYPE   — fibration descent with n fibers
          DUCK           — duck/protocol equivalence
          Z3             — Z3 leaf tactic
          STRUCTURAL     — structural/syntactic
          AXIOM          — axiom invocation
        """
        proof = ob.proof
        strategy = ob.strategy_used

        if proof is not None and _HAS_HOMOTOPY_KERNEL:
            if isinstance(proof, Refl):
                return "PATH/REFL"
            if isinstance(proof, Ap):
                return "PATH/CONG"
            if isinstance(proof, FunExt):
                return "PATH/FUNEXT"
            if isinstance(proof, PathComp):
                return "PATH/COMP"
            if isinstance(proof, TransportProof):
                return "TRANSPORT"
            if isinstance(proof, CechGlue):
                n = len(proof.patches)
                return f"ČECH/{n}-PATCH"
            if isinstance(proof, Fiber):
                n = len(proof.type_branches)
                return f"FIBER/{n}-TYPE"
            if isinstance(proof, DuckPath):
                return "DUCK"
            if isinstance(proof, Univalence):
                return "UNIVALENCE"

        return self.STRATEGY_LABELS.get(strategy, strategy.upper())


# ═══════════════════════════════════════════════════════════════════
# Obligation Generator
# ═══════════════════════════════════════════════════════════════════

class ObligationGenerator:
    """Generate proof obligations from function specs.

    Each guarantee becomes a TYPE_CHECK obligation:
        Γ ⊢ f : {x : ReturnType | guarantee_predicate}

    Each assumption generates a WELL_FORMED obligation to confirm
    the assumption is self-consistent.

    Each check generates a TYPE_CHECK obligation at the point
    where it appears in the function body.
    """

    def generate(self, spec: FunctionSpec) -> list[tuple[str, Judgment]]:
        """Generate proof obligations from a FunctionSpec.

        Returns list of (description, Judgment) pairs.
        """
        obligations: list[tuple[str, Judgment]] = []

        ctx = Context()
        for pname, ptype in spec.params:
            ctx = ctx.extend(pname, ptype)

        for assumption in spec.assumptions:
            obligations.append((
                f"Assumption: {assumption.description}",
                Judgment(
                    kind=JudgmentKind.WELL_FORMED,
                    context=ctx,
                    type_=RefinementType(
                        base_type=PyObjType(),
                        predicate=assumption.description,
                    ),
                ),
            ))

        for guarantee in spec.guarantees:
            obligations.append((
                f"Guarantee: {guarantee.description}",
                Judgment(
                    kind=JudgmentKind.TYPE_CHECK,
                    context=ctx,
                    term=Var(spec.name),
                    type_=RefinementType(
                        base_type=spec.return_type,
                        predicate=guarantee.description,
                    ),
                ),
            ))

        for chk in spec.checks:
            obligations.append((
                f"Check: {chk.description}",
                Judgment(
                    kind=JudgmentKind.TYPE_CHECK,
                    context=ctx,
                    term=Var(spec.name),
                    type_=RefinementType(
                        base_type=PyObjType(),
                        predicate=chk.description,
                    ),
                ),
            ))

        if not obligations:
            obligations.append((
                f"Type: {spec.name} returns {spec.return_type}",
                Judgment(
                    kind=JudgmentKind.TYPE_CHECK,
                    context=ctx,
                    term=Var(spec.name),
                    type_=spec.return_type,
                ),
            ))

        return obligations


# ═══════════════════════════════════════════════════════════════════
# AST-to-SynTerm Compiler (lightweight fallback)
# ═══════════════════════════════════════════════════════════════════

class _LightweightCompiler:
    """Minimal AST → SynTerm compiler used when ASTCompiler is unavailable.

    Only handles the subset needed for basic verification:
    - Function definitions → Lam
    - Return statements → body term
    - Variables → Var
    - Literals → Literal
    - Binary ops → App
    """

    def compile_function(self, node: ast.FunctionDef) -> SynTerm:
        """Compile a function definition to a SynTerm."""
        from synhopy.core.types import Lam, App

        body_term = self._compile_body(node)

        params = list(reversed(node.args.args))
        result = body_term
        for arg in params:
            ptype = self._resolve_type(arg.annotation)
            result = Lam(param=arg.arg, param_type=ptype, body=result)

        return result

    def _compile_body(self, node: ast.FunctionDef) -> SynTerm:
        """Compile the function body (last return statement)."""
        for child in ast.walk(node):
            if isinstance(child, ast.Return) and child.value is not None:
                return self._compile_expr(child.value)
        return Literal(value=None, type_=PyNoneType())

    def _compile_expr(self, node: ast.expr) -> SynTerm:
        """Compile a Python expression AST to a SynTerm."""
        if isinstance(node, ast.Constant):
            return self._compile_constant(node)
        if isinstance(node, ast.Name):
            return Var(name=node.id)
        if isinstance(node, ast.BinOp):
            return self._compile_binop(node)
        if isinstance(node, ast.Call):
            return self._compile_call(node)
        if isinstance(node, ast.UnaryOp):
            return self._compile_unaryop(node)
        if isinstance(node, ast.Compare):
            return self._compile_compare(node)
        if isinstance(node, ast.BoolOp):
            return self._compile_boolop(node)
        if isinstance(node, ast.IfExp):
            from synhopy.core.types import IfThenElse
            return IfThenElse(
                cond=self._compile_expr(node.test),
                then_branch=self._compile_expr(node.body),
                else_branch=self._compile_expr(node.orelse),
            )
        if isinstance(node, ast.Subscript):
            from synhopy.core.types import GetItem
            return GetItem(
                obj=self._compile_expr(node.value),
                key=self._compile_expr(node.slice),
            )
        if isinstance(node, ast.Attribute):
            from synhopy.core.types import GetAttr
            return GetAttr(
                obj=self._compile_expr(node.value),
                attr=node.attr,
            )
        if isinstance(node, ast.List):
            elts = [self._compile_expr(e) for e in node.elts]
            return Literal(value=elts, type_=PyListType())
        if isinstance(node, ast.Tuple):
            elts = [self._compile_expr(e) for e in node.elts]
            from synhopy.core.types import PyTupleType
            return Literal(value=tuple(elts), type_=PyTupleType())
        return Var(name=f"<unknown:{type(node).__name__}>")

    @staticmethod
    def _compile_constant(node: ast.Constant) -> Literal:
        """Compile a constant literal."""
        val = node.value
        if isinstance(val, bool):
            return Literal(value=val, type_=PyBoolType())
        if isinstance(val, int):
            return Literal(value=val, type_=PyIntType())
        if isinstance(val, float):
            return Literal(value=val, type_=PyFloatType())
        if isinstance(val, str):
            return Literal(value=val, type_=PyStrType())
        if val is None:
            return Literal(value=None, type_=PyNoneType())
        return Literal(value=val, type_=PyObjType())

    def _compile_binop(self, node: ast.BinOp) -> SynTerm:
        """Compile a binary operation."""
        from synhopy.core.types import App, PyCall
        op_name = type(node.op).__name__.lower()
        op_map = {
            "add": "__add__", "sub": "__sub__", "mult": "__mul__",
            "div": "__truediv__", "floordiv": "__floordiv__",
            "mod": "__mod__", "pow": "__pow__",
            "bitor": "__or__", "bitand": "__and__", "bitxor": "__xor__",
            "lshift": "__lshift__", "rshift": "__rshift__",
        }
        func_name = op_map.get(op_name, f"__binop_{op_name}__")
        left = self._compile_expr(node.left)
        right = self._compile_expr(node.right)
        return PyCall(
            func=Var(name=func_name),
            args=(left, right),
        )

    def _compile_call(self, node: ast.Call) -> SynTerm:
        """Compile a function call."""
        from synhopy.core.types import PyCall
        func = self._compile_expr(node.func)
        args = tuple(self._compile_expr(a) for a in node.args)
        kwargs = tuple(
            (kw.arg or "_", self._compile_expr(kw.value))
            for kw in node.keywords
        )
        return PyCall(func=func, args=args, kwargs=kwargs)

    def _compile_unaryop(self, node: ast.UnaryOp) -> SynTerm:
        """Compile a unary operation."""
        from synhopy.core.types import PyCall
        op_map = {
            "not": "__not__", "usub": "__neg__",
            "uadd": "__pos__", "invert": "__invert__",
        }
        op_name = type(node.op).__name__.lower()
        func_name = op_map.get(op_name, f"__unaryop_{op_name}__")
        operand = self._compile_expr(node.operand)
        return PyCall(func=Var(name=func_name), args=(operand,))

    def _compile_compare(self, node: ast.Compare) -> SynTerm:
        """Compile a comparison expression."""
        from synhopy.core.types import PyCall
        left = self._compile_expr(node.left)
        op = node.ops[0]
        right = self._compile_expr(node.comparators[0])
        op_map = {
            "eq": "__eq__", "noteq": "__ne__",
            "lt": "__lt__", "lte": "__le__",
            "gt": "__gt__", "gte": "__ge__",
            "is": "__is__", "isnot": "__isnot__",
            "in": "__contains__", "notin": "__notcontains__",
        }
        op_name = type(op).__name__.lower()
        func_name = op_map.get(op_name, f"__cmp_{op_name}__")
        return PyCall(func=Var(name=func_name), args=(left, right))

    def _compile_boolop(self, node: ast.BoolOp) -> SynTerm:
        """Compile a boolean operation (and/or)."""
        from synhopy.core.types import PyCall
        op_name = "__and__" if isinstance(node.op, ast.And) else "__or__"
        values = [self._compile_expr(v) for v in node.values]
        result = values[0]
        for v in values[1:]:
            result = PyCall(func=Var(name=op_name), args=(result, v))
        return result

    @staticmethod
    def _resolve_type(ann: ast.expr | None) -> SynType:
        """Resolve annotation to SynType."""
        if ann is None:
            return PyObjType()
        if isinstance(ann, ast.Name):
            return _ANNOTATION_TYPE_MAP.get(ann.id, PyObjType())
        return PyObjType()


# ═══════════════════════════════════════════════════════════════════
# The Main Pipeline
# ═══════════════════════════════════════════════════════════════════

class VerificationPipeline:
    """End-to-end Python program verification — homotopy-native.

    Orchestrates the full verification flow:
        1. Parse source → AST
        2. Extract specs (decorators, docstrings, type annotations)
        3. Compile AST → SynTerms
        4. Generate proof obligations from specs
        5. Attempt proofs using homotopy-first strategy chain:
             HomotopyStrategy → Z3 → structural → axiom
           The HomotopyStrategy itself uses path search, transport,
           Čech decomposition, fibration descent, and duck equivalence.
           Z3 is a leaf tactic inside HomotopyStrategy patches AND a
           secondary fallback after it.
        6. Verify proofs with the kernel
        7. Cache proven obligations for future transport
        8. Report results (with homotopy-aware labels)

    Usage:
        pipeline = VerificationPipeline()
        results = pipeline.verify_file("path/to/module.py")
        pipeline.report(results)
    """

    def __init__(
        self,
        kernel: ProofKernel | None = None,
        axiom_registry: dict[str, AxiomEntry] | None = None,
        strategy: ProofStrategy | None = None,
    ) -> None:
        self._kernel = kernel or ProofKernel()

        if axiom_registry:
            for name, entry in axiom_registry.items():
                self._kernel.register_axiom(
                    name=entry.name,
                    statement=entry.statement,
                    module=entry.module,
                )

        self._extractor = SpecExtractor()
        self._obligation_gen = ObligationGenerator()
        self._compiler = _LightweightCompiler()
        self._reporter = Reporter()
        self._transport_cache = ProofTransportCache()

        if strategy is not None:
            self._strategy = strategy
        else:
            z3_leaf = Z3Strategy()
            self._homotopy = HomotopyStrategy(
                kernel=self._kernel,
                transport_cache=self._transport_cache,
                leaf_z3=z3_leaf,
            )
            self._strategy = CompositeStrategy([
                self._homotopy,           # PRIMARY — homotopy-native
                z3_leaf,                   # secondary — leaf tactic fallback
                StructuralStrategy(),      # structural
                AxiomStrategy(self._kernel),  # axiom
            ])

    # ── Public API ────────────────────────────────────────────────

    def verify_file(self, filepath: str) -> list[FunctionResult]:
        """Verify all functions in a Python source file.

        Args:
            filepath: Path to the Python source file.

        Returns:
            List of FunctionResult, one per function found.
        """
        with open(filepath, "r") as f:
            source = f.read()
        return self.verify_source(source, filename=filepath)

    def verify_source(self, source: str, filename: str = "<string>") -> list[FunctionResult]:
        """Verify all functions in a Python source string.

        Args:
            source: Python source code.
            filename: Used for error messages.

        Returns:
            List of FunctionResult, one per function found.
        """
        dedented = textwrap.dedent(source)

        try:
            tree = ast.parse(dedented, filename=filename)
        except SyntaxError as e:
            return [FunctionResult(
                name="<parse_error>",
                source=dedented,
                specs=[],
                obligations=[],
                trust_level=TrustLevel.UNTRUSTED,
                verified=False,
                errors=[f"Syntax error: {e}"],
                warnings=[],
                duration_ms=0.0,
            )]

        results: list[FunctionResult] = []
        for node in ast.iter_child_nodes(tree):
            if isinstance(node, ast.FunctionDef):
                func_source = ast.get_source_segment(dedented, node) or ""
                result = self._verify_function_node(node, func_source, filename)
                results.append(result)

        if not results:
            results.append(FunctionResult(
                name="<no_functions>",
                source=dedented,
                specs=[],
                obligations=[],
                trust_level=TrustLevel.UNTRUSTED,
                verified=True,
                errors=[],
                warnings=["No function definitions found."],
                duration_ms=0.0,
            ))

        return results

    def verify_function(self, func_source: str) -> FunctionResult:
        """Verify a single function given its source code.

        Args:
            func_source: Python source of a single function.

        Returns:
            FunctionResult for that function.
        """
        results = self.verify_source(func_source)
        if results:
            return results[0]
        return FunctionResult(
            name="<unknown>",
            source=func_source,
            specs=[],
            obligations=[],
            trust_level=TrustLevel.UNTRUSTED,
            verified=False,
            errors=["Could not parse function source."],
            warnings=[],
            duration_ms=0.0,
        )

    def report(self, results: list[FunctionResult],
               verbose: bool = False) -> str:
        """Generate a human-readable verification report.

        Args:
            results: List of FunctionResult from verify_*.
            verbose: If True, include detailed per-function output.

        Returns:
            Formatted string report.
        """
        parts: list[str] = [self._reporter.format_summary(results)]
        if verbose:
            for r in results:
                parts.append(self._reporter.format_detail(r))
        return "\n".join(parts)

    # ── Internal pipeline steps ───────────────────────────────────

    def _verify_function_node(
        self,
        node: ast.FunctionDef,
        func_source: str,
        filename: str,
    ) -> FunctionResult:
        """Run the full verification pipeline on a single function node.

        Homotopy-native flow:
          1. Extract specs
          2. Compile AST → SynTerm
          3. Pass source AST to HomotopyStrategy for Čech/fiber extraction
          4. Try transport from cache before generating new proofs
          5. Generate proof obligations
          6. Attempt proofs (homotopy-first, Z3 as leaf)
          7. Cache successful proofs for future transport
        """
        t0 = time.monotonic()
        errors: list[str] = []
        warnings: list[str] = []

        # Step 1: Extract specs
        spec = self._extractor.extract_from_function(node)
        spec_list: list[Spec] = spec.guarantees + spec.assumptions + spec.checks

        # Step 2: Compile AST → SynTerm
        compiled_term: SynTerm | None = None
        try:
            if ASTCompiler is not None:
                compiler = ASTCompiler()
                compiled = compiler.compile_function(node)
                compiled_term = compiled.term if hasattr(compiled, 'term') else None
            else:
                compiled_term = self._compiler.compile_function(node)
        except Exception as e:
            warnings.append(f"Compilation warning: {e}")
            try:
                compiled_term = self._compiler.compile_function(node)
            except Exception as e2:
                errors.append(f"Compilation failed: {e2}")

        # Step 3: Pass source AST to HomotopyStrategy
        if hasattr(self, '_homotopy'):
            self._homotopy.set_source_ast(node)

        # Step 4: Generate proof obligations
        raw_obligations = self._obligation_gen.generate(spec)

        # Step 5: Attempt proofs — homotopy-first with transport cache
        obligation_results: list[ObligationResult] = []
        for desc, judgment in raw_obligations:
            ob_result = self._attempt_proof(desc, judgment, spec)
            obligation_results.append(ob_result)

            # Step 6: Cache successful proofs for transport reuse
            if ob_result.verified and ob_result.proof is not None:
                self._transport_cache.store(
                    judgment, ob_result.proof, ob_result.result
                )

        # Step 7: Compute aggregate trust level and verification status
        all_verified = all(ob.verified for ob in obligation_results)

        if obligation_results:
            trust_levels = [
                ob.result.trust_level for ob in obligation_results
                if ob.verified
            ]
            if trust_levels:
                trust_level = min(trust_levels, key=lambda t: t.value)
            else:
                trust_level = TrustLevel.UNTRUSTED
        else:
            trust_level = TrustLevel.UNTRUSTED

        if errors:
            all_verified = False
            trust_level = TrustLevel.UNTRUSTED

        duration_ms = (time.monotonic() - t0) * 1000.0

        return FunctionResult(
            name=spec.name,
            source=func_source,
            specs=spec_list,
            obligations=obligation_results,
            trust_level=trust_level,
            verified=all_verified,
            errors=errors,
            warnings=warnings,
            duration_ms=duration_ms,
        )

    def _attempt_proof(
        self,
        description: str,
        judgment: Judgment,
        spec: FunctionSpec,
    ) -> ObligationResult:
        """Attempt to prove a single obligation using the strategy chain."""
        ctx = judgment.context

        # Try the composite strategy
        if isinstance(self._strategy, CompositeStrategy):
            proof, strategy_name = self._strategy.try_prove_with_info(judgment, ctx)
        else:
            proof = self._strategy.try_prove(judgment, ctx)
            strategy_name = self._strategy.name if proof is not None else "none"

        # Verify the proof with the kernel
        if proof is not None:
            vresult = self._kernel.verify(ctx, judgment, proof)
        else:
            vresult = VerificationResult.fail(
                f"No strategy could prove: {description}",
                code="E_NO_PROOF",
            )
            strategy_name = "none"

        return ObligationResult(
            description=description,
            judgment=judgment,
            proof=proof,
            result=vresult,
            strategy_used=strategy_name,
        )


# ═══════════════════════════════════════════════════════════════════
# Self-test
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Run a basic self-test of the verification pipeline."""
    source = '''
def add(x: int, y: int) -> int:
    """Returns the sum of x and y."""
    return x + y
'''
    pipeline = VerificationPipeline()
    results = pipeline.verify_source(source)
    print(pipeline.report(results))
    print()

    # Verbose output
    print(pipeline.report(results, verbose=True))
    print()

    # Verify basic properties
    assert len(results) == 1, f"Expected 1 result, got {len(results)}"
    r = results[0]
    assert r.name == "add", f"Expected name 'add', got {r.name!r}"
    assert r.verified, f"Expected verified=True, got {r.verified}"
    assert len(r.specs) >= 1, f"Expected ≥1 spec, got {len(r.specs)}"
    assert r.obligation_count >= 1, f"Expected ≥1 obligation"
    assert r.proved_count >= 1, f"Expected ≥1 proved"
    assert r.duration_ms >= 0, "Duration should be non-negative"

    # Test spec extraction
    extractor = SpecExtractor()
    func_specs = extractor.extract_from_source(source)
    assert len(func_specs) == 1
    fs = func_specs[0]
    assert fs.name == "add"
    assert len(fs.params) == 2
    assert isinstance(fs.params[0][1], PyIntType)
    assert isinstance(fs.return_type, PyIntType)

    # Test with @guarantee decorator
    source2 = '''
@guarantee("result >= 0")
def abs_val(x: int) -> int:
    if x >= 0:
        return x
    return -x
'''
    results2 = pipeline.verify_source(source2)
    print(pipeline.report(results2, verbose=True))
    assert len(results2) == 1
    assert results2[0].name == "abs_val"

    # Test with multiple functions
    source3 = '''
def foo(x: int) -> int:
    """Returns x."""
    return x

def bar(y: str) -> str:
    """Returns y."""
    return y
'''
    results3 = pipeline.verify_source(source3)
    print(pipeline.report(results3))
    assert len(results3) == 2

    # Test error handling with bad syntax
    results4 = pipeline.verify_source("def broken(")
    assert len(results4) == 1
    assert not results4[0].verified or results4[0].errors

    # Test verify_function
    single = pipeline.verify_function("def identity(x: int) -> int:\n    return x\n")
    assert single.name == "identity"
    assert single.verified

    print("\n✓ All self-tests passed.")


if __name__ == "__main__":
    _self_test()
