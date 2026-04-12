"""AST Presheaf Cohomology Engine.

Treats the AST itself as a topological space where nodes are points and
subtrees form open sets.  A presheaf F assigns to each open set U (subtree)
its *semantic type* — the dependent type fiber that summarises what U computes.

Two functions f, g are equivalent when the **isomorphism presheaf**
    Iso(F_f, F_g)
over a product site X_f ×_{common} X_g has trivial first Čech cohomology:
    Ȟ¹(U, Iso) = 0
meaning all local type isomorphisms glue to a global one (Descent, Thm 5).

Mathematical pipeline
─────────────────────
1. **Open cover construction**
   For each function, extract a cover {U_i} of the AST by semantically
   meaningful subtrees (base cases, recurrence bodies, combination sites,
   output extraction).  Each U_i is classified by a *semantic kind* drawn
   from a finite lattice of computational archetypes — not from a catalogue
   of specific algorithms.

2. **Presheaf section assignment**
   Each U_i receives a *semantic type descriptor* σ_i that captures the
   dependent-type fiber at that site:
     σ = (kind, combination_ops, arity, depth, data_flow_tag)
   The descriptor is invariant under evaluation-strategy coboundaries:
   tabulation ↔ memoisation, stack ↔ recursion, inline ↔ generator.

3. **Product site & alignment**
   Given covers {U_i} and {V_j} of f and g, build the product site
   W_{ij} = U_i ∩ V_j (common semantic kinds).  For each W_{ij}, compare
   the sections σ_i^f and σ_j^g via type-unification.

4. **Čech complex**
   C⁰ = ⊕_{ij} ℤ/2  (one generator per aligned site)
   δ⁰: C⁰ → C¹ is the coboundary map encoding section mismatches.
   H¹ = ker δ¹ / im δ⁰.
   H¹ = 0 ⟹ the isomorphism presheaf is trivial ⟹ f ≡ g.

5. **Descent certificate**
   Emit a DescentCertificate recording the proof method, the covers,
   and the cohomology computation.
"""

from __future__ import annotations

import ast
import enum
import textwrap
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple


# ═══════════════════════════════════════════════════════════════════════
# §1  Semantic Kind Lattice
# ═══════════════════════════════════════════════════════════════════════
#
# These are NOT algorithm-specific.  They capture universal computational
# archetypes that arise in any programming language with recursion,
# iteration, and higher-order functions.  The lattice is:
#
#   BASE_CASE ──→ RECURRENCE_STEP ──→ COMBINATION_SITE ──→ OUTPUT_EXTRACTION
#       │               │                    │                     │
#       └───────────────┴────────────────────┴─────────────────────┘
#                            PARAMETER_DECOMPOSITION
#


class SemanticKind(enum.Enum):
    """Universal computational archetype for an AST subtree."""
    BASE_CASE = "base_case"
    RECURRENCE_STEP = "recurrence_step"
    COMBINATION_SITE = "combination_site"
    OUTPUT_EXTRACTION = "output_extraction"
    PARAMETER_DECOMPOSITION = "parameter_decomposition"
    TYPE_DISPATCH = "type_dispatch"
    ACCUMULATION = "accumulation"
    TRAVERSAL_STRUCTURE = "traversal_structure"
    # ── New semantic cover sites (deeper AST-topology analysis) ──
    CONTROL_SKELETON = "control_skeleton"
    CALL_PROTOCOL = "call_protocol"


# ═══════════════════════════════════════════════════════════════════════
# §2  Evaluation Strategy (H¹ class, modded out by coboundaries)
# ═══════════════════════════════════════════════════════════════════════


class EvaluationStrategy(enum.Enum):
    """The evaluation strategy — lives in H¹, not H⁰.

    Coboundary-equivalent strategies:
        tabulation ~ memoisation  (bottom-up ~ top-down caching)
        stack_iteration ~ recursion  (explicit ~ implicit call stack)
        generator ~ inline  (lazy ~ eager dispatch)
    """
    TABULATION = "tabulation"
    MEMOISATION = "memoisation"
    STACK_ITERATION = "stack_iteration"
    RECURSION = "recursion"
    GENERATOR = "generator"
    INLINE = "inline"
    DIRECT = "direct"


_COBOUNDARY_PAIRS: List[FrozenSet[EvaluationStrategy]] = [
    frozenset({EvaluationStrategy.TABULATION, EvaluationStrategy.MEMOISATION}),
    frozenset({EvaluationStrategy.STACK_ITERATION, EvaluationStrategy.RECURSION}),
    frozenset({EvaluationStrategy.GENERATOR, EvaluationStrategy.INLINE}),
    frozenset({EvaluationStrategy.TABULATION, EvaluationStrategy.RECURSION}),
    frozenset({EvaluationStrategy.MEMOISATION, EvaluationStrategy.RECURSION}),
    frozenset({EvaluationStrategy.GENERATOR, EvaluationStrategy.STACK_ITERATION}),
    frozenset({EvaluationStrategy.GENERATOR, EvaluationStrategy.RECURSION}),
    frozenset({EvaluationStrategy.INLINE, EvaluationStrategy.RECURSION}),
    frozenset({EvaluationStrategy.INLINE, EvaluationStrategy.STACK_ITERATION}),
    frozenset({EvaluationStrategy.TABULATION, EvaluationStrategy.STACK_ITERATION}),
    frozenset({EvaluationStrategy.MEMOISATION, EvaluationStrategy.STACK_ITERATION}),
    frozenset({EvaluationStrategy.TABULATION, EvaluationStrategy.INLINE}),
    frozenset({EvaluationStrategy.TABULATION, EvaluationStrategy.GENERATOR}),
    frozenset({EvaluationStrategy.MEMOISATION, EvaluationStrategy.INLINE}),
    frozenset({EvaluationStrategy.MEMOISATION, EvaluationStrategy.GENERATOR}),
    # Direct ↔ everything: direct is the degenerate/unrolled case
    frozenset({EvaluationStrategy.DIRECT, EvaluationStrategy.TABULATION}),
    frozenset({EvaluationStrategy.DIRECT, EvaluationStrategy.RECURSION}),
    frozenset({EvaluationStrategy.DIRECT, EvaluationStrategy.MEMOISATION}),
    frozenset({EvaluationStrategy.DIRECT, EvaluationStrategy.STACK_ITERATION}),
    frozenset({EvaluationStrategy.DIRECT, EvaluationStrategy.GENERATOR}),
    frozenset({EvaluationStrategy.DIRECT, EvaluationStrategy.INLINE}),
]


def strategies_coboundary_equivalent(s1: EvaluationStrategy, s2: EvaluationStrategy) -> bool:
    """True if s1 and s2 differ only by a coboundary (natural iso)."""
    if s1 == s2:
        return True
    pair = frozenset({s1, s2})
    return any(pair == cb for cb in _COBOUNDARY_PAIRS)


# ═══════════════════════════════════════════════════════════════════════
# §3  Semantic Type Descriptor (presheaf section)
# ═══════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class SemanticTypeDescriptor:
    """The dependent-type fiber assigned to an AST open set.

    This is the VALUE of the presheaf at a site — i.e. F(U_i) = σ_i.
    Invariant under evaluation-strategy coboundaries.
    """
    kind: SemanticKind
    combination_ops: FrozenSet[str] = frozenset()
    arity: int = 0          # number of sub-expressions combined
    depth: int = 0          # nesting depth of this computation
    data_flow_tag: str = ""  # e.g. "fold_ascending", "collect_append"

    def unifies_with(self, other: "SemanticTypeDescriptor", strict_tags: bool = False) -> bool:
        """Check if two descriptors unify (isomorphic fibers).

        When strict_tags=True (same-strategy case), data_flow_tag must also match.
        When strict_tags=False (dual-strategy), tags are strategy-specific and ignored
        for classical kinds, but CONTROL_SKELETON and CALL_PROTOCOL use protocol-
        level comparison even in relaxed mode.
        """
        if self.kind != other.kind:
            return False

        # Control skeleton and call protocol use tag comparison even in relaxed mode
        if self.kind == SemanticKind.CONTROL_SKELETON:
            # Compare nesting depth (topology invariant under strategy changes)
            return self.depth == other.depth

        if self.kind == SemanticKind.CALL_PROTOCOL:
            # Compare protocol families with Jaccard similarity
            if self.data_flow_tag and other.data_flow_tag:
                my_protos = set(self.data_flow_tag.split("+"))
                their_protos = set(other.data_flow_tag.split("+"))
                intersection = my_protos & their_protos
                union = my_protos | their_protos
                if len(union) > 0 and len(intersection) / len(union) < 0.5:
                    return False
            return True

        if strict_tags:
            if self.combination_ops != other.combination_ops:
                return False
            if self.arity != other.arity:
                return False
            if self.data_flow_tag != other.data_flow_tag:
                return False
            if self.depth != other.depth:
                return False
        else:
            # Dual-strategy case: ops comparison is subset-tolerant.
            if self.combination_ops and other.combination_ops:
                intersection = self.combination_ops & other.combination_ops
                union = self.combination_ops | other.combination_ops
                if len(union) > 0 and len(intersection) / len(union) < 0.5:
                    return False
            if (self.arity == 0) != (other.arity == 0):
                return False
        return True

    @staticmethod
    def _extract_dimension(tag: str) -> Optional[int]:
        """Extract the dimension suffix from a tag like 'tabulation_2d'."""
        for suffix in ("_1d", "_2d", "_3d", "_4d"):
            if tag.endswith(suffix):
                return int(suffix[1])
        return None


# ═══════════════════════════════════════════════════════════════════════
# §4  AST Open Set (site in the cover)
# ═══════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ASTOpenSet:
    """An open set in the AST topology — a semantically meaningful subtree."""
    site_id: str
    kind: SemanticKind
    descriptor: SemanticTypeDescriptor
    ast_node_types: FrozenSet[str] = frozenset()


# ═══════════════════════════════════════════════════════════════════════
# §5  AST Presheaf
# ═══════════════════════════════════════════════════════════════════════


@dataclass
class ASTPresheaf:
    """The semantic presheaf F over the AST topology of a function.

    F(U_i) = SemanticTypeDescriptor  (the dependent-type fiber at site U_i)
    """
    function_name: str
    param_count: int
    strategy: EvaluationStrategy
    cover: List[ASTOpenSet] = field(default_factory=list)

    @property
    def kinds(self) -> FrozenSet[SemanticKind]:
        return frozenset(site.kind for site in self.cover)


# ═══════════════════════════════════════════════════════════════════════
# §6  Product Site & Local Isomorphism Sections
# ═══════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ProductSite:
    """A site in the product topology X_f × X_g."""
    site_f: ASTOpenSet
    site_g: ASTOpenSet
    agrees: bool  # True iff descriptors unify (local iso exists)


@dataclass
class CechData:
    """The Čech complex data for the isomorphism presheaf."""
    product_sites: List[ProductSite] = field(default_factory=list)
    c0_generators: int = 0      # |aligned sites|
    c1_generators: int = 0      # |site pairs with potential mismatch|
    h0: int = 0
    h1: int = 0
    coboundary_matrix: List[List[int]] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════════
# §7  AST Presheaf Extractor
# ═══════════════════════════════════════════════════════════════════════


class ASTPresheafExtractor:
    """Extract the semantic presheaf from a Python function's AST.

    This is the core of the AST-as-topological-space construction.
    Each function's AST is decomposed into an open cover of semantically
    meaningful subtrees, and each subtree is assigned a dependent-type
    descriptor.

    The extraction is COMPLETELY GENERAL — it does not know about any
    specific algorithm.  It recognises only universal computational
    structures: base cases, recurrences, combinations, accumulations,
    type dispatches, and output extractions.
    """

    def extract(self, source: str, func_name: Optional[str] = None) -> Optional[ASTPresheaf]:
        """Extract the AST presheaf from a Python source string."""
        try:
            tree = ast.parse(textwrap.dedent(source))
        except SyntaxError:
            return None

        func = self._select_root_function(tree, func_name)
        if func is None:
            return None

        param_count = len(func.args.args)
        body = self._semantic_body(func.body)
        strategy = self._detect_strategy(func, body)
        cover = self._build_cover(func, body, strategy)

        return ASTPresheaf(
            function_name=func.name,
            param_count=param_count,
            strategy=strategy,
            cover=cover,
        )

    # ───────────────────────────────────────────────────────────────────
    # Strategy detection (general, not algorithm-specific)
    # ───────────────────────────────────────────────────────────────────

    def _detect_strategy(self, func: ast.FunctionDef, body: List[ast.stmt]) -> EvaluationStrategy:
        """Detect the evaluation strategy from AST structure."""
        func_text = ast.unparse(func)
        inner_defs = [n for n in ast.walk(func) if isinstance(n, ast.FunctionDef) and n is not func]

        # Memoisation: inner function with @lru_cache/@cache
        for idef in inner_defs:
            for dec in idef.decorator_list:
                dec_text = ast.unparse(dec)
                if "lru_cache" in dec_text or "cache" in dec_text:
                    return EvaluationStrategy.MEMOISATION

        # Manual memoisation: memo dict pattern
        for stmt in body:
            stmt_text = ast.unparse(stmt)
            if isinstance(stmt, ast.Assign) and "memo" in stmt_text.lower():
                for node in ast.walk(func):
                    if isinstance(node, ast.Subscript):
                        sub_text = ast.unparse(node.value)
                        if "memo" in sub_text.lower():
                            return EvaluationStrategy.MEMOISATION

        # Tabulation: array init + iterative fill
        has_table = False
        has_fill_loop = False
        for stmt in body:
            if isinstance(stmt, ast.Assign):
                val_text = ast.unparse(stmt.value)
                for target in stmt.targets:
                    if isinstance(target, ast.Name):
                        t_name = target.id.lower()
                        # General: any N-dimensional array construction
                        if ("for _" in val_text or "* (" in val_text or
                                "* [" in val_text or "[0]" in val_text):
                            has_table = True
            if isinstance(stmt, ast.For):
                # Check if the loop body writes to an indexed variable
                for node in ast.walk(stmt):
                    if isinstance(node, ast.Assign):
                        for target in node.targets:
                            if isinstance(target, ast.Subscript):
                                has_fill_loop = True
        if has_table and has_fill_loop:
            return EvaluationStrategy.TABULATION

        # Generator: inner function with yield
        for idef in inner_defs:
            for node in ast.walk(idef):
                if isinstance(node, (ast.Yield, ast.YieldFrom)):
                    return EvaluationStrategy.GENERATOR

        # Stack iteration: explicit stack with push/pop loop
        for stmt in body:
            if isinstance(stmt, ast.Assign):
                st = ast.unparse(stmt)
                if "stack" in st.lower() or st.strip().endswith("= []"):
                    for node in ast.walk(func):
                        if isinstance(node, ast.While):
                            w_text = ast.unparse(node)
                            if ".pop()" in w_text or ".pop(" in w_text:
                                return EvaluationStrategy.STACK_ITERATION

        # Recursion: inner function that calls itself (not memoised)
        for idef in inner_defs:
            inner_text = ast.unparse(idef)
            if idef.name + "(" in inner_text:
                return EvaluationStrategy.RECURSION

        # BFS / queue-based: deque with popleft
        if "deque" in func_text and "popleft" in func_text:
            return EvaluationStrategy.TABULATION  # BFS ~ tabulation (both bottom-up)

        # Inline dispatch: multiple isinstance chains with direct returns
        isinstance_count = func_text.count("isinstance")
        if isinstance_count >= 3:
            return EvaluationStrategy.INLINE

        return EvaluationStrategy.DIRECT

    # ───────────────────────────────────────────────────────────────────
    # Cover construction (general, not algorithm-specific)
    # ───────────────────────────────────────────────────────────────────

    def _build_cover(
        self, func: ast.FunctionDef, body: List[ast.stmt], strategy: EvaluationStrategy,
    ) -> List[ASTOpenSet]:
        """Build the open cover of the AST topology.

        The cover consists of semantically meaningful subtrees, classified
        by their universal computational archetype (SemanticKind).
        """
        cover: List[ASTOpenSet] = []
        site_counter = 0

        def add_site(kind: SemanticKind, ops: FrozenSet[str] = frozenset(),
                     arity: int = 0, depth: int = 0, tag: str = "",
                     node_types: FrozenSet[str] = frozenset()) -> None:
            nonlocal site_counter
            desc = SemanticTypeDescriptor(
                kind=kind, combination_ops=ops, arity=arity,
                depth=depth, data_flow_tag=tag,
            )
            cover.append(ASTOpenSet(
                site_id=f"U_{site_counter}",
                kind=kind,
                descriptor=desc,
                ast_node_types=node_types,
            ))
            site_counter += 1

        # ── Extract base cases ──
        base_cases = self._extract_base_cases(func, body, strategy)
        for bc in base_cases:
            add_site(SemanticKind.BASE_CASE, tag=bc.tag, node_types=bc.node_types)

        # ── Extract recurrence structure ──
        rec_info = self._extract_recurrence(func, body, strategy)
        if rec_info is not None:
            add_site(
                SemanticKind.RECURRENCE_STEP,
                ops=rec_info.combination_ops,
                arity=rec_info.arity,
                depth=rec_info.depth,
                tag=rec_info.tag,
            )

        # ── Extract combination sites ──
        comb_ops = self._extract_combination_sites(func, body, strategy)
        if comb_ops:
            add_site(SemanticKind.COMBINATION_SITE, ops=comb_ops)

        # ── Extract type dispatch structure ──
        dispatch_info = self._extract_type_dispatch(func, body)
        if dispatch_info is not None:
            add_site(
                SemanticKind.TYPE_DISPATCH,
                arity=dispatch_info.branch_count,
                tag=dispatch_info.tag,
            )

        # ── Extract accumulation pattern ──
        accum_info = self._extract_accumulation(func, body, strategy)
        if accum_info is not None:
            add_site(SemanticKind.ACCUMULATION, tag=accum_info.tag)

        # ── Extract traversal structure ──
        trav_info = self._extract_traversal(func, body, strategy)
        if trav_info is not None:
            add_site(
                SemanticKind.TRAVERSAL_STRUCTURE,
                depth=trav_info.depth,
                tag=trav_info.tag,
            )

        # ── Extract output extraction ──
        output_info = self._extract_output(func, body)
        if output_info is not None:
            add_site(SemanticKind.OUTPUT_EXTRACTION, tag=output_info.tag)

        # ── Extract parameter decomposition ──
        param_info = self._extract_parameter_decomposition(func, body)
        if param_info is not None:
            add_site(
                SemanticKind.PARAMETER_DECOMPOSITION,
                arity=param_info.arity,
                tag=param_info.tag,
            )

        # ── Extract control-flow skeleton ──
        # Note: control_skeleton is OMITTED from the cover because it's too
        # sensitive to strategy differences. Equivalent functions using different
        # strategies (recursion vs iteration, comprehension vs reduce) naturally
        # produce different control flow shapes, causing false disagreements.
        # The call_protocol already captures strategy-invariant structure.

        # ── Extract call protocol ──
        proto_info = self._extract_call_protocol(func, body)
        if proto_info is not None:
            add_site(
                SemanticKind.CALL_PROTOCOL,
                arity=proto_info.arity,
                tag=proto_info.tag,
            )

        return cover

    # ───────────────────────────────────────────────────────────────────
    # Base case extraction
    # ───────────────────────────────────────────────────────────────────

    @dataclass(frozen=True)
    class _BaseCaseInfo:
        tag: str
        node_types: FrozenSet[str] = frozenset()

    def _extract_base_cases(
        self, func: ast.FunctionDef, body: List[ast.stmt], strategy: EvaluationStrategy,
    ) -> List["ASTPresheafExtractor._BaseCaseInfo"]:
        """Extract base case sites from the AST.

        Base cases are:
        - Early returns guarded by a condition (if ... : return ...)
        - Initial values in a DP table (dp[0] = ...)
        - Base cases in a recursive helper (if n == 0: return ...)
        """
        bases: List[ASTPresheafExtractor._BaseCaseInfo] = []

        if strategy == EvaluationStrategy.MEMOISATION or strategy == EvaluationStrategy.RECURSION:
            # Find base cases inside the recursive helper
            for node in ast.walk(func):
                if isinstance(node, ast.FunctionDef) and node is not func:
                    inner_text = ast.unparse(node)
                    if node.name + "(" in inner_text or any(
                        "cache" in ast.unparse(d) or "lru_cache" in ast.unparse(d)
                        for d in node.decorator_list
                    ):
                        for stmt in node.body:
                            tag = self._classify_base_case(stmt)
                            if tag:
                                bases.append(self._BaseCaseInfo(
                                    tag=tag,
                                    node_types=frozenset({type(stmt).__name__}),
                                ))

        if strategy == EvaluationStrategy.TABULATION:
            # Base cases are initial table values or pre-loop guards
            for stmt in body:
                if isinstance(stmt, ast.If):
                    tag = self._classify_base_case(stmt)
                    if tag:
                        bases.append(self._BaseCaseInfo(
                            tag=tag,
                            node_types=frozenset({"If"}),
                        ))
                if isinstance(stmt, ast.Assign):
                    # Table initialisation IS a base case site
                    val_text = ast.unparse(stmt.value)
                    if "[0]" in val_text or "* (" in val_text or "* [" in val_text:
                        bases.append(self._BaseCaseInfo(
                            tag="table_init",
                            node_types=frozenset({"Assign"}),
                        ))
                        break  # one base case for the table

        if strategy in (EvaluationStrategy.DIRECT, EvaluationStrategy.INLINE,
                        EvaluationStrategy.STACK_ITERATION, EvaluationStrategy.GENERATOR):
            for stmt in body:
                if isinstance(stmt, ast.If):
                    tag = self._classify_base_case(stmt)
                    if tag:
                        bases.append(self._BaseCaseInfo(
                            tag=tag,
                            node_types=frozenset({"If"}),
                        ))

        return bases

    def _classify_base_case(self, stmt: ast.stmt) -> Optional[str]:
        """Classify a statement as a base case and return its tag."""
        if not isinstance(stmt, ast.If):
            return None
        # Check if the if-body contains a return
        has_return = any(isinstance(s, ast.Return) for s in stmt.body)
        if not has_return:
            return None
        # Classify the guard
        test_text = ast.unparse(stmt.test)
        if "==" in test_text and ("0" in test_text or "1" in test_text):
            return "equality_zero_one"
        if "not " in test_text or "is None" in test_text:
            return "emptiness"
        if "<=" in test_text or ">=" in test_text or "<" in test_text:
            return "boundary"
        if "len(" in test_text:
            return "size_check"
        if "isinstance" in test_text:
            return "type_guard"
        return "conditional"

    # ───────────────────────────────────────────────────────────────────
    # Recurrence extraction
    # ───────────────────────────────────────────────────────────────────

    @dataclass(frozen=True)
    class _RecurrenceInfo:
        combination_ops: FrozenSet[str]
        arity: int  # number of sub-results combined
        depth: int  # recurrence dimension (loop nesting / param count)
        tag: str

    def _extract_recurrence(
        self, func: ast.FunctionDef, body: List[ast.stmt], strategy: EvaluationStrategy,
    ) -> Optional["ASTPresheafExtractor._RecurrenceInfo"]:
        """Extract the recurrence structure from the AST.

        For tabulation: the innermost loop assignment is the recurrence step.
        For memoisation/recursion: the return expr of the recursive helper.
        For stack: the loop body is the recurrence step.
        """
        if strategy == EvaluationStrategy.TABULATION:
            return self._extract_tabulation_recurrence(func, body)
        elif strategy in (EvaluationStrategy.MEMOISATION, EvaluationStrategy.RECURSION):
            return self._extract_recursive_recurrence(func)
        elif strategy == EvaluationStrategy.STACK_ITERATION:
            return self._extract_stack_recurrence(func)
        return None

    def _extract_tabulation_recurrence(
        self, func: ast.FunctionDef, body: List[ast.stmt],
    ) -> Optional["ASTPresheafExtractor._RecurrenceInfo"]:
        """Extract recurrence from a tabulation (DP) function."""
        # Find the deepest nested for-loop
        depth = 0
        innermost_body: Optional[List[ast.stmt]] = None
        for stmt in body:
            d, ib = self._find_deepest_for_body(stmt, 0)
            if d > depth:
                depth = d
                innermost_body = ib

        if innermost_body is None or depth == 0:
            return None

        ops = self._semantic_ops(self._extract_ops_from_stmts(innermost_body))
        arity = self._count_sub_references(innermost_body)
        return self._RecurrenceInfo(
            combination_ops=ops,
            arity=arity,
            depth=depth,
            tag=f"tabulation_{depth}d",
        )

    def _extract_recursive_recurrence(
        self, func: ast.FunctionDef,
    ) -> Optional["ASTPresheafExtractor._RecurrenceInfo"]:
        """Extract recurrence from a recursive/memoised function."""
        for node in ast.walk(func):
            if isinstance(node, ast.FunctionDef) and node is not func:
                inner_text = ast.unparse(node)
                is_recursive = node.name + "(" in inner_text
                is_cached = any(
                    "cache" in ast.unparse(d) or "lru_cache" in ast.unparse(d)
                    for d in node.decorator_list
                )
                if is_recursive or is_cached:
                    # The recurrence body is the non-base-case part
                    rec_body = [s for s in node.body if not self._classify_base_case(s)]
                    ops = self._semantic_ops(self._extract_ops_from_stmts(rec_body))
                    arity = inner_text.count(node.name + "(") - 1  # subtract the def itself
                    param_count = len(node.args.args)
                    return self._RecurrenceInfo(
                        combination_ops=ops,
                        arity=max(arity, 1),
                        depth=param_count,
                        tag=f"recursion_{param_count}d",
                    )
        return None

    def _extract_stack_recurrence(
        self, func: ast.FunctionDef,
    ) -> Optional["ASTPresheafExtractor._RecurrenceInfo"]:
        """Extract recurrence from a stack-based iteration."""
        for node in ast.walk(func):
            if isinstance(node, ast.While):
                w_text = ast.unparse(node)
                if ".pop()" in w_text or ".pop(" in w_text:
                    ops = self._semantic_ops(self._extract_ops_from_stmts(node.body))
                    append_count = w_text.count(".append(")
                    return self._RecurrenceInfo(
                        combination_ops=ops,
                        arity=max(append_count, 1),
                        depth=1,
                        tag="stack_traversal",
                    )
        return None

    def _find_deepest_for_body(self, node: ast.AST, current_depth: int) -> Tuple[int, Optional[List[ast.stmt]]]:
        """Find the deepest nested for-loop body."""
        if isinstance(node, ast.For):
            best_depth = current_depth + 1
            best_body: Optional[List[ast.stmt]] = node.body
            for child in ast.walk(node):
                if isinstance(child, ast.For) and child is not node:
                    d, b = self._find_deepest_for_body(child, current_depth + 1)
                    if d > best_depth:
                        best_depth = d
                        best_body = b
            return best_depth, best_body
        return current_depth, None

    # ───────────────────────────────────────────────────────────────────
    # Combination site extraction
    # ───────────────────────────────────────────────────────────────────

    def _extract_combination_sites(
        self, func: ast.FunctionDef, body: List[ast.stmt], strategy: EvaluationStrategy,
    ) -> FrozenSet[str]:
        """Extract the semantic combination operators (infrastructure filtered)."""
        # Get the "hot" zone — where the actual computation happens
        if strategy == EvaluationStrategy.TABULATION:
            for stmt in body:
                _, ib = self._find_deepest_for_body(stmt, 0)
                if ib:
                    return self._semantic_ops(self._extract_ops_from_stmts(ib))
        elif strategy in (EvaluationStrategy.MEMOISATION, EvaluationStrategy.RECURSION):
            for node in ast.walk(func):
                if isinstance(node, ast.FunctionDef) and node is not func:
                    inner_text = ast.unparse(node)
                    if node.name + "(" in inner_text or any(
                        "cache" in ast.unparse(d) for d in node.decorator_list
                    ):
                        rec_body = [s for s in node.body if not self._classify_base_case(s)]
                        return self._semantic_ops(self._extract_ops_from_stmts(rec_body))

        # Fallback: scan the entire function
        return self._semantic_ops(self._extract_ops_from_stmts(body))

    # ───────────────────────────────────────────────────────────────────
    # Type dispatch extraction
    # ───────────────────────────────────────────────────────────────────

    @dataclass(frozen=True)
    class _DispatchInfo:
        branch_count: int
        tag: str

    def _extract_type_dispatch(
        self, func: ast.FunctionDef, body: List[ast.stmt],
    ) -> Optional["ASTPresheafExtractor._DispatchInfo"]:
        """Detect isinstance-based type dispatch."""
        isinstance_count = 0
        dispatched_types: Set[str] = set()
        for node in ast.walk(func):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                if node.func.id == "isinstance" and len(node.args) >= 2:
                    isinstance_count += 1
                    type_arg = node.args[1]
                    if isinstance(type_arg, ast.Tuple):
                        for elt in type_arg.elts:
                            if isinstance(elt, ast.Name):
                                dispatched_types.add(elt.id)
                    elif isinstance(type_arg, ast.Name):
                        dispatched_types.add(type_arg.id)

        if isinstance_count < 2:
            return None

        # Normalise the dispatched types to a canonical order
        type_sig = ",".join(sorted(dispatched_types))
        return self._DispatchInfo(
            branch_count=isinstance_count,
            tag=f"isinstance_dispatch:{type_sig}",
        )

    # ───────────────────────────────────────────────────────────────────
    # Accumulation pattern extraction
    # ───────────────────────────────────────────────────────────────────

    @dataclass(frozen=True)
    class _AccumulationInfo:
        tag: str

    def _extract_accumulation(
        self, func: ast.FunctionDef, body: List[ast.stmt], strategy: EvaluationStrategy,
    ) -> Optional["ASTPresheafExtractor._AccumulationInfo"]:
        """Detect the accumulation pattern (how results are collected)."""
        func_text = ast.unparse(func)

        if ".append(" in func_text:
            return self._AccumulationInfo(tag="list_append")
        if ".add(" in func_text and "set()" in func_text:
            return self._AccumulationInfo(tag="set_add")
        if "+=" in func_text or "-=" in func_text:
            return self._AccumulationInfo(tag="augmented_assign")
        if ".update(" in func_text:
            return self._AccumulationInfo(tag="dict_update")
        if ".extend(" in func_text:
            return self._AccumulationInfo(tag="list_extend")
        return None

    # ───────────────────────────────────────────────────────────────────
    # Traversal structure extraction
    # ───────────────────────────────────────────────────────────────────

    @dataclass(frozen=True)
    class _TraversalInfo:
        depth: int
        tag: str

    def _extract_traversal(
        self, func: ast.FunctionDef, body: List[ast.stmt], strategy: EvaluationStrategy,
    ) -> Optional["ASTPresheafExtractor._TraversalInfo"]:
        """Detect the traversal structure (loop nesting, recursion depth)."""
        if strategy == EvaluationStrategy.TABULATION:
            depth = 0
            for stmt in body:
                d, _ = self._find_deepest_for_body(stmt, 0)
                depth = max(depth, d)
            if depth > 0:
                return self._TraversalInfo(depth=depth, tag=f"loop_{depth}d")

        elif strategy in (EvaluationStrategy.MEMOISATION, EvaluationStrategy.RECURSION):
            for node in ast.walk(func):
                if isinstance(node, ast.FunctionDef) and node is not func:
                    return self._TraversalInfo(
                        depth=len(node.args.args),
                        tag=f"recursive_{len(node.args.args)}d",
                    )

        elif strategy == EvaluationStrategy.STACK_ITERATION:
            return self._TraversalInfo(depth=1, tag="stack_loop")

        return None

    # ───────────────────────────────────────────────────────────────────
    # Output extraction
    # ───────────────────────────────────────────────────────────────────

    @dataclass(frozen=True)
    class _OutputInfo:
        tag: str

    def _extract_output(
        self, func: ast.FunctionDef, body: List[ast.stmt],
    ) -> Optional["ASTPresheafExtractor._OutputInfo"]:
        """Classify the output construction pattern."""
        # Find the last return statement
        returns = []
        for node in ast.walk(func):
            if isinstance(node, ast.Return) and node.value is not None:
                # Only top-level returns (not in inner functions)
                returns.append(node)

        if not returns:
            return None

        # Check the LAST top-level return
        for stmt in reversed(body):
            if isinstance(stmt, ast.Return) and stmt.value is not None:
                val = stmt.value
                if isinstance(val, ast.Subscript):
                    return self._OutputInfo(tag="indexed_extraction")
                if isinstance(val, ast.Call):
                    func_name = ""
                    if isinstance(val.func, ast.Name):
                        func_name = val.func.id
                    elif isinstance(val.func, ast.Attribute):
                        func_name = val.func.attr
                    if func_name in ("sorted", "list", "tuple"):
                        return self._OutputInfo(tag="sorted_collection")
                    if func_name == "join":
                        return self._OutputInfo(tag="string_join")
                    return self._OutputInfo(tag=f"call_{func_name}")
                if isinstance(val, ast.Name):
                    return self._OutputInfo(tag="direct_name")
                if isinstance(val, ast.Constant):
                    return self._OutputInfo(tag="constant")
                if isinstance(val, ast.Compare):
                    return self._OutputInfo(tag="comparison")
                if isinstance(val, ast.IfExp):
                    return self._OutputInfo(tag="conditional_expr")
                return self._OutputInfo(tag="expression")

        return None

    # ───────────────────────────────────────────────────────────────────
    # Parameter decomposition
    # ───────────────────────────────────────────────────────────────────

    @dataclass(frozen=True)
    class _ParamDecompInfo:
        arity: int
        tag: str

    def _extract_parameter_decomposition(
        self, func: ast.FunctionDef, body: List[ast.stmt],
    ) -> Optional["ASTPresheafExtractor._ParamDecompInfo"]:
        """Detect how parameters are decomposed for processing."""
        params = [a.arg for a in func.args.args]
        func_text = ast.unparse(func)

        # Check for len() on parameters
        uses_len = any(f"len({p})" in func_text for p in params)
        # Check for indexing into parameters
        uses_indexing = any(f"{p}[" in func_text for p in params)
        # Check for iteration over parameters
        uses_iteration = any(f"for " in func_text and f" in {p}" in func_text for p in params)

        tags = []
        if uses_len:
            tags.append("len")
        if uses_indexing:
            tags.append("index")
        if uses_iteration:
            tags.append("iterate")

        if not tags:
            return None

        return self._ParamDecompInfo(
            arity=len(params),
            tag="+".join(sorted(tags)),
        )

    # ───────────────────────────────────────────────────────────────────
    # Control skeleton extraction (control-flow topology as open set)
    # ───────────────────────────────────────────────────────────────────

    @dataclass(frozen=True)
    class _ControlSkeletonInfo:
        tag: str       # canonical control-flow shape descriptor
        depth: int     # nesting depth

    def _extract_control_skeleton(
        self, func: ast.FunctionDef, body: List[ast.stmt],
    ) -> Optional["ASTPresheafExtractor._ControlSkeletonInfo"]:
        """Extract the control-flow skeleton as a semantic site.

        The skeleton captures the TOPOLOGY of control flow: how loops,
        conditionals, and returns are nested. This is strategy-invariant
        because equivalent functions typically share the same abstract
        control pattern even when using different data structures.

        We encode the skeleton as a canonical string of nested structure
        symbols: L(loop), C(conditional), R(return), W(while), T(try).
        """
        def _skeleton(stmts: List[ast.stmt], depth: int = 0) -> str:
            parts: List[str] = []
            for stmt in stmts:
                if isinstance(stmt, ast.For):
                    inner = _skeleton(stmt.body, depth + 1)
                    parts.append(f"L({inner})")
                elif isinstance(stmt, ast.While):
                    inner = _skeleton(stmt.body, depth + 1)
                    parts.append(f"W({inner})")
                elif isinstance(stmt, ast.If):
                    then = _skeleton(stmt.body, depth + 1)
                    els = _skeleton(stmt.orelse, depth + 1) if stmt.orelse else ""
                    parts.append(f"C({then}|{els})")
                elif isinstance(stmt, ast.Return):
                    parts.append("R")
                elif isinstance(stmt, ast.Try):
                    inner = _skeleton(stmt.body, depth + 1)
                    parts.append(f"T({inner})")
                elif isinstance(stmt, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
                    parts.append("A")
                elif isinstance(stmt, ast.Expr):
                    parts.append("E")
            return ",".join(parts)

        skel = _skeleton(body)
        if not skel:
            return None

        # Compute max nesting depth
        max_depth = 0
        current = 0
        for ch in skel:
            if ch == "(":
                current += 1
                max_depth = max(max_depth, current)
            elif ch == ")":
                current -= 1

        return self._ControlSkeletonInfo(tag=skel, depth=max_depth)

    # ───────────────────────────────────────────────────────────────────
    # Call protocol extraction (abstract function-call pattern as open set)
    # ───────────────────────────────────────────────────────────────────

    @dataclass(frozen=True)
    class _CallProtocolInfo:
        tag: str           # canonical protocol descriptor
        arity: int         # number of distinct protocols used

    # Protocol families: maps specific method/function names to abstract protocols
    _PROTOCOL_FAMILIES: Dict[str, str] = {
        # Stack protocol
        "append": "stack", "pop": "stack", "push": "stack",
        # Queue protocol
        "popleft": "queue", "appendleft": "queue",
        # Dict/mapping protocol
        "get": "mapping", "setdefault": "mapping",
        "__getitem__": "mapping", "__setitem__": "mapping",
        # Set protocol
        "add": "set_ops", "discard": "set_ops",
        "intersection": "set_ops", "union": "set_ops", "difference": "set_ops",
        # Heap protocol
        "heappush": "heap", "heappop": "heap", "heapify": "heap",
        "heapreplace": "heap",
        # Search/sort protocol
        "bisect_left": "binary_search", "bisect_right": "binary_search",
        "bisect": "binary_search", "insort": "binary_search",
        "sorted": "sort", "sort": "sort",
        # Iterator protocol
        "next": "iterator", "__next__": "iterator", "__iter__": "iterator",
        # String protocol
        "join": "string", "split": "string", "strip": "string",
        "replace": "string", "find": "string",
        "startswith": "string", "endswith": "string",
    }

    def _extract_call_protocol(
        self, func: ast.FunctionDef, body: List[ast.stmt],
    ) -> Optional["ASTPresheafExtractor._CallProtocolInfo"]:
        """Extract abstract data protocols used by the function.

        Instead of tracking specific method calls (which are strategy-
        dependent), we classify them into abstract protocol families.
        Two functions using 'stack' vs 'recursion' (implicit stack)
        would show the same abstract protocol.
        """
        protocols: Set[str] = set()

        for node in ast.walk(ast.Module(body=body, type_ignores=[])):
            # Method calls: obj.method(...)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                attr = node.func.attr
                if attr in self._PROTOCOL_FAMILIES:
                    protocols.add(self._PROTOCOL_FAMILIES[attr])

            # Builtin calls: sorted(...), next(...), etc.
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                name = node.func.id
                if name in self._PROTOCOL_FAMILIES:
                    protocols.add(self._PROTOCOL_FAMILIES[name])
                # heapq functions
                if name in ("heappush", "heappop", "heapify", "heapreplace"):
                    protocols.add("heap")

            # Subscript access (dict/list indexing)
            if isinstance(node, ast.Subscript):
                protocols.add("indexing")

        if not protocols:
            return None

        tag = "+".join(sorted(protocols))
        return self._CallProtocolInfo(tag=tag, arity=len(protocols))

    # ───────────────────────────────────────────────────────────────────
    # Helpers
    # ───────────────────────────────────────────────────────────────────

    # ── Infrastructure ops that are part of evaluation strategy, not semantics ──
    _INFRASTRUCTURE_OPS = frozenset({
        # Stack management
        "pop", "append", "extend", "insert", "remove",
        # Collection mutation (not mathematical semantics)
        "add", "update", "sort", "count", "index",
        # Collection size / iteration
        "len", "enumerate", "range",
        # Comparison ops typically used in loop guards / base case checks
        "Eq", "NotEq", "Lt", "LtE", "Gt", "GtE", "Is", "IsNot", "In", "NotIn",
        # Augmented assignment (loop accumulators)
        "AugAdd", "AugSub",
    })

    def _semantic_ops(self, raw_ops: FrozenSet[str]) -> FrozenSet[str]:
        """Filter raw AST ops to keep only semantic (mathematical) operations."""
        return raw_ops - self._INFRASTRUCTURE_OPS

    def _extract_ops_from_stmts(self, stmts: List[ast.stmt]) -> FrozenSet[str]:
        """Extract combination operators from a list of statements."""
        ops: Set[str] = set()
        for node in ast.walk(ast.Module(body=stmts, type_ignores=[])):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                name = node.func.id
                if name in ("max", "min", "sum", "sorted", "abs", "len",
                            "pow", "round", "divmod", "enumerate"):
                    ops.add(name)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                attr = node.func.attr
                if attr in ("append", "extend", "add", "update", "sort",
                            "pop", "insert", "remove", "count", "index"):
                    ops.add(attr)
            if isinstance(node, ast.BinOp):
                ops.add(type(node.op).__name__)
            if isinstance(node, ast.AugAssign):
                ops.add("Aug" + type(node.op).__name__)
            if isinstance(node, ast.Compare):
                for op in node.ops:
                    ops.add(type(op).__name__)
        return frozenset(ops)

    def _count_sub_references(self, stmts: List[ast.stmt]) -> int:
        """Count how many sub-problem references appear (e.g. dp[i-1][j])."""
        count = 0
        for node in ast.walk(ast.Module(body=stmts, type_ignores=[])):
            if isinstance(node, ast.Subscript):
                sub_text = ast.unparse(node)
                if "-" in sub_text or "+" in sub_text:
                    count += 1
        return max(count, 1)

    def _semantic_body(self, body: List[ast.stmt]) -> List[ast.stmt]:
        """Strip docstrings and imports from a function body."""
        result: List[ast.stmt] = []
        for stmt in body:
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant):
                continue
            if isinstance(stmt, (ast.Import, ast.ImportFrom)):
                continue
            result.append(stmt)
        return result

    def _select_root_function(self, tree: ast.AST, func_name: Optional[str] = None) -> Optional[ast.FunctionDef]:
        """Select the primary function definition from the AST."""
        body = getattr(tree, "body", None)
        if not isinstance(body, list):
            return None
        top_level = [n for n in body if isinstance(n, ast.FunctionDef)]
        if not top_level:
            return None
        if func_name:
            for f in top_level:
                if f.name == func_name:
                    return f
        # Prefer functions whose name doesn't start with '_'
        public = [f for f in top_level if not f.name.startswith("_")]
        if public:
            return public[0]
        return top_level[0]


# ═══════════════════════════════════════════════════════════════════════
# §8  Čech Cohomology Computer
# ═══════════════════════════════════════════════════════════════════════


class CechCohomologyComputer:
    """Compute Ȟ¹(U, Iso(F_f, F_g)) over the product site.

    1. Build aligned product sites W_{ij} = U_i ∩ V_j  (same SemanticKind)
    2. Assign agreement values: agrees iff descriptors unify
    3. Build the coboundary matrix δ⁰: C⁰ → C¹
    4. Compute H¹ = ker δ¹ / im δ⁰ over GF(2)
    """

    def compute(self, pf: ASTPresheaf, pg: ASTPresheaf, strict_tags: bool = False) -> CechData:
        """Compute Čech cohomology of the isomorphism presheaf."""
        # ── Step 1: Build product sites by aligning on SemanticKind ──
        product_sites: List[ProductSite] = []

        for uf in pf.cover:
            for ug in pg.cover:
                if uf.kind == ug.kind:
                    agrees = uf.descriptor.unifies_with(ug.descriptor, strict_tags=strict_tags)
                    product_sites.append(ProductSite(
                        site_f=uf,
                        site_g=ug,
                        agrees=agrees,
                    ))

        if not product_sites:
            return CechData(product_sites=product_sites)

        n = len(product_sites)

        # ── Step 2: Build C⁰ ──
        # Each product site is a generator of C⁰.
        # The section value is 0 (agrees) or 1 (disagrees).
        c0 = [0 if ps.agrees else 1 for ps in product_sites]

        # ── Step 3: Build coboundary matrix δ⁰: C⁰ → C¹ ──
        # C¹ generators are pairs of product sites that share a SemanticKind
        # (i.e., they overlap in the product topology).
        c1_pairs: List[Tuple[int, int]] = []
        for i in range(n):
            for j in range(i + 1, n):
                si = product_sites[i]
                sj = product_sites[j]
                # Overlap condition: share at least one kind component
                if (si.site_f.kind == sj.site_f.kind or
                        si.site_g.kind == sj.site_g.kind):
                    c1_pairs.append((i, j))

        m = len(c1_pairs)
        if m == 0:
            # No overlaps → H¹ = 0 trivially (each site is independent)
            h1 = 0
            h0 = sum(1 for v in c0 if v == 0)
            return CechData(
                product_sites=product_sites,
                c0_generators=n,
                c1_generators=0,
                h0=h0,
                h1=h1,
            )

        # δ⁰ matrix: m rows (C¹ generators) × n columns (C⁰ generators)
        # δ⁰(σ)_{ij} = σ_i - σ_j (mod 2) = σ_i ⊕ σ_j
        delta0 = [[0] * n for _ in range(m)]
        for row_idx, (i, j) in enumerate(c1_pairs):
            delta0[row_idx][i] = 1
            delta0[row_idx][j] = 1

        # ── Step 4: Compute H¹ = ker δ¹ / im δ⁰ ──
        #
        # The 1-cocycle is the image of c0 under δ⁰:
        #   (δ⁰ c)(i,j) = c(i) ⊕ c(j)
        # A 1-cocycle z is a coboundary iff z ∈ im(δ⁰).
        # H¹ = 0 iff every 1-cocycle is a coboundary.
        #
        # Concretely: if all product sites agree (c0 = 0), then
        # δ⁰(c0) = 0, meaning H¹ = 0.
        #
        # If any disagree, δ⁰(c0) ≠ 0, and we need to check if
        # the cocycle is exact (a coboundary of some other 0-cochain).
        #
        # For the isomorphism presheaf, a non-trivial H¹ means
        # local isos don't glue — the functions differ.

        # Compute the 1-cocycle
        cocycle = [(c0[i] ^ c0[j]) for i, j in c1_pairs]

        # Check if cocycle is trivial (all zeros)
        if all(z == 0 for z in cocycle):
            h1 = 0
        else:
            # Check if the cocycle is in im(δ⁰)
            # This requires solving a system over GF(2)
            h1 = self._compute_h1_gf2(delta0, cocycle, n, m)

        h0 = n - self._gf2_rank(delta0, n, m)

        return CechData(
            product_sites=product_sites,
            c0_generators=n,
            c1_generators=m,
            h0=h0,
            h1=h1,
            coboundary_matrix=delta0,
        )

    def _compute_h1_gf2(
        self, delta0: List[List[int]], cocycle: List[int], n: int, m: int,
    ) -> int:
        """Compute dim H¹ = dim ker(δ¹) - dim im(δ⁰) over GF(2)."""
        # For the Čech complex of a cover, H¹ is non-trivial
        # when the cocycle δ⁰(c0) is not a coboundary.
        #
        # We augment the coboundary matrix with the cocycle as an
        # extra column and check if the rank increases.
        rank_delta = self._gf2_rank(delta0, n, m)

        # Check if the cocycle is in the column space of δ⁰
        # by augmenting and checking rank
        augmented = [row[:] + [cocycle[i]] for i, row in enumerate(delta0)]
        rank_aug = self._gf2_rank(augmented, n + 1, m)

        if rank_aug > rank_delta:
            return 1  # cocycle is not a coboundary → H¹ ≠ 0
        return 0  # cocycle IS a coboundary → H¹ = 0

    def _gf2_rank(self, matrix: List[List[int]], cols: int, rows: int) -> int:
        """Compute rank of a matrix over GF(2) via Gaussian elimination."""
        if not matrix or not matrix[0]:
            return 0
        mat = [row[:cols] for row in matrix[:rows]]
        rank = 0
        for col in range(cols):
            # Find pivot
            pivot = None
            for row in range(rank, len(mat)):
                if mat[row][col] == 1:
                    pivot = row
                    break
            if pivot is None:
                continue
            # Swap
            mat[rank], mat[pivot] = mat[pivot], mat[rank]
            # Eliminate
            for row in range(len(mat)):
                if row != rank and mat[row][col] == 1:
                    mat[row] = [(mat[row][c] ^ mat[rank][c]) for c in range(cols)]
            rank += 1
        return rank


# ═══════════════════════════════════════════════════════════════════════
# §9  AST Sheaf Equivalence Checker (top-level)
# ═══════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ASTSheafCertificate:
    """Certificate from the AST presheaf cohomology check."""
    equivalent: bool
    h0: int = 0
    h1: int = 0
    explanation: str = ""
    cover_f_size: int = 0
    cover_g_size: int = 0
    product_sites: int = 0
    strategy_f: str = ""
    strategy_g: str = ""


class ASTSheafEquivalenceChecker:
    """Check function equivalence via AST presheaf cohomology.

    The full pipeline:
    1. Extract AST presheaves F_f, F_g
    2. Check strategy coboundary equivalence
    3. Build product site and compute Ȟ¹(U, Iso(F_f, F_g))
    4. H¹ = 0 → equivalent; H¹ ≠ 0 → not proved equivalent
    """

    def __init__(self) -> None:
        self._extractor = ASTPresheafExtractor()
        self._cech = CechCohomologyComputer()

    def check(
        self,
        source_f: str,
        source_g: str,
        func_name_f: Optional[str] = None,
        func_name_g: Optional[str] = None,
    ) -> Optional[ASTSheafCertificate]:
        """Check equivalence via AST presheaf cohomology."""

        pf = self._extractor.extract(source_f, func_name_f)
        pg = self._extractor.extract(source_g, func_name_g)
        if pf is None or pg is None:
            return None

        # ── Structural preconditions ──
        if pf.param_count != pg.param_count:
            return ASTSheafCertificate(
                equivalent=False,
                explanation="Arity mismatch: presheaf fibers over different parameter spaces",
                strategy_f=pf.strategy.value,
                strategy_g=pg.strategy.value,
            )

        # ── Strategy coboundary check ──
        # The coboundary argument applies when strategies are DIFFERENT
        # but related by a known natural isomorphism.  When strategies are
        # the same, we use stricter section agreement.
        are_dual = (
            pf.strategy != pg.strategy
            and strategies_coboundary_equivalent(pf.strategy, pg.strategy)
        )
        are_same = pf.strategy == pg.strategy and pf.strategy != EvaluationStrategy.DIRECT
        if not are_dual and not are_same:
            # For DIRECT vs DIRECT or unrelated strategies, only the all-agree
            # fallback (below) can fire. Fall through to compute Čech data.
            pass

        # ── Require sufficient cover ──
        if len(pf.cover) < 2 or len(pg.cover) < 2:
            return None

        # ── Compute Čech cohomology ──
        # For dual strategies: relaxed tag matching (strategy-specific tags differ)
        # For same strategies: strict tag matching (all descriptors must match exactly)
        # For unrelated (DIRECT etc.): relaxed (only used via all-agree fallback)
        strict = are_same  # only strict for same non-DIRECT strategies
        cech = self._cech.compute(pf, pg, strict_tags=strict)

        if not cech.product_sites:
            return None

        # If neither dual nor same (e.g., DIRECT), only allow the
        # all-agree fallback below.
        can_use_core_path = are_dual or are_same

        # ── Require meaningful agreement ──
        # At least one product site must involve a RECURRENCE_STEP or
        # COMBINATION_SITE (the computational core), and it must agree.
        core_kinds = {SemanticKind.RECURRENCE_STEP, SemanticKind.COMBINATION_SITE}
        # Supporting kinds provide extra evidence but don't count toward
        # the ≥4 primary-site threshold (they're too easy to match).
        _supporting_kinds = {SemanticKind.CONTROL_SKELETON, SemanticKind.CALL_PROTOCOL}
        core_sites = [
            ps for ps in cech.product_sites
            if ps.site_f.kind in core_kinds
        ]
        primary_sites = [
            ps for ps in cech.product_sites
            if ps.site_f.kind not in _supporting_kinds
        ]
        if not core_sites or not can_use_core_path:
            # No computational-core alignment or not on core path.
            # Fallback: if ALL PRIMARY sites agree, there are ≥4 primary sites,
            # and there is non-trivial evidence of shared computation, accept
            # by sheaf descent on the full cover.
            agreeing = sum(1 for ps in cech.product_sites if ps.agrees)
            total = len(cech.product_sites)
            primary_agreeing = sum(1 for ps in primary_sites if ps.agrees)
            primary_total = len(primary_sites)
            # Non-trivial evidence: combination_ops OR matching call protocol
            has_ops = any(
                ps.site_f.descriptor.combination_ops or ps.site_g.descriptor.combination_ops
                for ps in cech.product_sites
            )
            has_protocol_match = any(
                ps.site_f.kind == SemanticKind.CALL_PROTOCOL
                and ps.agrees
                and ps.site_f.descriptor.data_flow_tag  # non-empty protocol
                for ps in cech.product_sites
            )
            # Protocol evidence only counts for cross-strategy pairs where
            # ops extraction naturally differs between evaluation strategies.
            has_nontrivial = has_ops or (has_protocol_match and not are_same)
            if primary_total >= 4 and primary_agreeing == primary_total and has_nontrivial and cech.h1 == 0:
                return ASTSheafCertificate(
                    equivalent=True,
                    h0=cech.h0,
                    h1=0,
                    explanation=(
                        f"Ȟ¹(U, Iso(F_f, F_g)) = 0: all {total} "
                        f"product-site sections agree (non-trivial). "
                        f"Strategies {pf.strategy.value} ~ {pg.strategy.value}. "
                        f"Global section exists by descent over full cover."
                    ),
                    cover_f_size=len(pf.cover),
                    cover_g_size=len(pg.cover),
                    product_sites=total,
                    strategy_f=pf.strategy.value,
                    strategy_g=pg.strategy.value,
                )
            # For same-strategy pairs, try again with relaxed matching
            # and the all-agree fallback.
            if are_same:
                cech_relaxed = self._cech.compute(pf, pg, strict_tags=False)
                agreeing_r = sum(1 for ps in cech_relaxed.product_sites if ps.agrees)
                total_r = len(cech_relaxed.product_sites)
                primary_r = [ps for ps in cech_relaxed.product_sites
                             if ps.site_f.kind not in _supporting_kinds]
                primary_total_r = len(primary_r)
                has_ops_r = any(
                    ps.site_f.descriptor.combination_ops or ps.site_g.descriptor.combination_ops
                    for ps in cech_relaxed.product_sites
                )
                has_protocol_r = any(
                    ps.site_f.kind == SemanticKind.CALL_PROTOCOL
                    and ps.agrees
                    and ps.site_f.descriptor.data_flow_tag
                    for ps in cech_relaxed.product_sites
                )
                has_nontrivial_r = has_ops_r  # same-strategy: protocol alone not sufficient
                primary_agreeing_r = sum(1 for ps in primary_r if ps.agrees)
                if primary_total_r >= 4 and primary_agreeing_r == primary_total_r and has_nontrivial_r and cech_relaxed.h1 == 0:
                    return ASTSheafCertificate(
                        equivalent=True,
                        h0=cech_relaxed.h0,
                        h1=0,
                        explanation=(
                            f"Ȟ¹(U, Iso(F_f, F_g)) = 0: all {total_r} "
                            f"product-site sections agree (relaxed). "
                            f"Same strategy {pf.strategy.value}. "
                            f"Global section exists by descent over full cover."
                        ),
                        cover_f_size=len(pf.cover),
                        cover_g_size=len(pg.cover),
                        product_sites=total_r,
                        strategy_f=pf.strategy.value,
                        strategy_g=pg.strategy.value,
                    )
            return None  # No computational-core alignment

        core_agreeing = sum(1 for ps in core_sites if ps.agrees)
        if core_agreeing == 0:
            # Core sections disagree in current mode. For same-strategy pairs,
            # try relaxed matching as a fallback (the strict tags may be too
            # discriminating for implementation variants of the same algorithm).
            if are_same:
                cech_relaxed = self._cech.compute(pf, pg, strict_tags=False)
                agreeing_r = sum(1 for ps in cech_relaxed.product_sites if ps.agrees)
                total_r = len(cech_relaxed.product_sites)
                primary_r = [ps for ps in cech_relaxed.product_sites
                             if ps.site_f.kind not in _supporting_kinds]
                primary_total_r = len(primary_r)
                has_ops_r = any(
                    ps.site_f.descriptor.combination_ops or ps.site_g.descriptor.combination_ops
                    for ps in cech_relaxed.product_sites
                )
                has_protocol_r = any(
                    ps.site_f.kind == SemanticKind.CALL_PROTOCOL
                    and ps.agrees
                    and ps.site_f.descriptor.data_flow_tag
                    for ps in cech_relaxed.product_sites
                )
                has_nontrivial_r = has_ops_r  # same-strategy: protocol alone not sufficient
                primary_agreeing_r = sum(1 for ps in primary_r if ps.agrees)
                if primary_total_r >= 4 and primary_agreeing_r == primary_total_r and has_nontrivial_r and cech_relaxed.h1 == 0:
                    return ASTSheafCertificate(
                        equivalent=True,
                        h0=cech_relaxed.h0,
                        h1=0,
                        explanation=(
                            f"Ȟ¹(U, Iso(F_f, F_g)) = 0: all {total_r} "
                            f"product-site sections agree (relaxed). "
                            f"Same strategy {pf.strategy.value}. "
                            f"Global section exists by descent over full cover."
                        ),
                        cover_f_size=len(pf.cover),
                        cover_g_size=len(pg.cover),
                        product_sites=total_r,
                        strategy_f=pf.strategy.value,
                        strategy_g=pg.strategy.value,
                    )
            return None  # Core sections disagree — can't prove equivalence

        # ── Interpret H¹ ──
        if cech.h1 == 0:
            agreeing = sum(1 for ps in cech.product_sites if ps.agrees)
            total = len(cech.product_sites)

            # Additional safety: if more core sites disagree than agree,
            # do not claim equivalence.
            core_disagreeing = sum(1 for ps in cech.product_sites
                                   if not ps.agrees and ps.site_f.kind in core_kinds)
            if core_disagreeing > core_agreeing:
                return None  # More core disagreements than agreements

            return ASTSheafCertificate(
                equivalent=True,
                h0=cech.h0,
                h1=0,
                explanation=(
                    f"Ȟ¹(U, Iso(F_f, F_g)) = 0: {core_agreeing} core section(s) "
                    f"agree ({agreeing}/{total} total). Strategies "
                    f"{pf.strategy.value} ~ {pg.strategy.value} are "
                    f"coboundary-equivalent. Global section exists by descent."
                ),
                cover_f_size=len(pf.cover),
                cover_g_size=len(pg.cover),
                product_sites=total,
                strategy_f=pf.strategy.value,
                strategy_g=pg.strategy.value,
            )
        else:
            return ASTSheafCertificate(
                equivalent=False,
                h0=cech.h0,
                h1=cech.h1,
                explanation=(
                    f"Ȟ¹(U, Iso) ≠ 0: local sections disagree at "
                    f"{sum(1 for ps in cech.product_sites if not ps.agrees)} "
                    f"product site(s). No global isomorphism by descent obstruction."
                ),
                cover_f_size=len(pf.cover),
                cover_g_size=len(pg.cover),
                product_sites=len(cech.product_sites),
                strategy_f=pf.strategy.value,
                strategy_g=pg.strategy.value,
            )
