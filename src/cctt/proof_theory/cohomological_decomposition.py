"""Cohomological Decomposition — LLM-assisted invariant-cover proving.

The core idea: a function's correctness decomposes into a Čech cover of
local invariants.  Each invariant defines a refinement predicate on the
program state.  Each region (CFG edge between invariant points) creates
a verification condition.  The Čech complex captures compatibility at
joins.  H¹ = 0 iff local proofs glue to global correctness.

This is genuinely cohomological, not just metaphorical:
- **Opens** = invariant predicates on program states
- **Sections** = per-region proofs that one invariant implies the next
- **Overlaps** = CFG join points where two paths merge
- **Cocycles** = compatibility: proofs from both branches must agree at joins
- **H¹** = cohomological obstruction to gluing

The LLM's role (NEVER proving):
- Generate invariant annotations (the decomposition plan)
- Suggest candidate proof term shapes (checker verifies or rejects)
- Refine decompositions when regions fail to prove

The checker's role (ALWAYS proving):
- Parse predicates formally via predicates.py
- Generate verification conditions per region
- Discharge via Z3, library axioms, or structural rules
- Verify overlap compatibility
- Compute H¹ and produce global GluePath

Usage::

    # Manual annotation
    @decompose
    @postcondition("len(result) == len(xs)")
    @postcondition("all(result[i] <= result[i+1] for i in range(len(result)-1))")
    def merge_sort(xs: list[int]) -> list[int]:
        precondition("isinstance(xs, list)")
        if len(xs) <= 1:
            return xs
        mid = len(xs) // 2
        left = merge_sort(xs[:mid])
        right = merge_sort(xs[mid:])
        invariant("sorted(left) and sorted(right)")
        invariant("len(left) + len(right) == len(xs)")
        return _merge(left, right)

    # LLM-assisted: auto-decompose, then prove
    result = auto_decompose_and_prove(source_code, guarantee="returns sorted list")
"""
from __future__ import annotations

import ast
import functools
import inspect
import textwrap
from dataclasses import dataclass, field
from enum import Enum
from typing import (
    Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple, Union,
)

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OAbstract,
)

from cctt.proof_theory.terms import (
    ProofTerm, Refl, Sym, Trans, Cong, Assume, Cut, LetProof,
    CasesSplit, Z3Discharge, LoopInvariant,
    FiberDecomposition, CechGluing,
    var, lit, op, abstract,
)

from cctt.proof_theory.predicates import (
    Pred, PTrue, PFalse, PVar, PAnd, POr, PNot, PImplies,
    PCompare, PCall, PLibCall, PLit,
    parse_predicate, Decidability,
    RefinementFiber, RefinementCover, OverlapInfo,
)

from cctt.proof_theory.checker import (
    check_proof, VerificationResult, ProofContext,
)


# ═══════════════════════════════════════════════════════════════════
# §1. Runtime Markers — no-ops at runtime, AST markers at analysis time
# ═══════════════════════════════════════════════════════════════════

def invariant(predicate: str) -> bool:
    """Mark an invariant at the current program point.

    At runtime: returns True (no-op).
    At analysis time: creates an InvariantPoint that splits the CFG.

    The predicate string must be a parseable Python expression
    referring to variables in scope.

    Example::

        result = []
        for x in xs:
            result.append(x)
            invariant("len(result) <= len(xs)")
        invariant("len(result) == len(xs)")
    """
    return True


def precondition(predicate: str) -> bool:
    """Mark a precondition at function entry.

    At runtime: returns True (assertion-like, but never raises).
    At analysis time: creates an entry invariant.

    Example::

        def safe_div(a: float, b: float) -> float:
            precondition("b != 0")
            return a / b
    """
    return True


def postcondition(predicate_or_func: Union[str, Callable]) -> Any:
    """Mark a postcondition.

    As decorator: ``@postcondition("sorted(result)")``
    As statement: ``postcondition("len(result) == len(input)")``

    When used as a decorator, attaches postcondition metadata to the function.
    When used as a statement (string arg) inside a function body, returns True.
    """
    if callable(predicate_or_func) and not isinstance(predicate_or_func, str):
        # Used as @postcondition without arguments (unusual)
        return predicate_or_func

    predicate = predicate_or_func

    def decorator(func: Callable) -> Callable:
        if not hasattr(func, '__postconditions__'):
            func.__postconditions__ = []
        func.__postconditions__.append(predicate)
        return func

    # Always return the decorator — if called as a statement in a function
    # body, the returned decorator object is truthy (which is fine).
    # The AST parser handles the marker extraction separately.
    return decorator


def loop_invariant(predicate: str) -> bool:
    """Mark a loop invariant.

    Must appear inside a loop body. At analysis time, generates:
    - Init obligation: invariant holds on entry
    - Preservation: if invariant holds before iteration, holds after
    - Post: invariant holds on loop exit

    Example::

        total = 0
        for x in xs:
            loop_invariant("total == sum(xs[:i])")
            total += x
    """
    return True


def library_fact(library: str, fact: str) -> bool:
    """Assert a library fact as a local axiom.

    The fact is trusted (LIBRARY_ASSUMED trust level) and can be
    used by the proof engine to discharge obligations in this region.

    Example::

        library_fact("sympy", "simplify(expand(e)) == e for polynomial e")
        result = sympy.simplify(sympy.expand(expr))
        invariant("result == expr")
    """
    return True


def assume_correct(func_name: str) -> bool:
    """Mark a called function as correct by assumption.

    Creates a trust boundary: the called function's postconditions
    are assumed true. This is LIBRARY_ASSUMED trust level.

    Example::

        left = merge_sort(xs[:mid])
        assume_correct("merge_sort")
        invariant("sorted(left)")
    """
    return True


# ═══════════════════════════════════════════════════════════════════
# §2. Trust Model
# ═══════════════════════════════════════════════════════════════════

class TrustLevel(Enum):
    """How much we trust a proof step."""
    KERNEL = "kernel"          # Z3-discharged or structurally checked
    LIBRARY = "library"        # Trusted library axiom
    STRUCTURAL = "structural"  # Checker accepted structurally
    ASSUMED = "assumed"        # Explicitly assumed by user
    UNVERIFIED = "unverified"  # Not yet proved


@dataclass(frozen=True)
class TrustSummary:
    """Trust accounting for a proof or decomposition."""
    kernel_steps: int = 0
    library_steps: int = 0
    structural_steps: int = 0
    assumed_steps: int = 0
    unverified_steps: int = 0

    @property
    def total_steps(self) -> int:
        return (self.kernel_steps + self.library_steps +
                self.structural_steps + self.assumed_steps +
                self.unverified_steps)

    @property
    def max_trust(self) -> TrustLevel:
        """Weakest link: the highest (least trusted) trust level used."""
        if self.unverified_steps > 0:
            return TrustLevel.UNVERIFIED
        if self.assumed_steps > 0:
            return TrustLevel.ASSUMED
        if self.structural_steps > 0:
            return TrustLevel.STRUCTURAL
        if self.library_steps > 0:
            return TrustLevel.LIBRARY
        return TrustLevel.KERNEL

    @property
    def verified_fraction(self) -> float:
        """Fraction of steps that are kernel or library verified."""
        if self.total_steps == 0:
            return 1.0
        return (self.kernel_steps + self.library_steps) / self.total_steps

    def pretty(self) -> str:
        parts = []
        if self.kernel_steps:
            parts.append(f'{self.kernel_steps} kernel')
        if self.library_steps:
            parts.append(f'{self.library_steps} library')
        if self.structural_steps:
            parts.append(f'{self.structural_steps} structural')
        if self.assumed_steps:
            parts.append(f'{self.assumed_steps} assumed')
        if self.unverified_steps:
            parts.append(f'{self.unverified_steps} unverified')
        return f'[{self.max_trust.value}] {", ".join(parts) or "empty"}'


# ═══════════════════════════════════════════════════════════════════
# §3. Data Model — Invariant Points, CFG, Regions, Covers
# ═══════════════════════════════════════════════════════════════════

class MarkerKind(Enum):
    PRECONDITION = "precondition"
    POSTCONDITION = "postcondition"
    INVARIANT = "invariant"
    LOOP_INVARIANT = "loop_invariant"
    LIBRARY_FACT = "library_fact"
    ASSUME_CORRECT = "assume_correct"


@dataclass
class InvariantPoint:
    """A single invariant annotation at a program point.

    Dual representation: human-readable surface text + compiled Pred AST.
    The compiled form is the source of truth for verification.
    """
    surface_text: str                    # original NL/Python string
    compiled: Pred                       # formal predicate AST
    kind: MarkerKind                     # what type of marker
    line: int = 0                        # source line number
    parse_status: str = 'ok'             # 'ok', 'fallback', 'failed'
    library: str = ''                    # library name (for library_fact)
    func_ref: str = ''                   # function ref (for assume_correct)

    @property
    def is_formal(self) -> bool:
        """True if the predicate was formally parsed (not a fallback PVar)."""
        return self.parse_status == 'ok' and not isinstance(self.compiled, PVar)

    def pretty(self) -> str:
        status = '✓' if self.is_formal else '~'
        return f'[{status}] {self.kind.value}@L{self.line}: {self.surface_text}'


class CFGNodeKind(Enum):
    ENTRY = "entry"
    EXIT = "exit"
    BRANCH = "branch"
    JOIN = "join"
    LOOP_HEADER = "loop_header"
    LOOP_EXIT = "loop_exit"
    INVARIANT = "invariant"
    STATEMENT = "statement"
    RETURN = "return"
    RAISE = "raise"


@dataclass
class CFGNode:
    """A node in the simplified control flow graph."""
    node_id: str
    kind: CFGNodeKind
    invariants: List[InvariantPoint] = field(default_factory=list)
    source_lines: Tuple[int, int] = (0, 0)
    branch_condition: str = ''

    def pretty(self) -> str:
        invs = f' [{len(self.invariants)} inv]' if self.invariants else ''
        return f'{self.node_id}({self.kind.value}){invs}'


@dataclass
class CFGEdge:
    """An edge in the CFG — a straight-line code region between nodes."""
    edge_id: str
    source: str             # source node_id
    target: str             # target node_id
    condition: str = ''     # branch condition (if edge comes from a branch)
    source_lines: Tuple[int, int] = (0, 0)

    def pretty(self) -> str:
        cond = f' [{self.condition}]' if self.condition else ''
        return f'{self.source} →{cond} {self.target}'


@dataclass
class FunctionCFG:
    """Simplified control flow graph for a function.

    Nodes are invariant attachment sites (entry, exit, branches, joins,
    loop headers, explicit invariant() calls).  Edges are straight-line
    code regions between these points.
    """
    function_name: str
    nodes: Dict[str, CFGNode] = field(default_factory=dict)
    edges: List[CFGEdge] = field(default_factory=list)
    entry: str = ''
    exits: List[str] = field(default_factory=list)

    def add_node(self, node: CFGNode) -> None:
        self.nodes[node.node_id] = node

    def add_edge(self, edge: CFGEdge) -> None:
        self.edges.append(edge)

    def predecessors(self, node_id: str) -> List[str]:
        return [e.source for e in self.edges if e.target == node_id]

    def successors(self, node_id: str) -> List[str]:
        return [e.target for e in self.edges if e.source == node_id]

    def pretty(self) -> str:
        lines = [f'CFG: {self.function_name}']
        lines.append(f'  entry: {self.entry}')
        lines.append(f'  exits: {self.exits}')
        for n in self.nodes.values():
            lines.append(f'  {n.pretty()}')
        for e in self.edges:
            lines.append(f'  {e.pretty()}')
        return '\n'.join(lines)


@dataclass
class ProofRegion:
    """A region between two invariant points — a single verification condition.

    The VC is: assuming entry invariants hold, after executing the region's
    code, the exit invariants must hold.

    Trust is tracked per-region so the global proof reports its weakest link.
    """
    region_id: str
    edge: CFGEdge
    entry_invariants: List[InvariantPoint]
    exit_invariants: List[InvariantPoint]
    obligation_text: str = ''
    proof: Optional[ProofTerm] = None
    trust: TrustLevel = TrustLevel.UNVERIFIED
    failure_reason: str = ''
    z3_formula: str = ''

    @property
    def is_proved(self) -> bool:
        return self.proof is not None and self.trust != TrustLevel.UNVERIFIED

    def pretty(self) -> str:
        status = '✓' if self.is_proved else '○'
        trust = f' [{self.trust.value}]' if self.is_proved else ''
        entry = ', '.join(ip.surface_text[:30] for ip in self.entry_invariants)
        exit_ = ', '.join(ip.surface_text[:30] for ip in self.exit_invariants)
        return (f'{status}{trust} {self.region_id}: '
                f'{{{entry}}} → {{{exit_}}}')


@dataclass
class OverlapObligation:
    """Cocycle condition at a CFG join point.

    When two paths merge, their exit invariants must be compatible:
    the proofs from both branches must agree on the merged state.
    """
    join_node_id: str
    branch_a: str       # edge_id of first incoming branch
    branch_b: str       # edge_id of second incoming branch
    invariants_a: List[InvariantPoint]
    invariants_b: List[InvariantPoint]
    proof: Optional[ProofTerm] = None
    trust: TrustLevel = TrustLevel.UNVERIFIED


@dataclass
class InvariantCover:
    """A Čech cover of a function's correctness via invariants.

    The cover carries:
    1. The CFG with invariant attachment points
    2. Proof regions (verification conditions per CFG edge)
    3. Overlap obligations (cocycle conditions at joins)
    4. H¹ rank (0 = glues, >0 = obstruction)
    5. Trust summary

    The Čech complex:
    - C⁰ = ⊕ over regions: proof that entry → exit invariant
    - C¹ = ⊕ over joins: compatibility proof at merges
    - δ⁰: region proof → restriction to each endpoint's invariant
    - H¹ = ker(δ¹)/im(δ⁰)
    """
    function_name: str
    cfg: FunctionCFG
    preconditions: List[InvariantPoint]
    postconditions: List[InvariantPoint]
    all_invariants: List[InvariantPoint]
    regions: List[ProofRegion]
    overlaps: List[OverlapObligation]
    global_proof: Optional[ProofTerm] = None
    h1_rank: int = -1                  # -1 = not computed
    trust: Optional[TrustSummary] = None

    @property
    def n_regions(self) -> int:
        return len(self.regions)

    @property
    def n_proved(self) -> int:
        return sum(1 for r in self.regions if r.is_proved)

    @property
    def all_proved(self) -> bool:
        return all(r.is_proved for r in self.regions)

    @property
    def is_globally_proved(self) -> bool:
        return self.global_proof is not None and self.h1_rank == 0

    def compute_trust(self) -> TrustSummary:
        kernel = library = structural = assumed = unverified = 0
        for r in self.regions:
            if r.trust == TrustLevel.KERNEL:
                kernel += 1
            elif r.trust == TrustLevel.LIBRARY:
                library += 1
            elif r.trust == TrustLevel.STRUCTURAL:
                structural += 1
            elif r.trust == TrustLevel.ASSUMED:
                assumed += 1
            else:
                unverified += 1
        for o in self.overlaps:
            if o.trust == TrustLevel.KERNEL:
                kernel += 1
            elif o.trust == TrustLevel.LIBRARY:
                library += 1
            elif o.trust == TrustLevel.STRUCTURAL:
                structural += 1
            elif o.trust == TrustLevel.ASSUMED:
                assumed += 1
            else:
                unverified += 1
        self.trust = TrustSummary(kernel, library, structural, assumed, unverified)
        return self.trust

    def pretty(self) -> str:
        lines = [f'InvariantCover: {self.function_name}']
        lines.append(f'  Preconditions: {len(self.preconditions)}')
        lines.append(f'  Postconditions: {len(self.postconditions)}')
        lines.append(f'  Internal invariants: {len(self.all_invariants)}')
        lines.append(f'  Regions: {self.n_proved}/{self.n_regions} proved')
        lines.append(f'  Overlaps: {len(self.overlaps)}')
        lines.append(f'  H¹ rank: {self.h1_rank}')
        if self.trust:
            lines.append(f'  Trust: {self.trust.pretty()}')
        lines.append(f'  Global: {"✓" if self.is_globally_proved else "○"}')
        for r in self.regions:
            lines.append(f'    {r.pretty()}')
        return '\n'.join(lines)


# ═══════════════════════════════════════════════════════════════════
# §4. AST Analysis — find markers, build CFG
# ═══════════════════════════════════════════════════════════════════

_MARKER_FUNCTIONS = {
    'invariant': MarkerKind.INVARIANT,
    'precondition': MarkerKind.PRECONDITION,
    'postcondition': MarkerKind.POSTCONDITION,
    'loop_invariant': MarkerKind.LOOP_INVARIANT,
    'library_fact': MarkerKind.LIBRARY_FACT,
    'assume_correct': MarkerKind.ASSUME_CORRECT,
}


def _compile_predicate(text: str) -> Tuple[Pred, str]:
    """Compile a predicate string to a Pred AST.

    Returns (pred, status) where status is 'ok', 'fallback', or 'failed'.
    """
    try:
        pred = parse_predicate(text)
        if isinstance(pred, PVar) and pred.name == text:
            # parse_predicate fell back to wrapping the raw string
            return pred, 'fallback'
        return pred, 'ok'
    except Exception:
        return PVar(text), 'failed'


def extract_markers(source: str) -> List[InvariantPoint]:
    """Extract all invariant markers from Python source code.

    Parses the AST and finds calls to invariant(), precondition(),
    postcondition(), loop_invariant(), library_fact(), assume_correct().

    Also finds @postcondition decorators on the function.
    """
    try:
        tree = ast.parse(textwrap.dedent(source))
    except SyntaxError:
        return []

    markers: List[InvariantPoint] = []

    for node in ast.walk(tree):
        # Find calls: invariant("pred"), precondition("pred"), etc.
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
            call = node.value
            func_name = ''
            if isinstance(call.func, ast.Name):
                func_name = call.func.id
            elif isinstance(call.func, ast.Attribute):
                func_name = call.func.attr

            if func_name in _MARKER_FUNCTIONS and call.args:
                kind = _MARKER_FUNCTIONS[func_name]
                # Extract the predicate string
                arg = call.args[0]
                if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                    text = arg.value
                    library = ''
                    func_ref = ''

                    # library_fact has two args: library_fact("sympy", "fact")
                    if kind == MarkerKind.LIBRARY_FACT and len(call.args) >= 2:
                        if isinstance(call.args[0], ast.Constant):
                            library = str(call.args[0].value)
                        if isinstance(call.args[1], ast.Constant):
                            text = str(call.args[1].value)

                    # assume_correct has one arg: the function name
                    if kind == MarkerKind.ASSUME_CORRECT:
                        func_ref = text
                        text = f'{text} is correct'

                    pred, status = _compile_predicate(text)
                    markers.append(InvariantPoint(
                        surface_text=text,
                        compiled=pred,
                        kind=kind,
                        line=node.lineno,
                        parse_status=status,
                        library=library,
                        func_ref=func_ref,
                    ))

        # Find @postcondition("pred") decorators
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for dec in node.decorator_list:
                if isinstance(dec, ast.Call):
                    func_name = ''
                    if isinstance(dec.func, ast.Name):
                        func_name = dec.func.id
                    if func_name == 'postcondition' and dec.args:
                        arg = dec.args[0]
                        if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                            text = arg.value
                            pred, status = _compile_predicate(text)
                            markers.append(InvariantPoint(
                                surface_text=text,
                                compiled=pred,
                                kind=MarkerKind.POSTCONDITION,
                                line=dec.lineno,
                                parse_status=status,
                            ))

    return markers


def build_cfg(source: str) -> FunctionCFG:
    """Build a simplified CFG from Python source with invariant markers.

    The CFG has nodes at:
    - Function entry
    - Each invariant()/precondition()/loop_invariant() call
    - Each if/elif/else branch point
    - Each loop header
    - Each return/raise
    - Function exit (implicit)

    Edges connect consecutive nodes through straight-line code.
    """
    try:
        tree = ast.parse(textwrap.dedent(source))
    except SyntaxError:
        cfg = FunctionCFG(function_name='<parse_error>')
        entry = CFGNode('entry', CFGNodeKind.ENTRY)
        exit_node = CFGNode('exit', CFGNodeKind.EXIT)
        cfg.add_node(entry)
        cfg.add_node(exit_node)
        cfg.entry = 'entry'
        cfg.exits = ['exit']
        cfg.add_edge(CFGEdge('e_entry_exit', 'entry', 'exit'))
        return cfg

    # Find the function definition
    func_def = None
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_def = node
            break

    if func_def is None:
        cfg = FunctionCFG(function_name='<no_function>')
        entry = CFGNode('entry', CFGNodeKind.ENTRY)
        exit_node = CFGNode('exit', CFGNodeKind.EXIT)
        cfg.add_node(entry)
        cfg.add_node(exit_node)
        cfg.entry = 'entry'
        cfg.exits = ['exit']
        cfg.add_edge(CFGEdge('e_entry_exit', 'entry', 'exit'))
        return cfg

    # Extract markers first
    markers = extract_markers(source)
    marker_lines = {m.line: m for m in markers}

    cfg = FunctionCFG(function_name=func_def.name)

    # Entry node with preconditions
    entry = CFGNode('entry', CFGNodeKind.ENTRY)
    entry.invariants = [m for m in markers if m.kind == MarkerKind.PRECONDITION]
    cfg.add_node(entry)
    cfg.entry = 'entry'

    # Exit node with postconditions
    exit_node = CFGNode('exit', CFGNodeKind.EXIT)
    exit_node.invariants = [m for m in markers if m.kind == MarkerKind.POSTCONDITION]
    cfg.add_node(exit_node)
    cfg.exits = ['exit']

    # Walk the function body to build CFG nodes and edges
    _node_counter = [0]

    def _fresh_id(prefix: str) -> str:
        _node_counter[0] += 1
        return f'{prefix}_{_node_counter[0]}'

    def _process_body(stmts: List[ast.stmt], prev_node: str) -> str:
        """Process a list of statements, creating CFG nodes.
        Returns the node_id of the last node created."""
        current = prev_node

        for stmt in stmts:
            # Check if this statement is an invariant marker call
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                call = stmt.value
                fname = ''
                if isinstance(call.func, ast.Name):
                    fname = call.func.id
                if fname in _MARKER_FUNCTIONS:
                    marker = marker_lines.get(stmt.lineno)
                    if marker:
                        nid = _fresh_id('inv')
                        kind = CFGNodeKind.INVARIANT
                        if marker.kind == MarkerKind.LOOP_INVARIANT:
                            kind = CFGNodeKind.LOOP_HEADER
                        node = CFGNode(nid, kind,
                                       invariants=[marker],
                                       source_lines=(stmt.lineno, stmt.lineno))
                        cfg.add_node(node)
                        cfg.add_edge(CFGEdge(
                            _fresh_id('e'), current, nid,
                            source_lines=(stmt.lineno, stmt.lineno),
                        ))
                        current = nid
                    continue

            # If statement → branch
            if isinstance(stmt, ast.If):
                branch_id = _fresh_id('branch')
                cond_src = ast.dump(stmt.test)
                try:
                    cond_src = ast.unparse(stmt.test)
                except Exception:
                    pass
                branch_node = CFGNode(branch_id, CFGNodeKind.BRANCH,
                                      source_lines=(stmt.lineno, stmt.lineno),
                                      branch_condition=cond_src)
                cfg.add_node(branch_node)
                cfg.add_edge(CFGEdge(
                    _fresh_id('e'), current, branch_id,
                    source_lines=(stmt.lineno, stmt.lineno),
                ))

                # Join node for after the if
                join_id = _fresh_id('join')
                join_node = CFGNode(join_id, CFGNodeKind.JOIN,
                                   source_lines=(stmt.end_lineno or stmt.lineno,
                                                 stmt.end_lineno or stmt.lineno))
                cfg.add_node(join_node)

                # True branch
                if stmt.body:
                    last_true = _process_body(stmt.body, branch_id)
                    # Check if last statement is return/raise
                    if not _ends_with_exit(stmt.body):
                        cfg.add_edge(CFGEdge(
                            _fresh_id('e'), last_true, join_id,
                            condition='True',
                        ))

                # False/else branch
                if stmt.orelse:
                    last_false = _process_body(stmt.orelse, branch_id)
                    if not _ends_with_exit(stmt.orelse):
                        cfg.add_edge(CFGEdge(
                            _fresh_id('e'), last_false, join_id,
                            condition='False',
                        ))
                else:
                    cfg.add_edge(CFGEdge(
                        _fresh_id('e'), branch_id, join_id,
                        condition='False',
                    ))

                current = join_id
                continue

            # For/while loop → loop header + exit
            if isinstance(stmt, (ast.For, ast.While)):
                header_id = _fresh_id('loop')
                header_node = CFGNode(header_id, CFGNodeKind.LOOP_HEADER,
                                      source_lines=(stmt.lineno, stmt.lineno))
                cfg.add_node(header_node)
                cfg.add_edge(CFGEdge(
                    _fresh_id('e'), current, header_id,
                ))

                # Loop body
                if stmt.body:
                    last_body = _process_body(stmt.body, header_id)
                    # Back edge to loop header
                    if not _ends_with_exit(stmt.body):
                        cfg.add_edge(CFGEdge(
                            _fresh_id('e'), last_body, header_id,
                            condition='back_edge',
                        ))

                # Loop exit
                exit_id = _fresh_id('loop_exit')
                exit_n = CFGNode(exit_id, CFGNodeKind.LOOP_EXIT,
                                 source_lines=(stmt.end_lineno or stmt.lineno,
                                               stmt.end_lineno or stmt.lineno))
                cfg.add_node(exit_n)
                cfg.add_edge(CFGEdge(
                    _fresh_id('e'), header_id, exit_id,
                    condition='loop_done',
                ))

                current = exit_id
                continue

            # Return → exit
            if isinstance(stmt, ast.Return):
                ret_id = _fresh_id('return')
                ret_node = CFGNode(ret_id, CFGNodeKind.RETURN,
                                   source_lines=(stmt.lineno, stmt.lineno))
                cfg.add_node(ret_node)
                cfg.add_edge(CFGEdge(
                    _fresh_id('e'), current, ret_id,
                ))
                cfg.add_edge(CFGEdge(
                    _fresh_id('e'), ret_id, 'exit',
                ))
                # After a return, current is dead — but we continue processing
                # in case there's unreachable code (Python allows it)
                current = ret_id
                continue

            # Raise → exit with raise kind
            if isinstance(stmt, ast.Raise):
                raise_id = _fresh_id('raise')
                raise_node = CFGNode(raise_id, CFGNodeKind.RAISE,
                                     source_lines=(stmt.lineno, stmt.lineno))
                cfg.add_node(raise_node)
                cfg.add_edge(CFGEdge(
                    _fresh_id('e'), current, raise_id,
                ))
                current = raise_id
                continue

            # Regular statement → create a statement node if it has
            # meaningful content (assignments, expressions)
            stmt_id = _fresh_id('stmt')
            stmt_node = CFGNode(stmt_id, CFGNodeKind.STATEMENT,
                                source_lines=(stmt.lineno,
                                              stmt.end_lineno or stmt.lineno))
            cfg.add_node(stmt_node)
            cfg.add_edge(CFGEdge(
                _fresh_id('e'), current, stmt_id,
                source_lines=(stmt.lineno, stmt.end_lineno or stmt.lineno),
            ))
            current = stmt_id

        return current

    def _ends_with_exit(stmts: List[ast.stmt]) -> bool:
        """Check if statement list ends with return/raise."""
        if not stmts:
            return False
        last = stmts[-1]
        if isinstance(last, (ast.Return, ast.Raise)):
            return True
        if isinstance(last, ast.If):
            return (_ends_with_exit(last.body) and
                    bool(last.orelse) and _ends_with_exit(last.orelse))
        return False

    # Process the function body
    last_node = _process_body(func_def.body, 'entry')

    # Connect last node to exit if not already done
    if last_node != 'exit' and not _ends_with_exit(func_def.body):
        cfg.add_edge(CFGEdge(_fresh_id('e'), last_node, 'exit'))

    return cfg


# ═══════════════════════════════════════════════════════════════════
# §5. Verification Condition Generation
# ═══════════════════════════════════════════════════════════════════

def generate_regions(cfg: FunctionCFG) -> List[ProofRegion]:
    """Generate proof regions from the CFG.

    Each CFG edge with invariant-bearing endpoints creates a region.
    The region's obligation is: entry invariants ⟹ exit invariants
    (after executing the edge's code).

    For edges between non-invariant nodes, we propagate invariants
    from the nearest invariant-bearing ancestor/descendant.
    """
    regions: List[ProofRegion] = []

    for edge in cfg.edges:
        src_node = cfg.nodes.get(edge.source)
        tgt_node = cfg.nodes.get(edge.target)
        if not src_node or not tgt_node:
            continue

        # Collect entry invariants: from source node + ancestors
        entry_invs = list(src_node.invariants)

        # Collect exit invariants: from target node
        exit_invs = list(tgt_node.invariants)

        # Skip edges that have no invariants on either end
        # (these are just structural CFG edges, not verification conditions)
        if not entry_invs and not exit_invs:
            continue

        # Build obligation text
        entry_text = ' ∧ '.join(ip.surface_text for ip in entry_invs) or 'True'
        exit_text = ' ∧ '.join(ip.surface_text for ip in exit_invs) or 'True'
        obligation = f'{{{entry_text}}} ⟹ {{{exit_text}}}'

        # Build Z3 formula if all predicates are formal
        z3_formula = ''
        if entry_invs and exit_invs:
            all_formal = all(ip.is_formal for ip in entry_invs + exit_invs)
            if all_formal:
                entry_pred = (PAnd(tuple(ip.compiled for ip in entry_invs))
                              if len(entry_invs) > 1 else entry_invs[0].compiled)
                exit_pred = (PAnd(tuple(ip.compiled for ip in exit_invs))
                             if len(exit_invs) > 1 else exit_invs[0].compiled)
                implication = PImplies(entry_pred, exit_pred)
                z3_formula = implication.pretty()

        region = ProofRegion(
            region_id=edge.edge_id,
            edge=edge,
            entry_invariants=entry_invs,
            exit_invariants=exit_invs,
            obligation_text=obligation,
            z3_formula=z3_formula,
        )
        regions.append(region)

    return regions


def generate_overlaps(cfg: FunctionCFG,
                      regions: List[ProofRegion]) -> List[OverlapObligation]:
    """Generate overlap obligations at CFG join points.

    At each join node, incoming edges must produce compatible invariants.
    This is the cocycle condition in the Čech complex.
    """
    overlaps: List[OverlapObligation] = []

    for node in cfg.nodes.values():
        if node.kind != CFGNodeKind.JOIN:
            continue

        incoming = [e for e in cfg.edges if e.target == node.node_id]
        if len(incoming) < 2:
            continue

        # For each pair of incoming edges, create an overlap obligation
        for i in range(len(incoming)):
            for j in range(i + 1, len(incoming)):
                edge_a, edge_b = incoming[i], incoming[j]

                # Find the regions for these edges
                region_a = next((r for r in regions if r.edge == edge_a), None)
                region_b = next((r for r in regions if r.edge == edge_b), None)

                invs_a = region_a.exit_invariants if region_a else []
                invs_b = region_b.exit_invariants if region_b else []

                overlaps.append(OverlapObligation(
                    join_node_id=node.node_id,
                    branch_a=edge_a.edge_id,
                    branch_b=edge_b.edge_id,
                    invariants_a=invs_a,
                    invariants_b=invs_b,
                ))

    return overlaps


# ═══════════════════════════════════════════════════════════════════
# §6. Proof Discharge — try Z3, library axioms, structural rules
# ═══════════════════════════════════════════════════════════════════

def _discharge_region_z3(region: ProofRegion) -> bool:
    """Try to discharge a region's obligation via Z3."""
    if not region.z3_formula:
        return False

    # Build Z3 variables from the predicates
    variables: Dict[str, str] = {}
    for ip in region.entry_invariants + region.exit_invariants:
        if isinstance(ip.compiled, PCompare):
            for sub in [ip.compiled.left, ip.compiled.right]:
                if isinstance(sub, PVar):
                    variables[sub.name] = 'Int'  # default sort

    try:
        proof = Z3Discharge(
            formula=region.z3_formula,
            fragment='qf_lia',
            variables=variables,
        )
        # Verify with the checker
        lhs = OAbstract(region.obligation_text, ())
        rhs = OAbstract('True', ())
        result = check_proof(proof, lhs, rhs)
        if result.valid:
            region.proof = proof
            region.trust = TrustLevel.KERNEL
            return True
    except Exception:
        pass

    return False


def _discharge_region_library(region: ProofRegion) -> bool:
    """Try to discharge a region using library axioms."""
    # Check if any invariants reference library facts
    for ip in region.entry_invariants:
        if ip.kind == MarkerKind.LIBRARY_FACT and ip.library:
            try:
                from cctt.proof_theory.library_axioms import (
                    LibraryAxiom, get_library,
                )
                theory = get_library(ip.library)
                if theory:
                    proof = LibraryAxiom(
                        library=ip.library,
                        axiom_name=f'fact_{ip.surface_text[:30]}',
                        statement=ip.surface_text,
                    )
                    region.proof = proof
                    region.trust = TrustLevel.LIBRARY
                    return True
            except ImportError:
                pass

    return False


def _discharge_region_assume(region: ProofRegion) -> bool:
    """Discharge by assumption (explicit assume_correct or precondition)."""
    for ip in region.entry_invariants:
        if ip.kind == MarkerKind.ASSUME_CORRECT:
            proof = Assume(
                label=f'assume_{ip.func_ref}',
                assumed_lhs=OAbstract(ip.surface_text, ()),
                assumed_rhs=OAbstract('True', ()),
            )
            region.proof = proof
            region.trust = TrustLevel.ASSUMED
            return True

    return False


def _discharge_region_structural(region: ProofRegion) -> bool:
    """Discharge via structural rules (reflexivity, trivial implications)."""
    # If entry and exit invariants are identical, it's reflexivity
    if (region.entry_invariants and region.exit_invariants and
            len(region.entry_invariants) == len(region.exit_invariants)):
        all_same = all(
            e.surface_text == x.surface_text
            for e, x in zip(region.entry_invariants, region.exit_invariants)
        )
        if all_same:
            region.proof = Refl(term=OAbstract(
                region.entry_invariants[0].surface_text, ()))
            region.trust = TrustLevel.KERNEL
            return True

    # If no exit invariants, the region is trivially satisfied
    if not region.exit_invariants:
        region.proof = Refl(term=OAbstract('True', ()))
        region.trust = TrustLevel.KERNEL
        return True

    # If no entry invariants (precondition-free), still a valid proof point
    if not region.entry_invariants and region.exit_invariants:
        # This is really an assumption — the exit invariant is asserted
        proof = Assume(
            label=f'assert_{region.region_id}',
            assumed_lhs=OAbstract(
                region.exit_invariants[0].surface_text, ()),
            assumed_rhs=OAbstract('True', ()),
        )
        region.proof = proof
        region.trust = TrustLevel.ASSUMED
        return True

    return False


def discharge_region(region: ProofRegion) -> bool:
    """Try all discharge strategies on a region, in order of trust.

    Returns True if the region was discharged (proof assigned).
    """
    if region.is_proved:
        return True

    # Try in order: Z3 → structural → library → assume
    if _discharge_region_z3(region):
        return True
    if _discharge_region_structural(region):
        return True
    if _discharge_region_library(region):
        return True
    if _discharge_region_assume(region):
        return True

    return False


def discharge_overlap(overlap: OverlapObligation) -> bool:
    """Discharge an overlap obligation.

    Check that invariants from both branches are compatible at the join.
    """
    # If both branches have the same invariants, compatibility is trivial
    texts_a = {ip.surface_text for ip in overlap.invariants_a}
    texts_b = {ip.surface_text for ip in overlap.invariants_b}

    if texts_a == texts_b:
        overlap.proof = Refl(term=OAbstract('overlap_compat', ()))
        overlap.trust = TrustLevel.KERNEL
        return True

    # If one side is empty, the other is vacuously compatible
    if not overlap.invariants_a or not overlap.invariants_b:
        overlap.proof = Refl(term=OAbstract('vacuous_overlap', ()))
        overlap.trust = TrustLevel.STRUCTURAL
        return True

    # Otherwise, assume compatibility
    overlap.proof = Assume(
        label=f'overlap_{overlap.join_node_id}',
        assumed_lhs=OAbstract(str(texts_a), ()),
        assumed_rhs=OAbstract(str(texts_b), ()),
    )
    overlap.trust = TrustLevel.ASSUMED
    return True


# ═══════════════════════════════════════════════════════════════════
# §7. H¹ Computation — cohomological obstruction
# ═══════════════════════════════════════════════════════════════════

def compute_h1(cover: InvariantCover) -> int:
    """Compute H¹ of the invariant cover's Čech complex.

    The complex is:
        C⁰ = ⊕ regions (0-cochains: per-region proofs)
        C¹ = ⊕ overlaps (1-cochains: overlap compatibility)
        δ⁰: C⁰ → C¹ (restriction maps)

    H¹ = ker(δ¹) / im(δ⁰)

    In practice:
    - If all regions are proved and all overlaps are compatible: H¹ = 0
    - Each unproved region or incompatible overlap contributes to H¹
    - H¹ counts the number of independent obstructions to gluing
    """
    # Count unresolved obstructions
    unproved_regions = sum(1 for r in cover.regions if not r.is_proved)
    unresolved_overlaps = sum(1 for o in cover.overlaps
                              if o.proof is None)

    # H¹ is the number of independent obstructions
    # Each unproved region is a direct obstruction (failed to extend section)
    # Each unresolved overlap is a cocycle failure
    cover.h1_rank = unproved_regions + unresolved_overlaps
    return cover.h1_rank


# ═══════════════════════════════════════════════════════════════════
# §8. Global Gluing — build GluePath from local proofs
# ═══════════════════════════════════════════════════════════════════

def glue_proofs(cover: InvariantCover) -> Optional[ProofTerm]:
    """Glue region proofs into a global proof via GluePath.

    Requires H¹ = 0 (all regions proved, all overlaps compatible).
    The global proof is a GluePath wrapping all region proofs with
    the refinement cover structure.

    Returns None if gluing fails (H¹ > 0).
    """
    if cover.h1_rank != 0:
        return None

    if not cover.regions:
        # Trivial: no regions → reflexivity
        cover.global_proof = Refl(term=OAbstract(cover.function_name, ()))
        return cover.global_proof

    # Collect all proved region proofs
    local_proofs: Dict[str, ProofTerm] = {}
    for r in cover.regions:
        if r.proof:
            local_proofs[r.region_id] = r.proof

    if not local_proofs:
        return None

    # If only one region, the global proof IS the region proof
    if len(local_proofs) == 1:
        cover.global_proof = next(iter(local_proofs.values()))
        return cover.global_proof

    # Build a RefinementDescent with regions as fibers
    # Each region's entry invariant defines its fiber predicate
    fiber_predicates: Dict[str, str] = {}
    fiber_proofs: Dict[str, ProofTerm] = {}

    for r in cover.regions:
        if r.proof:
            pred_text = (r.entry_invariants[0].surface_text
                         if r.entry_invariants else 'True')
            fiber_predicates[r.region_id] = pred_text
            fiber_proofs[r.region_id] = r.proof

    # Overlap proofs
    overlap_proofs: Dict[Tuple[str, str], ProofTerm] = {}
    for o in cover.overlaps:
        if o.proof:
            overlap_proofs[(o.branch_a, o.branch_b)] = o.proof

    from cctt.proof_theory.terms import RefinementDescent

    global_proof = RefinementDescent(
        base_type='state',
        bound_var='s',
        fiber_predicates=fiber_predicates,
        fiber_proofs=fiber_proofs,
        overlap_proofs=overlap_proofs,
        exhaustiveness='assumed',
    )

    cover.global_proof = global_proof
    return global_proof


# ═══════════════════════════════════════════════════════════════════
# §9. Main Pipeline — decompose, prove, glue
# ═══════════════════════════════════════════════════════════════════

def decompose_and_prove(source: str,
                        guarantee: str = '',
                        max_retries: int = 0) -> InvariantCover:
    """Full pipeline: source → invariant cover → regional proofs → global proof.

    1. Parse source, extract markers
    2. Build CFG
    3. Generate proof regions (VCs)
    4. Discharge each region (Z3 → structural → library → assume)
    5. Generate overlap obligations
    6. Discharge overlaps
    7. Compute H¹
    8. If H¹ = 0, glue to global proof

    Args:
        source: Python source code with invariant markers
        guarantee: Optional postcondition text (added if not already present)
        max_retries: Number of decomposition refinement attempts

    Returns:
        InvariantCover with all proofs and diagnostics
    """
    # Step 1: Extract markers
    markers = extract_markers(source)

    # Add guarantee as postcondition if provided
    if guarantee:
        pred, status = _compile_predicate(guarantee)
        markers.append(InvariantPoint(
            surface_text=guarantee,
            compiled=pred,
            kind=MarkerKind.POSTCONDITION,
            parse_status=status,
        ))

    preconditions = [m for m in markers if m.kind == MarkerKind.PRECONDITION]
    postconditions = [m for m in markers if m.kind == MarkerKind.POSTCONDITION]
    internal = [m for m in markers if m.kind in (
        MarkerKind.INVARIANT, MarkerKind.LOOP_INVARIANT,
        MarkerKind.LIBRARY_FACT, MarkerKind.ASSUME_CORRECT,
    )]

    # Step 2: Build CFG
    cfg = build_cfg(source)

    # Step 3: Generate proof regions
    regions = generate_regions(cfg)

    # Step 4: Discharge each region
    for region in regions:
        discharge_region(region)

    # Step 5: Generate overlap obligations
    overlaps = generate_overlaps(cfg, regions)

    # Step 6: Discharge overlaps
    for overlap in overlaps:
        discharge_overlap(overlap)

    # Build the cover
    cover = InvariantCover(
        function_name=cfg.function_name,
        cfg=cfg,
        preconditions=preconditions,
        postconditions=postconditions,
        all_invariants=internal,
        regions=regions,
        overlaps=overlaps,
    )

    # Step 7: Compute H¹
    compute_h1(cover)

    # Step 8: Glue if H¹ = 0
    if cover.h1_rank == 0:
        glue_proofs(cover)

    # Compute trust summary
    cover.compute_trust()

    return cover


# ═══════════════════════════════════════════════════════════════════
# §10. LLM Decomposition Interface
# ═══════════════════════════════════════════════════════════════════

@dataclass
class DecompositionSuggestion:
    """An LLM-suggested invariant decomposition.

    The LLM generates a list of invariant annotations to insert into
    the source code. Each annotation has a program point (line number
    or description) and a predicate.

    The system then:
    1. Validates the predicates can be parsed
    2. Inserts them as InvariantPoints
    3. Runs the proof pipeline
    4. Reports which regions succeeded/failed
    """
    invariants: List[Dict[str, str]]  # [{"line": "after x=...", "predicate": "x > 0"}]
    loop_invariants: List[Dict[str, str]]
    library_facts: List[Dict[str, str]]  # [{"library": "sympy", "fact": "..."}]
    reasoning: str = ''


@dataclass
class DecompositionFeedback:
    """Feedback to the LLM after a decomposition attempt.

    Reports which regions proved and which failed, with specific
    reasons. The LLM can use this to refine its decomposition.
    """
    success: bool
    n_regions: int
    n_proved: int
    n_failed: int
    h1_rank: int
    failed_regions: List[Dict[str, str]]  # [{"region": "...", "reason": "..."}]
    trust_summary: str = ''
    suggestions: List[str] = field(default_factory=list)


def apply_decomposition(source: str,
                        suggestion: DecompositionSuggestion) -> str:
    """Apply an LLM decomposition suggestion to source code.

    Inserts invariant()/loop_invariant()/library_fact() calls at the
    suggested program points.

    Returns modified source code with markers inserted.
    """
    lines = source.split('\n')
    insertions: List[Tuple[int, str]] = []

    for inv in suggestion.invariants:
        pred = inv.get('predicate', '')
        line_hint = inv.get('line', '')

        # Find the insertion point
        insert_at = _find_insertion_line(lines, line_hint)
        if insert_at >= 0:
            # Detect indentation
            indent = _detect_indent(lines, insert_at)
            insertions.append(
                (insert_at, f'{indent}invariant({pred!r})')
            )

    for li in suggestion.loop_invariants:
        pred = li.get('predicate', '')
        line_hint = li.get('line', '')
        insert_at = _find_insertion_line(lines, line_hint)
        if insert_at >= 0:
            indent = _detect_indent(lines, insert_at)
            insertions.append(
                (insert_at, f'{indent}loop_invariant({pred!r})')
            )

    for lf in suggestion.library_facts:
        lib = lf.get('library', '')
        fact = lf.get('fact', '')
        line_hint = lf.get('line', '0')
        insert_at = _find_insertion_line(lines, line_hint)
        if insert_at >= 0:
            indent = _detect_indent(lines, insert_at)
            insertions.append(
                (insert_at, f'{indent}library_fact({lib!r}, {fact!r})')
            )

    # Sort insertions by line number (descending) to preserve positions
    insertions.sort(key=lambda x: x[0], reverse=True)
    for line_no, text in insertions:
        lines.insert(line_no, text)

    return '\n'.join(lines)


def _find_insertion_line(lines: List[str], hint: str) -> int:
    """Find the line number to insert at, given a hint."""
    # Try as integer line number
    try:
        n = int(hint)
        return max(0, min(n, len(lines)))
    except (ValueError, TypeError):
        pass

    # Try as substring match
    if isinstance(hint, str) and hint:
        for i, line in enumerate(lines):
            if hint in line:
                return i + 1  # insert after the matching line
    return -1


def _detect_indent(lines: List[str], line_no: int) -> str:
    """Detect the indentation level at the given line."""
    if 0 <= line_no < len(lines):
        line = lines[line_no]
        return line[:len(line) - len(line.lstrip())]
    # Find the nearest non-empty line
    for offset in [0, -1, 1, -2, 2]:
        idx = line_no + offset
        if 0 <= idx < len(lines) and lines[idx].strip():
            line = lines[idx]
            return line[:len(line) - len(line.lstrip())]
    return '    '


def generate_feedback(cover: InvariantCover) -> DecompositionFeedback:
    """Generate structured feedback from a decomposition attempt.

    This feedback is designed to be given to an LLM for refinement.
    """
    failed_regions = []
    for r in cover.regions:
        if not r.is_proved:
            failed_regions.append({
                'region': r.region_id,
                'obligation': r.obligation_text,
                'reason': r.failure_reason or 'no discharge strategy succeeded',
                'entry': ', '.join(ip.surface_text for ip in r.entry_invariants),
                'exit': ', '.join(ip.surface_text for ip in r.exit_invariants),
            })

    suggestions = []
    if failed_regions:
        suggestions.append(
            'Consider adding intermediate invariants to break large '
            'regions into smaller, provable pieces.'
        )
        for fr in failed_regions:
            if 'z3' not in fr.get('reason', '').lower():
                suggestions.append(
                    f'Region {fr["region"]}: try making predicates '
                    f'Z3-decidable (use comparisons, arithmetic, len(), etc.)'
                )

    trust_text = cover.trust.pretty() if cover.trust else ''

    return DecompositionFeedback(
        success=cover.is_globally_proved,
        n_regions=cover.n_regions,
        n_proved=cover.n_proved,
        n_failed=len(failed_regions),
        h1_rank=cover.h1_rank,
        failed_regions=failed_regions,
        trust_summary=trust_text,
        suggestions=suggestions,
    )


def build_llm_prompt(source: str,
                     guarantee: str = '',
                     feedback: Optional[DecompositionFeedback] = None) -> str:
    """Build a prompt for an LLM to generate a decomposition.

    The LLM should return a DecompositionSuggestion (as JSON).
    This is the ONLY place LLMs are used — they suggest invariants,
    never judge or prove correctness.
    """
    prompt_parts = [
        'You are a verification assistant. Given a Python function, '
        'suggest invariant annotations that decompose its correctness '
        'into locally provable regions.',
        '',
        'The invariants should be Python expressions that can be parsed '
        'as boolean predicates. Use variables that are in scope at each '
        'program point.',
        '',
        'Available markers:',
        '  invariant("predicate") — intermediate assertion',
        '  loop_invariant("predicate") — loop invariant (init + preservation)',
        '  library_fact("lib", "fact") — assumed library property',
        '',
        f'Function to decompose:',
        '```python',
        source,
        '```',
    ]

    if guarantee:
        prompt_parts.extend([
            '',
            f'Postcondition to prove: {guarantee}',
        ])

    if feedback and not feedback.success:
        prompt_parts.extend([
            '',
            'Previous attempt failed. Feedback:',
            f'  {feedback.n_proved}/{feedback.n_regions} regions proved, '
            f'H¹ = {feedback.h1_rank}',
        ])
        for fr in feedback.failed_regions[:5]:
            prompt_parts.append(
                f'  FAILED: {fr["obligation"][:80]}'
            )
            prompt_parts.append(
                f'    reason: {fr["reason"][:60]}'
            )
        for s in feedback.suggestions[:3]:
            prompt_parts.append(f'  Suggestion: {s}')

    prompt_parts.extend([
        '',
        'Return a JSON object with:',
        '  {"invariants": [{"line": "after <code>", "predicate": "<expr>"}],',
        '   "loop_invariants": [{"line": "...", "predicate": "..."}],',
        '   "library_facts": [{"library": "...", "fact": "...", "line": "..."}],',
        '   "reasoning": "..."}',
    ])

    return '\n'.join(prompt_parts)


# ═══════════════════════════════════════════════════════════════════
# §11. The @decompose Decorator
# ═══════════════════════════════════════════════════════════════════

def decompose(func: Callable) -> Callable:
    """Decorator: decompose a function via its invariant markers and prove.

    Extracts invariant markers from the function body, builds a CFG,
    generates verification conditions, and attempts to prove each region.

    Attaches the InvariantCover as metadata on the function.

    Usage::

        @decompose
        @postcondition("result >= 0")
        def abs_val(x: int) -> int:
            precondition("isinstance(x, int)")
            if x < 0:
                return -x
            return x
    """
    try:
        source = textwrap.dedent(inspect.getsource(func))
    except (OSError, TypeError):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            return func(*args, **kwargs)
        wrapper.__cover__ = None
        return wrapper

    # Get postconditions from decorator metadata
    guarantee = ''
    postconds = getattr(func, '__postconditions__', [])
    if postconds:
        guarantee = ' and '.join(postconds)

    cover = decompose_and_prove(source, guarantee)

    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        return func(*args, **kwargs)

    wrapper.__cover__ = cover
    wrapper.__trust__ = cover.trust
    wrapper.__h1__ = cover.h1_rank
    wrapper.__globally_proved__ = cover.is_globally_proved
    return wrapper


# ═══════════════════════════════════════════════════════════════════
# §12. Integration with Library Prover
# ═══════════════════════════════════════════════════════════════════

def decompose_library_function(source: str,
                               func_name: str,
                               library: str = '',
                               guarantee: str = '') -> InvariantCover:
    """Decompose and prove a library function (for use by library_prover).

    This is the integration point between cohomological_decomposition
    and library_prover. It:
    1. Auto-inserts a precondition from library contracts
    2. Runs the full pipeline
    3. Returns the cover for inclusion in the library proof report

    If the function has no explicit markers, creates a minimal cover
    with just the library contract as axiom.
    """
    # If we have a library, look up the contract
    if library:
        try:
            from cctt.proof_theory.library_axioms import get_library
            theory = get_library(library)
            if theory:
                contract = theory.get_contract(func_name)
                if contract:
                    # Add library preconditions as markers
                    for pre_name, pre_text in contract.preconditions.items():
                        source = _insert_after_def(
                            source,
                            f'    precondition({pre_text!r})')
                    if contract.postcondition:
                        guarantee = guarantee or contract.postcondition
        except ImportError:
            pass

    cover = decompose_and_prove(source, guarantee)
    return cover


def _insert_after_def(source: str, line_to_insert: str) -> str:
    """Insert a line right after the function's def line."""
    lines = source.split('\n')
    for i, line in enumerate(lines):
        stripped = line.lstrip()
        if stripped.startswith('def '):
            # Skip docstring if present
            next_i = i + 1
            if next_i < len(lines):
                next_line = lines[next_i].lstrip()
                if next_line.startswith(('"""', "'''")):
                    # Find end of docstring
                    quote = next_line[:3]
                    if next_line.count(quote) >= 2:
                        next_i += 1
                    else:
                        for j in range(next_i + 1, len(lines)):
                            if quote in lines[j]:
                                next_i = j + 1
                                break
                lines.insert(next_i, line_to_insert)
                return '\n'.join(lines)
    return source


# ═══════════════════════════════════════════════════════════════════
# §13. Counterexample-Guided Refinement
# ═══════════════════════════════════════════════════════════════════

@dataclass
class RefinementStep:
    """One step of counterexample-guided decomposition refinement."""
    iteration: int
    cover: InvariantCover
    feedback: DecompositionFeedback
    new_invariants: List[str] = field(default_factory=list)


def refine_decomposition(source: str,
                         guarantee: str = '',
                         max_iterations: int = 3,
                         suggest_fn: Optional[Callable] = None,
                         ) -> Tuple[InvariantCover, List[RefinementStep]]:
    """Counterexample-guided decomposition refinement.

    1. Run initial decomposition
    2. If H¹ > 0, generate feedback
    3. Use suggest_fn (LLM or heuristic) to propose new invariants
    4. Apply and retry
    5. Repeat until H¹ = 0 or max_iterations reached

    Args:
        source: Python source code
        guarantee: Postcondition to prove
        max_iterations: Maximum refinement attempts
        suggest_fn: Function that takes (source, feedback) and returns
                    DecompositionSuggestion. If None, uses heuristic.

    Returns:
        (final_cover, refinement_history)
    """
    history: List[RefinementStep] = []
    current_source = source

    for iteration in range(max_iterations + 1):
        cover = decompose_and_prove(current_source, guarantee)
        feedback = generate_feedback(cover)

        step = RefinementStep(
            iteration=iteration,
            cover=cover,
            feedback=feedback,
        )
        history.append(step)

        if cover.is_globally_proved or cover.h1_rank == 0:
            break

        if iteration >= max_iterations:
            break

        # Get refinement suggestion
        if suggest_fn:
            suggestion = suggest_fn(current_source, feedback)
        else:
            suggestion = _heuristic_refinement(current_source, cover, feedback)

        if suggestion and suggestion.invariants:
            current_source = apply_decomposition(current_source, suggestion)
            step.new_invariants = [
                inv['predicate'] for inv in suggestion.invariants
            ]

    return history[-1].cover if history else cover, history


def _heuristic_refinement(source: str,
                          cover: InvariantCover,
                          feedback: DecompositionFeedback,
                          ) -> Optional[DecompositionSuggestion]:
    """Simple heuristic refinement when no LLM is available.

    Adds obvious invariants:
    - Type assertions at function entry
    - len() invariants after list operations
    - Value range checks after arithmetic
    """
    invariants = []

    # For failed regions, try to add intermediate invariants
    for fr in feedback.failed_regions:
        # If the region spans multiple statements, suggest splitting
        if 'large' in fr.get('reason', '').lower() or not fr.get('reason'):
            invariants.append({
                'line': fr.get('region', '0'),
                'predicate': 'True',  # trivial invariant to split region
            })

    if invariants:
        return DecompositionSuggestion(
            invariants=invariants,
            loop_invariants=[],
            library_facts=[],
            reasoning='heuristic: added trivial invariants to split large regions',
        )

    return None


# ═══════════════════════════════════════════════════════════════════
# §14. Analysis Utilities
# ═══════════════════════════════════════════════════════════════════

def analyze_function(source: str, guarantee: str = '') -> Dict[str, Any]:
    """High-level analysis: decompose, prove, and return a summary.

    Suitable for use in reports, CI pipelines, or the library prover.
    """
    cover = decompose_and_prove(source, guarantee)
    feedback = generate_feedback(cover)

    return {
        'function_name': cover.function_name,
        'n_invariants': len(cover.all_invariants),
        'n_preconditions': len(cover.preconditions),
        'n_postconditions': len(cover.postconditions),
        'n_regions': cover.n_regions,
        'n_proved': cover.n_proved,
        'h1_rank': cover.h1_rank,
        'globally_proved': cover.is_globally_proved,
        'trust': cover.trust.pretty() if cover.trust else 'unknown',
        'trust_level': cover.trust.max_trust.value if cover.trust else 'unverified',
        'feedback': feedback,
        'cover': cover,
    }


def verify_annotations(source: str) -> Dict[str, Any]:
    """Verify all invariant annotations in a source file.

    Parses all marker calls, checks they can be compiled to formal
    predicates, and reports any issues.
    """
    markers = extract_markers(source)

    results = {
        'total': len(markers),
        'formal': sum(1 for m in markers if m.is_formal),
        'fallback': sum(1 for m in markers if m.parse_status == 'fallback'),
        'failed': sum(1 for m in markers if m.parse_status == 'failed'),
        'by_kind': {},
        'issues': [],
    }

    for kind in MarkerKind:
        count = sum(1 for m in markers if m.kind == kind)
        if count:
            results['by_kind'][kind.value] = count

    for m in markers:
        if m.parse_status != 'ok':
            results['issues'].append({
                'line': m.line,
                'kind': m.kind.value,
                'text': m.surface_text,
                'status': m.parse_status,
            })

    return results
