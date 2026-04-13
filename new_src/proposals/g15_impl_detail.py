"""
Code proposals for chapters 37-40 (g15_impl_detail):
  - The AST Compiler in Detail
  - Duck Type Inference in Detail
  - The Čech Complex Construction Algorithm
  - End-to-End Pipeline Trace

These proposals add utilities and documentation helpers that correspond
to the deepened chapter content.
"""
from __future__ import annotations


# ═══════════════════════════════════════════════════════════
# Proposal 1: Environment depth-bounded copy
# ═══════════════════════════════════════════════════════════
# Chapter 37 describes the depth-bounded inlining mechanism.
# This proposal adds a diagnostic method to Env showing the
# current inlining depth and whether further inlining is allowed.

def env_inline_status(env) -> dict:
    """Report inlining status of the compilation environment.

    Returns dict with:
      - depth: current nesting depth
      - can_inline: whether depth < 3
      - func_defs: list of available function names for inlining
    """
    return {
        'depth': env.depth,
        'can_inline': env.depth < 3,
        'func_defs': list(env.func_defs.keys()),
    }


# ═══════════════════════════════════════════════════════════
# Proposal 2: Section coverage checker
# ═══════════════════════════════════════════════════════════
# Chapter 37 describes the Section(guard, term) representation.
# This proposal adds a diagnostic to check whether section guards
# cover the full input space (their disjunction is tautological).

def check_section_coverage(sections, T) -> bool:
    """Check if the disjunction of section guards is tautological.

    Returns True if the sections provably cover all inputs.
    This is the presheaf completeness condition: every input
    falls under at least one section's guard.
    """
    try:
        from z3 import Solver, Or, Not, unsat
        solver = Solver()
        solver.set('timeout', 1000)
        guards = [s.guard for s in sections]
        solver.add(Not(Or(*guards)))
        return solver.check() == unsat
    except Exception:
        return False  # conservative: can't prove coverage


# ═══════════════════════════════════════════════════════════
# Proposal 3: Duck type lattice visualization
# ═══════════════════════════════════════════════════════════
# Chapter 38 describes the duck type lattice with its Hasse diagram.
# This proposal formalizes the lattice structure.

DUCK_TYPE_FIBERS = {
    'int': frozenset(['int']),
    'bool': frozenset(['bool']),
    'str': frozenset(['str']),
    'ref': frozenset(['ref']),
    'list': frozenset(['pair', 'ref']),
    'collection': frozenset(['pair', 'ref', 'str']),
    'any': frozenset(['int', 'bool', 'str', 'pair', 'ref', 'none']),
    'unknown': frozenset(['int', 'bool', 'str', 'pair', 'ref', 'none']),
}


def duck_type_leq(t1: str, t2: str) -> bool:
    """Check if duck type t1 is a subtype of t2 in the lattice.

    t1 ⊑ t2 iff F(t1) ⊆ F(t2), where F maps duck types to
    their allowed fiber sets.

    This formalizes the Galois connection described in Chapter 38:
    the inference algorithm returns the greatest lower bound
    (narrowest type) consistent with all observed operations.
    """
    f1 = DUCK_TYPE_FIBERS.get(t1, frozenset())
    f2 = DUCK_TYPE_FIBERS.get(t2, frozenset())
    return f1 <= f2


def duck_type_meet(t1: str, t2: str) -> str:
    """Compute the meet (greatest lower bound) of two duck types.

    The meet is the narrowest type whose fiber set contains
    both F(t1) and F(t2).  This is the Galois connection's
    abstract join (dual of the lattice meet).
    """
    f1 = DUCK_TYPE_FIBERS.get(t1, frozenset())
    f2 = DUCK_TYPE_FIBERS.get(t2, frozenset())
    union = f1 | f2
    # Find the narrowest duck type containing the union
    best = 'any'
    best_size = len(DUCK_TYPE_FIBERS['any'])
    for name, fibers in DUCK_TYPE_FIBERS.items():
        if union <= fibers and len(fibers) < best_size:
            best = name
            best_size = len(fibers)
    return best


# ═══════════════════════════════════════════════════════════
# Proposal 4: Opacity depth analysis
# ═══════════════════════════════════════════════════════════
# Chapter 39 describes the opacity check that prevents vacuous
# Z3 proofs.  This proposal adds a diagnostic function.

def analyze_term_opacity(term) -> dict:
    """Analyze the opacity of a Z3 PyObj term.

    Returns dict with:
      - total_depth: max depth of the term tree
      - uninterp_depth: max depth of uninterpreted function applications
      - uninterp_names: set of uninterpreted function names found
      - is_fully_interpreted: True if uninterp_depth == 0

    A fully interpreted term uses only Z3 RecFunctions with known
    semantics (binop, unop, truthy, fold).  When both terms in a
    comparison are fully interpreted, Z3's unsat proof is trusted.
    When either involves uninterpreted functions, the proof may be
    vacuously true.
    """
    names = set()
    depth = _opacity_walk(term, names, 0)
    return {
        'total_depth': depth,
        'uninterp_depth': depth,
        'uninterp_names': names,
        'is_fully_interpreted': len(names) == 0,
    }


def _opacity_walk(term, names: set, depth: int) -> int:
    """Walk a Z3 term tree collecting uninterpreted function names."""
    if depth > 10:
        return 0
    try:
        if term.num_args() == 0:
            return 0
        decl_name = term.decl().name()
        is_uninterp = any(decl_name.startswith(p)
                          for p in ('py_', 'meth_', 'call_', 'dyncall_', 'mut_'))
        if is_uninterp:
            names.add(decl_name)
        child_max = max(
            (_opacity_walk(term.arg(i), names, depth + 1)
             for i in range(term.num_args())),
            default=0
        )
        return (1 if is_uninterp else 0) + child_max
    except Exception:
        return 0


# ═══════════════════════════════════════════════════════════
# Proposal 5: Čech result pretty-printer
# ═══════════════════════════════════════════════════════════
# Chapter 39 and 40 describe the CechResult structure.
# This proposal adds a human-readable formatter.

def format_cech_result(cech) -> str:
    """Format a CechResult as a human-readable summary.

    Includes:
      - H⁰ (number of locally equivalent fibers)
      - H¹ rank (number of independent obstructions)
      - Coverage percentage
      - Obstruction details (if any)
    """
    lines = []
    lines.append(f"H⁰ = {cech.h0}")
    lines.append(f"H¹ rank = {cech.h1_rank}")
    lines.append(f"Total fibers = {cech.total_fibers}")
    lines.append(f"Unknown fibers = {cech.unknown_fibers}")

    if cech.total_fibers > 0:
        coverage = cech.h0 / cech.total_fibers * 100
        lines.append(f"Coverage = {coverage:.0f}%")

    if cech.equivalent is True:
        lines.append("Verdict: EQUIVALENT (local equivalences glue)")
    elif cech.equivalent is False:
        lines.append("Verdict: INEQUIVALENT")
        for obs in cech.obstructions:
            lines.append(f"  Obstruction on fiber: {obs}")
    else:
        lines.append("Verdict: INCONCLUSIVE")

    return '\n'.join(lines)


# ═══════════════════════════════════════════════════════════
# Proposal 6: Pipeline trace logger
# ═══════════════════════════════════════════════════════════
# Chapter 40 traces the full pipeline.  This proposal adds a
# structured trace logger that records each pipeline stage.

class PipelineTrace:
    """Records each stage of the CCTT equivalence pipeline.

    Usage:
        trace = PipelineTrace()
        trace.log('parse', 'Parsed both functions, 1 param each')
        trace.log('compile_f', 'fold(ADD, 0, ival(p0)+1, IntObj(0))')
        trace.log('duck_type', {'n': 'int'})
        trace.log('z3_check', 'UNSAT on (int,)')
        trace.log('cech', {'h0': 1, 'h1': 0})
        trace.log('verdict', 'EQUIVALENT')
        print(trace.format())
    """

    def __init__(self):
        self.stages: list[tuple[str, object]] = []

    def log(self, stage: str, data: object):
        """Record a pipeline stage with its data."""
        self.stages.append((stage, data))

    def format(self) -> str:
        """Format the trace as a human-readable report."""
        lines = ["═══ CCTT Pipeline Trace ═══"]
        for i, (stage, data) in enumerate(self.stages, 1):
            lines.append(f"Step {i}: {stage}")
            if isinstance(data, dict):
                for k, v in data.items():
                    lines.append(f"  {k}: {v}")
            else:
                lines.append(f"  {data}")
        return '\n'.join(lines)


# ═══════════════════════════════════════════════════════════
# Proposal 7: Compiler limitation detector
# ═══════════════════════════════════════════════════════════
# Chapter 37 lists what the compiler can't handle.  This proposal
# adds a pre-compilation check that warns about unsupported features.

def detect_compiler_limitations(source: str) -> list[str]:
    """Detect Python features that the CCTT compiler cannot fully handle.

    Returns a list of warnings about constructs that will produce
    fresh constants (uninterpreted symbols) rather than precise
    Z3 terms.
    """
    import ast
    warnings = []
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return ['SyntaxError: cannot parse source']

    for node in ast.walk(tree):
        if isinstance(node, ast.Lambda):
            warnings.append(
                f'Line {node.lineno}: lambda expression '
                '(will produce fresh constant, not inlined)')

        if isinstance(node, (ast.Yield, ast.YieldFrom)):
            warnings.append(
                f'Line {node.lineno}: generator yield '
                '(lazy evaluation semantics not modeled)')

        if isinstance(node, ast.ListComp):
            if len(node.generators) > 1:
                warnings.append(
                    f'Line {node.lineno}: nested comprehension '
                    '(outer generator hashed, inner chained)')

        if isinstance(node, ast.Constant) and isinstance(node.value, float):
            v = node.value
            if v != v or v == float('inf') or v == float('-inf'):
                warnings.append(
                    f'Line {node.lineno}: special float {v!r} '
                    '(produces fresh constant)')

    return warnings
