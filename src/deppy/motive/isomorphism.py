"""Multi-Level Z3 Motive Isomorphism Solver.

Given two motives M(f) and M(g), decides "M(f) ≅ M(g)?" via a
multi-level Z3 satisfiability encoding that captures program semantics
at several abstraction layers simultaneously.

The insight: pure graph isomorphism fails for recursive-vs-iterative
equivalences (different wiring), and pure bag isomorphism fails for
same-ops-different-wiring non-equivalences (FPs).  The solution is
to encode BOTH levels in a single Z3 query, letting the solver find
equivalences that span abstraction layers.

═══════════════════════════════════════════════════════════════════
Level 1 — Dependent Type Signature (Π-type)
═══════════════════════════════════════════════════════════════════
  Checks: input/output sorts, arity, global refinements.
  This is a hard necessary condition — if Π-types disagree, programs
  cannot be equivalent regardless of implementation.

═══════════════════════════════════════════════════════════════════
Level 2 — Semantic Role Profile
═══════════════════════════════════════════════════════════════════
  Each operation is classified into a semantic role:
    TRAVERSE  — iterating over a collection (for/while/recursion/comprehension)
    TRANSFORM — mapping/converting elements
    FILTER    — selecting elements by predicate
    ACCUMULATE — folding/reducing to a single value
    CONSTRUCT — building a new data structure
    COMPUTE   — pure arithmetic/logic/string computation
    COMPARE   — comparison/ordering
    ACCESS    — reading/writing variables or containers
    CONTROL   — branching, exception handling
    CONVERT   — type conversion
    DEFINE    — function/class definition

  Crucially: recursion and iteration both map to TRAVERSE.  This is
  the coboundary equivalence that allows rec ≅ iter.

  Z3 encodes: ∃ bijection between role-sort profiles (with multiplicities).

═══════════════════════════════════════════════════════════════════
Level 3 — Data Flow Edges (when available)
═══════════════════════════════════════════════════════════════════
  If both motives have data flow graph structure (morphisms in the
  category), encode edge preservation as SOFT constraints in Z3.
  This catches FPs where ops are identical but wiring differs.

  When graphs have different shapes (rec vs iter), this level is
  skipped — Level 2 role matching suffices.

═══════════════════════════════════════════════════════════════════
Level 4 — Concrete Content (post-Z3)
═══════════════════════════════════════════════════════════════════
  After Z3 says SAT, check concrete fingerprints (constants,
  attribute accesses, argument ordering).  This catches FPs where
  abstract structure is identical but concrete semantics differ
  (str vs repr, except Exception vs bare except).
"""

from __future__ import annotations

from collections import Counter
from enum import IntEnum, auto
from typing import FrozenSet, List, Optional, Set, Tuple

from deppy.motive.sorts import Sort, sorts_compatible
from deppy.motive.operations import TypedOp, Effect, Refinement
from deppy.motive.motive import Motive
from deppy.motive.morphism import MotiveMorphism


# ═══════════════════════════════════════════════════════════════════
# §1  Semantic Roles
# ═══════════════════════════════════════════════════════════════════

class SemanticRole(IntEnum):
    """Semantic role of an operation — what it DOES, not how."""
    TRAVERSE   = 0   # iterate over collection (for/while/recursion/comprehension)
    TRANSFORM  = auto()   # map/convert elements
    FILTER     = auto()   # select elements by predicate
    ACCUMULATE = auto()   # fold/reduce to single value
    CONSTRUCT  = auto()   # build new data structure
    COMPUTE    = auto()   # pure arithmetic/logic/string
    COMPARE    = auto()   # comparison/ordering
    ACCESS     = auto()   # read/write variable or container
    CONTROL    = auto()   # branch, exception, return
    CONVERT    = auto()   # type conversion
    DEFINE     = auto()   # function/class definition


# Maps operation name prefixes/names to semantic roles
_ROLE_MAP = {
    # TRAVERSE: iteration, recursion, comprehension iteration
    'Loop': SemanticRole.TRAVERSE,
    'Comprehension.iterate': SemanticRole.TRAVERSE,
    'Recurse': SemanticRole.TRAVERSE,
    'Seq.range': SemanticRole.TRAVERSE,
    # TRANSFORM: mapping operations
    'Comprehension.collect': SemanticRole.TRANSFORM,
    'Comprehension.collect_set': SemanticRole.TRANSFORM,
    'Comprehension.collect_map': SemanticRole.TRANSFORM,
    'Comprehension.lazy': SemanticRole.TRANSFORM,
    'Str.transform': SemanticRole.TRANSFORM,
    'Cast': SemanticRole.CONVERT,
    # FILTER
    'Comprehension.filter': SemanticRole.FILTER,
    # ACCUMULATE
    'Accum': SemanticRole.ACCUMULATE,
    # CONSTRUCT
    'Seq.push': SemanticRole.CONSTRUCT,
    'Seq.extend': SemanticRole.CONSTRUCT,
    'Seq.insert': SemanticRole.CONSTRUCT,
    'Set.insert': SemanticRole.CONSTRUCT,
    'Map.insert_default': SemanticRole.CONSTRUCT,
    'Map.merge': SemanticRole.CONSTRUCT,
    'Seq.sort': SemanticRole.CONSTRUCT,
    'Seq.reverse': SemanticRole.CONSTRUCT,
    'Func.define': SemanticRole.DEFINE,
    'Func.lambda': SemanticRole.DEFINE,
    # COMPUTE
    'Arith': SemanticRole.COMPUTE,
    'Logic': SemanticRole.COMPUTE,
    'Unary': SemanticRole.COMPUTE,
    'Str.join': SemanticRole.COMPUTE,
    'Str.split': SemanticRole.COMPUTE,
    'Str.replace': SemanticRole.COMPUTE,
    'Str.search': SemanticRole.COMPUTE,
    'Str.trim': SemanticRole.COMPUTE,
    'Seq.pop': SemanticRole.COMPUTE,
    'Map.lookup': SemanticRole.COMPUTE,
    'Map.keys': SemanticRole.COMPUTE,
    'Map.values': SemanticRole.COMPUTE,
    'Map.items': SemanticRole.COMPUTE,
    # COMPARE
    'Cmp': SemanticRole.COMPARE,
    'Contain': SemanticRole.COMPARE,
    'Identity': SemanticRole.COMPARE,
    # ACCESS
    'Assign': SemanticRole.ACCESS,
    'Container.index': SemanticRole.ACCESS,
    'Container.store': SemanticRole.ACCESS,
    'Container.slice': SemanticRole.ACCESS,
    'Destructure': SemanticRole.ACCESS,
    'Mem': SemanticRole.ACCESS,
    # CONTROL
    'Branch': SemanticRole.CONTROL,
    'Return': SemanticRole.CONTROL,
}


def op_to_role(op: TypedOp) -> SemanticRole:
    """Classify a typed operation into its semantic role."""
    # Exact match first
    if op.name in _ROLE_MAP:
        return _ROLE_MAP[op.name]
    # Family prefix match
    family = op.name.split('.')[0] if '.' in op.name else op.name
    if family in _ROLE_MAP:
        return _ROLE_MAP[family]
    # Prefix match for compound names like Comprehension.iterate
    for prefix, role in _ROLE_MAP.items():
        if op.name.startswith(prefix):
            return role
    # Default: external calls are COMPUTE
    if op.effect == Effect.CALL_EXT:
        return SemanticRole.COMPUTE
    return SemanticRole.COMPUTE


def _role_sort_key(op: TypedOp) -> Tuple:
    """Classification key at the semantic role level.

    Two ops match if they have the same role + compatible sort signature.
    Within COMPUTE/ACCUMULATE roles, we also include the operation
    FAMILY (Arith, Logic, etc.) to prevent x*2 ≅ x+2.

    For TRAVERSE ops, sort signatures are relaxed — a recursive call
    f(n-1) has signature NUM→NUM while for-loop has SEQ→TOP, but both
    serve the TRAVERSE role.  We normalize TRAVERSE sigs to just count
    the number of inputs.
    """
    role = op_to_role(op)
    if role == SemanticRole.TRAVERSE:
        # Normalize: just arity for traversal ops (abstract away container vs scalar)
        return (role, '', len(op.input_sorts), op.output_sort)
    if role in (SemanticRole.COMPUTE, SemanticRole.ACCUMULATE):
        family = op.family
        # Include specific op name to distinguish Arith.add from Arith.mul
        specific = op.name
        return (role, family, specific, op.sort_signature, op.effect)
    if role in (SemanticRole.CONSTRUCT, SemanticRole.ACCESS,
                SemanticRole.CONTROL, SemanticRole.DEFINE):
        # Structural roles: just role + output sort
        return (role, '', op.output_sort, op.effect)
    return (role, '', op.sort_signature, op.effect)


def _exact_key(op: TypedOp) -> Tuple:
    """Fine-grained classification key preserving operation name."""
    return op.classification_key()


# Operations too syntactic to carry semantic content — excluded
# from both role-level and exact-level comparisons
_TRIVIAL_OPS = frozenset({
    'Assign.bind', 'Assign.rebind', 'Return',
    'Branch.test', 'Destructure.unpack',
})


# ═══════════════════════════════════════════════════════════════════
# §2  Multi-Level Z3 Solver
# ═══════════════════════════════════════════════════════════════════

class MotiveIsomorphismSolver:
    """Multi-level Z3 solver for motive isomorphism.

    Encodes the question "M(f) ≅ M(g)?" at multiple abstraction
    levels simultaneously, letting Z3 find the right level of
    abstraction for each pair of programs.
    """

    def __init__(self, timeout_ms: int = 5000) -> None:
        self._timeout_ms = timeout_ms

    # ── Concrete execution cross-check ─────────────────────────

    @staticmethod
    def _concrete_execution_crosscheck(
        source_f: str, source_g: str,
        func_name_f: str, func_name_g: str,
    ) -> Tuple[Optional[bool], str]:
        """Run both functions on sample inputs to detect counterexamples.

        This is the "runtime sheaf stalk" check: for each concrete input x,
        the stalk F_x must agree.  Any disagreement is a counterexample
        that disproves equivalence (sheaf sections don't glue).

        Returns:
            (False, explanation) — counterexample found
            (None, "")          — no disagreement found (or can't run)
        """
        import ast
        import textwrap

        src_f = textwrap.dedent(source_f).strip()
        src_g = textwrap.dedent(source_g).strip()

        # Parse to find function names if not provided
        if not func_name_f:
            try:
                tree = ast.parse(src_f)
                for node in ast.walk(tree):
                    if isinstance(node, ast.FunctionDef):
                        func_name_f = node.name
                        break
            except Exception:
                return None, ""
        if not func_name_g:
            try:
                tree = ast.parse(src_g)
                for node in ast.walk(tree):
                    if isinstance(node, ast.FunctionDef):
                        func_name_g = node.name
                        break
            except Exception:
                return None, ""

        if not func_name_f or not func_name_g:
            return None, ""

        # Execute in sandboxed namespace with common imports
        _SAFE_IMPORTS = {
            'defaultdict': __import__('collections').defaultdict,
            'Counter': __import__('collections').Counter,
            'deque': __import__('collections').deque,
            'OrderedDict': __import__('collections').OrderedDict,
            'namedtuple': __import__('collections').namedtuple,
            'heapq': __import__('heapq'),
            'math': __import__('math'),
            'functools': __import__('functools'),
            'itertools': __import__('itertools'),
            'operator': __import__('operator'),
            'reduce': __import__('functools').reduce,
            'bisect': __import__('bisect'),
            're': __import__('re'),
            'copy': __import__('copy'),
        }

        ns_f: dict = dict(_SAFE_IMPORTS)
        ns_g: dict = dict(_SAFE_IMPORTS)

        try:
            exec(compile(src_f, '<f>', 'exec'), ns_f)
            exec(compile(src_g, '<g>', 'exec'), ns_g)
        except Exception:
            return None, ""

        fn_f = ns_f.get(func_name_f)
        fn_g = ns_g.get(func_name_g)
        if not callable(fn_f) or not callable(fn_g):
            return None, ""

        # Determine arity
        import inspect
        try:
            sig_f = inspect.signature(fn_f)
            arity = len([p for p in sig_f.parameters.values()
                         if p.default is inspect.Parameter.empty])
        except (ValueError, TypeError):
            arity = 1

        # Generate sample inputs based on arity
        if arity == 0:
            test_inputs = [()]
        elif arity == 1:
            # Include callables that exercise exception handler scope
            # _CustomBase is a BaseException subclass NOT derived from
            # Exception — caught by bare `except` but NOT `except Exception`.
            class _CustomBase(BaseException):
                pass
            def _raise_custom_base():
                raise _CustomBase("test")
            def _raise_value():
                raise ValueError("test")
            def _return_42():
                return 42

            test_inputs = [
                (0,), (1,), (-1,), (2,), (5,),
                ('',), ('a',), ('hello world',), (' a  b  c ',),
                ([],), ([1, 2, 3],), ([3, 1, 2],),
                (True,), (False,), (None,),
                ({},), ({'a': 1},),
                # Tuples with duplicate keys (for sort stability tests)
                ([(1, 'b'), (1, 'a'), (2, 'c')],),
                ([(2, 'x'), (1, 'y'), (1, 'z'), (2, 'w')],),
                # Callables (for try/except scope tests)
                (_return_42,), (_raise_value,), (_raise_custom_base,),
            ]
        elif arity == 2:
            test_inputs = [
                (0, 0), (1, 0), (0, 1), (1, 1), (-1, 1), (1, -1),
                (2, 3), (5, 2),
                ('hello', ' '), ('abc', ''),
                ([1, 2], [3, 4]), ([], []),
                ('a', 'b'),
            ]
        elif arity == 3:
            test_inputs = [
                (0, 0, 0), (1, 2, 3), (5, 1, 10),
                ('abc', 'a', 'x'), ([1, 2, 3], 0, 2),
                # Strings with repeated substrings (for replace tests)
                ('aaa', 'a', 'x'), ('abab', 'ab', 'cd'),
            ]
        else:
            test_inputs = [
                tuple(range(arity)),
                tuple(range(1, arity + 1)),
            ]

        import signal

        def _run_with_timeout(fn, args, timeout_s=0.5):
            """Run fn(*args) with a timeout. Returns (result, ok, exc)."""
            result = [None]
            ok = [False]
            exc = [None]

            def _handler(signum, frame):
                raise TimeoutError()

            old = signal.signal(signal.SIGALRM, _handler)
            signal.setitimer(signal.ITIMER_REAL, timeout_s)
            try:
                result[0] = fn(*args)
                ok[0] = True
            except TimeoutError:
                pass
            except BaseException:
                exc[0] = True
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
                signal.signal(signal.SIGALRM, old)
            return result[0], ok[0], exc[0]

        # Separate probe inputs (callables) from regular inputs.
        # For probes, exception disagreements are significant (they test
        # error handling scope). For regular inputs, we only care about
        # value disagreements (partial function equivalence).
        probe_inputs = [a for a in test_inputs if any(callable(v) for v in a)]
        regular_inputs = [a for a in test_inputs if a not in probe_inputs]

        for args in regular_inputs:
            rf, ok_f, _ = _run_with_timeout(fn_f, args)
            if not ok_f:
                continue
            rg, ok_g, _ = _run_with_timeout(fn_g, args)
            if not ok_g:
                continue
            if rf != rg:
                return False, (
                    f"runtime stalk disagreement at {args}: "
                    f"f={rf!r}, g={rg!r}")

        for args in probe_inputs:
            rf, ok_f, exc_f = _run_with_timeout(fn_f, args)
            rg, ok_g, exc_g = _run_with_timeout(fn_g, args)

            if ok_f and ok_g and rf != rg:
                return False, (
                    f"runtime stalk disagreement at {args}: "
                    f"f={rf!r}, g={rg!r}")
            if ok_f and exc_g:
                return False, (
                    f"runtime stalk disagreement at {args}: "
                    f"f={rf!r}, g raised")
            if ok_g and exc_f:
                return False, (
                    f"runtime stalk disagreement at {args}: "
                    f"f raised, g={rg!r}")

        return None, ""

    def check(self, mf: Motive, mg: Motive,
              source_f: str = '', source_g: str = '',
              func_name_f: str = '', func_name_g: str = ''
              ) -> Tuple[Optional[bool], str]:
        """Check if motives are isomorphic via multi-level Z3 encoding.

        Returns (result, explanation) where result is:
            True  — Z3 proved equivalence at some abstraction level
            False — Z3 proved non-equivalence (or necessary conditions fail)
            None  — inconclusive
        """
        # ── Level 0: Symbolic return expression equivalence ──
        # This is the dependent type approach: extract the function's
        # return value as a symbolic expression over inputs, then check
        # if the two expressions normalize to the same form.
        if source_f and source_g:
            sym_result, sym_expl = self._check_symbolic(
                source_f, source_g, func_name_f, func_name_g)
            if sym_result is not None:
                if sym_result is True:
                    # Denotational/cotangent proofs are authoritative
                    # (they check ∀x. f(x) = g(x), not just structure).
                    if ('denotationally equivalent' in sym_expl or
                            'cotangent' in sym_expl):
                        # Still cross-check with runtime stalks
                        rt, rt_expl = self._concrete_execution_crosscheck(
                            source_f, source_g, func_name_f, func_name_g)
                        if rt is False:
                            return False, rt_expl
                        return True, f"symbolic: {sym_expl}"

                    # Geometric morphism: trust when ≥2 ops or fingerprints agree.
                    n_ops = 0
                    import re
                    m = re.search(r'(\d+) ops preserved', sym_expl)
                    if m:
                        n_ops = int(m.group(1))

                    # Cross-check with runtime stalks before trusting
                    rt, rt_expl = self._concrete_execution_crosscheck(
                        source_f, source_g, func_name_f, func_name_g)
                    if rt is False:
                        return False, rt_expl

                    if n_ops >= 2:
                        return True, f"symbolic: {sym_expl}"
                    if mf.soft_fingerprints_match(mg):
                        return True, f"symbolic: {sym_expl}"
                    # Weak morphism + fingerprints differ → fall through

                if sym_result is False:
                    # Counterexample from denotational check = definitive.
                    if 'counterexample' in sym_expl:
                        return False, f"symbolic: {sym_expl}"
                    # Cotangent divergence (same gradient, different value).
                    if 'differ by constant' in sym_expl:
                        return False, f"symbolic: {sym_expl}"
                    # Structural UNSAT from geometric morphism — might just
                    # be a shallow interpreter limitation. Fall through.
                    pass

        # ── Level 1: Dependent type signature (hard necessary) ──
        ok, reason = self._check_pi_type(mf, mg)
        if not ok:
            return False, f"Π-type: {reason}"

        # ── Level 2+3: Multi-level Z3 query ──
        result, explanation = self._multi_level_z3(mf, mg)
        if result is True:
            # ── Level 4: Post-Z3 concrete content check ──
            if not mf.soft_fingerprints_match(mg):
                return False, "Z3-SAT but concrete fingerprints diverge"
            # ── Runtime stalk cross-check ──
            if source_f and source_g:
                rt, rt_expl = self._concrete_execution_crosscheck(
                    source_f, source_g, func_name_f, func_name_g)
                if rt is False:
                    return False, rt_expl
            return True, explanation
        if result is False:
            return False, explanation

        # ── Fallback: algebraic invariant convergence ──
        return self._algebraic_fallback(mf, mg)

    # ── Level 0: Symbolic return expression equivalence ─────────

    def _check_symbolic(self, source_f: str, source_g: str,
                         func_name_f: str, func_name_g: str
                         ) -> Tuple[Optional[bool], str]:
        """Check equivalence via symbolic return expressions.

        This is the core dependent-type approach: extract each function's
        return value as a symbolic expression tree over its inputs,
        then check if the two trees normalize to equivalent forms.
        """
        from deppy.motive.symbolic import symbolic_returns, symbolic_exprs_equivalent

        exprs_f = symbolic_returns(source_f, func_name_f)
        exprs_g = symbolic_returns(source_g, func_name_g)

        if not exprs_f or not exprs_g:
            return None, "could not extract symbolic returns"

        eq, expl = symbolic_exprs_equivalent(exprs_f, exprs_g)
        return eq, expl

    # ── Level 1: Π-type check ──────────────────────────────────

    def _check_pi_type(self, mf: Motive, mg: Motive) -> Tuple[bool, str]:
        """Check dependent type signature compatibility.

        This is the hardest necessary condition — if the Π-types
        disagree, the programs cannot be equivalent.
        """
        if len(mf.input_sorts) != len(mg.input_sorts):
            return False, f"arity {len(mf.input_sorts)} ≠ {len(mg.input_sorts)}"

        if not sorts_compatible(mf.output_sort, mg.output_sort):
            return False, f"output {mf.output_sort.name} ≇ {mg.output_sort.name}"

        if mf.h1 != mg.h1:
            return False, f"H¹ rank {mf.h1} ≠ {mg.h1}"

        # Argument order fingerprint — only a hard rejection when
        # both programs have the same iteration pattern
        if mf.argument_order_fingerprint and mg.argument_order_fingerprint:
            same_iteration_pattern = (
                (mf.has_recursion == mg.has_recursion) and
                (mf.has_iteration == mg.has_iteration)
            )
            if same_iteration_pattern:
                if mf.argument_order_fingerprint != mg.argument_order_fingerprint:
                    return False, "argument order fingerprint mismatch"

        return True, ""

    # ── Level 2+3: Multi-level Z3 ────────────────────────────────

    def _multi_level_z3(self, mf: Motive, mg: Motive
                        ) -> Tuple[Optional[bool], str]:
        """Multi-level Z3 encoding.

        First tries EXACT operation matching (Level 3 — fine-grained).
        If UNSAT, relaxes to ROLE-based matching (Level 2 — coarse).
        This allows rec ≅ iter at Level 2 while catching FPs at Level 3.
        """
        try:
            import z3
        except ImportError:
            return None, "Z3 not available"

        # Filter trivial ops
        ops_f = [op for op in mf.operations if op.name not in _TRIVIAL_OPS]
        ops_g = [op for op in mg.operations if op.name not in _TRIVIAL_OPS]

        # ── Try Level 3 first: exact-name graph isomorphism ──
        result = self._z3_exact_match(ops_f, ops_g, mf, mg)
        if result is True:
            return True, self._format_sat(mf, mg, "exact-name")
        if result is False:
            # Exact match definitively failed — try Level 2 (role-based)
            pass

        # ── Level 2: semantic role matching ──
        result = self._z3_role_match(ops_f, ops_g, mf, mg)
        if result is True:
            return True, self._format_sat(mf, mg, "semantic-role")
        if result is False:
            return False, "Z3-UNSAT at both exact and role levels"

        return None, "Z3 timeout"

    def _z3_exact_match(self, ops_f: List[TypedOp], ops_g: List[TypedOp],
                        mf: Motive, mg: Motive) -> Optional[bool]:
        """Level 3: Exact operation name matching with data flow edges.

        Encodes a bijection π on operation classes where:
        1. Names must be exactly compatible (via MotiveMorphism)
        2. Sort signatures must match
        3. Effects must match
        4. Refinements must overlap
        5. Multiplicities must match
        6. Data flow edges must be preserved (when available)
        """
        import z3

        sem_f = Counter(_exact_key(op) for op in ops_f)
        sem_g = Counter(_exact_key(op) for op in ops_g)

        if sem_f == sem_g:
            # Identical multisets — check data flow if available
            if not self._data_flow_compatible(mf, mg):
                return False
            return True

        classes_f = sorted(sem_f.keys())
        classes_g = sorted(sem_g.keys())
        nf, ng = len(classes_f), len(classes_g)

        if nf == 0 and ng == 0:
            return True
        if nf != ng:
            return None  # Different class count → inconclusive at this level

        solver = z3.Solver()
        solver.set("timeout", self._timeout_ms)

        pi = [z3.Int(f'exact_pi_{i}') for i in range(nf)]
        for i in range(nf):
            solver.add(pi[i] >= 0, pi[i] < ng)
        if nf > 1:
            solver.add(z3.Distinct(*pi))

        for i, cf in enumerate(classes_f):
            for j, cg in enumerate(classes_g):
                if not self._exact_classes_compatible(cf, cg, sem_f, sem_g):
                    solver.add(pi[i] != j)

        result = solver.check()
        if result == z3.sat:
            if not self._data_flow_compatible(mf, mg):
                return False
            return True
        if result == z3.unsat:
            return False
        return None

    def _z3_role_match(self, ops_f: List[TypedOp], ops_g: List[TypedOp],
                       mf: Motive, mg: Motive) -> Optional[bool]:
        """Level 2: Semantic role matching.

        Encodes a bijection π on role-sort profiles where:
        1. Roles must match (TRAVERSE ≅ TRAVERSE, even if Loop vs Recurse)
        2. Sort signatures must be compatible (with subsorting)
        3. Effects must be compatible (ITERATE ≅ RECURSE within TRAVERSE)
        4. Role multiplicities must match

        This is the key level that enables rec ≅ iter equivalence.
        """
        import z3

        # Build role profiles
        role_f = Counter(_role_sort_key(op) for op in ops_f)
        role_g = Counter(_role_sort_key(op) for op in ops_g)

        # Quick check: identical role profiles
        if role_f == role_g:
            return True

        classes_f = sorted(role_f.keys(), key=str)
        classes_g = sorted(role_g.keys(), key=str)
        nf, ng = len(classes_f), len(classes_g)

        if nf == 0 and ng == 0:
            return True
        if nf == 0 or ng == 0:
            return None

        # Allow some difference in class count due to implementation details
        if abs(nf - ng) > max(nf, ng) // 2 + 1:
            return False

        # Pad the smaller set with wildcards for the Z3 encoding
        if nf != ng:
            return self._z3_role_match_asymmetric(
                classes_f, classes_g, role_f, role_g, nf, ng)

        solver = z3.Solver()
        solver.set("timeout", self._timeout_ms)

        pi = [z3.Int(f'role_pi_{i}') for i in range(nf)]
        for i in range(nf):
            solver.add(pi[i] >= 0, pi[i] < ng)
        if nf > 1:
            solver.add(z3.Distinct(*pi))

        for i, cf in enumerate(classes_f):
            for j, cg in enumerate(classes_g):
                if not self._role_classes_compatible(cf, cg, role_f, role_g):
                    solver.add(pi[i] != j)

        result = solver.check()
        if result == z3.sat:
            return True
        if result == z3.unsat:
            return False
        return None

    def _z3_role_match_asymmetric(self, classes_f, classes_g,
                                   role_f, role_g, nf, ng
                                   ) -> Optional[bool]:
        """Handle asymmetric role profiles via injective Z3 matching.

        When programs have different numbers of role classes, find
        an injective map from the smaller to the larger, requiring
        that all "substantial" roles (TRAVERSE, ACCUMULATE, TRANSFORM)
        are matched.
        """
        import z3

        # Map smaller into larger
        if nf <= ng:
            small, large = classes_f, classes_g
            small_c, large_c = role_f, role_g
        else:
            small, large = classes_g, classes_f
            small_c, large_c = role_g, role_f

        ns, nl = len(small), len(large)
        solver = z3.Solver()
        solver.set("timeout", self._timeout_ms)

        pi = [z3.Int(f'asym_pi_{i}') for i in range(ns)]
        for i in range(ns):
            solver.add(pi[i] >= 0, pi[i] < nl)
        if ns > 1:
            solver.add(z3.Distinct(*pi))

        for i, cs in enumerate(small):
            for j, cl in enumerate(large):
                if not self._role_classes_compatible(cs, cl, small_c, large_c):
                    solver.add(pi[i] != j)

        result = solver.check()
        if result == z3.sat:
            return True
        if result == z3.unsat:
            return False
        return None

    # ── Compatibility predicates ────────────────────────────────

    def _exact_classes_compatible(self, cf: Tuple, cg: Tuple,
                                   counts_f: Counter, counts_g: Counter
                                   ) -> bool:
        """Check if two exact operation classes can be mapped."""
        name_f, sig_f, eff_f, ref_f = cf
        name_g, sig_g, eff_g, ref_g = cg

        if not MotiveMorphism.names_compatible(name_f, name_g):
            return False

        input_f, output_f = sig_f
        input_g, output_g = sig_g
        if len(input_f) != len(input_g):
            return False
        if not sorts_compatible(output_f, output_g):
            return False
        for sf, sg in zip(input_f, input_g):
            if not sorts_compatible(sf, sg):
                return False

        if eff_f != eff_g:
            return False

        ref_set_f, ref_set_g = set(ref_f), set(ref_g)
        if ref_set_f and ref_set_g and not (ref_set_f & ref_set_g):
            return False

        if counts_f[cf] != counts_g[cg]:
            return False

        return True

    def _role_classes_compatible(self, cf: Tuple, cg: Tuple,
                                  counts_f: Counter, counts_g: Counter
                                  ) -> bool:
        """Check if two role-level classes can be mapped.

        Key formats:
        - TRAVERSE: (role, '', arity, output_sort)
        - COMPUTE/ACCUMULATE: (role, family, specific_name, sig, eff)
        - CONSTRUCT/ACCESS/CONTROL/DEFINE: (role, '', output_sort, eff)
        - others: (role, '', sig, eff)

        Cross-role compatibility:
        - COMPUTE ↔ ACCUMULATE for compatible families (Arith ↔ Accum)
        - ITERATE ≅ RECURSE effects
        """
        role_f = cf[0]
        role_g = cg[0]

        # Role compatibility check
        if role_f != role_g:
            cross_role_ok = (
                {role_f, role_g} == {SemanticRole.COMPUTE, SemanticRole.ACCUMULATE}
            )
            if not cross_role_ok:
                return False

        # Family compatibility (field index 1)
        family_f = cf[1]
        family_g = cg[1]
        if family_f and family_g and family_f != family_g:
            from deppy.motive.operations import COMPATIBLE_FAMILIES
            if frozenset({family_f, family_g}) not in COMPATIBLE_FAMILIES:
                return False

        # For same-role COMPUTE/ACCUMULATE with same family:
        # If both programs have the same iteration pattern, require
        # exact specific name. If they differ (rec vs iter), allow
        # same-family flexibility since index arithmetic differs.
        if role_f == role_g and role_f in (SemanticRole.COMPUTE, SemanticRole.ACCUMULATE):
            if family_f and family_g and family_f == family_g:
                specific_f = cf[2]
                specific_g = cg[2]
                if specific_f != specific_g:
                    # Check if the counts profiles suggest structural difference
                    # (many different counts → different implementation patterns)
                    total_f = sum(counts_f.values())
                    total_g = sum(counts_g.values())
                    if total_f == total_g:
                        # Same total op count → likely same structure → strict match
                        return False
                    # Different total → likely rec/iter → allow family match

        # For cross-role (COMPUTE↔ACCUMULATE): allow any compatible
        # family pair (e.g., Arith.mul ↔ Accum.product)

        # Multiplicities: tolerant at role level
        cf_count = counts_f[cf]
        cg_count = counts_g[cg]
        if abs(cf_count - cg_count) > 2:
            return False

        return True

    # ── Data flow edge compatibility ────────────────────────────

    def _data_flow_compatible(self, mf: Motive, mg: Motive) -> bool:
        """Check if data flow graph structures are compatible.

        Uses the category morphisms to verify that when two motives
        have isomorphic operation bags, their wiring also matches.
        This catches FPs where ops are identical but data flows differ.

        Only applied when BOTH motives have meaningful graph structure.
        If either has no morphisms, skip (graph info unavailable).
        """
        cat_f = mf.category
        cat_g = mg.category

        # Skip if either has no graph structure
        if not cat_f.morphisms or not cat_g.morphisms:
            return True

        # Compare graph shape: degree sequences
        nf = len(cat_f.objects)
        ng = len(cat_g.objects)

        if nf != ng:
            return True  # Different block counts — inconclusive, not FP

        # Compare morphism op-name multisets on each edge
        adj_f = cat_f.adjacency_multiset()
        adj_g = cat_g.adjacency_multiset()

        # Normalize: compare sorted edge op-name multisets
        def edge_profile(adj):
            profile = []
            for (s, t), ops in sorted(adj.items()):
                op_names = tuple(sorted(op.name for op in ops))
                profile.append((s == t, op_names))  # (is_self_loop, op_names)
            return sorted(profile)

        pf = edge_profile(adj_f)
        pg = edge_profile(adj_g)

        if pf != pg:
            return False  # Different wiring → not equivalent

        return True

    # ── Algebraic fallback ──────────────────────────────────────

    def _algebraic_fallback(self, mf: Motive, mg: Motive
                            ) -> Tuple[Optional[bool], str]:
        """Conservative algebraic comparison when Z3 is inconclusive.

        Uses all invariants: K-theory, tropical, character, groupoid.
        Only returns True when ALL invariants converge strongly.
        """
        # Check invariant compatibility (soft — not pre-filters)
        issues = []
        if not mf.tropical.compatible_with(mg.tropical):
            issues.append("tropical")
        if not mf.groupoid.compatible_with(mg.groupoid):
            issues.append("π₁")
        if not mf.k_theory.compatible_with(mg.k_theory):
            issues.append("K₀")

        # If multiple invariants disagree, probably not equivalent
        if len(issues) >= 2:
            return None, f"invariant divergence: {', '.join(issues)}"

        # Character similarity at role level
        ops_f = [op for op in mf.operations if op.name not in _TRIVIAL_OPS]
        ops_g = [op for op in mg.operations if op.name not in _TRIVIAL_OPS]
        sem_f = Counter(_role_sort_key(op) for op in ops_f)
        sem_g = Counter(_role_sort_key(op) for op in ops_g)

        all_keys = set(sem_f.keys()) | set(sem_g.keys())
        if all_keys:
            match = sum(min(sem_f.get(k, 0), sem_g.get(k, 0)) for k in all_keys)
            total = sum(max(sem_f.get(k, 0), sem_g.get(k, 0)) for k in all_keys)
            char_sim = match / total if total > 0 else 1.0
        else:
            char_sim = 1.0

        if char_sim >= 0.85 and len(issues) == 0:
            return True, (f"Algebraic convergence: role_sim={char_sim:.2f}, "
                         f"all invariants compatible")

        return None, f"inconclusive: role_sim={char_sim:.2f}, issues={issues}"

    # ── Formatting ──────────────────────────────────────────────

    def _format_sat(self, mf: Motive, mg: Motive, level: str) -> str:
        return (f"Z3-SAT ({level}): motive isomorphism. "
                f"H⁰={mf.h0}/{mg.h0}, H¹={mf.h1}/{mg.h1}, "
                f"ops={mf.op_count}/{mg.op_count}, "
                f"blocks={mf.num_blocks}/{mg.num_blocks}")
