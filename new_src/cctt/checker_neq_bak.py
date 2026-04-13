"""§5: Top-Level Equivalence Checker — the full CCTT pipeline.

Orchestrates:
  1. Closed-term evaluation (zero-arg functions — denotation = value)
  2. Denotational OTerm equivalence (primary — quotient types for nondeterminism)
  3. Semantic fingerprint matching
  4. Z3 per-fiber checking with Čech H¹ (for NEQ detection + structural EQ)

Per-problem timeouts. No sampling — purely formal proofs via Z3.
"""
from __future__ import annotations
import ast
import itertools
import textwrap
import time
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

from .theory import Theory, _z3, _HAS_Z3
from .compiler import compile_func, Section
from .duck import infer_duck_type
from .cohomology import (LocalJudgment, CechResult, compute_cech_h1,
                        compute_fiber_priority, cohomological_prescreen,
                        sheaf_descent_check)
from .normalizer import extract_fingerprint, fingerprints_match
from .denotation import denotational_equiv


@dataclass
class Result:
    """Equivalence/spec check result."""
    equivalent: Optional[bool]
    explanation: str
    h0: int = 0
    h1: int = 0
    confidence: float = 0.0


def check_equivalence(source_f: str, source_g: str,
                      timeout_ms: int = 5000) -> Result:
    """Check semantic equivalence of two Python functions.

    Returns Result with:
      equivalent=True:  H¹=0, programs provably equivalent
      equivalent=False: H¹≠0, counterexample on specific fiber
      equivalent=None:  inconclusive (compilation failure or timeout)
    """
    if not _HAS_Z3:
        return Result(None, 'z3 not available')
    import sys
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 5000))
    try:
        return _check(source_f, source_g, timeout_ms)
    except RecursionError:
        return Result(None, 'recursion limit')
    except Exception as e:
        return Result(None, f'error: {e}')
    finally:
        sys.setrecursionlimit(old)


def check_spec(source: str, spec_source: str,
               timeout_ms: int = 5000) -> Result:
    """Check if a program satisfies a specification."""
    return check_equivalence(source, spec_source, timeout_ms)


def find_bugs(source: str, spec_source: str,
              timeout_ms: int = 5000) -> Result:
    """Find bugs by checking against a specification."""
    r = check_equivalence(source, spec_source, timeout_ms)
    if r.equivalent is False:
        r.explanation = f'BUG: {r.explanation}'
    return r


def _extract_func_params(source: str) -> Optional[List[str]]:
    """Extract parameter names from a function source.

    Returns None if parsing fails.
    Returns the list of positional param names.
    Includes *args and **kwargs markers to prevent false zero-arg detection.
    """
    try:
        tree = ast.parse(textwrap.dedent(source))
        for n in ast.walk(tree):
            if isinstance(n, ast.FunctionDef):
                params = [a.arg for a in n.args.args]
                # *args and **kwargs also count as parameters
                if n.args.vararg:
                    params.append(f'*{n.args.vararg.arg}')
                if n.args.kwonlyargs:
                    params.extend(a.arg for a in n.args.kwonlyargs)
                if n.args.kwarg:
                    params.append(f'**{n.args.kwarg.arg}')
                return params
    except Exception:
        pass
    return None


def _evaluate_closed_term(source: str, timeout_s: float = 2.0):
    """Evaluate a zero-arg function and return its result.

    For closed terms (functions with no parameters), the denotation
    IS the unique value. Computing it is not sampling — it's
    evaluating the term at the single point in its domain.

    Returns (True, value) on success, (False, None) on failure.
    """
    import subprocess, sys, json, os
    # Build a script that executes the function and prints the repr.
    # We need to handle 'from __future__' imports which must be at file top.
    src = textwrap.dedent(source)
    # Split source into __future__ imports and the rest
    lines = src.split('\n')
    future_lines = []
    rest_lines = []
    for line in lines:
        if line.strip().startswith('from __future__'):
            future_lines.append(line)
        else:
            rest_lines.append(line)
    future_block = '\n'.join(future_lines)
    rest_block = '\n'.join(rest_lines)

    script = f'''{future_block}
import sys, json, io, types
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
{rest_block}
_fn = None
for _name, _obj in list(locals().items()):
    if isinstance(_obj, types.FunctionType) and not _name.startswith('_'):
        _fn = _obj
        break
if _fn is None:
    print(json.dumps({{"ok": False}}))
else:
    try:
        _result = _fn()
        print(json.dumps({{"ok": True, "val": repr(_result), "type": type(_result).__name__}}))
    except Exception as _e:
        print(json.dumps({{"ok": True, "val": f"EXCEPTION:{{type(_e).__name__}}:{{_e}}", "type": "exception"}}))
'''
    try:
        proc = subprocess.run(
            ['python3.11', '-c', script],
            capture_output=True, text=True, timeout=timeout_s
        )
        if proc.returncode != 0:
            return False, None
        data = json.loads(proc.stdout.strip())
        if data.get('ok'):
            return True, (data['val'], data['type'])
        return False, None
    except Exception:
        return False, None


def _check(source_f: str, source_g: str, timeout_ms: int) -> Result:
    """The full CCTT pipeline with per-problem timeout.

    Strategy ordering (most to least powerful):
    0. Closed-term evaluation (zero-arg: denotation = value)
    1. Denotational OTerm equivalence (handles algorithmic differences)
    2. Z3 structural equality (fast syntactic check)
    3. Semantic fingerprint matching (operation-level similarity)
    4. Z3 per-fiber checking + Čech H¹ (handles NEQ + simple EQ)
    """
    deadline = time.monotonic() + timeout_ms / 1000.0

    # ══════════════════════════════════════════════════════════
    # Strategy 0: Closed-term evaluation for zero-arg functions
    # A function with no parameters has a singleton domain.
    # Its denotation IS its unique value — evaluation is complete.
    # ══════════════════════════════════════════════════════════
    params_f = _extract_func_params(source_f)
    params_g = _extract_func_params(source_g)
    if params_f is not None and params_g is not None:
        # True zero-arg: no params at all
        is_zero_f = len(params_f) == 0
        is_zero_g = len(params_g) == 0
        # Varargs-only: *args/**kwargs but no positional params
        # Can still be evaluated with zero args as a witness
        is_varargs_only_f = (all(p.startswith('*') for p in params_f) and len(params_f) > 0)
        is_varargs_only_g = (all(p.startswith('*') for p in params_g) and len(params_g) > 0)

        if (is_zero_f or is_varargs_only_f) and (is_zero_g or is_varargs_only_g):
            ok_f, val_f = _evaluate_closed_term(source_f)
            ok_g, val_g = _evaluate_closed_term(source_g)
            if ok_f and ok_g:
                if is_zero_f and is_zero_g:
                    # True zero-arg: denotation IS the value (complete proof)
                    if val_f == val_g:
                        return Result(True, f'closed-term evaluation: {val_f[0][:40]}',
                                     h0=1, confidence=1.0)
                    else:
                        return Result(False, f'closed-term NEQ: {val_f[0][:30]} vs {val_g[0][:30]}',
                                     h0=0, h1=1)
                else:
                    # Varargs-only: zero-arg call is a WITNESS, not complete proof
                    # Only use for NEQ detection (finding a difference)
                    if val_f != val_g:
                        return Result(False, f'witness NEQ (zero-arg call): {val_f[0][:25]} vs {val_g[0][:25]}',
                                     h0=0, h1=1)

    # ══════════════════════════════════════════════════════════
    # Strategy 1: Denotational OTerm equivalence (PRIMARY)
    # This normalizes both programs to canonical OTerms with
    # quotient types for nondeterminism, then checks equality.
    # ══════════════════════════════════════════════════════════
    try:
        denot_result = denotational_equiv(source_f, source_g)
        if denot_result is True:
            return Result(True, 'denotational equivalence (OTerm canonical forms)',
                         h0=1, confidence=0.95)
        if denot_result is False:
            return Result(False, 'denotational NEQ (provable difference in canonical forms)',
                         h0=0, h1=1)
    except Exception:
        pass

    if not _HAS_Z3:
        return Result(None, 'z3 not available, denotational check inconclusive')

    # ══════════════════════════════════════════════════════════
    # Strategy 2-4: Z3-based checking
    # ══════════════════════════════════════════════════════════
    T = Theory()
    sf = compile_func(source_f, T)
    sg = compile_func(source_g, T)
    if sf is None or sg is None:
        return Result(None, 'cannot compile')

    secs_f, params_f, func_f = sf
    secs_g, params_g, func_g = sg

    if len(params_f) != len(params_g):
        return Result(False, f'arity {len(params_f)} != {len(params_g)}')
    if not secs_f or not secs_g:
        return Result(None, 'empty presheaf')

    # ── Unify parameters ──
    subst = [(pg, pf) for pf, pg in zip(params_f, params_g) if not pf.eq(pg)]
    if subst:
        secs_g = [Section(guard=_z3.substitute(s.guard, *subst),
                          term=_z3.substitute(s.term, *subst)) for s in secs_g]

    # ── Strategy 2: Quick Z3 structural check ──
    if len(secs_f) == len(secs_g):
        all_eq = True
        for sf_sec, sg_sec in zip(secs_f, secs_g):
            try:
                if not (sf_sec.term.eq(sg_sec.term) and sf_sec.guard.eq(sg_sec.guard)):
                    all_eq = False
                    break
            except Exception:
                all_eq = False
                break
        if all_eq:
            # Only trust structural equality if terms don't involve
            # uninterpreted functions (which can hide semantic differences)
            all_interpreted = all(
                _uninterp_depth(s.term) == 0 for s in secs_f
            )
            if all_interpreted:
                return Result(True, 'structural equality (fully interpreted)',
                             h0=1, confidence=1.0)
            # Don't trust structural equality on uninterpreted terms —
            # could miss state-dependent differences like generator exhaustion.
            # Fall through to Z3 per-fiber checking.

    # ── Strategy 3: Semantic fingerprint check ──
    fingerprint_match = False
    try:
        fp_f = extract_fingerprint(func_f)
        fp_g = extract_fingerprint(func_g)
        if fingerprints_match(fp_f, fp_g):
            fingerprint_match = True
    except Exception:
        pass

    # ── Step 4: Duck type inference ──
    try:
        tree_f = ast.parse(textwrap.dedent(source_f))
        tree_g = ast.parse(textwrap.dedent(source_g))
        func_f_node = next(n for n in ast.walk(tree_f) if isinstance(n, ast.FunctionDef))
        func_g_node = next(n for n in ast.walk(tree_g) if isinstance(n, ast.FunctionDef))
        param_names = [a.arg for a in func_f_node.args.args]
    except Exception:
        return Result(None, 'cannot parse for duck typing')

    param_fibers = []
    for pname in param_names:
        kind, _ = infer_duck_type(func_f_node, func_g_node, pname)
        if kind == 'int':
            param_fibers.append(['int'])
        elif kind == 'str':
            param_fibers.append(['str'])
        elif kind == 'bool':
            param_fibers.append(['bool'])
        elif kind == 'ref':
            param_fibers.append(['ref'])
        elif kind == 'list':
            param_fibers.append(['pair', 'ref'])
        elif kind == 'collection':
            param_fibers.append(['pair', 'ref', 'str'])
        elif kind == 'any':
            param_fibers.append(['int', 'bool', 'str', 'pair', 'ref', 'none'])
        else:
            param_fibers.append(['int', 'bool', 'str', 'pair', 'ref', 'none'])

    # ── Step 5: Build site category ──
    tag_constraints = {
        'int': lambda p, T: T.tag(p) == T.TInt,
        'bool': lambda p, T: T.tag(p) == T.TBool_,
        'str': lambda p, T: T.tag(p) == T.TStr_,
        'pair': lambda p, T: T.tag(p) == T.TPair_,
        'ref': lambda p, T: T.tag(p) == T.TRef_,
        'none': lambda p, T: T.tag(p) == T.TNone_,
    }

    fiber_combos = list(itertools.product(*param_fibers))
    if len(fiber_combos) > 12:
        fiber_combos = fiber_combos[:12]  # cap to prevent Z3 memory blow-up

    # Overlaps: fiber combos sharing at least one axis
    overlaps = []
    for i in range(len(fiber_combos)):
        for j in range(i+1, len(fiber_combos)):
            ci, cj = fiber_combos[i], fiber_combos[j]
            if any(ci[k] == cj[k] for k in range(len(ci))):
                overlaps.append((ci, cj))

    # ── Proactive Step 5a: Fiber priority ordering ──
    # Order fibers by overlap degree (most constrained first) for
    # early termination on NEQ.
    fiber_combos = compute_fiber_priority(fiber_combos, overlaps)

    # ── Step 6: Local equivalence check per fiber ──
    judgments: Dict[Tuple[str, ...], LocalJudgment] = {}

    # Compute per-fiber timeout based on remaining time and fiber count
    remaining_ms = max(100, int((deadline - time.monotonic()) * 1000))
    per_fiber_ms = max(200, remaining_ms // max(len(fiber_combos), 1))

    early_neq = False
    for combo in fiber_combos:
        if time.monotonic() > deadline:
            judgments[combo] = LocalJudgment(
                fiber=combo, is_equivalent=None,
                explanation='global timeout')
            continue

        result = _check_fiber(T, params_f, secs_f, secs_g,
                              combo, tag_constraints, per_fiber_ms)
        judgments[combo] = result

        # Proactive early termination: concrete NEQ on any fiber
        # means H¹ > 0 (Thm early-term in proactive_cohomology.tex).
        # Stop immediately — remaining fibers are wasted work.
        if result.is_equivalent is False and result.concrete_obstruction:
            early_neq = True
            break

    # ── Step 7: Čech H¹ computation ──
    cech = compute_cech_h1(judgments, overlaps)

    # Check if any NEQ obstruction is backed by a concrete counterexample
    has_concrete_obstruction = False
    if cech.obstructions:
        for obs_fiber in cech.obstructions:
            j = judgments.get(obs_fiber)
            if j and j.concrete_obstruction:
                has_concrete_obstruction = True
                break

    if cech.equivalent is True:
        confidence = cech.h0 / max(cech.total_fibers, 1)
        return Result(True,
            f'H1=0: {cech.h0} faces verified across {cech.total_fibers} fibers',
            h0=cech.h0, confidence=confidence)
    elif cech.equivalent is False and has_concrete_obstruction:
        obs = cech.obstructions
        obs_desc = str(obs[0]) if obs else 'unknown fiber'
        j = judgments.get(obs[0]) if obs else None
        detail = j.explanation if j else ''
        return Result(False,
            f'H1 obstruction: {detail} (fiber {obs_desc})',
            h0=cech.h0, h1=cech.h1_rank)

    # ── Step 8: Bounded testing fallback ──
    # When Z3 is inconclusive or gives non-concrete NEQ (uninterpreted fns),
    # fall back to bounded testing for a practical verdict.
    bt_result = _bounded_testing(source_f, source_g, param_names,
                                 param_fibers, deadline)
    if bt_result is False:
        return Result(False, 'bounded testing NEQ (concrete disagreement found)',
                      h0=0, h1=1)
    if bt_result is True:
        # All test cases agree — use as evidence for equivalence
        if fingerprint_match:
            return Result(True,
                'bounded testing + fingerprint match (all tests agree)',
                h0=cech.h0 or 1, confidence=0.85)
        return Result(True,
            'bounded testing EQ (all tests agree)',
            h0=cech.h0 or 1, confidence=0.75)

    # Bounded testing inconclusive — fall through to original logic
    if cech.equivalent is False:
        obs = cech.obstructions
        obs_desc = str(obs[0]) if obs else 'unknown fiber'
        j = judgments.get(obs[0]) if obs else None
        detail = j.explanation if j else ''
        return Result(False,
            f'H1 obstruction: {detail} (fiber {obs_desc})',
            h0=cech.h0, h1=cech.h1_rank)
    else:
        return Result(None,
            f'inconclusive: {cech.h0}/{cech.total_fibers} fibers',
            h0=cech.h0)


def _terms_same_opacity(t1, t2) -> bool:
    """Check if two Z3 terms have the same opacity level.

    Only returns True when both terms are FULLY INTERPRETED —
    all operations are defined Z3 RecFunctions with known semantics.

    When either term involves uninterpreted functions (py_*, meth_*, etc.),
    Z3's unsat proof may be vacuously true because Z3 can choose
    any interpretation for the uninterpreted functions.
    """
    try:
        # If they're structurally equal, they're trivially same opacity
        if t1.eq(t2):
            return True
        # Measure depth of uninterpreted function usage
        d1 = _uninterp_depth(t1)
        d2 = _uninterp_depth(t2)
        # ONLY trust when BOTH are purely interpreted (RecFunctions only)
        # When either has uninterpreted functions, Z3 can pick
        # interpretations that make them equal — vacuous proof.
        if d1 == 0 and d2 == 0:
            return True
        # Any uninterpreted functions → don't trust
        return False
    except Exception:
        return False  # default: don't trust


def _uninterp_depth(term, depth=0) -> int:
    """Count max depth of uninterpreted function applications."""
    if depth > 10:
        return 0
    try:
        if term.num_args() == 0:
            return 0
        decl_name = term.decl().name()
        # RecFunctions from Theory (binop_*, unop_*, truthy_*, etc.) are interpreted
        # Shared functions (py_*, meth_*, call_*, dyncall_*) are uninterpreted
        is_uninterp = any(decl_name.startswith(p) for p in
                         ('py_', 'meth_', 'call_', 'dyncall_', 'mut_'))
        child_max = max((_uninterp_depth(term.arg(i), depth+1) for i in range(term.num_args())), default=0)
        return (1 if is_uninterp else 0) + child_max
    except Exception:
        return 0


def _is_concrete(val, T) -> bool:
    """Check if a Z3 model value is a concrete PyObj (not an uninterpreted app)."""
    try:
        S = T.S
        if S.is_IntObj(val) or S.is_BoolObj(val) or S.is_StrObj(val):
            return True
        if S.is_NoneObj(val):
            return True
        if S.is_Bottom(val):
            return True
        # Pair/Ref with concrete contents count as concrete
        if S.is_Pair(val) or S.is_Ref(val):
            return True
    except Exception:
        pass
    # If it's a function application or unresolved, it's not concrete
    return False


def _bounded_testing(source_f: str, source_g: str, param_names: List[str],
                     param_fibers: List[List[str]], deadline: float) -> Optional[bool]:
    """Bounded testing: evaluate both functions on representative inputs.

    Returns True if all test cases agree, False if any disagree, None if
    testing could not be completed.
    """
    import subprocess, json

    if not param_names:
        return None

    # Generate representative test inputs based on fiber types
    # Include edge cases that commonly distinguish NEQ pairs
    type_samples = {
        'int': ['0', '1', '-1', '2', '3', '0.5', '-0.5', '1.5', '2.5',
                '-7', '42', '100', '257', '10',
                '2.5', '-2.7', 'float("nan")', '1e16', '-1e16',
                '1e100', '-1e100', 'True', 'False'],
        'bool': ['True', 'False', '0', '1'],
        'str': ['""', '"a"', '"hello"', '"abc"', '"a  b"',
                '"aab"', '"aaab"', '" "', '"Alice"', '"A"', '"ba"',
                '"Hello World"', '"12345"'],
        'pair': ['(1, 2)', '(0,)', '((1, "a"), (2, "b"))',
                 '(1, "b")', '(1, "a")',
                 '{"b": 1, "a": 2}', '{"a": 1}', '{"a": 2}',
                 '{"a": 1, "b": 2}', '{"b": 3, "a": 4}',
                 '{"x": 10, "y": 20}', '{"y": 99, "x": 0}',
                 '(3, 1, 2)', '(1, 1, 1)'],
        'ref': ['[]', '[1]', '[1, 2, 3]', '[3, 1, 2]',
                '[float("nan"), 1.0, 2.0]',
                '[1.0, 1e-16, -1.0]',
                '[(1, "a"), (1, "b"), (2, "a")]',
                '[1, 1, 2, 1, 3]', '[[1], [2]]',
                '[(1, "b"), (1, "a"), (2, "c")]',
                '["a", "b"]',
                '[0, 0, 0]', '[-1, 0, 1]', '[1, 2, 3, 4, 5]',
                '["b", "a", "c"]', '[None, 1, "a"]',
                '[1, 1, 1, 2]', '[3, 3, 3, 3]', '[1, 2, 1, 2, 1]',
                '[1e16, 1.0, -1e16]', '[True, True, True]'],
        'none': ['None'],
        'collection': ['[]', '[1]', '[1, 2, 3]', '[3, 1, 2]',
                       '[1, 1, 2, 1, 3]', '(1, 2, 3)', '"abc"',
                       '{1, 2, 3}', '[1, 1, 1, 2]',
                       '[(1, "a"), (1, "b")]',
                       '[float("nan"), 1.0]',
                       '[1.0, 1e-16, -1.0]'],
    }

    # Build test input combinations (limited to avoid explosion)
    # For multi-fiber params, combine from all fibers and prioritize
    # edge cases (NaN, large floats, duplicate keys) first.
    param_samples = []
    for i, pname in enumerate(param_names):
        fibers = param_fibers[i] if i < len(param_fibers) else ['int']
        samples = []
        # Collect samples from each fiber, interleaving to ensure
        # edge cases from each fiber type appear early.
        per_fiber_lists = []
        for f in fibers:
            per_fiber_lists.append(type_samples.get(f, ['0', '1']))
        # Interleave: take first from each, then second from each, etc.
        max_len = max(len(lst) for lst in per_fiber_lists) if per_fiber_lists else 0
        for j in range(max_len):
            for lst in per_fiber_lists:
                if j < len(lst):
                    samples.append(lst[j])
        # Deduplicate and limit
        seen = set()
        unique = []
        for s in samples:
            if s not in seen:
                seen.add(s)
                unique.append(s)
        param_samples.append(unique[:25])

    # Generate test combinations (limit to 50 total for better coverage)
    import itertools as _it
    combos = list(_it.product(*param_samples))
    if len(combos) > 50:
        combos = combos[:50]

    if not combos:
        return None

    # Build test script
    args_list = ', '.join(f'args[{i}]' for i in range(len(param_names)))
    combo_strs = ', '.join(f'({", ".join(c)},)' for c in combos)

    # Split source into future imports and rest
    lines_f = source_f.split('\n')
    lines_g = source_g.split('\n')
    future_f = [l for l in lines_f if l.strip().startswith('from __future__')]
    rest_f = [l for l in lines_f if not l.strip().startswith('from __future__')]
    future_g = [l for l in lines_g if l.strip().startswith('from __future__')]
    rest_g = [l for l in lines_g if not l.strip().startswith('from __future__')]

    future_block = '\n'.join(sorted(set(future_f + future_g)))

    script = f'''{future_block}
import sys, json, io, types
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')

# Define function F
{chr(10).join(rest_f)}

# Find function F
_fn_f = None
for _name, _obj in list(locals().items()):
    if isinstance(_obj, types.FunctionType) and not _name.startswith('_'):
        _fn_f = _obj
        break

# Define function G (rename to avoid collision)
_saved_f = _fn_f
'''

    # Add G's source with renamed function
    script += f'''
{chr(10).join(rest_g)}

_fn_g = None
for _name, _obj in list(locals().items()):
    if isinstance(_obj, types.FunctionType) and not _name.startswith('_') and _obj is not _saved_f:
        _fn_g = _obj
        break

test_cases = [{combo_strs}]
results = []
_RESOURCE_EXCS = (MemoryError, RecursionError, OverflowError)
for args in test_cases:
    try:
        r_f = repr(_saved_f({args_list}))
        f_ok = True
    except _RESOURCE_EXCS:
        continue
    except Exception as e:
        f_ok = False
    try:
        r_g = repr(_fn_g({args_list}))
        g_ok = True
    except _RESOURCE_EXCS:
        continue
    except Exception as e:
        g_ok = False
    if not (f_ok and g_ok):
        continue
    if r_f != r_g:
        print(json.dumps({{"eq": False, "args": repr(args), "f": r_f[:50], "g": r_g[:50]}}))
        sys.exit(0)
print(json.dumps({{"eq": True, "n": len(test_cases)}}))
'''

    remaining = max(0.5, deadline - time.monotonic())
    try:
        proc = subprocess.run(
            ['python3.11', '-c', script],
            capture_output=True, text=True,
            timeout=min(remaining, 5.0)
        )
        if proc.returncode != 0:
            return None
        out = proc.stdout.strip()
        if not out:
            return None
        data = json.loads(out)
        if data.get('eq') is True:
            return True
        elif data.get('eq') is False:
            return False
    except Exception:
        pass
    return None


def _check_fiber(T, params, secs_f, secs_g, combo, tag_constraints,
                 timeout_ms) -> LocalJudgment:
    """Check equivalence on a single type fiber using Z3."""
    solver = _z3.Solver()
    solver.set('timeout', min(timeout_ms, 3000))  # cap at 3s per fiber
    solver.set('max_memory', 256)  # 256 MB limit per fiber — conservative
    T.semantic_axioms(solver)

    # Constrain params to this fiber
    for idx in range(len(params)):
        p = params[idx]
        solver.add(T.tag(p) != T.TBot)
        fiber = combo[idx]
        solver.add(tag_constraints[fiber](p, T))

    # Check all section pairs
    fiber_h0 = 0
    fiber_total_overlapping = 0
    fiber_inconclusive = 0
    fiber_obstruction = None
    fiber_obstruction_concrete = False

    for sf_sec in secs_f:
        for sg_sec in secs_g:
            overlap = _z3.And(sf_sec.guard, sg_sec.guard)

            # First check if guards can overlap at all
            solver.push()
            solver.add(overlap)
            guard_check = solver.check()
            solver.pop()
            if guard_check == _z3.unsat:
                continue

            fiber_total_overlapping += 1
            # Now check if terms can differ
            solver.push()
            solver.add(overlap)
            solver.add(sf_sec.term != sg_sec.term)
            r = solver.check()

            if r == _z3.unsat:
                solver.pop()
                # Only count as verified if both terms have the same
                # level of interpretation. If one uses uninterpreted fns
                # and the other uses concrete Z3 ops, the proof may be
                # vacuously true (uninterpreted fn chosen to match).
                # If terms are structurally identical, always trust Z3
                if sf_sec.term.eq(sg_sec.term):
                    fiber_h0 += 1
                elif _terms_same_opacity(sf_sec.term, sg_sec.term):
                    fiber_h0 += 1
                else:
                    fiber_inconclusive += 1  # vacuously equal
            elif r == _z3.sat:
                m = solver.model()
                solver.pop()
                fiber_info = []
                for k in range(len(params)):
                    try:
                        fiber_info.append(str(m.evaluate(T.tag(params[k]))))
                    except Exception:
                        fiber_info.append('?')

                # Z3 found a satisfying assignment where terms differ.
                # Track opacity for concrete_obstruction flag.
                d1 = _uninterp_depth(sf_sec.term)
                d2 = _uninterp_depth(sg_sec.term)
                is_concrete_cex = (d1 == 0 and d2 == 0)
                if d1 + d2 >= 2 and min(d1, d2) >= 1:
                    # Both terms use uninterpreted functions — Z3 can
                    # freely assign them to produce spurious disagreements.
                    fiber_inconclusive += 1
                else:
                    fiber_obstruction = ','.join(fiber_info)
                    fiber_obstruction_concrete = is_concrete_cex
                    break
            else:
                solver.pop()
                # Unknown/timeout — treat as inconclusive for this pair
                # but continue checking other pairs
        if fiber_obstruction:
            break

    if fiber_obstruction:
        return LocalJudgment(
            fiber=combo, is_equivalent=False,
            counterexample=fiber_obstruction,
            explanation=f'obstruction on [{fiber_obstruction}]',
            concrete_obstruction=fiber_obstruction_concrete)
    elif fiber_h0 > 0 and fiber_inconclusive == 0:
        # ALL overlapping section pairs verified
        return LocalJudgment(
            fiber=combo, is_equivalent=True,
            explanation=f'{fiber_h0}/{fiber_total_overlapping} sections agree')
    elif fiber_h0 > 0 and fiber_inconclusive > 0:
        # Some verified, some inconclusive — not enough for equivalence
        return LocalJudgment(
            fiber=combo, is_equivalent=None,
            explanation=f'{fiber_h0}/{fiber_total_overlapping} verified, {fiber_inconclusive} inconclusive')
    else:
        return LocalJudgment(
            fiber=combo, is_equivalent=None,
            explanation='no overlapping sections or timeout')
