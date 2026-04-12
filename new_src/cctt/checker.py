"""§5: Top-Level Equivalence Checker — the full CCTT pipeline.

Orchestrates: compile → duck type → site → local checks → Čech H¹ → verdict.
Also provides spec checking and bug finding entry points.
"""
from __future__ import annotations
import ast
import itertools
import textwrap
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

from .theory import Theory, _z3, _HAS_Z3
from .compiler import compile_func, Section
from .duck import infer_duck_type
from .cohomology import LocalJudgment, CechResult, compute_cech_h1


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
    sys.setrecursionlimit(max(old, 3000))
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
    """Check if a program satisfies a specification.

    spec_source is a reference implementation that defines the spec.
    The program satisfies the spec iff it's equivalent to the reference.
    """
    return check_equivalence(source, spec_source, timeout_ms)


def find_bugs(source: str, spec_source: str,
              timeout_ms: int = 5000) -> Result:
    """Find bugs by checking against a specification.

    Returns Result with fiber-localized bug information.
    """
    r = check_equivalence(source, spec_source, timeout_ms)
    if r.equivalent is False:
        r.explanation = f'BUG: {r.explanation}'
    return r


def _check(source_f: str, source_g: str, timeout_ms: int) -> Result:
    """The full CCTT pipeline."""

    # ── Step 1-2: Compile both programs ──
    T = Theory()
    sf = compile_func(source_f, T)
    sg = compile_func(source_g, T)
    if sf is None or sg is None:
        return Result(None, 'cannot compile')

    secs_f, params_f = sf
    secs_g, params_g = sg

    if len(params_f) != len(params_g):
        return Result(False, f'arity {len(params_f)} != {len(params_g)}')
    if not secs_f or not secs_g:
        return Result(None, 'empty presheaf')

    # ── Step 3: Unify parameters ──
    subst = [(pg, pf) for pf, pg in zip(params_f, params_g) if not pf.eq(pg)]
    if subst:
        secs_g = [Section(guard=_z3.substitute(s.guard, *subst),
                          term=_z3.substitute(s.term, *subst)) for s in secs_g]

    # ── Step 4: Duck type inference ──
    try:
        tree_f = ast.parse(textwrap.dedent(source_f))
        tree_g = ast.parse(textwrap.dedent(source_g))
        func_f = next(n for n in tree_f.body if isinstance(n, ast.FunctionDef))
        func_g = next(n for n in tree_g.body if isinstance(n, ast.FunctionDef))
        param_names = [a.arg for a in func_f.args.args]
    except Exception:
        return Result(None, 'cannot parse for duck typing')

    param_fibers = []
    for pname in param_names:
        kind, _ = infer_duck_type(func_f, func_g, pname)
        if kind == 'int': param_fibers.append(['int'])
        elif kind == 'str': param_fibers.append(['str'])
        elif kind == 'bool': param_fibers.append(['bool'])
        elif kind == 'ref': param_fibers.append(['ref'])
        elif kind == 'list': param_fibers.append(['pair', 'ref'])
        elif kind == 'collection': param_fibers.append(['pair', 'ref', 'str'])
        else: param_fibers.append(['int', 'bool', 'str', 'pair', 'ref', 'none'])

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
    if len(fiber_combos) > 50:
        fiber_combos = fiber_combos[:50]

    # Overlaps: fiber combos sharing at least one axis
    overlaps = []
    for i in range(len(fiber_combos)):
        for j in range(i+1, len(fiber_combos)):
            ci, cj = fiber_combos[i], fiber_combos[j]
            if any(ci[k] == cj[k] for k in range(len(ci))):
                overlaps.append((ci, cj))

    # ── Step 6: Local equivalence check per fiber ──
    judgments: Dict[Tuple[str, ...], LocalJudgment] = {}

    for combo in fiber_combos:
        solver = _z3.Solver()
        solver.set('timeout', timeout_ms)
        T.semantic_axioms(solver)

        # Constrain params to this fiber
        for idx in range(len(params_f)):
            p = params_f[idx]
            solver.add(T.tag(p) != T.TBot)
            fiber = combo[idx]
            solver.add(tag_constraints[fiber](p, T))

        # Check all section pairs
        fiber_h0 = 0
        fiber_obstruction = None

        for sf_sec in secs_f:
            for sg_sec in secs_g:
                overlap = _z3.And(sf_sec.guard, sg_sec.guard)

                solver.push()
                solver.add(overlap)
                if solver.check() == _z3.unsat:
                    solver.pop()
                    continue
                solver.pop()

                solver.push()
                solver.add(overlap)
                solver.add(sf_sec.term != sg_sec.term)
                r = solver.check()

                if r == _z3.unsat:
                    solver.pop()
                    fiber_h0 += 1
                elif r == _z3.sat:
                    m = solver.model()
                    fiber_info = [str(m.evaluate(T.tag(params_f[k])))
                                  for k in range(len(params_f))]
                    solver.pop()
                    fiber_obstruction = ','.join(fiber_info)
                    break
                else:
                    solver.pop()
            if fiber_obstruction:
                break

        if fiber_obstruction:
            judgments[combo] = LocalJudgment(
                fiber=combo, is_equivalent=False,
                counterexample=fiber_obstruction,
                explanation=f'obstruction on [{fiber_obstruction}]')
        elif fiber_h0 > 0:
            judgments[combo] = LocalJudgment(
                fiber=combo, is_equivalent=True,
                explanation=f'{fiber_h0} sections agree')
        else:
            judgments[combo] = LocalJudgment(
                fiber=combo, is_equivalent=None,
                explanation='no overlapping sections')

    # ── Step 7: Čech H¹ computation ──
    cech = compute_cech_h1(judgments, overlaps)

    if cech.equivalent is True:
        confidence = cech.h0 / max(cech.total_fibers, 1)
        return Result(True,
            f'H1=0: {cech.h0} faces verified across {cech.total_fibers} fibers',
            h0=cech.h0, confidence=confidence)
    elif cech.equivalent is False:
        obs = cech.obstructions
        obs_desc = str(obs[0]) if obs else 'unknown fiber'
        j = judgments.get(obs[0]) if obs else None
        detail = j.explanation if j else ''
        return Result(False,
            f'H1 obstruction: {detail} (fiber {obs_desc})',
            h0=cech.h0, h1=cech.h1_rank)
    else:
        return Result(None, f'inconclusive: {cech.h0}/{cech.total_fibers} fibers',
                      h0=cech.h0)
